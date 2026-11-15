/-
P3 (DESIGN.md §9), CSpace: the abstraction of capabilities.

FL4 stores a capability as two words in its own encoding
(`capability.rs`, `Cap::encode`/`Cap::decode`) and computes on the decoded
`capability.Cap`. The abstract spec (`Fl4Spec.Cap`, l4v Structures_A
`cap`) has its own representation: guards are bit lists, rights are sets,
mapped VSpace caps carry `Option (asid, vaddr)`.

* `bitsOf x n`: the low `n` bits of `x`, most significant first. This is
  how a word becomes an l4v bit list (`Fl4Spec.toBl`, then `drop`): a guard
  of `guard_size` bits, a capability pointer resolved to depth `n`.
* `absCap`: the abstract cap of a decoded cap. It is a function; the
  well-formedness conditions under which it is faithful are `CapWf`.
* `CapRel c a := CapWf c ∧ absCap c = a`, the relation used by the state
  relation and the refinement theorems.
* `LookupFaultRel`: FL4's `LookupFault` against the spec's
  `LookupFailure`.

Where the abstraction loses information, it is deliberate and listed here:
- `SchedControl { cpu }` maps to `schedControlCap`: the spec is
  single-core (DESIGN.md §8; the per-core difference goes in `Fl4Spec/Ext`).
- `IrqHandler { irq }` maps to the 8-bit `Irq` (`CapWf`: `irq < 256`).
- `SchedContext { size_bits }` is absolute in FL4 and relative to
  `min_sched_context_bits` in the spec (`Retype_A.default_cap`), so the
  abstraction subtracts it (`CapWf`: `size_bits ≥ 7`).
- `Reply { grant }` maps to the rights `{AllowGrant, AllowWrite}` or
  `{AllowWrite}` (l4v rt `StateRelation.cap_relation`: only `AllowGrant ∈ R`
  is observable; `Retype_A.default_cap` creates `{AllowGrant, AllowWrite}`).

Facts proved:
- bit lists: `bitsOf_take`, `bitsOf_drop`, `bitsOf_eq_iff`, `ofBl_bitsOf`,
  `toBl_eq_bitsOf`, `toBl_drop` (what the lookup proof needs);
- the encoding: `decode_cnode_eq` (decoding a tag-5 word pair),
  `decode_cnode_inv` (every decoded CNode cap has radix and guard size
  below 64 and a 58-bit guard, so `CapWf_of_decode_cnode` reduces `CapWf`
  of a stored CNode cap to "the guard fits its size"), `decode_encode_cnode`
  (`Cap::decode ∘ Cap::encode` is the identity on CNode caps with a
  canonical pointer, 6-bit radix and guard size and 58-bit guard: every
  CNode cap FL4 makes, since `update_cap_data` takes the guard from the 58
  bits `data >> 6`), `decode_encode_null`;
- the relation: `CapRel.cnode`, `CapRel.cnode_inv` (a related CNode cap
  has the spec's radix and guard, and conversely), `bitsOf_guard_inj`,
  `CapRel.null_iff`, `isCnodeCap_absCap` (`absCap` preserves being a
  CNode cap, which is what the walk branches on).
-/
import Fl4Proofs.P1.Store
import Fl4Spec.CSpace
import Mathlib.Tactic.IntervalCases
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Bit lists -/

/-- The low `n` bits of `x`, most significant first (l4v `drop (64 - n)
(to_bl x)` for a word `x`, `n ≤ 64`). -/
def bitsOf (x : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => x.testBit n :: bitsOf x n

@[simp] theorem bitsOf_zero (x : Nat) : bitsOf x 0 = [] := rfl
theorem bitsOf_succ (x n : Nat) : bitsOf x (n + 1) = x.testBit n :: bitsOf x n := rfl

@[simp] theorem length_bitsOf (x n : Nat) : (bitsOf x n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitsOf_succ, ih]

theorem bitsOf_eq_nil {x n : Nat} : bitsOf x n = [] ↔ n = 0 := by
  constructor
  · intro h; have := congrArg List.length h; simpa using this
  · rintro rfl; rfl

/-- Element `i` of `bitsOf x n` is bit `n - 1 - i`. -/
theorem getElem_bitsOf (x n i : Nat) (h : i < (bitsOf x n).length) :
    (bitsOf x n)[i] = x.testBit (n - 1 - i) := by
  induction n generalizing i with
  | zero => simp at h
  | succ n ih =>
    cases i with
    | zero => simp [bitsOf_succ]
    | succ i =>
      simp only [bitsOf_succ, List.getElem_cons_succ]
      rw [ih]; congr 1; omega

theorem bitsOf_drop (x : Nat) {k n : Nat} (hk : k ≤ n) : (bitsOf x n).drop k = bitsOf x (n - k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [bitsOf_succ, List.drop_succ_cons]
    rw [ih (by omega)]
    congr 1; omega

theorem bitsOf_take (x : Nat) {k n : Nat} (hk : k ≤ n) :
    (bitsOf x n).take k = bitsOf (x / 2 ^ (n - k)) k := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, getElem_bitsOf, Nat.testBit_div_two_pow]
    congr 1
    simp at h1 h2
    omega

/-- Bit lists of equal length are equal iff the numbers agree below `n`. -/
theorem bitsOf_eq_iff (x y n : Nat) : bitsOf x n = bitsOf y n ↔ x % 2 ^ n = y % 2 ^ n := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases hi : i < n
    · have := congrArg (fun l => l[n - 1 - i]?) h
      rw [List.getElem?_eq_getElem (by simp; omega), List.getElem?_eq_getElem (by simp; omega)] at this
      simp only [Option.some.injEq, getElem_bitsOf] at this
      have e : n - 1 - (n - 1 - i) = i := by omega
      rw [e] at this
      simp [hi, this]
    · simp [hi]
  · intro h
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [getElem_bitsOf]
      have := congrArg (fun z => z.testBit (n - 1 - i)) h
      simp only [Nat.testBit_mod_two_pow] at this
      simp at h1
      have hlt : n - 1 - i < n := by omega
      simpa [hlt] using this

theorem bitsOf_mod (x n : Nat) : bitsOf (x % 2 ^ n) n = bitsOf x n :=
  (bitsOf_eq_iff _ _ _).2 (Nat.mod_mod _ _)

theorem bitsOf_mod_of_le (x : Nat) {n m : Nat} (h : n ≤ m) : bitsOf (x % 2 ^ m) n = bitsOf x n := by
  rw [bitsOf_eq_iff, Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow 2 h

/-- The value of a bit list, most significant first. -/
def blVal (acc : Nat) (bs : List Bool) : Nat := bs.foldl (fun a b => 2 * a + (if b then 1 else 0)) acc

theorem blVal_bitsOf (acc x n : Nat) : blVal acc (bitsOf x n) = acc * 2 ^ n + x % 2 ^ n := by
  induction n generalizing acc with
  | zero => simp [blVal, Nat.mod_one]
  | succ n ih =>
    simp only [blVal, bitsOf_succ, List.foldl_cons] at ih ⊢
    rw [ih]
    rw [Nat.mod_pow_succ]
    have : (x.testBit n) = decide (x / 2 ^ n % 2 = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
    rw [this]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ n) with h | h <;> simp [h, Nat.pow_succ] <;> ring

private theorem ofBl_step (acc : BitVec 64) (b : Bool) :
    ((acc <<< 1) ||| (if b then 1 else 0)) = acc + acc + (if b then 1 else 0) := by
  have h0 : acc <<< 1 &&& (if b then (1 : BitVec 64) else 0) = 0#64 := by
    ext i hi
    cases b <;> simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft] <;> interval_cases i <;> simp
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ h0, BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  rw [show BitVec.twoPow 64 1 = 2#64 from rfl, BitVec.mul_two]

theorem ofBl_foldl_toNat (acc : BitVec 64) (bs : List Bool) :
    (bs.foldl (fun (acc : BitVec 64) b => (acc <<< 1) ||| (if b then (1 : BitVec 64) else 0)) acc).toNat =
      blVal acc.toNat bs % 2 ^ 64 := by
  induction bs generalizing acc with
  | nil => simp [blVal, Nat.mod_eq_of_lt acc.isLt]
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rw [ofBl_step, ih]
    simp only [blVal, List.foldl_cons]
    -- both sides are the fold from a start that agrees mod 2^64
    have key : ∀ (a a' : Nat), a % 2 ^ 64 = a' % 2 ^ 64 →
        (bs.foldl (fun a b => 2 * a + (if b then 1 else 0)) a) % 2 ^ 64 =
        (bs.foldl (fun a b => 2 * a + (if b then 1 else 0)) a') % 2 ^ 64 := by
      clear ih
      induction bs with
      | nil => intro a a' h; simpa using h
      | cons c cs ihc =>
        intro a a' h
        simp only [List.foldl_cons]
        apply ihc
        omega
    apply key
    cases b <;> simp [BitVec.toNat_add, Nat.add_mod, Nat.two_mul]

theorem ofBl_bitsOf (x n : Nat) : (Fl4Spec.ofBl (bitsOf x n) : BitVec 64).toNat = x % 2 ^ n % 2 ^ 64 := by
  unfold Fl4Spec.ofBl
  rw [ofBl_foldl_toNat]
  simp [blVal_bitsOf]

theorem toBl_eq_bitsOf (w : BitVec 64) : Fl4Spec.toBl w = bitsOf w.toNat 64 := by
  apply List.ext_getElem
  · simp [Fl4Spec.toBl]
  · intro i h1 h2
    simp only [Fl4Spec.toBl, List.getElem_map, List.getElem_reverse, List.getElem_range,
      getElem_bitsOf, BitVec.getLsbD, List.length_range]

/-- A capability pointer of 64 bits, resolved to depth `n` (l4v callers pass
`to_bl cptr`; `lookup_slot_for_cnode_op` drops to the last `depth` bits). -/
theorem toBl_drop (w : BitVec 64) (n : Nat) (hn : n ≤ 64) :
    (Fl4Spec.toBl w).drop (64 - n) = bitsOf w.toNat n := by
  rw [toBl_eq_bitsOf, bitsOf_drop _ (by omega)]
  congr 1; omega

/-! ## Rights -/

/-- The rights set of the flags `write`, `read`, `grant`, `grantReply`. -/
def rightsOf (w r g gr : Bool) : Fl4Spec.CapRights :=
  {x | match x with
    | .allowWrite => w = true
    | .allowRead => r = true
    | .allowGrant => g = true
    | .allowGrantReply => gr = true}

/-- Reply cap rights (see the module comment). -/
def replyRights (grant : Bool) : Fl4Spec.CapRights :=
  if grant then {.allowGrant, .allowWrite} else {.allowWrite}

/-- x86 `vm_rights_t` (`VM_KERNEL_ONLY = 1`, `VM_READ_ONLY = 2`,
`VM_READ_WRITE = 3`) as l4v VM rights. -/
def vmRightsOf (r : U64) : Fl4Spec.VMRights :=
  if r.val = 3 then Fl4Spec.vmReadWrite else if r.val = 2 then Fl4Spec.vmReadOnly else Fl4Spec.vmKernelOnly

def frameSizeOf : capability.FrameSize → Fl4Spec.VMPageSize
  | .Small => .x64SmallPage
  | .Large => .x64LargePage
  | .Huge => .x64HugePage

/-! ## The abstraction -/

/-- Zombie type `65` is a TCB (`capability::ZOMBIE_TCB`), otherwise the
CNode radix. -/
def zombieBits (zt : U64) : Option Nat := if zt.val = 65 then none else some zt.val

/-- The abstract cap of a decoded FL4 cap. Faithful under `CapWf`. -/
def absCap : capability.Cap → Fl4Spec.Cap
  | .Null => .nullCap
  | .Untyped p sb fi dev => .untypedCap dev p.bv sb.val fi.val
  | .Endpoint p b s r g gr => .endpointCap p.bv b.bv (rightsOf s r g gr)
  | .Notification p b s r => .notificationCap p.bv b.bv (rightsOf s r false false)
  | .Reply p g => .replyCap p.bv (replyRights g)
  | .CNode p r gs g => .cnodeCap p.bv r.val (bitsOf g.val gs.val)
  | .Thread p => .threadCap p.bv
  | .IrqControl => .irqControlCap
  | .IrqHandler i => .irqHandlerCap (BitVec.ofNat 8 i.val)
  | .Zombie p zt n => .zombie p.bv (zombieBits zt) n.val
  | .Domain => .domainCap
  | .SchedContext p sb => .schedContextCap p.bv (sb.val - Fl4Spec.minSchedContextBits)
  | .SchedControl _ => .schedControlCap
  | .Frame p sz r dev m ept asid va =>
    .archObjectCap (.pageCap dev p.bv (vmRightsOf r) (if m then (if ept then .vmEptMap else .vmVSpaceMap) else .vmNoMap)
      (frameSizeOf sz) (if m then some (asid.bv, va.bv) else none))
  | .PageTable p m asid va => .archObjectCap (.pageTableCap p.bv (if m then some (asid.bv, va.bv) else none))
  | .PageDirectory p m asid va =>
    .archObjectCap (.pageDirectoryCap p.bv (if m then some (asid.bv, va.bv) else none))
  | .Pdpt p m asid va => .archObjectCap (.pdPointerTableCap p.bv (if m then some (asid.bv, va.bv) else none))
  | .Pml4 p m asid => .archObjectCap (.pml4Cap p.bv (if m then some asid.bv else none))
  | .Vcpu p => .archObjectCap (.vcpuCap p.bv)
  | .Ept p level m asid va => .archObjectCap (.eptCap p.bv level.val (if m then some (asid.bv, va.bv) else none))
  | .AsidControl => .archObjectCap .asidControlCap
  | .AsidPool p base => .archObjectCap (.asidPoolCap p.bv base.bv)
  | .IoPortControl => .archObjectCap .ioPortControlCap
  | .IoPort f l _ => .archObjectCap (.ioPortCap (BitVec.ofNat 16 f.val) (BitVec.ofNat 16 l.val))

/-- Field ranges under which `absCap` is faithful. Every cap `Cap::decode`
produces satisfies the CNode bounds on radix and guard size
(`decode_cnode_wf`); the guard fitting its size is an invariant (l4v
`valid_cap`: the guard is a list of `guard_size` bits by construction). -/
def CapWf : capability.Cap → Prop
  | .CNode _ r gs g => r.val < 64 ∧ gs.val < 64 ∧ g.val < 2 ^ gs.val
  | .IrqHandler i => i.val < 256
  | .Zombie _ zt _ => zt.val ≤ 64 ∨ zt.val = 65
  | .SchedContext _ sb => Fl4Spec.minSchedContextBits ≤ sb.val
  | .Frame _ _ r _ _ _ _ _ => 1 ≤ r.val ∧ r.val ≤ 3
  | .IoPort f l _ => f.val < 2 ^ 16 ∧ l.val < 2 ^ 16
  | _ => True

/-- The capability relation: FL4 cap `c` represents abstract cap `a`. -/
def CapRel (c : capability.Cap) (a : Fl4Spec.Cap) : Prop := CapWf c ∧ absCap c = a

theorem CapRel.abs {c : capability.Cap} {a} (h : CapRel c a) : a = absCap c := h.2.symm

/-! ## What lookup needs of the relation -/

@[simp] theorem absCap_null : absCap .Null = .nullCap := rfl

theorem CapRel.null_iff {c : capability.Cap} {a} (h : CapRel c a) :
    a = .nullCap ↔ c = .Null := by
  obtain ⟨_, rfl⟩ := h
  cases c <;> simp [absCap]

/-- `absCap` preserves being a CNode cap (`isCnodeCap`). -/
theorem isCnodeCap_absCap (c : capability.Cap) :
    Fl4Spec.isCnodeCap (absCap c) = (match c with | .CNode .. => true | _ => false) := by
  cases c <;> rfl

/-- A related CNode cap: the spec's radix is FL4's radix, the spec's guard
is FL4's `guard_size` low bits of the guard, and the guard fits. -/
theorem CapRel.cnode {p r gs g : U64} {a} (h : CapRel (.CNode p r gs g) a) :
    a = .cnodeCap p.bv r.val (bitsOf g.val gs.val) ∧ r.val < 64 ∧ gs.val < 64 ∧ g.val < 2 ^ gs.val :=
  ⟨h.2.symm, h.1⟩

theorem CapRel.cnode_inv {c : capability.Cap} {oref bits guard} (h : CapRel c (.cnodeCap oref bits guard)) :
    ∃ p r gs g, c = .CNode p r gs g ∧ oref = p.bv ∧ bits = r.val ∧ guard = bitsOf g.val gs.val ∧
      r.val < 64 ∧ gs.val < 64 ∧ g.val < 2 ^ gs.val := by
  obtain ⟨hw, ha⟩ := h
  cases c <;> simp [absCap] at ha
  case CNode p r gs g =>
    obtain ⟨rfl, rfl, rfl⟩ := ha
    exact ⟨p, r, gs, g, rfl, rfl, rfl, rfl, hw⟩

/-- The guard as a bit list determines guard size and (fitting) guard. -/
theorem bitsOf_guard_inj {g g' gs gs' : Nat} (h : bitsOf g gs = bitsOf g' gs')
    (hg : g < 2 ^ gs) (hg' : g' < 2 ^ gs') : gs = gs' ∧ g = g' := by
  have hl : gs = gs' := by simpa using congrArg List.length h
  subst hl
  refine ⟨rfl, ?_⟩
  have := (bitsOf_eq_iff _ _ _).1 h
  rwa [Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt hg'] at this

/-! ## The two-word encoding

Equations for the Aeneas shift and bit operations at constant amounts, the
`Cap::decode` and `Cap::encode` cases lookup uses, and their agreement. -/

theorem shr_eq (x : U64) (k : I32) (h0 : 0 ≤ k.val) (h : k.val < 64) : x >>> k = ok ⟨x.bv >>> k.toNat⟩ := by
  have hk : k.toNat < 64 := by scalar_tac
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, h0, UScalar.shiftRight, ite_true]
  simp [hk, BitVec.ushiftRight_eq]
theorem shl_eq (x : U64) (k : I32) (h0 : 0 ≤ k.val) (h : k.val < 64) : x <<< k = ok ⟨x.bv <<< k.toNat⟩ := by
  have hk : k.toNat < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_IScalar, h0, UScalar.shiftLeft, ite_true]
  simp [hk, BitVec.shiftLeft_eq]

/-- Decoding a word pair with tag 5 (CNode). -/
theorem decode_cnode_eq (w0 w1 p : U64) (ht : w0.bv >>> 59 = 5#64) (hp : capability.unpack_ptr w0 = ok p) :
    capability.Cap.decode w0 w1 = ok (.CNode p ⟨(w0.bv >>> 48) &&& 63#64⟩ ⟨w1.bv >>> 58⟩ ⟨w1.bv &&& 0x03ffffffffffffff#64⟩) := by
  unfold capability.Cap.decode
  simp only [shr_eq _ 59#i32 (by decide) (by decide), hp, bind_ok]
  split <;> rename_i heq
  all_goals first
    | (exfalso; have := congrArg UScalar.bv heq; simp [ht] at this; done)
    | (simp only [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 58#i32 (by decide) (by decide), lift,
        bind_ok]; rfl)
    | (exfalso; simp_all)

theorem unpack_ptr_eq (w : U64) : capability.unpack_ptr w =
    ok ⟨if (w.bv &&& 0xffffffffffff#64) &&& 0x800000000000#64 = 0 then w.bv &&& 0xffffffffffff#64
        else (w.bv &&& 0xffffffffffff#64) ||| 0xffff000000000000#64⟩ := by
  unfold capability.unpack_ptr
  simp only [lift, bind_ok, capability.PTR_MASK]
  split <;> rename_i h <;> split <;> rename_i h' <;> first | rfl | (exfalso; simp_all [UScalar.eq_equiv_bv_eq])

theorem encode_cnode (p r gs g : U64) : capability.Cap.encode (.CNode p r gs g) =
    ok (⟨(5#64 <<< 59) ||| (p.bv &&& 0xffffffffffff#64) ||| ((r.bv &&& 63#64) <<< 48)⟩,
        ⟨((gs.bv &&& 63#64) <<< 58) ||| (g.bv &&& 0x03ffffffffffffff#64)⟩) := by
  simp only [capability.Cap.encode, capability.tag, capability.pack_ptr, lift, bind_ok, capability.PTR_MASK,
    shl_eq _ 59#i32 (by decide) (by decide), shl_eq _ 48#i32 (by decide) (by decide),
    shl_eq _ 58#i32 (by decide) (by decide)]
  rfl

theorem high_bits_false {x : BitVec 64} {k : Nat} (h : x.toNat < 2 ^ k) :
    ∀ j (hj : j < 64), k ≤ j → x[j] = false := fun j hj hk => by
  rw [← BitVec.getLsbD_eq_getElem]
  exact Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide : 2 > 0) hk))

/-- A canonical x86-64 address: bits 63..47 all equal (what `unpack_ptr`
restores from the 48 stored bits). -/
def Canonical (p : U64) : Prop :=
  (∀ j (hj : j < 64), 47 ≤ j → p.bv[j] = false) ∨ (∀ j (hj : j < 64), 47 ≤ j → p.bv[j] = true)



section CNodeWords
set_option linter.unusedSimpArgs false
variable (p r gs g : BitVec 64)

/-- Word 0 of an encoded CNode cap. -/
abbrev cw0 : BitVec 64 := 5#64 <<< 59 ||| p &&& 0xffffffffffff#64 ||| (r &&& 63#64) <<< 48
/-- Word 1 of an encoded CNode cap. -/
abbrev cw1 : BitVec 64 := (gs &&& 63#64) <<< 58 ||| g &&& 0x03ffffffffffffff#64

theorem cw0_tag : cw0 p r >>> 59 = 5#64 := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
  interval_cases i <;> simp

theorem cw0_radix (hr : ∀ j (hj : j < 64), 6 ≤ j → r[j] = false) : (cw0 p r >>> 48) &&& 63#64 = r := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
  interval_cases i <;> simp [hr]

theorem cw1_gs (hgs : ∀ j (hj : j < 64), 6 ≤ j → gs[j] = false) : cw1 gs g >>> 58 = gs := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
  interval_cases i <;> simp [hgs]

theorem cw1_guard (hg : ∀ j (hj : j < 64), 58 ≤ j → g[j] = false) : cw1 gs g &&& 0x03ffffffffffffff#64 = g := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
  interval_cases i <;> simp [hg]

theorem cw0_ptr_lo (hp : ∀ j (hj : j < 64), 47 ≤ j → p[j] = false) : cw0 p r &&& 0xffffffffffff#64 = p := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
  interval_cases i <;> simp [hp]

theorem cw0_ptr_hi (hp : ∀ j (hj : j < 64), 47 ≤ j → p[j] = true) :
    cw0 p r &&& 0xffffffffffff#64 ||| 0xffff000000000000#64 = p := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
  interval_cases i <;> simp [hp]

theorem cw0_sign_lo (hp : ∀ j (hj : j < 64), 47 ≤ j → p[j] = false) :
    cw0 p r &&& 0xffffffffffff#64 &&& 0x800000000000#64 = 0#64 := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
  interval_cases i <;> simp [hp]

theorem cw0_sign_hi (hp : ∀ j (hj : j < 64), 47 ≤ j → p[j] = true) :
    cw0 p r &&& 0xffffffffffff#64 &&& 0x800000000000#64 ≠ 0#64 := by
  intro h
  have := congrArg (fun x : BitVec 64 => x[47]) h
  simp [hp] at this

end CNodeWords

/-- `Cap::encode` then `Cap::decode` is the identity on CNode caps whose
fields fit their encoding (canonical pointer, 6-bit radix and guard size,
58-bit guard). -/
theorem decode_encode_cnode (p r gs g : U64) (hp : Canonical p) (hr : r.val < 64) (hgs : gs.val < 64)
    (hg : g.val < 2 ^ 58) :
    ∃ w0 w1, capability.Cap.encode (.CNode p r gs g) = ok (w0, w1) ∧
      capability.Cap.decode w0 w1 = ok (.CNode p r gs g) := by
  refine ⟨_, _, encode_cnode p r gs g, ?_⟩
  have hr' := high_bits_false (x := r.bv) (k := 6) (by simpa using hr)
  have hgs' := high_bits_false (x := gs.bv) (k := 6) (by simpa using hgs)
  have hg' := high_bits_false (x := g.bv) (k := 58) (by simpa using hg)
  have hup : capability.unpack_ptr ⟨cw0 p.bv r.bv⟩ = ok p := by
    rw [unpack_ptr_eq]; congr 1; rw [UScalar.eq_equiv_bv_eq]
    rcases hp with hp | hp
    · split
      · exact cw0_ptr_lo _ _ hp
      · exfalso; rename_i h; exact h (cw0_sign_lo _ _ hp)
    · split
      · exfalso; rename_i h; exact cw0_sign_hi _ _ hp h
      · exact cw0_ptr_hi _ _ hp
  rw [decode_cnode_eq _ _ p (cw0_tag _ _) hup]
  simp only [cw0_radix _ _ hr', cw1_gs _ _ hgs', cw1_guard _ _ hg']

theorem shr_u64_eq (x i : U64) (h : i.val < 64) : x >>> i = ok ⟨x.bv >>> i.val⟩ := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_UScalar, UScalar.shiftRight]
  simp [h, BitVec.ushiftRight_eq]

/-- `unpack_asid`: a mapping cap's 20-bit ASID, the high 4 bits at `sh`
of the first word. -/
def asidF (w0 : BitVec 64) (sh : Nat) (w1 : BitVec 64) : BitVec 64 :=
  (((w0 >>> sh) &&& 0xf#64) <<< 16) ||| (w1 >>> 48)

theorem unpack_asid_eq (w0 sh w1 : U64) (h : sh.val < 64) :
    capability.unpack_asid w0 sh w1 = ok ⟨asidF w0.bv sh.val w1.bv⟩ := by
  unfold capability.unpack_asid
  have : (sh &&& 63#u64).val = sh.val := by
    have : (sh &&& 63#u64).val = sh.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod sh.val 6
    omega
  simp only [lift, bind_ok]
  rw [shr_u64_eq _ _ (by omega), this]
  simp only [bind_ok, shl_eq _ 16#i32 (by decide) (by decide), shr_eq _ 48#i32 (by decide) (by decide)]
  rfl

theorem bit_eq (w n : U64) : capability.bit w n = ok (((⟨w.bv >>> ((n &&& 63#u64).val)⟩ : U64) &&& 1#u64) != 0#u64) := by
  unfold capability.bit
  have : (n &&& 63#u64).val < 64 := by
    have : (n &&& 63#u64).val = n.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod n.val 6
    omega
  simp only [lift, bind_ok, shr_u64_eq _ _ this]

theorem from_code_eq (c : U64) : capability.FrameSize.from_code c =
    ok (if c = 1#u64 then .Large else if c = 2#u64 then .Huge else .Small) := by
  unfold capability.FrameSize.from_code; split_ifs <;> rfl

/-- Every decoded CNode cap has a radix and guard size below 64 (and a
58-bit guard): the CNode part of `CapWf` other than the guard fitting its
size holds of anything read from memory. -/
theorem decode_cnode_inv {w0 w1 p r gs g : U64} (h : capability.Cap.decode w0 w1 = ok (.CNode p r gs g)) :
    r.val < 64 ∧ gs.val < 64 ∧ g.val < 2 ^ 58 := by
  unfold capability.Cap.decode at h
  simp only [shr_eq _ 59#i32 (by decide) (by decide), unpack_ptr_eq, bind_ok] at h
  split at h
  all_goals simp [shr_eq _ 48#i32 (by decide) (by decide), shr_eq _ 50#i32 (by decide) (by decide),
    shr_eq _ 58#i32 (by decide) (by decide), shr_eq _ 53#i32 (by decide) (by decide), shr_eq _ 16#i32 (by decide) (by decide), lift, bit_eq, from_code_eq,
    unpack_asid_eq _ 54#u64 _ (by decide), unpack_asid_eq _ 49#u64 _ (by decide)] at h
  case h_5 =>
    obtain ⟨-, rfl, rfl, rfl⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · simp only [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    · simp only [UScalar.val, BitVec.toNat_ushiftRight]
      have := w1.bv.isLt
      rw [Nat.shiftRight_eq_div_pow]; omega
    · simp only [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

  all_goals split_ifs at h <;> simp_all

theorem CapWf_of_decode_cnode {w0 w1 p r gs g : U64} (h : capability.Cap.decode w0 w1 = ok (.CNode p r gs g))
    (hg : g.val < 2 ^ gs.val) : CapWf (.CNode p r gs g) :=
  ⟨(decode_cnode_inv h).1, (decode_cnode_inv h).2.1, hg⟩

/-- `Cap::encode` then `Cap::decode` on the null cap. -/
theorem decode_encode_null : capability.Cap.encode .Null = ok (0#u64, 0#u64) ∧
    capability.Cap.decode 0#u64 0#u64 = ok .Null := by
  refine ⟨rfl, ?_⟩
  unfold capability.Cap.decode
  simp only [shr_eq _ 59#i32 (by decide) (by decide), unpack_ptr_eq, bind_ok]
  split <;> rename_i heq
  all_goals first
    | (exfalso; have := congrArg UScalar.bv heq; simp at this)
    | rfl

/-! ## Lookup faults -/

/-- FL4's lookup faults against l4v `lookup_failure`. `DepthMismatch` and
`GuardMismatch` carry the same numbers; the guard is a word plus size in
FL4 and a bit list in the spec. -/
def LookupFaultRel : error.LookupFault → Fl4Spec.LookupFailure → Prop
  | .InvalidRoot, .invalidRoot => True
  | .MissingCapability bl, .missingCapability bl' => bl' = bl.val
  | .DepthMismatch found left, .depthMismatch left' found' => left' = left.val ∧ found' = found.val
  | .GuardMismatch g left gs, .guardMismatch left' g' => left' = left.val ∧ g' = bitsOf g.val gs.val
  | _, _ => False

end

end Fl4Proofs.P3
