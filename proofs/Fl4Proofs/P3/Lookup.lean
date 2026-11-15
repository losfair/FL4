/-
P3 (DESIGN.md §9), CSpace: the first refinement theorems. FL4's CSpace walk
(`cspace.rs`) refines the spec's (l4v CSpace_A).

* `resolve_address_bits_refines`: for a state related by `StateRel`, a
  root cap related by `CapRel` and valid (`CapValid`), and a depth `n ≤ 64`,
  FL4's `resolve_address_bits s cap cptr n` returns `r` such that the
  spec's `resolve_address_bits' (cap', bits)`, with `bits` the low `n` bits
  of `cptr` (`bitsOf cptr n`, l4v `drop (64 - n) (to_bl cptr)`), has exactly
  one outcome `e` (and does not fail, in the l4v sense of the failure flag),
  from which the state is unchanged, and `ResRel r e`:
  - success: FL4's slot is the address of the spec's slot (`cslotAddr`),
    and FL4's `bits_left` is the length of the spec's remaining bits;
  - failure: the lookup faults correspond (`LookupFaultRel`):
    `InvalidRoot` ↔ `InvalidRoot`, `GuardMismatch { guard_found, bits_left,
    guard_size }` ↔ `GuardMismatch bits_left (guard_size low bits of
    guard_found)`, `DepthMismatch { bits_found, bits_left }` ↔
    `DepthMismatch bits_left bits_found`. (`MissingCapability` is not
    produced by the walk, in either.)
  So FL4 fails exactly when the spec throws, with the same fault.
* `lookup_slot_refines`, `lookup_cap_refines`, `lookup_cap_and_slot_refines`:
  the same for `lookup_slot` / `lookup_cap` / `lookup_cap_and_slot`
  against `lookup_slot_for_thread` / `lookup_cap` / `lookup_cap_and_slot`
  at a 64-bit cptr `toBl cptr`, for a TCB of the typed heap; `lookup_cap`'s
  lookup faults are FL4's `Exc::Lookup lf`, its cap is `CapRel`-related to
  the spec's.
* `lookup_slot_for_cnode_op_refines`: `lookup_slot_for_cnode_op` (hence
  `lookup_source_slot`, `lookup_target_slot`, `lookup_pivot_slot`) against
  l4v `lookup_slot_for_cnode_op` at `toBl cptr` and `unat depth`; its errors
  are `SysErrRel`-related syscall errors (`RangeError 1 64`,
  `FailedLookup source lf`, including the `DepthMismatch 0 bits_left` for
  a walk that stopped early).

Hypotheses about the concrete state: `StateRel th (L.mem s) σ` and
`SlotsValid th (L.mem s)` (StateRel.lean), `CapValid th` of the root cap.
The radix of every CNode reached is at least 1 (from `CapValid`), which
excludes the one case where the two disagree: a CNode cap with radix and
guard size both 0, where the spec fails (`fail`, "table broken") and FL4
returns `InvalidRoot`.
-/
import Fl4Proofs.P3.StateRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

/-! ## The spec side: unfolding `resolve_address_bits'` -/

section Spec
open Fl4Spec
variable {Z : Type}

section
variable {σ α β ε : Type}
@[simp] theorem nd_pure_apply (a : α) (s : σ) : (pure a : NonDet σ α) s = ({(a, s)}, False) := rfl
@[simp] theorem nd_bind_apply (m : NonDet σ α) (f : α → NonDet σ β) (s : σ) :
    (m >>= f) s = ({r | ∃ x ∈ (m s).1, r ∈ (f x.1 x.2).1}, (m s).2 ∨ ∃ x ∈ (m s).1, (f x.1 x.2).2) := rfl
theorem nd_pure_bind (a : α) (f : α → NonDet σ β) : (pure a >>= f) = f a := by
  funext s
  simp only [nd_bind_apply, nd_pure_apply, Set.mem_singleton_iff, exists_eq_left, false_or]
  ext <;> simp
theorem nd_bind_single {m : NonDet σ α} {s : σ} {a : α} (h : m s = ({(a, s)}, False)) (f : α → NonDet σ β) :
    (m >>= f) s = f a s := by
  simp only [nd_bind_apply, h, Set.mem_singleton_iff, exists_eq_left, false_or]
  ext <;> simp
theorem nd_bind_single' {m : NonDet σ α} {s : σ} {a : α} (h : m s = ({(a, s)}, False))
    (f : α → NonDet σ β) : NonDet.bind m f s = f a s := nd_bind_single h f
@[simp] theorem ndE_pure_bind (a : α) (f : α → NonDetE σ ε β) : (pure a >>= f) = f a := by
  show ExceptT.mk (pure (Except.ok a) >>= ExceptT.bindCont f) = f a
  rw [nd_pure_bind]; rfl
@[simp] theorem ndE_throw_bind (e : ε) (f : α → NonDetE σ ε β) : (throw e >>= f) = throw e := by
  show ExceptT.mk (pure (Except.error e) >>= ExceptT.bindCont f) = ExceptT.mk (pure (Except.error e))
  rw [nd_pure_bind]; rfl
end

theorem rab_noncnode (a : Cap) (cref : CapRef) (σ : State Z) (h : isCnodeCap a = false) :
    (resolveAddressBits' (Z := Z) (a, cref)).run σ = ({(.error .invalidRoot, σ)}, False) := by
  rw [resolveAddressBits']
  cases a <;> simp [isCnodeCap] at h <;> rfl

theorem rab_guard (oref : ObjRef) (radix : Nat) (guard : List Bool) (cref : CapRef) (σ : State Z)
    (h0 : radix + guard.length ≠ 0) (hg : ¬ guard <+: cref) :
    (resolveAddressBits' (Z := Z) (.cnodeCap oref radix guard, cref)).run σ =
      ({(.error (.guardMismatch cref.length guard), σ)}, False) := by
  rw [resolveAddressBits']
  simp only [h0, _root_.dite_false]
  simp [hg, NonDetE.whenE, NonDetE.throwError]

theorem rab_depth (oref : ObjRef) (radix : Nat) (guard : List Bool) (cref : CapRef) (σ : State Z)
    (h0 : radix + guard.length ≠ 0) (hg : guard <+: cref) (hd : cref.length < radix + guard.length) :
    (resolveAddressBits' (Z := Z) (.cnodeCap oref radix guard, cref)).run σ =
      ({(.error (.depthMismatch cref.length (radix + guard.length)), σ)}, False) := by
  rw [resolveAddressBits']
  simp only [h0, _root_.dite_false]
  simp [hg, hd, NonDetE.whenE, NonDetE.throwError]

theorem rab_last (oref : ObjRef) (radix : Nat) (guard : List Bool) (cref : CapRef) (σ : State Z)
    (h0 : radix + guard.length ≠ 0) (hg : guard <+: cref) (hd : ¬ cref.length < radix + guard.length)
    (hr : cref.drop (radix + guard.length) = []) :
    (resolveAddressBits' (Z := Z) (.cnodeCap oref radix guard, cref)).run σ =
      ({(.ok ((oref, (cref.drop guard.length).take radix), []), σ)}, False) := by
  rw [resolveAddressBits']
  simp only [h0, _root_.dite_false]
  simp [hg, hd, hr, NonDetE.whenE, NonDetE.returnOk]

theorem rab_next (oref : ObjRef) (radix : Nat) (guard : List Bool) (cref : CapRef) (σ : State Z) (c : Cap)
    (h0 : radix + guard.length ≠ 0) (hg : guard <+: cref) (hd : ¬ cref.length < radix + guard.length)
    (hr : cref.drop (radix + guard.length) ≠ [])
    (hget : getCap (Z := Z) (oref, (cref.drop guard.length).take radix) σ = ({(c, σ)}, False)) :
    (resolveAddressBits' (Z := Z) (.cnodeCap oref radix guard, cref)).run σ =
      if isCnodeCap c then (resolveAddressBits' (Z := Z) (c, cref.drop (radix + guard.length))).run σ
      else ({(.ok ((oref, (cref.drop guard.length).take radix), cref.drop (radix + guard.length)), σ)}, False) := by
  rw [resolveAddressBits']
  simp only [h0, _root_.dite_false]
  have h1 : (Except.ok <$> getCap (Z := Z) (oref, (cref.drop guard.length).take radix) :
      NonDet (State Z) (Except LookupFailure Cap)) σ = ({(.ok c, σ)}, False) := by
    show (getCap _ >>= _) σ = _
    rw [nd_bind_single hget]; rfl
  simp only [hg, hd, hr, not_true_eq_false, ite_false, _root_.dite_false, NonDetE.whenE, NonDetE.returnOk, NonDetE.liftE,
    ExceptT.run_bind, ExceptT.run_lift, ExceptT.run_pure, nd_pure_bind]
  rw [nd_bind_single h1]
  by_cases h : isCnodeCap c = true <;> simp only [h] <;> rfl

theorem getCap_cnode {σ : State Z} {p : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool} {a : Cap}
    (hk : σ.kheap p = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (ha : cs idx = some a) :
    getCap (Z := Z) (p, idx) σ = ({(a, σ)}, False) := by
  unfold getCap
  have h1 : getObject (Z := Z) p σ = ({(.cnode r cs, σ)}, False) := by
    simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt]; rfl
  show (getObject p >>= _) σ = _
  rw [nd_bind_single h1]
  have h2 : (NonDet.assert (wellFormedCnodeN r cs) : NonDet (State Z) Unit) σ = ({((), σ)}, False) := by
    simp [NonDet.assert, hwf]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_single h2]
  show ((pure cs : NonDet (State Z) CnodeContents) >>= _) σ = _
  rw [nd_pure_bind]
  simp [ha, NonDet.assertOpt]; rfl

theorem getTcb_ctable {σ : State Z} {t : ObjRef} {tcb : Tcb} (hk : σ.kheap t = some (.tcb tcb)) :
    NonDet.getsThe (getTcb (Z := Z) t) σ = ({(tcb, σ)}, False) := by
  simp [NonDet.getsThe, getTcb, readObject, hk, NonDet.assertOpt]; rfl

end Spec

/-! ## The concrete side: specs of the pieces of the walk -/

section Concrete
open Fl4Proofs.P0

private theorem bit_total (w n : U64) : capability.bit w n ⦃ _ => True ⦄ := by
  unfold capability.bit; p0_auto
private theorem unpack_total (w : U64) : capability.unpack_ptr w ⦃ _ => True ⦄ := by
  unfold capability.unpack_ptr; p0_auto
private theorem from_code_total (c : U64) : capability.FrameSize.from_code c ⦃ _ => True ⦄ := by
  unfold capability.FrameSize.from_code; p0_auto
private theorem unpack_asid_total (w0 sh w1 : U64) : capability.unpack_asid w0 sh w1 ⦃ _ => True ⦄ := by
  unfold capability.unpack_asid; p0_auto

attribute [local step] bit_total unpack_total from_code_total unpack_asid_total in
private theorem decode_total' (w0 w1 : U64) : capability.Cap.decode w0 w1 ⦃ _ => True ⦄ := by
  unfold capability.Cap.decode; p0_split

/-- `Cap::decode` never fails. -/
theorem decode_total (w0 w1 : U64) : ∃ c, capability.Cap.decode w0 w1 = ok c := by
  have := decode_total' w0 w1
  revert this
  cases capability.Cap.decode w0 w1 <;> simp [WP.spec_vis, WP.spec_div]

theorem capAt_total (mem : U64 → U64) (a : U64) : ∃ c, capAt mem a = ok c := decode_total _ _

@[step] theorem mask_spec (bits : U64) (h : bits.val < 64) :
    cspace.mask bits ⦃ m => m.val = 2 ^ bits.val - 1 ⦄ := by
  unfold cspace.mask
  have : ¬ (bits ≥ 64#u64) := by scalar_tac
  simp only [this, ite_false, lift, bind_ok]
  step*
  have h63 : (bits &&& 63#u64).val = bits.val := by
    have : (bits &&& 63#u64).val = bits.val % 64 := by
      simp; exact Nat.and_two_pow_sub_one_eq_mod bits.val 6
    omega
  have hp : 2 ^ bits.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) h
  have hp1 : 1 ≤ 2 ^ bits.val := Nat.one_le_two_pow
  have hi : i1.val = 2 ^ bits.val := by
    rw [i1_post, h63, Nat.one_shiftLeft]
    simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
    simpa using hp
  simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi]
  omega

@[step] theorem slot_index_spec (p i : U64) : obj.Slot.index p i ⦃ sl => sl = slotAddr p.bv i.bv ⦄ := by
  unfold obj.Slot.index
  simp only [lift, bind_ok, WP.spec_ok, slotAddr, UScalar.eq_equiv_bv_eq]
  simp [layout.cte.SIZE]

variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem slot_cap_eq (sl : obj.Slot) (s : S) : obj.Slot.cap st sl s = capAt (L.mem s) sl := by
  unfold obj.Slot.cap capAt
  simp [L.read_eq, lift]

@[step] theorem slot_cap_spec (sl : obj.Slot) (s : S) :
    obj.Slot.cap st sl s ⦃ c => capAt (L.mem s) sl = ok c ⦄ := by
  rw [slot_cap_eq]
  obtain ⟨c, hc⟩ := capAt_total (L.mem s) sl
  rw [hc]; simp

end Concrete

/-! ## Bit-level facts of one round -/

theorem guard_not_prefix {c n gs guard : Nat} (h : n < gs) : ¬ bitsOf guard gs <+: bitsOf c n := by
  intro hp; have := hp.length_le; simp at this; omega

theorem guard_prefix_iff {c n gs guard : Nat} (h : gs ≤ n) (hg : guard < 2 ^ gs) :
    bitsOf guard gs <+: bitsOf c n ↔ c / 2 ^ (n - gs) % 2 ^ gs = guard := by
  rw [List.prefix_iff_eq_take, length_bitsOf, bitsOf_take _ h, bitsOf_eq_iff, Nat.mod_eq_of_lt hg]
  exact eq_comm

/-- FL4's guard extraction `(cptr >> ((n - guard_size) & 63)) & mask(guard_size)`. -/
theorem guard_bits (c n gs : Nat) (h : gs ≤ n) (hn : n ≤ 64) :
    (c >>> ((n - gs) % 64)) &&& (2 ^ gs - 1) = c / 2 ^ (n - gs) % 2 ^ gs := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  by_cases h64 : n - gs = 64
  · have : gs = 0 := by omega
    subst this; simp [Nat.mod_one]
  · have : (n - gs) % 64 = n - gs := Nat.mod_eq_of_lt (by omega)
    rw [this]

/-- FL4's offset extraction `(cptr >> ((n - level) & 63)) & mask(radix)`. -/
theorem offset_bits (c n level radix : Nat) (h : level ≤ n) (h1 : 1 ≤ level) (hn : n ≤ 64) :
    (c >>> ((n - level) % 64)) &&& (2 ^ radix - 1) = c / 2 ^ (n - level) % 2 ^ radix := by
  have : (n - level) % 64 = n - level := Nat.mod_eq_of_lt (by omega)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, this]

/-- The spec's slot index, `take radix (drop (length guard) cref)`. -/
theorem offset_list (c n gs radix : Nat) (h : radix + gs ≤ n) :
    ((bitsOf c n).drop gs).take radix = bitsOf (c / 2 ^ (n - (radix + gs))) radix := by
  rw [bitsOf_drop _ (by omega), bitsOf_take _ (by omega)]
  congr 3; omega

theorem rest_list (c n level : Nat) (h : level ≤ n) : (bitsOf c n).drop level = bitsOf c (n - level) :=
  bitsOf_drop _ h

theorem bv_eq_ofNat (x : U64) : x.bv = BitVec.ofNat 64 x.val := by
  apply BitVec.eq_of_toNat_eq; simp

/-! ## The walk refines `resolve_address_bits'` -/

section Walk
variable {Z : Type}

/-- The spec's `resolve_address_bits'` run from `σ`: its outcomes and
failure flag. -/
abbrev rab (p : Fl4Spec.Cap × Fl4Spec.CapRef) (σ : Fl4Spec.State Z) :=
  (Fl4Spec.resolveAddressBits' (Z := Z) p).run σ

/-- Results of FL4's walk against outcomes of the spec's. -/
def ResRel : core.result.Result cspace.Resolved error.LookupFault →
    Except Fl4Spec.LookupFailure (Fl4Spec.CslotPtr × Fl4Spec.CapRef) → Prop
  | .Ok r, .ok (sl, rest) => r.slot = cslotAddr sl ∧ r.bits_left.val = rest.length
  | .Err lf, .error lf' => LookupFaultRel lf lf'
  | _, _ => False

/-- A slot the walk returns is a slot of a CNode of the typed heap, with an
index of the CNode's radix (what reading the cap there needs). -/
def SlotOk (th : TypedHeap) : Except Fl4Spec.LookupFailure (Fl4Spec.CslotPtr × Fl4Spec.CapRef) → Prop
  | .ok (sl, _) => ∃ p, sl.1 = p.bv ∧ th p = some (.cnode sl.2.length)
  | .error _ => True

/-- The walk's results against the spec's outcomes, with `SlotOk`. -/
def WalkRel (th : TypedHeap) (r : core.result.Result cspace.Resolved error.LookupFault)
    (e : Except Fl4Spec.LookupFailure (Fl4Spec.CslotPtr × Fl4Spec.CapRef)) : Prop :=
  ResRel r e ∧ SlotOk th e

/-- `m` (a spec computation run from `σ`) has exactly one outcome, `e`,
satisfying `P`, does not change the state and cannot fail. -/
def Single {α : Type} (m : Set (α × Fl4Spec.State Z) × Prop) (σ : Fl4Spec.State Z) (P : α → Prop) : Prop :=
  ∃ e, m = ({(e, σ)}, False) ∧ P e

variable (th : TypedHeap) (mem : U64 → U64) (σ : Fl4Spec.State Z) (cptr : U64)

/-- The loop invariant of the walk: from the current cap and depth, the spec
computes what it computes from the start `p0`. -/
def WalkInv (p0 : Fl4Spec.Cap × Fl4Spec.CapRef) (x : capability.Cap × U64 × U64) : Prop :=
  x.2.1.val ≤ 64 ∧ x.2.1.val < x.2.2.val ∧
  ∃ a, CapRel x.1 a ∧ CapValid th x.1 ∧ rab (a, bitsOf cptr.val x.2.1.val) σ = rab p0 σ

end Walk

section WalkProof
variable {Z : Type} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem body_spec (th : TypedHeap) (s : S) (σ : Fl4Spec.State Z) (hR : StateRel th (L.mem s) σ)
    (hV : SlotsValid th (L.mem s)) (cptr : U64) (p0 : Fl4Spec.Cap × Fl4Spec.CapRef)
    (cap : capability.Cap) (n fuel : U64) (hx : WalkInv th σ cptr p0 (cap, n, fuel)) :
    cspace.resolve_address_bits_loop.body st s cptr cap n fuel ⦃ r =>
      match r with
      | .done y => Single (rab p0 σ) σ (WalkRel th y)
      | .cont x' => WalkInv th σ cptr p0 x' ∧ x'.2.1.val < n.val ⦄ := by
  obtain ⟨hn, hf, a, ⟨hwf, rfl⟩, hcv, hrab⟩ := hx
  simp only at hn hf hrab hcv hwf ⊢
  rw [← hrab]
  cases cap
  case CNode ptr radix gs guard =>
    obtain ⟨hr, hgs, hg⟩ := hwf
    obtain ⟨hth, hr0⟩ := hcv
    unfold cspace.resolve_address_bits_loop.body
    have h0 : radix.val + (bitsOf guard.val gs.val).length ≠ 0 := by simp; omega
    step as ⟨level, hlev⟩
    have hl : level.val = radix.val + gs.val := by
      subst hlev
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
      omega
    split
    · exfalso; rename_i h; subst h; simp at hl; omega
    split
    · exfalso; rename_i h; subst h; simp at hf
    step as ⟨fuel1, hf1, hf1'⟩
    step as ⟨i, hi⟩
    step as ⟨shift, hsh, hsh'⟩
    step as ⟨i1, hi1, hi1'⟩
    step as ⟨i2, hi2⟩
    step as ⟨g, hgv, hgv'⟩
    split
    · -- not enough bits for the guard
      rename_i hgn
      simp only [WP.spec_ok]
      have hlt : n.val < gs.val := by scalar_tac
      refine ⟨_, rab_guard _ _ _ _ _ h0 (guard_not_prefix hlt), ?_⟩
      simp [WalkRel, ResRel, SlotOk, LookupFaultRel]
    have hgsn : gs.val ≤ n.val := by rename_i h; scalar_tac
    have hgval : g.val = cptr.val / 2 ^ (n.val - gs.val) % 2 ^ gs.val := by
      have hiv : i.val = n.val - gs.val := by
        have : n.val < 2 ^ 64 := by scalar_tac
        subst hi
        simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
        omega
      have hshv : shift.val = (n.val - gs.val) % 64 := by
        rw [hsh, ← hiv]; simp; exact Nat.and_two_pow_sub_one_eq_mod i.val 6
      rw [hgv]; simp only [UScalar.val_and]; rw [hi1, hi2, hshv]
      exact guard_bits _ _ _ hgsn hn
    have hpre : bitsOf guard.val gs.val <+: bitsOf cptr.val n.val ↔ g = guard := by
      rw [guard_prefix_iff hgsn hg, ← hgval, UScalar.eq_equiv]
    split
    · -- guard mismatch
      rename_i hne
      simp only [WP.spec_ok]
      have hne' : g ≠ guard := by simpa using hne
      refine ⟨_, rab_guard _ _ _ _ _ h0 (fun h => hne' (hpre.1 h)), ?_⟩
      simp [WalkRel, ResRel, SlotOk, LookupFaultRel]
    have hp : bitsOf guard.val gs.val <+: bitsOf cptr.val n.val := hpre.2 (by rename_i h; exact UScalar.eq_of_val_eq (by simpa using h))
    split
    · -- not enough bits for the level
      rename_i hgt
      simp only [WP.spec_ok]
      have : n.val < level.val := by scalar_tac
      refine ⟨_, rab_depth _ _ _ _ _ h0 hp (by simp; omega), ?_⟩
      simp [WalkRel, ResRel, SlotOk, LookupFaultRel, hl]
    have hln : level.val ≤ n.val := by rename_i h; scalar_tac
    step as ⟨i3, hi3, hi3'⟩
    step as ⟨i4, hi4, hi4'⟩
    step as ⟨i5, hi5, hi5'⟩
    step as ⟨i6, hi6⟩
    step as ⟨offset, hoff, hoff'⟩
    step as ⟨slot, hslot⟩
    have hofv : offset.val = cptr.val / 2 ^ (n.val - (radix.val + gs.val)) % 2 ^ radix.val := by
      have hi4v : i4.val = (n.val - level.val) % 64 := by
        rw [hi4, ← hi3]; simp; exact Nat.and_two_pow_sub_one_eq_mod _ 6
      rw [hoff]; simp only [UScalar.val_and]; rw [hi5, hi6, hi4v, ← hl]
      exact offset_bits _ _ _ _ hln (by omega) hn
    have hoffL : ((bitsOf cptr.val n.val).drop (bitsOf guard.val gs.val).length).take radix.val =
        bitsOf (cptr.val / 2 ^ (n.val - (radix.val + gs.val))) radix.val := by
      rw [length_bitsOf]; exact offset_list _ _ _ _ (by omega)
    have hslotN : slot = slotAddr ptr.bv
        (BitVec.ofNat 64 (cptr.val / 2 ^ (n.val - (radix.val + gs.val)) % 2 ^ radix.val)) := by
      rw [hslot, bv_eq_ofNat offset, hofv]
    have hslot' : slot = cslotAddr (ptr.bv, bitsOf (cptr.val / 2 ^ (n.val - (radix.val + gs.val))) radix.val) := by
      rw [hslotN, cslotAddr, ofBl_bitsOf_eq]
    split
    · -- all bits resolved
      rename_i heq
      simp only [WP.spec_ok]
      have hnl : n.val = level.val := by rw [heq]
      have hr' : (bitsOf cptr.val n.val).drop (radix.val + (bitsOf guard.val gs.val).length) = [] := by
        rw [length_bitsOf, rest_list _ _ _ (by omega), bitsOf_eq_nil]; omega
      refine ⟨_, rab_last _ _ _ _ _ h0 hp (by simp; omega) hr', ?_⟩
      simp only [WalkRel, ResRel, SlotOk]; rw [hoffL]; exact ⟨⟨hslot', by simp⟩, ptr, rfl, by simpa using hth⟩
    have hlt : level.val < n.val := by
      rename_i h; have : n.val ≠ level.val := fun e => h (UScalar.eq_of_val_eq e); omega
    obtain ⟨cs, c, a', hk, hwf, hca', hcap, hrel, hval⟩ :=
      hR.cnode_slot hV hth (cptr.val / 2 ^ (n.val - (radix.val + gs.val)))
    rw [← hslotN] at hcap
    have hget : Fl4Spec.getCap (Z := Z) (ptr.bv,
        ((bitsOf cptr.val n.val).drop (bitsOf guard.val gs.val).length).take radix.val) σ = ({(a', σ)}, False) := by
      rw [hoffL]; exact getCap_cnode hk hwf hca'
    have hrest : (bitsOf cptr.val n.val).drop (radix.val + (bitsOf guard.val gs.val).length) =
        bitsOf cptr.val i3.val := by
      rw [length_bitsOf, rest_list _ _ _ (by omega), hi3, hl]
    have hnil : (bitsOf cptr.val n.val).drop (radix.val + (bitsOf guard.val gs.val).length) ≠ [] := by
      rw [hrest, ne_eq, bitsOf_eq_nil]; omega
    have hstep := rab_next (Z := Z) ptr.bv radix.val (bitsOf guard.val gs.val) (bitsOf cptr.val n.val) σ a' h0 hp
      (by simp; omega) hnil hget
    rw [hrest, hoffL] at hstep
    have hdone : Fl4Spec.isCnodeCap a' = false →
        Single (rab (absCap (.CNode ptr radix gs guard), bitsOf cptr.val n.val) σ) σ
          (WalkRel th (.Ok { slot := slot, bits_left := i3 })) := by
      intro hc
      refine ⟨.ok ((ptr.bv, bitsOf (cptr.val / 2 ^ (n.val - (radix.val + gs.val))) radix.val),
        bitsOf cptr.val i3.val), ?_, ?_⟩
      · show (Fl4Spec.resolveAddressBits' _).run σ = _
        rw [show absCap (.CNode ptr radix gs guard) = .cnodeCap ptr.bv radix.val (bitsOf guard.val gs.val) from rfl,
          hstep, hc]
        rfl
      · exact ⟨⟨hslot', by simp⟩, ptr, rfl, by simpa using hth⟩
    have hcont : Fl4Spec.isCnodeCap a' = true →
        rab (a', bitsOf cptr.val i3.val) σ = rab p0 σ := by
      intro hc
      rw [← hrab]
      show _ = (Fl4Spec.resolveAddressBits' _).run σ
      rw [show absCap (.CNode ptr radix gs guard) = .cnodeCap ptr.bv radix.val (bitsOf guard.val gs.val) from rfl,
        hstep, hc]
      rfl
    step as ⟨next, hnext⟩
    have : next = c := by rw [hcap] at hnext; simpa [eq_comm] using hnext
    subst this
    have ha' := hrel.abs
    cases next
    case CNode p' r' gs' g' =>
      simp only [WP.spec_ok]
      exact ⟨⟨show i3.val ≤ 64 by omega, show i3.val < fuel1.val by omega, a', hrel, hval,
        hcont (by rw [ha']; rfl)⟩, show i3.val < n.val by omega⟩
    all_goals
      simp only [WP.spec_ok]
      exact hdone (by rw [ha']; rfl)
  all_goals
    unfold cspace.resolve_address_bits_loop.body
    simp only [WP.spec_ok]
    exact ⟨_, rab_noncnode _ _ _ rfl, trivial, trivial⟩

/-- **FL4's `resolve_address_bits` refines l4v `resolve_address_bits'`.**
For related states, a related and valid root cap and a depth `n ≤ 64`, the
spec resolving the low `n` bits of `cptr` has exactly one outcome, does not
fail and does not change the state, and FL4's result corresponds to it: the
same slot and number of bits left, or the corresponding lookup fault. -/
theorem resolve_address_bits_refines (th : TypedHeap) (s : S) (σ : Fl4Spec.State Z)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s))
    (c : capability.Cap) (a : Fl4Spec.Cap) (hc : CapRel c a) (hcv : CapValid th c)
    (cptr n : U64) (hn : n.val ≤ 64) :
    cspace.resolve_address_bits st s c cptr n ⦃ r =>
      Single (rab (a, bitsOf cptr.val n.val) σ) σ (WalkRel th r) ⦄ := by
  unfold cspace.resolve_address_bits cspace.resolve_address_bits_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.1.val)
    (inv := WalkInv th σ cptr (a, bitsOf cptr.val n.val))
  · rintro ⟨c1, n1, f1⟩ hx
    have h := body_spec th s σ hR hV cptr _ c1 n1 f1 hx
    convert h using 2
    rename_i r; cases r <;> rfl
  · exact ⟨hn, by simp; omega, a, hc, hcv, rfl⟩

end WalkProof

/-! ## `lookup_slot`, `lookup_cap`, `lookup_cap_and_slot` -/

section SpecLookup
open Fl4Spec
variable {Z : Type}

theorem tcbCnodeMap_ctable (tcb : Tcb) : tcbCnodeMap tcb (tcbCnodeIndex 0) = some tcb.tcbCtable := by
  have h1 : tcbCnodeIndex 0 ≠ tcbCnodeIndex 1 := by decide
  have h2 : tcbCnodeIndex 0 ≠ tcbCnodeIndex 2 := by decide
  have h3 : tcbCnodeIndex 0 ≠ tcbCnodeIndex 3 := by decide
  have h4 : tcbCnodeIndex 0 ≠ tcbCnodeIndex 4 := by decide
  have h5 : tcbCnodeIndex 0 ≠ tcbCnodeIndex 5 := by decide
  simp [tcbCnodeMap, h1, h2, h3, h4, h5]

theorem lookupSlotForThread_eq {σ : State Z} {t : ObjRef} {tcb : Tcb} (hk : σ.kheap t = some (.tcb tcb))
    (cref : CapRef) :
    (lookupSlotForThread (Z := Z) t cref).run σ = (resolveAddressBits' (Z := Z) (tcb.tcbCtable, cref)).run σ := by
  unfold lookupSlotForThread resolveAddressBits NonDetE.liftE
  rw [ExceptT.run_bind, ExceptT.run_lift]
  have h1 : (Except.ok <$> NonDet.getsThe (getTcb (Z := Z) t) : NonDet (State Z) (Except LookupFailure Tcb)) σ =
      ({(.ok tcb, σ)}, False) := by
    show (NonDet.getsThe _ >>= _) σ = _
    rw [nd_bind_single (getTcb_ctable hk)]; rfl
  rw [nd_bind_single h1]

section
variable {σ α β ε : Type}

theorem run_bind_ok {m : NonDetE σ ε α} {s : σ} {a : α} (h : m.run s = ({(.ok a, s)}, False))
    (f : α → NonDetE σ ε β) : (m >>= f).run s = (f a).run s := by
  rw [ExceptT.run_bind, nd_bind_single h]

theorem run_bind_error {m : NonDetE σ ε α} {s : σ} {e : ε} (h : m.run s = ({(.error e, s)}, False))
    (f : α → NonDetE σ ε β) : (m >>= f).run s = ({(.error e, s)}, False) := by
  rw [ExceptT.run_bind, nd_bind_single h]; rfl

theorem run_liftE {m : NonDet σ α} {s : σ} {a : α} (h : m s = ({(a, s)}, False)) :
    (NonDetE.liftE (ε := ε) m).run s = ({(.ok a, s)}, False) := by
  unfold NonDetE.liftE
  rw [ExceptT.run_lift]
  show (m >>= _) s = _
  rw [nd_bind_single h]; rfl

end

/-- What `lookup_slot_for_cnode_op` makes of the walk's outcome. -/
def cnodeOpOutcome (b : Bool) : Except LookupFailure (CslotPtr × CapRef) → Except SyscallError CslotPtr
  | .ok (sl, []) => .ok sl
  | .ok (_, rem) => .error (.failedLookup b (.depthMismatch rem.length 0))
  | .error lf => .error (.failedLookup b lf)

theorem lsfco_noncnode (b : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) (σ : State Z)
    (h : isCnodeCap croot = false) :
    (lookupSlotForCnodeOp (Z := Z) b croot ptr depth).run σ = ({(.error (.failedLookup b .invalidRoot), σ)}, False) := by
  unfold lookupSlotForCnodeOp; simp only [h, Bool.false_eq_true, ↓reduceIte]; rfl

theorem lsfco_range (b : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) (σ : State Z)
    (h : isCnodeCap croot = true) (hd : depth < 1 ∨ depth > wordBits) :
    (lookupSlotForCnodeOp (Z := Z) b croot ptr depth).run σ =
      ({(.error (.rangeError 1 (BitVec.ofNat 64 wordBits)), σ)}, False) := by
  unfold lookupSlotForCnodeOp; simp only [h, NonDetE.whenE, hd, ↓reduceIte, NonDetE.throwError, ndE_throw_bind]; rfl

theorem lsfco_walk (b : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) (σ : State Z)
    (h : isCnodeCap croot = true) (hd : ¬ (depth < 1 ∨ depth > wordBits)) {e}
    (hw : (resolveAddressBits' (Z := Z) (croot, ptr.drop (ptr.length - depth))).run σ = ({(e, σ)}, False)) :
    (lookupSlotForCnodeOp (Z := Z) b croot ptr depth).run σ = ({(cnodeOpOutcome b e, σ)}, False) := by
  unfold lookupSlotForCnodeOp; simp only [h, NonDetE.whenE, hd, ↓reduceIte, ndE_pure_bind]
  unfold lookupErrorOnFailure NonDetE.handleE NonDetE.returnOk resolveAddressBits
  rw [ndE_pure_bind]
  have hm : ∃ e', (resolveAddressBits' (Z := Z) (croot, ptr.drop (ptr.length - depth)) >>= fun __x =>
      match __x.2 with
      | [] => (pure __x.1 : LFMonad Z CslotPtr)
      | _ => NonDetE.throwError (LookupFailure.depthMismatch __x.2.length 0)).run σ = ({(e', σ)}, False) ∧
      cnodeOpOutcome b e = (match e' with | .ok a => .ok a | .error lf => .error (.failedLookup b lf)) := by
    cases e with
    | ok v =>
      obtain ⟨sl, rem⟩ := v
      rw [run_bind_ok hw]
      cases rem with
      | nil => exact ⟨.ok sl, rfl, rfl⟩
      | cons r rs => exact ⟨.error (.depthMismatch (r :: rs).length 0), rfl, rfl⟩
    | error lf => exact ⟨.error lf, run_bind_error hw _, rfl⟩
  obtain ⟨e', he', hout⟩ := hm
  rw [ExceptT.run_mk]
  refine (nd_bind_single' (a := e') ?_ _).trans ?_
  · exact he'
  · rw [hout]; cases e' <;> rfl

end SpecLookup

section LookupProof
variable {Z : Type} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

@[step] theorem tcb_slot_spec (t i : U64) : obj.Tcb.slot t i ⦃ sl => sl = slotAddr t.bv i.bv ⦄ := by
  unfold obj.Tcb.slot
  simp only [lift, bind_ok, WP.spec_ok, slotAddr, UScalar.eq_equiv_bv_eq]
  simp [layout.cte.SIZE]

/-- The root CNode cap of a TCB of the typed heap is related to the spec's
`tcb_ctable` and valid. -/
theorem StateRel.ctable {th : TypedHeap} {s : S} {σ : Fl4Spec.State Z}
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) {t : U64} (ht : th t = some .tcb) :
    ∃ tcb c, σ.kheap t.bv = some (.tcb tcb) ∧ capAt (L.mem s) (slotAddr t.bv 0#64) = ok c ∧
      CapRel c tcb.tcbCtable ∧ CapValid th c := by
  obtain ⟨tcb, hk, hs⟩ := hR.tcb t ht
  obtain ⟨c, ac, hc, hac, hrel⟩ := hs 0 (by decide)
  rw [tcbCnodeMap_ctable] at hac
  cases hac
  exact ⟨tcb, c, hk, hc, hrel, hV.tcb t ht 0 (by decide) c hc⟩

/-- **FL4's `lookup_slot` refines l4v `lookup_slot_for_thread`** at the
64-bit capability pointer `to_bl cptr`, for a thread of the typed heap. -/
theorem lookup_slot_refines (th : TypedHeap) (s : S) (σ : Fl4Spec.State Z)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (t : U64) (ht : th t = some .tcb)
    (cptr : U64) :
    cspace.lookup_slot st s t cptr ⦃ r =>
      Single ((Fl4Spec.lookupSlotForThread (Z := Z) t.bv (Fl4Spec.toBl cptr.bv)).run σ) σ (WalkRel th r) ⦄ := by
  obtain ⟨tcb, c, hk, hc, hrel, hval⟩ := hR.ctable hV ht
  rw [lookupSlotForThread_eq hk, toBl_eq_bitsOf]
  unfold cspace.lookup_slot
  step as ⟨sl, hsl⟩
  rw [slot_cap_eq, hsl, show (layout.tcb.SLOT_CTABLE.bv : BitVec 64) = 0#64 by simp [layout.tcb.SLOT_CTABLE], hc]
  simp only [bind_ok]
  have := resolve_address_bits_refines th s σ hR hV c _ hrel hval cptr cspace.WORD_BITS
    (by simp [cspace.WORD_BITS])
  simpa [cspace.WORD_BITS] using this

/-- FL4's `lookup_cap` results against the spec's: a related cap, or the
corresponding lookup fault as `Exc::Lookup`. -/
def CapResRel : core.result.Result capability.Cap error.Exc → Except Fl4Spec.LookupFailure Fl4Spec.Cap → Prop
  | .Ok c, .ok a => CapRel c a
  | .Err (.Lookup lf), .error lf' => LookupFaultRel lf lf'
  | _, _ => False

/-- `lookup_cap_and_slot` results: a related cap and the slot's address. -/
def CapSlotResRel : core.result.Result (capability.Cap × obj.Slot) error.Exc →
    Except Fl4Spec.LookupFailure (Fl4Spec.Cap × Fl4Spec.CslotPtr) → Prop
  | .Ok (c, sl), .ok (a, sl') => CapRel c a ∧ sl = cslotAddr sl'
  | .Err (.Lookup lf), .error lf' => LookupFaultRel lf lf'
  | _, _ => False

/-- The cap at a slot the walk returned. -/
theorem StateRel.slot_cap {th : TypedHeap} {s : S} {σ : Fl4Spec.State Z}
    (hR : StateRel th (L.mem s) σ) {sl : Fl4Spec.CslotPtr} {p : U64} (hp : sl.1 = p.bv)
    (hth : th p = some (.cnode sl.2.length)) :
    ∃ c a, capAt (L.mem s) (cslotAddr sl) = ok c ∧ CapRel c a ∧
      Fl4Spec.getCap (Z := Z) sl σ = ({(a, σ)}, False) := by
  obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode p _ hth
  obtain ⟨c, a, hc, ha, hrel⟩ := hs sl.2 rfl
  obtain ⟨o, i⟩ := sl
  simp only at hp; subst hp
  exact ⟨c, a, hc, hrel, getCap_cnode hk hwf ha⟩

/-- **FL4's `lookup_cap` refines l4v `lookup_cap`.** -/
theorem lookup_cap_refines (th : TypedHeap) (s : S) (σ : Fl4Spec.State Z)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (t : U64) (ht : th t = some .tcb)
    (cptr : U64) :
    cspace.lookup_cap st s t cptr ⦃ r =>
      Single ((Fl4Spec.lookupCap (Z := Z) t.bv (Fl4Spec.toBl cptr.bv)).run σ) σ (CapResRel r) ⦄ := by
  unfold cspace.lookup_cap
  step with lookup_slot_refines th s σ hR hV t ht cptr as ⟨r, hr⟩
  obtain ⟨e, he, hrel, hok⟩ := hr
  unfold Fl4Spec.lookupCap
  cases r with
  | Ok r1 =>
    cases e with
    | ok v =>
      obtain ⟨sl, rest⟩ := v
      obtain ⟨hsl, -⟩ := hrel
      obtain ⟨p, hp, hth⟩ := hok
      obtain ⟨c, a, hc, hca, hget⟩ := hR.slot_cap hp hth
      simp only
      rw [slot_cap_eq, hsl, hc]
      simp only [bind_ok, WP.spec_ok]
      exact ⟨.ok a, by rw [run_bind_ok he]; exact run_liftE hget, hca⟩
    | error lf' => exact hrel.elim
  | Err lf =>
    cases e with
    | ok v => exact hrel.elim
    | error lf' =>
      simp only [WP.spec_ok]
      exact ⟨.error lf', run_bind_error he _, hrel⟩

/-- **FL4's `lookup_cap_and_slot` refines l4v `lookup_cap_and_slot`.** -/
theorem lookup_cap_and_slot_refines (th : TypedHeap) (s : S) (σ : Fl4Spec.State Z)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (t : U64) (ht : th t = some .tcb)
    (cptr : U64) :
    cspace.lookup_cap_and_slot st s t cptr ⦃ r =>
      Single ((Fl4Spec.lookupCapAndSlot (Z := Z) t.bv (Fl4Spec.toBl cptr.bv)).run σ) σ (CapSlotResRel r) ⦄ := by
  unfold cspace.lookup_cap_and_slot
  step with lookup_slot_refines th s σ hR hV t ht cptr as ⟨r, hr⟩
  obtain ⟨e, he, hrel, hok⟩ := hr
  unfold Fl4Spec.lookupCapAndSlot
  cases r with
  | Ok r1 =>
    cases e with
    | ok v =>
      obtain ⟨sl, rest⟩ := v
      obtain ⟨hsl, -⟩ := hrel
      obtain ⟨p, hp, hth⟩ := hok
      obtain ⟨c, a, hc, hca, hget⟩ := hR.slot_cap hp hth
      simp only
      rw [slot_cap_eq, hsl, hc]
      simp only [bind_ok, WP.spec_ok]
      refine ⟨.ok (a, sl), ?_, hca, rfl⟩
      rw [run_bind_ok he]
      simp only
      rw [run_bind_ok (run_liftE hget)]
      rfl
    | error lf' => exact hrel.elim
  | Err lf =>
    cases e with
    | ok v => exact hrel.elim
    | error lf' =>
      simp only [WP.spec_ok]
      exact ⟨.error lf', run_bind_error he _, hrel⟩

/-- Syscall errors (the cases `lookup_slot_for_cnode_op` and the CNode
invocations produce; the other constructors are related as later
subsystems need them). -/
def SysErrRel : error.Exc → Fl4Spec.SyscallError → Prop
  | .Sys (.RangeError mn mx), .rangeError mn' mx' => mn' = mn.bv ∧ mx' = mx.bv
  | .Sys (.FailedLookup src lf), .failedLookup src' lf' => src' = src ∧ LookupFaultRel lf lf'
  | .Sys .IllegalOperation, .illegalOperation => True
  | .Sys .AlignmentError, .alignmentError => True
  | .Sys (.InvalidArgument n), .invalidArgument n' => n' = n.val
  | .Sys (.NotEnoughMemory b), .notEnoughMemory b' => b' = b.bv
  | .Sys .TruncatedMessage, .truncatedMessage => True
  | .Sys .DeleteFirst, .deleteFirst => True
  | .Sys .RevokeFirst, .revokeFirst => True
  | _, _ => False

/-- `lookup_slot_for_cnode_op` results: the slot's address (a slot of a
CNode of the typed heap), or the corresponding syscall error. -/
def SlotResRel (th : TypedHeap) : core.result.Result obj.Slot error.Exc →
    Except Fl4Spec.SyscallError Fl4Spec.CslotPtr → Prop
  | .Ok sl, .ok sl' => sl = cslotAddr sl' ∧ ∃ p, sl'.1 = p.bv ∧ th p = some (.cnode sl'.2.length)
  | .Err e, .error e' => SysErrRel e e'
  | _, _ => False

/-- **FL4's `lookup_slot_for_cnode_op` refines l4v
`lookup_slot_for_cnode_op`** (and so `lookup_source_slot`,
`lookup_target_slot`, `lookup_pivot_slot`), for a related, valid root cap,
the 64-bit capability pointer `to_bl cptr` and any depth word. -/
theorem lookup_slot_for_cnode_op_refines (th : TypedHeap) (s : S) (σ : Fl4Spec.State Z)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (b : Bool)
    (root : capability.Cap) (a : Fl4Spec.Cap) (hc : CapRel root a) (hcv : CapValid th root)
    (cptr depth : U64) :
    cspace.lookup_slot_for_cnode_op st s b root cptr depth ⦃ r =>
      Single ((Fl4Spec.lookupSlotForCnodeOp (Z := Z) b a (Fl4Spec.toBl cptr.bv) depth.val).run σ) σ
        (SlotResRel th r) ⦄ := by
  obtain ⟨hwf, rfl⟩ := hc
  unfold cspace.lookup_slot_for_cnode_op
  cases root
  case CNode ptr radix gs guard =>
    have hcn : Fl4Spec.isCnodeCap (absCap (.CNode ptr radix gs guard)) = true := rfl
    simp only [bind_ok, ↓reduceIte]
    by_cases h1 : depth < 1#u64
    · simp only [h1, ↓reduceIte, WP.spec_ok]
      refine ⟨_, lsfco_range _ _ _ _ σ hcn (Or.inl (by scalar_tac)), ?_⟩
      simp [SlotResRel, SysErrRel, cspace.WORD_BITS, Fl4Spec.wordBits]
    by_cases h2 : depth > cspace.WORD_BITS
    · simp only [h1, h2, ↓reduceIte, WP.spec_ok]
      refine ⟨_, lsfco_range _ _ _ _ σ hcn (Or.inr ?_), ?_⟩
      · simp [cspace.WORD_BITS] at h2; simp [Fl4Spec.wordBits]; scalar_tac
      · simp [SlotResRel, SysErrRel, cspace.WORD_BITS, Fl4Spec.wordBits]
    simp only [h1, h2, ↓reduceIte]
    have hd : depth.val ≤ 64 := by simp [cspace.WORD_BITS] at h2; scalar_tac
    have hd' : ¬ (depth.val < 1 ∨ depth.val > Fl4Spec.wordBits) := by
      simp [Fl4Spec.wordBits]; constructor
      · scalar_tac
      · omega
    step with resolve_address_bits_refines th s σ hR hV _ _ ⟨hwf, rfl⟩ hcv cptr depth hd as ⟨r, hr⟩
    obtain ⟨e, he, hrel, hok⟩ := hr
    have hlen : (Fl4Spec.toBl cptr.bv).length = 64 := by simp [toBl_eq_bitsOf]
    rw [lsfco_walk _ _ _ _ σ hcn hd' (e := e) (by rw [hlen, toBl_drop _ _ hd]; exact he)]
    cases r with
    | Ok r1 =>
      cases e with
      | error lf => exact hrel.elim
      | ok v =>
        obtain ⟨sl, rest⟩ := v
        obtain ⟨hsl, hbl⟩ := hrel
        by_cases hz : r1.bits_left = 0#u64
        · have hrest : rest = [] := by
            rw [← List.length_eq_zero_iff, ← hbl, hz]; rfl
          subst hrest
          simp only [hz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          exact ⟨_, rfl, hsl, hok⟩
        · have hne : (r1.bits_left != 0#u64) = true := by simpa using hz
          simp only [hne, ↓reduceIte, WP.spec_ok]
          cases rest with
          | nil => exact absurd (UScalar.eq_of_val_eq (by simpa using hbl)) hz
          | cons x xs =>
            refine ⟨_, rfl, ?_⟩
            simp [SlotResRel, SysErrRel, LookupFaultRel, cnodeOpOutcome, hbl]
    | Err lf =>
      cases e with
      | ok v => exact hrel.elim
      | error lf' =>
        simp only [WP.spec_ok]
        exact ⟨_, rfl, rfl, hrel⟩
  all_goals
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨_, lsfco_noncnode _ _ _ _ σ rfl, rfl, trivial⟩

end LookupProof

end Fl4Proofs.P3
