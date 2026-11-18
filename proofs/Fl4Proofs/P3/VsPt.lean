/-
P3 (DESIGN.md §9), VSpace: **page tables and the page-table walk**.

FL4's page tables are 4K frames of 512 x86 entries; l4v has `PageMapL4`,
`PDPointerTable`, `PageDirectory` and `PageTable` objects of 512 `PML4E` /
`PDPTE` / `PDE` / `PTE`. The relation (`PtRel`) is over ghost sets of the
tables of each level, `L4 L3 L2 L1`: entry `i` of a table at `p` is the
word at `peA p i`, related by `PML4ERel` … `PTERel`:
* not present (bit 0 clear) ↔ the invalid entry;
* a present entry for a table of the next level: the physical address bits
  (`& ADDR_MASK`) are the spec's (physical) table pointer, and the table
  (`pptr` of it) is in the next ghost set; at the PDPT and PD level the
  page-size bit (7) is clear;
* a present huge/large page entry (PS set) ↔ `hugePagePDPTE` /
  `largePagePDE`; a present PTE ↔ `smallPagePTE`; the frame is the address
  bits (`frame_base`: `lA`, `hA` for large and huge pages), the rights
  (`US`, `RW`: `PteRights`) and the cache attributes (`PWT`, `PCD`, `PAT`:
  `PteAttrs`, `PteAttrsL`; `PteAttrsH` without PAT, which l4v drops for huge
  pages).

The walk: `lookup_pdpt_slot_rel`, `lookup_pd_slot_rel`, `lookup_pt_slot_rel`
against l4v `lookup_pdpt_slot` / `lookup_pd_slot` / `lookup_pt_slot`: the
same slot (an entry of a table of the right level) or the same
`MissingCapability` fault, and the spec does not fail.
-/
import Fl4Proofs.P3.VsDelRoot
import Mathlib.Tactic.NormNum
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

/-- Removing the visibility bits recovers an untagged GPA for either polarity. -/
theorem untag_address (pa priv sh : BitVec 64) (hg : pa &&& (priv ||| sh) = 0) (tag : BitVec 64)
    (ht : tag = priv ∨ tag = sh) : (pa ||| tag) &&& ~~~(priv ||| sh) = pa := by
  have clear : pa &&& ~~~(priv ||| sh) = pa := by
    calc
      _ = (pa &&& (priv ||| sh)) ||| (pa &&& ~~~(priv ||| sh)) := by simp [hg]
      _ = pa := by rw [← BitVec.and_or_distrib_left, BitVec.or_not_self, BitVec.and_allOnes]
  have drop (x y : BitVec 64) : x &&& ~~~(x ||| y) = 0 := by
    rw [BitVec.not_or, ← BitVec.and_assoc, BitVec.and_not_self]; simp
  rw [BitVec.and_or_distrib_right, clear]
  rcases ht with ht | ht
  · rw [ht, drop]; simp
  · rw [ht, BitVec.or_comm priv sh, drop]; simp

/-- Frame leaf selection and GPA recovery, including private firmware device caps. -/
theorem sev_frame_address {S A : Type} (st : machine.Store S) (ar : machine.Arch A)
    (s : S) (a : A) (f : vspace.FrameCap) (pa priv sh : U64) (firmware : Bool)
    (hp : layout.paddr f.ptr = ok pa) (hm : st.frame_masks s = ok (priv, sh))
    (hen : priv ||| sh ≠ 0#u64) (hgpa : pa.bv &&& (priv.bv ||| sh.bv) = 0)
    (hd : ar.private_device_frame a pa = ok firmware) :
    let tag := if f.is_device && !firmware then sh else priv
    vspace.frame_address st ar s a f = ok (pa ||| tag) ∧ vspace.frame_gpa st s (pa ||| tag) = ok pa := by
  have recover (tag : U64) (ht : tag.bv = priv.bv ∨ tag.bv = sh.bv) :
      (pa ||| tag) &&& ~~~(priv ||| sh) = pa := eq_of_bv (untag_address _ _ _ hgpa _ ht)
  cases hf : f.is_device <;> cases firmware <;>
    simp [vspace.frame_address, vspace.frame_gpa, hp, hm, hf, hd, lift, recover priv (Or.inl rfl), recover sh (Or.inr rfl)] <;>
    rintro rfl rfl <;> exact False.elim (hen rfl)

theorem frame_address_plain {S A : Type} {st : machine.Store S} [PlainStore st] (ar : machine.Arch A)
    (s : S) (a : A) (f : vspace.FrameCap) : vspace.frame_address st ar s a f = layout.paddr f.ptr := by
  simp [vspace.frame_address, layout.paddr, PlainStore.frame_masks_eq, lift]

/-- On the native address format, reading a leaf returns its GPA. -/
theorem frame_gpa_plain {S : Type} {st : machine.Store S} [PlainStore st] (s : S) (p : U64) :
    vspace.frame_gpa st s p = ok p := by
  simp only [vspace.frame_gpa, PlainStore.frame_masks_eq, lift, bind_ok]
  change ok (p &&& ~~~(0#u64 ||| 0#u64)) = ok p
  congr 1
  apply eq_of_bv
  change p.bv &&& BitVec.allOnes 64 = p.bv
  exact BitVec.and_allOnes

/-! ## Bits -/

theorem nat_and_hi (n : Nat) (hn : n < 2 ^ 64) : n &&& (2 ^ 64 - 1 - (2 ^ 12 - 1)) = 2 ^ 12 * (n / 2 ^ 12) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show (2 ^ 64 - 1 - (2 ^ 12 - 1) : Nat) = 2 ^ 12 * (2 ^ 52 - 1) by norm_num,
    Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h : 12 ≤ i
  · have : i - 12 + 12 = i := by omega
    rw [this]
    by_cases h2 : i < 64
    · simp [h, show i - 12 < 52 by omega]
    · have : n.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [h, this]
  · simp [h]

theorem mask12 : (Fl4Spec.mask 12 : BitVec 64).toNat = 2 ^ 12 - 1 := by decide

theorem base_eq (p o : BitVec 64) (hp : p.toNat % 4096 = 0) (ho : o.toNat < 4096) :
    (p + o) &&& ~~~(Fl4Spec.mask 12) = p := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_not, mask12, BitVec.toNat_add,
    Nat.mod_eq_of_lt (show p.toNat + o.toNat < 2 ^ 64 by omega), nat_and_hi _ (by omega)]
  omega

theorem off_eq (p o : BitVec 64) (hp : p.toNat % 4096 = 0) (ho : o.toNat < 4096) :
    ((p + o) &&& Fl4Spec.mask 12).toNat = o.toNat := by
  rw [BitVec.toNat_and, mask12, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_add,
    Nat.mod_eq_of_lt (show p.toNat + o.toNat < 2 ^ 64 by omega)]
  omega

/-- Splitting the address of entry `j` of the table at `q` (l4v
`get_pml4e` & co.): the table and the index. -/
theorem split_slot (q j : BitVec 64) (hq : q.toNat % 4096 = 0) (hj : j.toNat < 512) :
    (q + (j <<< Fl4Spec.wordSizeBits)) &&& ~~~(Fl4Spec.mask 12) = q ∧
    (Fl4Spec.ucast 9 (((q + (j <<< Fl4Spec.wordSizeBits)) &&& Fl4Spec.mask 12) >>> Fl4Spec.wordSizeBits) : BitVec 9) =
      Fl4Spec.ucast 9 j := by
  have hs : (j <<< Fl4Spec.wordSizeBits).toNat = j.toNat * 8 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [Fl4Spec.wordSizeBits]
    rw [Nat.mod_eq_of_lt (by omega)]
  refine ⟨base_eq _ _ hq (by omega), ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [Fl4Spec.ucast, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  rw [off_eq _ _ hq (by omega), hs]
  simp [Fl4Spec.wordSizeBits, Nat.shiftRight_eq_div_pow]

/-! ## Entries -/

/-- The present bit, the page-size bit and the address bits of an entry. -/
def eP (w : U64) : Prop := (w &&& 1#u64) ≠ 0#u64
def eS (w : U64) : Prop := (w &&& 128#u64) ≠ 0#u64
def eA (w : U64) : U64 := w &&& 4503599627366400#u64
/-- The kernel pointer of a table at physical address `eA w` (`layout::pptr`). -/
def eT (w : U64) : U64 := core.num.U64.wrapping_add (eA w) 18446743523953737728#u64

/-- Bit `k` of a word. -/
def bitL (w : U64) (k : Nat) : Bool := w.bv.getLsbD k

/-- The frame address of a large (2M) page entry (`vspace::frame_base`). -/
def lA (w : U64) : U64 := w &&& 4503599625273344#u64
/-- The frame address of a huge (1G) page entry. -/
def hA (w : U64) : U64 := w &&& 4503598553628672#u64

/-- The rights of a page entry: `US` clear is kernel-only, else `RW` set is
read-write, clear read-only. -/
def PteRights (w : U64) (r : Fl4Spec.VMRights) : Prop :=
  r = if bitL w 2 = false then Fl4Spec.vmKernelOnly else if bitL w 1 then Fl4Spec.vmReadWrite else Fl4Spec.vmReadOnly

/-- The cache attributes of a page entry (`PWT`, `PCD`, `PAT`). -/
def PteAttrs (w : U64) (a : Fl4Spec.VMAttributes) : Prop :=
  (Fl4Spec.VMAttribute.ptAttr .writeThrough ∈ a ↔ bitL w 3 = true) ∧
  (Fl4Spec.VMAttribute.ptAttr .cacheDisabled ∈ a ↔ bitL w 4 = true) ∧ (Fl4Spec.VMAttribute.pat ∈ a ↔ bitL w 7 = true)

/-- The cache attributes of a large page entry (PAT is bit 12). -/
def PteAttrsL (w : U64) (a : Fl4Spec.VMAttributes) : Prop :=
  (Fl4Spec.VMAttribute.ptAttr .writeThrough ∈ a ↔ bitL w 3 = true) ∧
  (Fl4Spec.VMAttribute.ptAttr .cacheDisabled ∈ a ↔ bitL w 4 = true) ∧ (Fl4Spec.VMAttribute.pat ∈ a ↔ bitL w 12 = true)

/-- The cache attributes of a huge page entry: l4v drops PAT for huge pages
(`attr_mask'`); FL4, as C seL4, sets bit 12. -/
def PteAttrsH (w : U64) (a : Fl4Spec.VMAttributes) : Prop :=
  (Fl4Spec.VMAttribute.ptAttr .writeThrough ∈ a ↔ bitL w 3 = true) ∧
  (Fl4Spec.VMAttribute.ptAttr .cacheDisabled ∈ a ↔ bitL w 4 = true)

def PML4ERel (L3 : Set U64) (w : U64) : Fl4Spec.PML4E → Prop
  | .invalidPML4E => ¬ eP w
  | .pdPointerTablePML4E tab _ _ => eP w ∧ (eA w).bv = tab ∧ eT w ∈ L3

def PDPTERel (L2 : Set U64) (w : U64) : Fl4Spec.PDPTE → Prop
  | .invalidPDPTE => ¬ eP w
  | .pageDirectoryPDPTE tab _ _ => eP w ∧ ¬ eS w ∧ (eA w).bv = tab ∧ eT w ∈ L2
  | .hugePagePDPTE f attrs rights => eP w ∧ eS w ∧ (hA w).bv = f ∧ PteRights w rights ∧ PteAttrsH w attrs

def PDERel (L1 : Set U64) (w : U64) : Fl4Spec.PDE → Prop
  | .invalidPDE => ¬ eP w
  | .pageTablePDE tab _ _ => eP w ∧ ¬ eS w ∧ (eA w).bv = tab ∧ eT w ∈ L1
  | .largePagePDE f attrs rights => eP w ∧ eS w ∧ (lA w).bv = f ∧ PteRights w rights ∧ PteAttrsL w attrs

def PTERel (w : U64) : Fl4Spec.PTE → Prop
  | .invalidPTE => ¬ eP w
  | .smallPagePTE f attrs rights => eP w ∧ (eA w).bv = f ∧ PteRights w rights ∧ PteAttrs w attrs

/-- The page tables of FL4 memory `m` and of `σ`. -/
structure PtRel (L4 L3 L2 L1 : Set U64) (m : U64 → U64) (σ : Fl4Spec.State Unit) : Prop where
  l4 : ∀ p ∈ L4, ∃ f, σ.kheap p.bv = some (.archObj (.pageMapL4 f)) ∧
    ∀ i : U64, i.val < 512 → PML4ERel L3 (m (peA p i)) (f (Fl4Spec.ucast 9 i.bv))
  l3 : ∀ p ∈ L3, ∃ f, σ.kheap p.bv = some (.archObj (.pdPointerTable f)) ∧
    ∀ i : U64, i.val < 512 → PDPTERel L2 (m (peA p i)) (f (Fl4Spec.ucast 9 i.bv))
  l2 : ∀ p ∈ L2, ∃ f, σ.kheap p.bv = some (.archObj (.pageDirectory f)) ∧
    ∀ i : U64, i.val < 512 → PDERel L1 (m (peA p i)) (f (Fl4Spec.ucast 9 i.bv))
  l1 : ∀ p ∈ L1, ∃ f, σ.kheap p.bv = some (.archObj (.pageTable f)) ∧
    ∀ i : U64, i.val < 512 → PTERel (m (peA p i)) (f (Fl4Spec.ucast 9 i.bv))

/-- The tables are 4K-aligned. -/
def PtPlaced (L4 L3 L2 L1 : Set U64) : Prop :=
  ∀ p, (p ∈ L4 ∨ p ∈ L3 ∨ p ∈ L2 ∨ p ∈ L1) → p.val % 4096 = 0

/-- FL4's slot result as the spec's. -/
def slotRes : core.result.Result U64 error.LookupFault → Except Fl4Spec.LookupFailure Fl4Spec.ObjRef
  | .Ok x => .ok x.bv
  | .Err (.MissingCapability n) => .error (.missingCapability n.val)
  | .Err _ => .error .invalidRoot

/-! ## The spec's entry reads -/

section Spec
open Fl4Spec

theorem peA_bv (q j : U64) (hj : j.val < 512) (hq : q.val + 4096 ≤ 2 ^ 64) :
    (peA q j).bv = q.bv + (j.bv <<< wordSizeBits) := by
  apply BitVec.eq_of_toNat_eq
  show (peA q j).val = _
  rw [peA_val hq hj, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [wordSizeBits]
  show q.val + 8 * j.val = (q.val + j.val * 2 ^ 3 % 2 ^ 64) % 2 ^ 64
  rw [Nat.mod_eq_of_lt (by omega : j.val * 2 ^ 3 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  omega

theorem getPml4e_at {σ : State Unit} {q : U64} (hq : q.val % 4096 = 0) {f : BitVec 9 → PML4E}
    (hk : σ.kheap q.bv = some (.archObj (.pageMapL4 f))) {j : U64} (hj : j.val < 512) :
    getPml4e (Z := Unit) (q.bv + (j.bv <<< wordSizeBits)) σ = ({(f (ucast 9 j.bv), σ)}, False) := by
  obtain ⟨h1, h2⟩ := split_slot q.bv j.bv hq hj
  unfold getPml4e
  rw [nd_pure_bind', nd_pure_bind']
  simp only [pml4Bits, tableSize, ptTranslationBits, wordSizeBits] at h1 h2 ⊢
  rw [h1, h2, nd_bind_one (show getPml4 (Z := Unit) q.bv σ = ({(f, σ)}, False) by
    unfold getPml4; rw [nd_bind_one (getObject_eq hk)]; rfl)]
  rfl

theorem getPdpte_at {σ : State Unit} {q : U64} (hq : q.val % 4096 = 0) {f : BitVec 9 → PDPTE}
    (hk : σ.kheap q.bv = some (.archObj (.pdPointerTable f))) {j : U64} (hj : j.val < 512) :
    getPdpte (Z := Unit) (q.bv + (j.bv <<< wordSizeBits)) σ = ({(f (ucast 9 j.bv), σ)}, False) := by
  obtain ⟨h1, h2⟩ := split_slot q.bv j.bv hq hj
  unfold getPdpte
  rw [nd_pure_bind', nd_pure_bind']
  simp only [pdptBits, tableSize, ptTranslationBits, wordSizeBits] at h1 h2 ⊢
  rw [h1, h2, nd_bind_one (show getPdpt (Z := Unit) q.bv σ = ({(f, σ)}, False) by
    unfold getPdpt; rw [nd_bind_one (getObject_eq hk)]; rfl)]
  rfl

theorem getPde_at {σ : State Unit} {q : U64} (hq : q.val % 4096 = 0) {f : BitVec 9 → PDE}
    (hk : σ.kheap q.bv = some (.archObj (.pageDirectory f))) {j : U64} (hj : j.val < 512) :
    getPde (Z := Unit) (q.bv + (j.bv <<< wordSizeBits)) σ = ({(f (ucast 9 j.bv), σ)}, False) := by
  obtain ⟨h1, h2⟩ := split_slot q.bv j.bv hq hj
  unfold getPde
  rw [nd_pure_bind', nd_pure_bind']
  simp only [pdBits, tableSize, ptTranslationBits, wordSizeBits] at h1 h2 ⊢
  rw [h1, h2, nd_bind_one (show getPd (Z := Unit) q.bv σ = ({(f, σ)}, False) by
    unfold getPd; rw [nd_bind_one (getObject_eq hk)]; rfl)]
  rfl

theorem getPte_at {σ : State Unit} {q : U64} (hq : q.val % 4096 = 0) {f : BitVec 9 → PTE}
    (hk : σ.kheap q.bv = some (.archObj (.pageTable f))) {j : U64} (hj : j.val < 512) :
    getPte (Z := Unit) (q.bv + (j.bv <<< wordSizeBits)) σ = ({(f (ucast 9 j.bv), σ)}, False) := by
  obtain ⟨h1, h2⟩ := split_slot q.bv j.bv hq hj
  unfold getPte
  rw [nd_pure_bind', nd_pure_bind']
  simp only [ptBits, tableSize, ptTranslationBits, wordSizeBits] at h1 h2 ⊢
  rw [h1, h2, nd_bind_one (show getPt (Z := Unit) q.bv σ = ({(f, σ)}, False) by
    unfold getPt; rw [nd_bind_one (getObject_eq hk)]; rfl)]
  rfl

end Spec


/-! ## FL4's entry accessors -/

/-- The index of `vaddr` at level shift `sh`. -/
def vIdx (vaddr : U64) (sh : Nat) : U64 := ⟨vaddr.bv >>> sh⟩ &&& 511#u64

theorem vIdx_lt (vaddr : U64) (sh : Nat) : (vIdx vaddr sh).val < 512 := and_lt _ 9 511#u64 rfl (by decide)

theorem vIdx_bv (vaddr : U64) (sh : Nat) : (vIdx vaddr sh).bv = (vaddr.bv >>> sh) &&& Fl4Spec.mask 9 := by
  show (⟨vaddr.bv >>> sh⟩ &&& 511#u64 : U64).bv = _
  rw [UScalar.bv_and]; rfl

theorem and63_of_lt {x : U64} (h : x.val < 64) : (x &&& 63#u64) = x := by
  apply UScalar.eq_of_val_eq
  show (x &&& 63#u64).bv.toNat = x.bv.toNat
  rw [UScalar.bv_and, BitVec.toNat_and, show (UScalar.bv (63#u64 : U64)).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by show x.val < _; omega)]

theorem and511_of_lt {x : U64} (h : x.val < 512) : (x &&& 511#u64) = x := by
  apply UScalar.eq_of_val_eq
  show (x &&& 511#u64).bv.toNat = x.bv.toNat
  rw [UScalar.bv_and, BitVec.toNat_and, show (UScalar.bv (511#u64 : U64)).toNat = 2 ^ 9 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by show x.val < _; omega)]

theorem idx_eq (vaddr sh : U64) (h : sh.val < 64) : vspace.idx vaddr sh = ok (vIdx vaddr sh.val) := by
  unfold vspace.idx
  simp only [lift, bind_ok]
  rw [and63_of_lt h, shr_u64_eq _ _ h]
  simp only [bind_ok]; rfl

theorem entry_addr_eq (t i : U64) (hi : i.val < 512) : vspace.entry_addr t i = ok (peA t i) := by
  unfold vspace.entry_addr
  simp only [lift, bind_ok]
  rw [and511_of_lt hi]; rfl

theorem table_of_eq (e : U64) : vspace.table_of e = ok (eT e) := by
  unfold vspace.table_of vspace.ADDR_MASK layout.pptr layout.PPTR_BASE
  simp only [lift, bind_ok]; rfl

theorem P_PRESENT_eq : vspace.P_PRESENT = ok 1#u64 := by
  unfold vspace.P_PRESENT; rw [shl_eq _ _ (by decide) (by decide)]; rfl

theorem P_PS_eq : vspace.P_PS = ok 128#u64 := by
  unfold vspace.P_PS; rw [shl_eq _ _ (by decide) (by decide)]; rfl

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem entry_eq (s : S) (t i : U64) (hi : i.val < 512) : vspace.entry st s t i = ok (L.mem s (peA t i)) := by
  unfold vspace.entry
  simp only [lift, bind_ok]
  rw [and511_of_lt hi, L.read_eq]; rfl

end

theorem eT_bv (w : U64) : (eT w).bv = Fl4Spec.ptrFromPAddr (eA w).bv := by
  unfold eT Fl4Spec.ptrFromPAddr Fl4Spec.pptrBase
  rw [core.num.U64.wrapping_add_bv_eq]; rfl

theorem eP_iff (w : U64) : ((w &&& 1#u64) = 0#u64) ↔ ¬ eP w := by unfold eP; exact not_not.symm
theorem eS_iff (w : U64) : ((w &&& 128#u64) != 0#u64) = true ↔ eS w := by unfold eS; simp

theorem tbl_fit {p : U64} (h : p.val % 4096 = 0) : p.val + 4096 ≤ 2 ^ 64 := by
  have := p.hBounds; simp at this; omega

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem slot_bv (q : U64) (vaddr : U64) (sh : Nat) (hq : q.val % 4096 = 0) :
    (peA q (vIdx vaddr sh)).bv = q.bv + (((vaddr.bv >>> sh) &&& Fl4Spec.mask 9) <<< Fl4Spec.wordSizeBits) := by
  rw [peA_bv _ _ (vIdx_lt vaddr sh) (tbl_fit hq), vIdx_bv]

/-- **`lookup_pdpt_slot`** refines l4v `lookup_pdpt_slot` on a PML4 of `L4`. -/
theorem lookup_pdpt_slot_rel {L4 L3 L2 L1 : Set U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64) :
    vspace.lookup_pdpt_slot st s pm vaddr ⦃ r =>
      ExceptT.run (Fl4Spec.lookupPdptSlot (Z := Unit) pm.bv vaddr.bv) σ = ({(slotRes r, σ)}, False) ∧
      (∀ x, r = .Ok x → ∃ q ∈ L3, x = peA q (vIdx vaddr 30)) ∧
      (∀ e, r = .Err e → ∃ n, e = .MissingCapability n) ⦄ := by
  obtain ⟨f, hk, hf⟩ := hR.l4 pm hpm
  have hpa := hP pm (Or.inl hpm)
  have hi := vIdx_lt vaddr 39
  have hfe := hf _ hi
  have hsl : Fl4Spec.lookupPml4Slot pm.bv vaddr.bv = pm.bv + ((vIdx vaddr 39).bv <<< Fl4Spec.wordSizeBits) := by
    unfold Fl4Spec.lookupPml4Slot Fl4Spec.getPml4Index
    rw [vIdx_bv]; rfl
  unfold Fl4Spec.lookupPdptSlot
  rw [runE_bind_ok (runE_ret _ σ), hsl, runE_bind_ok (runE_liftE (getPml4e_at hpa hk hi))]
  unfold vspace.lookup_pdpt_slot
  rw [show vspace.idx vaddr 39#u64 = ok (vIdx vaddr 39) from idx_eq _ _ (by decide)]
  apply ok_bind_spec
  rw [entry_eq s pm _ (vIdx_lt _ _)]
  apply ok_bind_spec
  rw [P_PRESENT_eq]
  apply ok_bind_spec
  unfold lift
  apply ok_bind_spec
  cases hfx : f (Fl4Spec.ucast 9 (vIdx vaddr 39).bv) with
  | invalidPML4E =>
    rw [hfx] at hfe
    have h0 := (eP_iff _).2 hfe
    simp only [h0, ↓reduceIte]
    refine (WP.spec_ok _).2 ⟨?_, (fun x hx => by cases hx), fun e he => by cases he; exact ⟨_, rfl⟩⟩
    unfold vspace.PML4_INDEX_OFFSET
    rfl
  | pdPointerTablePML4E tab ta tr =>
    rw [hfx] at hfe
    obtain ⟨hp, ha, hT⟩ := hfe
    have h0 : ¬ (L.mem s (peA pm (vIdx vaddr 39)) &&& 1#u64) = 0#u64 := hp
    simp only [h0, ↓reduceIte]
    rw [table_of_eq]
    apply ok_bind_spec
    rw [show vspace.idx vaddr 30#u64 = ok (vIdx vaddr 30) from idx_eq _ _ (by decide)]
    apply ok_bind_spec
    rw [entry_addr_eq _ _ (vIdx_lt _ _)]
    apply ok_bind_spec
    refine (WP.spec_ok _).2 ⟨?_, (fun x hx => ⟨_, hT, by cases hx; rfl⟩), fun e he => by cases he⟩
    have hq := hP _ (Or.inr (Or.inl hT))
    show ExceptT.run (do
          let pd ← Fl4Spec.NonDetE.returnOk (Fl4Spec.ptrFromPAddr tab)
          let pdIndex ← Fl4Spec.NonDetE.returnOk (Fl4Spec.getPdptIndex vaddr.bv)
          let pdSlot ← Fl4Spec.NonDetE.returnOk (pd + (pdIndex <<< Fl4Spec.wordSizeBits))
          Fl4Spec.NonDetE.returnOk (ε := Fl4Spec.LookupFailure) pdSlot) σ = _
    rw [runE_bind_ok (runE_ret _ σ), runE_bind_ok (runE_ret _ σ), runE_bind_ok (runE_ret _ σ)]
    show ({(Except.ok _, σ)}, False) = ({(Except.ok (peA (eT (L.mem s (peA pm (vIdx vaddr 39)))) (vIdx vaddr 30)).bv, σ)}, False)
    rw [slot_bv _ _ _ hq, eT_bv, ha]
    rfl

/-- **`lookup_pd_slot`** refines l4v `lookup_pd_slot` on a PML4 of `L4`. -/
theorem lookup_pd_slot_rel {L4 L3 L2 L1 : Set U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64) :
    vspace.lookup_pd_slot st s pm vaddr ⦃ r =>
      ExceptT.run (Fl4Spec.lookupPdSlot (Z := Unit) pm.bv vaddr.bv) σ = ({(slotRes r, σ)}, False) ∧
      (∀ x, r = .Ok x → ∃ q ∈ L2, x = peA q (vIdx vaddr 21)) ∧
      (∀ e, r = .Err e → ∃ n, e = .MissingCapability n) ⦄ := by
  unfold vspace.lookup_pd_slot Fl4Spec.lookupPdSlot
  refine WP.spec_bind (lookup_pdpt_slot_rel s σ hR hP hpm vaddr) ?_
  rintro r ⟨hsp, hsl, hse⟩
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from]
    apply ok_bind_spec
    cases e <;> exact (WP.spec_ok _).2 ⟨runE_bind_err hsp, (fun x hx => by cases hx), fun e' he' => by cases he'; exact hse _ rfl⟩
  | Ok x =>
    obtain ⟨q, hq, rfl⟩ := hsl x rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨f, hk, hf⟩ := hR.l3 q hq
    have hqa := hP q (Or.inr (Or.inl hq))
    have hj := vIdx_lt vaddr 30
    have hfe := hf _ hj
    rw [runE_bind_ok hsp]
    rw [L.read_eq]
    apply ok_bind_spec
    rw [P_PRESENT_eq]
    apply ok_bind_spec
    unfold lift
    apply ok_bind_spec
    rw [peA_bv _ _ hj (tbl_fit hqa), runE_bind_ok (runE_liftE (getPdpte_at hqa hk hj))]
    cases hfx : f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) with
    | invalidPDPTE =>
      rw [hfx] at hfe
      have h0 := (eP_iff _).2 hfe
      simp only [h0, ↓reduceIte]
      refine (WP.spec_ok _).2 ⟨?_, (fun x hx => by cases hx), fun e he => by cases he; exact ⟨_, rfl⟩⟩
      unfold vspace.PDPT_INDEX_OFFSET
      rfl
    | hugePagePDPTE fr fa frr =>
      rw [hfx] at hfe
      obtain ⟨hp, hs, -⟩ := hfe
      have h0 : ¬ (L.mem s (peA q (vIdx vaddr 30)) &&& 1#u64) = 0#u64 := hp
      simp only [h0, ↓reduceIte]
      rw [P_PS_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      simp only [(eS_iff _).2 hs, ↓reduceIte]
      refine (WP.spec_ok _).2 ⟨?_, (fun x hx => by cases hx), fun e he => by cases he; exact ⟨_, rfl⟩⟩
      unfold vspace.PDPT_INDEX_OFFSET
      rfl
    | pageDirectoryPDPTE tab ta tr =>
      rw [hfx] at hfe
      obtain ⟨hp, hs, ha, hT⟩ := hfe
      have h0 : ¬ (L.mem s (peA q (vIdx vaddr 30)) &&& 1#u64) = 0#u64 := hp
      simp only [h0, ↓reduceIte]
      rw [P_PS_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      have hs' : ¬ ((L.mem s (peA q (vIdx vaddr 30)) &&& 128#u64) != 0#u64) = true := fun h => hs ((eS_iff _).1 h)
      simp only [hs', Bool.false_eq_true, ↓reduceIte]
      rw [table_of_eq]
      apply ok_bind_spec
      rw [show vspace.idx vaddr 21#u64 = ok (vIdx vaddr 21) from idx_eq _ _ (by decide)]
      apply ok_bind_spec
      rw [entry_addr_eq _ _ (vIdx_lt _ _)]
      apply ok_bind_spec
      refine (WP.spec_ok _).2 ⟨?_, (fun x hx => ⟨_, hT, by cases hx; rfl⟩), fun e he => by cases he⟩
      have hq' := hP _ (Or.inr (Or.inr (Or.inl hT)))
      show ExceptT.run (do
            let pd ← Fl4Spec.NonDetE.returnOk (Fl4Spec.ptrFromPAddr tab)
            let pdIndex ← Fl4Spec.NonDetE.returnOk (Fl4Spec.getPdIndex vaddr.bv)
            let pdSlot ← Fl4Spec.NonDetE.returnOk (pd + (pdIndex <<< Fl4Spec.wordSizeBits))
            Fl4Spec.NonDetE.returnOk (ε := Fl4Spec.LookupFailure) pdSlot) σ = _
      rw [runE_bind_ok (runE_ret _ σ), runE_bind_ok (runE_ret _ σ), runE_bind_ok (runE_ret _ σ)]
      show ({(Except.ok _, σ)}, False) =
        ({(Except.ok (peA (eT (L.mem s (peA q (vIdx vaddr 30)))) (vIdx vaddr 21)).bv, σ)}, False)
      rw [slot_bv _ _ _ hq', eT_bv, ha]
      rfl

/-- **`lookup_pt_slot`** refines l4v `lookup_pt_slot` on a PML4 of `L4`. -/
theorem lookup_pt_slot_rel {L4 L3 L2 L1 : Set U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64) :
    vspace.lookup_pt_slot st s pm vaddr ⦃ r =>
      ExceptT.run (Fl4Spec.lookupPtSlot (Z := Unit) pm.bv vaddr.bv) σ = ({(slotRes r, σ)}, False) ∧
      (∀ x, r = .Ok x → ∃ q ∈ L1, x = peA q (vIdx vaddr 12)) ∧
      (∀ e, r = .Err e → ∃ n, e = .MissingCapability n) ⦄ := by
  unfold vspace.lookup_pt_slot Fl4Spec.lookupPtSlot
  refine WP.spec_bind (lookup_pd_slot_rel s σ hR hP hpm vaddr) ?_
  rintro r ⟨hsp, hsl, hse⟩
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from]
    apply ok_bind_spec
    cases e <;> exact (WP.spec_ok _).2 ⟨runE_bind_err hsp, (fun x hx => by cases hx), fun e' he' => by cases he'; exact hse _ rfl⟩
  | Ok x =>
    obtain ⟨q, hq, rfl⟩ := hsl x rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨f, hk, hf⟩ := hR.l2 q hq
    have hqa := hP q (Or.inr (Or.inr (Or.inl hq)))
    have hj := vIdx_lt vaddr 21
    have hfe := hf _ hj
    rw [runE_bind_ok hsp]
    rw [L.read_eq]
    apply ok_bind_spec
    rw [P_PRESENT_eq]
    apply ok_bind_spec
    unfold lift
    apply ok_bind_spec
    rw [peA_bv _ _ hj (tbl_fit hqa), runE_bind_ok (runE_liftE (getPde_at hqa hk hj))]
    cases hfx : f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) with
    | invalidPDE =>
      rw [hfx] at hfe
      have h0 := (eP_iff _).2 hfe
      simp only [h0, ↓reduceIte]
      refine (WP.spec_ok _).2 ⟨?_, (fun x hx => by cases hx), fun e he => by cases he; exact ⟨_, rfl⟩⟩
      unfold vspace.PD_INDEX_OFFSET
      rfl
    | largePagePDE fr fa frr =>
      rw [hfx] at hfe
      obtain ⟨hp, hs, -⟩ := hfe
      have h0 : ¬ (L.mem s (peA q (vIdx vaddr 21)) &&& 1#u64) = 0#u64 := hp
      simp only [h0, ↓reduceIte]
      rw [P_PS_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      simp only [(eS_iff _).2 hs, ↓reduceIte]
      refine (WP.spec_ok _).2 ⟨?_, (fun x hx => by cases hx), fun e he => by cases he; exact ⟨_, rfl⟩⟩
      unfold vspace.PD_INDEX_OFFSET
      rfl
    | pageTablePDE tab ta tr =>
      rw [hfx] at hfe
      obtain ⟨hp, hs, ha, hT⟩ := hfe
      have h0 : ¬ (L.mem s (peA q (vIdx vaddr 21)) &&& 1#u64) = 0#u64 := hp
      simp only [h0, ↓reduceIte]
      rw [P_PS_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      have hs' : ¬ ((L.mem s (peA q (vIdx vaddr 21)) &&& 128#u64) != 0#u64) = true := fun h => hs ((eS_iff _).1 h)
      simp only [hs', Bool.false_eq_true, ↓reduceIte]
      rw [table_of_eq]
      apply ok_bind_spec
      rw [show vspace.idx vaddr 12#u64 = ok (vIdx vaddr 12) from idx_eq _ _ (by decide)]
      apply ok_bind_spec
      rw [entry_addr_eq _ _ (vIdx_lt _ _)]
      apply ok_bind_spec
      refine (WP.spec_ok _).2 ⟨?_, (fun x hx => ⟨_, hT, by cases hx; rfl⟩), fun e he => by cases he⟩
      have hq' := hP _ (Or.inr (Or.inr (Or.inr hT)))
      show ExceptT.run (do
            let pd ← Fl4Spec.NonDetE.returnOk (Fl4Spec.ptrFromPAddr tab)
            let pdIndex ← Fl4Spec.NonDetE.returnOk (Fl4Spec.getPtIndex vaddr.bv)
            let pdSlot ← Fl4Spec.NonDetE.returnOk (pd + (pdIndex <<< Fl4Spec.wordSizeBits))
            Fl4Spec.NonDetE.returnOk (ε := Fl4Spec.LookupFailure) pdSlot) σ = _
      rw [runE_bind_ok (runE_ret _ σ), runE_bind_ok (runE_ret _ σ), runE_bind_ok (runE_ret _ σ)]
      show ({(Except.ok _, σ)}, False) =
        ({(Except.ok (peA (eT (L.mem s (peA q (vIdx vaddr 21)))) (vIdx vaddr 12)).bv, σ)}, False)
      rw [slot_bv _ _ _ hq', eT_bv, ha]
      rfl

end

end Fl4Proofs.P3.Vs
