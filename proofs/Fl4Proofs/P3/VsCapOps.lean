/-
P3 (DESIGN.md §9), VSpace: **`VsCapsIn` through the VSpace operations**,
per primitive (for the MdbStep constructors).

* `VsCapsIn.after`: a remap (frame and table map/unmap, Assign): one slot's
  cap replaced, `SlotFoot`, the new cap `VsLike` the old (the remap posts).
* `pam_iff_small`/`pam_iff_large`: the address masks as arithmetic
  (`paddr % 2^12 = 0 ∧ paddr < 2^52`, `paddr % 2^21 = 0 ∧ paddr < 2^52`).
* `vcap_alias`: a 4 KiB alias of a page of a well-placed RAM large frame is
  well placed (`DeriveSubframe`'s insert, `VsCapsIn.insert_copy`).
* `vcap_pool`: `MakePool`'s pool cap, in the grown pool set
  (`VsCapsIn.insert_fresh`).
-/
import Fl4Proofs.P3.VsCapInv
import Fl4Proofs.P3.VsSubMdb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

section
variable {P L4 L3 L2 L1 : Set U64} {G : MdbGhost}

/-- **A remap keeps the invariant**: one slot's cap replaced by a `VsLike`
one, the other slots kept (`SlotFoot`). -/
theorem VsCapsIn.after {th : TypedHeap} {m m' : U64 → U64} {x : U64} {c : capability.Cap}
    (hM : MdbLinks th m G) (h : VsCapsIn P L4 L3 L2 L1 m G) (hF : SlotFoot th m m' x)
    (hcx : capAt m x = ok c) (hL : VsLike (capV m' x) c) : VsCapsIn P L4 L3 L2 L1 m' G := by
  have hc : ∀ z ∈ G.chains.flatten, z ≠ x → capV m' z = capV m z := fun z hz hne => by
    have hzs := ((hM.members z).1 hz).1
    unfold capV; rw [((hF z hzs).2.2 hne).1, ((hF z hzs).2.2 hne).2]
  by_cases hx : x ∈ G.chains.flatten
  · refine h.recap x (hL.2 _ _ _ _ _ ?_) hc
    have := h x hx
    rwa [capV_of_capAt hcx] at this
  · exact h.of_caps fun z hz => hc z hz (fun e => hx (e ▸ hz))

end

/-- A 64-bit word equal to its masking by `M` has its bits in `M`'s. -/
theorem land_self_iff (x M : BitVec 64) : x &&& M = x ↔ ∀ i < 64, x.getLsbD i = true → M.getLsbD i = true := by
  constructor
  · intro h i _ hx
    have := congrArg (fun y => y.getLsbD i) h
    simp only [BitVec.getLsbD_and] at this
    rw [hx] at this; simpa using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and]
    cases hx : x.getLsbD i
    · simp
    · simp [h i hi hx]

/-- The bits of a number below `2^52` and a multiple of `2^lo`. -/
theorem bits_iff (x : BitVec 64) (lo : Nat) (hlo : lo ≤ 52) :
    (∀ i < 64, x.getLsbD i = true → lo ≤ i ∧ i < 52) ↔ x.toNat % 2 ^ lo = 0 ∧ x.toNat < 2 ^ 52 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
      by_cases hi : i < lo
      · simp only [hi, decide_true, Bool.true_and]
        cases hb : x.toNat.testBit i
        · rfl
        · have := h i (by omega) (by rw [BitVec.getLsbD]; exact hb); omega
      · simp [hi]
    · apply Nat.lt_pow_two_of_testBit
      intro i hi
      cases hb : x.toNat.testBit i
      · rfl
      · by_cases h64 : i < 64
        · have := h i h64 (by rw [BitVec.getLsbD]; exact hb); omega
        · have := Nat.testBit_lt_two_pow (show x.toNat < 2 ^ i from
            lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
          rw [hb] at this; cases this
  · rintro ⟨h1, h2⟩ i hi hx
    rw [BitVec.getLsbD] at hx
    refine ⟨?_, ?_⟩
    · by_contra hc
      have := Nat.testBit_mod_two_pow x.toNat lo i
      rw [h1, Nat.zero_testBit] at this
      simp [show i < lo by omega, hx] at this
    · by_contra hc
      have := Nat.testBit_lt_two_pow (show x.toNat < 2 ^ i from
        lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [hx] at this; cases this

theorem mask_small_bits : ∀ i < 64, (4503599627366400#64 : BitVec 64).getLsbD i = decide (12 ≤ i ∧ i < 52) := by
  intro i hi; interval_cases i <;> decide

theorem mask_large_bits : ∀ i < 64, (4503599625273344#64 : BitVec 64).getLsbD i = decide (21 ≤ i ∧ i < 52) := by
  intro i hi; interval_cases i <;> decide

/-- `PaM` as arithmetic, from the mask's bits. -/
theorem pam_iff {p M : U64} {lo : Nat} (hlo : lo ≤ 52)
    (hM : ∀ i < 64, M.bv.getLsbD i = decide (lo ≤ i ∧ i < 52)) :
    PaM p M ↔ (core.num.U64.wrapping_sub p layout.PPTR_BASE).val % 2 ^ lo = 0 ∧
      (core.num.U64.wrapping_sub p layout.PPTR_BASE).val < 2 ^ 52 := by
  unfold PaM
  set x := core.num.U64.wrapping_sub p layout.PPTR_BASE
  have e : (x &&& M = x) ↔ (x.bv &&& M.bv = x.bv) := by
    constructor
    · intro h; rw [← UScalar.bv_and, h]
    · intro h; apply UScalar.eq_of_val_eq
      have := congrArg BitVec.toNat h
      rw [← UScalar.bv_and] at this; exact this
  have hb := bits_iff x.bv lo hlo
  rw [show x.bv.toNat = x.val from rfl] at hb
  rw [e, land_self_iff, ← hb]
  constructor
  · intro h i hi hx; have := h i hi hx; rw [hM i hi] at this; simpa using this
  · intro h i hi hx; rw [hM i hi]; simpa using h i hi hx

theorem pam_iff_small (p : U64) : PaM p 4503599627366400#u64 ↔
    (core.num.U64.wrapping_sub p layout.PPTR_BASE).val % 2 ^ 12 = 0 ∧
      (core.num.U64.wrapping_sub p layout.PPTR_BASE).val < 2 ^ 52 :=
  pam_iff (by decide) mask_small_bits

theorem pam_iff_large (p : U64) : PaM p 4503599625273344#u64 ↔
    (core.num.U64.wrapping_sub p layout.PPTR_BASE).val % 2 ^ 21 = 0 ∧
      (core.num.U64.wrapping_sub p layout.PPTR_BASE).val < 2 ^ 52 :=
  pam_iff (by decide) mask_large_bits

/-- **The alias of a page of a well-placed large frame is well placed.** -/
theorem vcap_alias {P L4 L3 L2 L1 : Set U64} {ptr rt fa fv q vm : U64} {mm : Bool}
    (h : VCapOK P L4 L3 L2 L1 (.Frame ptr .Large rt false mm false fa fv))
    (hq1 : ptr.val ≤ q.val) (hq2 : q.val + 4096 ≤ ptr.val + 2 ^ 21) (hqal : q.val % 4096 = 0) :
    VCapOK P L4 L3 L2 L1 (.Frame q .Small vm false false false 0#u64 0#u64) := by
  have hp : PaM ptr 4503599625273344#u64 := by
    simp only [VCapOK, frameMaskOf] at h; first | exact h.2 | exact h
  suffices hq : PaM q 4503599627366400#u64 by
    simp only [VCapOK, frameMaskOf]; exact ⟨fun e => absurd e (by decide), hq⟩
  have hp' := (pam_iff_large ptr).1 hp
  rw [pam_iff_small]
  have hb := Fl4Proofs.P0.Consts.layout.PPTR_BASE.val_eq
  have hpv : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE).val =
      (ptr.val + (2 ^ 64 - layout.PPTR_BASE.val)) % 2 ^ 64 := by
    simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]
  have hqv : (core.num.U64.wrapping_sub q layout.PPTR_BASE).val =
      (q.val + (2 ^ 64 - layout.PPTR_BASE.val)) % 2 ^ 64 := by
    simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]
  rw [hpv] at hp'; rw [hqv]
  have : q.val < 2 ^ 64 := q.hBounds
  omega

/-- **`MakePool`'s pool cap is well placed** in the pool set grown by it. -/
theorem vcap_pool {P L4 L3 L2 L1 : Set U64} {p base i : U64} (hbase : base.val = i.val * 512)
    (hi : i.val < 2048) (hp0 : p ≠ 0#u64) : VCapOK (insert p P) L4 L3 L2 L1 (.AsidPool p base) :=
  ⟨⟨Set.mem_insert _ _, hp0⟩, by omega, by omega⟩


/-! ## The untyped regions apart from the kernel-global area -/

/-- **The untyped regions lie apart from the kernel-global area** (the
placement of `MakePool`'s pool page; per primitive as `VsCapsIn`). -/
def UtKsOut (ksb : U64) (mem : U64 → U64) (G : MdbGhost) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p sb fi : U64, ∀ d : Bool, capV mem x = .Untyped p sb fi d →
    p.val + 2 ^ sb.val ≤ ksb.val ∨ ksb.val + 13568 ≤ p.val

/-- An untyped cap whose region lies apart from the kernel-global area
(any other cap). -/
def UtOut (ksb : U64) : capability.Cap → Prop
  | .Untyped p sb _ _ => p.val + 2 ^ sb.val ≤ ksb.val ∨ ksb.val + 13568 ≤ p.val
  | _ => True

section
variable {ksb : U64} {mem mem' : U64 → U64} {G : MdbGhost}

theorem utKsOut_iff : UtKsOut ksb mem G ↔ ∀ x ∈ G.chains.flatten, UtOut ksb (capV mem x) := by
  constructor
  · intro h x hx
    cases e : capV mem x <;> simp only [UtOut]
    exact h x hx _ _ _ _ e
  · intro h x hx p sb fi d e
    have := h x hx; rw [e] at this; exact this

theorem UtKsOut.of_caps (h : UtKsOut ksb mem G) (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) :
    UtKsOut ksb mem' G :=
  fun x hx p sb fi d e => h x hx p sb fi d (by rw [← hc x hx]; exact e)

/-- One slot's cap replaced by one apart from the kernel-global area. -/
theorem UtKsOut.recap (h : UtKsOut ksb mem G) (x0 : U64) (hx : UtOut ksb (capV mem' x0))
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z) : UtKsOut ksb mem' G := by
  rw [utKsOut_iff] at h ⊢
  intro x hxm
  by_cases e : x = x0
  · subst e; exact hx
  · rw [hc x hxm e]; exact h x hxm

theorem UtKsOut.remove {th : TypedHeap} (hM : MdbLinks th mem G) (h : UtKsOut ksb mem G) (x0 : U64)
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z) : UtKsOut ksb mem' (remG G x0) := by
  rw [utKsOut_iff] at h ⊢
  intro x hx
  obtain ⟨hx0, hxn⟩ := (Mdb.mem_removeChains hM.tree.nodup).1 hx
  rw [hc x hx0 hxn]; exact h x hx0

theorem UtKsOut.rename (h : UtKsOut ksb mem G) (e : U64 ≃ U64)
    (hc : ∀ z ∈ G.chains.flatten, capV mem' (e z) = capV mem z) : UtKsOut ksb mem' (renG G e) := by
  rw [utKsOut_iff] at h ⊢
  intro x hx
  have hx0 := (mem_renG e x).1 hx
  have := hc _ hx0
  rw [Equiv.apply_symm_apply] at this
  rw [this]; exact h _ hx0

/-- A cap inserted after `src`, apart from the kernel-global area (an
untyped cap over part of its parent's region, or any other cap). -/
theorem UtKsOut.insert (h : UtKsOut ksb mem G) {src dest : U64} (hsrc : src ∈ G.chains.flatten) (b : Bool)
    (hcd : UtOut ksb (capV mem' dest))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ dest → UtOut ksb (capV mem z) → UtOut ksb (capV mem' z)) :
    UtKsOut ksb mem' (insG G src dest b) := by
  rw [utKsOut_iff] at h ⊢
  intro x hx
  rcases (mem_flatten_ins hsrc).1 hx with rfl | hx0
  · exact hcd
  · by_cases e : x = dest
    · subst e; exact hcd
    · exact hcap x hx0 e (h x hx0)

/-- An untyped cap within one apart from the kernel-global area is apart. -/
theorem utOut_within {p sb q sb' : U64} {fi fi' : U64} {d d' : Bool}
    (h : UtOut ksb (.Untyped p sb fi d)) (h1 : p.val ≤ q.val) (h2 : q.val + 2 ^ sb'.val ≤ p.val + 2 ^ sb.val) :
    UtOut ksb (.Untyped q sb' fi' d') := by
  simp only [UtOut] at h ⊢; omega

/-- **`MakePool`'s pool page apart from the kernel-global area**, from the
untyped placement. -/
theorem UtKsOut.pool {th : TypedHeap} (h : UtKsOut ksb mem G) (hM : MdbLinks th mem G) {x : U64}
    (hx : IsSlot th x) {p fi : U64} (hc : capAt mem x = ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi false)) :
    p.val + 4096 ≤ ksb.val ∨ ksb.val + 13568 ≤ p.val := by
  have := h x ((hM.members x).2 ⟨hx, _, hc, by simp⟩) p _ fi false (capV_of_capAt hc)
  have e : fl4_abi.consts.bits.ASID_POOL.val = 12 := by unfold fl4_abi.consts.bits.ASID_POOL; rfl
  rw [e] at this; simpa using this

end

end

end Fl4Proofs.P3.Vs
