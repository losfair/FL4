/-
P3 (DESIGN.md §9), VSpace: **the weakened VSpace cap placement, base**
(below the CSpace layer, for `StepSem` and the CNode proofs): `VCapW`,
`TabUn`, `VCapW.transfer`, and the slot form `VsSlotsW` / `VsSlotsT`.
VsCapW's docstring explains the weakening; this module holds what does not
need the MDB.
-/
import Fl4Proofs.P3.VsFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section


/-- **A VSpace cap placed, weakened** (module docstring). -/
def VCapW (P L4 L3 L2 L1 : Set U64) : capability.Cap → Prop
  | .PageTable p mp a v => (mp = false → p ∈ L1) ∧ PaM p 4503599627366400#u64 ∧
      (mp = true → a ≠ 0#u64 ∧ v.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0) ∧
      (mp = true → UserV v)
  | .PageDirectory p mp a v => (mp = false → p ∈ L2) ∧ PaM p 4503599627366400#u64 ∧ (mp = true → a ≠ 0#u64) ∧
      (mp = true → UserV v)
  | .Pdpt p mp a v => (mp = false → p ∈ L3) ∧ PaM p 4503599627366400#u64 ∧ (mp = true → a ≠ 0#u64) ∧
      (mp = true → UserV v)
  | c => VCapOK P L4 L3 L2 L1 c

/-- An unmapped page-table, page-directory or PDPT cap. -/
def TabUn : capability.Cap → Prop
  | .PageTable _ mp _ _ => mp = false
  | .PageDirectory _ mp _ _ => mp = false
  | .Pdpt _ mp _ _ => mp = false
  | _ => False

/-- A cap whose placement names no VSpace set (no table, PML4 or ASID pool
cap). -/
def SetFree : capability.Cap → Prop
  | .PageTable .. => False
  | .PageDirectory .. => False
  | .Pdpt .. => False
  | .Pml4 .. => False
  | .AsidPool .. => False
  | _ => True

/-- **A set-free cap's placement holds at any sets.** -/
theorem VCapOK.setFree {P L4 L3 L2 L1 P' L4' L3' L2' L1' : Set U64} {c : capability.Cap} (h : SetFree c)
    (hv : VCapOK P L4 L3 L2 L1 c) : VCapOK P' L4' L3' L2' L1' c := by
  cases c <;> first | exact False.elim h | exact hv

/-- `VCapOK` at grown sets (VsCapInv's `VCapOK.mono`, here below it). -/
theorem vcapOK_monoB {P L4 L3 L2 L1 P' L4' L3' L2' L1' : Set U64} (hP : P ⊆ P') (h4 : L4 ⊆ L4') (h3 : L3 ⊆ L3')
    (h2 : L2 ⊆ L2') (h1 : L1 ⊆ L1') {c : capability.Cap} (h : VCapOK P L4 L3 L2 L1 c) :
    VCapOK P' L4' L3' L2' L1' c := by
  cases c <;> simp only [VCapOK] at h ⊢
  all_goals first
    | exact ⟨h1 h.1, h.2⟩
    | exact ⟨h2 h.1, h.2⟩
    | exact ⟨h3 h.1, h.2⟩
    | exact ⟨h4 h.1, h.2⟩
    | exact ⟨hP h.1, h.2⟩
    | exact ⟨⟨hP h.1.1, h.1.2⟩, h.2⟩
    | exact h

section
variable {P L4 L3 L2 L1 : Set U64}

/-- `VCapOK` is the strong form. -/
theorem VCapOK.toW {c : capability.Cap} (h : VCapOK P L4 L3 L2 L1 c) : VCapW P L4 L3 L2 L1 c := by
  cases c <;> simp only [VCapOK, VCapW] at h ⊢
  all_goals first
    | exact ⟨fun _ => h.1, h.2⟩
    | exact h

/-- **Back to `VCapOK`**: an unmapped table cap, or any cap but a mapped
table cap. -/
theorem VCapW.ok_of {c : capability.Cap} (h : VCapW P L4 L3 L2 L1 c)
    (hm : ∀ p a v, c ≠ .PageTable p true a v ∧ c ≠ .PageDirectory p true a v ∧ c ≠ .Pdpt p true a v) :
    VCapOK P L4 L3 L2 L1 c := by
  cases c with
  | PageTable p mp a v =>
    have := (hm p a v).1; simp only [VCapW] at h; simp only [VCapOK]
    cases mp
    · exact ⟨h.1 rfl, h.2⟩
    · exact absurd rfl this
  | PageDirectory p mp a v =>
    have := (hm p a v).2.1; simp only [VCapW] at h; simp only [VCapOK]
    cases mp
    · exact ⟨h.1 rfl, h.2⟩
    · exact absurd rfl this
  | Pdpt p mp a v =>
    have := (hm p a v).2.2; simp only [VCapW] at h; simp only [VCapOK]
    cases mp
    · exact ⟨h.1 rfl, h.2⟩
    · exact absurd rfl this
  | _ => exact h

/-- **A table cap's table in its set** (mapped or not; no condition on the
other caps): what `VCapW` leaves out of `VCapOK` for a mapped table cap. -/
def TabIn (L3 L2 L1 : Set U64) : capability.Cap → Prop
  | .PageTable p _ _ _ => p ∈ L1
  | .PageDirectory p _ _ _ => p ∈ L2
  | .Pdpt p _ _ _ => p ∈ L3
  | _ => True

/-- **The strong placement from the weakened one** and the table in its set. -/
theorem VCapW.okTab {c : capability.Cap} (h : VCapW P L4 L3 L2 L1 c) (ht : TabIn L3 L2 L1 c) :
    VCapOK P L4 L3 L2 L1 c := by
  cases c with
  | PageTable p mp a v => exact ⟨ht, h.2⟩
  | PageDirectory p mp a v => exact ⟨ht, h.2⟩
  | Pdpt p mp a v => exact ⟨ht, h.2⟩
  | _ => exact h

/-- `VCapOK` puts a table cap's table in its set. -/
theorem VCapOK.tabIn {c : capability.Cap} (h : VCapOK P L4 L3 L2 L1 c) : TabIn L3 L2 L1 c := by
  cases c with
  | PageTable p mp a v => exact h.1
  | PageDirectory p mp a v => exact h.1
  | Pdpt p mp a v => exact h.1
  | _ => trivial

/-- A mapped table cap's or an unmapped one's placement: the table in its set
when unmapped. -/
theorem VCapW.mono {P' L4' L3' L2' L1' : Set U64} (hP : P ⊆ P') (h4 : L4 ⊆ L4') (h3 : L3 ⊆ L3')
    (h2 : L2 ⊆ L2') (h1 : L1 ⊆ L1') {c : capability.Cap} (h : VCapW P L4 L3 L2 L1 c) :
    VCapW P' L4' L3' L2' L1' c := by
  cases c <;> simp only [VCapW] at h ⊢
  all_goals first
    | exact ⟨fun e => h1 (h.1 e), h.2⟩
    | exact ⟨fun e => h2 (h.1 e), h.2⟩
    | exact ⟨fun e => h3 (h.1 e), h.2⟩
    | exact vcapOK_monoB hP h4 h3 h2 h1 h

/-- **The step lemma** (module docstring): `VCapOK` carried from `c0` to `c`
at every set, `c` an unmapped table cap only if `c0` is one. -/
theorem VCapW.transfer {c0 c : capability.Cap} (h : VCapW P L4 L3 L2 L1 c0)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, VCapOK P L4 L3 L2 L1 c0 → VCapOK P L4 L3 L2 L1 c)
    (hu : TabUn c → TabUn c0) : VCapW P L4 L3 L2 L1 c := by
  -- the target's placement from `VCapOK` at sets differing from these in
  -- `L3`, `L2` or `L1` only, when the target is no unmapped table cap
  have back : ∀ L3' L2' L1' : Set U64, VCapOK P L4 L3' L2' L1' c → ¬ TabUn c → VCapW P L4 L3 L2 L1 c := by
    intro L3' L2' L1' hc hn
    cases c with
    | PageTable p mp a v =>
      cases mp
      · exact absurd rfl hn
      · exact ⟨fun e => absurd e (by decide), hc.2⟩
    | PageDirectory p mp a v =>
      cases mp
      · exact absurd rfl hn
      · exact ⟨fun e => absurd e (by decide), hc.2⟩
    | Pdpt p mp a v =>
      cases mp
      · exact absurd rfl hn
      · exact ⟨fun e => absurd e (by decide), hc.2⟩
    | _ => exact hc
  cases c0 with
  | PageTable p mp a v =>
    cases mp
    · exact (hv _ _ _ _ _ (VCapW.ok_of h fun _ _ _ => ⟨by simp, by simp, by simp⟩)).toW
    · exact back _ _ (insert p L1) (hv P L4 L3 L2 (insert p L1) ⟨Set.mem_insert _ _, h.2.1, fun _ => h.2.2.1 rfl, fun _ => h.2.2.2 rfl⟩)
        fun ht => by have := hu ht; simp [TabUn] at this
  | PageDirectory p mp a v =>
    cases mp
    · exact (hv _ _ _ _ _ (VCapW.ok_of h fun _ _ _ => ⟨by simp, by simp, by simp⟩)).toW
    · exact back _ (insert p L2) _ (hv P L4 L3 (insert p L2) L1 ⟨Set.mem_insert _ _, h.2.1, fun _ => h.2.2.1 rfl, fun _ => h.2.2.2 rfl⟩)
        fun ht => by have := hu ht; simp [TabUn] at this
  | Pdpt p mp a v =>
    cases mp
    · exact (hv _ _ _ _ _ (VCapW.ok_of h fun _ _ _ => ⟨by simp, by simp, by simp⟩)).toW
    · exact back (insert p L3) _ _ (hv P L4 (insert p L3) L2 L1 ⟨Set.mem_insert _ _, h.2.1, fun _ => h.2.2.1 rfl, fun _ => h.2.2.2 rfl⟩)
        fun ht => by have := hu ht; simp [TabUn] at this
  | _ => exact (hv _ _ _ _ _ (VCapW.ok_of h fun _ _ _ => ⟨by simp, by simp, by simp⟩)).toW

end

/-! ## Over the slots

The form carried at `J` (`JAtZ.vsc`): every slot of the typed heap holds a
placed cap (a null cap is placed), so no MDB ghost is involved;
`VsSlotsT th m m'` is a step's obligation: placed slots before give placed
slots after, at every set, and (`FrSlots`) every non-device frame cap's
bytes lying in a set `U` before gives the same after, at every `U` (a step
moves, copies or derives frame caps only within the ranges of frame caps
before: what `JAtZ.fcap`, l4v `valid_cap` for frame caps, is kept by). -/

/-- **A non-device frame cap's bytes lie in `U`** (every other cap: no
condition). -/
def FrIn (U : Nat → Prop) : capability.Cap → Prop
  | .Frame q sz _ d _ _ _ _ => d = false → ∀ a : Nat, q.val ≤ a → a < q.val + 2 ^ (fbitsF sz).val → U a
  | _ => True

theorem FrIn.mono {U U' : Nat → Prop} {c : capability.Cap} (h : FrIn U c) (hU : ∀ a, U a → U' a) : FrIn U' c := by
  cases c with
  | Frame q sz r d m e a v => exact fun hd x h1 h2 => hU x (h hd x h1 h2)
  | _ => trivial

/-- `FrIn` reads only the cap's object key (`okey`: a frame's base, size and
device flag). -/
theorem FrIn.of_okey {U : Nat → Prop} {c c0 : capability.Cap} (h : okey c = okey c0) (h0 : FrIn U c0) :
    FrIn U c := by
  cases c with
  | Frame q sz r d m e a v =>
    cases c0 <;> simp [okey] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; exact h0
  | _ => trivial

theorem FrIn.null (U : Nat → Prop) : FrIn U .Null := trivial

section
variable {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {m m' m'' : U64 → U64}

/-- **Every slot's cap placed** at the sets. -/
def VsSlotsW (th : TypedHeap) (P L4 L3 L2 L1 : Set U64) (m : U64 → U64) : Prop :=
  ∀ y, IsSlot th y → VCapW P L4 L3 L2 L1 (capV m y)

/-- **Every slot's non-device frame cap's bytes in `U`.** -/
def FrSlots (th : TypedHeap) (U : Nat → Prop) (m : U64 → U64) : Prop :=
  ∀ y, IsSlot th y → FrIn U (capV m y)

/-- **Every slot's cap native** (`NativeCap`). -/
def VsNat (th : TypedHeap) (m : U64 → U64) : Prop :=
  ∀ y, IsSlot th y → NativeCap (capV m y)

theorem VsNat.of_eq (h : VsNat th m) (hc : ∀ y, IsSlot th y → capV m' y = capV m y) : VsNat th m' :=
  fun y hy => by rw [hc y hy]; exact h y hy

/-- **A step keeps the slots placed**, at every set, and the frame caps'
ranges within the old ones' (`FrSlots`, at every `U`). -/
def VsSlotsT (th : TypedHeap) (m m' : U64 → U64) : Prop :=
  (∀ P L4 L3 L2 L1 : Set U64, VsSlotsW th P L4 L3 L2 L1 m → VsSlotsW th P L4 L3 L2 L1 m') ∧
    (∀ U : Nat → Prop, FrSlots th U m → FrSlots th U m') ∧ (VsNat th m → VsNat th m')

theorem FrSlots.of_eq {U : Nat → Prop} (h : FrSlots th U m) (hc : ∀ y, IsSlot th y → capV m' y = capV m y) :
    FrSlots th U m' := fun y hy => by rw [hc y hy]; exact h y hy

theorem FrSlots.mono {U U' : Nat → Prop} (h : FrSlots th U m) (hU : ∀ a, U a → U' a) : FrSlots th U' m :=
  fun y hy => (h y hy).mono hU

theorem FrSlots.step {U : Nat → Prop} (h : FrSlots th U m) (hT : VsSlotsT th m m') : FrSlots th U m' :=
  hT.2.1 U h

theorem VsNat.step (h : VsNat th m) (hT : VsSlotsT th m m') : VsNat th m' :=
  hT.2.2 h

theorem VsSlotsW.of_eq (h : VsSlotsW th P L4 L3 L2 L1 m) (hc : ∀ y, IsSlot th y → capV m' y = capV m y) :
    VsSlotsW th P L4 L3 L2 L1 m' := fun y hy => by rw [hc y hy]; exact h y hy

theorem VsSlotsW.step (h : VsSlotsW th P L4 L3 L2 L1 m) (hT : VsSlotsT th m m') : VsSlotsW th P L4 L3 L2 L1 m' :=
  hT.1 P L4 L3 L2 L1 h

theorem VsSlotsW.mono {P' L4' L3' L2' L1' : Set U64} (h : VsSlotsW th P L4 L3 L2 L1 m) (hP : P ⊆ P')
    (h4 : L4 ⊆ L4') (h3 : L3 ⊆ L3') (h2 : L2 ⊆ L2') (h1 : L1 ⊆ L1') : VsSlotsW th P' L4' L3' L2' L1' m :=
  fun y hy => (h y hy).mono hP h4 h3 h2 h1

theorem VsSlotsW.at (h : VsSlotsW th P L4 L3 L2 L1 m) {x : U64} (hx : IsSlot th x) {c : capability.Cap}
    (hc : capAt m x = ok c) : VCapW P L4 L3 L2 L1 c := by
  have e : capV m x = c := by rw [capAt_capV] at hc; simpa using hc
  rw [← e]; exact h x hx

/-- The strong form at a slot for an unmapped table cap, or a PML4, pool or
frame cap. -/
theorem VsSlotsW.atOK (h : VsSlotsW th P L4 L3 L2 L1 m) {x : U64} (hx : IsSlot th x) {c : capability.Cap}
    (hc : capAt m x = ok c)
    (hm : ∀ p a v, c ≠ .PageTable p true a v ∧ c ≠ .PageDirectory p true a v ∧ c ≠ .Pdpt p true a v) :
    VCapOK P L4 L3 L2 L1 c :=
  (h.at hx hc).ok_of hm

theorem VsSlotsT.refl : VsSlotsT th m m := ⟨fun _ _ _ _ _ h => h, fun _ h => h, fun h => h⟩

theorem VsSlotsT.trans (h1 : VsSlotsT th m m') (h2 : VsSlotsT th m' m'') : VsSlotsT th m m'' :=
  ⟨fun P L4 L3 L2 L1 h => h2.1 P L4 L3 L2 L1 (h1.1 P L4 L3 L2 L1 h), fun U h => h2.2.1 U (h1.2.1 U h),
    fun h => h2.2.2 (h1.2.2 h)⟩

theorem VsSlotsT.of_eq (hc : ∀ y, IsSlot th y → capV m' y = capV m y) : VsSlotsT th m m' :=
  ⟨fun _ _ _ _ _ h => h.of_eq hc, fun _ h => h.of_eq hc, fun h => h.of_eq hc⟩

/-- **Slots `W` rewritten**, each new cap placed whenever the old slots are
(a copy, move, swap, a remap: `VCapW.transfer` from a source slot), the
others kept. -/
theorem VsSlotsT.of_some (W : U64 → Prop) (hc : ∀ y, IsSlot th y → ¬ W y → capV m' y = capV m y)
    (hw : ∀ y, IsSlot th y → W y → ∀ P L4 L3 L2 L1 : Set U64, VsSlotsW th P L4 L3 L2 L1 m →
      VCapW P L4 L3 L2 L1 (capV m' y))
    (hf : ∀ y, IsSlot th y → W y → ∀ U : Nat → Prop, FrSlots th U m → FrIn U (capV m' y))
    (hn : ∀ y, IsSlot th y → W y → VsNat th m → NativeCap (capV m' y)) :
    VsSlotsT th m m' := by
  refine ⟨fun P L4 L3 L2 L1 h y hy => ?_, fun U h y hy => ?_, fun h y hy => ?_⟩
  · by_cases e : W y
    · exact hw y hy e P L4 L3 L2 L1 h
    · rw [hc y hy e]; exact h y hy
  · by_cases e : W y
    · exact hf y hy e U h
    · rw [hc y hy e]; exact h y hy
  · by_cases e : W y
    · exact hn y hy e h
    · rw [hc y hy e]; exact h y hy

/-- An untyped cap is placed. -/
theorem vcapW_ut {P L4 L3 L2 L1 : Set U64} {c : capability.Cap} (h : isUt c = true) : VCapW P L4 L3 L2 L1 c := by
  cases c <;> first | trivial | (simp [isUt] at h)

/-- A cap that is placed at every set (a non-VSpace or null cap). -/
theorem VCapW.of_nonVs {c : capability.Cap}
    (h : ∀ P L4 L3 L2 L1 : Set U64, VCapW P L4 L3 L2 L1 c) : VCapW P L4 L3 L2 L1 c := h _ _ _ _ _

/-- A copy of slot `x`'s cap (`VCapW.transfer`). -/
theorem VsSlotsW.copy (h : VsSlotsW th P L4 L3 L2 L1 m) {x : U64} (hx : IsSlot th x) {c : capability.Cap}
    (hv : ∀ P L4 L3 L2 L1 : Set U64, VCapOK P L4 L3 L2 L1 (capV m x) → VCapOK P L4 L3 L2 L1 c)
    (hu : TabUn c → TabUn (capV m x)) : VCapW P L4 L3 L2 L1 c :=
  (h x hx).transfer hv hu

end

end

end Fl4Proofs.P3.Vs