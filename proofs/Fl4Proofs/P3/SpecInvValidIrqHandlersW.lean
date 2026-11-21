/-
P3 (DESIGN.md §9), invariant line G1 (vih3): **the cap and IRQ-state writers
of `ValidIrqMasks ∧ ValidIrqHandlers`** (spec side only; outside the `JAtZ`
cone: SpecInvValidIrqHandlersD, SpecInvUt).

* `CA c is`: if `c` is a handler cap its line is not inactive in `is` (what
  l4v's `valid_irq_handlers` asks of a cap about to be written).
  `ca_of_slot`: a cap in a slot of a `ValidIrqHandlers` state is `CA`.
* `VH R σ := ValidIrqMasks σ ∧ ValidIrqHandlers σ ∧ R σ.interruptStates`, with
  `R` a fact about the IRQ states carried along (the `CA` of caps a later
  write will use); `VI := VH (fun _ => True)`. `VH R` is a `WLH` predicate, so
  the generated frames (SpecInvValidIrqHandlersF1..F4) keep it. `RM R`: `R`
  survives lines becoming non-inactive (the IRQ control issue).
* Leaves (`IKH (VH R)`): `set_cap` of a `CA` cap (`vh_setCap`; the machine
  fields by MachFieldFamT's `mtk_setCap`); `set_cdt` / `set_original` /
  `update_cdt` keep every `WLH` predicate; `set_untyped_cap_as_full`,
  `cap_insert`, `cap_move`, `cap_swap` of `CA` caps; `cap_swap_for_delete`
  (both caps read from slots); `create_cap` (default caps), `retype_region`
  (default objects hold no handler cap), `delete_objects` (removed objects
  hold no cap); `set_irq_state` of a non-inactive state for `RM R`.
-/
import Fl4Proofs.P3.SpecInvValidIrqHandlersD
import Fl4Proofs.P3.SpecInvUt
open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.MachT Fl4Proofs.P3.MachF

noncomputable section

set_option maxHeartbeats 1000000

/-- A cap that may be written: a handler cap names a line that is not inactive. -/
def CA (c : Cap) (is : Irq → IrqState) : Prop := ∀ irq, c = .irqHandlerCap irq → is irq ≠ .irqInactive

/-- `R` survives lines becoming non-inactive. -/
def RM (R : (Irq → IrqState) → Prop) : Prop :=
  ∀ is is', (∀ i, is i ≠ .irqInactive → is' i ≠ .irqInactive) → R is → R is'

/-- **The invariant with a carried IRQ-state fact** (module docstring). -/
def VH (R : (Irq → IrqState) → Prop) (σ : State Unit) : Prop :=
  ValidIrqMasks σ ∧ ValidIrqHandlers σ ∧ R σ.interruptStates

abbrev VI : State Unit → Prop := VH (fun _ => True)

theorem ca_of_slot {σ : State Unit} (h : ValidIrqHandlers σ) {p : ObjRef} {r : CnodeIndex} {c : Cap}
    (hc : capOpt (σ.kheap p) r = some c) : CA c σ.interruptStates :=
  fun irq e => h p r irq (e ▸ hc)

theorem rm_ca (c : Cap) : RM (CA c) := fun _ _ hm h irq e => hm irq (h irq e)
theorem rm_true : RM (fun _ => True) := fun _ _ _ _ => trivial
theorem rm_and {R1 R2 : (Irq → IrqState) → Prop} (h1 : RM R1) (h2 : RM R2) : RM (fun is => R1 is ∧ R2 is) :=
  fun is is' hm h => ⟨h1 is is' hm h.1, h2 is is' hm h.2⟩

theorem ca_noH {c : Cap} (h : ∀ irq, c ≠ .irqHandlerCap irq) (is : Irq → IrqState) : CA c is :=
  fun irq e => absurd e (h irq)

instance (R : (Irq → IrqState) → Prop) : WLH (VH R) where
  view σ σ' e w h := ⟨WLH.view (P := ValidIrqMasks) σ σ' e w h.1,
    WLH.view (P := ValidIrqHandlers) σ σ' e w h.2.1, by rw [hV_is e]; exact h.2.2⟩
  uts σ h x hx := ⟨WLH.uts (P := ValidIrqMasks) σ h.1 x hx, WLH.uts (P := ValidIrqHandlers) σ h.2.1 x hx,
    by rw [hV_is (hv_uts (hV σ) σ rfl x hx)]; exact h.2.2⟩
  msk mop hm σ h x hx := ⟨WLH.msk (P := ValidIrqMasks) mop hm σ h.1 x hx,
    WLH.msk (P := ValidIrqHandlers) mop hm σ h.2.1 x hx,
    by rw [hV_is (ik_doMachineOp (P := fun σ' => hV σ' = hV σ) (fun _ _ h => h) mop σ rfl x hx)]; exact h.2.2⟩

theorem is_of_vw {σ σ' : State Unit} (e : vw σ' = vw σ) : σ'.interruptStates = σ.interruptStates :=
  congrArg (fun v => v.2.2.1) e

/-- A step keeping the machine fields keeps `ValidIrqMasks` and `R`; `VH R`
follows from `ValidIrqHandlers`. -/
theorem vh_of_mtk {R : (Irq → IrqState) → Prop} {σ σ' : State Unit} (e : msFT σ' = msFT σ) (h : VH R σ)
    (hh : ValidIrqHandlers σ') : VH R σ' :=
  ⟨vim_view σ σ' (vw_of_msFT e) h.1, hh, by rw [is_of_vw (vw_of_msFT e)]; exact h.2.2⟩

/-! ## Pinned binds -/

/-- A bind on `get_cap`, the continuation at the read state with the read cap. -/
theorem ik_getCap_bind {P : State Unit → Prop} {β : Type} {sl : CslotPtr} {k : Cap → NonDet (State Unit) β}
    (h : ∀ c σ, capOpt (σ.kheap sl.1) sl.2 = some c → IKp P σ (k c)) : IK P (getCap (Z := Unit) sl >>= k) := by
  obtain ⟨o, r⟩ := sl
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨e1, e2⟩ := vih_mem_getCap hy
  obtain ⟨c, s⟩ := y
  simp only at e1 e2; subst e1
  exact h c s e2 hσ x hx

theorem ikp_getCap_bind {P : State Unit → Prop} {β : Type} {σ : State Unit} {sl : CslotPtr}
    {k : Cap → NonDet (State Unit) β}
    (h : ∀ c, capOpt (σ.kheap sl.1) sl.2 = some c → IKp P σ (k c)) : IKp P σ (getCap (Z := Unit) sl >>= k) := by
  obtain ⟨o, r⟩ := sl
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨e1, e2⟩ := vih_mem_getCap hy
  obtain ⟨c, s⟩ := y
  simp only at e1 e2; subst e1
  exact h c e2 hσ x hx

/-- Strengthen the carried fact for one step. -/
theorem ikp_vh_and {R Q : (Irq → IrqState) → Prop} {α : Type} {m : NonDet (State Unit) α} {σ : State Unit}
    (hm : IKH (VH fun is => R is ∧ Q is) m) (hq : Q σ.interruptStates) : IKp (VH R) σ m :=
  fun h x hx => let h' := hm σ ⟨h.1, h.2.1, h.2.2, hq⟩ x hx; ⟨h'.1, h'.2.1, h'.2.2.1⟩

theorem ik_vh_weaken {R Q : (Irq → IrqState) → Prop} {α : Type} {m : NonDet (State Unit) α}
    (hm : IKH (VH Q) m) (hq : ∀ is, R is → Q is) (hr : ∀ σ x, x ∈ (m σ).1 → Q σ.interruptStates →
      R σ.interruptStates → R x.2.interruptStates) : IKH (VH R) m :=
  fun σ h x hx => let h' := hm σ ⟨h.1, h.2.1, hq _ h.2.2⟩ x hx; ⟨h'.1, h'.2.1, hr σ x hx (hq _ h.2.2) h.2.2⟩

/-! ## CDT and original-flag writers (every `WLH` predicate) -/

section W
variable {P : State Unit → Prop} [WLH P]

theorem hv_setCdt (t : Cdt) : IKH P (setCdt (Z := Unit) t) := by unfold setCdt; hv_auto
theorem hv_updateCdt (f : Cdt → Cdt) : IKH P (updateCdt (Z := Unit) f) := by
  unfold updateCdt; refine ik_bind (ik_gets _) fun _ => hv_setCdt _
theorem hv_setOriginal (sl : CslotPtr) (v : Bool) : IKH P (setOriginal (Z := Unit) sl v) := by
  unfold setOriginal; hv_auto

end W

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hv_setCdt _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hv_updateCdt _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hv_setOriginal _ _)

/-! ## `set_cap` -/

section C
variable {R : (Irq → IrqState) → Prop}

theorem vh_setCap_p (c : Cap) (sl : CslotPtr) (σ : State Unit) (hc : VH R σ → CA c σ.interruptStates) :
    IKp (VH R) σ (setCap (Z := Unit) c sl) := by
  intro h x hx
  have e := mtk_setCap c sl σ x hx
  exact vh_of_mtk e h (h.2.1.hk (hk_setCap sl (fun irq e' => Or.inr (hc h irq e')) x hx))

theorem vh_setCap (c : Cap) (sl : CslotPtr) (hc : ∀ is, R is → CA c is) : IKH (VH R) (setCap (Z := Unit) c sl) :=
  fun σ => vh_setCap_p c sl σ fun h => hc _ h.2.2

end C

/-- Side conditions `∀ is, R is → CA c is`. -/
macro "ca_side" : tactic => `(tactic| first
  | assumption
  | (intro _ _ _ h; cases h; done)
  | (intro _ _; exact ca_noH (by intro _ h; cases h) _)
  | (intro _ h; exact h.1)
  | (intro _ h; exact h.2.1)
  | (intro _ h; exact h.2)
  | (intro _ _; exact ca_noH (fun _ h => by simp_all) _))

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine vh_setCap _ _ ?_); ca_side))

section C2
variable {R : (Irq → IrqState) → Prop}

theorem ca_freeIndexUpdate_ut {c : Cap} (h : isUntypedCap c = true) (g : Nat → Nat) (is : Irq → IrqState) :
    CA (freeIndexUpdate g c) is := by
  cases c <;> first | (simp [isUntypedCap] at h; done) | exact ca_noH (fun _ e => by simp [freeIndexUpdate] at e) _

theorem vh_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : CslotPtr) :
    IKH (VH R) (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull
  split
  · rename_i h
    exact vh_setCap _ _ fun is _ => ca_freeIndexUpdate_ut (by simpa using h.1) _ is
  · exact ik_pure _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vh_setUntypedCapAsFull _ _ _)

theorem vh_capInsert (c : Cap) (src dst : CslotPtr) (hc : ∀ is, R is → CA c is) :
    IKH (VH R) (capInsert (Z := Unit) c src dst) := by
  unfold capInsert; hv_auto

theorem vh_capMove (c : Cap) (src dst : CslotPtr) (hc : ∀ is, R is → CA c is) :
    IKH (VH R) (capMove (Z := Unit) c src dst) := by
  unfold capMove; hv_auto

theorem vh_capSwap (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) (hc1 : ∀ is, R is → CA c1 is)
    (hc2 : ∀ is, R is → CA c2 is) : IKH (VH R) (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap; hv_auto

/-- `cap_swap_for_delete`: both caps are read from slots of the same state. -/
theorem vh_capSwapForDelete (s1 s2 : CslotPtr) : IKH (VH R) (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete
  refine ik_when _ (ik_getCap_bind fun c1 σ h1 => ikp_getCap_bind fun c2 h2 hσ => ?_)
  refine ikp_vh_and (Q := fun is => CA c1 is ∧ CA c2 is)
    (vh_capSwap c1 s1 c2 s2 (fun _ h => h.2.1) (fun _ h => h.2.2)) ⟨ca_of_slot hσ.2.1 h1, ca_of_slot hσ.2.1 h2⟩ hσ

theorem ca_defaultCap (t : ApiObjectType) (o : ObjRef) (b : Nat) (d : Bool) (is : Irq → IrqState) :
    CA (defaultCap t o b d) is :=
  ca_noH (fun _ e => by cases t <;> simp only [defaultCap] at e <;> cases e) _

theorem vh_createCap (t : ApiObjectType) (b : Nat) (u : CslotPtr) (d : Bool) (x : CslotPtr × ObjRef) :
    IKH (VH R) (createCap (Z := Unit) t b u d x) := by
  obtain ⟨dest, oref⟩ := x
  unfold createCap; dsimp only
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_gets _) fun _ => ik_bind (hv_setCdt _) fun _ =>
    ik_bind (ik_doExtendedOp (fun _ _ h => WLH.view _ _ (by rfl) (by rfl) h) _) fun _ =>
    ik_bind (hv_setOriginal _ _) fun _ => vh_setCap _ _ fun is _ => ca_defaultCap _ _ _ _ is

end C2

/-! ## Retype and detype -/

theorem capOpt_default_noH {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (n : Nat) (d : Domain)
    (cref : CnodeIndex) (irq : Irq) : capOpt (some (defaultObject ty dev n d)) cref ≠ some (.irqHandlerCap irq) := by
  intro h
  cases ty with
  | untyped => exact hty rfl
  | capTableObject =>
    simp only [defaultObject, capOpt] at h
    split_ifs at h with h1
    simp only [emptyCnode] at h
    split_ifs at h with h2
    cases h
  | tcbObject =>
    simp only [defaultObject, capOpt, tcbCnodeMap, defaultTcb, Function.update_apply] at h
    split_ifs at h <;> cases h
  | archObject a => simp only [defaultObject, capOpt] at h; cases h
  | _ => simp only [defaultObject, capOpt] at h; cases h

section RT
variable {R : (Irq → IrqState) → Prop}

theorem vh_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType)
    (dev : Bool) : IKH (VH R) (retypeRegionWith (Z := Unit) bA ptr n oB ty dev) := by
  intro σ h y hy
  have e := mtk_retypeRegionWith' bA ptr n oB ty dev σ y hy
  refine vh_of_mtk e h ?_
  rcases (SInvU.retypeRegionWith_out hy).2 with e' | ⟨hty, e'⟩
  · rw [e']; exact h.2.1
  · rw [e']
    intro p cref irq hc
    have ei := is_of_vw (vw_of_msFT e)
    rw [e'] at ei
    simp only [SInvU.retKh] at hc
    split_ifs at hc
    · exact absurd hc (capOpt_default_noH hty _ _ _ _ _)
    · exact h.2.1 p cref irq hc

theorem vh_retypeRegion (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool) :
    IKH (VH R) (retypeRegion (Z := Unit) ptr n oB ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact vh_retypeRegionWith _ _ _ _ _ _

theorem vh_deleteObjects (ptr : Word) (bits : Nat) : IKH (VH R) (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  refine ik_bind (WLH.msk _ (mt_freeMemory _ _)) fun _ => ik_modify fun σ h => ?_
  refine ⟨vim_view σ _ rfl h.1, fun p cref irq hc => ?_, h.2.2⟩
  simp only [detype] at hc
  split_ifs at hc
  · simp [capOpt] at hc
  · exact h.2.1 p cref irq hc

end RT

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vh_createCap _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vh_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vh_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vh_deleteObjects _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vh_capSwapForDelete _ _)

/-! ## `set_irq_state` -/

theorem vh_setIrqState_active {R : (Irq → IrqState) → Prop} (hR : RM R) {st : IrqState}
    (hst : st ≠ .irqInactive) (i : Irq) : IKH (VH R) (setIrqState (Z := Unit) st i) := by
  intro σ h x hx
  obtain ⟨hk, hi⟩ := setIrqState_out hx
  refine ⟨vim_sis st i σ h.1 x hx, h.2.1.hk (hk_setIrqState_active hst i σ x hx), ?_⟩
  refine hR _ _ (fun j hj => ?_) h.2.2
  rw [hi]; by_cases e : j = i
  · subst e; rw [Function.update_self]; exact hst
  · rw [Function.update_of_ne e]; exact hj

end

end Fl4Proofs.P3.SInvV
