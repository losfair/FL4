/-
P3 (DESIGN.md §9), invariant line G1 (vih2): **the frame of `ValidIrqHandlers`**
(spec side only; outside the `JAtZ` cone: SpecInvValidIrqHandlers and
SpecInvNativeScopeT).

* `hV σ`: what `ValidIrqHandlers` and `HK` read: every slot's cap as `get_cap`
  reads it (`capOpt`) and `interruptStates`.
* `WLH P` (a class): `P` reads only `hV` and invB's `vw` (time, IRQ states,
  masks), and is kept by `updateTimeStamp` and by machine operations that only
  mask (`MaskT`). Instances: `hV · = v` (frames), `ValidIrqMasks`,
  `ValidIrqHandlers`, `HK σ0 ·`, every predicate of `hV` alone (`wlh_of_hV`),
  conjunctions. The generated frames SpecInvValidIrqHandlersF1..F4
  (proofs/scratch/vih2/mkhv.sh, invA's gen.py as adapted by ut1) prove
  `[WLH P] → IK P f` for every spec function `f` reachable from the syscall
  entry that writes no cap, CDT link, original flag, heap address or IRQ state
  and does not ack an IRQ (ut1's writer set plus `setIrqState`, its callers
  `deletedIrqHandler`, `postCapDeletion`, and the ack `archInvokeIrqHandler`).
* `hkm_of_ikh`: such a function is an `HK` step (`HKM`).
* Leaves: `setObject` of an object with the same caps as the old one (the
  `aType` assertion makes every non-CNode, non-TCB write cap-free), the TCB
  writers that keep the six cap fields, machine and extended operations
  (`interruptStates` is a field of the kernel state, not of the machine).
-/
import Fl4Proofs.P3.SpecInvValidIrqHandlers
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- The view of `ValidIrqHandlers`: every slot's cap and the IRQ states. -/
abbrev HView := (CslotPtr → Option Cap) × (Irq → IrqState)

def hV (σ : State Unit) : HView := (fun sl => capOpt (σ.kheap sl.1) sl.2, σ.interruptStates)

/-- invA's `IK` (`SInvV.IK` is invB's copy of the same definition). -/
abbrev IKH (P : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop := SInv.IK P m
abbrev IKHE (P : State Unit → Prop) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := SInv.IKE P m

/-- **The leaves of a predicate reading `hV` and `vw`** (module docstring). -/
class WLH (P : State Unit → Prop) : Prop where
  view : ∀ σ σ', hV σ' = hV σ → vw σ' = vw σ → P σ → P σ'
  uts : SInv.IK P (updateTimeStamp (Z := Unit))
  msk : ∀ {α : Type} (mop : NonDet MachineState α), MaskT mop → SInv.IK P (doMachineOp (Z := Unit) mop)

theorem hV_cap {σ σ' : State Unit} (e : hV σ' = hV σ) (p : ObjRef) (cref : CnodeIndex) :
    capOpt (σ'.kheap p) cref = capOpt (σ.kheap p) cref :=
  congrArg (fun v : HView => v.1 (p, cref)) e

theorem hV_is {σ σ' : State Unit} (e : hV σ' = hV σ) : σ'.interruptStates = σ.interruptStates :=
  congrArg (fun v : HView => v.2) e

/-- Keeping the view is an `HK` step. -/
theorem hk_of_hV {σ σ' : State Unit} (e : hV σ' = hV σ) : HK σ σ' := by
  intro irq ⟨p, cref, h⟩
  refine Or.inr ⟨⟨p, cref, by rw [← hV_cap e]; exact h⟩, fun h' => by rw [hV_is e]; exact h'⟩

/-! ## Instances -/

theorem ik_dmo_any {P : State Unit → Prop} (hP : ∀ σ ms, P σ → P { σ with machineState := ms }) {α : Type}
    (mop : NonDet MachineState α) : SInv.IK P (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp hP mop

/-- `updateTimeStamp` keeps the caps and IRQ states. -/
theorem hv_uts (v : HView) : SInv.IK (fun σ => hV σ = v) (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp
  repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

/-- A predicate of the caps and IRQ states alone. -/
theorem wlh_of_hV {P : State Unit → Prop} (hP : ∀ σ σ', hV σ' = hV σ → P σ → P σ') : WLH P where
  view σ σ' e _ h := hP σ σ' e h
  uts σ h x hx := hP σ x.2 (hv_uts (hV σ) σ rfl x hx) h
  msk mop _ σ h x hx := hP σ x.2 (ik_doMachineOp (P := fun σ' => hV σ' = hV σ) (fun _ _ h => h) mop σ rfl x hx) h

instance (v : HView) : WLH (fun σ => hV σ = v) := wlh_of_hV fun _ _ e h => e.trans h

instance : WLH ValidIrqHandlers := wlh_of_hV fun σ σ' e h p cref irq hc => by
  rw [hV_is e]; exact h p cref irq (by rw [← hV_cap e]; exact hc)

instance (σ0 : State Unit) : WLH (fun σ => HK σ0 σ) := wlh_of_hV fun _ _ e h => h.trans (hk_of_hV e)

instance : WLH ValidIrqMasks where
  view σ σ' _ e h := vim_view σ σ' e h
  uts := vim_uts
  msk := vim_msk

instance {P Q : State Unit → Prop} [hp : WLH P] [hq : WLH Q] : WLH (fun σ => P σ ∧ Q σ) where
  view σ σ' e w h := ⟨hp.view σ σ' e w h.1, hq.view σ σ' e w h.2⟩
  uts σ h x hx := ⟨hp.uts σ h.1 x hx, hq.uts σ h.2 x hx⟩
  msk mop hm σ h x hx := ⟨hp.msk mop hm σ h.1 x hx, hq.msk mop hm σ h.2 x hx⟩

/-- A computation keeping every `WLH` predicate is an `HK` step. -/
theorem hkm_of_ikh {α : Type} {m : NonDet (State Unit) α} (h : ∀ σ0, IKH (fun σ => HK σ0 σ) m) : HKM m :=
  fun σ x hx => h σ σ (HK.refl σ) x hx

/-! ## Caps of objects -/

theorem capOpt_tcb (t : Tcb) : capOpt (some (.tcb t)) = tcbCnodeMap t := by funext c; rfl

/-- The type of a CNode is no simple or arch type, and a TCB's only a TCB's. -/
macro "hv_atype_ne" : tactic => `(tactic| first
  | (intro h; cases h; done)
  | (intro h; simp only [aType] at h; cases h; done)
  | (intro h; simp only [aType] at h; split at h <;> cases h; done)
  | (intro h; simp only [aType] at h; split at h <;> split at h <;> cases h; done)
  | (intro h; split at h <;> cases h; done)
  | (intro h; split at h <;> split at h <;> cases h; done))

/-- An object that is no CNode and no TCB, of the type of the old one: both hold no cap. -/
theorem hv_noCap {o old : KernelObject} (hc : ∀ sz cs, o ≠ .cnode sz cs) (ht : ∀ t, o ≠ .tcb t)
    (h : aType old = aType o) : capOpt (some o) = capOpt (some old) := by
  cases o with
  | cnode sz cs => exact absurd rfl (hc sz cs)
  | tcb t => exact absurd rfl (ht t)
  | _ =>
    revert h
    cases old with
    | cnode sz cs =>
      by_cases hw : wellFormedCnodeN sz cs
      · intro h; simp only [aType, if_pos hw] at h <;> (try split at h) <;> cases h
      · intro _; funext c; simp only [capOpt, if_neg hw]
    | tcb t => hv_atype_ne
    | _ => intro _; funext _; rfl

theorem hV_update {σ : State Unit} {p : ObjRef} {o old : KernelObject} (hk : σ.kheap p = some old)
    (ho : capOpt (some o) = capOpt (some old)) :
    hV { σ with kheap := Function.update σ.kheap p (some o) } = hV σ := by
  unfold hV
  refine Prod.ext (funext fun sl => ?_) rfl
  dsimp only
  by_cases e : sl.1 = p
  · rw [e, Function.update_self, hk, ho]
  · rw [Function.update_of_ne e]

/-! ## The leaves -/

section Leaves
variable {P : State Unit → Prop} [WLH P]

theorem hv_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : ∀ old, σ.kheap p = some old → aType old = aType o → capOpt (some o) = capOpt (some old)) :
    IKp P σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨old, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact WLH.view _ _ (hV_update hk (ho old hk hty)) rfl hσ

theorem hv_setObject (p : ObjRef) (o : KernelObject)
    (ho : ∀ old, aType old = aType o → capOpt (some o) = capOpt (some old)) : IKH P (setObject (Z := Unit) p o) :=
  fun σ => hv_setObject_p p o σ (fun old _ h => ho old h)

theorem hv_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    IKH P (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hsimp, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  refine hv_setObject_p p (f e) y2 (fun old hold hty => ?_) hσ x hx
  rw [hk] at hold; cases hold
  simp only [isSimpleType, Set.mem_insert_iff, Set.mem_singleton_iff] at hsimp
  refine hv_noCap (fun sz cs hc => ?_) (fun t hc => ?_) hty
  · rw [hc] at hty; revert hty; rcases hsimp with h | h | h <;> rw [h] <;> hv_atype_ne
  · rw [hc] at hty; revert hty; rcases hsimp with h | h | h <;> rw [h] <;> hv_atype_ne

theorem hv_threadSet (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, tcbCnodeMap (f x) = tcbCnodeMap x) :
    IKH P (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => hv_setObject_p _ _ σ fun old hold _ => ?_
  rw [getTcb_kheap hx] at hold; cases hold
  rw [capOpt_tcb, capOpt_tcb, hf x]

theorem hv_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : IKH P (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  refine ik_getsThe_bind fun x σ hx => hv_setObject_p _ _ σ fun old hold _ => ?_
  rw [getTcb_kheap hx] at hold; cases hold; rw [capOpt_tcb, capOpt_tcb]; rfl

theorem hv_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : IKH P (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (hv_setObject_p _ _ σ fun old hold _ => ?_) fun _ => ik_pure _
  rw [getTcb_kheap hx] at hold; cases hold; rw [capOpt_tcb, capOpt_tcb]; rfl

/-- The rest of `setMrs` after the register write: IPC-buffer stores. -/
macro "hv_mach" : tactic => `(tactic| repeat' (first | ik_step0 |
  ((with_reducible refine WLH.msk _ ?_); mt_auto; done) | ik_unfold))

theorem hv_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : IKH P (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (hv_setObject_p _ _ σ fun old hold _ => ?_) fun _ => ?_
  · rw [getTcb_kheap hx] at hold; cases hold; rw [capOpt_tcb, capOpt_tcb]; rfl
  · hv_mach

end Leaves

/-! ## `hv_auto` -/

/-- The side conditions of the leaves. -/
macro "hv_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro _; rfl)
  | (intro _ _; rfl)
  | (intro old hty; exact hv_noCap (fun _ _ h => by cases h) (fun _ h => by cases h) hty)
  | (intro _ _ _; rfl)
  | (simp; done)
  | decide)

syntax "hv_leaf" : tactic
macro_rules | `(tactic| hv_leaf) => `(tactic| fail "no hv_leaf")

macro "hv_auto" : tactic => `(tactic| repeat' (first | hv_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine WLH.msk _ ?_); mt_auto; done))
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact WLH.uts)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ik_doExtendedOp (fun _ _ h => WLH.view _ _ (by rfl) (by rfl) h) _)
macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible apply ik_modify); intro _ h; exact WLH.view _ _ (by rfl) (by rfl) h))
macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible apply ik_put_get); intro _ h; exact WLH.view _ _ (by rfl) (by rfl) h))
macro_rules | `(tactic| hv_leaf) => `(tactic| (exact ik_put_get (fun _ h => WLH.view _ _ (by rfl) (by rfl) h)))
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hv_setObject _ _ ?_); hv_side))
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hv_setSimpleKo _ _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hv_threadSet _ _ ?_); hv_side))
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hv_archThreadSet _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hv_asUser _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hv_setMrs _ _ _)

section Leaves2
variable {P : State Unit → Prop} [WLH P]

theorem hv_setThreadState (t : ObjRef) (ts : ThreadState) : IKH P (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (hv_threadSet _ _ fun _ => rfl) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; hv_auto

theorem hv_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ a x, tcbCnodeMap (fn a x) = tcbCnodeMap x) : IKH P (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact hv_threadSet _ _ (h _)

end Leaves2

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hv_setThreadState _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| ((with_reducible refine hv_optionUpdateThread _ _ _ ?_); hv_side))

end

end Fl4Proofs.P3.SInvV
