/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut1): **the cap-state
frame of the spec** (spec side only; imports only Fl4Spec via
SpecInvNativeScopeT, outside the JAtZ cone).

* `capView o`: the caps a kernel object holds as `get_cap` reads them (a
  well-formed CNode's slots, a TCB's six slots, nothing else); `capAt σ sl`:
  the cap in slot `sl` (l4v `caps_of_state`).
* `uV σ`: the view the untyped invariants of SpecInvUt read: which heap
  addresses hold an object, every slot's cap, the CDT and the original flags.
  `UK v m := IK (uV · = v) m` (every outcome of `m` keeps the view): the
  generated frames SpecInvUtF1..F3 prove it for every spec function reachable
  from the syscall entry that writes no cap, no CDT link, no original flag and
  no heap address (`setCap`, `setCdt`, `setOriginal`, `retypeRegion`,
  `deleteObjects` and their callers are the writers, SpecInvUt).
* Leaves: `setObject` of an object with the same caps as the old one (the
  `aType` assertion makes every non-CNode, non-TCB write cap-free), the TCB
  writers that keep the six cap fields, machine and extended operations.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- The caps an object holds as `get_cap` reads them. -/
def capView : KernelObject → CnodeIndex → Option Cap
  | .cnode sz cs => if wellFormedCnodeN sz cs then cs else fun _ => none
  | .tcb t => tcbCnodeMap t
  | _ => fun _ => none

/-- The cap in a slot (l4v `caps_of_state`). -/
def capAt (σ : State Unit) (sl : CslotPtr) : Option Cap :=
  match σ.kheap sl.1 with
  | some o => capView o sl.2
  | none => none

/-- The view of the untyped invariants. -/
abbrev UView := (ObjRef → Bool) × (CslotPtr → Option Cap) × Cdt × (CslotPtr → Bool)

def uV (σ : State Unit) : UView :=
  (fun p => (σ.kheap p).isSome, capAt σ, σ.cdt, σ.isOriginalCap)

/-- Every outcome keeps the view. -/
abbrev UK (v : UView) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (fun σ => uV σ = v) m
abbrev UKE (v : UView) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (fun σ => uV σ = v) m

/-! ## Caps of objects -/

theorem capView_tcb (t : Tcb) : capView (.tcb t) = tcbCnodeMap t := rfl

theorem capView_cnode (sz : Nat) (cs : CnodeContents) :
    capView (.cnode sz cs) = if wellFormedCnodeN sz cs then cs else fun _ => none := rfl

/-- The type of a CNode is no simple or arch type, and a TCB's only a TCB's. -/
macro "atype_ne" : tactic => `(tactic| first
  | (intro h; cases h; done)
  | (intro h; simp only [aType] at h; cases h; done)
  | (intro h; simp only [aType] at h; split at h <;> cases h; done)
  | (intro h; simp only [aType] at h; split at h <;> split at h <;> cases h; done)
  | (intro h; split at h <;> cases h; done)
  | (intro h; split at h <;> split at h <;> cases h; done))

/-- An object that is no CNode and no TCB, of the type of the old one: both hold no cap. -/
theorem cv_noCap {o old : KernelObject} (hc : ∀ sz cs, o ≠ .cnode sz cs) (ht : ∀ t, o ≠ .tcb t)
    (h : aType old = aType o) : capView o = capView old := by
  cases o with
  | cnode sz cs => exact absurd rfl (hc sz cs)
  | tcb t => exact absurd rfl (ht t)
  | _ =>
    revert h
    cases old with
    | cnode sz cs =>
      rw [capView_cnode]
      by_cases hw : wellFormedCnodeN sz cs
      · rw [if_pos hw]; atype_ne
      · rw [if_neg hw]; intro _; rfl
    | tcb t => atype_ne
    | _ => intro _; rfl

theorem uV_update {σ : State Unit} {p : ObjRef} {o old : KernelObject} (hk : σ.kheap p = some old)
    (ho : capView o = capView old) :
    uV { σ with kheap := Function.update σ.kheap p (some o) } = uV σ := by
  unfold uV
  have h1 : (fun q => (Function.update σ.kheap p (some o) q).isSome) = fun q => (σ.kheap q).isSome := by
    funext q
    by_cases e : q = p
    · subst e; rw [Function.update_self, hk]; rfl
    · rw [Function.update_of_ne e]
  have h2 : capAt { σ with kheap := Function.update σ.kheap p (some o) } = capAt σ := by
    funext sl
    unfold capAt
    by_cases e : sl.1 = p
    · simp only [e, Function.update_self, hk, ho]
    · simp only [Function.update_of_ne e]
  rw [h1, h2]

/-! ## The leaves -/

section Leaves
variable {v : UView}

theorem uk_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : ∀ old, σ.kheap p = some old → aType old = aType o → capView o = capView old) :
    IKp (fun σ => uV σ = v) σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨old, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  show uV { y2 with kheap := Function.update y2.kheap p (some o) } = v
  rw [uV_update hk (ho old hk hty)]; exact hσ

theorem uk_setObject (p : ObjRef) (o : KernelObject)
    (ho : ∀ old, aType old = aType o → capView o = capView old) : UK v (setObject (Z := Unit) p o) :=
  fun σ => uk_setObject_p p o σ (fun old _ h => ho old h)

theorem uk_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    UK v (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hsimp, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  refine uk_setObject_p p (f e) y2 (fun old hold hty => ?_) hσ x hx
  rw [hk] at hold; cases hold
  simp only [isSimpleType, Set.mem_insert_iff, Set.mem_singleton_iff] at hsimp
  refine cv_noCap (fun sz cs hc => ?_) (fun t hc => ?_) hty
  · rw [hc] at hty; revert hty; rcases hsimp with h | h | h <;> rw [h] <;> atype_ne
  · rw [hc] at hty; revert hty; rcases hsimp with h | h | h <;> rw [h] <;> atype_ne

theorem uk_threadSet (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, tcbCnodeMap (f x) = tcbCnodeMap x) :
    UK v (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => uk_setObject_p _ _ σ fun old hold _ => ?_
  rw [getTcb_kheap hx] at hold; cases hold
  exact hf x

theorem uk_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : UK v (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  refine ik_getsThe_bind fun x σ hx => uk_setObject_p _ _ σ fun old hold _ => ?_
  rw [getTcb_kheap hx] at hold; cases hold; rfl

theorem uk_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : UK v (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (uk_setObject_p _ _ σ fun old hold _ => ?_) fun _ => ik_pure _
  rw [getTcb_kheap hx] at hold; cases hold; rfl

/-- The rest of `setMrs` after the register write: IPC-buffer stores. -/
macro "uk_mach" : tactic => `(tactic| repeat' (first | ik_step0 |
  (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold))

theorem uk_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : UK v (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (uk_setObject_p _ _ σ fun old hold _ => ?_) fun _ => ?_
  · rw [getTcb_kheap hx] at hold; cases hold; rfl
  · uk_mach

end Leaves

/-! ## `uk_auto` -/

/-- The side conditions of the leaves. -/
macro "uk_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro _; rfl)
  | (intro _ _; rfl)
  | (intro old hty; exact cv_noCap (fun _ _ h => by cases h) (fun _ h => by cases h) hty)
  | (intro _ _ _; rfl)
  | (simp; done)
  | decide)

syntax "uk_leaf" : tactic
macro_rules | `(tactic| uk_leaf) => `(tactic| fail "no uk_leaf")

macro "uk_auto" : tactic => `(tactic| repeat' (first | uk_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| uk_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); uk_side))
macro_rules | `(tactic| uk_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); uk_side))
macro_rules | `(tactic| uk_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| uk_leaf) => `(tactic| ((with_reducible refine uk_setObject _ _ ?_); uk_side))
macro_rules | `(tactic| uk_leaf) => `(tactic| with_reducible exact uk_setSimpleKo _ _ _)
macro_rules | `(tactic| uk_leaf) => `(tactic| ((with_reducible refine uk_threadSet _ _ ?_); uk_side))
macro_rules | `(tactic| uk_leaf) => `(tactic| with_reducible exact uk_archThreadSet _ _)
macro_rules | `(tactic| uk_leaf) => `(tactic| with_reducible exact uk_asUser _ _)
macro_rules | `(tactic| uk_leaf) => `(tactic| with_reducible exact uk_setMrs _ _ _)

section Leaves2
variable {v : UView}

theorem uk_setThreadState (t : ObjRef) (ts : ThreadState) : UK v (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (uk_threadSet _ _ fun _ => rfl) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; uk_auto

theorem uk_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ a x, tcbCnodeMap (fn a x) = tcbCnodeMap x) : UK v (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact uk_threadSet _ _ (h _)

end Leaves2

macro_rules | `(tactic| uk_leaf) => `(tactic| with_reducible exact uk_setThreadState _ _)
macro_rules | `(tactic| uk_leaf) => `(tactic| ((with_reducible refine uk_optionUpdateThread _ _ _ ?_); uk_side))

/-- A predicate that reads only the view is kept by a `UK` computation. -/
theorem ik_of_uk {P : State Unit → Prop} (hP : ∀ σ σ', uV σ' = uV σ → P σ → P σ') {α : Type}
    {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK P m :=
  fun σ hσ x hx => hP σ x.2 (h (uV σ) σ rfl x hx) hσ

end

end Fl4Proofs.P3.SInvU
