/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, invC): **the domain-list
frame of the spec's kernel entry** (spec side only, outside the JAtZ cone).

* `dlV σ := (domain_list, domain_start_index, domain_index)`: the three fields
  `DomListOK` (ScNextDom, l4v `valid_domain_list`) reads. `DL m := FK dlV m`
  (VsDom's projection frame, its combinators and `dk_step0`).
* `dl_auto`: VsDom's `dk_step0` plus the `DL` leaves and `sf_unfold`, which
  unfolds the spec function at the head of the goal (a copy of sch12's
  `fv_unfold`, XTopJointMidRunS, which is inside the JAtZ cone). Every spec
  function writes the three fields only in `next_domain` (`domain_index`),
  `domain_set_start` and `domain_schedule_configure`, so the frame is proved by
  unfolding down to the monad's combinators, except for the recursive
  functions: `resolve_address_bits` (well-founded recursion, `dle_rab`),
  `transfer_caps_loop` (list induction), `rec_del` and `cap_revoke` (the least
  fixed point, `lfp_le_prefixed'`), FL4's TCB timers `fl4Awaken` (a reflexive
  transitive closure of `send_signal` outcomes).
* The frames of the kernel entry's pieces but the three writers:
  `fl4SyscallFaultIP`, `updateTimeStamp`, `checkBudgetRestart`, the receive,
  the yield, the fault handler, the preemption path, the invocation's front
  and decode, every perform but the Domain invocation's, `fl4Awaken`,
  `activateThread`, and the non-syscall events.
-/
import Fl4Proofs.P3.VsDom
import Fl4Spec.Ext.Entry
open Classical

namespace Fl4Proofs.P3.SInvDom
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- The fields `DomListOK` reads. -/
def dlV (σ : State Unit) : List (Domain × DomainDuration) × Nat × Nat :=
  (σ.domainList, σ.domainStartIndex, σ.domainIndex)

/-- Every outcome of `m` keeps the domain list, its start and its index. -/
abbrev DL {α : Type} (m : NonDet (State Unit) α) : Prop := FK dlV m

/-- `DL` for the exception monad. -/
abbrev DLE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE dlV m

open Lean Meta Elab Tactic in
/-- Unfold the spec function at the head of an `FK`/`FKE` goal (sch12's
`fv_unfold`). -/
elab "sf_unfold" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let args := t.getAppArgs
  if args.size == 0 then throwError "sf_unfold: no arguments"
  let m := args.back!
  let m := if m.isAppOf ``ExceptT.run then m.getAppArgs.back! else m
  match m.getAppFn with
  | .const n _ =>
    if (`Fl4Spec).isPrefixOf n && !(`Fl4Spec.NonDet).isPrefixOf n && !(`Fl4Spec.NonDetE).isPrefixOf n then
      evalTactic (← `(tactic| unfold $(mkIdent n):ident))
    else throwError "sf_unfold: {n} is not a spec function"
  | _ => throwError "sf_unfold: no head constant"

/-- A `DL` lemma of a spec function (extended below, one rule per lemma). -/
syntax "dl_leaf" : tactic
macro_rules | `(tactic| dl_leaf) => `(tactic| fail "no dl_leaf")

macro "dl_auto" : tactic => `(tactic| repeat' (first | dl_leaf | dk_step0 | sf_unfold))

/-- `dl_auto` without unfolding (for the scripted copies of the `DK` lemmas). -/
macro "dl_auto0" : tactic => `(tactic| repeat' (first | dl_leaf | dk_step0))

/-! ## Leaves -/

theorem dl_doMachineOp {α : Type} (mop : NonDet MachineState α) : DL (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_doMachineOp _)

theorem dl_doExtendedOp (eop : DetExtMonad Unit) : DL (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_doExtendedOp _)

theorem dl_getCap (sl : CslotPtr) : DL (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; dsimp only
  repeat' dk_step0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getCap _)

theorem dle_rab (p : Cap × CapRef) : DLE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (dl_getCap _)) fun nc => ?_
        split
        · exact dle_rab _
        · exact dke_returnOk _
  · exact dke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_rab _)

theorem dl_zipWithMx {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, DL (g a b)) :
    ∀ l1 l2, DL (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => dl_zipWithMx h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible refine dl_zipWithMx (fun _ _ => ?_) _ _)

set_option maxRecDepth 20000

theorem dl_setObject (p : ObjRef) (o : KernelObject) : DL (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setObject _ _)

/-- A bind on a returned value (so that the continuation sees the value). -/
theorem dle_returnOk_bind {ε α β : Type} {v : α} {g : α → NonDetE (State Unit) ε β} (h : DLE (g v)) :
    DLE (NonDetE.returnOk v >>= g) := by
  show FK dlV (ExceptT.run (NonDetE.returnOk v >>= g))
  rw [ExceptT.run_bind]
  intro σ x ⟨y, hy, hx⟩
  obtain rfl := Set.mem_singleton_iff.1 hy
  exact h σ x hx
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible refine dle_returnOk_bind ?_)

end

end Fl4Proofs.P3.SInvDom
