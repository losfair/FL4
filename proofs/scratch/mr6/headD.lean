/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr6): **the FL4 arch state
through the deletion's finalisation keeps `MR`** (`MRKeepD`, `MKD.*`).
MachKeep's `MRKeep` / `MK.*` walk, widened to the arch operations that FL4's
`finalise_cap` reaches (scripted call-graph check, scratch/mr6/cg.py +
topo.py): the TLB and EPT invalidations, `set_vspace`, `dma_frame`,
`irq_free`, besides MRKeep's FPU / remote-stall / VCPU-barrier operations.

* `MRKeepD arI AR` [P]: those state-returning arch operations keep `AR` at
  every second argument (with `AR := MR`: none of them changes an IRQ mask,
  a pending line or the clock; l4v: `invalidateTranslation*`,
  `invalidateASID`, `invalidateLocalPageStructureCacheASID`, `setCurrentCR3`,
  the FPU operations are `machine_op_lift`s outside `irq_masks`,
  `irq_state`, `time_state`, `last_machine_time`; `irq_free` / `dma_frame`
  are FL4's IOAPIC-routing / IOMMU bookkeeping, no machine field of the
  spec). Arch-only (∀ a, no spec state); the model platform satisfies it
  (XTopJointMRDel's `modelArch_mrKeepD`; not here: P1-level imports change `step`). `MRKeepD.toK`: MRKeep is a field subset.
* `mask_irq` is not a field (it moves `MR`: `MachPlat.mask`). It is reached
  from `finalise_cap` only through `cdt.empty_slot`'s `post_cap_deletion`
  of the cleanup cap, and `cdt.delete_one` (the IRQ handler's notification
  slot) empties with a `Null` cleanup: `MKD.cdt_empty_slot` is stated for
  `Null` only.
* `MKD.*`: one walk per arch-threading function of `finalise_cap`'s call
  graph, bottom-up (generated: scratch/mr6/mkdgen.py), the two fuel loops
  (`vcpu.revoke_ports_loop`, `vspace.delete_asid_pool_loop`) by
  `loop.spec_decr_nat` with `AR` as the invariant; top `MKD.objects_finalise_cap`.
-/
import Fl4Proofs.P3.MachKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

section
variable {A C : Type} (arI : machine.Arch A)

/-- **[P] The state-returning arch operations of the finalisation other than
`mask_irq` keep `AR`** (module docstring). -/
structure MRKeepD (AR : A → C → Prop) : Prop where
  set_deadline : ∀ a d c, AR a c → arI.set_deadline a d ⦃ a' => AR a' c ⦄
  send_reschedule : ∀ a m c, AR a c → arI.send_reschedule a m ⦃ a' => AR a' c ⦄
  remote_stall : ∀ a cpu c, AR a c → arI.remote_stall a cpu ⦃ a' => AR a' c ⦄
  fpu_flush : ∀ a t c, AR a c → arI.fpu_flush a t ⦃ a' => AR a' c ⦄
  fpu_release : ∀ a t c, AR a c → arI.fpu_release a t ⦃ a' => AR a' c ⦄
  fpu_sanitise : ∀ a t c, AR a c → arI.fpu_sanitise a t ⦃ a' => AR a' c ⦄
  fpu_reload : ∀ a t c, AR a c → arI.fpu_reload a t ⦃ a' => AR a' c ⦄
  vcpu_barrier : ∀ a c, AR a c → arI.vcpu_barrier a ⦃ a' => AR a' c ⦄
  invalidate_ept : ∀ a x y c, AR a c → arI.invalidate_ept a x y ⦃ a' => AR a' c ⦄
  invalidate_page : ∀ a x y c, AR a c → arI.invalidate_page a x y ⦃ a' => AR a' c ⦄
  invalidate_asid : ∀ a x c, AR a c → arI.invalidate_asid a x ⦃ a' => AR a' c ⦄
  invalidate_page_structures : ∀ a x c, AR a c → arI.invalidate_page_structures a x ⦃ a' => AR a' c ⦄
  set_vspace : ∀ a x y c, AR a c → arI.set_vspace a x y ⦃ a' => AR a' c ⦄
  dma_frame : ∀ a x y b c, AR a c → arI.dma_frame a x y b ⦃ a' => AR a' c ⦄
  irq_free : ∀ a x c, AR a c → arI.irq_free a x ⦃ a' => AR a' c ⦄

theorem MRKeepD.toK {AR : A → C → Prop} (h : MRKeepD arI AR) : MRKeep arI AR :=
  ⟨h.set_deadline, h.send_reschedule, h.remote_stall, h.fpu_flush, h.fpu_release, h.fpu_sanitise,
    h.fpu_reload, h.vcpu_barrier⟩

end

open Lean Elab Tactic Meta in
/-- MachKeep's `mk_call` with `MRKeepD`'s fields and the `MKD.*` lemmas. -/
elab "mkd_call" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``Aeneas.Std.WP.spec do throwError "mkd_call: not a spec"
  let args := target.getAppArgs
  let program := args[args.size - 2]!
  let program ← match ← Lean.Meta.reduceMatcher? program with
    | Lean.Meta.ReduceMatcherResult.reduced e => pure e.headBeta
    | _ => pure program
  let (m, bound) := match Aeneas.Step.getBindArgs? program with
    | some (m, _) => (m, true)
    | none => (program, false)
  let some n := m.getAppFn.constName? | throwError "mkd_call: no constant head"
  let hS := mkIdent `hS
  let hA := mkIdent `hA
  let hK := mkIdent `hK
  if n.getPrefix == ``fl4_core.machine.Arch then
    let fld := `MRKeepD ++ Name.mkSimple n.getString!
    unless (← getEnv).contains (``Fl4Proofs.P3.MRKeepD ++ Name.mkSimple n.getString!) do
      throwError "mkd_call: not a field"
    let f := mkIdent fld
    let k := (m.getAppNumArgs) - 3
    let us : Array (TSyntax `term) := Array.replicate (k + 2) (← `(_))
    if bound then
      evalTactic (← `(tactic| refine WP.spec_bind ($f $hK $us* (by assumption)) (fun _ _ => ?_)))
    else
      evalTactic (← `(tactic| exact $f $hK $us* (by assumption)))
  else
    let ak := `Fl4Proofs.P3.MKD ++ Name.mkSimple (((n.replacePrefix `fl4_core .anonymous).toString).replace "." "_")
    unless (← getEnv).contains ak do throwError "mkd_call: not an arch-threading function"
    let f := mkIdent ak
    if bound then
      evalTactic (← `(tactic| refine WP.spec_bind ($f $hS $hA $hK (by assumption)) (fun _ _ => ?_)))
    else
      evalTactic (← `(tactic| exact $f $hS $hA $hK (by assumption)))

macro "mkd_close" : tactic => `(tactic| try (first | assumption | (simp only at *; assumption) |
  (refine ⟨?_, ?_⟩ <;> (first | assumption | (simp only at *; assumption) | p0_close)) | p0_close))

macro "mkd_walk" : tactic => `(tactic|
  ((repeat' (first | mkd_call | p0_ite_head | (simp only [bind_tc_ok, bind_ok, bind_assoc_eq, Aeneas.Std.bind_assoc, Aeneas.Std.uncurry]) | p0_cases_prod | (dsimp only) | step | split)) <;> mkd_close))

/-- `mkd_walk` closing by assumption only (for bodies where the closers' `simp` recurses too deep). -/
macro "mkd_walk'" : tactic => `(tactic|
  ((repeat' (first | mkd_call | p0_ite_head | (simp only [bind_tc_ok, bind_ok, bind_assoc_eq, Aeneas.Std.bind_assoc, Aeneas.Std.uncurry]) | p0_cases_prod | (dsimp only) | step | split)) <;> try (first | assumption | (rw [WP.spec_ok]; assumption))))

section
variable {S A C : Type} {st : machine.Store S} {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : MRKeepD arI AR) {c₀ : C}
include hS hA hK
set_option linter.unusedSectionVars false

/-- `empty_slot` with a `Null` cleanup (its `post_cap_deletion` does nothing). -/
theorem MKD.cdt_empty_slot {s : S} {a : A} {slot : obj.Slot} (h : AR a c₀) :
    cdt.empty_slot st arI s a slot .Null ⦃ r => AR r.2 c₀ ⦄ := by
  unfold cdt.empty_slot objects.post_cap_deletion; mkd_walk

