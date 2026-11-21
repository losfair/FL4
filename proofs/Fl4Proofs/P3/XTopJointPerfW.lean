/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch26): **`JMidPerfHypQ` and
`JMidPerfHypB` [W] from a region fact and the IRQ handler family.**

XTopJointPerfU proves the Untyped (with the reset and its preemption points)
and ASID control performs keep `CQ` / `BI` where the region they touch avoids
the current thread and every SC a TCB is bound to (`RegC`). That fact is not a
property of the spec's operations (`retype_region` / `delete_objects` write any
address they are given): it is l4v's region freeness at the state the perform
starts in, so it is named here, at the `MidPerfAt` states only:

* `PerfRegOK ct inv σ1` / `JPerfRegHyp cptr σ` [J]: Untyped: `RegC ct (utD ..)`
  (the reset region of the source cap if `reset`, and the new objects'
  addresses); ASID control: `RegC ct (asidD frame)`. l4v:
  `invoke_untyped_invs`' precondition `valid_untyped_inv` (the retyped range is
  free, `descendants_range_in`; a reset untyped has no children, so by
  `valid_untyped` + `if_live_then_nonz_cap` no live object, in particular not
  `cur_thread` nor a bound SC (`sym_refs`), lies in it) and
  `perform_asid_control_invocation`'s `valid_aci` (`descendants_range`,
  `cte_wp_at` of a childless page-sized untyped). True in reachable states.
* `JPerfIrqHypQ` / `JPerfIrqHypB` [W]: the old premises restricted to the IRQ
  handler set / clear performs (`cap_delete_one` of the IRQ slot's cap:
  `fast_finalise` of a notification cap, `cancel_all_signals`).
* `midPerfAt_cq`: `CQ ∧ NQ` at the `MidPerfAt` state from the dispatch state.
* `jMidPerfHypQ_of`, `jMidPerfHypB_of`.
-/
import Fl4Proofs.P3.XTopJointPerfU
open Classical

namespace Fl4Proofs.P3.MidRun
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- The region fact of the Untyped / ASID control performs (module docstring). -/
def PerfRegOK (ct : ObjRef) : Fl4Invocation → State Unit → Prop
  | .invokeUntyped (.retype srcSlot reset _ rb ty objSz slots _), σ1 =>
      RegC ct (utD srcSlot σ1 reset rb ty objSz slots.length) σ1
  | .invokeArchObject (.spec (.invokeASIDControl (.makePool frame _ _ _))), σ1 => RegC ct (asidD frame) σ1
  | _, _ => True

/-- **[J] The Untyped and ASID control performs touch a region avoiding the
current thread and every bound SC**, at the states where they start on a run
of the first-phase invocation from the dispatch state `σ` (module docstring). -/
def JPerfRegHyp (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ inv σ1, MidPerfAt cptr σ inv σ1 → PerfRegOK σ.curThread inv σ1

/-- **[W] `JMidPerfHypQ` for the IRQ handler set / clear performs only**
(l4v `invoke_irq_handler`: `cap_delete_one` restarts only
`BlockedOnNotification` threads, not `ct`). -/
def JPerfIrqHypQ (don : Bool) (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ i σ1, MidPerfAt cptr σ (.invokeIRQHandler i) σ1 → PerfW (.invokeIRQHandler i) →
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false don (.invokeIRQHandler i)).run σ1).1, CQ σ.curThread y.2

/-- **[W] `JMidPerfHypB` for the IRQ handler set / clear performs only**
(l4v `invoke_irq_handler` keeps `sym_refs` of the SC binding,
`cur_sc_tcb_are_bound`, `ct_not_in_release_q`). -/
def JPerfIrqHypB (don : Bool) (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ i σ1, MidPerfAt cptr σ (.invokeIRQHandler i) σ1 → PerfW (.invokeIRQHandler i) → BI σ.curThread σ1 →
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false don (.invokeIRQHandler i)).run σ1).1, BI σ.curThread y.2

/-- `CQ ∧ NQ` at a `MidPerfAt` state from the dispatch state. -/
theorem midPerfAt_cq {cptr : CapRef} {σ σ1 : State Unit} {inv : Fl4Invocation} (hA : MidPerfAt cptr σ inv σ1)
    (hs : CQ σ.curThread σ) (hq : NQ σ.curThread σ) : CQ σ.curThread σ1 ∧ NQ σ.curThread σ1 := by
  obtain ⟨info, σa, a, σb, σc, hia, hb, hc, h1⟩ := hA
  have hIa := fq_I (fv_getMessageInfo (ct := σ.curThread) _) (qv_getMessageInfo' _) ⟨hs, hq⟩ _ hia
  have hIb := fq_I (fve_midF _ _ _) (qve_midF _ _ _) hIa _ hb
  have hIc := fq_I (fve_midE _ _ _ a) (qve_midE _ _ _ a) hIb _ hc
  exact ⟨pq_setThreadState_run _ _ rfl σc _ hIc.1 h1, NQ.of_nV (nv_setThreadState _ _ σc _ h1) hIc.2⟩

section
variable {ct : ObjRef}

theorem utD_rgn {sl : CslotPtr} {σ : State Unit} {rb : ObjRef} {ty : ApiObjectType} {objSz n : Nat} {c : Cap}
    (hc : (c, σ) ∈ (getCap (Z := Unit) sl σ).1) :
    rgn (objRefOf c) (Fl4Spec.bitsOf c) ⊆ utD sl σ true rb ty objSz n :=
  fun _ hx => Or.inl ⟨rfl, c, hc, hx⟩

theorem utD_ptr {sl : CslotPtr} {σ : State Unit} {reset : Bool} {rb : ObjRef} {ty : ApiObjectType}
    {objSz n : Nat} {p : ObjRef} (hp : p ∈ rtPtrs fl4ObjBitsApi rb n objSz ty) :
    p ∈ utD sl σ reset rb ty objSz n := Or.inr hp

theorem asidD_rgn {frame : ObjRef} : rgn frame page_bits ⊆ asidD frame := fun _ hx => Or.inl hx

theorem asidD_ptr {frame p : ObjRef} (hp : p ∈ rtPtrs objBitsApi frame 1 0 (.archObject .asidPoolObj)) :
    p ∈ asidD frame := Or.inr hp

/-- **The Untyped perform from an `I` state** (`I` one of `IQ`/`IB` at the
region). -/
theorem perfU_post {I : State Unit → Prop} (hI : IStable ct I) {don : Bool} {srcSlot : CslotPtr} {reset : Bool}
    {base rb : ObjRef} {ty : ApiObjectType} {objSz : Nat} {slots : List CslotPtr} {dev : Bool} {σ1 : State Unit}
    (hs : I σ1)
    (hD : reset = true → ∀ c, (c, σ1) ∈ (getCap (Z := Unit) srcSlot σ1).1 → ∀ σ', I σ' →
      I (detype (rgn (objRefOf c) (Fl4Spec.bitsOf c)) σ'))
    (hU : ∀ σ' p o, p ∈ rtPtrs fl4ObjBitsApi rb slots.length objSz ty → TPN o → I σ' →
      I { σ' with kheap := Function.update σ'.kheap p (some o) }) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false don
      (.invokeUntyped (.retype srcSlot reset base rb ty objSz slots dev))).run σ1).1, I y.2 := by
  simp only [fl4PerformInvocation]
  refine post_bindE (R := I) (ut_post hI srcSlot reset base rb ty objSz slots dev σ1 hs hD hU) (fun _ h => h) ?_
  intro a s' h y hy
  obtain rfl : y = (.ok [], s') := hy
  exact ut_post hI srcSlot reset base rb ty objSz slots dev σ1 hs hD hU _ h

/-- **The ASID control perform from an `I` state.** -/
theorem perfA_post {I : State Unit → Prop} (hI : IStable ct I) {don : Bool} {frame : ObjRef}
    {slot parent : CslotPtr} {base : Asid} {σ1 : State Unit} (hs : I σ1)
    (hD : ∀ σ', I σ' → I (detype (rgn frame page_bits) σ'))
    (hU : ∀ σ' p o, p ∈ rtPtrs objBitsApi frame 1 0 (.archObject .asidPoolObj) → TPN o → I σ' →
      I { σ' with kheap := Function.update σ'.kheap p (some o) }) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false don
      (.invokeArchObject (.spec (.invokeASIDControl (.makePool frame slot parent base))))).run σ1).1, I y.2 := by
  simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
  exact post_liftE fun x hx =>
    (pw_bind (pw_asidControl hI frame slot parent base hD hU) fun _ => pw_pure _) σ1 x hs hx

end

/-- **`JMidPerfHypQ` from the region fact and the IRQ handler family**
(module docstring). -/
theorem jMidPerfHypQ_of {don : Bool} {cptr : CapRef} {σ : State Unit} (hs : CQ σ.curThread σ)
    (hq : NQ σ.curThread σ) (hR : JPerfRegHyp cptr σ) (hIq : JPerfIrqHypQ don cptr σ) :
    JMidPerfHypQ don cptr σ := by
  intro inv σ1 hA hW y hy
  have h1 := (midPerfAt_cq hA hs hq).1
  have hR1 := hR inv σ1 hA
  cases inv with
  | invokeUntyped i =>
    obtain ⟨srcSlot, reset, base, rb, ty, objSz, slots, dev⟩ := i
    have hr : RegC σ.curThread (utD srcSlot σ1 reset rb ty objSz slots.length) σ1 := hR1
    exact (perfU_post iq_stable ⟨h1, hr.1⟩
      (fun hre c hc σ' h' => by subst hre; exact iq_detype (utD_rgn hc) h')
      (fun σ' p o hp _ h' => iq_upd (utD_ptr hp) h') y hy).1
  | invokeIRQHandler i => exact hIq i σ1 hA hW y hy
  | invokeArchObject i =>
    cases i with
    | spec i =>
      cases i with
      | invokeASIDControl i =>
        obtain ⟨frame, slot, parent, base⟩ := i
        have hr : RegC σ.curThread (asidD frame) σ1 := hR1
        exact (perfA_post iq_stable ⟨h1, hr.1⟩ (fun σ' h' => iq_detype asidD_rgn h')
          (fun σ' p o hp _ h' => iq_upd (asidD_ptr hp) h') y hy).1
      | _ => exact hW.elim
    | _ => exact hW.elim
  | _ => exact hW.elim

/-- **`JMidPerfHypB` from the region fact and the IRQ handler family**
(module docstring; `CQ ∧ NQ` at the dispatch state as for `midRunB_shell`). -/
theorem jMidPerfHypB_of {don : Bool} {cptr : CapRef} {σ : State Unit} (hs : CQ σ.curThread σ)
    (hq : NQ σ.curThread σ) (hR : JPerfRegHyp cptr σ) (hIb : JPerfIrqHypB don cptr σ) :
    JMidPerfHypB don cptr σ := by
  intro inv σ1 hA hW hb y hy
  have h1 := (midPerfAt_cq hA hs hq).1
  have hR1 := hR inv σ1 hA
  cases inv with
  | invokeUntyped i =>
    obtain ⟨srcSlot, reset, base, rb, ty, objSz, slots, dev⟩ := i
    have hr : RegC σ.curThread (utD srcSlot σ1 reset rb ty objSz slots.length) σ1 := hR1
    exact (perfU_post ib_stable ⟨h1, hb, hr⟩
      (fun hre c hc σ' h' => by subst hre; exact ib_detype (utD_rgn hc) h')
      (fun σ' p o hp ho h' => ib_upd (utD_ptr hp) ho h') y hy).2.1
  | invokeIRQHandler i => exact hIb i σ1 hA hW hb y hy
  | invokeArchObject i =>
    cases i with
    | spec i =>
      cases i with
      | invokeASIDControl i =>
        obtain ⟨frame, slot, parent, base⟩ := i
        have hr : RegC σ.curThread (asidD frame) σ1 := hR1
        exact (perfA_post ib_stable ⟨h1, hb, hr⟩ (fun σ' h' => ib_detype asidD_rgn h')
          (fun σ' p o hp ho h' => ib_upd (asidD_ptr hp) ho h') y hy).2.1
      | _ => exact hW.elim
    | _ => exact hW.elim
  | _ => exact hW.elim

end

end Fl4Proofs.P3.MidRun
