/-
P3 (DESIGN.md §9): **the preemption path's charging branch with an endpoint
timeout handler, a reschedule pending or not** (KENTRY-PLAN kp15 (A)/(B)):
`JPreemptRestHypE` [W] split into what is proved, a [J] fact and a narrower
[W] rest.

* `JHole.mcsPPJA`: `mcs_preemption_point` at a hole with `CurInv`, a
  non-idle schedulable `Running`/`Restart` current thread in no ready queue,
  the action `ResumeCurThread` or `ChooseNewThread`, an insufficient head, a
  non-round-robin current SC and an endpoint timeout handler whose endpoint
  is idle or sending: ScChargeTA's `JHole.checkBudgetTA` (the FL4 `true`
  outcome is excluded by the insufficient head, `check_budgetT`); `JAt`
  after.
* (kp16: the [J] premise `JHoleCtNQHyp` kp15 added here is gone; the current
  thread's absence from the ready queues is carried to the hole in `PPR0`,
  XTopJointPreemptQ.)
* `JPreemptRestHypC` [W]: `JPreemptRestHypE` narrowed to the timeout
  handler's endpoint with waiting receivers (`recvEP`), the current thread
  `Running`/`Restart` and unqueued, a non-round-robin SC (kp5 (i): the
  timeout fault's transfer to a receiver for the current thread from a
  `JTH`). Its use at the top: XTopJointPreemptQ.
-/
import Fl4Proofs.P3.ScChargeTA
import Fl4Proofs.P3.XTopJointPreemptE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`mcs_preemption_point` charging the current thread with an endpoint
timeout handler on an idle or sending endpoint, a reschedule pending or
not** (module docstring). -/
theorem JHole.mcsPPJA {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (hsch : Fl4Spec.schedulable σ.curThread σ = true)
    (hnsuf : ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true))
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : xt.tcbTimeoutHandler = .endpointCap p bd r)
    (hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0)
    (hcb : ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ⦄ := by
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec' as ⟨ct, hct'⟩
  step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [hc.cur] at hct'
  subst hct'
  rw [schedulable_eq hR hS hc.curT] at hb
  have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
  subst hb
  rw [← ect, hsch]
  simp only [↓reduceIte]
  refine WP.spec_bind (WP.spec_and (check_budgetT hAT s a σ hS hscC hact hmb)
    (Hh.checkBudgetTA hAT hC hni hres hnq hmrt hmb hkt hrr hth hper hcb)) ?_
  rintro ⟨r, s', a'⟩ ⟨hT, hF⟩
  refine (WP.spec_ok _).2 ?_
  cases r
  · obtain ⟨z, hz, -, V, Ac', Lst', D', J'⟩ := hF rfl
    exact ⟨z.2, fun y hy => mem_pp_sched hsch hz hy, fun hy => fail_pp_sched hsch hz hy,
      Z.mv Z.G V, H, Cs, Ac', Lst', D', J'⟩
  · exact absurd (hT rfl).2.2 hnsuf

variable (arI) in
/-- **The preemption path's charge with the current thread's timeout fault
sent to a waiting receiver** [W] (kp15: `JPreemptRestHypE` with the idle or
sending handler endpoint proved by `JHole.mcsPPJA` for either action, a
queued current thread excluded by `PPR0`'s `CtNQ`, XTopJointPreemptQ). Left: kp5 (i), l4v
`check_budget`'s `charge_budget … True` → `end_timeslice` → `handle_timeout`
→ `send_fault_ipc` → `send_ipc` to a receiver waiting on the handler's
endpoint, for the current thread inside `charge_budget` (a `JTH` state). -/
def JPreemptRestHypC (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ →
    CurInv σ → Fl4Spec.schedulable σ.curThread σ = true →
    ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) →
    (∀ d p, σ.curThread ∉ σ.readyQueues d p) →
    (∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0) →
    ∀ (xt : Fl4Spec.Tcb) (p bd : Fl4Spec.Word) (r : Fl4Spec.CapRights) (q : List Fl4Spec.ObjRef),
      σ.kheap σ.curThread = some (.tcb xt) → (xt.tcbState = .running ∨ xt.tcbState = .restart) →
      xt.tcbTimeoutHandler = .endpointCap p bd r → σ.kheap p = some (.endpoint (.recvEP q)) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

end

end

end Fl4Proofs.P3
