/-
P3 (DESIGN.md §9), invariant line G1 (rd8h, rd8f handoff 3):
**`rd_fl4PerformInvocation`: every perform arm keeps `Rdy`** (spec side
only, outside the JAtZ cone).

* `rd_invokeCnode` (rd8f's `RB`: revoke / delete by `rb_capRevoke` /
  `rb_capDelete`, cancel_badged_sends by `rq_cancelBadgedSends` with `NQ []`
  from `fh_of`, the moves / swaps / inserts by rd's leaves),
  `rd_invokeIrqHandler` (`rb_capDeleteOne`, `rd_capInsert`), `rd_archPerf`
  (every arch arm but ASIDControl by rd's leaves), the domain
  schedule set-start / configure arms by rd's leaves, DomainSet by Rd8hD.
* `PerfOK σ iv`: the per-arm facts at the perform — ThreadControl* (Rd8hC's
  `TcbOK`), SchedContext (rd8b's `ScIvOK`), SchedControl (rd8c's `CfgD`),
  Reply (`Sched.BlockedScActive`, rd8e's `rd_doReplyTransfer` input: rd8i's
  `kentry_bsa` / `kcall_bsa`), and two arms taken as `Rdy`-at-the-outcomes
  hypotheses: Untyped and ASIDControl (retype / detype / MakePool, goal item
  3); DomainSet takes rd's `SR t` at the perform (l4v `valid_blocked`, Rd8hD).
* **`rd_fl4PerformInvocation`**: `Rdy` at every outcome of
  `fl4PerformInvocation` from rd8f's `RB ct I`, the current thread `RdyT`,
  `OffReady`, `Suff`, nq2's `NtfnQB` and `PerfOK`.
-/
import Fl4Proofs.P3.SpecInvRd8hD
import Fl4Proofs.P3.SpecInvRd8eC
import Fl4Proofs.P3.SpecInvRd8cB
open Classical

namespace Fl4Proofs.P3.SInvR.B8h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8

noncomputable section

set_option maxHeartbeats 1000000

variable {C I : ObjRef}

/-- `m` then `returnOk b`. -/
theorem rd_seqRet {ε α β : Type} {m : NonDetE (State Unit) ε α} {b : β} {σ : State Unit}
    (hm : ∀ y ∈ (m.run σ).1, Rdy y.2) :
    ∀ y ∈ ((m >>= fun _ => (NonDetE.returnOk b : NonDetE (State Unit) ε β)).run σ).1, Rdy y.2 := by
  intro y hy
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  · rw [SInvU.mem_ret_ok hy]; exact hm z hz
  · exact hm z hz

theorem rd_lift {ε α : Type} {m : NonDet (State Unit) α} {σ : State Unit} (hm : ∀ y ∈ (m σ).1, Rdy y.2) :
    ∀ y ∈ ((NonDetE.liftE (ε := ε) m).run σ).1, Rdy y.2 := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
  exact hm x hx

/-- **`invoke_cnode`** from `RB`. -/
theorem rd_invokeCnode (i : CnodeInvocation) (σ : State Unit) (h : B8f.RB C I σ) :
    ∀ y ∈ ((invokeCnode (Z := Unit) i).run σ).1, Rdy y.2 := by
  cases i with
  | revokeCall sl => exact fun y hy => (B8f.rb_capRevoke sl σ h y hy).1
  | deleteCall sl => exact fun y hy => (B8f.rb_capDelete sl σ h y hy).1
  | insertCall c a b => exact rd_lift (rd_capInsert c a b σ h.1)
  | moveCall c a b => exact rd_lift (rd_capMove c a b σ h.1)
  | rotateCall c1 c2 s1 s2 s3 =>
    refine rd_lift ((?_ : IK Rdy _) σ h.1)
    repeat' (first | (with_reducible exact rd_capSwap _ _ _ _) | (with_reducible exact rd_capMove _ _ _) | ik_step0)
  | cancelBadgedSendsCall c =>
    cases c
    case endpointCap ep b r =>
      intro y hy
      simp only [invokeCnode] at hy
      exact (rd_lift (fun z hz => ((ik_when _ (B8f.rq_cancelBadgedSends ep b)) σ ⟨h.1, (B8f.fh_of h).2.1⟩ z hz).1)) y hy
    all_goals (intro y hy; simp only [invokeCnode] at hy; obtain ⟨x, hx, -⟩ := SInvU.mem_liftE' hy; exact hx.elim)

/-- **`invoke_irq_handler`** from `RB`. -/
theorem rd_invokeIrqHandler (i : IrqHandlerInvocation) (σ : State Unit) (h : B8f.RB C I σ) :
    ∀ y ∈ (invokeIrqHandler (Z := Unit) i σ).1, Rdy y.2 := by
  intro y hy
  cases i with
  | aCKIrq irq => exact rd_archInvokeIrqHandler _ σ h.1 y hy
  | setIRQHandler irq cap slot =>
    simp only [invokeIrqHandler] at hy
    obtain ⟨z1, h1, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 h1
    obtain ⟨z2, h2, hy⟩ := hy
    have b2 := B8f.rb_capDeleteOne _ σ h z2 h2
    exact rd_capInsert _ _ _ z2.2 b2.1 y hy
  | clearIRQHandler irq =>
    simp only [invokeIrqHandler] at hy
    obtain ⟨z1, h1, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 h1
    exact (B8f.rb_capDeleteOne _ σ h y hy).1

macro "rda_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact rd_performPageTableInvocation _) | (with_reducible exact rd_performPageDirectoryInvocation _)
  | (with_reducible exact rd_performPdptInvocation _) | (with_reducible exact rd_performPageInvocation _)
  | (with_reducible exact rd_performAsidPoolInvocation _) | (with_reducible exact rd_performIoPortInvocation _)
  | (with_reducible exact rd_performIoportControlInvocation _) | (with_reducible exact rd_performPml4Flush _)
  | (with_reducible exact rd_performDeriveSubframe _) | (with_reducible exact rd_performTestAndClearAccessed _)
  | (with_reducible exact rd_rescheduleRequired) | (with_reducible exact rd_domainScheduleConfigure _ _ _)
  | ik_step0 | ik_unfold))

/-- The arch arm's fact: ASIDControl (MakePool: delete_objects and a
retype) is goal item 3's; every other arch perform needs none. -/
def ArchOK (σ : State Unit) : Fl4ArchInvocation → Prop
  | .spec (.invokeASIDControl o) =>
    ∀ y ∈ ((fl4ArchPerformInvocation (Z := Unit) (.spec (.invokeASIDControl o))).run σ).1, Rdy y.2
  | _ => True

theorem rd_archPerf (i : Fl4ArchInvocation) (σ : State Unit) (hR : Rdy σ) (hOK : ArchOK σ i) :
    ∀ y ∈ ((fl4ArchPerformInvocation (Z := Unit) i).run σ).1, Rdy y.2 := by
  intro y hy
  cases i with
  | spec j =>
    cases j
    case invokeASIDControl o => exact hOK y hy
    all_goals
      simp only [fl4ArchPerformInvocation, archPerformInvocation] at hy
      exact (show IKE Rdy _ from ike_liftE (by rda_auto)) σ hR y hy
  | pml4Flush j =>
    simp only [fl4ArchPerformInvocation] at hy
    exact (show IKE Rdy _ from ike_liftE (by rda_auto)) σ hR y hy
  | deriveSubframe j =>
    simp only [fl4ArchPerformInvocation] at hy
    exact (show IKE Rdy _ from ike_liftE (by rda_auto)) σ hR y hy
  | testAndClearAccessed sl =>
    simp only [fl4ArchPerformInvocation] at hy
    exact (show IKE Rdy _ from ike_liftE (by rda_auto)) σ hR y hy

/-- The per-arm facts of a perform (module docstring). -/
def PerfOK (σ : State Unit) : Fl4Invocation → Prop
  | .invokeUntyped i => ∀ y ∈ ((fl4InvokeUntyped (Z := Unit) i).run σ).1, Rdy y.2
  | .invokeTCB i => TcbOK σ i
  | .invokeDomain (.invokeDomainSet t _) => SR t σ
  | .invokeReply _ _ => Sched.BlockedScActive σ
  | .invokeSchedContext i => ScIvOK σ i
  | .invokeSchedControl i => CfgD (.invokeSchedControl i)
  | .invokeArchObject i => ArchOK σ i
  | _ => True

/-- **Every perform arm keeps `Rdy`** (module docstring). -/
theorem rd_fl4PerformInvocation (bl call don : Bool) (iv : Fl4Invocation) (I : ObjRef) (σ : State Unit)
    (hRB : B8f.RB σ.curThread I σ) (hRT : RdyT σ σ.curThread) (hO : Sched.OffReady σ) (hS : Suff σ)
    (hN : SInv.NtfnQB σ) (hOK : PerfOK σ iv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don iv).run σ).1, Rdy y.2 := by
  have hR : Rdy σ := hRB.1
  have h1 : T1 σ := hRB.2.2.1
  have hI : SInvB.ScInv σ := hRB.2.2.2.1
  have hA : Simple σ := (B8f.fh_of hRB).2.2.2.1
  cases iv with
  | invokeUntyped i => simp only [fl4PerformInvocation]; exact rd_seqRet hOK
  | invokeEndpoint ep badge cg cgr =>
    intro y hy
    simp only [fl4PerformInvocation, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
    obtain ⟨w, hw, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hw
    obtain ⟨w2, hw2, hx⟩ := hx
    have r2 := B8d.rd_sendIpc_d bl call badge cg cgr don σ.curThread ep σ hRT h1 hA hI.fwd hR w2 hw2
    rw [Set.mem_singleton_iff.1 hx]; exact r2
  | invokeNotification ep badge =>
    simp only [fl4PerformInvocation, withoutPreemption]
    exact rd_seqRet (rd_lift (rd_sendSignal ep badge σ hR hN))
  | invokeTCB i => exact rd_invokeTcbP bl call don i I σ hRB hRT hOK
  | invokeFl4TCB i => simp only [fl4PerformInvocation]; exact rd_invokeFl4Tcb i σ hR
  | invokeDomain d =>
    simp only [fl4PerformInvocation]
    refine rd_lift fun x hx => ?_
    obtain ⟨z, hz, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
    cases d with
    | invokeDomainSet t dd => exact rd_invokeSetDomain t dd σ hR hOK z hz
    | invokeDomainScheduleSetStart k =>
      simp only [invokeDomain] at hz
      exact (show IK Rdy _ by rda_auto) σ hR z hz
    | invokeDomainScheduleConfigure k dd du =>
      simp only [invokeDomain] at hz
      exact rd_domainScheduleConfigure k dd du σ hR z hz
  | invokeReply reply grant =>
    simp only [fl4PerformInvocation]
    refine rd_lift fun x hx => ?_
    obtain ⟨w, hw, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hw
    obtain ⟨w2, hw2, hx⟩ := hx
    have r2 := B8e.rd_doReplyTransfer _ reply grant σ hR h1 hA hI hOK hw2
    rw [Set.mem_singleton_iff.1 hx]; exact r2
  | invokeCNode i => simp only [fl4PerformInvocation]; exact rd_seqRet (rd_invokeCnode i σ hRB)
  | invokeIRQControl i => simp only [fl4PerformInvocation]; exact rd_seqRet (rd_invokeFl4IrqControl i σ hR)
  | invokeIRQHandler i =>
    simp only [fl4PerformInvocation]; exact rd_seqRet (rd_lift (rd_invokeIrqHandler i σ hRB))
  | invokeSchedContext i =>
    simp only [fl4PerformInvocation, withoutPreemption]
    exact rd_lift (rd_invokeSchedContext i σ h1 hA hI.fwd hRT hOK hR)
  | invokeSchedControl i =>
    cases i with
    | invokeSchedControlConfigureFlags p b per mr badge flag =>
      simp only [fl4PerformInvocation]
      exact rd_seqRet (rd_lift (rd_configure_d p b per mr badge flag σ hO hS hI.sym hI.2 h1 hA hOK hR))
  | invokeArchObject i => simp only [fl4PerformInvocation]; exact rd_archPerf i σ hR hOK

end

end Fl4Proofs.P3.SInvR.B8h
