/-
P3 (DESIGN.md §9), scheduling contexts: **`Pres` for the spec's
scheduling-context invocations** (ScPres.lean): every outcome of
`invoke_sched_context` keeps the CNodes, the TCBs' caps and
`tcb_mcpriority`, the objects' kinds and SC sizes, the CDT and the domain
schedule (`Pres (false, true)`); Bind, UnbindObject and Consumed also keep the
yield-to links and the call stacks (`Pres (true, true)`).
-/
import Fl4Proofs.P3.ScPres
import Fl4Spec.Schedule
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-- One step of a `Pres` proof. -/
macro "pres_step0" : tactic => `(tactic| first
  | with_reducible exact pres_pure _ | with_reducible exact pres_pure' _ | with_reducible exact pres_fail
  | with_reducible exact pres_gets _ | with_reducible exact pres_get
  | with_reducible exact pres_assert _ | with_reducible exact pres_assertOpt _
  | with_reducible exact pres_getObject _ | with_reducible exact pres_getsThe _
  | with_reducible exact pres_selectF _
  | ((with_reducible apply pres_modify); intro _; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  | ((with_reducible apply pres_get_put); intro _; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  | with_reducible exact pres_doMachineOp _ | with_reducible exact pres_doExtendedOp _
  | with_reducible exact pres_asUser _ _
  | with_reducible exact pres_archThreadSet _ _ | with_reducible exact pres_setObject_ntfn _ _
  | ((with_reducible apply pres_threadSet); intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩)
  | ((with_reducible apply pres_updateSchedContext); intro _ _; exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩)
  | ((with_reducible apply pres_updateSkObjRef); intro _; trivial)
  | ((with_reducible apply pres_updateSkObjRef); intro _ _; exact ⟨rfl, rfl⟩)
  | ((with_reducible apply pres_threadSet); intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Bool.noConfusion⟩)
  | ((with_reducible apply pres_updateSchedContext); intro _ _; exact ⟨rfl, Bool.noConfusion, fun _ => rfl⟩)
  | ((with_reducible apply pres_updateSchedContext); intro _ _; exact ⟨rfl, fun _ => rfl, Bool.noConfusion⟩)
  | ((with_reducible apply pres_updateSkObjRef); intro _; exact Bool.noConfusion)
  | (with_reducible refine pres_zipWithMx (fun _ _ => ?_) _ _)
  | (with_reducible refine pres_bind ?_ (fun _ => ?_))
  | (with_reducible refine pres_bind' ?_ (fun _ => ?_))
  | (with_reducible apply pres_ite) | (with_reducible apply pres_when) | (with_reducible apply pres_unless)
  | (with_reducible refine pres_maybeM (fun _ => ?_) _) | (with_reducible apply pres_liftM)
  | (with_reducible refine pres_whileLoop (fun _ => ?_) _)
  | (with_reducible refine pres_mapMx (fun _ => ?_) _)
  | (with_reducible refine pres_mapM (fun _ => ?_) _)
  | split
  | (dsimp only))


section
variable (f : Bool × Bool)

theorem pres_getSchedContext (p : ObjRef) : Pres f (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext; repeat pres_step0

theorem pres_threadGet {α : Type} (g : Tcb → α) (p : ObjRef) : Pres f (threadGet (Z := Unit) g p) := by
  unfold threadGet; repeat pres_step0

theorem pres_getScObjRef (g : SchedContext → Option ObjRef) (p : ObjRef) :
    Pres f (getScObjRef (Z := Unit) g p) := by
  unfold getScObjRef; exact pres_bind (pres_getSchedContext f p) fun _ => pres_pure _

theorem pres_tcbSchedAction (a : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    Pres f (tcbSchedAction (Z := Unit) a t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue
  refine pres_bind (pres_threadGet f _ _) fun _ => pres_bind (pres_threadGet f _ _) fun _ => ?_
  repeat pres_step0

end

/-- One step of a `Pres` proof, with the lemmas above. -/
macro "pres_step" : tactic => `(tactic| first
  | with_reducible exact pres_threadGet _ _ _ | with_reducible exact pres_getSchedContext _ _
  | with_reducible exact pres_getScObjRef _ _ _ | with_reducible exact pres_tcbSchedAction _ _ _
  | pres_step0)

macro "pres_auto" : tactic => `(tactic| repeat pres_step)

section
variable (f : Bool × Bool)

theorem pres_rescheduleRequired : Pres f (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction getScRefillSufficient getScRefillReady
  pres_auto

theorem pres_tcbReleaseRemove (t : ObjRef) : Pres f (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue; pres_auto

theorem pres_tcbReleaseEnqueue (t : ObjRef) : Pres f (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue readyTimesAppend orderedInsert setReleaseQueue; pres_auto

theorem pres_postpone (p : ObjRef) : Pres f (postpone (Z := Unit) p) := by
  unfold postpone
  refine pres_bind (pres_getScObjRef f _ _) fun _ => pres_bind (pres_assertOpt _) fun _ => ?_
  exact pres_bind (pres_tcbSchedAction f _ _) fun _ => pres_bind (pres_tcbReleaseEnqueue f _) fun _ =>
    pres_modify (fun σ => ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem pres_schedContextResume (p : ObjRef) : Pres f (schedContextResume (Z := Unit) p) := by
  unfold schedContextResume getScRefillReady getScRefillSufficient getTcbQueue
  refine pres_bind (pres_getSchedContext f _) fun _ => pres_bind (pres_assertOpt _) fun _ => ?_
  refine pres_bind (pres_gets _) fun _ => pres_when _ ?_
  refine pres_bind (pres_threadGet f _ _) fun _ => pres_bind (pres_getsThe _) fun _ =>
    pres_bind (pres_getsThe _) fun _ => pres_when _ ?_
  refine pres_bind (pres_threadGet f _ _) fun _ => pres_bind (pres_threadGet f _ _) fun _ => ?_
  exact pres_bind (pres_bind (pres_gets _) fun _ => pres_pure _) fun _ =>
    pres_bind (pres_assert _) fun _ => pres_postpone f _

theorem pres_refillUnblockCheck (p : ObjRef) : Pres f (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck isRoundRobin getScRefillReady refillHeadOverlappingLoop mergeOverlappingRefills
    refillPopHead updateRefillHd getRefillHead
  refine pres_bind (pres_bind (pres_getSchedContext f _) fun _ => pres_pure _) fun _ => ?_
  pres_auto

theorem pres_ifCondRefillUnblockCheck (o : Option ObjRef) (a b : Option Bool) :
    Pres f (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck
  refine pres_maybeM (fun _ => ?_) _
  refine pres_bind (pres_getSchedContext f _) fun _ => pres_bind (pres_gets _) fun _ =>
    pres_bind (pres_pure _) fun _ => pres_when _ (pres_when _ (pres_refillUnblockCheck f _))

theorem pres_schedContextBindTcb (sc t : ObjRef) : Pres f (schedContextBindTcb (Z := Unit) sc t) := by
  unfold schedContextBindTcb
  refine pres_bind ?_ fun _ => pres_bind ?_ fun _ => pres_bind (pres_ifCondRefillUnblockCheck f _ _ _) fun _ =>
    pres_bind (pres_schedContextResume f _) fun _ => pres_bind (pres_gets _) fun _ => pres_when _ ?_
  · pres_auto
  · pres_auto
  · exact pres_bind (pres_tcbSchedAction f _ _) fun _ => pres_rescheduleRequired f

theorem pres_schedContextBindNtfn (sc n : ObjRef) : Pres f (schedContextBindNtfn (Z := Unit) sc n) := by
  unfold schedContextBindNtfn; pres_auto

theorem pres_schedContextUnbindNtfn (sc : ObjRef) : Pres f (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn
  refine pres_bind (pres_getScObjRef f _ _) fun _ => pres_maybeM (fun _ => ?_) _
  pres_auto

theorem pres_schedContextUnbindTcb (sc : ObjRef) : Pres f (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb
  refine pres_bind (pres_getSchedContext f _) fun _ => pres_bind (pres_assertOpt _) fun _ =>
    pres_bind (pres_gets _) fun _ => pres_bind (pres_when _ (pres_rescheduleRequired f)) fun _ =>
    pres_bind (pres_tcbSchedAction f _ _) fun _ => pres_bind (pres_tcbReleaseRemove f _) fun _ => ?_
  pres_auto

theorem pres_schedContextUnbindAllTcbs (sc : ObjRef) : Pres f (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs
  exact pres_bind (pres_getSchedContext f _) fun _ => pres_when _ (pres_schedContextUnbindTcb f _)

theorem pres_schedContextUpdateConsumed (sc : ObjRef) :
    Pres f (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed
  refine pres_bind (pres_getSchedContext f _) fun _ => pres_bind (pres_pure _) fun _ => ?_
  pres_auto

theorem pres_getCap (sl : CslotPtr) : Pres f (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine pres_bind (pres_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> pres_auto

theorem pres_setMrs (t : ObjRef) (buf : Option ObjRef) (msgs : List Message) :
    Pres f (setMrs (Z := Unit) t buf msgs) := by
  unfold setMrs storeWordOffs
  refine pres_getTcb_bind fun x => presAt_pure_bind _ (presAt_pure_bind _ ?_)
  refine presAt_setObject_tcb_bind ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩ fun _ => ?_
  pres_auto

theorem pres_replyFromKernel (t : ObjRef) (x : Data × List Data) :
    Pres f (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel lookupIpcBuffer setMessageInfo
  refine pres_bind (pres_pure _) fun _ => ?_
  split
  refine pres_bind ?_ fun _ => pres_bind (pres_asUser _ _) fun _ =>
    pres_bind (pres_setMrs f _ _ _) fun _ => pres_asUser _ _
  refine pres_bind (pres_threadGet f _ _) fun _ => pres_bind (pres_pure _) fun _ =>
    pres_bind (pres_getCap f _) fun _ => ?_
  pres_auto

theorem pres_setThreadState (t : ObjRef) (ts : ThreadState) : Pres f (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; pres_auto

theorem pres_returnConsumed (sc : ObjRef) : Pres f (returnConsumed (Z := Unit) sc) := by
  unfold returnConsumed
  exact pres_bind (pres_schedContextUpdateConsumed f _) fun _ => pres_pure _

theorem pres_setConsumed (sc t : ObjRef) : Pres f (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed
  exact pres_bind (pres_schedContextUpdateConsumed f _) fun _ => pres_replyFromKernel f _ _

end

/-! The yield-to links and the call stacks change: `Pres (false, true)`. -/

theorem pres_schedContextCancelYieldTo (t : ObjRef) : Pres (false, true) (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo getTcbObjRef
  refine pres_bind (pres_threadGet (false, true) _ _) fun _ => pres_maybeM (fun _ => ?_) _
  pres_auto

theorem pres_completeYieldTo (t : ObjRef) : Pres (false, true) (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo getTcbObjRef
  refine pres_bind (pres_threadGet (false, true) _ _) fun _ => pres_maybeM (fun _ => ?_) _
  exact pres_bind (pres_setConsumed (false, true) _ _) fun _ => pres_schedContextCancelYieldTo _

theorem pres_schedContextYieldTo (sc : ObjRef) : Pres (false, true) (schedContextYieldTo (Z := Unit) sc) := by
  unfold schedContextYieldTo
  refine pres_bind (pres_getScObjRef (false, true) _ _) fun _ => pres_bind ?_ fun _ =>
    pres_bind (pres_schedContextResume (false, true) _) fun _ => pres_bind ?_ fun _ => ?_
  · refine pres_when _ (pres_bind (pres_completeYieldTo _) fun _ =>
      pres_bind (pres_getScObjRef (false, true) _ _) fun _ => pres_assert _)
  · refine pres_bind (pres_getScObjRef (false, true) _ _) fun _ => pres_bind (pres_assertOpt _) fun _ =>
      pres_bind (pres_gets _) fun _ => ?_
    split
    · refine pres_bind (pres_gets _) fun _ => pres_bind (pres_threadGet (false, true) _ _) fun _ =>
        pres_bind (pres_threadGet (false, true) _ _) fun _ => ?_
      split
      · exact pres_bind (pres_tcbSchedAction (false, true) _ _) fun _ => pres_bind (pres_tcbSchedAction (false, true) _ _)
          fun _ => pres_pure _
      · refine pres_bind ?_ fun _ => pres_bind ?_ fun _ => pres_bind (pres_tcbSchedAction (false, true) _ _) fun _ =>
          pres_bind (pres_tcbSchedAction (false, true) _ _) fun _ => pres_bind (pres_tcbSchedAction (false, true) _ _) fun _ =>
          pres_bind (pres_rescheduleRequired (false, true)) fun _ => pres_pure _
        · pres_auto
        · pres_auto
    · exact pres_pure _
  · split
    · exact pres_returnConsumed (false, true) _
    · exact pres_pure _

theorem pres_schedContextUnbindReply (sc : ObjRef) : Pres (true, false) (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply
  refine pres_bind (pres_liftM _ (pres_getSchedContext (true, false) _)) fun _ => pres_unless _ ?_
  pres_auto

/-- **Every SchedContext invocation** keeps `SOK`: Bind, UnbindObject and
Consumed with both flags, Unbind the yield-to links, YieldTo the call stacks. -/
theorem pres_invokeSchedContext (iv : SchedContextInvocation) :
    Pres (decide (∀ p, iv ≠ .invokeSchedContextYieldTo p), decide (∀ p, iv ≠ .invokeSchedContextUnbind p))
      (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext
  split
  · exact pres_returnConsumed _ _
  · split
    · exact pres_bind (pres_schedContextBindTcb _ _ _) fun _ => pres_pure _
    · exact pres_bind (pres_schedContextBindNtfn _ _ _) fun _ => pres_pure _
    · exact pres_fail
  · split
    · exact pres_bind (pres_schedContextUnbindTcb _ _) fun _ => pres_pure _
    · exact pres_bind (pres_schedContextUnbindNtfn _ _) fun _ => pres_pure _
    · exact pres_fail
  · refine (pres_bind (pres_schedContextUnbindAllTcbs (true, false) _) fun _ =>
      pres_bind (pres_schedContextUnbindNtfn (true, false) _) fun _ =>
      pres_bind (pres_schedContextUnbindReply _) fun _ => pres_pure _).weaken (fun _ => rfl) (fun h => ?_)
    simp at h
  · exact (pres_schedContextYieldTo _).weaken (fun h => by simp at h) (fun _ => rfl)

end

end Fl4Proofs.P3.Sched
