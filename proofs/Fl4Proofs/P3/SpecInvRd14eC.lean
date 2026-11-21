/-
P3 (DESIGN.md §9), invariant line G1 (rd14e, KENTRY-PLAN rd14d handoff 2):
**`PerfF` for the Reply and IRQ handler arms** (spec side only; both arms can
come out of the first phase's decode — ReplyRecv's first phase is the Reply).

* `post_st` (after rd12b's post with `calling = false`, ct is Running /
  Inactive / idle if it was in rd14c's good state), **`fpo_tu`** (rd14b's `TU`:
  ct unbound, so `RT` / `CBa` are vacuous), **`perfF_ecq`** (every `ok` outcome
  `EC σ0 ∧ QT ct` ⇒ `PerfF`).
* `qt_setThreadState_ne` / `qt_threadSet_ne` (writes to a thread `≠ t`),
  **`qt_of_tv`** (rd8d's `TV` family — every TCB's state, fault, SC kept —
  carries `QT`: `do_ipc_transfer`, cap writes), the single-step walk
  `qt14e_auto` (rd14c's `qt_auto` steps inlined: a nested `repeat'` makes no
  progress and loops); `qt_replyRemove`, `qt_handleTimeout`;
  **`qt_doReplyTransfer`** (the receiver is not ct, so the only non-good states
  written — the timeout fault's send — land on it); `qt_cancelAllIpc`,
  `qt_cancelAllSignals`, `qt_fastFinalise`, `qt_capDeleteOne`,
  `qt_invokeIrqHandler`.
* **`perfF_reply`**, **`perfF_irqHandler`**, `CovRI`, **`armF_covRI`**,
  **`armF_c14e`** (rd14c's `CovC` and these).
* Bridges in rd8w's shape: **`brR_c14e`** (`BrR (InvRc C14e2)`), **`brF_c14e`**
  (`BrF (InvFc CF14e)`); both need only `A8.EF` at the state.
-/
import Fl4Proofs.P3.SpecInvRd14eB
import Fl4Proofs.P3.SpecInvRd8dT
open Classical

namespace Fl4Proofs.P3.SInvR.A14e
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The post and the end cases -/

theorem post_st {σ0 y : State Unit} (a : List Data) (hq0 : QT σ0.curThread y) :
    ∀ q ∈ (invPost false σ0.curThread a y).1, ∃ x, q.2.kheap σ0.curThread = some (.tcb x) ∧
      (x.tcbState = .running ∨ x.tcbState = .inactive ∨ x.tcbState = .idleThreadState) := by
  intro q hq
  obtain ⟨x0, hx0, g0⟩ := hq0
  obtain ⟨w, hw, hq'⟩ := hq
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  rw [hx0] at hx; cases hx
  dsimp only at hq'
  rcases g0 with e | e | e
  · rw [e] at hq'
    obtain ⟨u1, hu1, hq2⟩ := hq'
    have hS1 := sv_whenReply false _ _ y u1 hu1
    have hS2 := SVK.sv_setThreadState' _ _ u1.2 q hq2
    have e1 := (hS1.trans hS2).1 σ0.curThread
    rw [hx0] at e1
    obtain ⟨x', hx', -⟩ := SVK.sv_tcb (o := q.2.kheap σ0.curThread) (a := x0.tcbSchedContext) e1
    exact ⟨x', hx', Or.inl (SInv.sts_post hq2 x' hx')⟩
  all_goals
    rw [e] at hq'
    dsimp only at hq'
    rw [Set.mem_singleton_iff.1 hq']
    refine ⟨x0, hx0, ?_⟩
    rw [e]
    first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)

/-- **`TU` and ct Running / Inactive / idle give `FPO`** (ct unbound). -/
theorem fpo_tu {σ0 q : State Unit} (h : TU σ0 q) {x : Tcb} (hx : q.kheap σ0.curThread = some (.tcb x))
    (hst : x.tcbState = .running ∨ x.tcbState = .inactive ∨ x.tcbState = .idleThreadState) : FPO q := by
  have et : q.curThread = σ0.curThread := cf_curThread h.1
  have hn := h.2.2.1 x hx
  rw [← et] at hx
  refine fpo_of hx hst ?_ ?_
  · intro x' c' hx' hc'
    rw [hx] at hx'; cases hx'
    rw [hn] at hc'; cases hc'
  · intro x' c' hx' hc'
    rw [hx] at hx'; cases hx'
    rw [hn] at hc'; cases hc'

/-- **An arm with `EC σ0 ∧ QT ct` at every `ok` outcome has `PerfF`.** -/
theorem perfF_ecq {σ0 u : State Unit} {oper : Fl4Invocation} (hB : A10.BS σ0)
    (h : ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false true oper).run u).1, ∀ a, y.1 = .ok a →
      EC σ0 y.2 ∧ QT σ0.curThread y.2) : PerfF σ0 oper u := by
  intro y hy a ha q hq
  obtain ⟨hE, hQ⟩ := h y hy a ha
  obtain ⟨x, hx, hst⟩ := post_st a hQ q hq
  obtain ⟨hc, hw, ⟨hb, hk⟩ | ⟨hn, hr⟩⟩ := hE
  · exact fpo_tb hB (tb_post false a ⟨hc, hw, fun x hx => hb _ x hx rfl, hk⟩ q hq) hx hst
  · exact fpo_tu (tu_post false a ⟨hc, hw, fun x hx => hn _ x hx rfl, hr⟩ q hq) hx hst

/-! ## `QT ct` across the two arms -/

theorem qt_threadSet_ne (t : ObjRef) (f : Tcb → Tcb) (p : ObjRef) (hp : p ≠ t) :
    IK (QT t) (threadSet (Z := Unit) f p) := by
  intro s hs y hy
  obtain ⟨x, -, e⟩ := SInv.mem_threadSet hy
  obtain ⟨x0, h0, g0⟩ := hs
  rw [e]
  refine ⟨x0, ?_, g0⟩
  dsimp only
  rw [Function.update_of_ne (fun h => hp h.symm)]
  exact h0

theorem qt_setThreadState_ne (t p : ObjRef) (st : ThreadState) (hp : p ≠ t) :
    IK (QT t) (setThreadState (Z := Unit) p st) := by
  unfold setThreadState
  refine SInv.ik_bind (qt_threadSet_ne t _ p hp) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction
  repeat' (first | (with_reducible apply SInv.ik_when) | ik_step0)

/-- **A step keeping every TCB's state, fault and SC** (rd8d's `TV`) keeps `QT`. -/
theorem qt_of_tv (t : ObjRef) {α : Type} {m : NonDet (State Unit) α} (h : ∀ V, B8d.TVK V m) : IK (QT t) m := by
  intro s hs y hy
  obtain ⟨x, hx, g⟩ := hs
  have e1 := congrFun (h (B8d.TVv s) s rfl y hy) t
  have e2 : B8c.tcbV (y.2.kheap t) = some (x.tcbState, x.tcbFault, x.tcbSchedContext) := by
    have : B8c.tcbV (s.kheap t) = some (x.tcbState, x.tcbFault, x.tcbSchedContext) := by rw [hx]; rfl
    exact e1.trans this
  obtain ⟨x', hx', ev⟩ := A12b.tcbV_some e2
  refine ⟨x', hx', ?_⟩
  have e3 : x'.tcbState = x.tcbState := congrArg Prod.fst ev
  rw [e3]; exact g

/-- The `QT` walk of the reply / IRQ paths (a `p ≠ t` hypothesis may be in context). -/
macro "qt14e_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_doIpcTransfer _ _ _ _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_getCap _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_setCap _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_capInsert _ _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_lookupIpcBuffer _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_getMessageInfo _)
  | (with_reducible exact qt_cancelIpc _ _)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => fk_testReschedule ..)
  | (with_reducible exact qt_of_nks (nks_ifCondG _ _ _))
  | (with_reducible refine qt_setThreadState_ne _ _ _ ?_; assumption)
  | (with_reducible refine qt_threadSet_ne _ _ _ ?_; assumption)
  | (with_reducible refine qt_setThreadState _ _ _ ?_; first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl))
  | ((with_reducible refine qt_threadSet _ _ _ ?_); intro _ h; exact h)
  | (with_reducible exact qt_setSimpleKo _ _ _ _)
  | (with_reducible refine qt_setObject _ _ _ ?_; intro _ h; cases h; done)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_asUser ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_tcbSchedAction ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_tcbReleaseRemove ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_possibleSwitchTo ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_rescheduleRequired ..)
  | (with_reducible exact qt_of_nks (nks_ifCond _))
  | (with_reducible exact qt_of_nks (nks_schedContextResume _))
  | (with_reducible refine SInv.ik_bind ?_ (fun _ => ?_))
  | (with_reducible apply SInv.ik_when) | (with_reducible apply SInv.ik_ite)
  | (with_reducible refine SInv.ik_maybeM (fun _ => ?_) _)
  | ik_step0 | ik_unfold
  | split))

theorem qt_replyRemove (t c r : ObjRef) : IK (QT t) (replyRemove (Z := Unit) c r) := by
  unfold replyRemove; qt14e_auto

theorem qt_handleTimeout (t tp : ObjRef) (ex : Fault) (hne : tp ≠ t) :
    IK (QT t) (handleTimeout (Z := Unit) tp ex) := by
  unfold handleTimeout sendFaultIpc sendIpc sendIpcBlocked replyPush
  simp only [Bool.false_eq_true, and_false, false_and, NonDet.when, ↓reduceIte]
  qt14e_auto

macro_rules | `(tactic| qt14e_auto) => `(tactic| repeat' (first
  | (with_reducible exact qt_replyRemove _ _ _)
  | (with_reducible refine qt_handleTimeout _ _ _ ?_; assumption)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_doIpcTransfer _ _ _ _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_getCap _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_setCap _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_capInsert _ _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_lookupIpcBuffer _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_getMessageInfo _)
  | (with_reducible exact qt_cancelIpc _ _)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => fk_testReschedule ..)
  | (with_reducible exact qt_of_nks (nks_ifCondG _ _ _))
  | (with_reducible refine qt_setThreadState_ne _ _ _ ?_; assumption)
  | (with_reducible refine qt_threadSet_ne _ _ _ ?_; assumption)
  | (with_reducible refine qt_setThreadState _ _ _ ?_; first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl))
  | ((with_reducible refine qt_threadSet _ _ _ ?_); intro _ h; exact h)
  | (with_reducible exact qt_setSimpleKo _ _ _ _)
  | (with_reducible refine qt_setObject _ _ _ ?_; intro _ h; cases h; done)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_asUser ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_tcbSchedAction ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_tcbReleaseRemove ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_possibleSwitchTo ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_rescheduleRequired ..)
  | (with_reducible exact qt_of_nks (nks_ifCond _))
  | (with_reducible exact qt_of_nks (nks_schedContextResume _))
  | (with_reducible refine SInv.ik_bind ?_ (fun _ => ?_))
  | (with_reducible apply SInv.ik_when) | (with_reducible apply SInv.ik_ite)
  | (with_reducible refine SInv.ik_maybeM (fun _ => ?_) _)
  | ik_step0 | ik_unfold
  | split))

theorem qt_doReplyTransfer (t sender reply : ObjRef) (grant : Bool) (σ : State Unit) (hq : QT t σ)
    (hst : ∀ x, σ.kheap t = some (.tcb x) → ∀ r, x.tcbState ≠ .blockedOnReply r) :
    ∀ y ∈ (doReplyTransfer (Z := Unit) sender reply grant σ).1, QT t y.2 := by
  intro y hy
  unfold doReplyTransfer at hy
  obtain ⟨⟨ro, σ1⟩, h1, hy⟩ := hy
  have e1 : σ1 = σ := cq5_ro (fun _ => by
    show IK _ (NonDet.liftM Reply.replyTcb (getSimpleKo (Z := Unit) KernelObject.reply reply))
    unfold getSimpleKo; repeat' (first | ik_step0 | ik_unfold)) h1
  subst e1
  cases ro with
  | none => rw [Set.mem_singleton_iff.1 hy]; exact hq
  | some receiver =>
    dsimp only [NonDet.maybeM] at hy
    obtain ⟨w, hw, hy⟩ := hy
    unfold getThreadState at hw
    obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hw
    dsimp only at hy
    revert hy
    generalize hxs : x.tcbState = st
    cases st <;> intro hy
    case blockedOnReply r =>
      have hne : receiver ≠ t := by
        intro e; subst e
        exact hst x hx r hxs
      dsimp only at hy
      refine (?_ : IK (QT t) _) σ1 hq y hy
      qt14e_auto
    all_goals (rw [Set.mem_singleton_iff.1 hy]; exact hq)

theorem qt_cancelAllIpc (t e : ObjRef) : IK (QT t) (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc removeAndRestartEpQueuedThread restartThreadIfNoFault; qt14e_auto

theorem qt_cancelAllSignals (t n : ObjRef) : IK (QT t) (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals removeAndRestartNtfnQueuedThread; qt14e_auto

theorem qt_fastFinalise (t : ObjRef) (cap : Cap) (fin : Bool) : IK (QT t) (fastFinalise (Z := Unit) cap fin) := by
  cases cap <;> simp only [fastFinalise]
  case endpointCap r _ _ => exact SInv.ik_when _ (qt_cancelAllIpc t r)
  case notificationCap r _ _ =>
    refine SInv.ik_when _ (SInv.ik_bind ?_ fun _ => SInv.ik_bind ?_ fun _ => qt_cancelAllSignals t r)
    · unfold schedContextMaybeUnbindNtfn; qt14e_auto
    · unfold unbindMaybeNotification; qt14e_auto
  all_goals qt14e_auto

theorem qt_emptySlotNull (t : ObjRef) (sl : CslotPtr) : IK (QT t) (emptySlot (Z := Unit) sl .nullCap) :=
  qt_of_tv t fun _ => by simp only [emptySlot, postCapDeletion]; tv_auto

theorem qt_capDeleteOne (t : ObjRef) (sl : CslotPtr) : IK (QT t) (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne
  refine SInv.ik_bind (qt_of_tv t fun _ => B8d.tv_getCap _) fun _ => SInv.ik_unless _ ?_
  refine SInv.ik_bind (qt_of_tv t fun _ => by unfold isFinalCap; tv_auto) fun _ => ?_
  exact SInv.ik_bind (qt_fastFinalise t _ _) fun _ => qt_emptySlotNull t sl

theorem qt_invokeIrqHandler (t : ObjRef) (i : IrqHandlerInvocation) :
    IK (QT t) (invokeIrqHandler (Z := Unit) i) := by
  cases i
  · exact qt_of_tv t fun _ => by simp only [invokeIrqHandler, archInvokeIrqHandler]; tv_auto
  · simp only [invokeIrqHandler]
    refine SInv.ik_bind (qt_of_tv t fun _ => by unfold getIrqSlot; tv_auto) fun _ => ?_
    exact SInv.ik_bind (qt_capDeleteOne t _) fun _ => qt_of_tv t fun _ => B8d.tv_capInsert _ _ _
  · simp only [invokeIrqHandler]
    exact SInv.ik_bind (qt_of_tv t fun _ => by unfold getIrqSlot; tv_auto) fun _ => qt_capDeleteOne t _

/-! ## The arms -/

theorem perfF_reply {σ0 u : State Unit} (rp : ObjRef) (g : Bool) (h : RF σ0 u) :
    PerfF σ0 (.invokeReply rp g) u := by
  have hst : ∀ x, u.kheap σ0.curThread = some (.tcb x) → ∀ r, x.tcbState ≠ .blockedOnReply r := by
    intro x hx r e; rw [h.rs x hx] at e; cases e
  refine perfF_ecq h.bs fun y hy _ _ => ?_
  have he : fl4PerformInvocation (Z := Unit) false false true (.invokeReply rp g) = NonDetE.liftE (do
      let sender ← NonDet.gets fun s : State Unit => s.curThread
      doReplyTransfer sender rp g
      return []) := rfl
  rw [he] at hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  obtain ⟨w1, hw1, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hw1
  obtain ⟨w2, hw2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  exact ⟨ec_doReplyTransfer rp g (ec_of_tb h.tb) hst w2 hw2,
    qt_doReplyTransfer σ0.curThread _ rp g u h.qt hst w2 hw2⟩

theorem perfF_irqHandler {σ0 u : State Unit} (i : IrqHandlerInvocation) (h : RF σ0 u) :
    PerfF σ0 (.invokeIRQHandler i) u := by
  refine perfF_ecq h.bs fun y hy _ ha => ?_
  change y ∈ ((NonDetE.liftE (invokeIrqHandler (Z := Unit) i) >>= fun _ => NonDetE.returnOk []).run u).1 at hy
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hy
  · obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hz
    rw [SInvU.mem_ret_ok hy]
    exact ⟨ec_invokeIrqHandler i h x hx, qt_invokeIrqHandler σ0.curThread i u h.qt x hx⟩
  · obtain ⟨x, -, rfl⟩ := ft_mem_liftE hz
    cases he

def CovRI (b : Fl4Invocation) : Prop := CovR b ∨ CovI b

theorem armF_covRI : ArmF CovRI := by
  intro σ0 u b hc h
  rcases hc with hc | hc
  · cases b
    case invokeReply rp g => exact perfF_reply rp g h
    all_goals exact (hc : False).elim
  · cases b
    case invokeIRQHandler i => exact perfF_irqHandler i h
    all_goals exact (hc : False).elim

/-- rd14c's `CovC` and this module's arms. -/
def CF14e (b : Fl4Invocation) : Prop := CovC b ∨ CovRI b

theorem armF_c14e : ArmF CF14e := armF_covC.or armF_covRI

/-! ## Bridges in rd8w's `BrR` / `BrF` shape -/

/-- **rd8w's `BrR (InvRc C14e2)`**: `PerfA` asked only outside rd14e's covered
set; needs only `A8.EF` at the state. -/
theorem brR_c14e : ∀ (c : Syscall) (σ : State Unit), A8.EF σ → InvRc C14e2 c σ → InvR c σ :=
  fun _ _ hEF h => invR_ofKB armAKB_c14e2 hEF h

/-- **rd8w's `BrF (InvFc CF14e)`**: `PerfF` asked only outside `CF14e`. -/
theorem brF_c14e : ∀ (c : Syscall) (σ : State Unit), A8.EF σ → InvFc CF14e c σ → InvF c σ :=
  fun _ _ hEF h => invF_ofC armF_c14e hEF h

end

end Fl4Proofs.P3.SInvR.A14e
