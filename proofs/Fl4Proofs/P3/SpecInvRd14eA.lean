/-
P3 (DESIGN.md §9), invariant line G1 (rd14e, KENTRY-PLAN rd14d handoff 1):
**the Reply arm** (spec side only).

* `ET t c s := s.curThread = t ∧ EB t c s` (rd14b's `EB` with the current
  thread pinned); `et_svcf` (an `SVM ∧ CFK` step keeps it), `et_of`.
* `EBN t` (rd14b's unbound case of `EB`), **`ebn_donate`** (donating any SC to
  `u ≠ t` keeps `t` unbound with no resume), **`et_donate`** (with rd14b's
  `eb_donate` for the bound case).
* **`eb_sendIpcND`** (`send_ipc` without donation, from any thread, keeps
  `EB t c`: no binding is written), **`eb_handleTimeout`** (its only caller
  sends with `can_donate = false`).
* **`et_replyRemove`** (the caller `≠ t`), **`et_doReplyTransfer`** (the
  receiver is `BlockedOnReply`, ct is not: so the receiver is not ct; the reply
  removal may hand cur_sc back from ct to the caller — then ct ends unbound and
  rescheduled), **`cp_doReplyTransfer`** (rd8a's `CP` walk).
* **`perfA_reply`** (`EC σ0` at every outcome ⇒ rd13b's `TBN` or rd14b's `TU`
  via rd14d's `tbu_of_ec`), `CovR`, **`armA_covR`**, **`C14e1 := C14dC ∨
  CovR`**, **`armAKB_c14e1`**.
-/
import Fl4Proofs.P3.SpecInvRd14dD
import Fl4Proofs.P3.SpecInvRd11bA
open Classical

namespace Fl4Proofs.P3.SInvR.A14e
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `EB` with the current thread pinned -/

/-- rd14b's `EB t c` with `t` current. -/
abbrev ET (t c : ObjRef) (s : State Unit) : Prop := s.curThread = t ∧ EB t c s

theorem et_svcf {t c : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m) :
    IK (ET t c) m :=
  fun s hs y hy => ⟨(cf_curThread (h2 s y hy)).trans hs.1, eb_svs hs.2 (h1 s y hy)⟩

theorem et_of {t c : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : IK (EB t c) m) (h2 : CFK m) :
    IK (ET t c) m :=
  fun s hs y hy => ⟨(cf_curThread (h2 s y hy)).trans hs.1, h1 s hs.2 y hy⟩

/-- rd14b's unbound case of `EB`. -/
abbrev EBN (t : ObjRef) (s : State Unit) : Prop := TP (QN t) s ∧ NRes s

theorem ebn_svm {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : SVK.SVM m) : IK (EBN t) m :=
  fun s hs y hy => ebr_svs hs (h s y hy)

/-- **Donating any SC to `u ≠ t`** keeps `t` unbound with no resume. -/
theorem ebn_donate (t p u : ObjRef) (hne : u ≠ t) : IK (EBN t) (schedContextDonate (Z := Unit) p u) := by
  unfold schedContextDonate
  refine ik_bind (ebn_svm (by sv_auto)) fun _ => ik_bind (ik_when _ ?_) fun _ => ?_
  · refine ik_bind (ebn_svm (by sv_auto)) fun f => ik_bind (ebn_svm (by sv_auto)) fun _ => ?_
    refine ik_bind (ebn_svm (by sv_auto)) fun _ => ik_bind ?_ fun _ => ebn_svm (SVK.sv_testReschedule' f)
    exact SInv.ik_and (tp_threadSet _ _ fun _ _ _ => rfl) (by nres_auto)
  · refine ik_bind (SInv.ik_and (by qb_auto) (by nres_auto)) fun _ => ?_
    exact SInv.ik_and (tp_threadSet _ _ fun _ _ e => absurd e hne) (by nres_auto)

/-- **Donating any SC to `u ≠ t`** from `ET t c` ends in `ET t c`. -/
theorem et_donate (t c p u : ObjRef) (hne : u ≠ t) : IK (ET t c) (schedContextDonate (Z := Unit) p u) := by
  intro s hs y hy
  refine ⟨(cf_curThread ((by cfk_auto : CFK (schedContextDonate (Z := Unit) p u)) s y hy)).trans hs.1, ?_⟩
  rcases hs.2 with hb | hn
  · exact eb_donate t c p u s hne hs.1 hb y hy
  · exact Or.inr (ebn_donate t p u hne s hn y hy)

/-! ## `send_ipc` without donation, `handle_timeout` -/

theorem sv_isValidTimeoutHandler (t : ObjRef) : SVK.SVM (isValidTimeoutHandler (Z := Unit) t) := by
  unfold isValidTimeoutHandler; sv_auto

theorem cfk_isValidTimeoutHandler (t : ObjRef) : CFK (isValidTimeoutHandler (Z := Unit) t) := by
  unfold isValidTimeoutHandler; cfk_auto

theorem cp_isValidTimeoutHandler (t : ObjRef) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (isValidTimeoutHandler (Z := Unit) t) :=
  A8.ik_cp (sv_isValidTimeoutHandler t) (cfk_isValidTimeoutHandler t) σ0 c

theorem sv_postpone (p : ObjRef) : SVK.SVM (postpone (Z := Unit) p) := by
  unfold postpone tcbReleaseEnqueue readyTimesAppend
  repeat' (first | (with_reducible exact A11b.sv_orderedInsert _ _ _ _) | sv_leaf | sv_step0)

/-- The `EB` walk of the donation-free IPC paths. -/
macro "eb14e_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact eb_of_svm (A11b.sv_tcbEpAppend _ _ _))
  | (with_reducible exact eb_of_svm (sv_isValidTimeoutHandler _))
  | (with_reducible exact eb_of_svm (SVK.sv_replyUnlinkTcb _ _))
  | (with_reducible exact ik_eb (bl_possibleSwitchTo _ _ _) (qn_possibleSwitchTo _ _) (nres_possibleSwitchTo _))
  | (with_reducible exact ik_eb (bl_ifCond _ _ _) (qn_ifCond _ _) (nres_ifCond _))
  | ik_step0
  | (refine eb_of_svm ?_; sv_auto; done)
  | split))

/-- **`send_ipc` without donation** (from any thread) keeps `EB t c`. -/
theorem eb_sendIpcND (t c : ObjRef) (b k : Bool) (bd : Badge) (g gr : Bool) (thr ep : ObjRef) :
    IK (EB t c) (sendIpc (Z := Unit) b k bd g gr false thr ep) := by
  unfold sendIpc sendIpcBlocked replyPush
  simp only [Bool.false_eq_true, and_false, false_and, NonDet.when, ↓reduceIte]
  eb14e_auto

theorem eb_handleTimeout (t c tp : ObjRef) (ex : Fault) : IK (EB t c) (handleTimeout (Z := Unit) tp ex) := by
  unfold handleTimeout sendFaultIpc
  repeat' (first
    | (with_reducible exact eb_of_svm (sv_isValidTimeoutHandler _))
    | (with_reducible exact eb_sendIpcND _ _ _ _ _ _ _ _ _)
    | ik_step0
    | (refine eb_of_svm ?_; sv_auto; done)
    | split)

/-! ## `reply_remove`, `do_reply_transfer` -/

/-- The `ET` walk of the reply paths (`hne : caller ≠ t` in context). -/
macro "et14e_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact et_svcf (SVK.sv_replyUnlinkTcb _ _) (cfk_replyUnlinkTcb' _ _))
  | (with_reducible exact et_of (ik_eb (bl_possibleSwitchTo _ _ _) (qn_possibleSwitchTo _ _)
      (nres_possibleSwitchTo _)) (by cfk_auto))
  | (with_reducible exact et_of (ik_eb (bl_ifCond _ _ _) (qn_ifCond _ _) (nres_ifCond _)) (by cfk_auto))
  | (with_reducible exact et_of (eb_handleTimeout _ _ _ _) (cfk_handleTimeout' _ _))
  | (with_reducible refine et_donate _ _ _ _ ?_; assumption)
  | ik_step0
  | (refine et_svcf ?_ ?_ <;> first | (sv_auto; done) | (cfk_auto; done))
  | split))

/-- **`reply_remove caller r`** (`caller ≠ t`) keeps `ET t c`. -/
theorem et_replyRemove (t c caller r : ObjRef) (hne : caller ≠ t) :
    IK (ET t c) (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove
  et14e_auto

macro_rules | `(tactic| et14e_auto) => `(tactic| repeat' (first
  | (with_reducible exact et_svcf (sv_postpone _) (cfk_postpone' _))
  | (with_reducible refine et_replyRemove _ _ _ _ ?_; assumption)
  | (with_reducible exact et_svcf (SVK.sv_replyUnlinkTcb _ _) (cfk_replyUnlinkTcb' _ _))
  | (with_reducible exact et_of (ik_eb (bl_possibleSwitchTo _ _ _) (qn_possibleSwitchTo _ _)
      (nres_possibleSwitchTo _)) (by cfk_auto))
  | (with_reducible exact et_of (ik_eb (bl_ifCond _ _ _) (qn_ifCond _ _) (nres_ifCond _)) (by cfk_auto))
  | (with_reducible exact et_of (eb_handleTimeout _ _ _ _) (cfk_handleTimeout' _ _))
  | (with_reducible refine et_donate _ _ _ _ ?_; assumption)
  | ik_step0
  | (refine et_svcf ?_ ?_ <;> first | (sv_auto; done) | (cfk_auto; done))
  | split))

/-- **`do_reply_transfer`** from `ET t c` with `t` not `BlockedOnReply`. -/
theorem et_doReplyTransfer (t c sender reply : ObjRef) (grant : Bool) (σ : State Unit) (hσ : ET t c σ)
    (hst : ∀ x, σ.kheap t = some (.tcb x) → ∀ r, x.tcbState ≠ .blockedOnReply r) :
    ∀ y ∈ (doReplyTransfer (Z := Unit) sender reply grant σ).1, ET t c y.2 := by
  intro y hy
  unfold doReplyTransfer at hy
  obtain ⟨⟨ro, σ1⟩, h1, hy⟩ := hy
  have e1 : σ1 = σ := cq5_ro (fun _ => by
    show IK _ (NonDet.liftM Reply.replyTcb (getSimpleKo (Z := Unit) KernelObject.reply reply))
    unfold getSimpleKo; repeat' (first | ik_step0 | ik_unfold)) h1
  subst e1
  cases ro with
  | none => rw [Set.mem_singleton_iff.1 hy]; exact hσ
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
      refine (?_ : IK (ET t c) _) σ1 hσ y hy
      et14e_auto
    all_goals (rw [Set.mem_singleton_iff.1 hy]; exact hσ)

theorem cp_doReplyTransfer (s r : ObjRef) (g : Bool) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (doReplyTransfer (Z := Unit) s r g) := by
  unfold doReplyTransfer replyRemove handleTimeout
  repeat' (first
    | (with_reducible exact A11b.cp_replyUnlinkTcb _ _ _ _)
    | (with_reducible exact cp_isValidTimeoutHandler _ _ _)
    | (with_reducible exact A8.cp_schedContextDonate _ _ _ _)
    | (with_reducible exact A8.cp_possibleSwitchTo _ _ _)
    | (with_reducible exact A8.cp_postpone _ _ _)
    | (with_reducible exact A8.cp_ifCondTest _ _ _ _)
    | (with_reducible exact A11b.cp_sendFaultIpc _ _ _ _ _ _)
    | ik_step0
    | cp_leaf
    | split)

/-- **`do_reply_transfer` of ct from `EC σ0`** (ct not `BlockedOnReply`). -/
theorem ec_doReplyTransfer {σ0 s : State Unit} (reply : ObjRef) (grant : Bool) (h : EC σ0 s)
    (hst : ∀ x, s.kheap σ0.curThread = some (.tcb x) → ∀ r, x.tcbState ≠ .blockedOnReply r) :
    ∀ y ∈ (doReplyTransfer (Z := Unit) s.curThread reply grant s).1, EC σ0 y.2 := by
  intro y hy
  have et : s.curThread = σ0.curThread := cf_curThread h.1
  obtain ⟨-, hw⟩ := cp_doReplyTransfer s.curThread reply grant σ0 σ0.curSc s ⟨cf_curSc h.1, h.2.1⟩ y hy
  exact ⟨(cfk_doReplyTransfer' _ _ _ s y hy).trans h.1, hw,
    (et_doReplyTransfer σ0.curThread σ0.curSc s.curThread reply grant s ⟨et, h.2.2⟩ hst y hy).2⟩

/-! ## The arm -/

theorem perfA_reply {σ0 s : State Unit} (bl call don : Bool) (rp : ObjRef) (g : Bool) (h : RF σ0 s) :
    PerfA σ0 bl call don (.invokeReply rp g) s := by
  refine perfA_tbn3 h.bs h.suff fun y hy => ?_
  have he : fl4PerformInvocation (Z := Unit) bl call don (.invokeReply rp g) = NonDetE.liftE (do
      let sender ← NonDet.gets fun s : State Unit => s.curThread
      doReplyTransfer sender rp g
      return []) := rfl
  rw [he] at hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  obtain ⟨w1, hw1, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hw1
  obtain ⟨w2, hw2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  have hst : ∀ x, s.kheap σ0.curThread = some (.tcb x) → ∀ r, x.tcbState ≠ .blockedOnReply r := by
    intro x hx r e; rw [h.rs x hx] at e; cases e
  exact ⟨fun _ _ => tbu_of_ec (ec_doReplyTransfer rp g (ec_of_tb h.tb) hst w2 hw2), fun e he => by cases he⟩

def CovR : Fl4Invocation → Prop
  | .invokeReply _ _ => True
  | _ => False

theorem armA_covR : ArmA CovR := by
  intro σ0 u bl cl dn b hc h
  cases b
  case invokeReply rp g => exact perfA_reply bl cl dn rp g h
  all_goals exact (hc : False).elim

/-- rd14d's arms and the Reply arm. -/
def C14e1 (b : Fl4Invocation) : Prop := C14dC b ∨ CovR b

theorem armAKB_c14e1 : ArmAKB C14e1 := armAKB_c14dC.or (armAKB_of (armAK_of armA_covR))

end

end Fl4Proofs.P3.SInvR.A14e
