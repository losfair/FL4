/-
P3 (DESIGN.md §9), invariant line G1 (rd14b, KENTRY-PLAN rd13b handoff 1):
**the Notification perform arm** (spec side only) through SpecInvRd13bB's
`perfA_tbn`, on SpecInvRd14bA's `BL` transfers.

* `cp_sendSignalU`: rd8a's `cw_sendSignal` without `Rdy` (the cancel of the
  bound receive-blocked receiver is `SVM` by rd11a's `sv_cancelIpc`).
* `tp_svs`, `bl_svs`, `bl_of_svm` (the SVM callees: cancel_ipc,
  set_thread_state, as_user, the notification-queue dequeue), **`bl_sendSignal`**.
* **`perfA_notification`**: from the Restart state with `KP σ0`, ct bound to
  σ0's cur_sc and cur_sc an SC there, every outcome has `TB` (the arm has no
  error outcome), so `PerfA`.
-/
import Fl4Proofs.P3.SpecInvRd14bA
import Fl4Proofs.P3.SpecInvRd8eA
open Classical

namespace Fl4Proofs.P3.SInvR.A14b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `CP` across `send_signal` without `Rdy` -/

/-- **`send_signal` keeps `CP`** (rd8a's `cw_sendSignal` without `Rdy`). -/
theorem cp_sendSignalU (n : ObjRef) (b : Badge) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (sendSignal (Z := Unit) n b) := by
  intro s hs y hy
  unfold sendSignal at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, e⟩ := SInv.mem_getSimpleKo hz
  obtain ⟨nt, z2⟩ := z
  simp only at hk e; subst z2
  dsimp only at hy
  cases h1 : nt.ntfnObj with
  | idleNtfn =>
    cases h2 : nt.ntfnBoundTcb with
    | none =>
      rw [h1, h2] at hy
      exact A8.cp_setNotification n _ σ0 c s hs y hy
    | some tcb =>
      rw [h1, h2] at hy
      obtain ⟨w, hw, hy⟩ := hy
      unfold getThreadState at hw
      obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hw
      dsimp only at hy
      split at hy
      · obtain ⟨c1, hc1, hy⟩ := hy
        have h1' : A8.CP σ0 c c1.2 :=
          A8.ik_cp (B8e.sv_cancelIpc' tcb) (cfk_cancelIpc' tcb) σ0 c s hs c1 hc1
        exact A8.cp_wake tcb n b σ0 c c1.2 h1' y hy
      · exact A8.cp_setNotification n _ σ0 c s hs y hy
  | waitingNtfn queue =>
    rw [h1] at hy
    exact A8.cp_updateWaitingNtfn n queue b σ0 c s hs y hy
  | activeNtfn badge' =>
    rw [h1] at hy
    exact A8.cp_setNotification n _ σ0 c s hs y hy

/-! ## Across `send_signal` -/


theorem tp_svs {Q : ObjRef → Tcb → Prop} {s s' : State Unit}
    (hQ : ∀ p x y, y.tcbSchedContext = x.tcbSchedContext → Q p y → Q p x) (hS : SVK.SVS s s')
    (hq : TP Q s) : TP Q s' := by
  intro p x hx
  have e := hS.1 p
  rw [hx] at e
  obtain ⟨y, hy, hys⟩ := SVK.sv_tcb (o := s.kheap p) (a := x.tcbSchedContext) e.symm
  exact hQ p x y hys (hq p y hy)

theorem bl_svs {t c : ObjRef} {s s' : State Unit} (h : BL t c s) (hS : SVK.SVS s s') : BL t c s' := by
  refine ⟨tp_svs (fun p x y e h' => by intro he; rw [← e]; exact h' he) hS h.1, ?_⟩
  obtain ⟨y, n, hy⟩ := h.2
  have e := hS.1 c
  rw [hy] at e
  obtain ⟨y', hy', -⟩ := SVK.sv_sc (o := s'.kheap c) e
  exact ⟨y', n, hy'⟩

theorem bl_of_svm {t c : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : SVK.SVM m) : IK (BL t c) m :=
  fun s hs y hy => bl_svs hs (h s y hy)

/-- The walk keeping `BL` over `send_signal`'s callees. -/
macro "bl_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact bl_maybeDonateSc _ _ _ _)
  | (with_reducible exact bl_possibleSwitchTo _ _ _)
  | (with_reducible exact bl_ifCond _ _ _)
  | (with_reducible exact bl_of_svm (B8e.sv_cancelIpc' _))
  | (with_reducible exact bl_of_svm (SVK.sv_setThreadState' _ _))
  | (with_reducible exact bl_of_svm (SVK.sv_asUser' _ _))
  | (with_reducible exact bl_of_svm (sv_tcbNtfnDequeue _ _))
  | (with_reducible refine ik_bind ?_ (fun _ => ?_))
  | (with_reducible apply ik_when) | (with_reducible apply ik_ite)
  | (refine bl_of_svm ?_; sv_auto; done)
  | ik_step0))

/-- **`send_signal`** keeps `t` bound to `c` and `c` an SC. -/
theorem bl_sendSignal (t c n : ObjRef) (b : Badge) : IK (BL t c) (sendSignal (Z := Unit) n b) := by
  unfold sendSignal updateWaitingNtfn; bl_auto

/-! ## The arm -/

/-- **The Notification arm.** -/
theorem perfA_notification {σ0 s : State Unit} (ep : ObjRef) (bd : Badge) {bl call don : Bool}
    (hB : A10.BS σ0) (hS : Suff σ0) (hK : A11.KP σ0 s)
    (hbd : ∀ x, s.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = some σ0.curSc)
    (hsc : ∃ y n, s.kheap σ0.curSc = some (.schedContext y n)) :
    PerfA σ0 bl call don (.invokeNotification ep bd) s := by
  refine perfA_tbn hB hS fun y hy => ?_
  have hy' : y ∈ ((withoutPreemption (sendSignal (Z := Unit) ep bd) >>= fun _ =>
      (NonDetE.returnOk [] : PMonad Unit (List Data))).run s).1 := hy
  obtain ⟨z, hz, ⟨u0, -, hy2⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy'
  · unfold withoutPreemption at hz
    obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    have ey : y = (.ok [], w.2) := Set.mem_singleton_iff.1 hy2
    subst ey
    have hbl := bl_sendSignal σ0.curThread σ0.curSc ep bd s
      ⟨fun p x' hx' e => by subst e; exact hbd x' hx', hsc⟩ w hw
    refine ⟨fun _ _ => Or.inl ⟨(cfk_sendSignal' ep bd s w hw).trans hK.1,
      (cp_sendSignalU ep bd σ0 σ0.curSc s ⟨A11.kp_curSc hK, hK.2.1⟩ w hw).2,
      fun x hx => hbl.1 σ0.curThread x hx rfl, hbl.2⟩, fun _ h => by cases h⟩
  · unfold withoutPreemption at hz
    obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

end

end Fl4Proofs.P3.SInvR.A14b
