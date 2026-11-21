/-
P3 (DESIGN.md §9), IPC (KENTRY-PLAN.md sch9 (1)): **the spec's signal wakes
with `CurInvR`** (XTopJointJAtZR): `wake_specBR` (IpcSignalBoundSpec's
`wake_specB`), `wake_tailDR`/`wake_specGR` (IpcSignalDonSpec's `wake_tailD`/
`wake_specG`), copies with `cur` weakened to `CurInvR` in and out. A wake
never sets `resumeCurThread` (the action is kept, set to `chooseNewThread`, or
set to a switch from `resumeCurThread`), so `CurInv` is needed after only
where it was given before, through the same frame (`DWFr.curInv`).
-/
import Fl4Proofs.P3.IpcSignalBoundSpec
import Fl4Proofs.P3.IpcSignalDonSpec
import Fl4Proofs.P3.XTopJointJAtZR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

set_option maxHeartbeats 4000000 in
/-- **The scheduler invariants after the wake of an inactive bound thread**
(module docstring; `wake_spec`'s proof in `CFr`). -/
theorem wake_specBR {σ1 σ' : State Unit} {r t : ObjRef} {x : Tcb} {badge : Word}
    (hI : Inv σ1) (hB : BlockedScActive σ1) (hAI : ActIdle σ1)
    (hcur : CurInvR σ1) (hrun : CurRunM σ1)
    (hkt : σ1.kheap t = some (.tcb x)) (hxs : x.tcbState = .inactive)
    (hrib : RelIfBound σ1 t)
    (hsa : ∀ p y k, x.tcbSchedContext = some p → σ1.kheap p = some (.schedContext y k) → scActive y = true)
    (hND : maybeDonateSc (Z := Unit) t r (wakeSt3 σ1 t x badge) = ({((), wakeSt3 σ1 t x badge)}, False))
    (hm : ((), σ') ∈ (specWake t r badge σ1).1) :
    Inv σ' ∧ BlockedScActive σ' ∧ CFr r t σ1 σ' ∧ ActIdle σ' ∧
      CurInvR σ' ∧ CurRunM σ' := by
  set x1 : Tcb := { x with tcbState := .running } with hx1
  set x3 : Tcb := setReg x1 badge_register badge with hx3
  set σA := updK σ1 t (.tcb x1) with hσA
  set σ2 := Notif.stsAct σA t with hσ2
  set σ3 := wakeSt3 σ1 t x badge with hσ3
  have hk2 : σ2.kheap t = some (.tcb x1) := by rw [hσ2, stsAct_kheap]; simp [hσA, updK]
  have hkp2 : ∀ p, p ≠ t → σ2.kheap p = σ1.kheap p := fun p hp => by
    rw [hσ2, stsAct_kheap]; simp only [hσA, updK, Function.update_of_ne hp]
  have hk3 : σ3.kheap t = some (.tcb x3) := by
    show (updK σ2 t (.tcb x3)).kheap t = _; simp [updK]
  have hkp3 : ∀ p, p ≠ t → σ3.kheap p = σ1.kheap p := fun p hp => by
    show (updK σ2 t (.tcb x3)).kheap p = _
    simp only [updK, Function.update_of_ne hp]; exact hkp2 p hp
  have hI3 : Inv σ3 := wake_inv3B hI hkt hxs hrib badge
  -- `t`, not runnable, is in no release queue
  have htrel : t ∉ σ1.releaseQueue := fun hm' => by
    obtain ⟨x', -, -, -, h1, -, h3, -⟩ := hI.rel t hm'
    rw [hkt] at h1; cases h1; rw [hxs] at h3; cases h3
  have hsp : specWake t r badge σ1 = specWakeTail t r σ3 := by
    unfold specWake
    rw [nd_bind_one (Notif.setThreadState_eq _ hkt), nd_bind_one (Notif.asUser_setRegister_eq _ _ hk2)]
    rfl
  rw [hsp] at hm
  unfold specWakeTail at hm
  rw [nd_bind_one hND, nd_gets_bind] at hm
  have hS3 : Sk σ1 σ3 :=
    (show Sk σ1 σA from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).trans
      ((Sk.stsAct σA t).trans (show Sk σ2 σ3 from ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))
  have F3 : CFr r t σ1 σ3 := by
    refine ⟨hS3, fun p => ?_⟩
    by_cases e : p = t
    · subst e
      exact Or.inr ⟨.tcb x, .tcb x3, hkt, hk3, Or.inl ⟨x, .running, x.tcbBoundNotification, x.tcbFault, x3.tcbArch,
        rfl, rfl, Or.inr ⟨Or.inl rfl, rfl, Or.inr hxs, Or.inr (Or.inl rfl)⟩⟩⟩
    · exact Or.inl (hkp3 p e)
  have ha2 : σ2.schedulerAction = σA.schedulerAction ∨ σ2.schedulerAction = .chooseNewThread :=
    (stsAct_heap σA t).2.2.2
  have ha3 : σ3.schedulerAction = σ1.schedulerAction ∨ σ3.schedulerAction = .chooseNewThread := ha2
  obtain ⟨σ4, h4, F4, hI4, ha4, hk4e⟩ : ∃ σ4,
      (NonDet.when (schedulable t σ3 = true) (possibleSwitchTo (Z := Unit) t)) σ3 = ({((), σ4)}, False) ∧
      NFr false r σ3 σ4 ∧ Inv σ4 ∧
      (σ4.schedulerAction = σ3.schedulerAction ∨ σ4.schedulerAction = .chooseNewThread ∨
        (σ3.schedulerAction = .resumeCurThread ∧ σ4.schedulerAction = .switchThread t ∧
          schedulable t σ3 = true)) ∧ σ4.kheap = σ3.kheap := by
    by_cases hs : schedulable t σ3 = true
    · obtain ⟨σ4, he4, hq4⟩ := pst_q hk3 hI3.actReady
      have hQ := possibleSwitchTo_qchange hI3 hs he4
      refine ⟨σ4, by unfold NonDet.when; rw [if_pos hs]; exact he4, hq4.nfr, hI3.qchange hQ, ?_, hQ.1⟩
      rcases pst_act hk3 hI3.actReady he4 with e | e | ⟨e1, e2⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr ⟨e1, e2, hs⟩)
    · exact ⟨σ3, by unfold NonDet.when; rw [if_neg hs]; rfl, NFr.refl _ _ _, hI3, Or.inl rfl, rfl⟩
  rw [nd_bind_one h4] at hm
  have hu : ((), σ') ∈ (specUnblock t σ4).1 := hm
  have hk4 : σ4.kheap t = some (.tcb x3) := by rw [hk4e]; exact hk3
  have hsa4 : ∀ p y k, x3.tcbSchedContext = some p → σ4.kheap p = some (.schedContext y k) →
      scActive y = true := by
    intro p y k hp hky
    have hpt : p ≠ t := by rintro rfl; rw [hk4] at hky; cases hky
    rw [hk4e, hkp3 p hpt] at hky
    exact hsa p y k hp hky
  obtain ⟨F5, ha5⟩ := unblock_frame hI4 hk4 hsa4 hu r
  have FF : CFr r t σ1 σ' := F3.trans (CFr.ofNFr (F4.trans F5))
  have hrel4 : σ4.releaseQueue = σ1.releaseQueue := (hS3.trans F4.sk).rel
  have hI' : Inv σ' := hI4.unblockTail hk4 (fun p y k _ _ hm' => absurd (hrel4 ▸ hm') htrel)
    (fun p y k hp hky _ => hsa4 p y k hp hky) hu
  have hact : σ'.schedulerAction = σ1.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread ∨
      (σ1.schedulerAction = .resumeCurThread ∧ σ'.schedulerAction = .switchThread t ∧
        schedulable t σ3 = true) := by
    rw [ha5]
    rcases ha4 with e | e | ⟨e1, e2, e3⟩
    · rw [e]; exact ha3.imp_right Or.inl
    · exact Or.inr (Or.inl e)
    · rcases ha3 with e' | e'
      · exact Or.inr (Or.inr ⟨by rw [← e']; exact e1, e2, e3⟩)
      · rw [e'] at e1; cases e1
  have hcn : σ1.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread := by
    intro e
    rcases hact with e' | e' | ⟨e1, -, -⟩
    · rw [e', e]
    · exact e'
    · rw [e] at e1; cases e1
  refine ⟨hI', FF.bsa hB, FF, ⟨fun u hu' => ?_, FF.idleOK hAI.2⟩, ?_, ?_⟩
  · rcases hact with e | e | ⟨-, e2, e3⟩
    · exact FF.sched (hAI.1 u (by rw [← e]; exact hu'))
    · rw [e] at hu'; cases hu'
    · rw [e2] at hu'; cases hu'
      exact (F4.trans F5).sched e3
  · intro e
    refine FF.curInv (hcur ?_)
    rcases hact with e' | e' | ⟨e1, -, -⟩
    · rw [← e']; exact e
    · rw [e'] at e; cases e
    · exact e1
  · refine hrun.of_act FF.curRunW fun e => ?_
    rcases hact with e' | e' | ⟨e1, -, -⟩
    · rw [e']; exact e
    · exact act_cn_nr e'
    · exact absurd e1 e


set_option maxHeartbeats 8000000 in
/-- **The wake's tail with or without a donation** (module docstring). -/
theorem wake_tailDR {σ3 σd σ' : State Unit} {r t : ObjRef} {x3 : Tcb} {xn : Notification}
    (hI3 : Inv σ3) (hB3 : BlockedScActive σ3) (hAI3 : ActIdle σ3)
    (hcur3 : CurInvR σ3) (hrun3 : CurRunM σ3)
    (hk3 : σ3.kheap t = some (.tcb x3)) (hxr : x3.tcbState = .running)
    (hkn3 : σ3.kheap r = some (.notification xn)) (hnq3 : NotQueued σ3 t)
    (hoff3 : OffOK σ3)
    (hsp3 : ∀ c y k, σ3.kheap c = some (.schedContext y k) → y.scSporadic = true → scActive y = true)
    (hD : maybeDonateSc (Z := Unit) t r σ3 = ({((), σd)}, False))
    (hm : ((), σ') ∈ (specWakeTail t r σ3).1) :
    Inv σ' ∧ BlockedScActive σ' ∧ DWFr r t σ3 σ' ∧ ActIdle σ' ∧
      CurInvR σ' ∧ CurRunM σ' := by
  unfold specWakeTail at hm
  rw [nd_bind_one hD, nd_gets_bind] at hm
  have hrun3' : runnable x3.tcbState = true := by rw [hxr]; rfl
  have hnipc : ∀ x, σ3.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = false := fun x hx => by
    rw [hk3] at hx; cases hx; rw [hxr]; rfl
  -- the donation
  obtain ⟨Fd, had, -, -, Bd⟩ := donate_dfr (r := r) hI3 hk3 hkn3 hnq3 hoff3 hB3 hnipc hD
  obtain ⟨Id, hrq⟩ := Inv.donate hI3 hk3 hkn3 hrun3' hnq3 hD
  have AId : ActIdle σd := ActIdle.donate hAI3 hI3 hk3 hkn3 hnq3 hD
  obtain ⟨xd, hkd⟩ : ∃ xd, σd.kheap t = some (.tcb xd) := by
    obtain ⟨st, bn, fl, ar, sc, hkd, -⟩ := Fd.tcbF hk3
    exact ⟨_, hkd⟩
  -- the schedulability test and the switch
  obtain ⟨σ4, h4, F4, hI4, ha4, hk4e, ht4, hr4⟩ : ∃ σ4,
      (NonDet.when (schedulable t σd = true) (possibleSwitchTo (Z := Unit) t)) σd = ({((), σ4)}, False) ∧
      NFr false r σd σ4 ∧ Inv σ4 ∧
      (σ4.schedulerAction = σd.schedulerAction ∨ σ4.schedulerAction = .chooseNewThread ∨
        (σd.schedulerAction = .resumeCurThread ∧ σ4.schedulerAction = .switchThread t ∧
          schedulable t σd = true)) ∧ σ4.kheap = σd.kheap ∧ σ4.curTime = σd.curTime ∧
      σ4.releaseQueue = σd.releaseQueue := by
    by_cases hs : schedulable t σd = true
    · obtain ⟨σ4, he4, hq4⟩ := pst_q hkd Id.actReady
      have hQ := possibleSwitchTo_qchange Id hs he4
      have hn4 := hq4.nfr (r := r)
      obtain ⟨rq, act, e4⟩ := hq4
      refine ⟨σ4, by unfold NonDet.when; rw [if_pos hs]; exact he4, hn4, Id.qchange hQ, ?_, hQ.1,
        by rw [e4], by rw [e4]⟩
      rcases pst_act hkd Id.actReady he4 with e | e | ⟨e1, e2⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr ⟨e1, e2, hs⟩)
    · exact ⟨σd, by unfold NonDet.when; rw [if_neg hs]; rfl, NFr.refl _ _ _, Id, Or.inl rfl, rfl, rfl, rfl⟩
  rw [nd_bind_one h4] at hm
  have hu : ((), σ') ∈ (specUnblock t σ4).1 := hm
  have hk4 : σ4.kheap t = some (.tcb xd) := by rw [hk4e]; exact hkd
  have hsa4 : ∀ p y k, xd.tcbSchedContext = some p → σ4.kheap p = some (.schedContext y k) →
      y.scSporadic = true → scActive y = true := by
    intro p y k _ hky hs
    rw [hk4e] at hky
    obtain ⟨y0, rf, nt, tc, hy0, rfl, -⟩ := Fd.scB hky
    exact hsp3 p y0 k hy0 hs
  obtain ⟨F5, ha5⟩ := unblock_frameS hI4 hk4 hsa4 hu r
  have FF : DWFr r t σ3 σ' := Fd.trans (DWFr.ofNFr (F4.trans F5))
  have hI' : Inv σ' := hI4.unblockTail hk4
    (fun p y n hp hky hm' => by
      rw [ht4]; exact hrq xd p y n hkd hp (by rw [← hk4e]; exact hky) (by rw [← hr4]; exact hm'))
    hsa4 hu
  -- the action
  have hact : σ'.schedulerAction = σ3.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread ∨
      (σ3.schedulerAction = .resumeCurThread ∧ σ'.schedulerAction = .switchThread t ∧
        schedulable t σd = true) := by
    rw [ha5, ← had]
    rcases ha4 with e | e | ⟨e1, e2, e3⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr ⟨e1, e2, e3⟩)
  have hcn : σ3.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread := by
    intro e
    rcases hact with e' | e' | ⟨e1, -, -⟩
    · rw [e', e]
    · exact e'
    · rw [e] at e1; cases e1
  refine ⟨hI', (F4.trans F5).bsa Bd, FF, ⟨fun u hu' => ?_, FF.idleOK hAI3.2⟩, ?_, ?_⟩
  · rcases hact with e | e | ⟨-, e2, e3⟩
    · exact FF.sched (hAI3.1 u (by rw [← e]; exact hu'))
    · rw [e] at hu'; cases hu'
    · rw [e2] at hu'; cases hu'
      exact (F4.trans F5).sched e3
  · intro e
    refine FF.curInv (hcur3 ?_)
    rcases hact with e' | e' | ⟨e1, -, -⟩
    · rw [← e']; exact e
    · rw [e'] at e; cases e
    · exact e1
  · refine hrun3.of_act FF.curRunW fun e => ?_
    rcases hact with e' | e' | ⟨e1, -, -⟩
    · rw [e']; exact e
    · exact act_cn_nr e'
    · exact absurd e1 e


set_option maxHeartbeats 8000000 in
/-- **The scheduler invariants after a wake with or without a donation**
(module docstring). -/
theorem wake_specGR {σ1 σd σ' : State Unit} {r t : ObjRef} {x : Tcb} {xn : Notification} {badge : Word}
    (hI : Inv σ1) (hI3 : Inv (wakeSt3 σ1 t x badge)) (hB : BlockedScActive σ1) (hAI : ActIdle σ1)
    (hcur : CurInvR σ1) (hrun : CurRunM σ1)
    (hkt : σ1.kheap t = some (.tcb x)) (hxr : runnable x.tcbState = false)
    (F3 : CFr r t σ1 (wakeSt3 σ1 t x badge)) (hkn : σ1.kheap r = some (.notification xn))
    (hoff : OffOK σ1)
    (hsp : ∀ c y k, σ1.kheap c = some (.schedContext y k) → y.scSporadic = true → scActive y = true)
    (hD : maybeDonateSc (Z := Unit) t r (wakeSt3 σ1 t x badge) = ({((), σd)}, False))
    (hm : ((), σ') ∈ (specWake t r badge σ1).1) :
    Inv σ' ∧ BlockedScActive σ' ∧ DWFr r t σ1 σ' ∧ ActIdle σ' ∧
      CurInvR σ' ∧ CurRunM σ' := by
  set x1 : Tcb := { x with tcbState := .running } with hx1
  set x3 : Tcb := setReg x1 badge_register badge with hx3
  set σA := updK σ1 t (.tcb x1) with hσA
  set σ2 := Notif.stsAct σA t with hσ2
  set σ3 := wakeSt3 σ1 t x badge with hσ3
  have hk2 : σ2.kheap t = some (.tcb x1) := by rw [hσ2, stsAct_kheap]; simp [hσA, updK]
  have hkp2 : ∀ p, p ≠ t → σ2.kheap p = σ1.kheap p := fun p hp => by
    rw [hσ2, stsAct_kheap]; simp only [hσA, updK, Function.update_of_ne hp]
  have hk3 : σ3.kheap t = some (.tcb x3) := by
    show (updK σ2 t (.tcb x3)).kheap t = _; simp [updK]
  have hkp3 : ∀ p, p ≠ t → σ3.kheap p = σ1.kheap p := fun p hp => by
    show (updK σ2 t (.tcb x3)).kheap p = _
    simp only [updK, Function.update_of_ne hp]; exact hkp2 p hp
  have htn : t ≠ r := by rintro rfl; rw [hkt] at hkn; cases hkn
  have hkn3 : σ3.kheap r = some (.notification xn) := by rw [hkp3 r (Ne.symm htn)]; exact hkn
  have hq3 : σ3.readyQueues = σ1.readyQueues := by
    show (Notif.stsAct σA t).readyQueues = _; unfold Notif.stsAct; split <;> rfl
  have hr3 : σ3.releaseQueue = σ1.releaseQueue := F3.sk.rel
  have hnq1 := hI.notQueued hkt hxr
  have hnq3 : NotQueued σ3 t := ⟨fun d p => by rw [hq3]; exact hnq1.1 d p, by rw [hr3]; exact hnq1.2⟩
  have hsp3 : ∀ c y k, σ3.kheap c = some (.schedContext y k) → y.scSporadic = true → scActive y = true := by
    intro c y k hc
    have hct : c ≠ t := by rintro rfl; rw [hk3] at hc; cases hc
    rw [hkp3 c hct] at hc; exact hsp c y k hc
  have hoff3 : OffOK σ3 := F3.off hoff
  have ha3 : σ3.schedulerAction = σ1.schedulerAction ∨ σ3.schedulerAction = .chooseNewThread :=
    (stsAct_heap σA t).2.2.2
  have hcn3 : σ1.schedulerAction = .chooseNewThread → σ3.schedulerAction = .chooseNewThread := fun e => by
    rcases ha3 with e' | e'
    · rw [e', e]
    · exact e'
  have hAI3 : ActIdle σ3 := by
    refine ⟨fun u hu => ?_, F3.idleOK hAI.2⟩
    rcases ha3 with e | e
    · exact F3.sched (hAI.1 u (by rw [← e]; exact hu))
    · rw [e] at hu; cases hu
  have hsw : specWake t r badge σ1 = specWakeTail t r σ3 := by
    unfold specWake
    rw [nd_bind_one (Notif.setThreadState_eq _ hkt), nd_bind_one (Notif.asUser_setRegister_eq _ _ hk2)]
    rfl
  rw [hsw] at hm
  obtain ⟨I', B', F', AI', cur', run'⟩ := wake_tailDR (x3 := x3) hI3 (F3.bsa hB) hAI3 (fun e => F3.curInv (hcur (ha3.elim (fun e' => by rw [← e']; exact e) (fun e' => by rw [e'] at e; cases e))))
    (hrun.of_act F3.curRunW fun e => by
      rcases ha3 with e' | e'
      · rw [e']; exact e
      · exact act_cn_nr e') hk3 rfl hkn3 hnq3 hoff3 hsp3 hD hm
  exact ⟨I', B', (DWFr.ofCFr F3).trans F', AI', cur', run'⟩


end Spec

end

end Fl4Proofs.P3.Sched
