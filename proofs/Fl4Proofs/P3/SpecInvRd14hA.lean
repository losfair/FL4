/-
P3 (DESIGN.md §9), invariant line G1 (rd14h, rd14g handoff (1)): **`PerfF` for
the deletion arms** (CNode delete / revoke, ThreadControlCaps,
ThreadControlSched; spec side only).

* The end facts are rd14f's walk invariant `DW σ0` (rd14f E's `HJ` triple at
  the `ok` outcomes of `cap_delete` / `cap_revoke` / the installs; rd14f G's
  `HK` for ThreadControlSched's error-free tail): ct σ0's, and rd14g C's
  `rtc_dw` gives `RT ct ∧ CBa ct` (ct bound to cur_sc with σ0's refills and
  `OffReady`, or unbound).
* `QT ct` (a TCB in a Restart / Running / Inactive state) by the generated
  family SpecInvRd14hQ*: the cone writes only those states, deletes no TCB
  (finalisation only) and keeps every object's type.
* **`perfF_cnodeDelete`**, **`perfF_cnodeRevoke`**, **`perfF_tcCaps`**,
  **`perfF_tcSched`** (the bind target is not ct: sb2's `BindOK` finds it
  unbound, ct is bound), `armFV_covDR`, `armFV_covTC`.
-/
import Fl4Proofs.P3.SpecInvRd14hQ2
open Classical

namespace Fl4Proofs.P3.SInvR.A14h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14e Fl4Proofs.P3.SInvR.A14f Fl4Proofs.P3.SInvR.A14g

noncomputable section

set_option maxHeartbeats 1000000

/-- **An arm whose `ok` outcomes have `DW σ0` and `QT ct` has `PerfF`.** -/
theorem perfF_dw {σ0 u : State Unit} {oper : Fl4Invocation} (hB : A10.BS σ0)
    (hd : ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false true oper).run u).1, ∀ a, y.1 = .ok a → DW σ0 y.2)
    (hq : QTKE σ0.curThread (fl4PerformInvocation (Z := Unit) false false true oper)) (hu : QT σ0.curThread u) :
    PerfF σ0 oper u := by
  refine perfF_q fun y hy a ha => ?_
  have h := hd y hy a ha
  exact ⟨h.ct, hq u hu y hy, rtc_dw hB h⟩

/-- `PerfF` from rd14f E's triple. -/
theorem perfF_hj {σ0 u : State Unit} {I : ObjRef} {oper : Fl4Invocation} (hB : A10.BS σ0) (hJ : JS σ0 I u)
    (hm : HJ σ0 I (fl4PerformInvocation (Z := Unit) false false true oper))
    (hq : QTKE σ0.curThread (fl4PerformInvocation (Z := Unit) false false true oper)) (hu : QT σ0.curThread u) :
    PerfF σ0 oper u :=
  perfF_dw hB (fun y hy _ _ => (hm hB.ni u hJ y hy).1.2.2) hq hu

/-! ## CNode delete / revoke -/

theorem perfF_cnodeDelete {σ0 u : State Unit} {I : ObjRef} (sl : CslotPtr) (hR : RF σ0 u)
    (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u) :
    PerfF σ0 (.invokeCNode (.deleteCall sl)) u := by
  refine perfF_hj hR.bs (js_rf hR hnis hRB) ?_ ?_ hR.qt
  · show HJ σ0 I (invokeCnode (Z := Unit) (.deleteCall sl) >>= fun _ => NonDetE.returnOk [])
    exact hj_bind (hj_capDelete sl) fun _ => hj_ret _
  · show QTKE _ (invokeCnode (Z := Unit) (.deleteCall sl) >>= fun _ => NonDetE.returnOk [])
    exact ike_bind (qth_capDelete sl) fun _ => ike_returnOk _

theorem perfF_cnodeRevoke {σ0 u : State Unit} {I : ObjRef} (sl : CslotPtr) (hR : RF σ0 u)
    (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u) :
    PerfF σ0 (.invokeCNode (.revokeCall sl)) u := by
  refine perfF_hj hR.bs (js_rf hR hnis hRB) ?_ ?_ hR.qt
  · show HJ σ0 I (invokeCnode (Z := Unit) (.revokeCall sl) >>= fun _ => NonDetE.returnOk [])
    exact hj_bind (hj_capRevoke sl) fun _ => hj_ret _
  · show QTKE _ (invokeCnode (Z := Unit) (.revokeCall sl) >>= fun _ => NonDetE.returnOk [])
    exact ike_bind (qth_capRevoke sl) fun _ => ike_returnOk _

/-! ## ThreadControlCaps / ThreadControlSched -/

theorem perfF_tcCaps {σ0 u : State Unit} {I : ObjRef} (t : ObjRef) (sl : CslotPtr)
    (fh th cr vr : Option (Cap × CslotPtr)) (buf : Option (VSpaceRef × Option (Cap × CslotPtr))) (hR : RF σ0 u)
    (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u) :
    PerfF σ0 (.invokeTCB (.threadControlCaps t sl fh th cr vr buf)) u := by
  refine perfF_hj hR.bs (js_rf hR hnis hRB) ?_ ?_ hR.qt
  · show HJ σ0 I (invokeTcb (Z := Unit) (.threadControlCaps t sl fh th cr vr buf))
    simp only [invokeTcb]
    exact hj_bind (hj_installTcbCap _ _ _ _) fun _ => hj_bind (hj_installTcbCap _ _ _ _) fun _ =>
      hj_bind (hj_installTcbCap _ _ _ _) fun _ => hj_bind (hj_installTcbCap _ _ _ _) fun _ =>
        hj_bind (hj_installTcbFrameCap _ _ _) fun _ => hj_ret _
  · show QTKE _ (invokeTcb (Z := Unit) (.threadControlCaps t sl fh th cr vr buf))
    simp only [invokeTcb]
    exact ike_bind (qth_installTcbCap _ _ _ _) fun _ => ike_bind (qth_installTcbCap _ _ _ _) fun _ =>
      ike_bind (qth_installTcbCap _ _ _ _) fun _ => ike_bind (qth_installTcbCap _ _ _ _) fun _ =>
        ike_bind (qth_installTcbFrameCap _ _ _) fun _ => ike_returnOk _

/-- rd14f G's `HK` walk of ThreadControlSched (the bind's target is not ct). -/
theorem hk_tcSched {σ0 : State Unit} {I : ObjRef} (t : ObjRef) (sl : CslotPtr)
    (fh : Option (Cap × CslotPtr)) (mcp prio : Option (Word8 × ObjRef)) (sc : Option (Option ObjRef))
    (hb : ∀ p, sc = some (some p) → t ≠ σ0.curThread) :
    HK σ0 I (invokeTcb (Z := Unit) (.threadControlSched t sl fh mcp prio sc)) := by
  simp only [invokeTcb]
  refine hk_bind (hj_installTcbCap _ _ _ _) (fun _ => ?_) (fun _ => ?_)
  · refine ike_bind (ike_liftE (ik_maybeM (fun x => ?_) _)) fun _ => ?_
    · rcases x with ⟨m1, _⟩
      show IK (DWS σ0) (setMcpriority (Z := Unit) t m1)
      unfold setMcpriority
      exact dws_svcf (by sv_auto) (by cfk_auto)
    refine ike_bind (ike_liftE (ik_maybeM (fun x => ?_) _)) fun _ => ?_
    · rcases x with ⟨p1, _⟩
      exact (dst_svcf (sv14f_setPriority _ _) (cfk14f_setPriority _ _)).dws
    refine ike_bind (ike_liftE ?_) fun _ => ike_returnOk _
    rcases sc with _ | _ | p
    · exact ik_pure _
    · exact (dst_bind (dst_svcf (by sv_auto) (by cfk_auto)) fun o =>
        dst_bind (dst_svcf (by sv_auto) (by cfk_auto)) fun q => dst_unbindTcb q).dws
    · exact dws_bindTcb p t (hb p rfl)
  · exact noErr_bind (noErr_liftE _) fun _ => noErr_bind (noErr_liftE _) fun _ =>
      noErr_bind (noErr_liftE _) fun _ => noErr_returnOk _

theorem perfF_tcSched {σ0 u : State Unit} {I : ObjRef} (t : ObjRef) (sl : CslotPtr)
    (fh : Option (Cap × CslotPtr)) (mcp prio : Option (Word8 × ObjRef)) (sc : Option (Option ObjRef))
    (hR : RF σ0 u) (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u)
    (hb : ∀ p, sc = some (some p) → t ≠ σ0.curThread) :
    PerfF σ0 (.invokeTCB (.threadControlSched t sl fh mcp prio sc)) u := by
  have hk : HK σ0 I (fl4PerformInvocation (Z := Unit) false false true
      (.invokeTCB (.threadControlSched t sl fh mcp prio sc))) := hk_tcSched t sl fh mcp prio sc hb
  refine perfF_dw hR.bs (fun y hy a ha => ((hk hR.bs.ni u (js_rf hR hnis hRB) y hy).1 a ha).1) ?_ hR.qt
  show QTKE _ (invokeTcb (Z := Unit) (.threadControlSched t sl fh mcp prio sc))
  simp only [invokeTcb]
  qth_auto

/-! ## The arms at the interface -/

theorem armFV_covDR : ArmFV CovDR := by
  intro σ0 s u h0 b I hc hB hS hi hN hz hbo hbr hRB hF hL hG hu
  have hR : RF σ0 u.2 := rf_restart hB hS hz hu
  have et : s.curThread = σ0.curThread := kz_curThread hz
  have hRB' : B8f.RB σ0.curThread I u.2 := by
    rw [← et]; exact B8j.rb_restart s hRB hu
  cases b
  case invokeCNode i =>
    cases i
    case deleteCall sl => exact perfF_cnodeDelete sl hR hi hRB'
    case revokeCall sl => exact perfF_cnodeRevoke sl hR hi hRB'
    all_goals exact (hc : False).elim
  all_goals exact (hc : False).elim

theorem armFV_covTC : ArmFV CovTC := by
  intro σ0 s u h0 b I hc hB hS hi hN hz hbo hbr hRB hF hL hG hu
  have hR : RF σ0 u.2 := rf_restart hB hS hz hu
  have et : s.curThread = σ0.curThread := kz_curThread hz
  have hRB' : B8f.RB σ0.curThread I u.2 := by
    rw [← et]; exact B8j.rb_restart s hRB hu
  cases b
  case invokeTCB i =>
    cases i
    case threadControlCaps t sl fh th cr vr buf => exact perfF_tcCaps t sl fh th cr vr buf hR hi hRB'
    case threadControlSched t sl fh mcp prio sc =>
      refine perfF_tcSched t sl fh mcp prio sc hR hi hRB' fun p e => ?_
      subst e
      have hun := unb_of_bindOK hbo.2 hbr hu
      intro et'
      obtain ⟨x, hx⟩ := hR.ct
      rw [← et'] at hx
      have h1 := hun x hx
      have h2 := hR.bd x (by rw [et'] at hx; exact hx)
      rw [h1] at h2; cases h2
    all_goals exact (hc : False).elim
  all_goals exact (hc : False).elim

end

end Fl4Proofs.P3.SInvR.A14h
