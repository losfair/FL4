/-
P3 (DESIGN.md §9), invariant line G1 (rd14f, KENTRY-PLAN rd14e-3): **TCB
ThreadControlCaps / ThreadControlSched** (spec side only).

* `hj_installTcbCap`, `hj_installTcbFrameCap`: rd14f E's triple across the
  slot deletion and the checked inserts (`RB` at the `ok` outcomes by rd8h's
  `ro_installTcbCap` / `ro_installTcbFrameCap`, `CKC` by ctq14's
  `ckc_install*`, `DWS` across the inserts: `SVM ∧ CFK`).
* `HK σ0 I m` (every `ok` outcome `DWS σ0`, every error outcome rd14f E's `J`),
  `hk_of_hj`, `hk_bind` (a triple followed by an error-free `DWS` tail),
  **`perfA_hk`**.
* ThreadControlSched's tail: `setMcpriority`, `setPriority` (`SVM ∧ CFK`), the
  unbind of the target's SC (rd14d's `ec_schedContextUnbindTcb`, rd14f D's
  `QN` walk), the bind of a new SC `p` to the target (`ec_bindTcb`: the decode
  found the target unbound and `p` without a TCB — sb2's `BindOK` — while ct
  is bound to cur_sc and cur_sc's TCB is ct, so target ≠ ct and `p` ≠ cur_sc).
* **`perfA_tcCaps`**, **`perfA_tcSched`**, `CovTC`, **`armAKD_covTC`**,
  `C14f2 := C14f1 ∨ CovTC`, **`armAKD_c14f2`**.
-/
import Fl4Proofs.P3.SpecInvRd14fF
open Classical

namespace Fl4Proofs.P3.SInvR.A14f
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d

noncomputable section

set_option maxHeartbeats 1000000

variable {σ0 : State Unit} {I : ObjRef}

/-! ## The installs -/

theorem sv14f_ins (c : Cap) (src : CslotPtr) (t : ObjRef) (sl dest : CslotPtr) :
    SVK.SVM (checkCapAt (Z := Unit) c src (checkCapAt (.threadCap t) sl (capInsert c src dest))) := by
  unfold checkCapAt; sv_auto
  all_goals exact SVK.sv_capInsert _ _ _

theorem cfk14f_ins (c : Cap) (src : CslotPtr) (t : ObjRef) (sl dest : CslotPtr) :
    CFK (checkCapAt (Z := Unit) c src (checkCapAt (.threadCap t) sl (capInsert c src dest))) := by
  unfold checkCapAt; cfk_auto
  all_goals exact cfk_capInsert _ _ _

/-- **`install_tcb_cap`** keeps rd14f E's triple. -/
theorem hj_installTcbCap (t : ObjRef) (sl : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    HJ σ0 I (installTcbCap (Z := Unit) t sl n o) := by
  intro hni s hs y hy
  have hR := B8h.ro_installTcbCap (C := σ0.curThread) (I := I) t sl n o s hs.1.1 y hy
  have hC := R16.ckc_installTcbCap σ0.curThread t sl n o s hs.1.2.1 y hy
  rcases o with _ | ⟨c, src⟩
  · rw [SInvU.mem_ret_ok hy]; exact ⟨hs.1, fun _ _ => hs.2⟩
  · simp only [installTcbCap] at hy
    obtain ⟨z, hz, ⟨a, ha, hy'⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hz' := hj_capDelete (σ0 := σ0) (I := I) _ hni s hs z hz
      have h0 : DWS σ0 z.2 := ⟨hz'.1.2.2, hz'.2 a ha⟩
      have key : DWS σ0 y.2 ∧ ∃ b, y.1 = .ok b := by
        unfold NonDetE.unlessE at hy'
        split at hy'
        · rw [SInvU.mem_ret_ok hy']; exact ⟨h0, _, rfl⟩
        · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy'
          exact ⟨(dst_svcf (sv14f_ins _ _ _ _ _) (cfk14f_ins _ _ _ _ _)).dws z.2 h0 x hx, _, rfl⟩
      obtain ⟨hD, b, hb⟩ := key
      exact ⟨⟨hR.2 b hb, hC, hD.1⟩, fun _ _ => hD.2⟩
    · exact ⟨(hj_capDelete (σ0 := σ0) (I := I) _ hni s hs z hz).1, fun _ h => by simp at h⟩

/-- **`install_tcb_frame_cap`** keeps rd14f E's triple. -/
theorem hj_installTcbFrameCap (t : ObjRef) (sl : CslotPtr) (buf : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    HJ σ0 I (installTcbFrameCap (Z := Unit) t sl buf) := by
  intro hni s hs y hy
  have hR := B8h.ro_installTcbFrameCap (C := σ0.curThread) (I := I) t sl buf s hs.1.1 y hy
  have hC := R16.ckc_installTcbFrameCap σ0.curThread t sl buf s hs.1.2.1 y hy
  rcases buf with _ | ⟨ptr, frame⟩
  · rw [SInvU.mem_ret_ok hy]; exact ⟨hs.1, fun _ _ => hs.2⟩
  · simp only [installTcbFrameCap] at hy
    obtain ⟨z, hz, ⟨a, ha, hy'⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
    · have hz' := hj_capDelete (σ0 := σ0) (I := I) _ hni s hs z hz
      have h0 : DWS σ0 z.2 := ⟨hz'.1.2.2, hz'.2 a ha⟩
      have hD : DWS σ0 y.2 := by
        refine (show IKE (DWS σ0) _ from ?_) z.2 h0 y hy'
        refine ike_bind (ike_liftE (dws_svcf (by sv_auto) (by cfk_auto))) fun _ => ?_
        refine ike_bind (ike_liftE ?_) fun _ => ?_
        · rcases frame with _ | ⟨c, src⟩
          · exact ik_pure _
          · exact (dst_svcf (sv14f_ins _ _ _ _ _) (cfk14f_ins _ _ _ _ _)).dws
        · exact ike_bind (ike_liftE (ik_gets _)) fun _ =>
            ike_liftE (ik_when _ (dst_svcf SVK.sv_rescheduleRequired' cfk_rescheduleRequired').dws)
      have hne : ∀ e, y.1 ≠ .error e := by
        refine (show NoErr _ from ?_) z.2 y hy'
        exact noErr_bind (noErr_liftE _) fun _ => noErr_bind (noErr_liftE _) fun _ =>
          noErr_bind (noErr_liftE _) fun _ => noErr_liftE _
      cases hy1 : y.1 with
      | ok b => exact ⟨⟨hR.2 b hy1, hC, hD.1⟩, fun _ _ => hD.2⟩
      | error e => exact absurd hy1 (hne e)
    · exact ⟨(hj_capDelete (σ0 := σ0) (I := I) _ hni s hs z hz).1, fun _ h => by simp at h⟩

/-! ## An error-free `DWS` tail after the triple -/

/-- Every `ok` outcome `DWS σ0`, every error outcome rd14f E's `J`. -/
def HK (σ0 : State Unit) (I : ObjRef) {α : Type} (m : NonDetE (State Unit) Unit α) : Prop :=
  σ0.curThread ≠ σ0.idleThread → ∀ s, JS σ0 I s → ∀ y ∈ (m.run s).1,
    (∀ a, y.1 = .ok a → DWS σ0 y.2) ∧ (∀ e, y.1 = .error e → J σ0 I y.2)

theorem hk_of_hj {α : Type} {m : NonDetE (State Unit) Unit α} (h : HJ σ0 I m) : HK σ0 I m :=
  fun hni s hs y hy =>
    ⟨fun a ha => ⟨(h hni s hs y hy).1.2.2, (h hni s hs y hy).2 a ha⟩, fun _ _ => (h hni s hs y hy).1⟩

theorem hk_bind {α β : Type} {m : NonDetE (State Unit) Unit α} {g : α → NonDetE (State Unit) Unit β}
    (hm : HJ σ0 I m) (hg : ∀ a, IKE (DWS σ0) (g a)) (hn : ∀ a, NoErr (g a)) : HK σ0 I (m >>= g) := by
  intro hni s hs y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hy
  · have h := hm hni s hs z hz
    exact ⟨fun _ _ => hg a z.2 ⟨h.1.2.2, h.2 a ha⟩ y hy, fun e he' => absurd he' (hn a z.2 y hy e)⟩
  · exact ⟨fun _ h' => by simp at h', fun _ _ => (hm hni s hs z hz).1⟩

/-- **An arm with `HK` and rd8r's `HQ` at its error outcomes** has `PerfA`. -/
theorem perfA_hk {σ0 u : State Unit} {I : ObjRef} {bl call don : Bool} {oper : Fl4Invocation}
    (hB : A10.BS σ0) (hJ : JS σ0 I u) (hm : HK σ0 I (fl4PerformInvocation (Z := Unit) bl call don oper))
    (hq : ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don oper).run u).1, ∀ e, y.1 = .error e → B8r.HQ y.2) :
    PerfA σ0 bl call don oper u := by
  intro y hy
  have h := hm hB.ni u hJ y hy
  refine ⟨fun a ha => Or.inr fun q hq' hc => ss4_dws hB (dws_post call a (h.1 a ha) q hq') hc,
    fun e he z hz _ => ?_⟩
  have hJ' := h.2 e he
  have hQ' := hq y hy e he
  obtain ⟨hBd, hU⟩ := pre_of_dw hB hJ'.2.2
  exact ss4_preemptionPath hJ'.1.1 hQ'.2 hJ'.1.2.2.2.1 hJ'.2.1.1 hJ'.1.2.1.1 (B8r.curHold_of_ho hQ'.1)
    (by rw [hJ'.2.2.ct, hJ'.2.2.it]; exact hB.ni) hBd hU z hz

/-! ## ThreadControlSched's tail -/

theorem sv14f_setPriority (t : ObjRef) (p : Priority) : SVK.SVM (setPriority (Z := Unit) t p) := by
  unfold setPriority threadSetPriority reorderEp reorderNtfn tcbAppend
  repeat' (first | (with_reducible exact A11b.sv_orderedInsert _ _ _ _) | sv_leaf | sv_step0)

theorem cfk14f_setPriority (t : ObjRef) (p : Priority) : CFK (setPriority (Z := Unit) t p) := by
  unfold setPriority threadSetPriority; cfk_auto

theorem cp_bindTcb (p t : ObjRef) : ∀ σ1 c, IK (A8.CP σ1 c) (schedContextBindTcb (Z := Unit) p t) := by
  intro σ1 c
  unfold schedContextBindTcb
  refine ik_bind (A8.cp_threadSet _ _ _ _) fun _ => ik_bind (by cp_leaf) fun _ => ?_
  refine ik_bind (A8.cp_ifCondTest _ _ σ1 _) fun _ => ik_bind (A8.cp_schedContextResume _ σ1 _) fun _ => ?_
  exact ik_bind (ik_gets _) fun _ => ik_when _ (by cp_auto)

theorem qn_bindTcb (p t u : ObjRef) (hne : t ≠ u) : IK (TP (QN u)) (schedContextBindTcb (Z := Unit) p t) := by
  unfold schedContextBindTcb
  refine SInv.ik_bind (tp_threadSet _ _ fun _ _ e => absurd e hne) fun _ => ?_
  refine SInv.ik_bind (by qb_auto) fun _ => ?_
  refine SInv.ik_bind (ik_of_nks (fun _ _ hk h' => tp_sok hk h') (nks_ifCondG _ _ _)) fun _ => ?_
  refine SInv.ik_bind (ik_of_nks (fun _ _ hk h' => tp_sok hk h') (nks_schedContextResume _)) fun _ => ?_
  refine SInv.ik_bind (SInv.ik_gets _) fun _ => SInv.ik_when _ ?_
  exact SInv.ik_bind (qn_of_svm (by sv_auto) _) fun _ => qn_of_svm SVK.sv_rescheduleRequired' _

theorem bl_bindTcb (p t u c : ObjRef) (hne : t ≠ u) : IK (BL u c) (schedContextBindTcb (Z := Unit) p t) := by
  unfold schedContextBindTcb
  refine SInv.ik_bind (SInv.ik_and (tp_threadSet _ _ fun _ _ e => absurd e hne) (by ks_auto)) fun _ => ?_
  refine SInv.ik_bind (SInv.ik_and (by qb_auto) (by ks_auto)) fun _ => ?_
  refine SInv.ik_bind (bl_of_nks (nks_ifCondG _ _ _)) fun _ => ?_
  refine SInv.ik_bind (bl_of_nks (nks_schedContextResume _)) fun _ => ?_
  refine SInv.ik_bind (SInv.ik_gets _) fun _ => SInv.ik_when _ ?_
  exact SInv.ik_bind (bl_of_svm (by sv_auto)) fun _ => bl_of_svm SVK.sv_rescheduleRequired'

/-- **Binding an SC to a TCB other than ct keeps `DWS σ0`.** -/
theorem dws_bindTcb (p t : ObjRef) (hne : t ≠ σ0.curThread) : IK (DWS σ0) (schedContextBindTcb (Z := Unit) p t) := by
  intro s hs y hy
  have hne' : t ≠ s.curThread := by rw [hs.1.ct]; exact hne
  have he : IK (A14d.EC s) (schedContextBindTcb (Z := Unit) p t) :=
    A14d.ec_ik (by unfold schedContextBindTcb; cfk_auto) (cp_bindTcb p t s s.curSc)
      fun w _ h => ik_eb (bl_bindTcb p t _ _ hne') (qn_bindTcb p t _ hne') (nres_of_cp (cp_bindTcb p t)) w h
  exact dws_pt hs (fun y hy => he s (ec_self hs.1) y hy)
    (fun hn => ebn_of (cp_bindTcb p t) (qn_bindTcb p t _ hne') s hn) y hy

theorem dst_unbindTcb (p : ObjRef) : DSt (schedContextUnbindTcb (Z := Unit) p) :=
  ⟨fun σ1 => A14d.ec_schedContextUnbindTcb σ1 p,
    fun _ => ebn_of (fun σ1 c => by unfold schedContextUnbindTcb; cp_auto)
      (by unfold schedContextUnbindTcb; qn14f_auto)⟩

/-! ## The arms -/

theorem perfA_tcCaps {σ0 u : State Unit} {I : ObjRef} (bl call don : Bool) (t : ObjRef) (sl : CslotPtr)
    (fh th cr vr : Option (Cap × CslotPtr)) (buf : Option (VSpaceRef × Option (Cap × CslotPtr))) (hR : RF σ0 u)
    (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u) :
    PerfA σ0 bl call don (.invokeTCB (.threadControlCaps t sl fh th cr vr buf)) u := by
  refine perfA_hj hR.bs (js_rf hR hnis hRB) (hq_rf hR hRB) ?_ ?_
  · show HJ σ0 I (invokeTcb (Z := Unit) (.threadControlCaps t sl fh th cr vr buf))
    simp only [invokeTcb]
    exact hj_bind (hj_installTcbCap _ _ _ _) fun _ => hj_bind (hj_installTcbCap _ _ _ _) fun _ =>
      hj_bind (hj_installTcbCap _ _ _ _) fun _ => hj_bind (hj_installTcbCap _ _ _ _) fun _ =>
        hj_bind (hj_installTcbFrameCap _ _ _) fun _ => hj_ret _
  · show IKE B8r.HQ (invokeTcb (Z := Unit) (.threadControlCaps t sl fh th cr vr buf))
    simp only [invokeTcb]
    exact ike_bind (B8r.hq_installTcbCap _ _ _ _) fun _ => ike_bind (B8r.hq_installTcbCap _ _ _ _) fun _ =>
      ike_bind (B8r.hq_installTcbCap _ _ _ _) fun _ => ike_bind (B8r.hq_installTcbCap _ _ _ _) fun _ =>
        ike_bind (B8r.hq_installTcbFrameCap _ _ _) fun _ => ike_returnOk _

theorem perfA_tcSched {σ0 u : State Unit} {I : ObjRef} (bl call don : Bool) (t : ObjRef) (sl : CslotPtr)
    (fh : Option (Cap × CslotPtr)) (mcp prio : Option (Word8 × ObjRef)) (sc : Option (Option ObjRef))
    (hR : RF σ0 u) (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u)
    (hb : ∀ p, sc = some (some p) → t ≠ σ0.curThread) :
    PerfA σ0 bl call don (.invokeTCB (.threadControlSched t sl fh mcp prio sc)) u := by
  refine perfA_hk hR.bs (js_rf hR hnis hRB) ?_ ?_
  · show HK σ0 I (invokeTcb (Z := Unit) (.threadControlSched t sl fh mcp prio sc))
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
  · show ∀ y ∈ ((invokeTcb (Z := Unit) (.threadControlSched t sl fh mcp prio sc)).run u).1, ∀ e, y.1 = .error e →
      B8r.HQ y.2
    simp only [invokeTcb]
    intro y hy e he
    obtain ⟨z, hz, ⟨a, -, hy'⟩ | ⟨e', -, rfl⟩⟩ := ft_mem_bindE hy
    · exact absurd he ((noErr_bind (noErr_liftE _) fun _ => noErr_bind (noErr_liftE _) fun _ =>
        noErr_bind (noErr_liftE _) fun _ => noErr_returnOk _ : NoErr _) z.2 y hy' e)
    · exact B8r.hq_installTcbCap _ _ _ _ u (hq_rf hR hRB) z hz

def CovTC : Fl4Invocation → Prop
  | .invokeTCB (.threadControlCaps _ _ _ _ _ _ _) => True
  | .invokeTCB (.threadControlSched _ _ _ _ _ _) => True
  | _ => False

theorem armAKD_covTC : ArmAKD CovTC := by
  intro σ0 s u h0 bl cl dn b I hc hB hS hi hz hbo hbr hRB hu
  have hR : RF σ0 u.2 := rf_restart hB hS hz hu
  have et : s.curThread = σ0.curThread := kz_curThread hz
  have hRB' : B8f.RB σ0.curThread I u.2 := by
    rw [← et]; exact B8j.rb_restart s hRB hu
  cases b
  case invokeTCB i =>
    cases i
    case threadControlCaps t sl fh th cr vr buf => exact perfA_tcCaps bl cl dn t sl fh th cr vr buf hR hi hRB'
    case threadControlSched t sl fh mcp prio sc =>
      refine perfA_tcSched bl cl dn t sl fh mcp prio sc hR hi hRB' fun p e => ?_
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

/-- rd14f F's covered set and the ThreadControl arms. -/
def C14f2 (b : Fl4Invocation) : Prop := C14f1 b ∨ CovTC b

theorem armAKD_c14f2 : ArmAKD C14f2 := armAKD_c14f1.or armAKD_covTC

end

end Fl4Proofs.P3.SInvR.A14f
