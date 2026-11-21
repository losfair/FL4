/-
P3 (DESIGN.md §9), invariant line G1 (rd14f, KENTRY-PLAN rd14e-3): **the
deletion arms' end, CNode delete / revoke, the interface with rd8f's `RB`**
(spec side only).

* End: `dws_svs`, `dws_post` (the post keeps `DWS σ0`), **`ss4_dws`** (`DWS σ0`
  and `CB` ⇒ `SS4`: `OS` by its first disjunct while cur_sc's refills are
  σ0's, by rd14e's `OI` once its max is 0), `pre_of_dw` (the bound / unbound
  facts of rd14f B's `ss4_preemptionPath`), **`perfA_hj`** (an arm whose
  perform keeps rd14f E's triple and rd8r's `HQ` has `PerfA`).
* The Restart state: `js_rf` (rd14c's `RF` and `RB` at the Restart state give
  rd14f E's `JS`), `ho_rf` (ct is the only holder of cur_sc: sb2's `ScBack`),
  `hq_rf`.
* **`perfA_cnodeDelete`**, **`perfA_cnodeRevoke`**, `CovDR`.
* **`ArmAKD C`**: rd14f A's `ArmAKV` with rd8f's `RB ct I` at the decode's
  outcome; `armAKD_of`, `ArmAKD.or`, **`perfR_ofKD`** (rd8j's `JS` walk carries
  `RB` from the shell start), **`invR_ofKD`** (rd8j's `front_facts`),
  **`brR_kd`** (rd8w's `BrR` with the entry facts `T1`, `EB true`,
  `IdleScOutV`, `VfhAll` and cur_sc ≠ idle_sc inside `Q`), `armAKD_covDR`,
  `C14f1 := C14e2 ∨ CovDR`, **`armAKD_c14f1`**.
-/
import Fl4Proofs.P3.SpecInvRd14fE
open Classical

namespace Fl4Proofs.P3.SInvR.A14f
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The end of an arm -/

theorem dws_svs {σ0 s y : State Unit} (h : DWS σ0 s) (hS : SVK.SVS s y) (hc : cfS y = cfS s) : DWS σ0 y := by
  have hw : A8.CW s.curSc s y := A8.cw_of_svs hS
  refine ⟨dw_step h.1 hc hw ?_ fun hn => ebr_svs hn hS, suff_cw h.2 hw hc⟩
  have e : A14b.EB s.curThread s.curSc s := by rw [h.1.ct, h.1.cs]; exact h.1.eb
  exact eb_svs e hS

/-- **The post keeps `DWS σ0`.** -/
theorem dws_post (calling : Bool) (reply : List Data) {σ0 s : State Unit} (h : DWS σ0 s) :
    ∀ y ∈ (invPost calling σ0.curThread reply s).1, DWS σ0 y.2 := by
  intro y hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  dsimp only at hy
  revert hy
  generalize x.tcbState = st
  cases st <;> intro hy
  case restart =>
    obtain ⟨u, hu, hy⟩ := hy
    have h1 := dws_svs h (sv_whenReply calling _ _ s u hu) (cfk_whenReply calling _ _ s u hu)
    exact dws_svs h1 (SVK.sv_setThreadState' _ _ u.2 y hy) (cfk_setThreadState' _ _ u.2 y hy)
  all_goals (rw [Set.mem_singleton_iff.1 hy]; exact h)

/-- cur_sc active while its refills / max are σ0's. -/
theorem act_cw {σ0 q : State Unit} (hB : A10.BS σ0) (hw : A8.CW σ0.curSc σ0 q) :
    ∀ y n, q.kheap σ0.curSc = some (.schedContext y n) → scActive y = true := by
  intro y n hy
  obtain ⟨y0, n0, hy0, -, hm⟩ := hw.1 y n hy
  obtain ⟨xa, c, z, m, hxa, hca, hkz, hact⟩ := hB.ca hB.ni
  rw [hB.cs xa hxa] at hca; cases hca
  rw [hkz] at hy0; cases hy0
  simp only [scActive, hm]; exact hact

/-- **`DWS σ0` and `CB` give `SS4`.** -/
theorem ss4_dws {σ0 q : State Unit} (hB : A10.BS σ0) (h : DWS σ0 q) (hcb : CB q) : A10.SS4 q := by
  obtain ⟨hd, hSf⟩ := h
  have ni : q.curThread ≠ q.idleThread := by rw [hd.ct, hd.it]; exact hB.ni
  have hOS : OS q := by
    rcases hd.rf with ⟨-, hO⟩ | ⟨hm, hn⟩
    · exact Or.inl ⟨hO, hSf⟩
    · refine Or.inr (Or.inr ⟨by rw [hd.cs, hd.is]; exact hd.nis, fun y n hy => ?_, hn.2⟩)
      rw [hd.cs] at hy
      simp only [scActive, activeSc, hm y n hy, lt_self_iff_false, decide_false]
  rcases hd.eb with ⟨hq, hk⟩ | ⟨hq, hn⟩
  · -- ct bound to cur_sc
    have hb' : ∀ x, q.kheap q.curThread = some (.tcb x) → x.tcbSchedContext = some q.curSc := by
      intro x hx; rw [hd.cs]; exact hq _ x (by rw [← hd.ct]; exact hx) rfl
    rcases hd.rf with ⟨hw, hO⟩ | ⟨-, hn⟩
    · refine ⟨hOS, fun hres _ => ?_, A8.ctR_of_off hb' hO, fun _ x hx => hb' x hx⟩
      rcases hcb hres with ⟨x, hx, -⟩ | hi
      · obtain ⟨y, n, hy⟩ := hk
        exact ⟨x, q.curSc, y, n, hx, hb' x hx, by rw [hd.cs]; exact hy, act_cw hB hw y n hy⟩
      · exact absurd hi ni
    · refine ⟨hOS, fun e => absurd e hn.2, ?_, fun e => absurd e hn.2⟩
      intro x hx _ _ _
      have e1 := hb' x hx
      have e2 := hn.1 _ x (by rw [← hd.ct]; exact hx) rfl
      rw [e2] at e1; cases e1
  · -- ct unbound, no resume
    refine ⟨hOS, fun e => absurd e hn, fun x hx _ hA _ => ?_, fun e => absurd e hn⟩
    obtain ⟨x', c, y, n, h1, h2, -, -⟩ := hA
    rw [hx] at h1
    cases h1
    rw [hq _ x (by rw [← hd.ct]; exact hx) rfl] at h2; cases h2

/-- The facts rd14f B's preemption path asks of the walk. -/
theorem pre_of_dw {σ0 p : State Unit} (hB : A10.BS σ0) (hd : DW σ0 p) :
    (∀ x, p.kheap p.curThread = some (.tcb x) → x.tcbSchedContext = some p.curSc →
      (∀ y n, p.kheap p.curSc = some (.schedContext y n) → scActive y = true) ∧ Sched.OffReady p) ∧
    (∀ x, p.kheap p.curThread = some (.tcb x) → x.tcbSchedContext = none → NRes p) := by
  refine ⟨fun x hx hb => ?_, fun x hx hn => ?_⟩
  · rcases hd.rf with ⟨hw, hO⟩ | ⟨-, hn⟩
    · exact ⟨fun y n hy => act_cw hB hw y n (by rw [← hd.cs]; exact hy), hO⟩
    · have e := hn.1 _ x (by rw [← hd.ct]; exact hx) rfl
      rw [e] at hb; cases hb
  · rcases hd.eb with ⟨hq, -⟩ | ⟨-, hnr⟩
    · have e := hq _ x (by rw [← hd.ct]; exact hx) rfl
      rw [e] at hn; cases hn
    · exact hnr

/-- **An arm keeping rd14f E's triple and rd8r's `HQ`** has `PerfA`. -/
theorem perfA_hj {σ0 u : State Unit} {I : ObjRef} {bl call don : Bool} {oper : Fl4Invocation}
    (hB : A10.BS σ0) (hJ : JS σ0 I u) (hQ : B8r.HQ u)
    (hm : HJ σ0 I (fl4PerformInvocation (Z := Unit) bl call don oper))
    (hq : IKE B8r.HQ (fl4PerformInvocation (Z := Unit) bl call don oper)) :
    PerfA σ0 bl call don oper u := by
  intro y hy
  have h := hm hB.ni u hJ y hy
  refine ⟨fun a ha => Or.inr fun q hq' hc => ss4_dws hB (dws_post call a ⟨h.1.2.2, h.2 a ha⟩ q hq') hc,
    fun e he z hz _ => ?_⟩
  have hQ' := hq u hQ y hy
  have hd := h.1.2.2
  obtain ⟨hBd, hU⟩ := pre_of_dw hB hd
  exact ss4_preemptionPath h.1.1.1 hQ'.2 h.1.1.2.2.2.1 h.1.2.1.1 h.1.1.2.1.1 (B8r.curHold_of_ho hQ'.1)
    (by rw [hd.ct, hd.it]; exact hB.ni) hBd hU z hz

/-! ## The Restart state -/

theorem js_rf {σ0 u : State Unit} {I : ObjRef} (hR : RF σ0 u) (hnis : σ0.curSc ≠ σ0.idleSc)
    (hRB : B8f.RB σ0.curThread I u) : JS σ0 I u := by
  have hc := hR.tb.cf
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨-, e2, e3, e4, e5, -⟩ := hc'
  refine ⟨⟨hRB, ⟨fun x hx => ⟨Or.inr ?_, fun r e => ?_⟩, e3⟩, ⟨e2, e3, e4, e5, hnis,
    Or.inl ⟨fun p x hx he => by subst he; exact hR.bd x hx, hR.sc⟩,
    Or.inl ⟨hR.tb.cw, A11.offReady_kp hR.bs.off hR.kp⟩⟩⟩, suff_cw hR.suff hR.tb.cw hc⟩
  · rw [e2]; exact hR.bd x (by rw [← e3]; exact hx)
  · rw [hR.rs x (by rw [← e3]; exact hx)] at e; cases e

/-- **`HO` at the Restart state**: ct (Restart) is the only holder of cur_sc. -/
theorem ho_rf {σ0 u : State Unit} (hR : RF σ0 u) (hS : SInvB.ScInv u) : B8r.HO u := by
  have hc := hR.tb.cf
  simp only [cfS, Prod.mk.injEq] at hc
  obtain ⟨-, e2, e3, -, -, -⟩ := hc
  intro t x hx hb
  obtain ⟨x0, hx0⟩ := hR.ct
  have hb0 : x0.tcbSchedContext = some u.curSc := by rw [e2]; exact hR.bd x0 hx0
  obtain ⟨y1, k1, h1, t1, -⟩ := hS.back t x _ hx hb
  obtain ⟨y2, k2, h2, t2, -⟩ := hS.back _ x0 _ hx0 hb0
  rw [h1] at h2
  cases h2
  rw [t1] at t2
  cases t2
  have ex : x = x0 := by rw [hx] at hx0; cases hx0; rfl
  subst ex
  rw [hR.rs x hx]
  exact e3.symm

theorem hq_rf {σ0 u : State Unit} {I : ObjRef} (hR : RF σ0 u) (hRB : B8f.RB σ0.curThread I u) : B8r.HQ u :=
  ⟨ho_rf hR hRB.2.2.2.1, hRB.2.1.2.2.2.1, fun _ h => by simp at h⟩

/-! ## CNode delete / revoke -/

theorem perfA_cnodeDelete {σ0 u : State Unit} {I : ObjRef} (bl call don : Bool) (sl : CslotPtr) (hR : RF σ0 u)
    (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u) :
    PerfA σ0 bl call don (.invokeCNode (.deleteCall sl)) u := by
  refine perfA_hj hR.bs (js_rf hR hnis hRB) (hq_rf hR hRB) ?_ ?_
  · show HJ σ0 I (invokeCnode (Z := Unit) (.deleteCall sl) >>= fun _ => NonDetE.returnOk [])
    exact hj_bind (hj_capDelete sl) fun _ => hj_ret _
  · show IKE B8r.HQ (invokeCnode (Z := Unit) (.deleteCall sl) >>= fun _ => NonDetE.returnOk [])
    exact ike_bind (B8r.hq_capDelete sl) fun _ => ike_returnOk _

theorem perfA_cnodeRevoke {σ0 u : State Unit} {I : ObjRef} (bl call don : Bool) (sl : CslotPtr) (hR : RF σ0 u)
    (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u) :
    PerfA σ0 bl call don (.invokeCNode (.revokeCall sl)) u := by
  refine perfA_hj hR.bs (js_rf hR hnis hRB) (hq_rf hR hRB) ?_ ?_
  · show HJ σ0 I (invokeCnode (Z := Unit) (.revokeCall sl) >>= fun _ => NonDetE.returnOk [])
    exact hj_bind (hj_capRevoke sl) fun _ => hj_ret _
  · show IKE B8r.HQ (invokeCnode (Z := Unit) (.revokeCall sl) >>= fun _ => NonDetE.returnOk [])
    exact ike_bind (B8r.hq_capRevoke sl) fun _ => ike_returnOk _

def CovDR : Fl4Invocation → Prop
  | .invokeCNode (.deleteCall _) => True
  | .invokeCNode (.revokeCall _) => True
  | _ => False

/-! ## The interface with `RB` -/

/-- rd14f A's `ArmAKV` with rd8f's `RB ct I` at the decode's outcome. -/
def ArmAKD (C : Fl4Invocation → Prop) : Prop :=
  ∀ (σ0 s : State Unit) (u : Unit × State Unit) (h0 : KHeap) (bl cl dn : Bool) (b : Fl4Invocation) (I : ObjRef), C b →
    A10.BS σ0 → Suff σ0 → σ0.curSc ≠ σ0.idleSc → KZ σ0 s → SInvB.BindOK (SInvB.bv h0) b →
    SInvB.BR h0 s.kheap → B8f.RB s.curThread I s →
    u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1 → PerfA σ0 bl cl dn b u.2

theorem armAKD_of {C : Fl4Invocation → Prop} (h : ArmAKV C) : ArmAKD C :=
  fun σ0 s u h0 bl cl dn b _ hc hB hS hi hz ho hr _ hu => h σ0 s u h0 bl cl dn b hc hB hS hi hz ho hr hu

theorem ArmAKD.or {C1 C2 : Fl4Invocation → Prop} (h1 : ArmAKD C1) (h2 : ArmAKD C2) :
    ArmAKD (fun b => C1 b ∨ C2 b) :=
  fun σ0 s u h0 bl cl dn b I hc hB hS hi hz ho hr hRB hu =>
    hc.elim (fun c => h1 σ0 s u h0 bl cl dn b I c hB hS hi hz ho hr hRB hu)
      (fun c => h2 σ0 s u h0 bl cl dn b I c hB hS hi hz ho hr hRB hu)

theorem armAKD_covDR : ArmAKD CovDR := by
  intro σ0 s u h0 bl cl dn b I hc hB hS hi hz hbo hbr hRB hu
  have hR : RF σ0 u.2 := rf_restart hB hS hz hu
  have et : s.curThread = σ0.curThread := kz_curThread hz
  have hRB' : B8f.RB σ0.curThread I u.2 := by
    rw [← et]; exact B8j.rb_restart s hRB hu
  cases b
  case invokeCNode i =>
    cases i
    case deleteCall sl => exact perfA_cnodeDelete bl cl dn sl hR hi hRB'
    case revokeCall sl => exact perfA_cnodeRevoke bl cl dn sl hR hi hRB'
    all_goals exact (hc : False).elim
  all_goals exact (hc : False).elim

/-- **`PerfRc` gives rd12b's `PerfR`** for any `C` with `ArmAKD C`, from `RB` at the shell start. -/
theorem perfR_ofKD {C : Fl4Invocation → Prop} (hA : ArmAKD C) {σ0 σ : State Unit} {I : ObjRef} (hB : A10.BS σ0)
    (hS : Suff σ0) (hi : σ0.curSc ≠ σ0.idleSc) (hz : KZ σ0 σ) (hRB : B8f.RB σ.curThread I σ)
    {calling blocking don fp : Bool} {cptr : CapRef}
    (h : PerfRc C σ0 calling blocking don fp cptr σ) : PerfR σ0 calling blocking don fp cptr σ := by
  intro w0 hw0 a s b s' ha hb u hu
  rcases h w0 hw0 a s b s' ha hb u hu with hc | hP
  · have hz0 : KZ σ0 w0.2 := kz_trans hz (kz_getMessageInfo (V := σ) _ σ rfl w0 hw0)
    have hz1 : KZ σ0 s := kz_invF _ _ _ w0.2 hz0 _ ha
    have hz2 : KZ σ0 s' := kz_trans hz1 (kz_invE _ _ _ _ a s rfl _ hb)
    have hJ0 : B8j.JS σ.curThread I σ σ := ⟨rfl, rfl, hRB⟩
    have hJw := B8j.js_getMessageInfo _ σ hJ0 w0 hw0
    have hJs := B8j.js_invF _ _ _ w0.2 hJw _ ha
    have hJs' := B8j.js_invE _ _ _ _ a s hJs _ hb
    have et : σ.curThread = s'.curThread := by rw [kz_curThread hz2, kz_curThread hz]
    have hRB' : B8f.RB s'.curThread I s' := by rw [← et]; exact hJs'.2.2
    rw [et] at hu
    obtain ⟨h0, hok, hbr⟩ := bindOK_invE hb
    exact hA σ0 s' u h0 blocking calling don b I hc hB hS hi hz2 hok hbr hRB' hu
  · exact hP

/-- **`InvRc` gives rd12b's `InvR`** for any `C` with `ArmAKD C`. -/
theorem invR_ofKD {C : Fl4Invocation → Prop} (hA : ArmAKD C) {c : Syscall} {σ : State Unit} (hEF : A8.EF σ)
    (hi : σ.curSc ≠ σ.idleSc) (h1 : SInvQ.T1 σ) (hEB : SInvQ.EB true σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ)
    (hV : VfhAll σ) (h : InvRc C c σ) : InvR c σ := by
  intro v hv ht
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  obtain ⟨ec, ei⟩ := front_ci hEF hv ht
  have hi' : v.2.curSc ≠ v.2.idleSc := by rw [ec, ei]; exact hi
  obtain ⟨hRB, -⟩ := B8j.front_facts hEF h1 hEB hIO hV hv ht
  have hRBg : ∀ r, ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, B8f.RB g.2.curThread σ.idleSc g.2 := by
    intro r g hg
    have hJ := B8j.js_getCapReg r v.2 ⟨rfl, rfl, hRB⟩ g hg
    have ect : g.2.curThread = v.2.curThread := kz_curThread hJ.1
    rw [ect]; exact hJ.2.2
  exact ⟨fun r cl bl dn hc g hg =>
      perfR_ofKD hA hB hS hi' (kz_getCapReg (V := v.2) r v.2 rfl g hg) (hRBg r g hg)
        ((h v hv ht).1 r cl bl dn hc g hg),
    fun r cr hc g hg =>
      perfR_ofKD hA hB hS hi' (kz_getCapReg (V := v.2) r v.2 rfl g hg) (hRBg r g hg)
        ((h v hv ht).2 r cr hc g hg)⟩

/-- The entry facts the bridge needs beside `InvRc C`. -/
abbrev QD (C : Fl4Invocation → Prop) (c : Syscall) (σ : State Unit) : Prop :=
  InvRc C c σ ∧ σ.curSc ≠ σ.idleSc ∧ SInvQ.T1 σ ∧ SInvQ.EB true σ ∧ SInvU.IO (fun _ => σ.idleSc) σ ∧ VfhAll σ

/-- **rd8w's `BrR (QD C)`** for any `ArmAKD C`. -/
theorem brR_kd {C : Fl4Invocation → Prop} (hA : ArmAKD C) :
    ∀ (c : Syscall) (σ : State Unit), A8.EF σ → QD C c σ → InvR c σ :=
  fun _ _ hEF h => invR_ofKD hA hEF h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 h.1

/-- rd14e's covered set and CNode delete / revoke. -/
def C14f1 (b : Fl4Invocation) : Prop := A14e.C14e2 b ∨ CovDR b

theorem armAKD_c14f1 : ArmAKD C14f1 := (armAKD_of armAKV_c14e2).or armAKD_covDR

end

end Fl4Proofs.P3.SInvR.A14f
