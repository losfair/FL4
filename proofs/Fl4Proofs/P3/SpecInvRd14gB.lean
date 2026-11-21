/-
P3 (DESIGN.md §9), invariant line G1 (rd14g, rd14f handoff (a), (b), (d)): **the
Untyped and ASID-control arms, the interface `ArmAKU` with its bridge, and the
tops with every perform arm covered** (spec side only).

* **`perfA_untyped`**, **`perfA_asidControl`** (rd14g A's walk), `CovU`.
* **`ArmAKU C`**: rd14f F's `ArmAKD` with rd8n's `UF`, IfLiveT with ct holding a
  thread cap (`SInv.IL [ct]`) and ut8's `GapOKN` at the decode's outcome;
  `armAKU_of`, `ArmAKU.or`, **`armAKU_covU`** (the Restart write keeps `UF`
  (rd8n's `uf_restart`), `IL [ct]` (il1's `il_setThreadState`: Restart is live
  only at ct) and the cap view).
* `il_view` / `il_js` (IL along rd8j's `JS`: TCB states by `KZ`, caps by the
  view), `il_front`, **`gapOKN_of`** (ut8's `okv_fl4DecodeG` on the lookups'
  slot facts, as rd8n's `perfIn_of`), **`perfR_ofKU`**, **`invR_ofKU`**,
  `QU C c σ := QD C c σ ∧ UF σ ∧ IL [ct] σ`, **`brR_ku`**.
* `C14g := C14f2 ∨ CovU`, **`c14g_all`** (every invocation is covered),
  **`armAKU_all : ArmAKU (fun _ => True)`**.
* Tops: `qu_ofW` / `qu_fip` (UF from `uf_ofW` / rd8v's `uf_fip`; IfLiveT from
  `SInvA.live`, ct's thread cap from IfLiveT at the Running / Restart ct of
  `EntryJ`, il1's `il_asUser` across the FaultIP write), **`kcall_rdyOffU`** /
  **`kentry_rdyOffU`** (any `ArmAKU C`), and **`kcall_rdyOffP`** /
  **`kentry_rdyOffP`**: rd8w's tops with no `PerfA` input at all (only rd8w's
  `QF`, PerfF, remains).
-/
import Fl4Proofs.P3.SpecInvRd14gA
open Classical

namespace Fl4Proofs.P3.SInvR.A14g
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14f

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The arms -/

theorem live_of_bound {k : KHeap} {p : ObjRef} (h : SInvB.Bound (SInvB.bv k p)) :
    ∃ o, k p = some o ∧ SInvL.liveO o := by
  obtain ⟨c, hc⟩ := h
  unfold SInvB.bv at hc
  rcases e : k p with _ | o
  · rw [e] at hc; simp at hc
  · rw [e] at hc
    refine ⟨o, rfl, ?_⟩
    cases o <;> simp at hc <;> simp [SInvL.liveO, SInvL.scLv, hc]

/-- The walk's facts at the Restart state. -/
theorem uds_rf {σ0 u : State Unit} {I : ObjRef} (hR : RF σ0 u) (hnis : σ0.curSc ≠ σ0.idleSc)
    (hRB : B8f.RB σ0.curThread I u) : UDS σ0 u := by
  have hc := hR.tb.cf
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨-, e2, e3, e4, e5, -⟩ := hc'
  obtain ⟨x, hx⟩ := hR.ct
  exact ⟨⟨⟨e2, e3, e4, e5, hnis, ⟨x, hx, hR.bd x hx⟩, hR.sc, hR.tb.cw, A11.offReady_kp hR.bs.off hR.kp⟩,
    hRB.2.2.2.2.1⟩, suff_cw hR.suff hR.tb.cw hc⟩

set_option maxHeartbeats 4000000 in
/-- **The Untyped arm** (module docstring). -/
theorem perfA_untyped {σ0 u : State Unit} {I : ObjRef} (bl call don : Bool) (ui : UntypedInvocation)
    (hR : RF σ0 u) (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u) (hF : B8n.UF u)
    (hL : SInv.IfLiveT u) (hok : SInvU.UtRetOK u ui) :
    PerfA σ0 bl call don (.invokeUntyped ui) u := by
  have hJ := js_rf hR hnis hRB
  have hQ := hq_rf hR hRB
  have hU0 := uds_rf hR hnis hRB
  obtain ⟨hRdy, hDK, -, hSI, hv, hIO, hI⟩ := hRB
  have hO : SInvU.IO (fun _ => u.idleSc) u := by rw [hI]; exact hIO
  have hW := du_fl4InvokeUntyped ui u hU0 hF.1 hF.2.1 hF.2.2 hSI.back hO hok
  intro y hy
  simp only [fl4PerformInvocation] at hy
  obtain ⟨z, hz, ⟨a, ha, hy'⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hy
  · obtain rfl := SInvU.mem_ret_ok hy'
    refine ⟨fun a' _ => Or.inr fun q hq hcb =>
      ss4_dws hR.bs (dws_post call a' ⟨(hW z hz).1.dw, (hW z hz).2 a ha⟩ q hq) hcb, fun e he => by cases he⟩
  · refine ⟨(fun a h => by cases h), fun e' _ w hw _ => ?_⟩
    have hd := (hW z hz).1
    have hRz := B8n.rd_fl4InvokeUntyped ui u hRdy hv hF.1 hF.2.1 hF.2.2 hSI.back hO hok z hz
    have hNz : NQ [] z.2 := SInv.nq_invokeUntyped (K := []) ui u hF.1.1.1 hok
      (SInv.nqDet_of_live hF.1 (SInv.ifLiveB_of hL)) hQ.2 z hz
    have hSz : SInvB.ScInv z.2 := SInvB.sc_invokeUntyped ui u hF.1.1.1 hok
      (fun s dv b n fi hc hk p hp hB => by
        obtain ⟨o, hpo, hl⟩ := live_of_bound hB
        exact B8n.bnd_out hF.1 hF.2.1 hF.2.2 hO hc hk hpo hl hp) hSI z hz
    have hKz := R16.ckx_fl4InvokeUntyped σ0.curThread ui u hJ.1.2.1 z hz e he
    have hEz : SInvQ.EB true z.2 :=
      P15.eb_fl4InvokeUntyped (k := true) ui u hF.1 (SInvQ.ifLiveTN_of_ifLiveT hL) hok hDK.1 z hz
    have hHz := B8r.curHold_of_ho (B8r.hqx_fl4InvokeUntyped ui u hQ z hz e he)
    have hni : z.2.curThread ≠ z.2.idleThread := by rw [hd.ct, hd.it]; exact hR.bs.ni
    obtain ⟨hBd, hUn⟩ := pre_of_dw hR.bs hd.dw
    exact ss4_preemptionPath hRz hNz hSz hKz hEz hHz hni hBd hUn w hw

set_option maxHeartbeats 4000000 in
/-- **The ASID-control arm** (MakePool; never errors). -/
theorem perfA_asidControl {σ0 u : State Unit} {I : ObjRef} (bl call don : Bool) (o : AsidControlInvocation)
    (hR : RF σ0 u) (hnis : σ0.curSc ≠ σ0.idleSc) (hRB : B8f.RB σ0.curThread I u) (hF : B8n.UF u)
    (hok : SInvU.MpOKN (SInvU.uV u) o) :
    PerfA σ0 bl call don (.invokeArchObject (.spec (.invokeASIDControl o))) u := by
  have hU0 := uds_rf hR hnis hRB
  obtain ⟨-, -, -, hSI, -, hIO, hI⟩ := hRB
  have hO : SInvU.IO (fun _ => u.idleSc) u := by rw [hI]; exact hIO
  intro y hy
  cases o with
  | makePool frame slot parent base =>
    simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation] at hy
    obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
    obtain ⟨z, hz, hx⟩ := hx
    have hds : DS σ0 z.2 :=
      ds_makePool frame slot parent base u ⟨hU0.1.1, hU0.2⟩ hF.1 hF.2.1 hF.2.2 hSI.back hO hok z hz
    have e := Set.mem_singleton_iff.1 hx
    have hds' : DS σ0 x.2 := by rw [e]; exact hds
    exact ⟨fun a _ => Or.inr fun q hq hcb => ss4_dws hR.bs (dws_post call a ⟨hds'.1.dw, hds'.2⟩ q hq) hcb,
      fun e he => by cases he⟩

def CovU : Fl4Invocation → Prop
  | .invokeUntyped _ => True
  | .invokeArchObject (.spec (.invokeASIDControl _)) => True
  | _ => False

/-! ## The interface -/

/-- rd14f F's `ArmAKD` with rd8n's `UF`, `IL [ct]` and the decode's `GapOKN` at the decode's outcome. -/
def ArmAKU (C : Fl4Invocation → Prop) : Prop :=
  ∀ (σ0 s : State Unit) (u : Unit × State Unit) (h0 : KHeap) (bl cl dn : Bool) (b : Fl4Invocation) (I : ObjRef), C b →
    A10.BS σ0 → Suff σ0 → σ0.curSc ≠ σ0.idleSc → KZ σ0 s → SInvB.BindOK (SInvB.bv h0) b →
    SInvB.BR h0 s.kheap → B8f.RB s.curThread I s → B8n.UF s → SInv.IL [s.curThread] s →
    SInvU.GapOKN (SInvU.uV s) b →
    u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1 → PerfA σ0 bl cl dn b u.2

theorem armAKU_of {C : Fl4Invocation → Prop} (h : ArmAKD C) : ArmAKU C :=
  fun σ0 s u h0 bl cl dn b I hc hB hS hi hz ho hr hRB _ _ _ hu => h σ0 s u h0 bl cl dn b I hc hB hS hi hz ho hr hRB hu

theorem ArmAKU.or {C1 C2 : Fl4Invocation → Prop} (h1 : ArmAKU C1) (h2 : ArmAKU C2) :
    ArmAKU (fun b => C1 b ∨ C2 b) :=
  fun σ0 s u h0 bl cl dn b I hc hB hS hi hz ho hr hRB hF hL hG hu =>
    hc.elim (fun c => h1 σ0 s u h0 bl cl dn b I c hB hS hi hz ho hr hRB hF hL hG hu)
      (fun c => h2 σ0 s u h0 bl cl dn b I c hB hS hi hz ho hr hRB hF hL hG hu)

theorem armAKU_covU : ArmAKU CovU := by
  intro σ0 s u h0 bl cl dn b I hc hB hS hi hz hbo hbr hRB hF hL hG hu
  have hR : RF σ0 u.2 := rf_restart hB hS hz hu
  have et : s.curThread = σ0.curThread := kz_curThread hz
  have hRB' : B8f.RB σ0.curThread I u.2 := by
    rw [← et]; exact B8j.rb_restart s hRB hu
  have hF' : B8n.UF u.2 := B8n.uf_restart hF ⟨rfl, rfl, hRB⟩ hu
  have hL' : SInv.IfLiveT u.2 :=
    (SInv.il_setThreadState (K := [s.curThread]) s.curThread .restart (fun _ => List.mem_singleton_self _)
      s hL u hu).1
  have huv : SInvU.uV u.2 = SInvU.uV s := SInvU.uk_setThreadState s.curThread .restart s rfl u hu
  have hG' : SInvU.GapOKN (SInvU.uV u.2) b := by rw [huv]; exact hG
  cases b
  case invokeUntyped ui => exact perfA_untyped bl cl dn ui hR hi hRB' hF' hL' (SInvU.utRetOK_of_V hG'.1)
  case invokeArchObject i =>
    cases i with
    | spec j =>
      cases j
      case invokeASIDControl o => exact perfA_asidControl bl cl dn o hR hi hRB' hF' hG'
      all_goals exact (hc : False).elim
    | _ => exact (hc : False).elim
  all_goals exact (hc : False).elim

/-! ## The bridge -/

theorem il_view {K : List ObjRef} {σ s : State Unit} (h : SInv.IL K σ)
    (h1 : ∀ p, B8c.tcbV (s.kheap p) = B8c.tcbV (σ.kheap p)) (h2 : SInvU.capAt s = SInvU.capAt σ) :
    SInv.IL K s := by
  have hT : ∀ t, SInv.HasTC s t ↔ SInv.HasTC σ t := fun t => by unfold SInv.HasTC; rw [h2]
  refine ⟨fun t y ht hl => (hT t).2 ?_, fun t ht => (hT t).2 (h.2 t ht)⟩
  have e := h1 t
  rw [ht] at e
  obtain ⟨x, hx, ea⟩ := B8n.tcbV_some (a := (y.tcbState, y.tcbFault, y.tcbSchedContext)) e.symm
  have es : y.tcbState = x.tcbState := congrArg (fun p => p.1) ea
  exact h.1 t x hx (by rw [← es]; exact hl)

theorem il_js {K : List ObjRef} {C I : ObjRef} {σ s : State Unit} (h : SInv.IL K σ) (hJ : B8j.JS C I σ s) :
    SInv.IL K s :=
  il_view h (kz_parts hJ.1).1 (congrArg (fun w : SInvU.UView => w.2.1) hJ.2.1)

theorem il_front {σ : State Unit} (h : SInv.IL [σ.curThread] σ) {v : Bool × State Unit}
    (hv : v ∈ (A8.front σ).1) (ht : v.1 = true) : SInv.IL [v.2.curThread] v.2 := by
  obtain ⟨w, hw, hv'⟩ := hv
  rw [SInvB.checkBudgetRestart_true_eq hv' ht]
  obtain ⟨ek, -, -, -⟩ := SInvO.uts_off hw
  obtain ⟨et, -⟩ := ci_updateTimeStamp σ.curThread σ.idleThread σ ⟨rfl, rfl⟩ w hw
  rw [et]; exact SInv.il_of_kheap ek h

set_option maxHeartbeats 4000000 in
/-- **The decode's `GapOKN`** at the decode's outcome (rd8n's `perfIn_of`). -/
theorem gapOKN_of {σ : State Unit} {fp : Bool} {cptr : CapRef} {w0 : MessageInfo × State Unit}
    (hw0 : w0 ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1) {a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef}
    {s : State Unit} {b : Fl4Invocation} {s' : State Unit}
    (has : (.ok a, s) ∈ ((invF σ.curThread cptr w0.1).run w0.2).1)
    (hbs : (.ok b, s') ∈ ((invE fp cptr σ.curThread w0.1 a).run s).1) : SInvU.GapOKN (SInvU.uV s') b := by
  have hOk : SInvU.OkV (SInvU.uV w0.2) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (SInvU.uV w0.2).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (SInvU.uV w0.2).2.1 p.2 = some p.1 ∧
        SInvU.DestRefV (SInvU.uV w0.2) p.2) (invF σ.curThread cptr w0.1) := by
    unfold invF
    refine SInvU.okv_bind (fun _ => SInvU.uk_capFaultOnFailure _ _ _ (SInvU.uk_lookupCapAndSlot _ _))
      (SInvU.okv_capFaultOnFailure _ _ (SInvU.okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine SInvU.okv_bind_uk (fun _ => ike_liftE (SInvU.uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine SInvU.okv_bind (fun _ => SInvU.uk_lookupExtraCaps _ _ _) (SInvU.okv_lookupExtraCapsN _ _ _)
      fun ex hex => SInvU.okv_returnOk ?_
    exact ⟨hx, hex⟩
  obtain ⟨hcap, hex⟩ := hOk w0.2 rfl _ s has
  have hvs : SInvU.uV s = SInvU.uV w0.2 := B8j.uk_invF (SInvU.uV w0.2) σ.curThread cptr w0.1 w0.2 rfl _ has
  obtain ⟨sl, cap, ex, buf⟩ := a
  have hbs' := hbs
  unfold invE at hbs'
  obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e0, -, he0⟩⟩ := SInvU.mem_bindE' hbs'
  swap
  · simp at he0
  obtain ⟨x0, hx0, e0⟩ := SInvU.mem_liftE' hz0
  subst e0
  simp only [Except.ok.injEq] at ha0
  subst ha0
  have hvx : SInvU.uV x0.2 = SInvU.uV w0.2 :=
    (SInvU.uk_getMrs (uvw := SInvU.uV s) _ _ _ s rfl x0 hx0).trans hvs
  have hv' : SInvU.uV s' = SInvU.uV w0.2 :=
    (SInvU.uk_fl4DecodeInvocation (uvw := SInvU.uV x0.2) _ _ _ _ _ _ _ _ x0.2 rfl _ hb0).trans hvx
  have hG0 : SInvU.GapOKN (SInvU.uV w0.2) b :=
    SInvU.okv_fl4DecodeG fp _ _ _ _ _ _ _ hcap (fun p hp => (hex p hp).1) x0.2 hvx b s' hb0
  rw [hv']; exact hG0

/-- **`PerfRc` gives rd12b's `PerfR`** for any `C` with `ArmAKU C`, from `RB`, `UF` and `IL [ct]` at the
shell start. -/
theorem perfR_ofKU {C : Fl4Invocation → Prop} (hA : ArmAKU C) {σ0 σ : State Unit} {I : ObjRef} (hB : A10.BS σ0)
    (hS : Suff σ0) (hi : σ0.curSc ≠ σ0.idleSc) (hz : KZ σ0 σ) (hRB : B8f.RB σ.curThread I σ) (hF : B8n.UF σ)
    (hL : SInv.IL [σ.curThread] σ) {calling blocking don fp : Bool} {cptr : CapRef}
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
    have hF' : B8n.UF s' := B8v.uf_js hF hJs'
    have hL' : SInv.IL [s'.curThread] s' := by rw [← et]; exact il_js hL hJs'
    have hG := gapOKN_of hw0 ha hb
    rw [et] at hu
    obtain ⟨h0, hok, hbr⟩ := bindOK_invE hb
    exact hA σ0 s' u h0 blocking calling don b I hc hB hS hi hz2 hok hbr hRB' hF' hL' hG hu
  · exact hP

/-- **`InvRc` gives rd12b's `InvR`** for any `C` with `ArmAKU C`. -/
theorem invR_ofKU {C : Fl4Invocation → Prop} (hA : ArmAKU C) {c : Syscall} {σ : State Unit} (hEF : A8.EF σ)
    (hi : σ.curSc ≠ σ.idleSc) (h1 : SInvQ.T1 σ) (hEB : SInvQ.EB true σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ)
    (hV : VfhAll σ) (hF : B8n.UF σ) (hL : SInv.IL [σ.curThread] σ) (h : InvRc C c σ) : InvR c σ := by
  intro v hv ht
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  obtain ⟨ec, ei⟩ := front_ci hEF hv ht
  have hi' : v.2.curSc ≠ v.2.idleSc := by rw [ec, ei]; exact hi
  obtain ⟨hRB, -⟩ := B8j.front_facts hEF h1 hEB hIO hV hv ht
  have hFv := B8v.uf_front hF hv ht
  have hLv := il_front hL hv ht
  have key : ∀ r, ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, B8f.RB g.2.curThread σ.idleSc g.2 ∧ B8n.UF g.2 ∧
      SInv.IL [g.2.curThread] g.2 := by
    intro r g hg
    have hJ := B8j.js_getCapReg r v.2 ⟨rfl, rfl, hRB⟩ g hg
    have ect : g.2.curThread = v.2.curThread := kz_curThread hJ.1
    refine ⟨by rw [ect]; exact hJ.2.2, B8v.uf_js hFv hJ, by rw [ect]; exact il_js hLv hJ⟩
  exact ⟨fun r cl bl dn hc g hg =>
      perfR_ofKU hA hB hS hi' (kz_getCapReg (V := v.2) r v.2 rfl g hg) (key r g hg).1 (key r g hg).2.1
        (key r g hg).2.2 ((h v hv ht).1 r cl bl dn hc g hg),
    fun r cr hc g hg =>
      perfR_ofKU hA hB hS hi' (kz_getCapReg (V := v.2) r v.2 rfl g hg) (key r g hg).1 (key r g hg).2.1
        (key r g hg).2.2 ((h v hv ht).2 r cr hc g hg)⟩

/-- The entry facts the bridge needs beside rd14f F's `QD C`. -/
abbrev QU (C : Fl4Invocation → Prop) (c : Syscall) (σ : State Unit) : Prop :=
  QD C c σ ∧ B8n.UF σ ∧ SInv.IL [σ.curThread] σ

/-- **rd8w's `BrR (QU C)`** for any `ArmAKU C`. -/
theorem brR_ku {C : Fl4Invocation → Prop} (hA : ArmAKU C) :
    ∀ (c : Syscall) (σ : State Unit), A8.EF σ → QU C c σ → InvR c σ :=
  fun _ _ hEF h => invR_ofKU hA hEF h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2 h.2.1 h.2.2 h.1.1

/-! ## Every arm -/

def C14g (b : Fl4Invocation) : Prop := C14f2 b ∨ CovU b

theorem armAKU_c14g : ArmAKU C14g := (armAKU_of armAKD_c14f2).or armAKU_covU

set_option maxHeartbeats 4000000 in
/-- **Every invocation is covered.** -/
theorem c14g_all (b : Fl4Invocation) : C14g b := by
  cases b with
  | invokeTCB i =>
    cases i <;> simp [C14g, C14f2, C14f1, A14e.C14e2, A14e.C14e1, A14d.C14dC, A14d.C14dB, A14d.C14d, A14c.C14c,
      A14b.Cov, A14c.CovC, A14c.CovT, CovTC]
  | invokeCNode i =>
    cases i <;> simp [C14g, C14f2, C14f1, A14e.C14e2, A14e.C14e1, A14d.C14dC, A14d.C14dB, A14d.C14d, A14c.C14c,
      A14b.Cov, A14d.CovD, CovDR]
  | invokeSchedContext i =>
    cases i with
    | invokeSchedContextBind p cap =>
      cases cap <;> simp [C14g, C14f2, C14f1, A14e.C14e2, A14e.C14e1, A14d.C14dC, A14d.C14dB, A14d.C14d,
        A14d.CovD, A14d.CovSc, A14d.CovB]
    | _ => simp [C14g, C14f2, C14f1, A14e.C14e2, A14e.C14e1, A14d.C14dC, A14d.C14dB, A14d.C14d, A14d.CovD,
        A14d.CovSc]
  | invokeArchObject i =>
    cases i with
    | spec j =>
      cases j <;> simp [C14g, C14f2, C14f1, A14e.C14e2, A14e.C14e1, A14d.C14dC, A14d.C14dB, A14d.C14d,
        A14c.C14c, A14b.Cov, CovU]
    | _ => simp [C14g, C14f2, C14f1, A14e.C14e2, A14e.C14e1, A14d.C14dC, A14d.C14dB, A14d.C14d, A14c.C14c,
        A14b.Cov]
  | _ => simp [C14g, C14f2, C14f1, A14e.C14e2, A14e.C14e1, A14d.C14dC, A14d.C14dB, A14d.C14d, A14c.C14c,
      A14b.Cov, A14d.CovCfg, A14e.CovR, A14e.CovI, CovU]

/-- **`ArmAKU` for every invocation.** -/
theorem armAKU_all : ArmAKU (fun _ => True) :=
  fun σ0 s u h0 bl cl dn b I _ hB hS hi hz ho hr hRB hF hL hG hu =>
    armAKU_c14g σ0 s u h0 bl cl dn b I (c14g_all b) hB hS hi hz ho hr hRB hF hL hG hu

theorem invRc_all (c : Syscall) (σ : State Unit) : InvRc (fun _ => True) c σ :=
  fun _ _ _ => ⟨fun _ _ _ _ _ _ _ => fun _ _ _ _ _ _ _ _ _ _ => Or.inl trivial,
    fun _ _ _ _ _ => fun _ _ _ _ _ _ _ _ _ _ => Or.inl trivial⟩

/-! ## Tops -/

section Tops
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19
open Fl4Proofs.P3.SInvR.B8w

variable {σ : State Unit}

/-- IfLiveT with the Running / Restart ct holding a thread cap. -/
theorem il_ofW (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread) : SInv.IL [σ.curThread] σ := by
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJ h.sb hct).ctAct
  refine ⟨h.a.live, fun t ht => ?_⟩
  rw [List.mem_singleton.1 ht]
  refine h.a.live _ x0 hx0 ?_
  revert ha0
  generalize x0.tcbState = st
  cases st <;> intro h0 <;> first | trivial | exact False.elim h0

theorem qu_ofW {C : Fl4Invocation → Prop} {ev : Event} (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (c : Syscall) (e : ev = .syscallEvent c)
    (hP : A14c.InvRc C c σ) : QU C c σ :=
  ⟨qd_ofW h hev c e hP, uf_ofW h, il_ofW h (hev (by rw [e]; intro h; cases h))⟩

set_option maxHeartbeats 4000000 in
/-- **`SInvW` across every kernel event** with `PerfA` asked only outside `C` (`ArmAKU C`). -/
theorem kcall_rdyOffU {C : Fl4Invocation → Prop} (hA : ArmAKU C) (hnd : numDomains = 1) (rep : Bool) (ev : Event)
    (h : SInvW σ) (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    {QF : Syscall → State Unit → Prop} (bF : BrF QF)
    (hP : ∀ c, ev = .syscallEvent c → A14c.InvRc C c σ) (hF : ∀ c, ev = .syscallEvent c → QF c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffW hnd rep ev h hev (brR_ku hA) bF (fun c e => qu_ofW h hev c e (hP c e)) hF

theorem qu_fip {C : Fl4Invocation → Prop} (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, A14c.InvRc C c w.2 → QU C c w.2 := by
  intro w hw hP
  have hc : cfS w.2 = cfS σ :=
    (by unfold fl4SyscallFaultIP; cfk_auto : CFK (fl4SyscallFaultIP (Z := Unit) σ.curThread)) σ w hw
  have ect : w.2.curThread = σ.curThread := congrArg (fun p => p.2.2.1) hc
  have hL : SInv.IL [σ.curThread] w.2 :=
    (by unfold fl4SyscallFaultIP; exact SInv.il_asUser _ _ : SInv.ILK [σ.curThread]
      (fl4SyscallFaultIP (Z := Unit) σ.curThread)) σ (il_ofW h hct) w hw
  refine ⟨qd_fip c h hct w hw hP, B8v.uf_fip (uf_ofW h) w hw, ?_⟩
  rw [ect]; exact hL

set_option maxHeartbeats 4000000 in
/-- **`SInvW` across the syscall entry** with `PerfA` asked only outside `C` (`ArmAKU C`). -/
theorem kentry_rdyOffU {C : Fl4Invocation → Prop} (hA : ArmAKU C) (hnd : numDomains = 1) (c : Syscall)
    (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread) {QF : Syscall → State Unit → Prop} (bF : BrF QF)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, A14c.InvRc C c w.2 ∧ QF c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 :=
  kentry_rdyOffW hnd c h hct (brR_ku hA) bF fun w hw => ⟨qu_fip c h hct w hw (hW w hw).1, (hW w hw).2⟩

/-- **No `PerfA` input**: every perform arm covered (`armAKU_all`); only rd8w's `QF` (PerfF) remains. -/
theorem kcall_rdyOffP (hnd : numDomains = 1) (rep : Bool) (ev : Event) (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) {QF : Syscall → State Unit → Prop} (bF : BrF QF)
    (hF : ∀ c, ev = .syscallEvent c → QF c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffU armAKU_all hnd rep ev h hev bF (fun c _ => invRc_all c σ) hF

theorem kentry_rdyOffP (hnd : numDomains = 1) (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread)
    {QF : Syscall → State Unit → Prop} (bF : BrF QF)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, QF c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 :=
  kentry_rdyOffU armAKU_all hnd c h hct bF fun w hw => ⟨invRc_all c w.2, hW w hw⟩

end Tops

end

end Fl4Proofs.P3.SInvR.A14g
