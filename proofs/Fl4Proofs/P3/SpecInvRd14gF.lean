/-
P3 (DESIGN.md §9), invariant line G1 (rd14g, rd14f handoff (c)): **`PerfF` for the
Endpoint arm** (send_ipc with blocking = call = false, can_donate = true, ct the
sender; spec side only).

* `NF t s`: `t`'s TCB, if any, has no fault. `nf_of_tv` (rd8d's `TV`),
  `nf_threadSet`, `nf_setThreadState` (any thread, any state), `nf_kz` (rd12b's
  `KZ`: `tcbV` holds the fault), `nf_maybeUnlink`.
* **`ep_sendIpcF`**: rd14b's `ep_sendIpc` for these flags with `NF ct`: the
  `call ∨ fault ≠ none` branch (reply_push / Inactive) is dead, so every outcome
  has rd14b's `EB ct cur_sc` (a donation to the receiver leaves ct unbound) and
  rd14c's `QT ct`; **`perfF_endpoint`** (rd14g C's `rtc_ec`, `perfF_q`).
* The interface **`ArmFV C`** (rd14g C's `ArmFU` with `NF ct` at the front
  state), `armFV_of`, `ArmFV.or`, **`armFV_covE`** (the Restart write keeps `NF`),
  `nf_front`, **`perfFR_ofKV`**, **`invF_ofKV`**, `QFV C := QFU C ∧ NF ct`,
  **`brF_kv`**; `NF ct` at the entry from SInvA's `FaultTcbsS` (l4v
  `fault_tcb_states`: ct is Running / Restart, so it has no fault), across the
  FaultIP write by `TV`.
* `CF14g3 := CF14g2 ∨ CovE`, tops **`kcall_rdyOffG3`** / **`kentry_rdyOffG3`**
  (no PerfA input; PerfF only outside `CF14g3`: SchedControl configure, CNode
  delete / revoke, ThreadControlCaps / ThreadControlSched).
-/
import Fl4Proofs.P3.SpecInvRd14gE
open Classical

namespace Fl4Proofs.P3.SInvR.A14g
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14e Fl4Proofs.P3.SInvR.A14f

noncomputable section

set_option maxHeartbeats 1000000

/-! ## ct has no fault -/

/-- `t`'s TCB, if any, has no fault. -/
abbrev NF (t : ObjRef) (s : State Unit) : Prop := ∀ x, s.kheap t = some (.tcb x) → x.tcbFault = none

theorem nf_of_tv (t : ObjRef) {α : Type} {m : NonDet (State Unit) α} (h : ∀ V, B8d.TVK V m) : IK (NF t) m := by
  intro s hs y hy x hx
  have e1 := congrFun (h (B8d.TVv s) s rfl y hy) t
  have e2 : B8c.tcbV (y.2.kheap t) = some (x.tcbState, x.tcbFault, x.tcbSchedContext) := by rw [hx]; rfl
  have e1' : B8c.tcbV (y.2.kheap t) = B8c.tcbV (s.kheap t) := e1
  rw [e1'] at e2
  obtain ⟨x0, hx0, ev⟩ := A12b.tcbV_some e2
  have e3 : x.tcbFault = x0.tcbFault := (congrArg (fun p => p.2.1) ev).symm
  rw [e3]; exact hs x0 hx0

theorem nf_threadSet (t : ObjRef) (f : Tcb → Tcb) (p : ObjRef) (hf : ∀ x, (f x).tcbFault = x.tcbFault) :
    IK (NF t) (threadSet (Z := Unit) f p) := by
  intro s hs y hy x hx
  obtain ⟨x0, hx0, e⟩ := SInv.mem_threadSet hy
  rw [e] at hx
  dsimp only at hx
  by_cases hp : p = t
  · subst hp
    rw [Function.update_self] at hx
    cases hx
    rw [hf]; exact hs x0 hx0
  · rw [Function.update_of_ne (fun h => hp h.symm)] at hx
    exact hs x hx

theorem nf_setThreadState (t p : ObjRef) (st : ThreadState) : IK (NF t) (setThreadState (Z := Unit) p st) := by
  unfold setThreadState
  refine SInv.ik_bind (nf_threadSet t _ p fun _ => rfl) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction
  repeat' (first | (with_reducible apply SInv.ik_when) | ik_step0)

theorem nf_kz {σ0 s : State Unit} (hz : KZ σ0 s) {t : ObjRef} (h : NF t σ0) : NF t s := by
  intro x hx
  have e := (kz_parts hz).1 t
  rw [hx] at e
  obtain ⟨x0, hx0, ea⟩ := B8n.tcbV_some (a := (x.tcbState, x.tcbFault, x.tcbSchedContext)) e.symm
  have : x.tcbFault = x0.tcbFault := congrArg (fun p => p.2.1) ea
  rw [this]; exact h x0 hx0

theorem nf_maybeUnlink (t d : ObjRef) (r : Option ObjRef) :
    IK (NF t) (NonDet.maybeM (replyUnlinkTcb (Z := Unit) d) r) := by
  cases r with
  | none => unfold NonDet.maybeM; exact ik_pure _
  | some r =>
    unfold NonDet.maybeM replyUnlinkTcb
    refine SInv.ik_bind (nf_of_tv t fun _ => by unfold getReply; tv_auto) fun _ => ?_
    refine SInv.ik_bind (ik_assert _) fun _ => ?_
    refine SInv.ik_bind (nf_of_tv t fun _ => by unfold getThreadState; tv_auto) fun _ => ?_
    refine SInv.ik_bind (ik_assert _) fun _ => ?_
    exact SInv.ik_bind (nf_of_tv t fun _ => by unfold setReplyObjRef; tv_auto) fun _ => nf_setThreadState t d _

/-! ## `send_ipc` of ct, not blocking, not calling -/

theorem qt_schedContextDonate (t p u : ObjRef) : IK (QT t) (schedContextDonate (Z := Unit) p u) := by
  unfold schedContextDonate; qt14g_auto

theorem qt_wakeTail (t dest : ObjRef) : IK (QT t) (do
      setThreadState (Z := Unit) dest .running
      let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck destSc
      possibleSwitchTo dest) := by
  qt14g_auto

set_option maxHeartbeats 4000000 in
/-- **`send_ipc` of the non-faulting current thread `t` bound to `c`, not blocking, not calling**:
every outcome has `EB t c` and `QT t`. -/
theorem ep_sendIpcF (bd : Badge) (g gr : Bool) (t c ep : ObjRef) (σ : State Unit)
    (hct : σ.curThread = t) (hr : TP (QRn t) σ) (hb : TP (QB t c) σ ∧ KS c σ) (hq : QT t σ) (hn : NF t σ) :
    ∀ y ∈ (sendIpc (Z := Unit) false false bd g gr true t ep σ).1, EB t c y.2 ∧ QT t y.2 := by
  unfold sendIpc
  intro y ⟨e, he, hy⟩
  obtain ⟨hk, hs⟩ := mem_getSimpleKo he
  obtain ⟨ev, σ1⟩ := e
  simp only at hk hs; subst hs
  cases ev with
  | idleEP =>
    have ey : y = ((), σ1) := hy
    subst ey; exact ⟨Or.inl hb, hq⟩
  | sendEP q =>
    have ey : y = ((), σ1) := hy
    subst ey; exact ⟨Or.inl hb, hq⟩
  | recvEP l =>
    cases l with
    | nil => exact hy.elim
    | cons dest q =>
      obtain ⟨z1, hz1, hy⟩ := hy
      have hS1 := sv_tcbEpDequeue dest ep σ1 z1 hz1
      have hc1 := cfk_tcbEpDequeue' dest ep σ1 z1 hz1
      have hR1 : TP (QRn t) z1.2 :=
        (by unfold tcbEpDequeue; qb_auto : IK (TP (QRn t)) (tcbEpDequeue (Z := Unit) dest ep)) σ1 hr z1 hz1
      have hq1 : QT t z1.2 := (qt_of_tv t fun _ => by unfold tcbEpDequeue; tv_auto) σ1 hq z1 hz1
      have hn1 : NF t z1.2 := (nf_of_tv t fun _ => by unfold tcbEpDequeue; tv_auto) σ1 hn z1 hz1
      obtain ⟨z2, hz2, hy⟩ := hy
      unfold getThreadState at hz2
      obtain ⟨xd, hxd, rfl⟩ := mem_threadGet hz2
      dsimp only at hy
      cases hst : xd.tcbState with
      | blockedOnReceive ep' reply dd =>
        have hne : dest ≠ t := by
          intro e; subst e
          have h2 := hR1 dest xd hxd rfl
          rw [hst] at h2; simp [runnable] at h2
        rw [hst] at hy
        obtain ⟨z3, hz3, hy⟩ := hy
        rw [Set.mem_singleton_iff.1 hz3] at hy
        obtain ⟨z4, hz4, hy⟩ := hy
        have hS4 := SVK.sv_doIpcTransfer' t (some ep) bd g dest z1.2 z4 hz4
        have hc4 := cfk_doIpcTransfer' t (some ep) bd g dest z1.2 z4 hz4
        have hq4 : QT t z4.2 := qt_of_tv t (fun _ => B8d.tv_doIpcTransfer _ _ _ _ _) z1.2 hq1 z4 hz4
        have hn4 : NF t z4.2 := nf_of_tv t (fun _ => B8d.tv_doIpcTransfer _ _ _ _ _) z1.2 hn1 z4 hz4
        obtain ⟨z5, hz5, hy⟩ := hy
        have hS5 := sv_maybeUnlink dest reply z4.2 z5 hz5
        have hc5' := cfk_maybeUnlink dest reply z4.2 z5 hz5
        have hq5 : QT t z5.2 :=
          (by qt14g_auto : IK (QT t) (NonDet.maybeM (replyUnlinkTcb (Z := Unit) dest) reply)) z4.2 hq4 z5 hz5
        have hn5 : NF t z5.2 := nf_maybeUnlink t dest reply z4.2 hn4 z5 hz5
        have hc5 : z5.2.curThread = t := by rw [cf_curThread (hc5'.trans (hc4.trans hc1)), hct]
        have hL5 : TP (QB t c) z5.2 ∧ KS c z5.2 := bl_svs (bl_svs (bl_svs hb hS1) hS4) hS5
        obtain ⟨z6, hz6, hy⟩ := hy
        unfold getTcbObjRef at hz6
        obtain ⟨x6, -, rfl⟩ := mem_threadGet hz6
        obtain ⟨z7, hz7, hy⟩ := hy
        obtain ⟨xt, hxt, rfl⟩ := mem_threadGet hz7
        dsimp only at hy
        split at hy
        · rename_i hcf
          exfalso
          have h0 : xt.tcbFault = none := hn5 xt hxt
          simp [h0] at hcf
        · obtain ⟨z8, hz8, hy⟩ := hy
          have hq8 : QT t z8.2 :=
            (SInv.ik_when _ (SInv.ik_bind (by qt_auto) fun _ => qt_schedContextDonate t _ _)) z5.2 hq5 z8 hz8
          refine ⟨eb_wakeTail t c dest z8.2 ?_ y hy, qt_wakeTail t dest z8.2 hq8 y hy⟩
          unfold NonDet.when at hz8
          split at hz8
          · obtain ⟨z9, hz9, hz8⟩ := hz8
            unfold getTcbObjRef at hz9
            obtain ⟨x9, -, rfl⟩ := mem_threadGet hz9
            exact eb_donate t c _ dest z5.2 hne hc5 hL5 z8 hz8
          · rw [Set.mem_singleton_iff.1 hz8]; exact Or.inl hL5
      | _ => rw [hst] at hy; obtain ⟨_, h, _⟩ := hy; exact h.elim

set_option maxHeartbeats 4000000 in
/-- **The Endpoint arm** (ct the sender, no fault). -/
theorem perfF_endpoint {σ0 u : State Unit} (ep : ObjRef) (badge : Word) (g gr : Bool) (h : RF σ0 u)
    (hn : NF σ0.curThread u) : PerfF σ0 (.invokeEndpoint ep badge g gr) u := by
  refine perfF_q fun y hy a ha => ?_
  have hy' : y ∈ ((withoutPreemption (do
      let thread ← NonDet.gets fun s : State Unit => s.curThread
      sendIpc (Z := Unit) false false badge g gr true thread ep
      return ([] : List Data))).run u).1 := hy
  unfold withoutPreemption at hy'
  obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hy'
  obtain ⟨g1, hg1, hw⟩ := hw
  obtain rfl := mem_gets hg1
  obtain ⟨w2, hw2, hw⟩ := hw
  have ew : w.2 = w2.2 := by rw [Set.mem_singleton_iff.1 hw]
  dsimp only at hw2
  have et : u.curThread = σ0.curThread := cf_curThread h.tb.cf
  rw [et] at hw2
  have hcf := (cfk_sendIpc' false false badge g gr true σ0.curThread ep u w2 hw2).trans h.tb.cf
  have hcw :=
    (A11b.cp_sendIpc false false badge g gr true σ0.curThread ep σ0 σ0.curSc u ⟨A11.kp_curSc h.kp, h.kp.2.1⟩ w2 hw2).2
  obtain ⟨he, hq⟩ := ep_sendIpcF badge g gr σ0.curThread σ0.curSc ep u et
    (fun p x hx e => by subst e; simp [h.rs x hx, runnable])
    ⟨fun p x hx e => by subst e; exact h.bd x hx, h.sc⟩ h.qt hn w2 hw2
  dsimp only
  rw [ew]
  exact ⟨cf_curThread hcf, hq, rtc_ec h.bs ⟨hcf, hcw, he⟩⟩

def CovE : Fl4Invocation → Prop
  | .invokeEndpoint _ _ _ _ => True
  | _ => False

/-! ## The interface with `NF` -/

/-- rd14g C's `ArmFU` with `NF ct` at the front state. -/
def ArmFV (C : Fl4Invocation → Prop) : Prop :=
  ∀ (σ0 s : State Unit) (u : Unit × State Unit) (h0 : KHeap) (b : Fl4Invocation) (I : ObjRef), C b →
    A10.BS σ0 → Suff σ0 → σ0.curSc ≠ σ0.idleSc → NF σ0.curThread σ0 → KZ σ0 s → SInvB.BindOK (SInvB.bv h0) b →
    SInvB.BR h0 s.kheap → B8f.RB s.curThread I s → B8n.UF s → SInv.IL [s.curThread] s →
    SInvU.GapOKN (SInvU.uV s) b →
    u ∈ (setThreadState (Z := Unit) s.curThread .restart s).1 → PerfF σ0 b u.2

theorem armFV_of {C : Fl4Invocation → Prop} (h : ArmFU C) : ArmFV C :=
  fun σ0 s u h0 b I hc hB hS hi _ hz ho hr hRB hF hL hG hu => h σ0 s u h0 b I hc hB hS hi hz ho hr hRB hF hL hG hu

theorem ArmFV.or {C1 C2 : Fl4Invocation → Prop} (h1 : ArmFV C1) (h2 : ArmFV C2) :
    ArmFV (fun b => C1 b ∨ C2 b) :=
  fun σ0 s u h0 b I hc hB hS hi hN hz ho hr hRB hF hL hG hu =>
    hc.elim (fun c => h1 σ0 s u h0 b I c hB hS hi hN hz ho hr hRB hF hL hG hu)
      (fun c => h2 σ0 s u h0 b I c hB hS hi hN hz ho hr hRB hF hL hG hu)

theorem armFV_covE : ArmFV CovE := by
  intro σ0 s u h0 b I hc hB hS hi hN hz hbo hbr hRB hF hL hG hu
  have hR : RF σ0 u.2 := rf_restart hB hS hz hu
  have et : s.curThread = σ0.curThread := kz_curThread hz
  have hn : NF σ0.curThread u.2 := nf_setThreadState _ _ _ s (nf_kz hz hN) u hu
  cases b
  case invokeEndpoint ep badge g gr => exact perfF_endpoint ep badge g gr hR hn
  all_goals exact (hc : False).elim

theorem nf_front {σ : State Unit} (h : NF σ.curThread σ) {v : Bool × State Unit}
    (hv : v ∈ (A8.front σ).1) (ht : v.1 = true) : NF v.2.curThread v.2 := by
  obtain ⟨w, hw, hv'⟩ := hv
  rw [SInvB.checkBudgetRestart_true_eq hv' ht]
  obtain ⟨ek, -, -, -⟩ := SInvO.uts_off hw
  obtain ⟨et, -⟩ := ci_updateTimeStamp σ.curThread σ.idleThread σ ⟨rfl, rfl⟩ w hw
  rw [et]; intro x hx; rw [ek] at hx; exact h x hx

/-- **`PerfFRc` gives rd14b's `PerfFR`** for any `C` with `ArmFV C`. -/
theorem perfFR_ofKV {C : Fl4Invocation → Prop} (hA : ArmFV C) {σ0 σ : State Unit} {I : ObjRef} (hB : A10.BS σ0)
    (hS : Suff σ0) (hi : σ0.curSc ≠ σ0.idleSc) (hN : NF σ0.curThread σ0) (hz : KZ σ0 σ)
    (hRB : B8f.RB σ.curThread I σ) (hF : B8n.UF σ)
    (hL : SInv.IL [σ.curThread] σ) {cptr : CapRef} (h : PerfFRc C σ0 cptr σ) : PerfFR σ0 cptr σ := by
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
    exact hA σ0 s' u h0 b I hc hB hS hi hN hz2 hok hbr hRB' hF' hL' hG hu
  · exact hP

/-- **`InvFc` gives rd14b's `InvF`** for any `C` with `ArmFV C`. -/
theorem invF_ofKV {C : Fl4Invocation → Prop} (hA : ArmFV C) {c : Syscall} {σ : State Unit} (hEF : A8.EF σ)
    (hi : σ.curSc ≠ σ.idleSc) (h1 : SInvQ.T1 σ) (hEB : SInvQ.EB true σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ)
    (hV : VfhAll σ) (hF : B8n.UF σ) (hL : SInv.IL [σ.curThread] σ) (hN : NF σ.curThread σ) (h : InvFc C c σ) :
    InvF c σ := by
  intro v hv ht r cr hc g hg
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  obtain ⟨ec, ei⟩ := front_ci hEF hv ht
  have hi' : v.2.curSc ≠ v.2.idleSc := by rw [ec, ei]; exact hi
  obtain ⟨hRB, -⟩ := B8j.front_facts hEF h1 hEB hIO hV hv ht
  have hFv := B8v.uf_front hF hv ht
  have hLv := il_front hL hv ht
  have hJ := B8j.js_getCapReg r v.2 ⟨rfl, rfl, hRB⟩ g hg
  have ect : g.2.curThread = v.2.curThread := kz_curThread hJ.1
  exact perfFR_ofKV hA hB hS hi' (nf_front hN hv ht) (kz_getCapReg (V := v.2) r v.2 rfl g hg)
    (by rw [ect]; exact hJ.2.2) (B8v.uf_js hFv hJ) (by rw [ect]; exact il_js hLv hJ) (h v hv ht r cr hc g hg)

/-- The `PerfF` bridge's entry facts with `NF ct`. -/
abbrev QFV (C : Fl4Invocation → Prop) (c : Syscall) (σ : State Unit) : Prop :=
  QFU C c σ ∧ NF σ.curThread σ

theorem brF_kv {C : Fl4Invocation → Prop} (hA : ArmFV C) :
    ∀ (c : Syscall) (σ : State Unit), A8.EF σ → QFV C c σ → InvF c σ :=
  fun _ _ hEF h => invF_ofKV hA hEF h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2.1 h.1.2.2.2.2.2.2.1
    h.1.2.2.2.2.2.2.2 h.2 h.1.1

def CF14g3 (b : Fl4Invocation) : Prop := CF14g2 b ∨ CovE b

theorem armFV_cf14g3 : ArmFV CF14g3 := (armFV_of armFU_cf14g2).or armFV_covE

/-! ## Tops -/

section Tops
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19
open Fl4Proofs.P3.SInvR.B8w

variable {σ : State Unit}

/-- ct (Running / Restart) has no fault (SInvA's `FaultTcbsS`, l4v `fault_tcb_states`). -/
theorem nf_ofW (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread) : NF σ.curThread σ := by
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJ h.sb hct).ctAct
  intro x hx
  rw [hx0] at hx; cases hx
  exact SInv.FaultTcbs.ct h.a.fts.weak hx0 ha0

set_option maxHeartbeats 4000000 in
theorem kcall_rdyOffH {CR CF : Fl4Invocation → Prop} (hA : ArmAKU CR) (hAF : ArmFV CF) (hnd : numDomains = 1)
    (rep : Bool) (ev : Event) (h : SInvW σ) (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hP : ∀ c, ev = .syscallEvent c → A14c.InvRc CR c σ) (hF : ∀ c, ev = .syscallEvent c → InvFc CF c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffW hnd rep ev h hev (brR_ku hA) (brF_kv hAF) (fun c e => qu_ofW h hev c e (hP c e))
    (fun c e => ⟨qfu_ofW h hev c e (hF c e), nf_ofW h (hev (by rw [e]; intro h; cases h))⟩)

set_option maxHeartbeats 4000000 in
theorem kentry_rdyOffH {CR CF : Fl4Invocation → Prop} (hA : ArmAKU CR) (hAF : ArmFV CF) (hnd : numDomains = 1)
    (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, A14c.InvRc CR c w.2 ∧ InvFc CF c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 := by
  refine kentry_rdyOffW hnd c h hct (brR_ku hA) (brF_kv hAF) fun w hw =>
    ⟨qu_fip c h hct w hw (hW w hw).1, qfu_fip c h hct w hw (hW w hw).2, ?_⟩
  have hc : cfS w.2 = cfS σ :=
    (by unfold fl4SyscallFaultIP; cfk_auto : CFK (fl4SyscallFaultIP (Z := Unit) σ.curThread)) σ w hw
  have ect : w.2.curThread = σ.curThread := congrArg (fun p => p.2.2.1) hc
  rw [ect]
  exact (nf_of_tv _ fun _ => by unfold fl4SyscallFaultIP; tv_auto) σ (nf_ofW h hct) w hw

/-- **Today's tops**: no `PerfA` input; `PerfF` asked only outside `CF14g3` (SchedControl configure,
CNode delete / revoke, ThreadControlCaps / ThreadControlSched). -/
theorem kcall_rdyOffG3 (hnd : numDomains = 1) (rep : Bool) (ev : Event) (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (hF : ∀ c, ev = .syscallEvent c → InvFc CF14g3 c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffH armAKU_all armFV_cf14g3 hnd rep ev h hev (fun c _ => invRc_all c σ) hF

theorem kentry_rdyOffG3 (hnd : numDomains = 1) (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, InvFc CF14g3 c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 :=
  kentry_rdyOffH armAKU_all armFV_cf14g3 hnd c h hct fun w hw => ⟨invRc_all c w.2, hW w hw⟩

/-- **The end target's shape over `ArmFV`.** -/
theorem kcall_rdyOff9_ofV (hAF : ArmFV fun _ => True) (hnd : numDomains = 1) (rep : Bool) (ev : Event)
    (h : SInvW σ) (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffH armAKU_all hAF hnd rep ev h hev (fun c _ => invRc_all c σ) (fun c _ => invFc_true c σ)

theorem kentry_rdyOff9_ofV (hAF : ArmFV fun _ => True) (hnd : numDomains = 1) (c : Syscall) (h : SInvW σ)
    (hct : σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 :=
  kentry_rdyOffH armAKU_all hAF hnd c h hct fun w _ => ⟨invRc_all c w.2, invFc_true c w.2⟩

end Tops

end

end Fl4Proofs.P3.SInvR.A14g
