/-
P3 (DESIGN.md §9), invariant line G1 (il2): **IfLiveT across the syscall
entry and every kernel event** (il1 handoff step 4; spec side only).

* Shell invariant `Ju N ct s := IL [ct] s ∧ NQ [ct] s ∧ s.curThread = ct ∧
  P3 N s ∧ NodeIs N s` (the current thread holds a thread cap: it is active,
  so live; NtfnQB ∧ EpQB with ct in no queue; UtInv3 at the IRQ node `N`).
  `ju_of` / `ju_auto`: the il1 IL family, nq1's NQ family, the current-thread
  frame, ut1's view frame `UK` and ut7's node frame `NK`.
* `il_fl4HandleInvocationR`: post `IL []`, and `IL [ct]` after a first-phase
  decode (ReplyRecv / NBSendRecv / NBSendWait's send phase decodes no CNode or
  TCB invocation, so no thread cap is removed and `handle_recv` may block the
  current thread). The decode's facts: ut7's `InvOKN` and `DecodedFrom`, il2's
  `TgI` / `FpI` (SpecInvNtfnQLP).
* `il_handleRecv`, `il_fl4HandleSyscall`, `il_fl4HandleEvent_sys`,
  `il_handleEvent_other`, `il_fl4CallKernel_of` (the preemption path and the
  timer need NtfnQB ∧ EpQB after the handler: nq3's posts on the same run).
* Tops (given `PerfGapIL`, SpecInvNtfnQLP): `kentry_ifLiveT_of`,
  `kcall_ifLiveT_of`.
-/
import Fl4Proofs.P3.SpecInvNtfnQLP
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## The shell invariant -/

def Ju (N : Irq → ObjRef) (ct : ObjRef) (s : State Unit) : Prop :=
  IL [ct] s ∧ NQ [ct] s ∧ s.curThread = ct ∧ P3 N s ∧ NodeIs N s

theorem ju_of {N : Irq → ObjRef} {ct : ObjRef} {ε α : Type} {m : NonDetE (State Unit) ε α}
    (hL : ILKE [ct] m) (hQ : NQKE [ct] m) (hC : CTKE ct m) (hU : ∀ v, UKE v m) (hK : NKE N m) :
    IKE (Ju N ct) m :=
  fun σ h y hy => ⟨hL σ h.1 y hy, hQ σ h.2.1 y hy, hC σ h.2.2.1 y hy,
    p3_of_view (hU _ σ rfl y hy) h.2.2.2.1, hK σ h.2.2.2.2 y hy⟩

theorem ju_ofK {N : Irq → ObjRef} {ct : ObjRef} {α : Type} {m : NonDet (State Unit) α}
    (hL : ILK [ct] m) (hQ : NQK [ct] m) (hC : CTK ct m) (hU : ∀ v, UK v m) (hK : NK N m) :
    IK (Ju N ct) m :=
  fun σ h y hy => ⟨hL σ h.1 y hy, hQ σ h.2.1 y hy, hC σ h.2.2.1 y hy,
    p3_of_view (hU _ σ rfl y hy) h.2.2.2.1, hK σ h.2.2.2.2 y hy⟩

macro "ju_auto" : tactic => `(tactic| first
  | exact ju_of (by il_auto) (by nq_auto) (by ct_auto) (fun _ => by uk_auto) (by nk_auto)
  | exact ju_ofK (by il_auto) (by nq_auto) (by ct_auto) (fun _ => by uk_auto) (by nk_auto))

/-- The post of `handle_invocation`. -/
def JQ (ct : ObjRef) (fp : Bool) (s : State Unit) : Prop := IL [] s ∧ (fp = true → IL [ct] s)

theorem jq_of {N : Irq → ObjRef} {ct : ObjRef} {fp : Bool} {s : State Unit} (h : Ju N ct s) : JQ ct fp s :=
  ⟨il_nil_of h.1, fun _ => h.1⟩

theorem jq_of' {ct : ObjRef} {fp : Bool} {s : State Unit} (h : IL [ct] s) : JQ ct fp s :=
  ⟨il_nil_of h, fun _ => h⟩

theorem ju_sts {N : Irq → ObjRef} {ct : ObjRef} {σ : State Unit} (h : Ju N ct σ) {y : Unit × State Unit}
    (hy : y ∈ (setThreadState (Z := Unit) ct .restart σ).1) : Ju N ct y.2 :=
  ⟨il_setThreadState ct .restart (fun _ => List.mem_singleton_self _) σ h.1 y hy,
    nq_setThreadState ct .restart (List.mem_singleton_self _) (fun h => h) σ h.2.1 y hy,
    (ct_setThreadState (cq := ct) ct .restart) σ h.2.2.1 y hy,
    p3_of_view (uk_setThreadState (v := uV σ) ct .restart σ rfl y hy) h.2.2.2.1,
    (show NK N (setThreadState (Z := Unit) ct .restart) by nk_auto) σ h.2.2.2.2 y hy⟩

/-- The restart targets of a decoded TCB invocation hold the invoked thread cap. -/
theorem hasTC_of_tg {σ : State Unit} {w : UView} (hw : uV σ = w) {sl : CslotPtr} {cap : Cap}
    (hc : w.2.1 sl = some cap) {b : Fl4Invocation} (h : TgI cap b) : ∀ t ∈ invRT b, HasTC σ t := by
  cases b
  case invokeTCB ti =>
    obtain ⟨p, rfl, hp⟩ := h
    intro t ht
    have e : t = p := by cases ti <;> simp_all [invRT, tcbRT, TgT]
    subst e
    exact ⟨sl, by rw [← hw] at hc; exact hc⟩
  all_goals intro t ht; simp [invRT] at ht

/-! ## `handle_invocation` -/

set_option maxHeartbeats 8000000 in
theorem il_fl4HandleInvocationR (hG : PerfGapIL) (N : Irq → ObjRef) (ct : ObjRef) (rep calling blocking don fp : Bool)
    (cptr : CapRef) :
    HKE (Ju N ct) (JQ ct fp) (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine hke_gets_bind fun σ hσ => ?_
  have hc : σ.curThread = ct := hσ.2.2.1
  simp only [hc, withoutPreemption]
  refine hke_bind (R := Ju N ct) (Q := JQ ct fp) (hk_liftE (hk_of_ik ?_)) (fun info => ?_) (fun s h => jq_of h) σ hσ
  · ju_auto
  intro σ' hσ' y0 hy0
  have hF : ∀ v, UKE v (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) ct cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false ct
       let extracaps ← lookupExtraCaps ct buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := fun _ => by uk_auto
  have hOk : OkV (uV σ') (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (uV σ').2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (uV σ').2.1 p.2 = some p.1 ∧ DestRefV (uV σ') p.2) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) ct cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false ct
       let extracaps ← lookupExtraCaps ct buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _))
      (okv_capFaultOnFailure _ _ (okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine okv_bind_uk (fun _ => ike_liftE (uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine okv_bind (fun _ => uk_lookupExtraCaps _ _ _) (okv_lookupExtraCapsN _ _ _) fun ex hex => okv_returnOk ?_
    exact ⟨hx, hex⟩
  refine ft_syscall_post (I := Ju N ct) (Q := JQ ct fp) ?_ ?_ ?_ ?_ ?_ y0 hy0
  · refine (?_ : IKE (Ju N ct) _) σ' hσ'
    ju_auto
  · intro f s hs v hv
    unfold NonDet.when at hv
    split at hv
    · exact jq_of' (il_handleFault ct f (List.mem_singleton_self _) s hs.1 v hv)
    · rw [Set.mem_singleton_iff.1 hv]; exact jq_of hs
  · intro a s has w hw
    have hs : Ju N ct s := by
      refine (?_ : IKE (Ju N ct) _) σ' hσ' _ has
      ju_auto
    obtain ⟨sl, cap, ex, buf⟩ := a
    refine (?_ : IKE (Ju N ct) _) s hs w hw
    ju_auto
  · intro e s hs v hv
    refine jq_of' ((?_ : ILK [ct] _) s hs.1 v hv)
    il_auto
  · intro a s b s' has hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hvs : uV s = uV σ' := hF _ σ' rfl _ has
    obtain ⟨hcap, hex⟩ := hOk σ' rfl _ s has
    obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hbs
    swap
    · simp at he
    obtain ⟨x0, hx0, e0⟩ := mem_liftE' hz0
    subst e0
    simp only [Except.ok.injEq] at ha0
    subst ha0
    have hvx : uV x0.2 = uV σ' := (uk_getMrs (uvw := uV s) _ _ _ s rfl x0 hx0).trans hvs
    have hdec : InvOKN (uV σ') b :=
      okv_fl4DecodeN fp info.miLabel x0.1 cptr sl cap ex buf hcap hex x0.2 hvx b s' hb0
    have hDF : DecodedFrom (uV σ') b :=
      ⟨fp, info.miLabel, x0.1, cptr, sl, cap, ex, buf, x0.2, s', hvx, hcap, hex, hb0⟩
    have htg : TgI cap b := okv_tgI fp info.miLabel x0.1 cptr sl cap ex buf x0.2 hvx b s' hb0
    have hfp : fp = true → NoDelI b := okv_fpI fp info.miLabel x0.1 cptr sl cap ex buf x0.2 hvx b s' hb0
    have hv' : uV s' = uV σ' := by
      have hd : ∀ v, UKE v (fl4DecodeInvocation (Z := Unit) fp info.miLabel x0.1 cptr sl cap ex buf) :=
        fun _ => by uk_auto
      exact (hd _ x0.2 rfl _ hb0).trans hvx
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      have hJ1 : Ju N ct w.2 := ju_sts hI hw
      have hv1 : uV w.2 = uV σ' := (uk_setThreadState (v := uV s') ct .restart s' rfl w hw).trans hv'
      obtain ⟨r, s1⟩ := w
      dsimp only at hJ1 hv1
      have hok1 : InvOKN (uV s1) b := by rw [hv1]; exact hdec
      have hDF1 : DecodedFrom (uV s1) b := by rw [hv1]; exact hDF
      have hT1 : ∀ t ∈ invRT b, HasTC s1 t := hasTC_of_tg hv1 hcap htg
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := il_fl4PerformInvocation hG N blocking calling don fp b s1 [ct]
          ⟨⟨hJ1.1, nq_weak_nil _ hJ1.2.1⟩, hJ1.2.2.2.1⟩ hJ1.2.2.2.2 (by rw [hJ1.2.2.1]; simp) hT1 hfp hok1 hDF1 _ hz2
        refine ⟨(?_ : ILKE [] _) s2 hs2.1 y hy, fun hf => (?_ : ILKE [ct] _) s2 (hs2.2 hf) y hy⟩ <;> il2_auto
      · exact il_fl4PerformInvocation hG N blocking calling don fp b s1 [ct]
          ⟨⟨hJ1.1, nq_weak_nil _ hJ1.2.1⟩, hJ1.2.2.2.1⟩ hJ1.2.2.2.2 (by rw [hJ1.2.2.1]; simp) hT1 hfp hok1 hDF1 _ hz2
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      exact jq_of (ju_sts hI hw)

/-! ## `handle_recv` -/

set_option maxHeartbeats 8000000 in
theorem il_handleRecv (ct : ObjRef) (blk canReply : Bool) :
    HK (fun s => IL [ct] s ∧ s.curThread = ct) (IL []) (handleRecv (Z := Unit) blk canReply) := by
  have hct : ct ∈ [ct] := List.mem_singleton_self _
  have hRIP : ∀ c rc, HK (IL [ct]) (IL []) (receiveIpc (Z := Unit) ct c blk rc) :=
    fun c rc s hs z hz => il_nil_of (il_receiveIpc ct c blk rc hct s hs z hz)
  have hRS : ∀ c, HK (IL [ct]) (IL []) (receiveSignal (Z := Unit) ct c blk) :=
    fun c s hs z hz => il_nil_of (il_receiveSignal ct c blk hct s hs z hz)
  unfold handleRecv
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  have hc : σ.curThread = ct := hσ.2
  (try dsimp only at hy)
  rw [hc] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : IL [ct] y2.2 := (?_ : ILK [ct] _) σ hσ.1 y2 h2
  · refine hk_catch (I := IL [ct]) (Q0 := IL []) ?_ (fun e => ?_) y2.2 hb2 y hy
    · (try dsimp only)
      refine hkr_bind (by il_auto) (fun epCap => ?_)
      (try dsimp only)
      split
      · (try dsimp only)
        split
        · (try dsimp only)
          split
          · refine hkr_bind (by il_auto) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
          · refine hkr_bind (by il_auto) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
        · exact hkr_throw _
      · (try dsimp only)
        split
        · refine hkr_bind (by il_auto) (fun bt => ?_)
          (try dsimp only)
          split
          · exact hkr_liftE (hRS _)
          · exact hkr_throw _
        · exact hkr_throw _
      · exact hkr_throw _
    · exact hk_post (il_handleFault ct e hct) fun _ h => il_nil_of h
  · il_auto

/-! ## `handle_syscall` and the events -/

theorem il_handleYield : ILK [] (handleYield (Z := Unit)) := by
  unfold handleYield; il_auto

set_option maxHeartbeats 8000000 in
theorem il_fl4HandleSyscall (hG : PerfGapIL) (N : Irq → ObjRef) (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKE (Ju N ct) (IL []) (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv : ∀ (cl bl dn fp : Bool) (cptr : CapRef), HKE (Ju N ct) (IL []) (fl4HandleInvocationR (Z := Unit) rep cl bl dn fp cptr) :=
    fun cl bl dn fp cptr => hk_post (il_fl4HandleInvocationR hG N ct rep cl bl dn fp cptr) fun _ h => h.1
  have hInvNB : ∀ (cl bl dn : Bool) (cptr : CapRef), HKE (Ju N ct) (fun s => IL [ct] s ∧ s.curThread = ct)
      (fl4HandleInvocationR (Z := Unit) rep cl bl dn true cptr) :=
    fun cl bl dn cptr σ hσ y hy => ⟨(il_fl4HandleInvocationR hG N ct rep cl bl dn true cptr σ hσ y hy).2 rfl,
      ct_fl4HandleInvocationR (cq := ct) rep cl bl dn true cptr σ hσ.2.2.1 y hy⟩
  have hRecv : ∀ b r, HKE (fun s => IL [ct] s ∧ s.curThread = ct) (IL []) (withoutPreemption (Z := Unit) (handleRecv b r)) :=
    fun b r => hk_liftE (il_handleRecv ct b r)
  have hSR : ∀ (reg : Register) (cl bl dn : Bool) (b r : Bool), HKE (Ju N ct) (IL []) (do
      let cptr ← withoutPreemption (Z := Unit) (getCapReg reg)
      fl4HandleInvocationR rep cl bl dn true cptr
      withoutPreemption (handleRecv b r)) := by
    intro reg cl bl dn b r
    refine hke_bind (R := Ju N ct) (hk_liftE (hk_of_ik (by ju_auto))) (fun cptr => ?_) (fun s h => il_nil_of h.1)
    exact hke_bind (hInvNB _ _ _ cptr) (fun _ => hRecv b r) (fun s h => il_nil_of h.1)
  cases c
  case sysSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := Ju N ct) (hk_liftE (hk_of_ik (by ju_auto))) (fun cptr => hInv _ _ _ _ cptr) (fun s h => il_nil_of h.1)
  case sysNBSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := Ju N ct) (hk_liftE (hk_of_ik (by ju_auto))) (fun cptr => hInv _ _ _ _ cptr) (fun s h => il_nil_of h.1)
  case sysCall =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := Ju N ct) (hk_liftE (hk_of_ik (by ju_auto))) (fun cptr => hInv _ _ _ _ cptr) (fun s h => il_nil_of h.1)
  case sysYield =>
    simp only [fl4HandleSyscall]
    exact hk_liftE (fun s h y hy => il_handleYield s (il_nil_of h.1) y hy)
  case sysReplyRecv => exact hSR _ _ _ _ _ _
  case sysNBSendRecv => exact hSR _ _ _ _ _ _
  case sysNBSendWait => exact hSR _ _ _ _ _ _
  all_goals
    simp only [fl4HandleSyscall]
    exact hk_pre (hRecv _ _) fun s h => ⟨h.1, h.2.2.1⟩

theorem il_fl4HandleEvent_sys (hG : PerfGapIL) (N : Irq → ObjRef) (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKE (Ju N ct) (IL []) (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) := by
  simp only [fl4HandleEvent]
  refine hke_bind (R := Ju N ct) (hk_liftE (hk_of_ik (by ju_auto))) (fun _ => ?_) (fun s h => il_nil_of h.1)
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at ha; subst ha
    have hbw : IL [] w.2 := il_nil_of (il_checkBudgetRestart σ hσ.1 w hw)
    unfold NonDetE.whenE at hy
    split at hy
    · rename_i hr
      rw [checkBudgetRestart_true hw hr] at hy
      exact il_fl4HandleSyscall hG N ct rep c σ hσ y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact hbw
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

set_option maxHeartbeats 8000000 in
/-- The interrupt event (the current thread may be idle: `K = []`). -/
theorem il_handleEvent_int : HKE (ILN []) (IL []) (handleEvent (Z := Unit) .interrupt) := by
  simp only [handleEvent, withoutPreemption]
  refine hk_liftE ?_
  intro σ hσ y hy
  refine ((?_ : IK (ILN []) _) σ hσ y hy).1
  exact ik_bind (iln_ik (by il_auto) (by nq_auto)) fun _ =>
    ik_bind (iln_ik il_checkBudget (fun s h z hz => nq_checkBudget s h z hz)) fun _ =>
      iln_maybeHandleInterrupt false

/-- Every event other than a syscall or an interrupt, from a current thread `ct` holding a thread cap. -/
theorem il_handleEvent_other (ct : ObjRef) (ev : Event) (hev : ∀ c, ev ≠ .syscallEvent c)
    (hi : ev ≠ .interrupt) :
    HKE (fun s => ILN [ct] s ∧ s.curThread = ct) (IL []) (handleEvent (Z := Unit) ev) := by
  have hct : ct ∈ [ct] := List.mem_singleton_self _
  have hF : ∀ (m : SMonad Unit Unit) (hm : ILK [ct] m) (hc : CTK ct m) (F : ObjRef → SMonad Unit Unit)
      (hF : ∀ s, IL [ct] s → ∀ z ∈ (F ct s).1, IL [] z.2),
      HK (fun s => ILN [ct] s ∧ s.curThread = ct) (IL []) (do
        m
        let restart ← checkBudgetRestart (Z := Unit)
        NonDet.when restart <| do
          let thread ← NonDet.gets fun s : State Unit => s.curThread
          F thread) := by
    intro m hm hc F hF σ hσ y ⟨y1, h1, hy⟩
    have hb1 : IL [ct] y1.2 := hm σ hσ.1.1 y1 h1
    have hc1 : y1.2.curThread = ct := hc σ hσ.2 y1 h1
    obtain ⟨y2, h2, hy⟩ := hy
    have hb2 : IL [ct] y2.2 := il_checkBudgetRestart y1.2 hb1 y2 h2
    (try dsimp only at hy)
    unfold NonDet.when at hy
    split at hy
    · rename_i hr
      have e2 : y2.2 = y1.2 := checkBudgetRestart_true h2 hr
      obtain ⟨y3, h3, hy⟩ := hy
      rw [mem_gets h3] at hy
      (try dsimp only at hy)
      rw [e2, hc1] at hy
      exact hF _ hb1 y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact il_nil_of hb2
  have hHF : ∀ f, ∀ s, IL [ct] s → ∀ z ∈ (handleFault (Z := Unit) ct f s).1, IL [] z.2 :=
    fun f s hs z hz => il_nil_of (il_handleFault ct f hct s hs z hz)
  cases ev with
  | syscallEvent c => exact absurd rfl (hev c)
  | interrupt => exact absurd rfl hi
  | unknownSyscall n =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (hF _ (by il_auto) (by ct_auto) _ (hHF _))
  | userLevelFault w1 w2 =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (hF _ (by il_auto) (by ct_auto) _ (hHF _))
  | vmFaultEvent ft =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (hF _ (by il_auto) (by ct_auto) _ ?_)
    intro s hs z hz
    exact hk_catch (I := IL [ct]) (Q0 := IL []) (hkr_of_ike (by il_auto) fun _ h => il_nil_of h) (fun e => hHF e) s hs z hz
  | hypervisorEvent ht =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (hF _ (by il_auto) (by ct_auto) _ ?_)
    intro s hs z hz
    refine il_nil_of ((?_ : ILK [ct] _) s hs z hz)
    il2_auto

/-- `preemption_path` (it handles the pending interrupt: NtfnQB ∧ EpQB needed). -/
theorem iln_preemptionPath : IK (ILN []) (preemptionPath (Z := Unit)) :=
  fun σ h y hy => ⟨(show HK (ILN []) (IL []) (preemptionPath (Z := Unit)) by
    unfold preemptionPath
    have htail : HK (ILN []) (IL []) (maybeHandleInterrupt (Z := Unit) true) :=
      fun s hs z hz => (iln_maybeHandleInterrupt true s hs z hz).1
    refine hk_bind (hk_of_ik (iln_ik (by il_auto) (by nq_auto))) fun ct => ?_
    refine hk_bind (hk_of_ik (iln_ik (by il_auto) (by nq_auto))) fun sched => ?_
    cases sched
    · refine hk_bind (hk_of_ik (iln_ik (by il_auto) (by nq_auto))) fun csc => ?_
      refine hk_bind (hk_of_ik (iln_ik (by il_auto) (by nq_auto))) fun active => ?_
      cases active
      · refine hk_bind (hk_of_ik (iln_ik (by il_auto) (by nq_auto))) fun _ => ?_
        first | exact htail | exact hk_pure_bind htail
      · refine hk_bind (hk_of_ik (iln_ik (by il_auto) (by nq_auto))) fun _ => ?_
        refine hk_bind (hk_of_ik (iln_ik (il_chargeBudget _ _) (fun s h z hz =>
          nq_chargeBudget _ _ s h z hz))) fun _ => ?_
        first | exact htail | exact hk_pure_bind htail
    · refine hk_bind (hk_of_ik (iln_ik il_checkBudget (fun s h z hz => nq_checkBudget s h z hz))) fun _ => ?_
      first | exact htail | exact hk_pure_bind htail) σ h y hy, nq_preemptionPath σ h.2 y hy⟩

/-- `fl4CallKernel` from a handler result that is `IL []` (and, by nq3, `NQ []`) on both outcomes. -/
theorem il_fl4CallKernel_of {rep : Bool} {ev : Event} {P : State Unit → Prop}
    (h : HKE P (IL []) (fl4HandleEvent (Z := Unit) rep ev)) (hN : HKE P (NQ []) (fl4HandleEvent (Z := Unit) rep ev)) :
    HK P (IL []) (fl4CallKernel (Z := Unit) rep ev) := by
  intro σ hσ y hy
  unfold fl4CallKernel at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 : ILN [] y1.2 := by
    unfold NonDetE.handleE at h1
    obtain ⟨z, hz, h1⟩ := h1
    have hz' : ILN [] z.2 := ⟨h σ hσ z hz, hN σ hσ z hz⟩
    obtain ⟨r, s⟩ := z
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 h1]; exact hz'
    | error e =>
      obtain ⟨w, hw, rfl⟩ := ft_mem_liftE (m := preemptionPath (Z := Unit)) h1
      exact iln_preemptionPath s hz' w hw
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 := iln_fl4Awaken y1.2 hb1 y2 h2
  refine (?_ : ILK [] _) y2.2 hb2.1 y hy
  il_auto

/-! ## The tops (given `PerfGapIL`) -/

theorem live_of_active {s : ThreadState} (h : activeSt s) : liveSt s := by
  revert h; cases s <;> simp [activeSt, liveSt]

/-- **IfLiveT kept by the syscall entry** (given `PerfGapIL`), from an active
current thread (l4v `ct_active`: a TCB in an active state), NtfnQB ∧ EpQB and
UtInv3. -/
theorem kentry_ifLiveT_of (hG : PerfGapIL) (rep : Bool) (c : Syscall) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState)
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, IfLiveT y.2 := by
  obtain ⟨x0, hx0, ha0⟩ := ha
  intro y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hNQ : NQ [σ.curThread] σ := nq_cons ((nq_nil_iff σ).2 hN) fun x hx => by
    rw [hx0] at hx; cases hx; exact ok_of_active ha0
  have hJ : Ju σ.interruptIrqNode σ.curThread σ :=
    ⟨il_consT ((il_nil_iff σ).2 h) (h _ x0 hx0 (live_of_active ha0)), hNQ, rfl, hU, rfl⟩
  have hI : Iu σ.curThread σ :=
    ⟨hNQ, rfl, hU.1.1.1, nqDet_of_live hU.1 (ifLiveB_of h)⟩
  have hJ2 : Ju σ.interruptIrqNode σ.curThread y2.2 ∧ Iu σ.curThread y2.2 := by
    refine ⟨(?_ : IK (Ju σ.interruptIrqNode σ.curThread) _) σ hJ y2 h2, (?_ : IK (Iu σ.curThread) _) σ hI y2 h2⟩
    · ju_auto
    · iu_auto
  exact (il_fl4CallKernel_of (P := fun s => Ju σ.interruptIrqNode σ.curThread s ∧ Iu σ.curThread s)
    (hk_pre (il_fl4HandleEvent_sys hG _ σ.curThread rep c) fun _ h => h.1)
    (hk_pre (nq_fl4HandleEvent_sys σ.curThread rep c) fun _ h => h.2) y2.2 hJ2 y hy).1

/-- **IfLiveT kept by every kernel event** (given `PerfGapIL`): the current
thread a TCB, active (or, for an interrupt, idle). -/
theorem kcall_ifLiveT_of (hG : PerfGapIL) (rep : Bool) (ev : Event) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, IfLiveT y.2 := by
  obtain ⟨x0, hx0, ha0⟩ := ha
  have hNQ : NQ [σ.curThread] σ := by
    refine nq_cons ((nq_nil_iff σ).2 hN) fun x hx => ?_
    rw [hx0] at hx; cases hx
    rcases ha0 with h1 | ⟨-, h1⟩
    · exact ok_of_active h1
    · rw [h1]; exact ⟨fun h => h, rfl⟩
  have hI : Iu σ.curThread σ := ⟨hNQ, rfl, hU.1.1.1, nqDet_of_live hU.1 (ifLiveB_of h)⟩
  intro y hy
  by_cases hint : ev = .interrupt
  · subst hint
    exact (il_fl4CallKernel_of (P := fun s => ILN [] s ∧ NQ [σ.curThread] s ∧ s.curThread = σ.curThread)
      (hk_pre (by simp only [fl4HandleEvent]; exact il_handleEvent_int) fun _ h => h.1)
      (hk_pre (nq_fl4HandleEvent_other σ.curThread rep .interrupt fun c e => by cases e) fun _ h => h.2)
      σ ⟨⟨(il_nil_iff σ).2 h, nq_weak_nil _ hNQ⟩, hNQ, rfl⟩ y hy).1
  have hact : activeSt x0.tcbState := by
    rcases ha0 with h1 | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hint
  have hL : IL [σ.curThread] σ := il_consT ((il_nil_iff σ).2 h) (h _ x0 hx0 (live_of_active hact))
  by_cases hs : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := hs
    exact (il_fl4CallKernel_of (P := fun s => Ju σ.interruptIrqNode σ.curThread s ∧ Iu σ.curThread s)
      (hk_pre (il_fl4HandleEvent_sys hG _ σ.curThread rep c) fun _ h => h.1)
      (hk_pre (nq_fl4HandleEvent_sys σ.curThread rep c) fun _ h => h.2) σ ⟨⟨hL, hNQ, rfl, hU, rfl⟩, hI⟩ y hy).1
  · have hev : ∀ c, ev ≠ .syscallEvent c := fun c e => hs ⟨c, e⟩
    have hE : HKE (fun s => ILN [σ.curThread] s ∧ s.curThread = σ.curThread) (IL []) (fl4HandleEvent (Z := Unit) rep ev) := by
      rw [fl4HandleEvent_other rep ev hev]; exact il_handleEvent_other σ.curThread ev hev hint
    exact (il_fl4CallKernel_of (P := fun s => ILN [σ.curThread] s ∧ NQ [σ.curThread] s ∧ s.curThread = σ.curThread)
      (hk_pre hE fun _ h => ⟨h.1, h.2.2⟩)
      (hk_pre (nq_fl4HandleEvent_other σ.curThread rep ev hev) fun _ h => h.2)
      σ ⟨⟨hL, nq_weak_nil _ hNQ⟩, hNQ, rfl⟩ y hy).1

end

end Fl4Proofs.P3.SInv
