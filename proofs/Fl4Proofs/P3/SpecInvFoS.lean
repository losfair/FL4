/-
P3 (DESIGN.md §9), invariant line G1 (fo1): **`FT` across the syscall entry
and every kernel event** (spec side only): il2's SpecInvNtfnQLS with the owner.

* `JF N ct s := Ju N ct s ∧ FT s` (il2's shell invariant with `FT`); `juf_of`:
  a step keeping `Ju` (il2's `ju_auto`), `IL (L ++ [ct])` for every `L` (il1's
  family) and the owner with its TCB-ness (`OIK`) keeps `JF`. Post of the
  invocation shell `JQF ct fp s := ILF [] s ∧ (fp → ILF [ct] s)`.
* `il_handleRecvK` (il2's `il_handleRecv` at any `K ∋ ct`), `fo_handleRecv`,
  **`fo_fl4HandleInvocationR`** (SpecInvFoP's `fo_fl4PerformInvocation`),
  `fo_fl4HandleSyscall`, `fo_fl4HandleEvent_sys`, `fo_handleEvent_int`,
  `fo_handleEvent_other`, `ilnK_preemptionPath`, `fo_preemptionPath`,
  **`fo_fl4CallKernel_of`** (`schedule`: SpecInvFoA's `fo_schedule`).
* Tops: **`kentry_fpuOwn`**, **`kcall_fpuOwn`** (`IfLiveT ∧ FT`, hence
  ScArchF's FpuOwnOK, `fpuOwnOK_of_ft`).
-/
import Fl4Proofs.P3.SpecInvFoP
import Fl4Proofs.P3.SpecInvNtfnQLX
open Classical

namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## The shell invariant -/

def JF (N : Irq → ObjRef) (ct : ObjRef) (s : State Unit) : Prop := Ju N ct s ∧ FT s

def JQF (ct : ObjRef) (fp : Bool) (s : State Unit) : Prop := ILF [] s ∧ (fp = true → ILF [ct] s)

theorem jf_ilf {N : Irq → ObjRef} {ct : ObjRef} {s : State Unit} (h : JF N ct s) : ILF [ct] s := ⟨h.1.1, h.2⟩

theorem jqf_of {N : Irq → ObjRef} {ct : ObjRef} {fp : Bool} {s : State Unit} (h : JF N ct s) : JQF ct fp s :=
  ⟨ilf_nil (jf_ilf h), fun _ => jf_ilf h⟩

theorem jqf_of' {ct : ObjRef} {fp : Bool} {s : State Unit} (h : ILF [ct] s) : JQF ct fp s :=
  ⟨ilf_nil h, fun _ => h⟩

theorem juf_of {N : Irq → ObjRef} {ct : ObjRef} {ε α : Type} {m : NonDetE (State Unit) ε α}
    (hJ : IKE (Ju N ct) m) (hL : ∀ L, ILKE (L ++ [ct]) m) (hO : ∀ q, OIKE q m) : IKE (JF N ct) m :=
  fun σ h y hy => ⟨hJ σ h.1 y hy, (fo_ik hL hO σ (jf_ilf h) y hy).2⟩

theorem jufK_of {N : Irq → ObjRef} {ct : ObjRef} {α : Type} {m : NonDet (State Unit) α}
    (hJ : IK (Ju N ct) m) (hL : ∀ L, ILK (L ++ [ct]) m) (hO : ∀ q, OIK q m) : IK (JF N ct) m :=
  fun σ h y hy => ⟨hJ σ h.1 y hy, (fo_ik hL hO σ (jf_ilf h) y hy).2⟩

macro "juf_auto" : tactic => `(tactic| first
  | exact juf_of (by ju_auto) (fun _ => by il_auto) (fun _ => by oi_auto)
  | exact jufK_of (by ju_auto) (fun _ => by il_auto) (fun _ => by oi_auto))

theorem juf_sts {N : Irq → ObjRef} {ct : ObjRef} {σ : State Unit} (h : JF N ct σ) {y : Unit × State Unit}
    (hy : y ∈ (setThreadState (Z := Unit) ct .restart σ).1) : JF N ct y.2 :=
  ⟨ju_sts h.1 hy, (fo_ik (fun _ => il_setThreadState ct .restart (fun _ => by simp))
    (fun _ => oi_setThreadState _ _) σ (jf_ilf h) y hy).2⟩

theorem fo_handleFault (t : ObjRef) (f : Fault) {K : List ObjRef} (ht : t ∈ K) :
    IK (ILF K) (handleFault (Z := Unit) t f) :=
  fo_ik (fun _ => il_handleFault t f (List.mem_append_right _ ht)) (fun _ => oi_handleFault _ _)

/-! ## `handle_invocation` -/

set_option maxHeartbeats 8000000 in
theorem fo_fl4HandleInvocationR (N : Irq → ObjRef) (ct : ObjRef) (rep calling blocking don fp : Bool)
    (cptr : CapRef) :
    HKE (JF N ct) (JQF ct fp) (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine hke_gets_bind fun σ hσ => ?_
  have hc : σ.curThread = ct := hσ.1.2.2.1
  simp only [hc, withoutPreemption]
  refine hke_bind (R := JF N ct) (Q := JQF ct fp) (hk_liftE (hk_of_ik ?_)) (fun info => ?_) (fun s h => jqf_of h) σ hσ
  · juf_auto
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
  refine ft_syscall_post (I := JF N ct) (Q := JQF ct fp) ?_ ?_ ?_ ?_ ?_ y0 hy0
  · refine (?_ : IKE (JF N ct) _) σ' hσ'
    juf_auto
  · intro f s hs v hv
    unfold NonDet.when at hv
    split at hv
    · exact jqf_of' (fo_handleFault ct f (List.mem_singleton_self _) s (jf_ilf hs) v hv)
    · rw [Set.mem_singleton_iff.1 hv]; exact jqf_of hs
  · intro a s has w hw
    have hs : JF N ct s := by
      refine (?_ : IKE (JF N ct) _) σ' hσ' _ has
      juf_auto
    obtain ⟨sl, cap, ex, buf⟩ := a
    refine (?_ : IKE (JF N ct) _) s hs w hw
    juf_auto
  · intro e s hs v hv
    refine jqf_of' ((?_ : IK (ILF [ct]) _) s (jf_ilf hs) v hv)
    exact fo_ik (fun _ => by il_auto) (fun _ => by oi_auto)
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
      have hJ1 : JF N ct w.2 := juf_sts hI hw
      have hv1 : uV w.2 = uV σ' := (uk_setThreadState (v := uV s') ct .restart s' rfl w hw).trans hv'
      obtain ⟨r, s1⟩ := w
      dsimp only at hJ1 hv1
      have hok1 : InvOKN (uV s1) b := by rw [hv1]; exact hdec
      have hDF1 : DecodedFrom (uV s1) b := by rw [hv1]; exact hDF
      have hT1 : ∀ t ∈ invRT b, HasTC s1 t := hasTC_of_tg hv1 hcap htg
      have hP : FP N [ct] s1 := ⟨⟨⟨hJ1.1.1, nq_weak_nil _ hJ1.1.2.1⟩, hJ1.2⟩, hJ1.1.2.2.2.1⟩
      have hct1 : s1.curThread ∈ [ct] := by rw [hJ1.1.2.2.1]; simp
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := fo_fl4PerformInvocation N blocking calling don fp b s1 [ct] hP hct1 hT1 hfp hok1 hDF1 _ hz2
        refine ⟨(?_ : IKE (ILF []) _) s2 hs2.1 y hy, fun hf => (?_ : IKE (ILF [ct]) _) s2 (hs2.2 hf) y hy⟩ <;>
          exact fo_ik (fun _ => by il2_auto) (fun _ => by oi_auto)
      · exact fo_fl4PerformInvocation N blocking calling don fp b s1 [ct] hP hct1 hT1 hfp hok1 hDF1 _ hz2
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      exact jqf_of (juf_sts hI hw)

/-! ## `handle_recv` -/

set_option maxHeartbeats 8000000 in
/-- il2's `il_handleRecv` at any `K` holding the current thread. -/
theorem il_handleRecvK (ct : ObjRef) (K : List ObjRef) (hct : ct ∈ K) (blk canReply : Bool) :
    HK (fun s => IL K s ∧ s.curThread = ct) (IL K) (handleRecv (Z := Unit) blk canReply) := by
  have hRIP : ∀ c rc, HK (IL K) (IL K) (receiveIpc (Z := Unit) ct c blk rc) :=
    fun c rc s hs z hz => il_receiveIpc ct c blk rc hct s hs z hz
  have hRS : ∀ c, HK (IL K) (IL K) (receiveSignal (Z := Unit) ct c blk) :=
    fun c s hs z hz => il_receiveSignal ct c blk hct s hs z hz
  unfold handleRecv
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  have hc : σ.curThread = ct := hσ.2
  (try dsimp only at hy)
  rw [hc] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : IL K y2.2 := (?_ : ILK K _) σ hσ.1 y2 h2
  · refine hk_catch (I := IL K) (Q0 := IL K) ?_ (fun e => ?_) y2.2 hb2 y hy
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
    · exact il_handleFault ct e hct
  · il_auto

theorem fo_handleRecv (ct : ObjRef) (blk canReply : Bool) :
    HK (fun s => ILF [ct] s ∧ s.curThread = ct) (ILF []) (handleRecv (Z := Unit) blk canReply) :=
  fun σ ⟨h, hc⟩ y hy => ilf_nil (ft_back (il_handleRecvK ct (oL σ ++ [ct]) (by simp) blk canReply σ
    ⟨il_oL h.1 h.2, hc⟩ y hy) (oi_handleRecv _ _ σ ⟨rfl, fun t ht => (h.2 t ht).1⟩ y hy))

/-! ## `handle_syscall` and the events -/

theorem ilK_handleYield {K : List ObjRef} : ILK K (handleYield (Z := Unit)) := by
  unfold handleYield; il_auto

set_option maxHeartbeats 8000000 in
theorem fo_fl4HandleSyscall (N : Irq → ObjRef) (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKE (JF N ct) (ILF []) (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv : ∀ (cl bl dn fp : Bool) (cptr : CapRef), HKE (JF N ct) (ILF []) (fl4HandleInvocationR (Z := Unit) rep cl bl dn fp cptr) :=
    fun cl bl dn fp cptr => hk_post (fo_fl4HandleInvocationR N ct rep cl bl dn fp cptr) fun _ h => h.1
  have hInvNB : ∀ (cl bl dn : Bool) (cptr : CapRef), HKE (JF N ct) (fun s => ILF [ct] s ∧ s.curThread = ct)
      (fl4HandleInvocationR (Z := Unit) rep cl bl dn true cptr) :=
    fun cl bl dn cptr σ hσ y hy => ⟨(fo_fl4HandleInvocationR N ct rep cl bl dn true cptr σ hσ y hy).2 rfl,
      ct_fl4HandleInvocationR (cq := ct) rep cl bl dn true cptr σ hσ.1.2.2.1 y hy⟩
  have hRecv : ∀ b r, HKE (fun s => ILF [ct] s ∧ s.curThread = ct) (ILF []) (withoutPreemption (Z := Unit) (handleRecv b r)) :=
    fun b r => hk_liftE (fo_handleRecv ct b r)
  have hSR : ∀ (reg : Register) (cl bl dn : Bool) (b r : Bool), HKE (JF N ct) (ILF []) (do
      let cptr ← withoutPreemption (Z := Unit) (getCapReg reg)
      fl4HandleInvocationR rep cl bl dn true cptr
      withoutPreemption (handleRecv b r)) := by
    intro reg cl bl dn b r
    refine hke_bind (R := JF N ct) (hk_liftE (hk_of_ik (by juf_auto))) (fun cptr => ?_) (fun s h => ilf_nil (jf_ilf h))
    exact hke_bind (hInvNB _ _ _ cptr) (fun _ => hRecv b r) (fun s h => ilf_nil h.1)
  cases c
  case sysSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := JF N ct) (hk_liftE (hk_of_ik (by juf_auto))) (fun cptr => hInv _ _ _ _ cptr) (fun s h => ilf_nil (jf_ilf h))
  case sysNBSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := JF N ct) (hk_liftE (hk_of_ik (by juf_auto))) (fun cptr => hInv _ _ _ _ cptr) (fun s h => ilf_nil (jf_ilf h))
  case sysCall =>
    simp only [fl4HandleSyscall]
    exact hke_bind (R := JF N ct) (hk_liftE (hk_of_ik (by juf_auto))) (fun cptr => hInv _ _ _ _ cptr) (fun s h => ilf_nil (jf_ilf h))
  case sysYield =>
    simp only [fl4HandleSyscall]
    exact hk_liftE (fun s h y hy => fo_ik (fun _ => ilK_handleYield) (fun _ => oi_handleYield) s (ilf_nil (jf_ilf h)) y hy)
  case sysReplyRecv => exact hSR _ _ _ _ _ _
  case sysNBSendRecv => exact hSR _ _ _ _ _ _
  case sysNBSendWait => exact hSR _ _ _ _ _ _
  all_goals
    simp only [fl4HandleSyscall]
    exact hk_pre (hRecv _ _) fun s h => ⟨jf_ilf h, h.1.2.2.1⟩

theorem fo_fl4HandleEvent_sys (N : Irq → ObjRef) (ct : ObjRef) (rep : Bool) (c : Syscall) :
    HKE (JF N ct) (ILF []) (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) := by
  simp only [fl4HandleEvent]
  refine hke_bind (R := JF N ct) (hk_liftE (hk_of_ik (by juf_auto))) (fun _ => ?_) (fun s h => ilf_nil (jf_ilf h))
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at ha; subst ha
    have hbw : ILF [] w.2 :=
      ilf_nil (fo_ik (fun _ => il_checkBudgetRestart) (fun _ => oi_checkBudgetRestart) σ (jf_ilf hσ) w hw)
    unfold NonDetE.whenE at hy
    split at hy
    · rename_i hr
      rw [SInv.checkBudgetRestart_true hw hr] at hy
      exact fo_fl4HandleSyscall N ct rep c σ hσ y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact hbw
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

set_option maxHeartbeats 8000000 in
theorem fo_handleEvent_int : HKE (FN []) (ILF []) (handleEvent (Z := Unit) .interrupt) := by
  simp only [handleEvent, withoutPreemption]
  refine hk_liftE ?_
  intro σ hσ y hy
  refine fn_ilf ((?_ : IK (FN []) _) σ hσ y hy)
  exact ik_bind (fo_ikn (fun _ => iln_ik (by il_auto) (by nq_auto)) (fun _ => by oi_auto)) fun _ =>
    ik_bind (fo_ikn (fun _ => iln_ik il_checkBudget (fun s h z hz => nq_checkBudget s h z hz))
      (fun _ => oi_checkBudget)) fun _ =>
      fo_ikn (fun _ => iln_maybeHandleInterrupt false) (fun _ => oi_maybeHandleInterrupt _)

theorem fo_handleEvent_other (ct : ObjRef) (ev : Event) (hev : ∀ c, ev ≠ .syscallEvent c)
    (hi : ev ≠ .interrupt) :
    HKE (fun s => FN [ct] s ∧ s.curThread = ct) (ILF []) (handleEvent (Z := Unit) ev) := by
  have hct : ct ∈ [ct] := List.mem_singleton_self _
  have hF : ∀ (m : SMonad Unit Unit) (hm : IK (ILF [ct]) m) (hc : CTK ct m) (F : ObjRef → SMonad Unit Unit)
      (hF : ∀ s, ILF [ct] s → ∀ z ∈ (F ct s).1, ILF [] z.2),
      HK (fun s => FN [ct] s ∧ s.curThread = ct) (ILF []) (do
        m
        let restart ← checkBudgetRestart (Z := Unit)
        NonDet.when restart <| do
          let thread ← NonDet.gets fun s : State Unit => s.curThread
          F thread) := by
    intro m hm hc F hF σ hσ y ⟨y1, h1, hy⟩
    have hb1 : ILF [ct] y1.2 := hm σ (fn_ilf hσ.1) y1 h1
    have hc1 : y1.2.curThread = ct := hc σ hσ.2 y1 h1
    obtain ⟨y2, h2, hy⟩ := hy
    have hb2 : ILF [ct] y2.2 := fo_ik (fun _ => il_checkBudgetRestart) (fun _ => oi_checkBudgetRestart) y1.2 hb1 y2 h2
    (try dsimp only at hy)
    unfold NonDet.when at hy
    split at hy
    · rename_i hr
      have e2 : y2.2 = y1.2 := SInv.checkBudgetRestart_true h2 hr
      obtain ⟨y3, h3, hy⟩ := hy
      rw [mem_gets h3] at hy
      (try dsimp only at hy)
      rw [e2, hc1] at hy
      exact hF _ hb1 y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact ilf_nil hb2
  have hHF : ∀ f, ∀ s, ILF [ct] s → ∀ z ∈ (handleFault (Z := Unit) ct f s).1, ILF [] z.2 :=
    fun f s hs z hz => ilf_nil (fo_handleFault ct f hct s hs z hz)
  cases ev with
  | syscallEvent c => exact absurd rfl (hev c)
  | interrupt => exact absurd rfl hi
  | unknownSyscall n =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (hF _ (fo_ik (fun _ => by il_auto) (fun _ => by oi_auto)) (by ct_auto) _ (hHF _))
  | userLevelFault w1 w2 =>
    simp only [handleEvent, withoutPreemption]
    exact hk_liftE (hF _ (fo_ik (fun _ => by il_auto) (fun _ => by oi_auto)) (by ct_auto) _ (hHF _))
  | vmFaultEvent ft =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (hF _ (fo_ik (fun _ => by il_auto) (fun _ => by oi_auto)) (by ct_auto) _ ?_)
    intro s hs z hz
    exact hk_catch (I := ILF [ct]) (Q0 := ILF [])
      (hkr_of_ike (fo_ik (fun _ => by il_auto) (fun _ => by oi_auto)) fun _ h => ilf_nil h) (fun e => hHF e) s hs z hz
  | hypervisorEvent ht =>
    simp only [handleEvent, withoutPreemption]
    refine hk_liftE (hF _ (fo_ik (fun _ => by il_auto) (fun _ => by oi_auto)) (by ct_auto) _ ?_)
    intro s hs z hz
    refine ilf_nil ((?_ : IK (ILF [ct]) _) s hs z hz)
    exact fo_ik (fun _ => by il2_auto) (fun _ => by oi_auto)

/-- il2's `iln_preemptionPath` at any `K`. -/
theorem ilnK_preemptionPath {K : List ObjRef} : IK (ILN K) (preemptionPath (Z := Unit)) :=
  fun σ h y hy => ⟨(show HK (ILN K) (IL K) (preemptionPath (Z := Unit)) by
    unfold preemptionPath
    have htail : HK (ILN K) (IL K) (maybeHandleInterrupt (Z := Unit) true) :=
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

theorem fo_preemptionPath : IK (FN []) (preemptionPath (Z := Unit)) :=
  fo_ikn (fun _ => ilnK_preemptionPath) (fun _ => oi_preemptionPath)

/-- `fl4CallKernel` from a handler result that is `ILF []` (and, by nq3, `NQ []`) on both outcomes. -/
theorem fo_fl4CallKernel_of {rep : Bool} {ev : Event} {P : State Unit → Prop}
    (h : HKE P (ILF []) (fl4HandleEvent (Z := Unit) rep ev)) (hN : HKE P (NQ []) (fl4HandleEvent (Z := Unit) rep ev)) :
    HK P (ILF []) (fl4CallKernel (Z := Unit) rep ev) := by
  intro σ hσ y hy
  unfold fl4CallKernel at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 : FN [] y1.2 := by
    unfold NonDetE.handleE at h1
    obtain ⟨z, hz, h1⟩ := h1
    have hz' : FN [] z.2 := ⟨⟨(h σ hσ z hz).1, hN σ hσ z hz⟩, (h σ hσ z hz).2⟩
    obtain ⟨r, s⟩ := z
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 h1]; exact hz'
    | error e =>
      obtain ⟨w, hw, rfl⟩ := ft_mem_liftE (m := preemptionPath (Z := Unit)) h1
      exact fo_preemptionPath s hz' w hw
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 := fo_ikn (fun _ => iln_fl4Awaken) (fun _ => oi_fl4Awaken) y1.2 hb1 y2 h2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : ILF [] y3.2 := fo_schedule y2.2 (fn_ilf hb2) y3 h3
  exact fo_ik (fun _ => il_activateThread) (fun _ => oi_activateThread) y3.2 hb3 y hy

/-! ## The tops -/

/-- **`FT` (the FPU owner is a TCB holding a thread cap) kept by the syscall
entry**, with IfLiveT, from an active current thread (l4v `ct_active`),
NtfnQB ∧ EpQB and UtInv3 (all carried). -/
theorem kentry_fpuOwn (rep : Bool) (c : Syscall) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState)
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) (hF : FT σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, IfLiveT y.2 ∧ FT y.2 := by
  obtain ⟨x0, hx0, ha0⟩ := ha
  intro y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hNQ : NQ [σ.curThread] σ := nq_cons ((nq_nil_iff σ).2 hN) fun x hx => by
    rw [hx0] at hx; cases hx; exact ok_of_active ha0
  have hJ : JF σ.interruptIrqNode σ.curThread σ :=
    ⟨⟨il_consT ((il_nil_iff σ).2 h) (h _ x0 hx0 (live_of_active ha0)), hNQ, rfl, hU, rfl⟩, hF⟩
  have hI : Iu σ.curThread σ :=
    ⟨hNQ, rfl, hU.1.1.1, nqDet_of_live hU.1 (ifLiveB_of h)⟩
  have hJ2 : JF σ.interruptIrqNode σ.curThread y2.2 ∧ Iu σ.curThread y2.2 := by
    refine ⟨(?_ : IK (JF σ.interruptIrqNode σ.curThread) _) σ hJ y2 h2, (?_ : IK (Iu σ.curThread) _) σ hI y2 h2⟩
    · juf_auto
    · iu_auto
  have := fo_fl4CallKernel_of (P := fun s => JF σ.interruptIrqNode σ.curThread s ∧ Iu σ.curThread s)
    (hk_pre (fo_fl4HandleEvent_sys _ σ.curThread rep c) fun _ h => h.1)
    (hk_pre (nq_fl4HandleEvent_sys σ.curThread rep c) fun _ h => h.2) y2.2 hJ2 y hy
  exact ⟨this.1.1, this.2⟩

/-- **`FT` kept by every kernel event**, with IfLiveT: the current thread a TCB,
active (or, for an interrupt, idle). -/
theorem kcall_fpuOwn (rep : Bool) (ev : Event) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) (hF : FT σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, IfLiveT y.2 ∧ FT y.2 := by
  obtain ⟨x0, hx0, ha0⟩ := ha
  have hNQ : NQ [σ.curThread] σ := by
    refine nq_cons ((nq_nil_iff σ).2 hN) fun x hx => ?_
    rw [hx0] at hx; cases hx
    rcases ha0 with h1 | ⟨-, h1⟩
    · exact ok_of_active h1
    · rw [h1]; exact ⟨fun h => h, rfl⟩
  have hI : Iu σ.curThread σ := ⟨hNQ, rfl, hU.1.1.1, nqDet_of_live hU.1 (ifLiveB_of h)⟩
  intro y hy
  suffices hs : ILF [] y.2 from ⟨hs.1.1, hs.2⟩
  by_cases hint : ev = .interrupt
  · subst hint
    exact fo_fl4CallKernel_of (P := fun s => FN [] s ∧ NQ [σ.curThread] s ∧ s.curThread = σ.curThread)
      (hk_pre (by simp only [fl4HandleEvent]; exact fo_handleEvent_int) fun _ h => h.1)
      (hk_pre (nq_fl4HandleEvent_other σ.curThread rep .interrupt fun c e => by cases e) fun _ h => h.2)
      σ ⟨⟨⟨(il_nil_iff σ).2 h, nq_weak_nil _ hNQ⟩, hF⟩, hNQ, rfl⟩ y hy
  have hact : activeSt x0.tcbState := by
    rcases ha0 with h1 | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hint
  have hL : IL [σ.curThread] σ := il_consT ((il_nil_iff σ).2 h) (h _ x0 hx0 (live_of_active hact))
  by_cases hs : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := hs
    exact fo_fl4CallKernel_of (P := fun s => JF σ.interruptIrqNode σ.curThread s ∧ Iu σ.curThread s)
      (hk_pre (fo_fl4HandleEvent_sys _ σ.curThread rep c) fun _ h => h.1)
      (hk_pre (nq_fl4HandleEvent_sys σ.curThread rep c) fun _ h => h.2) σ ⟨⟨⟨hL, hNQ, rfl, hU, rfl⟩, hF⟩, hI⟩ y hy
  · have hev : ∀ c, ev ≠ .syscallEvent c := fun c e => hs ⟨c, e⟩
    have hE : HKE (fun s => FN [σ.curThread] s ∧ s.curThread = σ.curThread) (ILF []) (fl4HandleEvent (Z := Unit) rep ev) := by
      rw [fl4HandleEvent_other rep ev hev]; exact fo_handleEvent_other σ.curThread ev hev hint
    exact fo_fl4CallKernel_of (P := fun s => FN [σ.curThread] s ∧ NQ [σ.curThread] s ∧ s.curThread = σ.curThread)
      (hk_pre hE fun _ h => ⟨h.1, h.2.2⟩)
      (hk_pre (nq_fl4HandleEvent_other σ.curThread rep ev hev) fun _ h => h.2)
      σ ⟨⟨⟨hL, nq_weak_nil _ hNQ⟩, hF⟩, hNQ, rfl⟩ y hy

/-- **FpuOwnOK (l4v `valid_cur_fpu`) kept by the syscall entry** (via `FT`). -/
theorem kentry_fpuOwnOK (rep : Bool) (c : Syscall) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState)
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) (hF : FT σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, FpuOwnOKS y.2 ∧ FT y.2 :=
  fun y hy => let r := kentry_fpuOwn rep c ha hN hU h hF y hy; ⟨fpuOwnOK_of_ft r.2, r.2⟩

/-- **FpuOwnOK kept by every kernel event** (via `FT`). -/
theorem kcall_fpuOwnOK (rep : Bool) (ev : Event) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) (hF : FT σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, FpuOwnOKS y.2 ∧ FT y.2 :=
  fun y hy => let r := kcall_fpuOwn rep ev ha hN hU h hF y hy; ⟨fpuOwnOK_of_ft r.2, r.2⟩

/-- Boot (non-vacuity only, per the 2026-11-20 lead decision): no FPU owner. -/
theorem boot_ft : FT (initASt (Z := Unit)) := fun t ht => by
  simp [initASt, initArchState] at ht

end

end Fl4Proofs.P3.SInvF
