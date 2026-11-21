/-
P3 (DESIGN.md §9), invariant line G1 (ctq11): **`RT` across the event**
(KENTRY-PLAN ctq10 handoff 1; spec side only).

* At the event start `RT` is the exit's `CtExit` (ct is a TCB) with CurScT
  (`rt_of_curScT`); `resSc_of_rt` gives ctq10's `ResSc` wherever `RT` holds
  (ReplyRecv / NBSendRecv / NBSendWait need it at `handle_recv`).
* **`rt_fl4HandleInvocationR`**: the shell carries sl3's `Js I ct d N σe` beside
  `RT` (`js_auto` / `rt_auto` per step) only to supply the untyped / MakePool
  perform's facts (`spf_of`, ut7's `DecodedFrom` of the decode, the view frame
  for `IrqOutV`); the pin `d` is arbitrary.
* `rt_fl4HandleSyscall`, **`rt_fl4HandleEvent`** (every event; the non-syscall
  arms and `handle_recv` / `handle_yield` are generated leaves), **`rt_event`**
  (the event and the preemption handler, i.e. `call_kernel` before `fl4_awaken`).
-/
import Fl4Proofs.P3.SpecInvCqGP
import Fl4Proofs.P3.SpecInvSlE
import Fl4Proofs.P3.SpecInvCqB5
import Fl4Proofs.P3.SpecInvAllC
open Classical

namespace Fl4Proofs.P3.SInvQ.R11
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The event start and `ResSc` -/

theorem resSc_of_rt {s : State Unit} (h : RT s) : ResSc s := fun hs x hx => by
  obtain ⟨y, hy, hn⟩ := h hs
  rw [hx] at hy; cases hy; exact hn

/-- **`RT` at the event start**: the exit's `CtExit` and CurScT. -/
theorem rt_of_curScT {σ : State Unit} (hX : SInvAll.CtExit σ) (hC : CurScT σ) : RT σ := fun _ => by
  obtain ⟨x, hx, -⟩ := hX
  exact ⟨x, hx, by rw [hC x hx]; simp⟩

/-! ## `handle_invocation` -/

section S
variable {I : ObjRef × ObjRef} {N : Irq → ObjRef} {σe : State Unit} {ct : ObjRef} {d : Prop}

/-- The shell invariant: sl3's `Js` and `RT`. -/
abbrev JR (I : ObjRef × ObjRef) (ct : ObjRef) (d : Prop) (N : Irq → ObjRef) (σe s : State Unit) : Prop :=
  Js I ct d N σe s ∧ RT s

macro "jr_auto" : tactic => `(tactic| exact r11_ikAnd (by js_auto) (by rt_auto))

set_option maxHeartbeats 16000000 in
/-- **`handle_invocation` keeps `RT`.** -/
theorem rt_fl4HandleInvocationR (hE : EF N σe) (hI2 : I.2 = σe.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σe))
    (rep calling blocking don fp : Bool) (cptr : CapRef) :
    HKE (JR I ct d N σe) RT (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine hke_gets_bind fun σ hσ => ?_
  have hc : σ.curThread = ct := hσ.1.2.2.1
  simp only [hc, withoutPreemption]
  refine hke_bind (R := JR I ct d N σe) (hk_liftE (hk_of_ik ?_)) (fun info => ?_) (fun s h => h.2) σ hσ
  · jr_auto
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
  refine ft_syscall_post (I := JR I ct d N σe) (Q := RT) ?_ ?_ ?_ ?_ ?_ y0 hy0
  · refine (?_ : IKE (JR I ct d N σe) _) σ' hσ'
    jr_auto
  · intro f s hs v hv
    refine (?_ : RTK _) s hs.2 v hv
    rt_auto
  · intro a s has w hw
    have hs : JR I ct d N σe s := by
      refine (?_ : IKE (JR I ct d N σe) _) σ' hσ' _ has
      jr_auto
    obtain ⟨sl, cap, ex, buf⟩ := a
    refine (?_ : IKE (JR I ct d N σe) _) s hs w hw
    jr_auto
  · intro e s hs v hv
    refine (?_ : RTK _) s hs.2 v hv
    rt_auto
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
    have hDF : DecodedFrom (uV σ') b :=
      ⟨fp, info.miLabel, x0.1, cptr, sl, cap, ex, buf, x0.2, s', hvx, hcap, hex, hb0⟩
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      have hJ1 : Js I ct d N σe w.2 := js_sts s' hI.1 w hw
      have hR1 : RT w.2 := (show RTK (setThreadState (Z := Unit) ct .restart) by rt_auto) s' hI.2 w hw
      obtain ⟨r, s1⟩ := w
      dsimp only at hJ1 hR1
      have hv1 : uV s1 = uV σ' := hJ1.2.2.2.2.2.1.trans hσ'.1.2.2.2.2.2.1.symm
      have hDF1 : DecodedFrom (uV s1) b := by rw [hv1]; exact hDF
      have hP := rt_fl4PerformInvocation I N [ct] [ct] d ct blocking calling don b s1 hR1 (spf_of hJ1 hE hI2)
        (by rw [hJ1.2.2.2.2.2.1]; exact hI1) hDF1
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        refine (?_ : RTKE _) s2 (hP _ hz2) y hy
        rt_auto
      · exact hP _ hz2
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      exact (show RTK (setThreadState (Z := Unit) ct .restart) by rt_auto) s' hI.2 w hw

/-! ## `handle_syscall` and the events -/

set_option maxHeartbeats 8000000 in
/-- **`handle_syscall` keeps `RT`.** -/
theorem rt_fl4HandleSyscall (hE : EF N σe) (hI2 : I.2 = σe.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σe))
    (rep : Bool) (c : Syscall) : HKE (JR I ct d N σe) RT (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv : ∀ (cl bl dn fp : Bool) (cptr : CapRef),
      HKE (JR I ct d N σe) RT (fl4HandleInvocationR (Z := Unit) rep cl bl dn fp cptr) :=
    fun cl bl dn fp cptr => rt_fl4HandleInvocationR hE hI2 hI1 rep cl bl dn fp cptr
  have hCap : ∀ reg, HKE (JR I ct d N σe) (JR I ct d N σe) (withoutPreemption (Z := Unit) (getCapReg reg)) :=
    fun reg => hk_liftE (hk_of_ik (by jr_auto))
  cases c
  case sysSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (hCap _) (fun cptr => hInv _ _ _ _ cptr) (fun s h => h.2)
  case sysNBSend =>
    simp only [fl4HandleSyscall]
    exact hke_bind (hCap _) (fun cptr => hInv _ _ _ _ cptr) (fun s h => h.2)
  case sysCall =>
    simp only [fl4HandleSyscall]
    exact hke_bind (hCap _) (fun cptr => hInv _ _ _ _ cptr) (fun s h => h.2)
  all_goals
    simp only [fl4HandleSyscall]
    first
      | exact hke_bind (hCap _) (fun cptr => hke_bind (hInv _ _ _ _ cptr)
          (fun _ => hk_liftE (hk_of_ik (by rt_auto))) (fun s h => h)) (fun s h => h.2)
      | exact fun σ hσ => (show RTKE _ by rt_auto) σ hσ.2

/-- **Every event keeps `RT`.** -/
theorem rt_fl4HandleEvent (hE : EF N σe) (hI2 : I.2 = σe.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σe))
    (rep : Bool) (ev : Event) : HKE (JR I ct d N σe) RT (fl4HandleEvent (Z := Unit) rep ev) := by
  cases ev with
  | syscallEvent c =>
    simp only [fl4HandleEvent]
    refine hke_bind (R := JR I ct d N σe) (hk_liftE (hk_of_ik (by jr_auto))) (fun _ => ?_) (fun s h => h.2)
    intro σ hσ y hy
    obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      simp only [Except.ok.injEq] at ha; subst ha
      unfold NonDetE.whenE at hy
      split at hy
      · rename_i hr
        rw [SInv.checkBudgetRestart_true hw hr] at hy
        exact rt_fl4HandleSyscall hE hI2 hI1 rep c σ hσ y hy
      · rw [Set.mem_singleton_iff.1 hy]
        exact (show RTK (checkBudgetRestart (Z := Unit)) by rt_auto) σ hσ.2 w hw
    · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
      cases he
  | _ =>
    intro σ hσ y hy
    refine (?_ : RTKE _) σ hσ.2 y hy
    simp only [fl4HandleEvent, handleEvent]
    rt_auto

/-- **`RT` across the event and the preemption handler** (`call_kernel` up to `fl4_awaken`). -/
theorem rt_event (hE : EF N σe) (hI2 : I.2 = σe.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σe))
    (rep : Bool) (ev : Event) (σ : State Unit) (hσ : JR I ct d N σe σ) :
    ∀ y ∈ (ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev)
      (fun _ => withoutPreemption preemptionPath)) σ).1, RT y.2 := by
  intro y hy
  unfold NonDetE.handleE at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' := rt_fl4HandleEvent hE hI2 hI1 rep ev σ hσ z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a =>
    first
      | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hz')
      | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hz')
  | error e =>
    dsimp only at hy
    refine (?_ : RTKE _) s hz' y hy
    unfold withoutPreemption
    rt_auto

end S

end

end Fl4Proofs.P3.SInvQ.R11
