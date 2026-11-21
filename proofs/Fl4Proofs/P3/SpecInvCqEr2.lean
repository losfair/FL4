/-
P3 (DESIGN.md §9), invariant line G1 (ctq18, ctq16 handoff 1 (a), (d)): **`EB
true`, `NQ []` and `VI` at every error (preemption) outcome of the event**, so
ctq16's `ebx_fl4HandleEvent_preempt` applies (spec side only, outside the JAtZ
cone).

* The shell invariant `JE I ct d N σe := Js ∧ EB true ∧ Simple` (sl3's `Js`, as
  ctq11's `JR` carries it beside `RT`, only to supply the untyped perform's
  facts: `UtInv''` from `spf_of`, il2's `IfLiveT` in `Js`, ut7's `DecodedFrom`
  of the decode for ut8's `GapOKN`). It is kept by `update_time_stamp`,
  `check_budget_restart` on its `true` outcome (state unchanged), `get_cap_reg`,
  the front (`je_auto`: sl3's `js_auto`, the generated tq / sa / q4 / rb
  families, SpecInvCqEr0's `Simple` family) and the Restart write; at the
  perform it gives SpecInvCqEr1's `PFE ct b` (`DK ct`: `Js`'s ct and `NQ [ct]`).
* The fault / error handlers of `syscall`, the reply after the perform and the
  receive phase never error (ctq16's `NE`; `er_syscall_post`), nor does any
  non-syscall event: **`ebr_fl4HandleInvocationR`**, `ebr_fl4HandleSyscall`,
  **`ebr_fl4HandleEvent`**.
* **`eb_fl4HandleEvent_err`**: with nq3's `Iu ct` (`nq_fl4HandleEvent_sys`: `NQ
  []` at every outcome) and vi3's premises (`vi_fl4HandleEvent_sys viGap`:
  `VI` at every outcome), every error outcome has `EB true ∧ NQ [] ∧ VI`;
  **`ebx_fl4HandleEvent_err`** feeds it to ctq16's `ebx_fl4HandleEvent_preempt`.
-/
import Fl4Proofs.P3.SpecInvCqEr1
import Fl4Proofs.P3.SpecInvCqGS
import Fl4Proofs.P3.SpecInvCqHS
import Fl4Proofs.P3.SpecInvNtfnQH3
import Fl4Proofs.P3.SpecInvViM
open Classical

namespace Fl4Proofs.P3.SInvQ.R18
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL
  Fl4Proofs.P3.SInvQ.P12 Fl4Proofs.P3.SInvQ.R16

noncomputable section

set_option maxHeartbeats 2000000

/-! ## Combinators -/

theorem ebr_gets_bind {P : State Unit → Prop} {ε β γ : Type} {g : State Unit → β}
    {k : β → NonDetE (State Unit) ε γ}
    (h : ∀ σ, P σ → ∀ y ∈ ((k (g σ)).run σ).1, ∀ e, y.1 = .error e → EB true y.2) :
    EBR P (NonDetE.liftE (NonDet.gets g) >>= k) := by
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    obtain rfl := mem_gets hw
    simp only [Except.ok.injEq] at ha; subst ha
    exact h σ hσ y hy
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

/-- The `syscall` shell for error outcomes: only the final phase errors. -/
theorem er_syscall_post {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    {σ : State Unit} {I Q : State Unit → Prop}
    (h3 : ∀ a s, (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → ∀ w ∈ ((ExceptT.run (mE a)) s).1, I w.2)
    (h5 : ∀ a s b s', (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → (.ok b, s') ∈ ((ExceptT.run (mE a)) s).1 →
      I s' → ∀ y ∈ ((mFin b).run s').1, ∀ e, y.1 = .error e → Q y.2) :
    ∀ y ∈ ((syscall mF hF mE hE mFin).run σ).1, ∀ e, y.1 = .error e → Q y.2 := by
  intro y hy e0 he0
  unfold syscall withoutPreemption at hy
  obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    simp only [Except.ok.injEq] at hr
    subst hr
    obtain ⟨r, s⟩ := w
    cases r with
    | error f =>
      obtain ⟨v, -, rfl⟩ := ft_mem_liftE hy
      cases he0
    | ok a =>
      obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
      · obtain ⟨w, hw', rfl⟩ := ft_mem_liftE hz
        simp only [Except.ok.injEq] at hr
        subst hr
        obtain ⟨r, s'⟩ := w
        cases r with
        | error e =>
          obtain ⟨v, -, rfl⟩ := ft_mem_liftE hy
          cases he0
        | ok b => exact h5 a s b s' hw hw' (h3 a s hw _ hw') y hy e0 he0
      · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
        cases he
  · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

/-! ## The shell invariant -/

section S
variable {I : ObjRef × ObjRef} {N : Irq → ObjRef} {σe : State Unit} {ct : ObjRef} {d : Prop}

/-- The shell invariant: sl3's `Js`, `EB true` and no switch pending. -/
abbrev JE (I : ObjRef × ObjRef) (ct : ObjRef) (d : Prop) (N : Irq → ObjRef) (σe s : State Unit) : Prop :=
  Js I ct d N σe s ∧ EB true s ∧ Simple s

theorem je_ofK {α : Type} {m : NonDet (State Unit) α} (h1 : IK (Js I ct d N σe) m) (h2 : TQK m) (h3 : SAK m)
    (h4 : Q4K m) (h5 : RBK true m) (h6 : SMK m) : IK (JE I ct d N σe) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, eb_of h2 h3 h4 h5 σ h.2.1 y hy, h6 σ h.2.2 y hy⟩

macro "je_auto" : tactic => `(tactic| exact je_ofK (by js_auto) (by tq_auto) (by sa_auto) (by q4_auto)
  (by rb_auto) (by sm_auto))

theorem je_eb {s : State Unit} (h : JE I ct d N σe s) : EB true s := h.2.1

set_option maxHeartbeats 16000000 in
/-- **Every error outcome of `handle_invocation` from a `JE` state has `EB true`.** -/
theorem ebr_fl4HandleInvocationR (hE : EF N σe) (hI2 : I.2 = σe.idleSc)
    (rep calling blocking don fp : Bool) (cptr : CapRef) :
    EBR (JE I ct d N σe) (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ebr_gets_bind fun σ hσ => ?_
  have hc : σ.curThread = ct := hσ.1.2.2.1
  simp only [hc, withoutPreemption]
  refine ebr_bind_ike (P := JE I ct d N σe) (?_ : IKE (JE I ct d N σe) _) (fun s h => h.2.1)
    (fun info => ?_) σ hσ
  · exact ike_liftE (by je_auto)
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
  refine er_syscall_post (I := JE I ct d N σe) (Q := EB true) ?_ ?_ y0 hy0
  · intro a s has w hw
    have hs : JE I ct d N σe s := by
      refine (?_ : IKE (JE I ct d N σe) _) σ' hσ' _ has
      je_auto
    obtain ⟨sl, cap, ex, buf⟩ := a
    refine (?_ : IKE (JE I ct d N σe) _) s hs w hw
    je_auto
  · intro a s b s' has hbs hI y hy e he
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hvs : uV s = uV σ' := hF _ σ' rfl _ has
    obtain ⟨hcap, hex⟩ := hOk σ' rfl _ s has
    obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e0, -, he0⟩⟩ := mem_bindE' hbs
    swap
    · simp at he0
    obtain ⟨x0, hx0, e0⟩ := mem_liftE' hz0
    subst e0
    simp only [Except.ok.injEq] at ha0
    subst ha0
    have hvx : uV x0.2 = uV σ' := (uk_getMrs (uvw := uV s) _ _ _ s rfl x0 hx0).trans hvs
    have hDF : DecodedFrom (uV σ') b :=
      ⟨fp, info.miLabel, x0.1, cptr, sl, cap, ex, buf, x0.2, s', hvx, hcap, hex, hb0⟩
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e', he', rfl⟩⟩ := ft_mem_bindE hy
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      have hJ1 : Js I ct d N σe w.2 := js_sts s' hI.1 w hw
      have hE1 : EB true w.2 := eb_setThreadState_r (k := true) ct .restart rfl s' hI.2.1 w hw
      have hS1 : Simple w.2 := sm_setThreadState ct .restart s' hI.2.2 w hw
      obtain ⟨r, s1⟩ := w
      dsimp only at hJ1 hE1 hS1
      have hv1 : uV s1 = uV σ' := hJ1.2.2.2.2.2.1.trans hσ'.1.2.2.2.2.2.1.symm
      obtain ⟨fp', label, args', ci, sl', cap', ex', buf', σ0, s0, hv, hc', hex', hmem⟩ := hDF
      have hG : GapOKN (uV σ') b :=
        okv_fl4DecodeG fp' label args' ci sl' cap' ex' buf' hc' (fun p hp => (hex' p hp).1) σ0 hv _ s0 hmem
      have hspf := spf_of hJ1 hE hI2
      have hPF : PFE ct b s1 :=
        ⟨⟨hE1, hJ1.2.2.1, hS1, hJ1.2.1⟩, hspf.2.2.1.1, ifLiveTN_of_ifLiveT hJ1.1.2.1.1, by rw [hv1]; exact hG⟩
      obtain ⟨z2, hz2, ⟨rp, -, hy⟩ | ⟨e2, he2, rfl⟩⟩ := ft_mem_bindE hy
      · obtain ⟨v, -, rfl⟩ := ft_mem_liftE hy
        cases he
      · exact ebr_fl4PerformInvocation ct blocking calling don b s1 hPF z2 hz2 e2 he2
    · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
      cases he'

/-! ## `handle_syscall` and the events -/

/-- **`handle_syscall`.** -/
theorem ebr_fl4HandleSyscall (hE : EF N σe) (hI2 : I.2 = σe.idleSc) (rep : Bool) (c : Syscall) :
    EBR (JE I ct d N σe) (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv : ∀ (cl bl dn fp : Bool) (cptr : CapRef),
      EBR (JE I ct d N σe) (fl4HandleInvocationR (Z := Unit) rep cl bl dn fp cptr) :=
    fun cl bl dn fp cptr => ebr_fl4HandleInvocationR hE hI2 rep cl bl dn fp cptr
  have hCap : ∀ reg, IKE (JE I ct d N σe) (withoutPreemption (Z := Unit) (getCapReg reg)) :=
    fun reg => ike_liftE (by je_auto)
  cases c
  all_goals simp only [fl4HandleSyscall]
  all_goals first
    | exact ebr_bind_ike (hCap _) (fun _ h => h.2.1) fun cptr => hInv _ _ _ _ cptr
    | exact ebr_bind_ike (hCap _) (fun _ h => h.2.1) fun cptr =>
        ebr_bind_ne (hInv _ _ _ _ cptr) fun _ => ne_withoutPreemption _
    | exact ebr_of_ne (ne_withoutPreemption _)

/-- No non-syscall event errors. -/
theorem ne_fl4HandleEvent_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    NE (fl4HandleEvent (Z := Unit) rep ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [fl4HandleEvent, handleEvent]; exact ne_withoutPreemption _

/-- **Every error outcome of the event from a `JE` state has `EB true`.** -/
theorem ebr_fl4HandleEvent (hE : EF N σe) (hI2 : I.2 = σe.idleSc) (rep : Bool) (ev : Event) :
    EBR (JE I ct d N σe) (fl4HandleEvent (Z := Unit) rep ev) := by
  cases ev with
  | syscallEvent c =>
    simp only [fl4HandleEvent]
    refine ebr_bind_ike (ike_liftE (?_ : IK (JE I ct d N σe) (updateTimeStamp (Z := Unit)))) (fun _ h => h.2.1)
      fun _ => ?_
    · je_auto
    intro σ hσ y hy e he
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e', he', rfl⟩⟩ := ft_mem_bindE hy
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      simp only [Except.ok.injEq] at hr
      subst hr
      unfold NonDetE.whenE at hy
      split at hy
      · rename_i ht
        rw [Fl4Proofs.P3.SInv.checkBudgetRestart_true hw ht] at hy
        exact ebr_fl4HandleSyscall hE hI2 rep c σ hσ y hy e he
      · obtain rfl := Set.mem_singleton_iff.1 hy
        cases he
    · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
      cases he'
  | _ => exact ebr_of_ne (ne_fl4HandleEvent_other rep _ fun c h => by cases h)

/-! ## The bundle at the error outcomes -/

/-- **`EB true`, `NQ []` and `VI` at every error (preemption) outcome of the
event**: `JE` (the EB carry), nq3's `Iu ct` and vi3's premises at the event start
(`σ0`: vi3's view pin; `T`: its pinned thread). -/
theorem eb_fl4HandleEvent_err (hE : EF N σe) (hI2 : I.2 = σe.idleSc) (rep : Bool) (ev : Event)
    (σ : State Unit) (hJ : JE I ct d N σe σ) (hQ : Iu ct σ)
    {Ni Si T : ObjRef} {σ0 : State Unit} (hW : SInvI.W Ni Si T σ0 σ) (hO : IO (fun _ => Ni) σ0)
    (hS : IrqOutV (fun _ => Si) (uV σ0)) (hU : UtInv'' σ0)
    (hT : ∀ c, ev = .syscallEvent c → SInvI.Pinned c → T = σ0.curThread) :
    ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, ∀ e, y.1 = .error e →
      EB true y.2 ∧ NQ [] y.2 ∧ SInvI.VI Ni Si true y.2 := by
  intro y hy e he
  cases ev with
  | syscallEvent c =>
    exact ⟨ebr_fl4HandleEvent hE hI2 rep _ σ hJ y hy e he, nq_fl4HandleEvent_sys ct rep c σ hQ y hy,
      SInvI.vi_fl4HandleEvent_sys SInvI.viGap rep c hW hO hS hU (hT c rfl) y hy⟩
  | _ => exact absurd he (ne_fl4HandleEvent_other rep _ (fun c h => by cases h) σ y hy e)

/-- **The preemption handler applies at every error outcome of the event**
(ctq16's `ebx_fl4HandleEvent_preempt` with the bundle from `eb_fl4HandleEvent_err`). -/
theorem ebx_fl4HandleEvent_err (hE : EF N σe) (hI2 : I.2 = σe.idleSc) (rep : Bool) (ev : Event)
    (σ : State Unit) (hJ : JE I ct d N σe σ) (hQ : Iu ct σ)
    {Ni Si T : ObjRef} {σ0 : State Unit} (hW : SInvI.W Ni Si T σ0 σ) (hO : IO (fun _ => Ni) σ0)
    (hS : IrqOutV (fun _ => Si) (uV σ0)) (hU : UtInv'' σ0)
    (hT : ∀ c, ev = .syscallEvent c → SInvI.Pinned c → T = σ0.curThread)
    (hEO : SInvB.EntryOK σ) (hX : SInvAll.CtExit σ) (hC : CurScT σ) :
    ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, ∀ e, y.1 = .error e →
      EB true y.2 ∧ HKp (EB true) (EBX Ni Si true) y.2 (preemptionPath (Z := Unit)) := by
  intro y hy e he
  have h := eb_fl4HandleEvent_err hE hI2 rep ev σ hJ hQ hW hO hS hU hT y hy e he
  exact ⟨h.1, ebx_fl4HandleEvent_preempt Ni Si true rep ev σ hEO hX hC y hy e he h.2.1 h.2.2⟩

end S

end

end Fl4Proofs.P3.SInvQ.R18
