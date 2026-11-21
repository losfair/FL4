/-
P3 (DESIGN.md §9), invariant line G1 (ctq16, item 5 (c)-(d)): **ctq8's
`ebx_preemptionPath_p` without `hB`** (spec side only, outside the JAtZ cone).

* (c) `CKC C` (ctq14's `CKN` and ct = C) holds at the event start from the
  carried exit facts `CtExit` (ct Running or Idle, so not BlockedOnReply) and
  `CurScT` (ct's SC is `cur_sc`): `ckn_of_exit`. It is kept by
  `update_time_stamp`, by `check_budget_restart` on its `true` outcome (the
  state is unchanged: sb2's `checkBudgetRestart_true_eq`), `get_cap_reg`, the
  invocation front (message info, cap / buffer / extra-cap lookups, `get_mrs`,
  `fl4_decode_invocation`: SpecInvCqHF3) and the Restart write
  (`ck_setThreadState`), so the perform starts in `CKC C` and every error
  outcome has `CKN` (SpecInvCqHP's `ckx_fl4PerformInvocation`). The fault /
  error handlers of `syscall`, the reply after the perform and the receive
  phase of ReplyRecv / NBSendRecv / NBSendWait never error (`NE`), and no
  non-syscall event does. **`ckx_fl4HandleEvent`**.
* (d) sb2's `sb_fl4HandleEvent` gives `ScInv` (hence `ScBackS`) at every outcome,
  errors included, so ctq11's `bc_of_ck` gives ctq8's `hB` at every error
  outcome of the event: **`hb_fl4HandleEvent`**. **`ebx_preemptionPath_q`**:
  `ebx_preemptionPath_p` with `CKN` and `ScBackS` in place of `hB`;
  **`ebx_fl4HandleEvent_preempt`**: the preemption handler of `call_kernel`
  from an error outcome of the event, given the bundle there.
-/
import Fl4Proofs.P3.SpecInvCqHP
import Fl4Proofs.P3.SpecInvSbT
import Fl4Proofs.P3.SpecInvAllC
open Classical

namespace Fl4Proofs.P3.SInvQ.R16
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.R14

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The front -/

theorem ckx_syscall (C : ObjRef) {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    (h1 : IKE (CKC C) mF) (h3 : ∀ a, IKE (CKC C) (mE a)) (h5 : ∀ b, CKX C (mFin b)) :
    CKX C (syscall mF hF mE hE mFin) := by
  unfold syscall withoutPreemption
  refine ckx_bind_ike (ike_liftE h1) fun r => ?_
  cases r with
  | error f => exact ckx_of_ne (ne_liftE _)
  | ok a =>
    refine ckx_bind_ike (ike_liftE (h3 a)) fun r => ?_
    cases r with
    | error e => exact ckx_of_ne (ne_liftE _)
    | ok b => exact h5 b

/-- **`fl4_handle_invocation`**: every error outcome from a `CKC C` state has `CKN`. -/
theorem ckx_fl4HandleInvocationR (C : ObjRef) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    CKX C (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ckx_bind_ike (ike_liftE (ik_gets _)) fun thread => ?_
  refine ckx_bind_ike (ike_liftE (ckc_of (by ck_leaf) (by ct_auto))) fun info => ?_
  refine ckx_syscall C ?_ (fun a => ?_) (fun b => ?_)
  · exact ckc_ofE (by ck_auto) (by ct_auto)
  · obtain ⟨sl, cap, ex, buf⟩ := a
    dsimp only
    exact ckc_ofE (by ck_auto) (by ct_auto)
  · refine ckx_bind_ike (ike_liftE (ckc_of (ck_setThreadState _ _ fun r h => by cases h) (by ct_auto))) fun _ => ?_
    exact ckx_bind_ne (ckx_fl4PerformInvocation C _ _ _ b) fun _ => ne_liftE _

theorem ckc_getCapReg (C : ObjRef) (reg : Register) : IKE (CKC C) (withoutPreemption (Z := Unit) (getCapReg reg)) :=
  ike_liftE (ckc_of (by ck_leaf) (by ct_auto))

/-- **`fl4_handle_syscall`.** -/
theorem ckx_fl4HandleSyscall (C : ObjRef) (rep : Bool) (c : Syscall) : CKX C (fl4HandleSyscall (Z := Unit) rep c) := by
  have hInv := fun cl bl dn fp cptr => ckx_fl4HandleInvocationR C rep cl bl dn fp cptr
  cases c
  all_goals simp only [fl4HandleSyscall]
  all_goals first
    | exact ckx_bind_ike (ckc_getCapReg C _) fun cptr => hInv _ _ _ _ cptr
    | exact ckx_bind_ike (ckc_getCapReg C _) fun cptr => ckx_bind_ne (hInv _ _ _ _ cptr) fun _ => ne_withoutPreemption _
    | exact ckx_of_ne (ne_withoutPreemption _)

/-- **Every error outcome of the event from a `CKC C` state has `CKN`.** -/
theorem ckx_fl4HandleEvent (C : ObjRef) (rep : Bool) (ev : Event) : CKX C (fl4HandleEvent (Z := Unit) rep ev) := by
  cases ev with
  | syscallEvent c =>
    simp only [fl4HandleEvent]
    refine ckx_bind_ike (ike_liftE (ckc_of (by ck_leaf) (by ct_auto))) fun _ => ?_
    intro σ hσ y hy e he
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e', he', rfl⟩⟩ := ft_mem_bindE hy
    · obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
      simp only [Except.ok.injEq] at hr
      subst hr
      unfold NonDetE.whenE at hy
      split at hy
      · rename_i ht
        rw [SInvB.checkBudgetRestart_true_eq hw ht] at hy
        exact ckx_fl4HandleSyscall C rep c σ hσ y hy e he
      · obtain rfl := Set.mem_singleton_iff.1 hy
        cases he
    · obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
      cases he'
  | _ => exact ckx_of_ne (by simp only [fl4HandleEvent, handleEvent]; exact ne_withoutPreemption _)

/-! ## The event start and the bridge -/

/-- `CKN` at the event start from the carried exit facts. -/
theorem ckn_of_exit {σ : State Unit} (hX : SInvAll.CtExit σ) (hC : CurScT σ) : CKN σ := by
  intro x hx
  refine ⟨Or.inr (hC x hx), fun r h => ?_⟩
  obtain ⟨x', hx', hs⟩ := hX
  rw [hx] at hx'
  cases hx'
  rcases hs with hs | hs <;> rw [hs] at h <;> cases h

/-- **ctq8's `hB` at every error (preemption) outcome of the event.** -/
theorem hb_fl4HandleEvent (rep : Bool) (ev : Event) (σ : State Unit) (hE : SInvB.EntryOK σ)
    (hX : SInvAll.CtExit σ) (hC : CurScT σ) :
    ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, ∀ e, y.1 = .error e →
      schedulable y.2.curThread y.2 = true → BC y.2 := by
  intro y hy e he hs
  have hK : CKN y.2 := ckx_fl4HandleEvent σ.curThread rep ev σ ⟨ckn_of_exit hX hC, rfl⟩ y hy e he
  exact R11.bc_of_ck (ckn_ck hK) (SInvB.sb_fl4HandleEvent SInvB.scGap rep ev σ hE y hy).back hs

/-- **`preemption_path` without `hB`**: ctq8's `ebx_preemptionPath_p` from `CKN` and `ScBackS`. -/
theorem ebx_preemptionPath_q (N S : ObjRef) (b : Bool) (σ : State Unit) (hK : CKN σ) (hS : SInvB.ScBackS σ)
    (hN : NQ [] σ) (hV : SInvI.VI N S b σ) :
    HKp (EB true) (EBX N S b) σ (preemptionPath (Z := Unit)) :=
  ebx_preemptionPath_p N S b σ (fun hs => R11.bc_of_ck (ckn_ck hK) hS hs) hN hV

/-- **The preemption handler of `call_kernel` from an error outcome of the event**, given the bundle
(`EB true`, `NQ []`, `VI`) there. -/
theorem ebx_fl4HandleEvent_preempt (N S : ObjRef) (b : Bool) (rep : Bool) (ev : Event) (σ : State Unit)
    (hE : SInvB.EntryOK σ) (hX : SInvAll.CtExit σ) (hC : CurScT σ) :
    ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, ∀ e, y.1 = .error e →
      NQ [] y.2 → SInvI.VI N S b y.2 → HKp (EB true) (EBX N S b) y.2 (preemptionPath (Z := Unit)) :=
  fun y hy e he hN hV => ebx_preemptionPath_p N S b y.2 (hb_fl4HandleEvent rep ev σ hE hX hC y hy e he) hN hV

end

end Fl4Proofs.P3.SInvQ.R16
