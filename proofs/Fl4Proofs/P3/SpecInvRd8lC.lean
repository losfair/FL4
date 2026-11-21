/-
P3 (DESIGN.md §9), invariant line G1 (rd8l, KENTRY-PLAN rd8k handoff 2):
**`BlockedScActive` across the syscall arms, every event and the entry**
(spec side only, outside the JAtZ cone).

* `B0 I s` (the body start's bundle): rd8k's `KD I`, sb2's `ScInv`, `CBa ct`,
  vfh's `VfC`, `NotQ ct`, `Bd ct`. `b0_getCapReg`, `b0_heap` (heap and ct
  kept), `kc_updateTimeStamp`.
* Arms: `ba_sysInv` (Send / NBSend / Call: rd8l's shell), `ba_sysInvRecv`
  (ReplyRecv / NBSendRecv / NBSendWait: the shell, then rd8k's
  `ba_handleRecv` from `RK ct` at the shell's `ok` outcome: BSA by the
  shell, ScInv by sb2's `sb_handleInvocationR`, `NotQ ct ∧ CBa ct` the
  pinned input `RP`), the receive arms (`ba_handleRecv`), Yield
  (`ba_handleYield_p`); **`ba_fl4HandleSyscall`**.
* **`ba_fl4HandleEvent_sys`** (update_time_stamp, check_budget_restart: the
  `true` branch keeps the state, sb2's `checkBudgetRestart_true_eq`; the
  `false` branch rd8i's `ba_checkBudgetRestart_p`), `HF t`,
  `hf_handleVmFault`, `ba_utsCbr`, **`ba_handleEvent_other`** (faults by
  rd8i's `ba_handleFault_p`, the interrupt by `ba_checkBudget_p` and the
  generated `ba_maybeHandleInterrupt`).
* **`ba_fl4CallKernel`** (preemption path at an error outcome with sb2's
  `ScInv` there: `sb_fl4HandleEvent`), tops **`kcall_bsa`**,
  **`kentry_bsa`** (the FaultIP write by rd12b's KZ).
-/
import Fl4Proofs.P3.SpecInvRd8lB
import Fl4Proofs.P3.SpecInvSbT
import Fl4Proofs.P3.SpecInvRd8hF
open Classical

namespace Fl4Proofs.P3.SInvR.B8l
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif
  Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g Fl4Proofs.P3.SInvR.B8i Fl4Proofs.P3.SInvR.B8k

noncomputable section

set_option maxHeartbeats 1000000

/-- **The body start's bundle** (module docstring). -/
def B0 (I : ObjRef) (s : State Unit) : Prop :=
  KD I s ∧ SInvB.ScInv s ∧ CBa s.curThread s ∧ SInv.VfC s ∧ NotQ s.curThread s ∧ Bd s.curThread s

theorem nq_kz {σ0 s : State Unit} {t : ObjRef} (h : A12b.KZ σ0 s) (hn : NotQ t σ0) : NotQ t s := by
  intro x hx
  have e := (A12b.kz_parts h).1 t
  rw [hx] at e
  obtain ⟨x0, hx0, e1, -, -⟩ := B8c.tcbV_some (o := σ0.kheap t) e.symm
  rw [← e1]; exact hn x0 hx0

/-- `CBa`, `NotQ`, `Bd` of a thread along a heap-keeping step. -/
theorem cnb_heap {s s' : State Unit} {t : ObjRef} (hk : s'.kheap = s.kheap)
    (h : CBa t s ∧ NotQ t s ∧ Bd t s) : CBa t s' ∧ NotQ t s' ∧ Bd t s' := by
  obtain ⟨hc, hn, x, c, hx, hxc⟩ := h
  refine ⟨fun x c hx hxc => ?_, fun x hx => ?_, x, c, by rw [hk]; exact hx, hxc⟩
  · rw [hk] at hx
    obtain ⟨y, n, hy, ha⟩ := hc x c hx hxc
    exact ⟨y, n, by rw [hk]; exact hy, ha⟩
  · rw [hk] at hx; exact hn x hx

theorem kc_updateTimeStamp (K : ObjRef → Option KernelObject) (C : ObjRef) (N : Irq → ObjRef) :
    IK (fun s => s.kheap = K ∧ s.curThread = C) (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp
  repeat' (first
    | ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact h)
    | ((with_reducible refine ik_modify ?_); intro _ h; exact h)
    | ik_step0 | ik_unfold | (unfold NonDet.when))

theorem b0_getCapReg (r : Register) (I : ObjRef) (s : State Unit) (h : B0 I s) :
    ∀ w ∈ (getCapReg (Z := Unit) r s).1, B0 I w.2 ∧ w.2.curThread = s.curThread := by
  intro w hw
  have hz : A12b.KZ s w.2 := A12b.kz_getCapReg (V := s) r s rfl w hw
  have hJ := sj_of (C := s.curThread) (I := I) (D := True) (ba_getCapReg r) (fun _ => by sb_auto)
    (fun _ => by uk_auto) (fun _ => by isk_auto) (ws_of_kz fun V => A12b.kz_getCapReg (V := V) r) (by vfc_auto)
    s ⟨h.1, h.2.1, h.2.2.1, rfl, h.2.2.2.1, fun _ => h.2.2.2.2.2⟩ w hw
  obtain ⟨hK, hI, hC, hct, hv, hd⟩ := hJ
  refine ⟨⟨hK, hI, by rw [hct]; exact hC, hv, by rw [hct]; exact nq_kz hz h.2.2.2.2.1,
    by rw [hct]; exact hd trivial⟩, hct⟩

/-! ## The syscall arms -/

theorem ba_sysInv (rep cl bl dn fp : Bool) (r : Register) (I : ObjRef) (s : State Unit) (h : B0 I s) :
    ∀ y ∈ ((do
      let cptr ← NonDetE.liftE <| getCapReg (Z := Unit) r
      fl4HandleInvocationR rep cl bl dn fp cptr).run s).1, BSA y.2 := by
  intro y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  · obtain ⟨w, hw, rfl⟩ := SInvU.mem_liftE' hz
    simp only [Except.ok.injEq] at ha; subst ha
    obtain ⟨hw', -⟩ := b0_getCapReg r I s h w hw
    exact ba_fl4HandleInvocationR rep cl bl dn fp w.1 I w.2
      ⟨hw'.1, hw'.2.1, hw'.2.2.1, rfl, hw'.2.2.2.1, fun _ => hw'.2.2.2.2.2⟩ y hy
  · obtain ⟨w, -, hw⟩ := SInvU.mem_liftE' hz; rw [hw] at he; cases he

/-- **The pinned input of the ReplyRecv arms**: `ct` is not ipc-queued and its
SC (if any) is active at every `ok` outcome of the non-blocking first phase
(l4v: `ct_active` and `active_sc_tcb_at ct` after a non-blocking
`handle_invocation`). -/
def RP (rep cl bl dn fp : Bool) (r : Register) (s : State Unit) : Prop :=
  ∀ w ∈ (getCapReg (Z := Unit) r s).1, ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep cl bl dn fp w.1).run w.2).1,
    (∃ u, y.1 = .ok u) → NotQ y.2.curThread y.2 ∧ CBa y.2.curThread y.2

theorem ba_sysInvRecv (rep cl bl dn fp a b : Bool) (r : Register) (I : ObjRef) (s : State Unit) (h : B0 I s)
    (hE : SInvB.EntryOK s) (hR : RP rep cl bl dn fp r s) :
    ∀ y ∈ ((do
      let c ← withoutPreemption <| getCapReg (Z := Unit) r
      fl4HandleInvocationR rep cl bl dn fp c
      withoutPreemption <| handleRecv a b).run s).1, BSA y.2 := by
  intro y hy
  obtain ⟨z, hz, ⟨a0, ha, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · unfold withoutPreemption at hz; obtain ⟨w, -, hw⟩ := SInvU.mem_liftE' hz; rw [hw] at he; cases he
  unfold withoutPreemption at hz
  obtain ⟨w, hw, rfl⟩ := SInvU.mem_liftE' hz
  simp only [Except.ok.injEq] at ha; subst ha
  obtain ⟨hw', -⟩ := b0_getCapReg r I s h w hw
  have hS := ba_fl4HandleInvocationR rep cl bl dn fp w.1 I w.2
    ⟨hw'.1, hw'.2.1, hw'.2.2.1, rfl, hw'.2.2.2.1, fun _ => hw'.2.2.2.2.2⟩
  have hRel : SInvB.Rel s w.2 :=
    SInvB.rel_step (fun _ => SInvU.uk_getCapReg r) (fun _ => by sb_auto) ⟨rfl, SInvB.BR.refl _⟩ hw
  obtain ⟨z2, hz2, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := SInvU.mem_bindE' hy
  · have hb := hS z2 hz2
    have hI2 : SInvB.ScInv z2.2 :=
      SInvB.sb_handleInvocationR SInvB.scGap rep cl bl dn fp w.1 s hE w.2 hw'.2.1 hRel z2 hz2
    obtain ⟨hn, hc⟩ := hR w hw z2 hz2 ⟨u, hu⟩
    unfold withoutPreemption at hy
    obtain ⟨v, hv, rfl⟩ := SInvU.mem_liftE' hy
    exact ba_handleRecv z2.2.curThread a b z2.2 ⟨hb, hI2, hn, hc, rfl⟩ v hv
  · exact hS z2 hz2

theorem ba_recvArm (a b : Bool) (I : ObjRef) (s : State Unit) (h : B0 I s) :
    ∀ y ∈ ((withoutPreemption (Z := Unit) (handleRecv a b)).run s).1, BSA y.2 := by
  intro y hy
  unfold withoutPreemption at hy
  obtain ⟨v, hv, rfl⟩ := SInvU.mem_liftE' hy
  exact ba_handleRecv s.curThread a b s ⟨h.1.1, h.2.1, h.2.2.2.2.1, h.2.2.1, rfl⟩ v hv

/-- The pinned input `RP` of the syscall's arm (True for the other arms). -/
def RR (rep : Bool) (s : State Unit) : Syscall → Prop
  | .sysReplyRecv => RP rep false false true true replyRegister s
  | .sysNBSendRecv => RP rep false false true true nbsendRecvDest s
  | .sysNBSendWait => RP rep false false true true replyRegister s
  | _ => True

/-- **Every syscall arm keeps `BlockedScActive`** from `B0` at the body start. -/
theorem ba_fl4HandleSyscall (rep : Bool) (c : Syscall) (I : ObjRef) (s : State Unit) (h : B0 I s)
    (hE : SInvB.EntryOK s) (hR : RR rep s c) :
    ∀ y ∈ ((fl4HandleSyscall (Z := Unit) rep c).run s).1, BSA y.2 := by
  cases c with
  | sysSend => exact ba_sysInv rep false true false false cap_register I s h
  | sysNBSend => exact ba_sysInv rep false false false false cap_register I s h
  | sysCall => exact ba_sysInv rep true true true false cap_register I s h
  | sysRecv => exact ba_recvArm true true I s h
  | sysYield =>
    intro y hy
    simp only [fl4HandleSyscall, withoutPreemption] at hy
    obtain ⟨v, hv, rfl⟩ := SInvU.mem_liftE' hy
    exact ba_handleYield_p s h.2.1 h.1.1 v hv
  | sysReplyRecv => exact ba_sysInvRecv rep false false true true true true replyRegister I s h hE hR
  | sysNBSendRecv => exact ba_sysInvRecv rep false false true true true true nbsendRecvDest I s h hE hR
  | sysNBSendWait => exact ba_sysInvRecv rep false false true true true false replyRegister I s h hE hR
  | sysWait => exact ba_recvArm true false I s h
  | sysNBWait => exact ba_recvArm false false I s h
  | sysNBRecv => exact ba_recvArm false true I s h

/-! ## The events -/

/-- **The syscall event** from `B0` and sb2's `EntryOK` at its start. -/
theorem ba_fl4HandleEvent_sys (rep : Bool) (c : Syscall) (I : ObjRef) (σ : State Unit) (h : B0 I σ)
    (hE : SInvB.EntryOK σ) (hR : ∀ z ∈ (updateTimeStamp (Z := Unit) σ).1, RR rep z.2 c) :
    ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep (.syscallEvent c)).run σ).1, BSA y.2 := by
  simp only [fl4HandleEvent]
  intro y hy
  obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, he0, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz; cases he0
  obtain ⟨z1, hz1, rfl⟩ := SInvU.mem_liftE' hz
  have hE1 : SInvB.EntryOK z1.2 := SInvB.entryOK_keep hE (SInvU.uk_mem (fun _ => SInvU.uk_updateTimeStamp) hz1)
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) hz1)
    ((show SInvU.NK σ.interruptIrqNode (updateTimeStamp (Z := Unit)) from SInvU.nk_updateTimeStamp) σ rfl z1 hz1)
    ((show IK VfhAll (updateTimeStamp (Z := Unit)) by unfold updateTimeStamp; kh_auto) σ hE.vfh z1 hz1)
  obtain ⟨hk, hct⟩ := kc_updateTimeStamp σ.kheap σ.curThread σ.interruptIrqNode σ ⟨rfl, rfl⟩ z1 hz1
  have hcnb := cnb_heap hk ⟨h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  rw [← hct] at hcnb
  have h1 : B0 I z1.2 := ⟨⟨ba_updateTimeStamp σ h.1.1 z1 hz1,
    SInvU.io_of_uk (fun _ => SInvU.uk_updateTimeStamp) σ h.1.2.1 z1 hz1,
    SInvL.isk_updateTimeStamp σ h.1.2.2 z1 hz1⟩, hE1.sc, hcnb.1,
    (show IK SInv.VfC (updateTimeStamp (Z := Unit)) by vfc_auto) σ h.2.2.2.1 z1 hz1, hcnb.2.1, hcnb.2.2⟩
  obtain ⟨z2, hz2, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz2; cases he
  obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz2
  simp only [Except.ok.injEq] at hr; subst hr
  unfold NonDetE.whenE at hy
  split at hy
  · rename_i ht
    have e := SInvB.checkBudgetRestart_true_eq hx ht
    rw [e] at hy
    exact ba_fl4HandleSyscall rep c I z1.2 h1 hE1 (hR z1 hz1) y hy
  · rw [Set.mem_singleton_iff.1 hy]
    exact ba_checkBudgetRestart_p z1.2 hE1.sc h1.1.1 x hx

/-- What a fault handler needs of the faulting thread. -/
abbrev HF (t : ObjRef) (s : State Unit) : Prop := BSA s ∧ SInvB.ScInv s ∧ CBa t s

theorem hf_handleVmFault (t : ObjRef) (ft : VMFaultType) : IKE (HF t) (handleVmFault (Z := Unit) t ft) := by
  unfold handleVmFault
  refine ike_bind (ike_liftE (ik_doMachineOp (fun _ _ h => ⟨⟨h.1.1, h.1.2⟩, h.2.1, h.2.2⟩) _)) fun _ => ?_
  refine ike_bind (ike_liftE (fun s hs y hy => ⟨(by ba_auto : BAK (asUser (Z := Unit) t (getRegister .errorRegister)))
    s hs.1 y hy, SInvB.sik_of_sbk (fun _ => SInvB.sb_asUser _ _) s hs.2.1 y hy,
    cba_sv hs.2.2 (SVK.sv_asUser' _ _ s y hy)⟩)) fun _ => ?_
  split <;> exact ike_throw _

/-- update_time_stamp, check_budget_restart, then `k ct` on the `true` branch. -/
theorem ba_utsCbr (k : ObjRef → NonDet (State Unit) Unit)
    (hk : ∀ s, HF s.curThread s → ∀ y ∈ (k s.curThread s).1, BSA y.2) (σ : State Unit) (h : HF σ.curThread σ) :
    ∀ y ∈ ((do
      updateTimeStamp (Z := Unit)
      let restart ← checkBudgetRestart (Z := Unit)
      NonDet.when restart <| do
        let thread ← NonDet.gets fun s : State Unit => s.curThread
        k thread) σ).1, BSA y.2 := by
  intro y ⟨z1, hz1, z2, hz2, hy⟩
  obtain ⟨hk1, hct⟩ := kc_updateTimeStamp σ.kheap σ.curThread σ.interruptIrqNode σ ⟨rfl, rfl⟩ z1 hz1
  have hI1 : SInvB.ScInv z1.2 := SInvB.sik_of_sbk (fun _ => SInvB.sb_updateTimeStamp) σ h.2.1 z1 hz1
  have hB1 : BSA z1.2 := ba_updateTimeStamp σ h.1 z1 hz1
  have hC1 : CBa z1.2.curThread z1.2 := by
    rw [hct]
    intro x c hx hc
    rw [hk1] at hx
    obtain ⟨y0, n, hy0, ha⟩ := h.2.2 x c hx hc
    exact ⟨y0, n, by rw [hk1]; exact hy0, ha⟩
  unfold NonDet.when at hy
  dsimp only at hy
  split at hy
  · rename_i ht
    have e := SInvB.checkBudgetRestart_true_eq hz2 ht
    rw [e] at hy
    obtain ⟨w, hw, hy⟩ := hy
    obtain rfl := mem_gets hw
    exact hk z1.2 ⟨hB1, hI1, hC1⟩ y hy
  · rw [Set.mem_singleton_iff.1 hy]
    exact ba_checkBudgetRestart_p z1.2 hI1 hB1 z2 hz2

theorem ba_hf (s : State Unit) (ex : Fault) (h : HF s.curThread s) :
    ∀ y ∈ (handleFault (Z := Unit) s.curThread ex s).1, BSA y.2 :=
  ba_handleFault_p s.curThread ex s (ta_of_fwd h.2.1.fwd h.2.2) h.2.2 h.1

set_option maxHeartbeats 4000000 in
/-- **Every non-syscall event keeps `BlockedScActive`**; `CBa ct` read only by
the fault events. -/
theorem ba_handleEvent_other (ev : Event) (hne : ∀ c, ev ≠ .syscallEvent c) (σ : State Unit) (hB : BSA σ)
    (hI : SInvB.ScInv σ) (hC : ev ≠ .interrupt → CBa σ.curThread σ) :
    ∀ y ∈ ((handleEvent (Z := Unit) ev).run σ).1, BSA y.2 := by
  intro y hy
  cases ev with
  | syscallEvent c => exact absurd rfl (hne c)
  | unknownSyscall n =>
    simp only [handleEvent, withoutPreemption] at hy
    obtain ⟨v, hv, rfl⟩ := SInvU.mem_liftE' hy
    exact ba_utsCbr _ (fun s hs y hy => ba_hf s _ hs y hy) σ ⟨hB, hI, hC (by intro e; cases e)⟩ v hv
  | userLevelFault w1 w2 =>
    simp only [handleEvent, withoutPreemption] at hy
    obtain ⟨v, hv, rfl⟩ := SInvU.mem_liftE' hy
    exact ba_utsCbr _ (fun s hs y hy => ba_hf s _ hs y hy) σ ⟨hB, hI, hC (by intro e; cases e)⟩ v hv
  | vmFaultEvent ft =>
    simp only [handleEvent, withoutPreemption] at hy
    obtain ⟨v, hv, rfl⟩ := SInvU.mem_liftE' hy
    refine ba_utsCbr _ (fun s hs y hy => ?_) σ ⟨hB, hI, hC (by intro e; cases e)⟩ v hv
    simp only [NonDetE.catch] at hy
    obtain ⟨w, hw, hy⟩ := hy
    have hw' : HF s.curThread w.2 := hf_handleVmFault s.curThread ft s hs w hw
    rcases w with ⟨_ | a, s1⟩
    · exact ba_handleFault_p s.curThread _ s1 (ta_of_fwd hw'.2.1.fwd hw'.2.2) hw'.2.2 hw'.1 y hy
    · rw [Set.mem_singleton_iff.1 hy]; exact hw'.1
  | hypervisorEvent hf =>
    simp only [handleEvent, withoutPreemption] at hy
    obtain ⟨v, hv, rfl⟩ := SInvU.mem_liftE' hy
    exact ba_utsCbr _ (fun s hs y hy => ba_handleHypervisorFault _ _ s hs.1 y hy) σ
      ⟨hB, hI, hC (by intro e; cases e)⟩ v hv
  | interrupt =>
    simp only [handleEvent, withoutPreemption] at hy
    obtain ⟨v, hv, rfl⟩ := SInvU.mem_liftE' hy
    obtain ⟨z1, hz1, z2, hz2, hv⟩ := hv
    have hI1 : SInvB.ScInv z1.2 := SInvB.sik_of_sbk (fun _ => SInvB.sb_updateTimeStamp) σ hI z1 hz1
    have hB1 : BSA z1.2 := ba_updateTimeStamp σ hB z1 hz1
    exact ba_maybeHandleInterrupt false z2.2 (ba_checkBudget_p z1.2 hI1 hB1 z2 hz2) v hv

/-! ## The kernel call and the entry -/

set_option maxHeartbeats 4000000 in
/-- **`BlockedScActive` across `fl4CallKernel`** from the event start's facts. -/
theorem ba_fl4CallKernel (rep : Bool) (ev : Event) (σ : State Unit) (hB : BSA σ) (hE : SInvB.EntryOK σ)
    (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hV : SInv.VfC σ) (hC : ev ≠ .interrupt → CBa σ.curThread σ)
    (hN : ∀ c, ev = .syscallEvent c → NotQ σ.curThread σ ∧ Bd σ.curThread σ)
    (hR : ∀ c, ev = .syscallEvent c → ∀ z ∈ (updateTimeStamp (Z := Unit) σ).1, RR rep z.2 c) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, BSA y.2 := by
  unfold fl4CallKernel
  intro y hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' : BSA z.2 := by
    unfold NonDetE.handleE at hz
    rw [ExceptT.run_mk] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hwB : BSA w.2 := by
      by_cases hs : ∃ c, ev = .syscallEvent c
      · obtain ⟨c, rfl⟩ := hs
        obtain ⟨hn, hd⟩ := hN c rfl
        exact ba_fl4HandleEvent_sys rep c σ.idleSc σ ⟨⟨hB, hO, rfl⟩, hE.sc, hC (by intro e; cases e), hV, hn, hd⟩
          hE (hR c rfl) w hw
      · rw [fl4HandleEvent_other rep ev fun c e => hs ⟨c, e⟩] at hw
        exact ba_handleEvent_other ev (fun c e => hs ⟨c, e⟩) σ hB hE.sc hC w hw
    have hwI := SInvB.sb_fl4HandleEvent SInvB.scGap rep ev σ hE w hw
    obtain ⟨r, s⟩ := w
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 hz]; exact hwB
    | error e =>
      unfold withoutPreemption at hz
      obtain ⟨v, hv, rfl⟩ := SInvU.mem_liftE' hz
      exact ba_preemptionPath_p s hwI hwB v hv
  exact (show BAK (do fl4Awaken (Z := Unit); schedule; activateThread) by ba_auto) z.2 hz' y hy

/-- **`BlockedScActive` across every kernel event.** Premises (all carried or
entry facts): BSA (this line), sb2's `EntryOK` (ScInv, UtInv3, VfhAll,
ScLive [J]), IdleScOutV (vi3 / ut7), CnDom (vfh), rd7's `CAx`; ct not
ipc-queued (from rd8a's `EF.ct` or SInvAll's `EntryJ.ctAct`: Running / Restart /
idle) and ct ≠ idle for a non-interrupt event (l4v `call_kernel`'s
`ct_running s ∨ (ev = Interrupt ∧ ct_idle s)`; rd8a's `EF.ni`); and
the pinned `RR` of a ReplyRecv / NBSendRecv / NBSendWait syscall. -/
theorem kcall_bsa (rep : Bool) (ev : Event) {σ : State Unit} (hB : BSA σ) (hE : SInvB.EntryOK σ)
    (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hCD : CnDom σ) (hA : CAx σ)
    (hNQ : NotQ σ.curThread σ)
    (hni : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hR : ∀ c, ev = .syscallEvent c → ∀ z ∈ (updateTimeStamp (Z := Unit) σ).1, RR rep z.2 c) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, BSA y.2 := by
  refine ba_fl4CallKernel rep ev σ hB hE hO ⟨(vfhV_iff σ).2 hE.vfh, hCD⟩
    (fun h => cba_of_actB (hA (hni h))) (fun c e => ⟨hNQ, ?_⟩) hR
  obtain ⟨x, c', y, n, hx, hc, -, -⟩ := hA (hni (by rw [e]; intro h; cases h))
  exact ⟨x, c', hx, hc⟩

set_option maxHeartbeats 4000000 in
/-- **`BlockedScActive` across the syscall entry** (the FaultIP write, then
the syscall event); premises as `kcall_bsa` with ct ≠ idle, `RR` pinned at the
FaultIP outcome. -/
theorem kentry_bsa (c : Syscall) {σ : State Unit} (hB : BSA σ) (hE : SInvB.EntryOK σ)
    (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hCD : CnDom σ) (hA : CAx σ)
    (hNQ : NotQ σ.curThread σ)
    (hni : σ.curThread ≠ σ.idleThread)
    (hR : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, ∀ z ∈ (updateTimeStamp (Z := Unit) w.2).1,
      RR true z.2 c) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, BSA y.2 := by
  unfold fl4KernelEntrySyscall
  intro y ⟨z, hz, hy⟩
  obtain rfl := Set.mem_singleton_iff.1 hz
  obtain ⟨w, hw, hy⟩ := hy
  have hE' : SInvB.EntryOK w.2 := SInvB.entryOK_keep hE (SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) hw)
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) hw)
    ((show SInvU.NK σ.interruptIrqNode (fl4SyscallFaultIP (Z := Unit) σ.curThread) from
      SInvU.nk_fl4SyscallFaultIP _) σ rfl w hw)
    ((show IK VfhAll (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
      unfold fl4SyscallFaultIP; exact ti_asUser _ _ (fun _ _ h => h)) σ hE.vfh w hw)
  have hz : A12b.KZ σ w.2 := (show A12b.KZK σ (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
    unfold fl4SyscallFaultIP; exact A12b.kz_asUser _ _) σ rfl w hw
  have hctw : w.2.curThread = σ.curThread := A12b.kz_curThread hz
  obtain ⟨x, c', y0, n, hx, hc, hy0, ha⟩ := hA hni
  have hSV := svs_of_kz hz
  have hidle : w.2.idleSc = σ.idleSc := congrArg (fun x => x.2.2.2.2.1) (A12b.kz_parts hz).2.2.1
  refine ba_fl4CallKernel true _ w.2 ((show BAK (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
      unfold fl4SyscallFaultIP; ba_auto) σ hB w hw) hE'
    (by rw [hidle]; exact SInvU.io_of_uk (fun _ => SInvU.uk_fl4SyscallFaultIP _) σ hO w hw)
    ((show IK SInv.VfC (fl4SyscallFaultIP (Z := Unit) σ.curThread) by unfold fl4SyscallFaultIP; vfc_auto) σ
      ⟨(vfhV_iff σ).2 hE.vfh, hCD⟩ w hw)
    (fun _ => by rw [hctw]; exact cba_sv (cba_of_actB (hA hni)) hSV)
    (fun _ _ => ⟨by rw [hctw]; exact nq_kz hz hNQ, by rw [hctw]; exact bd_sv ⟨x, c', hx, hc⟩ hSV⟩)
    (fun c0 e z hz' => by cases e; exact hR w hw z hz') y hy

end

end Fl4Proofs.P3.SInvR.B8l
