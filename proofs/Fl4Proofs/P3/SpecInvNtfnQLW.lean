/-
P3 (DESIGN.md §9), invariant line G1 (il2): **IfLiveT across the queue
wake-ups** (il1 handoff step 1; spec side only).

A thread queued on a notification or an endpoint is BlockedOnNotification /
BlockedOnSend / BlockedOnReceive (NtfnQB / EpQB), so live, so it holds a
thread cap: at the read of the queue the whole queue joins `K`, and the
generated `il_removeAndRestart*Thread (t ∈ K)` lemmas apply per item.

* `ILN K σ := IL K σ ∧ NQ [] σ` (IfLiveT carried with nq1/nq2's NtfnQB ∧ EpQB);
  `iln_ik` (an `IL` lemma and an `NQ` lemma), `iln_of` (an `HK (ILN K) (IL K)`
  lemma and an `NQ` lemma).
* `il_cancelAllSignals`, `il_cancelAllIpc`, `il_cancelBadgedSends`,
  `il_updateWaitingNtfn` (the queue in `K`), `il_sendSignal`:
  `HK (ILN K) (IL K)`; their `iln_*` forms `IK (ILN K)`.
* The callers: `iln_fastFinalise`, `iln_capDeleteOne` (`fast_finalise` has no
  outcome on a thread cap: il1's `MX_capDeleteOne`), `iln_deletingIrqHandler`,
  `iln_invokeIrqHandler`, `iln_handleInterrupt`, `iln_maybeHandleInterrupt`,
  `iln_fl4Awaken` (the timer's signals).
-/
import Fl4Proofs.P3.SpecInvNtfnQLT
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

/-- IfLiveT (with the threads of `K`) carried with NtfnQB ∧ EpQB. -/
def ILN (K : List ObjRef) (σ : State Unit) : Prop := IL K σ ∧ NQ [] σ

theorem iln_ik {α : Type} {m : NonDet (State Unit) α} (h1 : ILK Kq m) (h2 : NQK [] m) : IK (ILN Kq) m :=
  fun σ h x hx => ⟨h1 σ h.1 x hx, h2 σ h.2 x hx⟩

theorem iln_of {α : Type} {m : NonDet (State Unit) α} (h1 : HK (ILN Kq) (IL Kq) m) (h2 : NQK [] m) :
    IK (ILN Kq) m :=
  fun σ h x hx => ⟨h1 σ h x hx, h2 σ h.2 x hx⟩

theorem iln_mono {K K' : List ObjRef} {σ : State Unit} (h : ILN K σ) (hK : ∀ u ∈ K', u ∈ K) : ILN K' σ :=
  ⟨il_mono h.1 hK, h.2⟩

/-- The queue of a notification joins `K`. -/
theorem il_ntfnQueue {σ : State Unit} {n : ObjRef} {a : Notification} (h : ILN Kq σ)
    (hn : σ.kheap n = some (.notification a)) : IL (a.ntfnObj.ntfnQueue ++ Kq) σ := by
  refine ⟨h.1.1, fun t ht => ?_⟩
  rcases List.mem_append.1 ht with ht | ht
  · obtain ⟨y, hy, hs⟩ := h.2.1.1 n a t hn ht
    exact h.1.1 t y hy (liveSt_eq hs True.intro)
  · exact h.1.2 t ht

/-- The queue of an endpoint joins `K`. -/
theorem il_epQueue {σ : State Unit} {e : ObjRef} {a : Endpoint} (h : ILN Kq σ)
    (he : σ.kheap e = some (.endpoint a)) : IL (a.epQueue ++ Kq) σ := by
  refine ⟨h.1.1, fun t ht => ?_⟩
  rcases List.mem_append.1 ht with ht | ht
  · obtain ⟨y, hy, hs⟩ := h.2.1.2 e a t he ht
    exact h.1.1 t y hy (liveSt_of_ipcBlk (Or.inr (by rw [hs]; simp)))
  · exact h.1.2 t ht

theorem hk_getSimpleKo_p {P Q : State Unit → Prop} {α β : Type} [Nonempty α] {C : α → KernelObject}
    {p : ObjRef} {k : α → NonDet (State Unit) β}
    (h : ∀ σ a, σ.kheap p = some (C a) → P σ → ∀ y ∈ (k a σ).1, Q y.2) :
    HK P Q (getSimpleKo (Z := Unit) C p >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getSimpleKo hy
  obtain ⟨a, s⟩ := y
  simp only at hs hk; subst s
  exact h σ a hk hσ x hx

theorem hk_getSimpleKo_e {P Q : State Unit → Prop} {α β : Type} [Nonempty α] {C : α → KernelObject}
    {p : ObjRef} {k : α → NonDet (State Unit) β}
    (h : ∀ σ a, σ.kheap p = some (C a) → P σ → HK (· = σ) Q (k a)) :
    HK P Q (getSimpleKo (Z := Unit) C p >>= k) :=
  hk_getSimpleKo_p fun σ a ha hσ y hy => h σ a ha hσ σ rfl y hy

theorem il_app_right {σ : State Unit} {L : List ObjRef} (h : IL (L ++ Kq) σ) : IL Kq σ :=
  il_mono h fun _ hu => List.mem_append_right _ hu

/-! ## The wake-ups -/

theorem il_cancelAllSignals (n : ObjRef) : HK (ILN Kq) (IL Kq) (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals
  refine hk_getSimpleKo_e fun σ a ha hσ => ?_
  have hq := il_ntfnQueue hσ ha
  split
  · rename_i q hq'
    intro s hs y hy; subst hs
    have e : a.ntfnObj.ntfnQueue = q := by rw [hq']; rfl
    rw [e] at hq
    exact il_app_right ((ik_bind (P := IL (q ++ Kq))
      (ik_mapMx_mem q fun t ht => il_removeAndRestartNtfnQueuedThread t n (List.mem_append_left _ ht))
      fun _ => il_rescheduleRequired) _ hq y hy)
  all_goals intro s hs y hy; subst hs; exact ik_pure _ _ hσ.1 y hy

theorem iln_cancelAllSignals (n : ObjRef) : IK (ILN Kq) (cancelAllSignals (Z := Unit) n) :=
  iln_of (il_cancelAllSignals n) (nq_cancelAllSignals n)

theorem il_cancelAllIpc (e : ObjRef) : HK (ILN Kq) (IL Kq) (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc
  refine hk_getSimpleKo_e fun σ a ha hσ => ?_
  have hq := il_epQueue hσ ha
  split
  · intro s hs y hy; subst hs; exact ik_pure _ _ hσ.1 y hy
  · intro s hs y hy; subst hs
    refine il_app_right ((?_ : ILK (a.epQueue ++ Kq) _) _ hq y hy)
    refine ik_pure_bind ?_
    exact ik_bind (ik_mapMx_mem _ fun t ht => il_removeAndRestartEpQueuedThread t e (List.mem_append_left _ ht))
      fun _ => il_rescheduleRequired

theorem iln_cancelAllIpc (e : ObjRef) : IK (ILN Kq) (cancelAllIpc (Z := Unit) e) :=
  iln_of (il_cancelAllIpc e) (nq_cancelAllIpc e)

theorem il_cancelBadgedSends (e : ObjRef) (badge : Badge) :
    HK (ILN Kq) (IL Kq) (cancelBadgedSends (Z := Unit) e badge) := by
  unfold cancelBadgedSends
  refine hk_getSimpleKo_e fun σ a ha hσ => ?_
  have hq := il_epQueue hσ ha
  split
  · intro s hs y hy; subst hs; subst_vars
    refine il_app_right ((ik_bind (ik_mapMx_mem _ fun t ht => ?_) fun _ => il_rescheduleRequired) _ hq y hy)
    exact il_removeAndRestartBadgedThread t e badge (List.mem_append_left _ ht)
  all_goals intro s hs y hy; subst hs; exact ik_pure _ _ hσ.1 y hy

theorem iln_cancelBadgedSends (e : ObjRef) (badge : Badge) :
    IK (ILN Kq) (cancelBadgedSends (Z := Unit) e badge) :=
  iln_of (il_cancelBadgedSends e badge) (nq_cancelBadgedSends e badge)

/-- `update_waiting_ntfn` of a queue whose threads are in `K` (the woken thread is its head). -/
theorem il_updateWaitingNtfn (n : ObjRef) (queue : List ObjRef) (badge : Badge) (hq : ∀ t ∈ queue, t ∈ Kq) :
    ILK Kq (updateWaitingNtfn (Z := Unit) n queue badge) := by
  cases queue with
  | nil =>
    intro σ _ y hy
    unfold updateWaitingNtfn at hy
    obtain ⟨z, hz, -⟩ := hy
    exact (hz.1 rfl).elim
  | cons a l =>
    have ha : the (a :: l).head? ∈ Kq := hq a (List.mem_cons_self ..)
    unfold updateWaitingNtfn
    il_auto

/-- `send_signal`: a waiting queue joins `K` (NtfnQB); a bound receiver is read live. -/
theorem il_sendSignal (n : ObjRef) (badge : Badge) : HK (ILN Kq) (IL Kq) (sendSignal (Z := Unit) n badge) := by
  unfold sendSignal
  refine hk_getSimpleKo_e fun σ a ha hσ => ?_
  have hq := il_ntfnQueue hσ ha
  split
  all_goals intro s hs y hy; subst hs
  all_goals first
    | (refine il_app_right (il_updateWaitingNtfn n _ badge (fun t ht => List.mem_append_left _ ?_) _ hq y hy);
       simp_all [Ntfn.ntfnQueue]; done)
    | (refine (?_ : ILK Kq _) _ hσ.1 y hy; il2_auto; done)

theorem iln_sendSignal (n : ObjRef) (badge : Badge) : IK (ILN Kq) (sendSignal (Z := Unit) n badge) :=
  iln_of (il_sendSignal n badge) (nq_sendSignal n badge)

/-! ## Their callers -/

theorem iln_fastFinalise (c : Cap) (f : Bool) : IK (ILN Kq) (fastFinalise (Z := Unit) c f) := by
  cases c <;> simp only [fastFinalise]
  case nullCap => exact ik_pure _
  case replyCap r b =>
    exact iln_ik (by il_auto) (nq_fastFinalise (.replyCap r b) f)
  case endpointCap r b g =>
    exact ik_when _ (iln_cancelAllIpc r)
  case notificationCap r b g =>
    refine ik_when _ (ik_bind (iln_ik (il_schedContextMaybeUnbindNtfn r) (nq_schedContextMaybeUnbindNtfn r)) fun _ =>
      ik_bind (iln_ik (il_unbindMaybeNotification r) (nq_unbindMaybeNotification r)) fun _ => iln_cancelAllSignals r)
  all_goals exact ik_fail

/-- `cap_delete_one`: `fast_finalise` has no outcome on a thread cap, and keeps the caps (ut1's `UK` frame). -/
theorem il_capDeleteOne (slot : CslotPtr) : HK (ILN Kq) (IL Kq) (capDeleteOne (Z := Unit) slot) := by
  intro σ hσ x hx
  unfold capDeleteOne at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := SInvU.getCap_capAt hy1
  obtain ⟨c, s1⟩ := y1
  simp only at e1 hc1; subst s1
  dsimp only at hx
  unfold NonDet.unless at hx
  split at hx
  · exact ik_pure () σ hσ.1 x hx
  · obtain ⟨y2, hy2, hx⟩ := hx
    have u2 := SInvU.uk_isFinalCap (uvw := SInvU.uV σ) c σ rfl y2 hy2
    have i2 : ILN Kq y2.2 := iln_ik (il_isFinalCap c) (nq_isFinalCap c) σ hσ y2 hy2
    obtain ⟨y3, hy3, hx⟩ := hx
    have u3 := SInvU.uk_fastFinalise (uvw := SInvU.uV σ) c y2.1 y2.2 u2 y3 hy3
    have i3 := iln_fastFinalise c y2.1 y2.2 i2 y3 hy3
    have hc3 : SInvU.capAt y3.2 slot = some c := by
      rw [show SInvU.capAt y3.2 = SInvU.capAt σ from congrArg (fun w : SInvU.UView => w.2.1) u3]; exact hc1
    refine il_emptySlot_p slot .nullCap y3.2 (fun t e => ?_) (by il_auto) i3.1 x hx
    rw [hc3] at e; cases e
    simp [fastFinalise, NonDet.fail] at hy3

theorem iln_capDeleteOne (slot : CslotPtr) : IK (ILN Kq) (capDeleteOne (Z := Unit) slot) :=
  iln_of (il_capDeleteOne slot) (nq_capDeleteOne slot)

theorem iln_deletingIrqHandler (irq : Irq) : IK (ILN Kq) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler
  exact ik_bind (iln_ik (il_getIrqSlot _) (nq_getIrqSlot _)) fun s => iln_capDeleteOne s

theorem iln_invokeIrqHandler (i : IrqHandlerInvocation) : IK (ILN Kq) (invokeIrqHandler (Z := Unit) i) := by
  cases i <;> simp only [invokeIrqHandler]
  case aCKIrq irq => exact iln_ik (il_archInvokeIrqHandler _) (nq_archInvokeIrqHandler _)
  case setIRQHandler irq cap slot =>
    exact ik_bind (iln_ik (il_getIrqSlot _) (nq_getIrqSlot _)) fun s => ik_bind (iln_capDeleteOne s) fun _ =>
      iln_ik (il_capInsert _ _ _) (nq_capInsert _ _ _)
  case clearIRQHandler irq =>
    exact ik_bind (iln_ik (il_getIrqSlot _) (nq_getIrqSlot _)) fun s => iln_capDeleteOne s

theorem iln_handleInterrupt (irq : Irq) : IK (ILN Kq) (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt
  split
  · exact iln_ik (by il_auto) (by nq_auto)
  · refine ik_bind (iln_ik (by il_auto) (by nq_auto)) fun st => ?_
    cases st <;> dsimp only
    case irqSignal =>
      refine ik_bind (iln_ik (il_getIrqSlot _) (nq_getIrqSlot _)) fun s => ?_
      refine ik_bind (iln_ik (by il_auto) (by nq_auto)) fun c => ?_
      refine ik_bind (ik_when _ (iln_sendSignal _ _)) fun _ => ?_
      exact ik_bind (iln_ik (il_archMaskIrqSignal _) (nq_archMaskIrqSignal _)) fun _ =>
        iln_ik (il_doMachineOp _) (nq_doMachineOp _)
    all_goals exact iln_ik (by il_auto) (by nq_auto)

theorem iln_maybeHandleInterrupt (inKernel : Bool) : IK (ILN Kq) (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt
  refine ik_bind (iln_ik (by il_auto) (by nq_auto)) fun o => ?_
  cases o
  · exact iln_ik il_handleSpuriousIrq nq_handleSpuriousIrq
  · exact iln_handleInterrupt _

theorem iln_fl4Awaken : IK (ILN Kq) (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · exact iln_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)

end

end Fl4Proofs.P3.SInv
