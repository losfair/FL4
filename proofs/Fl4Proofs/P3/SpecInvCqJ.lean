/-
P3 (DESIGN.md §9), invariant line G1 (ctq3): **TQ across cap deletion, with
nq2's EpQB** (spec side only, outside the JAtZ cone).

`cancel_all_ipc` restarts or makes Inactive every thread of an endpoint
queue (`restart_thread_if_no_fault`): the Inactive write is safe for TQ only
if the thread is in no ready queue, which holds because an endpoint-queued
thread is BlockedOnSend / BlockedOnReceive (nq2's EpQB, l4v `valid_ep`) and so
not runnable. The deletion functions above it carry the joint invariant
`JQ K := NQ K ∧ TQ` (nq2/nq3's `NQ K`, SpecInvNtfnQ): each step either is
covered by both families (`ik_and` of an `nq_*` and a `tq_*` lemma) or is one
of the joint lemmas here (`jq_cancelAllIpc`, the deletion chain up to
`install_tcb_cap`).
-/
import Fl4Proofs.P3.SpecInvCqRF5
import Fl4Proofs.P3.SpecInvNtfnQG
import Fl4Proofs.P3.ScTK
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- nq2's `NQ K` with TQ. -/
abbrev JQ (K : List ObjRef) (σ : State Unit) : Prop := NQ K σ ∧ TQ σ

variable {K : List ObjRef}

theorem hk1_ik {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : IK P m) : HK1 P P m :=
  fun σ hσ x hx => h σ hσ x hx

/-- A step keeping every TCB's state (sch's `ScTKw` with no state change)
keeps "`t` is a runnable TCB". -/
theorem rnH_of_tkw {σ σ' : State Unit} (h : Sched.ScTKw (fun _ => False) σ σ') {t : ObjRef}
    (hr : RnH t σ.kheap) : RnH t σ'.kheap := by
  obtain ⟨x, hx, hrx⟩ := hr
  have hk : Sched.OTK False (σ.kheap t) (σ'.kheap t) := h.kh t
  rw [hx] at hk
  cases e : σ'.kheap t with
  | none => rw [e] at hk; unfold Sched.OTK at hk; exact hk.elim
  | some o =>
    rw [e] at hk
    unfold Sched.OTK Sched.TKObj at hk
    rcases hk with h1 | ⟨x', y, h1, h2, -, hs⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, h1, -⟩ | ⟨_, _, h1, -⟩
    · exact ⟨x, by rw [e, h1], hrx⟩
    · cases h1
      refine ⟨y, by rw [e, h2], ?_⟩
      rcases hs with hs | ⟨hf, -⟩
      · rw [hs]; exact hrx
      · exact hf.elim
    all_goals cases h1

/-- The refill unblock check, then `possible_switch_to` of a runnable thread. -/
theorem tq_unblock_pst (t : ObjRef) (σ : State Unit) (h : TQ σ) (hr : RnH t σ.kheap) (y : Unit × State Unit)
    (hy : y ∈ ((do
      let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t
      ifSporadicCurScAssertRefillUnblockCheck scOpt
      possibleSwitchTo t) σ).1) : TQ y.2 := by
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain ⟨x1, hx1, rfl⟩ := q1_mem_threadGet hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  have h2 : TQ z2.2 := tq_ifCondRefillUnblockCheck _ _ _ σ h z2 hz2
  have hr2 := rnH_of_tkw (Sched.nkt_ifCondRefillUnblockCheck _ _ _ σ z2 hz2) hr
  exact tq_possibleSwitchTo_p t z2.2 hr2 h2 y hy

/-- `restart_thread_if_no_fault` of a thread in no ready queue. -/
theorem tq_restartThreadIfNoFault_u (t : ObjRef) : HK1 (TQU t) TQ (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  dsimp only at hy
  split at hy
  · obtain ⟨z1, hz1, hy⟩ := hy
    have h1 := tqc_setThreadState_r t .restart rfl σ z1 ⟨hσ.1, trivial⟩ hz1
    exact tq_unblock_pst t z1.2 h1.1 h1.2 y hy
  · exact ⟨(tqu_setThreadState t _ σ hσ y hy).1, trivial⟩

/-- **`remove_and_restart_ntfn_queued_thread`** (Restart, then the switch). -/
theorem tq_removeAndRestartNtfnQueuedThread (t n : ObjRef) :
    TQK (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread
  refine ik_bind (by tq_auto) fun _ => ?_
  intro σ hσ y ⟨z1, hz1, hy⟩
  have h1 := tqc_setThreadState_r t .restart rfl σ z1 hσ hz1
  exact tq_unblock_pst t z1.2 h1.1 h1.2 y hy
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tq_removeAndRestartNtfnQueuedThread _ _)

theorem tq_cancelAllSignals (n : ObjRef) : TQK (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; tq_auto
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tq_cancelAllSignals _)

/-- `tcb_ep_dequeue` asserts the thread is in the endpoint's queue. -/
theorem tcbEpDequeue_mem {t e : ObjRef} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (tcbEpDequeue (Z := Unit) t e σ).1) :
    ∃ x, σ.kheap e = some (.endpoint x) ∧ t ∈ x.epQueue := by
  unfold tcbEpDequeue at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst e1
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨hq, rfl⟩, hy⟩ := hy
  exact ⟨a, hk, hq⟩

/-- **`remove_and_restart_ep_queued_thread`**: the dequeued thread was
BlockedOnSend / BlockedOnReceive (EpQB), so in no ready queue. -/
theorem jq_removeAndRestartEpQueuedThread (t e : ObjRef) :
    IK (JQ K) (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  intro σ hσ y hy
  refine ⟨nq_removeAndRestartEpQueuedThread (Kq := K) t e σ hσ.1 y hy, ?_⟩
  unfold removeAndRestartEpQueuedThread at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain ⟨x, hk, hq⟩ := tcbEpDequeue_mem hz1
  obtain ⟨yt, hyt, hbt⟩ := hσ.1.1.2 e x t hk hq
  have hr : runnable yt.tcbState = false := by
    revert hbt; cases yt.tcbState <;> simp [epBlocked, runnable]
  have h1 : TQU t z1.2 :=
    (show IK (TQU t) (tcbEpDequeue (Z := Unit) t e) by tq_auto) σ (tqu_of hσ.2 hyt hr) z1 hz1
  refine (?_ : HK1 (TQU t) TQ _) z1.2 h1 y hy
  unfold getThreadState
  refine hk1_bind (hk1_ik (by tq_auto)) fun st => ?_
  refine hk1_bind (hk1_ik (ik_pure _)) fun ro => ?_
  exact hk1_bind (hk1_ik (by tq_auto)) fun _ => tq_restartThreadIfNoFault_u t

/-! ## The joint automation -/

syntax "jq_leaf" : tactic
macro_rules | `(tactic| jq_leaf) => `(tactic| fail "no jq_leaf")
macro_rules | `(tactic| jq_leaf) => `(tactic| (refine ik_and ?_ ?_ <;> first | (nq_leaf; done) | (tq_leaf; done)))

macro "jq_auto" : tactic => `(tactic| repeat' (first | jq_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| jq_leaf) => `(tactic| with_reducible exact jq_removeAndRestartEpQueuedThread _ _)

theorem jq_cancelAllIpc (e : ObjRef) : IK (JQ K) (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; jq_auto
macro_rules | `(tactic| jq_leaf) => `(tactic| with_reducible exact jq_cancelAllIpc _)

/-- A function covered by both families, at every cap but the endpoint's. -/
theorem jq_fastFinalise (c : Cap) (b : Bool) : IK (JQ K) (fastFinalise (Z := Unit) c b) := by
  cases c
  case endpointCap r bd rt => unfold fastFinalise; jq_auto
  all_goals exact ik_and (nq_fastFinalise (Kq := K) _ _) (by unfold fastFinalise; tq_auto)
macro_rules | `(tactic| jq_leaf) => `(tactic| with_reducible exact jq_fastFinalise _ _)

theorem jq_capDeleteOne (sl : CslotPtr) : IK (JQ K) (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; jq_auto
macro_rules | `(tactic| jq_leaf) => `(tactic| with_reducible exact jq_capDeleteOne _)

theorem jq_deletingIrqHandler (irq : Irq) : IK (JQ K) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; jq_auto
macro_rules | `(tactic| jq_leaf) => `(tactic| with_reducible exact jq_deletingIrqHandler _)

theorem jq_finaliseCap (c : Cap) (b : Bool) : IK (JQ K) (finaliseCap (Z := Unit) c b) := by
  cases c
  case endpointCap r bd rt =>
    simp only [finaliseCap]
    exact ik_liftM _ (ik_when _ (jq_cancelAllIpc r))
  case irqHandlerCap irq =>
    simp only [finaliseCap]
    exact ik_ite _ (ik_bind (jq_deletingIrqHandler irq) fun _ => ik_pure _) (ik_pure _)
  all_goals first
    | exact ik_and (nq_finaliseCap (Kq := K) _ _) (by unfold finaliseCap; tq_auto)
    | (unfold finaliseCap; jq_auto; done)
macro_rules | `(tactic| jq_leaf) => `(tactic| with_reducible exact jq_finaliseCap _ _)

/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem jq_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, IK (JQ K) (f k)) (k : RecDelCall) : IKE (JQ K) (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IKE (JQ K) (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; jq_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; jq_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> jq_auto
    all_goals exact hrec' _

theorem jq_recDel (c : RecDelCall) : IKE (JQ K) (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => jq_recDelF hf k) c
macro_rules | `(tactic| jq_leaf) => `(tactic| with_reducible exact jq_recDel _)

theorem jq_capDelete (sl : CslotPtr) : IKE (JQ K) (capDelete (Z := Unit) sl) := by
  unfold capDelete; jq_auto
macro_rules | `(tactic| jq_leaf) => `(tactic| with_reducible exact jq_capDelete _)

/-- **`install_tcb_cap` keeps `NQ K ∧ TQ`.** -/
theorem jq_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (so : Option (Cap × CslotPtr)) :
    IKE (JQ K) (installTcbCap (Z := Unit) target slot n so) := by
  unfold installTcbCap; jq_auto
macro_rules | `(tactic| jq_leaf) => `(tactic| with_reducible exact jq_installTcbCap _ _ _ _)

end

end Fl4Proofs.P3.SInvQ
