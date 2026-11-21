/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi1): `VI N S b`, part C: **endpoint
and notification queues** (no queue holds `N`) and the cancel / restart paths. An append
adds a thread the caller shows is not `N`; a dequeue asserts membership, so the dequeued
thread is not `N` (`vi_epDeq_bind` / `vi_ntfnDeq_bind`): every thread taken from a queue
(cancel_all_ipc, cancel_badged_sends, cancel_all_signals, update_waiting_ntfn) is not idle.
-/
import Fl4Proofs.P3.SpecInvViB
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N S T : ObjRef} {b : Bool}

theorem mem_removeAll_vi {t x : ObjRef} {q : List ObjRef} (h : x ∈ removeAll t q) : x ∈ q :=
  (List.mem_filter.1 h).1

theorem epQueue_updateEpQueue (ep : Endpoint) (q : List ObjRef) (r : Bool) : (updateEpQueue ep q r).epQueue = q := by
  cases ep <;> (try cases r) <;> rfl

theorem mem_pure_vi {α : Type} {a : α} {σ : State Unit} {y : α × State Unit}
    (h : y ∈ ((pure a : NonDet (State Unit) α) σ).1) : y = (a, σ) := Set.mem_singleton_iff.1 h

theorem mem_takeWhile_vi {α : Type} {p : α → Bool} : ∀ {l : List α} {x : α}, x ∈ l.takeWhile p → x ∈ l
  | [], _, h => by cases h
  | a :: l, x, h => by
    unfold List.takeWhile at h
    split at h
    · rcases List.mem_cons.1 h with e | h
      · exact List.mem_cons.2 (Or.inl e)
      · exact List.mem_cons.2 (Or.inr (mem_takeWhile_vi h))
    · cases h

theorem mem_dropWhile_vi {α : Type} {p : α → Bool} : ∀ {l : List α} {x : α}, x ∈ l.dropWhile p → x ∈ l
  | [], _, h => by cases h
  | a :: l, x, h => by
    unfold List.dropWhile at h
    split at h
    · exact List.mem_cons.2 (Or.inr (mem_dropWhile_vi h))
    · exact h

/-- `tcb_append t q` returns a list of `t` and members of `q`. -/
theorem tcbAppend_sub {t : ObjRef} {q : List ObjRef} {σ : State Unit} {y : List ObjRef × State Unit}
    (h : y ∈ (tcbAppend (Z := Unit) t q σ).1) : ∀ x ∈ y.1, x = t ∨ x ∈ q := by
  unfold tcbAppend orderedInsert at h
  obtain ⟨⟨v, s1⟩, -, h⟩ := h
  obtain ⟨⟨vs, s2⟩, -, h⟩ := h
  obtain ⟨⟨zp, s3⟩, h3, h⟩ := h
  rw [mem_pure_vi h3] at h
  obtain ⟨⟨zp', s4⟩, h4, h⟩ := h
  rw [mem_pure_vi h4] at h
  rw [mem_pure_vi h]
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  simp only [List.mem_append, List.mem_singleton] at hp
  rcases hp with (hp | rfl) | hp
  · exact Or.inr (List.of_mem_zip (mem_takeWhile_vi hp)).1
  · exact Or.inl rfl
  · exact Or.inr (List.of_mem_zip (mem_dropWhile_vi hp)).1

theorem vi_tcbEpAppend (t ep : ObjRef) (r : Bool) (ht : t ≠ N) :
    IK (VIT N S T b) (tcbEpAppend (Z := Unit) t ep r) := by
  unfold tcbEpAppend
  refine vi_gep_bind ep fun e he => ik_pure_bind ?_
  refine vi_bindQ (fun q' => ∀ x ∈ q', x = t ∨ x ∈ e.epQueue) (vi_tcbAppend _ _)
    (fun _ _ _ hy => tcbAppend_sub hy) fun q' hq' => vi_setSimpleKo _ _ _ ?_
  show N ∉ (updateEpQueue e q' r).epQueue
  rw [epQueue_updateEpQueue]
  intro hN; rcases hq' N hN with h | h
  · exact ht h.symm
  · exact he h

theorem vi_tcbNtfnAppend (t n : ObjRef) (ht : t ≠ N) : IK (VIT N S T b) (tcbNtfnAppend (Z := Unit) t n) := by
  unfold tcbNtfnAppend
  refine vi_gntfn_bind n fun e he => ik_pure_bind ?_
  refine vi_bindQ (fun q' => ∀ x ∈ q', x = t ∨ x ∈ ntfnQueueOf e) (vi_tcbAppend _ _)
    (fun _ _ _ hy => tcbAppend_sub hy) fun q' hq' => vi_setSimpleKo _ _ _ ?_
  show N ∉ q'
  intro hN; rcases hq' N hN with h | h
  · exact ht h.symm
  · exact he h

theorem vi_tcbEpDequeue (t ep : ObjRef) : IK (VIT N S T b) (tcbEpDequeue (Z := Unit) t ep) := by
  unfold tcbEpDequeue
  refine vi_gep_bind ep fun e he => ik_pure_bind ?_
  refine ik_bind (ik_assert _) fun _ => ik_pure_bind (ik_pure_bind (vi_setSimpleKo _ _ _ ?_))
  show N ∉ (match removeAll t e.epQueue with | [] => Endpoint.idleEP | _ => updateEpQueue e (removeAll t e.epQueue) true).epQueue
  split
  · simp [Endpoint.epQueue]
  · rw [epQueue_updateEpQueue]; exact fun h => he (mem_removeAll_vi h)

theorem vi_tcbNtfnDequeue (t n : ObjRef) : IK (VIT N S T b) (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue
  refine vi_gntfn_bind n fun e he => ik_pure_bind ?_
  refine ik_bind (ik_assert _) fun _ => ik_pure_bind (ik_pure_bind (vi_setSimpleKo _ _ _ ?_))
  show N ∉ (match removeAll t (ntfnQueueOf e) with | [] => Ntfn.idleNtfn | _ => Ntfn.waitingNtfn (removeAll t (ntfnQueueOf e))).ntfnQueue
  split
  · simp [Ntfn.ntfnQueue]
  · exact fun h => he (mem_removeAll_vi h)

/-- A dequeued thread was in the queue, so it is not `N`. -/
theorem tcbEpDequeue_ne {t ep : ObjRef} : ∀ σ, VIT N S T b σ → ∀ y ∈ (tcbEpDequeue (Z := Unit) t ep σ).1, t ≠ N := by
  intro σ hσ y hy
  unfold tcbEpDequeue at hy
  obtain ⟨⟨e, s⟩, h1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo h1
  simp only at hk e1; subst e1
  obtain ⟨⟨q, s⟩, h2, hy⟩ := hy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_pure_vi h2)
  obtain ⟨⟨u, s⟩, ⟨hin, -⟩, -⟩ := hy
  intro e2; subst e2
  exact (vi_obj hσ hk) hin

theorem tcbNtfnDequeue_ne {t n : ObjRef} : ∀ σ, VIT N S T b σ → ∀ y ∈ (tcbNtfnDequeue (Z := Unit) t n σ).1, t ≠ N := by
  intro σ hσ y hy
  unfold tcbNtfnDequeue at hy
  obtain ⟨⟨e, s⟩, h1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo h1
  simp only at hk e1; subst e1
  obtain ⟨⟨q, s⟩, h2, hy⟩ := hy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_pure_vi h2)
  obtain ⟨⟨u, s⟩, ⟨hin, -⟩, -⟩ := hy
  intro e2; subst e2
  exact (vi_obj hσ hk) hin

theorem vi_epDeq_bind {β : Type} (t ep : ObjRef) {k : Unit → NonDet (State Unit) β}
    (hk : t ≠ N → IK (VIT N S T b) (k ())) : IK (VIT N S T b) (tcbEpDequeue (Z := Unit) t ep >>= k) :=
  vi_bindQ (fun _ => t ≠ N) (vi_tcbEpDequeue t ep) tcbEpDequeue_ne fun _ h => hk h

theorem vi_ntfnDeq_bind {β : Type} (t n : ObjRef) {k : Unit → NonDet (State Unit) β}
    (hk : t ≠ N → IK (VIT N S T b) (k ())) : IK (VIT N S T b) (tcbNtfnDequeue (Z := Unit) t n >>= k) :=
  vi_bindQ (fun _ => t ≠ N) (vi_tcbNtfnDequeue t n) tcbNtfnDequeue_ne fun _ h => hk h

macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_tcbEpDequeue _ _)
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_tcbNtfnDequeue _ _)
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_epDeq_bind _ _ fun _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_ntfnDeq_bind _ _ fun _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_tcbEpAppend _ _ _ ?_; vi_side2))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_tcbNtfnAppend _ _ ?_; vi_side2))

theorem vi_reorderEp (ep t : ObjRef) (ht : t ≠ N) : IK (VIT N S T b) (reorderEp (Z := Unit) ep t) := by
  unfold reorderEp
  refine vi_gep_bind ep fun e he => ik_bind (ik_assert _) fun _ => ik_pure_bind ?_
  refine ik_bind (ik_assert _) fun _ => ik_pure_bind ?_
  refine vi_bindQ (fun q' => ∀ x ∈ q', x = t ∨ x ∈ removeAll t e.epQueue) (vi_tcbAppend _ _)
    (fun _ _ _ hy => tcbAppend_sub hy) fun q' hq' => vi_setSimpleKo _ _ _ ?_
  show N ∉ (updateEpQueue e q' true).epQueue
  rw [epQueue_updateEpQueue]
  intro hN; rcases hq' N hN with h | h
  · exact ht h.symm
  · exact he (mem_removeAll_vi h)

theorem vi_reorderNtfn (n t : ObjRef) (ht : t ≠ N) : IK (VIT N S T b) (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn
  refine vi_gntfn_bind n fun e he => ik_bind (ik_assert _) fun _ => ik_pure_bind ?_
  refine ik_bind (ik_assert _) fun _ => ik_pure_bind ?_
  refine vi_bindQ (fun q' => ∀ x ∈ q', x = t ∨ x ∈ removeAll t (ntfnQueueOf e)) (vi_tcbAppend _ _)
    (fun _ _ _ hy => tcbAppend_sub hy) fun q' hq' => vi_setSimpleKo _ _ _ ?_
  show N ∉ q'
  intro hN; rcases hq' N hN with h | h
  · exact ht h.symm
  · exact he (mem_removeAll_vi h)

macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_reorderEp _ _ ?_; vi_side2))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_reorderNtfn _ _ ?_; vi_side2))

/-! ## Cancelling -/

theorem vi_cancelSignal (t n : ObjRef) : IK (VIT N S T b) (cancelSignal (Z := Unit) t n) := by
  unfold cancelSignal; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_cancelSignal _ _)

theorem vi_blockedCancelIpc (st : ThreadState) (t : ObjRef) (r : Option ObjRef) :
    IK (VIT N S T b) (blockedCancelIpc (Z := Unit) st t r) := by
  unfold blockedCancelIpc; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_blockedCancelIpc _ _ _)

theorem vi_replyRemoveTcb (t r : ObjRef) : IK (VIT N S T b) (replyRemoveTcb (Z := Unit) t r) := by
  unfold replyRemoveTcb; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_replyRemoveTcb _ _)

theorem vi_cancelIpc (t : ObjRef) : IK (VIT N S T b) (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_cancelIpc _)

theorem vi_restartThreadIfNoFault (t : ObjRef) (ht : t ≠ N) : IK (VIT N S T b) (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_restartThreadIfNoFault _ ?_; vi_side2))

theorem vi_removeAndRestartEpQueuedThread (t ep : ObjRef) :
    IK (VIT N S T b) (removeAndRestartEpQueuedThread (Z := Unit) t ep) := by
  unfold removeAndRestartEpQueuedThread; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_removeAndRestartEpQueuedThread _ _)

theorem vi_cancelAllIpc (ep : ObjRef) : IK (VIT N S T b) (cancelAllIpc (Z := Unit) ep) := by
  unfold cancelAllIpc; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_cancelAllIpc _)

theorem vi_removeAndRestartBadgedThread (t ep : ObjRef) (bd : Badge) :
    IK (VIT N S T b) (removeAndRestartBadgedThread (Z := Unit) t ep bd) := by
  unfold removeAndRestartBadgedThread; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_removeAndRestartBadgedThread _ _ _)

theorem vi_cancelBadgedSends (ep : ObjRef) (bd : Badge) : IK (VIT N S T b) (cancelBadgedSends (Z := Unit) ep bd) := by
  unfold cancelBadgedSends; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_cancelBadgedSends _ _)

theorem vi_removeAndRestartNtfnQueuedThread (t n : ObjRef) :
    IK (VIT N S T b) (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_removeAndRestartNtfnQueuedThread _ _)

theorem vi_cancelAllSignals (n : ObjRef) : IK (VIT N S T b) (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_cancelAllSignals _)

end

end Fl4Proofs.P3.SInvI
