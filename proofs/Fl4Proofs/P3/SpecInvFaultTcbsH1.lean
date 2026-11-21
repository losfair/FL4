/-
P3 (DESIGN.md §9), invariant line G1 (ft2): **the bundle `B` across the
wake-ups** (spec side only): `b_auto` = the generic frame (`b_of_gf` over
`fg_leaf`) | `b_setThreadState` | a state read adding the thread to `L` (a
state that holds no fault and is not active) | a fault read showing none | a
fault clear (`thread_set`, `cancel_ipc`). The wake-ups whose thread is read
before (`restart_thread_if_no_fault`, `restart`, the endpoint cancel loops)
by `b_auto`; those that take the thread from a notification queue
(`remove_and_restart_ntfn_queued_thread`, `update_waiting_ntfn`, so
`cancel_all_signals`, `send_signal`, `fl4Awaken`) by `NQB` at the read of the
notification (`b_queue_cons`).
-/
import Fl4Proofs.P3.SpecInvFaultTcbsN
import Fl4Proofs.P3.SpecInvFaultTcbsW
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

variable {L E K : List ObjRef} {C : ObjRef → Prop}

theorem ikp_bcons {α : Type} {σ : State Unit} {t : ObjRef} {m : NonDet (State Unit) α}
    (ht : B L E K C σ → ∀ x, σ.kheap t = some (.tcb x) → x.tcbFault = none) (hm : BK (t :: L) E K C m) :
    IKp (B L E K C) σ m :=
  fun hσ y hy => b_mono (hm σ (b_cons hσ (ht hσ)) y hy) (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h) id

/-- Pre/post with a thread joining `L`. -/
theorem ik_bhk_bind {α γ : Type} {t : ObjRef} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ}
    (hm : HK (B L E K C) (B (t :: L) E K C) m) (hg : ∀ a, BK (t :: L) E K C (g a)) : BK L E K C (m >>= g) :=
  fun σ hσ x ⟨y, hy, hx⟩ =>
    b_mono (hg y.1 y.2 (hm σ hσ y hy) x hx) (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h) id

theorem b_hk_clearFault (t : ObjRef) :
    HK (B L E K C) (B (t :: L) E K C) (threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t) :=
  fun σ hσ y hy => b_cons (b_of_gf (fun F S => fg_threadSet _ _ fun x hx => F.clr _ _ _ hx) σ hσ y hy)
    (clearFault_post t hy)

/-- With no exempt thread: a state that holds no fault means no fault. -/
theorem b_noFault0 {σ : State Unit} (h : B L [] K C σ) {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hs : ¬ faultTcbSt x.tcbState) : x.tcbFault = none := by
  by_contra hf
  rcases (h.1.1 t _ hx).1 hf with h' | ⟨h', -⟩
  · exact hs h'
  · simp at h'

syntax "b_leaf" : tactic
macro_rules | `(tactic| b_leaf) => `(tactic| fail "no b_leaf")

/-- The side conditions of `b_setThreadState`. -/
macro "b_sts_side" : tactic => `(tactic| first
  | exact Or.inl trivial
  | exact Or.inr (Or.inl (by simp; done))
  | exact Or.inr (Or.inl (by simp_all; done))
  | exact fun _ h => h
  | exact Or.inl (fun h => h)
  | exact Or.inr (by simp_all; done)
  | exact fun _ => Or.inl trivial
  | exact fun _ => Or.inr trivial)

macro_rules | `(tactic| b_leaf) => `(tactic| ((refine b_of_gf (fun _ _ => ?_)); fg_leaf; done))
macro_rules | `(tactic| b_leaf) => `(tactic| ((refine b_of_gfE (fun _ _ => ?_)); fg_leaf; done))
macro_rules | `(tactic| b_leaf) => `(tactic| ((with_reducible refine b_setThreadState _ _ ?_ ?_ ?_ ?_) <;> b_sts_side))

/-- A state read: a state that holds no fault and is not active adds the thread to `L`. -/
macro "b_rds" : tactic => `(tactic| (show IK _ (getThreadState (Z := Unit) _ >>= _); unfold getThreadState; refine ik_threadGet_bind fun σ x hx => ?_; (try dsimp only); cases hs : x.tcbState <;> (try dsimp only) <;> first | (refine ikp_bcons (fun hσ y hy => by rw [hx] at hy; cases hy; exact b_noFault hσ hx (by rw [hs]; exact fun h => h) (by rw [hs]; exact fun h => h)) ?_) | (refine ikp_bcons (fun hσ y hy => by rw [hx] at hy; cases hy; exact b_noFault0 hσ hx (by rw [hs]; exact fun h => h)) ?_) | (refine ikp_of_ik ?_ σ)))

/-- A fault read showing none adds the thread to `L`. -/
macro "b_rdf" : tactic => `(tactic| (show IK _ (threadGet (Z := Unit) Tcb.tcbFault _ >>= _); refine ik_threadGet_bind fun σ x hx => ?_; (try dsimp only); cases hf : x.tcbFault <;> (try dsimp only) <;> first | (refine ikp_bcons (fun _ y hy => by rw [hx] at hy; cases hy; exact hf) ?_) | (refine ikp_of_ik ?_ σ)))

macro "b_rd" : tactic => `(tactic| first | b_rds | b_rdf | (refine ik_bhk_bind (b_hk_clearFault _) fun _ => ?_))

macro "b_auto" : tactic => `(tactic| repeat' (first | b_leaf | b_rd | (show IK _ (ite _ _ _); split) | (show IK _ (ite _ _ _ >>= _); split) | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless) | (exfalso; contradiction)))

/-- `cancel_ipc`: it clears the fault first. -/
theorem b_hk_cancelIpc (t : ObjRef) : HK (B L E K C) (B (t :: L) E K C) (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc
  refine hk_bind (hk_of_ik (b_of_gf fun _ _ => by fg_auto)) fun st => hk_bind (b_hk_clearFault t) fun _ =>
    hk_of_ik ?_
  b_auto

macro_rules | `(tactic| b_rd) => `(tactic| (refine ik_bhk_bind (b_hk_cancelIpc _) fun _ => ?_))

/-! ## Wake-ups after a read of the woken thread -/

theorem b_restartThreadIfNoFault (t : ObjRef) : BK L E K C (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_restartThreadIfNoFault _)

theorem b_removeAndRestartEpQueuedThread (t ep : ObjRef) :
    BK L E K C (removeAndRestartEpQueuedThread (Z := Unit) t ep) := by
  unfold removeAndRestartEpQueuedThread; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_removeAndRestartEpQueuedThread _ _)

theorem b_removeAndRestartBadgedThread (t ep : ObjRef) (bd : Badge) :
    BK L E K C (removeAndRestartBadgedThread (Z := Unit) t ep bd) := by
  unfold removeAndRestartBadgedThread; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_removeAndRestartBadgedThread _ _ _)

theorem b_cancelAllIpc (ep : ObjRef) : BK L E K C (cancelAllIpc (Z := Unit) ep) := by
  unfold cancelAllIpc; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_cancelAllIpc _)

theorem b_cancelBadgedSends (ep : ObjRef) (bd : Badge) : BK L E K C (cancelBadgedSends (Z := Unit) ep bd) := by
  unfold cancelBadgedSends; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_cancelBadgedSends _ _)

theorem b_restart (t : ObjRef) : BK L E K C (restart (Z := Unit) t) := by
  unfold restart; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_restart _)

/-! ## Wake-ups from a notification queue -/

theorem b_removeAndRestartNtfnQueuedThread (t n : ObjRef) (ht : t ∈ L) :
    BK L E K C (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; b_auto

theorem ik_mapMx_mem {P : State Unit → Prop} {α γ : Type} {g : α → NonDet (State Unit) γ} :
    ∀ xs : List α, (∀ a ∈ xs, IK P (g a)) → IK P (NonDet.mapMx g xs)
  | [], _ => ik_pure' _
  | a :: xs, h => ik_bind' (h a (by simp)) fun _ => ik_mapMx_mem xs fun b hb => h b (by simp [hb])

/-- A `get_notification` read, its queue joining `L`. -/
theorem ik_getNtfn_bind {β : Type} {n : ObjRef} {k : Notification → NonDet (State Unit) β}
    (h : ∀ a : Notification, BK (a.ntfnObj.ntfnQueue ++ L) E K C (k a)) :
    BK L E K C (getNotification (Z := Unit) n >>= k) :=
  ik_getSimpleKo_bind (C := KernelObject.notification) fun σ a ha hσ y hy =>
    b_mono (h a σ (b_queue_cons hσ ha) y hy) (fun _ h => List.mem_append_right _ h) (fun _ h => h) id

theorem b_cancelAllSignals (n : ObjRef) : BK L E K C (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals
  refine ik_getNtfn_bind fun a => ?_
  split
  · rename_i q hq
    refine ik_bind (ik_mapMx_mem _ fun t ht => ?_) fun _ => ?_
    · exact b_removeAndRestartNtfnQueuedThread t n (List.mem_append_left _ (by rw [hq]; exact ht))
    · b_auto
  · exact ik_pure _
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_cancelAllSignals _)

theorem ik_assert_bind {P : State Unit → Prop} {γ : Type} {Q : Prop} {g : Unit → NonDet (State Unit) γ}
    (h : Q → IK P (g ())) : IK P (NonDet.assert Q >>= g) := by
  intro σ hσ x ⟨y, ⟨hq, hy⟩, hx⟩
  subst hy
  exact h hq σ hσ x hx

theorem the_head_mem {q : List ObjRef} (h : q ≠ []) : the q.head? ∈ q := by
  cases q with
  | nil => exact absurd rfl h
  | cons a q => simp [the]

theorem b_updateWaitingNtfn (n : ObjRef) (q : List ObjRef) (bd : Badge) (h : ∀ t ∈ q, t ∈ L) :
    BK L E K C (updateWaitingNtfn (Z := Unit) n q bd) := by
  unfold updateWaitingNtfn
  refine ik_assert_bind fun hq => ?_
  have hd : the q.head? ∈ L := h _ (the_head_mem hq)
  b_auto

theorem b_sendSignal (n : ObjRef) (bd : Badge) : BK L E K C (sendSignal (Z := Unit) n bd) := by
  unfold sendSignal
  refine ik_getNtfn_bind fun a => ?_
  split <;> first
    | (exact b_updateWaitingNtfn _ _ _ (fun t ht => List.mem_append_left _ (by simp_all [Ntfn.ntfnQueue])))
    | b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_sendSignal _ _)

theorem b_fl4Awaken : BK L E K C (fl4Awaken (Z := Unit)) := by
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
    · exact b_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_fl4Awaken)

theorem b_activateThread : BK L [] K C (activateThread (Z := Unit)) := by
  unfold activateThread; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_activateThread)

end

end Fl4Proofs.P3.SInv
