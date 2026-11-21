/- nq3: sends and faults (see SpecInvNtfnQG2). -/
import Fl4Proofs.P3.SpecInvNtfnQG
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem nq_filter_post {t : ObjRef} (s : State Unit) (h : NQ Kq s) : NQ (Kq.filter (· ≠ t)) s :=
  nq_filter_of h

/-! ## Sends and faults -/

/-- `send_ipc` of a thread of `K`: it may block on the endpoint, so it leaves `K`. -/
theorem nq_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef)
    (ht : thread ∈ Kq) :
    HK (NQ Kq) (NQ (Kq.filter (· ≠ thread)))
      (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc
  refine hk_bind (hk_of_ik (by nq2_auto)) fun ep => ?_
  split
  · exact nq_sendIpcBlocked _ _ _ _ _ _ ht
  · exact nq_sendIpcBlocked _ _ _ _ _ _ ht
  all_goals exact hk_post (hk_of_ik (by nq2_auto)) nq_filter_post

/-- A non-blocking `send_ipc` keeps `K`. -/
theorem nq_sendIpc_nb (call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef)
    (ht : thread ∈ Kq) :
    NQK Kq (sendIpc (Z := Unit) false call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc
  refine ik_bind (by nq2_auto) fun ep => ?_
  split
  all_goals nq2_auto

/-- `send_fault_ipc` of a thread of `K`: it leaves `K` only when a handler is called. -/
theorem nq_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) (ht : tptr ∈ Kq) :
    ∀ σ, NQ Kq σ → ∀ y ∈ (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate σ).1,
      NQ (Kq.filter (· ≠ tptr)) y.2 ∧ (y.1 = false → NQ Kq y.2) := by
  unfold sendFaultIpc
  split
  · intro σ hσ y hy
    obtain ⟨y1, h1, hy⟩ := hy
    have hb1 : NQ Kq y1.2 := nq_threadSet (fun tcb => { tcb with tcbFault := some fault }) tptr (fun _ => rfl) σ hσ y1 h1
    obtain ⟨y2, h2, hy⟩ := hy
    have hb2 := nq_sendIpc _ _ _ _ _ _ _ _ ht y1.2 hb1 y2 h2
    rw [Set.mem_singleton_iff.1 hy]
    exact ⟨hb2, fun h => by cases h⟩
  · intro σ hσ y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact ⟨nq_filter_of hσ, fun _ => hσ⟩
  · intro σ hσ y hy
    exact hy.elim

theorem nq_handleTimeout (tptr : ObjRef) (ex : Fault) (ht : tptr ∈ Kq) :
    HK (NQ Kq) (NQ (Kq.filter (· ≠ tptr))) (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout
  refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
  refine hk_pure_bind ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
  intro σ hσ y ⟨z, hz, hy⟩
  rw [Set.mem_singleton_iff.1 hy]
  exact (nq_sendFaultIpc tptr _ _ _ ht σ hσ z hz).1
macro_rules | `(tactic| nqh_leaf) => `(tactic| (exact hk_post (nq_handleTimeout _ _ (by nq_mem)) nq_weak_nil))
macro_rules | `(tactic| nqh_leaf) => `(tactic| (exact hk_post (nq_receiveIpcBlocked _ _ _ _ (by nq_mem)) nq_weak_nil))
macro_rules | `(tactic| nqh_leaf) => `(tactic| (refine hk_bind (hk_post (nq_handleTimeout _ _ (by nq_mem)) nq_weak_nil) fun _ => ?_))

theorem nq_handleFault (thread : ObjRef) (ex : Fault) (ht : thread ∈ Kq) :
    HK (NQ Kq) (NQ (Kq.filter (· ≠ thread))) (handleFault (Z := Unit) thread ex) := by
  unfold handleFault
  refine hk_pure_bind ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨h1, h2⟩ := nq_sendFaultIpc thread _ _ _ ht σ hσ z hz
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  unfold NonDet.unless at hw
  split at hw
  · rw [Set.mem_singleton_iff.1 hw]; exact h1
  · rename_i hf
    exact nq_filter_of (nq_handleNoFault thread ht z.2 (h2 (by simpa using hf)) w hw)
macro_rules | `(tactic| nqh_leaf) => `(tactic| (exact hk_post (nq_handleFault _ _ (by nq_mem)) nq_weak_nil))
macro_rules | `(tactic| nqh_leaf) => `(tactic| (refine hk_bind (hk_post (nq_handleFault _ _ (by nq_mem)) nq_weak_nil) fun _ => ?_))


end

end Fl4Proofs.P3.SInv
