/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi2): `VI N S b`, part E: **send_ipc
and the fault / timeout senders** (vi1's handoff step 1, first half of step 2).

`send_ipc`'s only idle hazard is the non-call donation `sched_context_donate (the
sender_sc) dest` (taken when `canDonate`, not `call`, no fault and `dest` unbound): with
`sender_sc = None` the SC `the None` is unspecified and may be `S`. `vh_sendIpc` is a
pre/post lemma `HK (VIT N S T b) (VI N S b)` whose pinned thread `T` is the sender whenever
`canDonate ∧ ¬call` (`hT`): the pinned thread has an SC, so `the sender_sc ≠ S`
(a thread other than `N` is never bound to `S`). Every other written thread is the sender
(`ht : thread ≠ N`) or the dequeued receiver (`tcbEpDequeue_ne`).
`handle_fault` reads the faulting thread's SC and donates only when it is bound, so it
needs no pinned thread (`vit_of_vi` at the read).
-/
import Fl4Proofs.P3.SpecInvViD
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N S T : ObjRef} {b : Bool}

/-! ## Pre/post combinators -/

theorem vh_bindQ {P R : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    (Q : α → Prop) (hm : IK P m) (hq : ∀ σ, P σ → ∀ y ∈ (m σ).1, Q y.1) (hk : ∀ a, Q a → HK P R (k a)) :
    HK P R (m >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  exact hk y.1 (hq σ hσ y hy) y.2 (hm σ hσ y hy) x hx

theorem vh_bind {P R : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    (hm : IK P m) (hk : ∀ a, HK P R (k a)) : HK P R (m >>= k) :=
  hk_bind hm hk

theorem vh_pure_bind {P R : State Unit → Prop} {α β : Type} {a : α} {k : α → NonDet (State Unit) β}
    (h : HK P R (k a)) : HK P R ((pure a : NonDet (State Unit) α) >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ hσ x hx

theorem vh_fail_bind {P R : State Unit → Prop} {α β : Type} {k : α → NonDet (State Unit) β} :
    HK P R ((NonDet.fail : NonDet (State Unit) α) >>= k) :=
  fun _ _ _ ⟨_, hy, _⟩ => hy.elim

/-- An `IK (VI)` step after the pinned prefix. -/
theorem vh_of_vi {α : Type} {m : NonDet (State Unit) α} (h : IK (VI N S b) m) :
    HK (VIT N S T b) (VI N S b) m :=
  fun σ hσ y hy => h σ (vi_of_vit hσ) y hy

theorem vh_of_vit {α : Type} {m : NonDet (State Unit) α} (h : IK (VIT N S T b) m) :
    HK (VIT N S T b) (VI N S b) m :=
  fun σ hσ y hy => vi_of_vit (h σ hσ y hy)

theorem vh_vi_bind {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    (hm : HK (VIT N S T b) (VI N S b) m) (hk : ∀ a, IK (VI N S b) (k a)) :
    HK (VIT N S T b) (VI N S b) (m >>= k) :=
  hk_bind hm hk

/-! ## send_ipc -/

/-- The receiver arm's tail after the pinned prefix (everything is at `VI`). -/
theorem vi_sendIpc_tail (dest : ObjRef) (hd : dest ≠ N) :
    IK (VI N S b) (do
      setThreadState (Z := Unit) dest .running
      let destSc ← getTcbObjRef Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck destSc
      possibleSwitchTo dest) := by
  vi_auto

/-- The donation branch: the pinned sender's SC is not `S`. -/
theorem vh_donate (thread dest : ObjRef) (ht : thread ≠ N) (hd : dest ≠ N) :
    HK (VIT N S thread b) (VI N S b) (do
      let threadSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext thread
      schedContextDonate (the threadSc) dest) := by
  refine vh_bindQ (fun sc => (thread ≠ N → sc ≠ some S) ∧ (thread = thread → sc ≠ none)) (vi_threadGet _ _)
    (vi_tget_q Tcb.tcbSchedContext thread (fun sc => (thread ≠ N → sc ≠ some S) ∧ (thread = thread → sc ≠ none))
      fun x hx => ⟨hx.2.1, hx.2.2⟩) fun sc hsc => ?_
  refine vh_of_vi (vi_schedContextDonate _ _ ?_ hd)
  obtain ⟨h1, h2⟩ := hsc
  cases sc with
  | none => exact absurd rfl (h2 rfl)
  | some p => intro e; exact h1 ht (by simp only [Fl4Spec.the] at e; rw [e])

set_option maxHeartbeats 4000000 in
/-- **`send_ipc`**: pre `VIT N S T b` with `T` the sender when the send may donate. -/
theorem vh_sendIpc (bl call : Bool) (bd : Badge) (g gr cd : Bool) (thread ep : ObjRef) (ht : thread ≠ N)
    (hT : cd = true → call = false → T = thread) :
    HK (VIT N S T b) (VI N S b) (sendIpc (Z := Unit) bl call bd g gr cd thread ep) := by
  unfold sendIpc
  refine vh_bind (by vi_auto) fun e => ?_
  rcases e with _ | q | (_ | ⟨dest, q⟩) <;> cases bl <;> dsimp only
  · exact vh_of_vit (ik_pure _)
  · exact vh_of_vit (vi_sendIpcBlocked _ _ _ _ _ _ ht)
  · exact vh_of_vit (ik_pure _)
  · exact vh_of_vit (vi_sendIpcBlocked _ _ _ _ _ _ ht)
  · exact vh_of_vit ik_fail
  · exact vh_of_vit ik_fail
  all_goals
    refine vh_bindQ (fun _ => dest ≠ N) (vi_tcbEpDequeue _ _) tcbEpDequeue_ne fun _ hd => ?_
    refine vh_bind (vi_getThreadState _) fun st => ?_
    cases st with
    | blockedOnReceive e0 reply d0 =>
      (try simp only [letFun]); (try dsimp only); (try refine vh_pure_bind ?_)
      refine vh_bind (vi_doIpcTransfer _ _ _ _ _) fun _ => ?_
      refine vh_bind (by vi_auto) fun _ => ?_
      refine vh_bind (vi_getTcbObjRef _ _) fun scOpt => ?_
      refine vh_bind (vi_threadGet _ _) fun fault => ?_
      (try simp only [letFun]); (try dsimp only)
      by_cases hc : (call = true ∨ fault ≠ none)
      · rw [if_pos hc]
        by_cases hg : ((g = true ∨ gr = true) ∧ reply ≠ none)
        · rw [if_pos hg]
          exact vh_vi_bind (vh_of_vi (vi_replyPush _ _ _ _ ht hd)) fun _ => vi_sendIpc_tail dest hd
        · rw [if_neg hg]
          exact vh_vi_bind (vh_of_vi (vi_setThreadState _ _ fun e => absurd e ht)) fun _ => vi_sendIpc_tail dest hd
      · rw [if_neg hc]
        refine vh_vi_bind ?_ fun _ => vi_sendIpc_tail dest hd
        unfold NonDet.when
        by_cases hw : (cd = true ∧ scOpt = none)
        · rw [if_pos hw]
          have hcall : call = false := by
            cases call
            · rfl
            · exact absurd (Or.inl rfl) hc
          rw [hT hw.1 hcall]
          exact vh_donate thread dest ht hd
        · rw [if_neg hw]; exact vh_of_vit (ik_pure' _)
    | _ => (try simp only [letFun]); (try dsimp only); first | exact vh_fail_bind | exact vh_of_vit ik_fail

/-- A `send_ipc` that cannot donate (`¬(canDonate ∧ ¬call)`) keeps `VI`. -/
theorem vi_sendIpc_nd (bl call : Bool) (bd : Badge) (g gr cd : Bool) (thread ep : ObjRef) (ht : thread ≠ N)
    (hnd : cd = true → call = false → False) :
    IK (VI N S b) (sendIpc (Z := Unit) bl call bd g gr cd thread ep) :=
  vh_sendIpc (T := N) bl call bd g gr cd thread ep ht fun h1 h2 => (hnd h1 h2).elim

/-! ## Faults and timeouts -/

/-- `send_fault_ipc` (never a call): pinned `T` is the faulting thread when it may donate. -/
theorem vh_sendFaultIpc (tptr : ObjRef) (hc : Cap) (f : Fault) (cd : Bool) (ht : tptr ≠ N)
    (hT : cd = true → T = tptr) :
    ∀ σ, VIT N S T b σ → ∀ y ∈ (sendFaultIpc (Z := Unit) tptr hc f cd σ).1, VI N S b y.2 := by
  unfold sendFaultIpc
  split
  · intro σ hσ y hy
    obtain ⟨y1, h1, hy⟩ := hy
    have hb1 : VIT N S T b y1.2 := vi_threadSet_same (fun tcb => { tcb with tcbFault := some f }) tptr
      (fun _ => ⟨rfl, rfl, rfl, rfl⟩) σ hσ y1 h1
    obtain ⟨y2, h2, hy⟩ := hy
    have hb2 := vh_sendIpc true false _ _ _ cd tptr _ ht (fun h _ => hT h) y1.2 hb1 y2 h2
    rw [Set.mem_singleton_iff.1 hy]; exact hb2
  · intro σ hσ y hy
    rw [Set.mem_singleton_iff.1 hy]; exact vi_of_vit hσ
  · intro σ hσ y hy
    exact hy.elim

theorem vi_sendFaultIpc_nd (tptr : ObjRef) (hc : Cap) (f : Fault) (ht : tptr ≠ N) :
    IK (VI N S b) (sendFaultIpc (Z := Unit) tptr hc f false) :=
  vh_sendFaultIpc (T := N) tptr hc f false ht fun h => by cases h

macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_sendFaultIpc_nd _ _ _ ?_; vi_side2))

theorem vi_handleTimeout (tptr : ObjRef) (ex : Fault) (ht : tptr ≠ N) :
    IK (VI N S b) (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_handleTimeout _ _ ?_; vi_side2))

theorem vi_handleNoFault (t : ObjRef) (ht : t ≠ N) : IK (VI N S b) (handleNoFault (Z := Unit) t) := by
  unfold handleNoFault; exact vi_setThreadState _ _ fun e => absurd e ht
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_handleNoFault _ ?_; vi_side2))

/-- **`handle_fault`**: it donates only when the faulting thread is bound, read at that state. -/
theorem vi_handleFault (thread : ObjRef) (ex : Fault) (ht : thread ≠ N) :
    IK (VI N S b) (handleFault (Z := Unit) thread ex) := by
  unfold handleFault
  refine ik_pure_bind ?_
  refine ik_bind (vi_getCap _) fun hc => ?_
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hz
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨u, hu, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  have hpin : VIT N S (if x.tcbSchedContext ≠ none then thread else N) b σ := by
    by_cases hs : x.tcbSchedContext ≠ none
    · rw [if_pos hs]
      exact vit_of_vi hσ fun x' hx' => by rw [hx] at hx'; cases hx'; exact hs
    · rw [if_neg hs]; exact hσ
  have hw' : VI N S b w.2 := vh_sendFaultIpc thread hc ex _ ht (fun h => by
      simp only [decide_eq_true_eq] at h; rw [if_pos h]) σ hpin w hw
  unfold NonDet.unless at hu
  split at hu
  · rw [Set.mem_singleton_iff.1 hu]; exact hw'
  · exact vi_handleNoFault thread ht w.2 hw' u hu
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_handleFault _ _ ?_; vi_side2))

end

end Fl4Proofs.P3.SInvI
