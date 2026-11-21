/-
P3 (DESIGN.md §9), invariant line G1 (ft2): **`B` across the sends**
(spec side only). The sender may be exempt (`sendFaultIpc`: it has just been
given a fault and is still active); `send_ipc` ends its exemption: it blocks
(BlockedOnSend), becomes BlockedOnReply / Inactive, or has no fault. The
woken receiver was BlockedOnReceive, so it had no fault.
-/
import Fl4Proofs.P3.SpecInvFaultTcbsH1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

variable {L L0 E K : List ObjRef} {C : ObjRef → Prop}

/-! ## Pre/post combinators -/

/-- `HK` at one start state. -/
def HKp (P Q : State Unit → Prop) (σ : State Unit) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  P σ → ∀ y, y ∈ (m σ).1 → Q y.2

theorem hk_threadGet_bind {P Q : State Unit → Prop} {β γ : Type} {f : Tcb → β} {t : ObjRef}
    {k : β → NonDet (State Unit) γ}
    (h : ∀ σ x, σ.kheap t = some (.tcb x) → HKp P Q σ (k (f x))) : HK P Q (threadGet (Z := Unit) f t >>= k) := by
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hz
  exact h σ x hx hσ y hy

theorem hkp_of_hk {P Q : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : HK P Q m)
    (σ : State Unit) : HKp P Q σ m := fun hσ => h σ hσ

theorem hkp_fail_bind {P Q : State Unit → Prop} {α β : Type} {σ : State Unit} {g : α → NonDet (State Unit) β} :
    HKp P Q σ ((NonDet.fail : NonDet (State Unit) α) >>= g) := by
  intro _ x ⟨y, hy, _⟩; exact hy.elim

theorem hkp_pure_bind {P Q : State Unit → Prop} {α β : Type} {σ : State Unit} {a : α}
    {g : α → NonDet (State Unit) β} (h : HKp P Q σ (g a)) : HKp P Q σ ((pure a : NonDet (State Unit) α) >>= g) := by
  intro hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h hσ x hx

theorem hk_pure_bind {P Q : State Unit → Prop} {α β : Type} {a : α}
    {g : α → NonDet (State Unit) β} (h : HK P Q (g a)) : HK P Q ((pure a : NonDet (State Unit) α) >>= g) :=
  fun σ => hkp_pure_bind (h σ)

theorem hk_fail {P Q : State Unit → Prop} {α : Type} : HK P Q (NonDet.fail : NonDet (State Unit) α) :=
  fun _ _ _ hy => hy.elim

/-- A thread with no fault joins `L` for the rest. -/
theorem hkp_bcons {Q : State Unit → Prop} {α : Type} {σ : State Unit} {t : ObjRef} {m : NonDet (State Unit) α}
    (ht : B L E K C σ → ∀ x, σ.kheap t = some (.tcb x) → x.tcbFault = none)
    (hm : HK (B (t :: L) E K C) Q m) : HKp (B L E K C) Q σ m :=
  fun hσ y hy => hm σ (b_cons hσ (ht hσ)) y hy

/-- Run a `BK` computation for a longer list, ending with the shorter one. -/
theorem hk_of_bk_sub {L1 : List ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : BK L1 E K C m)
    (h1 : ∀ t ∈ L1, t ∈ L) (h2 : ∀ t ∈ L0, t ∈ L1) : HK (B L E K C) (B L0 E K C) m :=
  fun σ hσ y hy => b_mono (h σ (b_mono hσ h1 (fun _ h => h) id) y hy) h2 (fun _ h => h) id

/-- The exemption of a thread of `L` ends. -/
theorem hk_dropL {α : Type} {t : ObjRef} {m : NonDet (State Unit) α} (h : BK L (t :: E) K C m) (ht : t ∈ L) :
    HK (B L (t :: E) K C) (B L E K C) m :=
  fun σ hσ y hy => b_dropE (h σ hσ y hy) fun x hx => Or.inl (((h σ hσ y hy).1.1 t _ hx).2.1 ht)

/-! ## `set_thread_state` with a fault-holding state ends an exemption -/

theorem setThreadStateAct_kheap (t : ObjRef) {P : KHeap → Prop} :
    IK (fun σ => P σ.kheap) (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct setSchedulerAction; repeat' ik_step0

theorem sts_post {t : ObjRef} {ts : ThreadState} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (setThreadState (Z := Unit) t ts σ).1) : ∀ x, y.2.kheap t = some (.tcb x) → x.tcbState = ts := by
  unfold setThreadState at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' : ∀ x, z.2.kheap t = some (.tcb x) → x.tcbState = ts := by
    unfold threadSet at hz
    obtain ⟨w, hw, hz⟩ := hz
    unfold NonDet.getsThe at hw
    cases e : getTcb t σ with
    | none => rw [e] at hw; exact hw.elim
    | some a =>
      rw [e] at hw
      have hw' := Set.mem_singleton_iff.1 hw
      subst hw'
      rw [mem_setObject hz]
      intro x hx
      dsimp only at hx
      simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hx
      rw [← hx]
  exact setThreadStateAct_kheap t (P := fun kh => ∀ x, kh t = some (.tcb x) → x.tcbState = ts) z.2 hz' y hy

theorem b_sts_drop (t : ObjRef) (ts : ThreadState) (hts : faultTcbSt ts) (h2 : t ∈ K → ¬ isBoN ts)
    (h3 : ¬ sndRpl ts ∨ t ∈ K) :
    HK (B L (t :: E) K C) (B L E K C) (setThreadState (Z := Unit) t ts) :=
  fun σ hσ y hy => b_dropE (b_setThreadState t ts (Or.inl hts) h2 h3 (fun _ => Or.inr hts) σ hσ y hy)
    (fun x hx => Or.inr (by rw [sts_post hy x hx]; exact hts))

/-- `reply_push`: the caller (in no queue) becomes BlockedOnReply. -/
theorem b_replyPush (caller callee r : ObjRef) (d : Bool) (hK : caller ∈ K) :
    HK (B L (caller :: E) K C) (B L E K C) (replyPush (Z := Unit) caller callee r d) := by
  unfold replyPush
  refine hk_bind (hk_of_ik (by b_auto)) fun _ => hk_bind (hk_of_ik (by b_auto)) fun _ =>
    hk_bind (hk_of_ik (by b_auto)) fun _ => hk_bind (b_sts_drop _ _ trivial (fun _ h => h) (Or.inr hK)) fun _ =>
    hk_of_ik (by b_auto)

/-! ## `send_ipc` -/

theorem b_sendIpc (block call : Bool) (bd : Badge) (g gr d : Bool) (thread ep : ObjRef) (hK : thread ∈ K)
    (hb : block = true ∨ thread ∈ L) :
    HK (B L (thread :: E) K C) (B L E K C) (sendIpc (Z := Unit) block call bd g gr d thread ep) := by
  have hblk : HK (B L (thread :: E) K C) (B L E K C)
      (sendIpcBlocked (Z := Unit) thread ep bd g gr call) := by
    unfold sendIpcBlocked
    exact hk_bind (b_sts_drop _ _ trivial (fun _ h => h) (Or.inr hK)) fun _ => hk_of_ik (by b_auto)
  have hrest : ∀ dest : ObjRef, BK (dest :: L) E K C (do
      setThreadState (Z := Unit) dest .running
      let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck destSc
      possibleSwitchTo dest) := fun dest => by b_auto
  have hret : thread ∈ L → HK (B L (thread :: E) K C) (B L E K C) (pure () : NonDet (State Unit) Unit) :=
    fun ht => hk_dropL (ik_pure ()) ht
  unfold sendIpc
  refine hk_bind (hk_of_ik (by b_auto)) fun epv => ?_
  cases block <;> split
  all_goals first
    | (with_reducible exact hblk)
    | (with_reducible exact hk_fail)
    | (exact hret (by simpa using hb))
    | (show HK _ _ (pure ()); exfalso; simp_all; done)
    | skip
  all_goals
    rename_i dest q
    refine hk_bind (hk_of_ik (by b_auto)) fun _ => ?_
    unfold getThreadState
    refine hk_threadGet_bind fun σ x hx => ?_
    (try dsimp only)
    cases hs : x.tcbState <;> (try dsimp only) <;> try exact hkp_fail_bind
    refine hkp_bcons (fun hσ y hy => by
      rw [hx] at hy; cases hy; exact b_noFault hσ hx (by rw [hs]; exact fun h => h) (by rw [hs]; exact fun h => h)) ?_
    refine hk_pure_bind (hk_bind (hk_of_ik (by b_auto)) fun _ => hk_bind (hk_of_ik (by b_auto)) fun _ =>
      hk_bind (hk_of_ik (by b_auto)) fun _ => ?_)
    refine hk_threadGet_bind fun σ' x' hx' => ?_
    (try dsimp only)
    cases hf : x'.tcbFault with
    | none =>
      refine hkp_bcons (fun _ y hy => by rw [hx'] at hy; cases hy; exact hf) ?_
      have hr : HK (B (thread :: dest :: L) E K C) (B L E K C) (do
          setThreadState (Z := Unit) dest .running
          let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
          ifSporadicCurScTestRefillUnblockCheck destSc
          possibleSwitchTo dest) :=
        hk_of_bk_sub (hrest dest) (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => List.mem_cons_of_mem _ h)
      split
      · split
        · exact hk_bind (b_replyPush _ _ _ _ hK) fun _ => hr
        · exact hk_bind (b_sts_drop _ _ trivial (fun _ h => h) (Or.inl fun h => h)) fun _ => hr
      · intro σ1 hσ1 y hy
        have h1 := hk_dropL (L := thread :: dest :: L) (E := E) (K := K) (C := C) (t := thread) (by b_auto)
          (by simp) σ1 hσ1 y hy
        exact b_mono h1 (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) (fun _ h => h) id
    | some f =>
      refine hkp_of_hk ?_ σ'
      have hr : HK (B (dest :: L) E K C) (B L E K C) (do
          setThreadState (Z := Unit) dest .running
          let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
          ifSporadicCurScTestRefillUnblockCheck destSc
          possibleSwitchTo dest) :=
        hk_of_bk_sub (hrest dest) (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h)
      split
      · split
        · exact hk_bind (b_replyPush _ _ _ _ hK) fun _ => hr
        · exact hk_bind (b_sts_drop _ _ trivial (fun _ h => h) (Or.inl fun h => h)) fun _ => hr
      · rename_i hc; exact absurd (Or.inr (by simp)) hc

end

end Fl4Proofs.P3.SInv
