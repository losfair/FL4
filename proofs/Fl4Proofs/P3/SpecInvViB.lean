/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi1): `VIT N S T b`, part B: **pinned
reads**. A read of the idle-relevant fields at a `VI` state yields a pure fact about the
value (`vi_bindQ`), which the continuation's writes then use: a thread read in a non-idle
state is not `N`, an SC read with no / another TCB is not `S`, a thread read from an
endpoint / notification queue is not `N`, a schedulable thread is not `N`, the current
thread is not `N` under `b`. The conditional leaves (`vi_threadSet` / `vi_updateSchedContext`
/ `vi_setThreadState` with their side conditions) are closed from those facts by `vi_side2`.
-/
import Fl4Proofs.P3.SpecInvViG6
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N S T : ObjRef} {b : Bool}

/-- A read with a fact on its value. -/
theorem vi_bindQ {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β} (Q : α → Prop)
    (hm : IK (VIT N S T b) m) (hq : ∀ σ, VIT N S T b σ → ∀ y ∈ (m σ).1, Q y.1) (hk : ∀ a, Q a → IK (VIT N S T b) (k a)) :
    IK (VIT N S T b) (m >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  exact hk y.1 (hq σ hσ y hy) y.2 (hm σ hσ y hy) x hx

theorem mem_gets_vi {β : Type} {g : State Unit → β} {σ : State Unit} {y : β × State Unit}
    (h : y ∈ (NonDet.gets (σ := State Unit) g σ).1) : y = (g σ, σ) := Set.mem_singleton_iff.1 h

theorem vi_tget_q {β : Type} (f : Tcb → β) (t : ObjRef) (Q : β → Prop)
    (hQ : ∀ x, ObjOK N S T t (.tcb x) → Q (f x)) : ∀ σ, VIT N S T b σ → ∀ y ∈ (threadGet (Z := Unit) f t σ).1, Q y.1 := by
  intro σ hσ y hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hy
  exact hQ x (vi_obj hσ hx)

theorem vi_gts_bind {β : Type} (t : ObjRef) {k : ThreadState → NonDet (State Unit) β}
    (hk : ∀ st, (t = N → st = .idleThreadState) → IK (VIT N S T b) (k st)) :
    IK (VIT N S T b) (getThreadState (Z := Unit) t >>= k) :=
  vi_bindQ _ (vi_getThreadState t) (vi_tget_q _ t _ fun x hx e => ((hx.1 e).1)) hk

theorem vi_tsc_bind {β : Type} (t : ObjRef) {k : Option ObjRef → NonDet (State Unit) β}
    (hk : ∀ sc, (t = N → sc = some S) → (t ≠ N → sc ≠ some S) → (t = T → sc ≠ none) → IK (VIT N S T b) (k sc)) :
    IK (VIT N S T b) (threadGet (Z := Unit) Tcb.tcbSchedContext t >>= k) :=
  vi_bindQ (fun sc => (t = N → sc = some S) ∧ (t ≠ N → sc ≠ some S) ∧ (t = T → sc ≠ none)) (vi_threadGet _ t)
    (vi_tget_q Tcb.tcbSchedContext t (fun sc => (t = N → sc = some S) ∧ (t ≠ N → sc ≠ some S) ∧ (t = T → sc ≠ none))
      fun x hx => ⟨fun e => (hx.1 e).2.2.1, hx.2.1, hx.2.2⟩) fun a h => hk a h.1 h.2.1 h.2.2

theorem vi_tsc_bind' {β : Type} (t : ObjRef) {k : Option ObjRef → NonDet (State Unit) β}
    (hk : ∀ sc, (t = N → sc = some S) → (t ≠ N → sc ≠ some S) → (t = T → sc ≠ none) → IK (VIT N S T b) (k sc)) :
    IK (VIT N S T b) (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= k) := vi_tsc_bind t hk

theorem vi_tyt_bind {β : Type} (t : ObjRef) {k : Option ObjRef → NonDet (State Unit) β}
    (hk : ∀ v, (t = N → v = none) → IK (VIT N S T b) (k v)) :
    IK (VIT N S T b) (getTcbObjRef (Z := Unit) Tcb.tcbYieldTo t >>= k) :=
  vi_bindQ _ (vi_threadGet _ t) (vi_tget_q _ t _ fun x hx e => (hx.1 e).2.2.2) hk

theorem vi_tbn_bind {β : Type} (t : ObjRef) {k : Option ObjRef → NonDet (State Unit) β}
    (hk : ∀ v, (t = N → v = none) → IK (VIT N S T b) (k v)) :
    IK (VIT N S T b) (getTcbObjRef (Z := Unit) Tcb.tcbBoundNotification t >>= k) :=
  vi_bindQ _ (vi_threadGet _ t) (vi_tget_q _ t _ fun x hx e => (hx.1 e).2.1) hk

theorem mem_getSchedContext_vi {p : ObjRef} {σ : State Unit} {y : SchedContext × State Unit}
    (h : y ∈ (getSchedContext (Z := Unit) p σ).1) : (∃ n, σ.kheap p = some (.schedContext y.1 n)) ∧ y.2 = σ := by
  unfold getSchedContext at h
  obtain ⟨⟨o, s⟩, hz, hy⟩ := h
  obtain ⟨hk, e⟩ := mem_getObject hz
  simp only at hk e; subst e
  cases o with
  | schedContext sc n => rw [Set.mem_singleton_iff.1 hy]; exact ⟨⟨n, hk⟩, rfl⟩
  | _ => exact hy.elim

/-- The SC facts of `VI` at `p`. -/
def ScQ (N S p : ObjRef) (sc : SchedContext) : Prop :=
  (p = S → sc.scTcb = some N ∧ sc.scReplies = []) ∧ (p ≠ S → sc.scTcb ≠ some N)

theorem vi_getSc_q (p : ObjRef) : ∀ σ, VIT N S T b σ → ∀ y ∈ (getSchedContext (Z := Unit) p σ).1, ScQ N S p y.1 := by
  intro σ hσ y hy
  obtain ⟨⟨n, hk⟩, -⟩ := mem_getSchedContext_vi hy
  have h := vi_obj hσ hk
  exact ⟨fun e => ⟨(h.1 e).1, (h.1 e).2.1⟩, h.2⟩

theorem vi_gsc_bind {β : Type} (p : ObjRef) {k : SchedContext → NonDet (State Unit) β}
    (hk : ∀ sc, ScQ N S p sc → IK (VIT N S T b) (k sc)) :
    IK (VIT N S T b) (getSchedContext (Z := Unit) p >>= k) :=
  vi_bindQ _ (vi_getSchedContext p) (vi_getSc_q p) hk

theorem vi_gscTcb_bind {β : Type} (p : ObjRef) {k : Option ObjRef → NonDet (State Unit) β}
    (hk : ∀ v, (p = S → v = some N) → (p ≠ S → v ≠ some N) → IK (VIT N S T b) (k v)) :
    IK (VIT N S T b) (getScObjRef (Z := Unit) SchedContext.scTcb p >>= k) := by
  unfold getScObjRef
  refine vi_bindQ (fun v => (p = S → v = some N) ∧ (p ≠ S → v ≠ some N)) (by vi_auto) ?_ fun a h => hk a h.1 h.2
  intro σ hσ y ⟨z, hz, hy⟩
  rw [Set.mem_singleton_iff.1 hy]
  have h := vi_getSc_q p σ hσ z hz
  exact ⟨fun e => (h.1 e).1, h.2⟩

theorem vi_gscRep_bind {β : Type} (p : ObjRef) {k : List ObjRef → NonDet (State Unit) β}
    (hk : ∀ v, (p = S → v = []) → IK (VIT N S T b) (k v)) :
    IK (VIT N S T b) (NonDet.liftM SchedContext.scReplies (getSchedContext (Z := Unit) p) >>= k) := by
  refine vi_bindQ (fun v => p = S → v = []) (by vi_auto) ?_ hk
  intro σ hσ y ⟨z, hz, hy⟩
  rw [Set.mem_singleton_iff.1 hy]
  exact fun e => ((vi_getSc_q p σ hσ z hz).1 e).2

theorem vi_gep_bind {β : Type} (p : ObjRef) {k : Endpoint → NonDet (State Unit) β}
    (hk : ∀ ep, N ∉ ep.epQueue → IK (VIT N S T b) (k ep)) :
    IK (VIT N S T b) (getEndpoint (Z := Unit) p >>= k) := by
  refine vi_bindQ _ (by vi_auto) ?_ hk
  intro σ hσ y hy
  exact vi_obj hσ (mem_getSimpleKo hy).1

theorem vi_gntfn_bind {β : Type} (p : ObjRef) {k : Notification → NonDet (State Unit) β}
    (hk : ∀ n, N ∉ n.ntfnObj.ntfnQueue → IK (VIT N S T b) (k n)) :
    IK (VIT N S T b) (getNotification (Z := Unit) p >>= k) := by
  refine vi_bindQ _ (by vi_auto) ?_ hk
  intro σ hσ y hy
  exact vi_obj hσ (mem_getSimpleKo hy).1

theorem vi_gct_bind {β : Type} {k : ObjRef → NonDet (State Unit) β}
    (hk : ∀ c, (b = true → c ≠ N) → IK (VIT N S T b) (k c)) :
    IK (VIT N S T b) (NonDet.gets (fun s : State Unit => s.curThread) >>= k) := by
  refine vi_bindQ _ (ik_gets _) ?_ hk
  intro σ hσ y hy
  rw [mem_gets_vi hy]; exact hσ.2.2.1

theorem vi_gisc_bind {β : Type} {k : ObjRef → NonDet (State Unit) β}
    (hk : ∀ c, c = S → IK (VIT N S T b) (k c)) :
    IK (VIT N S T b) (NonDet.gets (fun s : State Unit => s.idleSc) >>= k) := by
  refine vi_bindQ _ (ik_gets _) ?_ hk
  intro σ hσ y hy
  rw [mem_gets_vi hy]; exact hσ.2.1

theorem vi_git_bind {β : Type} {k : ObjRef → NonDet (State Unit) β}
    (hk : ∀ c, c = N → IK (VIT N S T b) (k c)) :
    IK (VIT N S T b) (NonDet.gets (fun s : State Unit => s.idleThread) >>= k) := by
  refine vi_bindQ _ (ik_gets _) ?_ hk
  intro σ hσ y hy
  rw [mem_gets_vi hy]; exact hσ.1

theorem vi_gsched_bind {β : Type} (t : ObjRef) {k : Bool → NonDet (State Unit) β}
    (hk : ∀ c, (c = true → t ≠ N) → IK (VIT N S T b) (k c)) :
    IK (VIT N S T b) (NonDet.gets (schedulable (Z := Unit) t) >>= k) := by
  refine vi_bindQ _ (ik_gets _) ?_ hk
  intro σ hσ y hy
  rw [mem_gets_vi hy]; exact vi_ne_of_schedulable hσ

theorem scWithReply_ne {σ : State Unit} (h : VIT N S T b σ) {r p : ObjRef} (hp : scWithReply r σ = some p) : p ≠ S := by
  rintro rfl
  have e := partialInv_some hp
  simp only [decide_eq_true_eq] at e
  obtain ⟨sc, n, hk, hr⟩ := e
  rw [((vi_obj h hk).1 rfl).2.1] at hr
  cases hr

theorem vi_gswr_bind {β : Type} (r : ObjRef) {k : Option ObjRef → NonDet (State Unit) β}
    (hk : ∀ o, o ≠ some S → IK (VIT N S T b) (k o)) :
    IK (VIT N S T b) (NonDet.gets (scWithReply (Z := Unit) r) >>= k) := by
  refine vi_bindQ _ (ik_gets _) ?_ hk
  intro σ hσ y hy
  rw [mem_gets_vi hy]
  intro e; exact scWithReply_ne hσ e rfl

/-- The general writers' side conditions from the facts in context. -/
macro "vi_side2" : tactic => `(tactic| first
  | vi_side
  | (intro hN; subst hN; simp_all [Fl4Spec.the, ObjOK, ScQ, runnable, receiveBlocked, tcbSchedContextUpdate, tcbYieldToUpdate, tcbBoundNotificationUpdate, scTcbUpdate, scRepliesUpdate, scYieldFromUpdate, scNtfnUpdate]; done)
  | (intro x hx; simp only [ObjOK] at hx ⊢;
     refine ⟨?_, ?_, ?_⟩ <;> intro hN <;> (try subst hN) <;> simp_all [Fl4Spec.the, ObjOK, ScQ, runnable, receiveBlocked, tcbSchedContextUpdate, tcbYieldToUpdate, tcbBoundNotificationUpdate, scTcbUpdate, scRepliesUpdate, scYieldFromUpdate, scNtfnUpdate]; done)
  | (intro sc n hx; simp only [ObjOK] at hx ⊢;
     refine ⟨?_, ?_⟩ <;> intro hN <;> (try subst hN) <;> simp_all [Fl4Spec.the, ObjOK, ScQ, runnable, receiveBlocked, tcbSchedContextUpdate, tcbYieldToUpdate, tcbBoundNotificationUpdate, scTcbUpdate, scRepliesUpdate, scYieldFromUpdate, scNtfnUpdate]; done)
  | (simp_all [Fl4Spec.the, ObjOK, ScQ, runnable, receiveBlocked, tcbSchedContextUpdate, tcbYieldToUpdate, tcbBoundNotificationUpdate, scTcbUpdate, scRepliesUpdate, scYieldFromUpdate, scNtfnUpdate]; done))

macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine vi_threadSet _ _ ?_); vi_side2))
macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine vi_updateSchedContext _ _ ?_); vi_side2))
macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine vi_setThreadState _ _ ?_); vi_side2))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gts_bind _ fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_tsc_bind _ fun _ _ _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_tsc_bind' _ fun _ _ _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_tyt_bind _ fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_tbn_bind _ fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gsc_bind _ fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gscTcb_bind _ fun _ _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gscRep_bind _ fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gep_bind _ fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gntfn_bind _ fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gct_bind fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gisc_bind fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_git_bind fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gsched_bind _ fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gswr_bind _ fun _ _ => ?_))

theorem vi_assert_bind {P : State Unit → Prop} {β : Type} (Q : Prop) {k : Unit → NonDet (State Unit) β}
    (hk : Q → IK P (k ())) : IK P (NonDet.assert Q >>= k) := by
  intro σ hσ x ⟨y, ⟨hq, e⟩, hx⟩
  rw [e] at hx; exact hk hq σ hσ x hx

theorem vi_assertOpt_bind {P : State Unit → Prop} {α β : Type} (o : Option α) {k : α → NonDet (State Unit) β}
    (hk : ∀ a, o = some a → IK P (k a)) : IK P (NonDet.assertOpt o >>= k) := by
  cases o with
  | none => exact fun _ _ _ ⟨_, hy, _⟩ => hy.elim
  | some a => exact ik_pure_bind' (hk a rfl)

macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_assert_bind _ fun _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_assertOpt_bind _ fun _ _ => ?_))

/-- `when` / `if` keeping their condition for the side goals (`ik_when` / `ik_ite` drop it). -/
theorem vi_when {P : State Unit → Prop} (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit}
    (h : Q → IK P m) : IK P (NonDet.when Q m) := by
  unfold NonDet.when; split
  · exact h ‹_›
  · exact ik_pure' _

theorem vi_ite {P : State Unit → Prop} {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α}
    (h1 : Q → IK P m1) (h2 : ¬ Q → IK P m2) : IK P (if Q then m1 else m2) := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_when _ fun _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_ite _ (fun _ => ?_) (fun _ => ?_)))

/-- `maybe_m` keeping the option's value for the side goals (`ik_maybeM` drops it). -/
theorem vi_maybeM {P : State Unit → Prop} {α : Type} {g : α → NonDet (State Unit) Unit} (o : Option α)
    (h : ∀ a, o = some a → IK P (g a)) : IK P (NonDet.maybeM g o) := by
  cases o
  · exact ik_pure' _
  · exact h _ rfl

macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_maybeM _ fun _ _ => ?_))

/-- `set_tcb_obj_ref tcb_sched_context_update t v` with the binding facts of the new value. -/
theorem vi_setTcbSc (t : ObjRef) (v : Option ObjRef) (h1 : t = N → v = some S) (h2 : t ≠ N → v ≠ some S)
    (h3 : t = T → v ≠ none) : IK (VIT N S T b) (setTcbObjRef (Z := Unit) tcbSchedContextUpdate t v) :=
  vi_threadSet _ _ fun x hx => by
    simp only [ObjOK, tcbSchedContextUpdate] at hx ⊢
    exact ⟨fun e => ⟨(hx.1 e).1, (hx.1 e).2.1, h1 e, (hx.1 e).2.2.2⟩, h2, h3⟩

/-- `set_sc_obj_ref sc_tcb_update p v` with the binding facts of the new value. -/
theorem vi_setScTcb (p : ObjRef) (v : Option ObjRef) (h1 : p = S → v = some N) (h2 : p ≠ S → v ≠ some N) :
    IK (VIT N S T b) (setScObjRef (Z := Unit) scTcbUpdate p v) :=
  vi_updateSchedContext _ _ fun sc n hx => by
    simp only [ObjOK, scTcbUpdate] at hx ⊢
    exact ⟨fun e => ⟨h1 e, (hx.1 e).2.1, (hx.1 e).2.2⟩, h2⟩

macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine vi_setTcbSc _ _ ?_ ?_ ?_) <;> vi_side2))
macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine vi_setScTcb _ _ ?_ ?_) <;> vi_side2))

/-! ## First hand lemmas (state-guarded writers) -/

theorem vi_schedContextCancelYieldTo (t : ObjRef) : IK (VIT N S T b) (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedContextCancelYieldTo _)

theorem vi_completeYieldTo (t : ObjRef) : IK (VIT N S T b) (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_completeYieldTo _)

theorem vi_unbindNotification (t : ObjRef) : IK (VIT N S T b) (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_unbindNotification _)

theorem vi_unbindMaybeNotification (n : ObjRef) : IK (VIT N S T b) (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_unbindMaybeNotification _)

theorem vi_schedContextUnbindYieldFrom (p : ObjRef) : IK (VIT N S T b) (schedContextUnbindYieldFrom (Z := Unit) p) := by
  unfold schedContextUnbindYieldFrom; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedContextUnbindYieldFrom _)

theorem vi_schedContextUnbindReply (p : ObjRef) : IK (VIT N S T b) (schedContextUnbindReply (Z := Unit) p) := by
  unfold schedContextUnbindReply; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedContextUnbindReply _)

theorem vi_replyUnlinkTcb (t r : ObjRef) : IK (VIT N S T b) (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_replyUnlinkTcb _ _)

theorem vi_schedContextUnbindTcb (p : ObjRef) (hp : p ≠ S) : IK (VI N S b) (schedContextUnbindTcb (Z := Unit) p) := by
  unfold schedContextUnbindTcb; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_schedContextUnbindTcb _ ?_; vi_side2))

theorem vi_schedContextUnbindAllTcbs (p : ObjRef) : IK (VI N S b) (schedContextUnbindAllTcbs (Z := Unit) p) := by
  unfold schedContextUnbindAllTcbs; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedContextUnbindAllTcbs _)

theorem vi_unbindFromSc (t : ObjRef) (ht : t ≠ N) : IK (VI N S b) (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_unbindFromSc _ ?_; vi_side2))

theorem vi_schedContextDonate (p t : ObjRef) (hp : p ≠ S) (ht : t ≠ N) :
    IK (VI N S b) (schedContextDonate (Z := Unit) p t) := by
  unfold schedContextDonate; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_schedContextDonate _ _ ?_ ?_ <;> vi_side2))

theorem vi_schedContextBindTcb (p t : ObjRef) (hp : p ≠ S) (ht : t ≠ N) :
    IK (VI N S b) (schedContextBindTcb (Z := Unit) p t) := by
  unfold schedContextBindTcb; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_schedContextBindTcb _ _ ?_ ?_ <;> vi_side2))

theorem vi_maybeReturnSc (n t : ObjRef) (ht : t ≠ N) : IK (VI N S b) (maybeReturnSc (Z := Unit) n t) := by
  unfold maybeReturnSc; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_maybeReturnSc _ _ ?_; vi_side2))

theorem vi_maybeDonateSc (t n : ObjRef) (ht : t ≠ N) : IK (VI N S b) (maybeDonateSc (Z := Unit) t n) := by
  unfold maybeDonateSc; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_maybeDonateSc _ _ ?_; vi_side2))

end

end Fl4Proofs.P3.SInvI
