/-
P3 (DESIGN.md §9), invariant line G1 (nq1): **NtfnQB, the queue half of l4v
`valid_ntfn`**: every thread in a notification's queue is a TCB
BlockedOnNotification on that notification (spec side only, outside the JAtZ
cone).

* `NtfnQB σ` and its consumer: `ctEntry_of` / `ctEntryI_of` turn "the current
  thread is active (or idle)" into ft3's per-entry premise `CtEntry` /
  `CtEntryI` (a queued thread is BlockedOnNotification, so not active).
* nq2: **EpQB, the queue half of l4v `valid_ep`** (every endpoint-queued
  thread is a TCB BlockedOnSend / BlockedOnReceive on that endpoint), carried
  with NtfnQB: NtfnQB alone is not inductive (`cancel_all_ipc` /
  `cancel_badged_sends` restart endpoint-queued threads without a
  BlockedOnNotification check).
* The carried form `NQ K σ := (NtfnQB σ ∧ EpQB σ) ∧` the threads of `K` are in
  no notification queue, not BlockedOnNotification and in no endpoint queue
  (`K` collects the threads whose state may be written: a thread read in a
  state other than BlockedOnNotification / BlockedOnSend / BlockedOnReceive,
  or just dequeued from a notification or an endpoint).
* Object writers: `nq_update` (`NqOK`: a TCB keeps its state or is in no
  queue, a TCB is replaced by a non-TCB only if in no queue, a notification's
  or an endpoint's new queue lies in its old one), `setObject`, `set_simple_ko`,
  `update_sk_obj_ref`, `thread_set` (state kept, or a thread of `K`),
  `arch_thread_set`, `as_user`, `set_mrs`, `set_cap`, `tcb_ntfn_dequeue`
  (the dequeued thread joins `K`: it was in that queue only), `tcb_ep_dequeue`
  (likewise, by EpQB),
  `set_thread_state` of a thread of `K`. Leaves of `nq_auto`.
-/
import Fl4Proofs.P3.SpecInvFaultTcbsH10
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

/-- **NtfnQB** (l4v `valid_ntfn`, the queue part): a thread in the queue of
the notification `n` is a TCB BlockedOnNotification on `n`. -/
def NtfnQB (σ : State Unit) : Prop :=
  ∀ n x t, σ.kheap n = some (.notification x) → t ∈ x.ntfnObj.ntfnQueue →
    ∃ y, σ.kheap t = some (.tcb y) ∧ y.tcbState = .blockedOnNotification n

/-- The `waitingNtfn` form of the statement. -/
theorem ntfnQB_iff (σ : State Unit) : NtfnQB σ ↔ ∀ n x q t, σ.kheap n = some (.notification x) →
    x.ntfnObj = .waitingNtfn q → t ∈ q →
    ∃ y, σ.kheap t = some (.tcb y) ∧ y.tcbState = .blockedOnNotification n := by
  constructor
  · intro h n x q t hn hq ht
    exact h n x t hn (by rw [hq]; exact ht)
  · intro h n x t hn ht
    cases hq : x.ntfnObj with
    | waitingNtfn q => exact h n x q t hn hq (by rw [hq] at ht; exact ht)
    | idleNtfn => rw [hq] at ht; simp [Ntfn.ntfnQueue] at ht
    | activeNtfn _ => rw [hq] at ht; simp [Ntfn.ntfnQueue] at ht

theorem NtfnQB.tcb {σ : State Unit} (h : NtfnQB σ) {t : ObjRef} (ht : queued σ t) :
    ∃ y, σ.kheap t = some (.tcb y) ∧ isBoN y.tcbState := by
  obtain ⟨n, x, hn, hq⟩ := ht
  obtain ⟨y, hy, hs⟩ := h n x t hn hq
  exact ⟨y, hy, by rw [hs]; trivial⟩

theorem NtfnQB.not_queued {σ : State Unit} (h : NtfnQB σ) {t : ObjRef}
    (ht : ∀ y, σ.kheap t = some (.tcb y) → ¬ isBoN y.tcbState) : ¬ queued σ t := by
  intro hq
  obtain ⟨y, hy, hb⟩ := h.tcb hq
  exact ht y hy hb

/-- A queued thread is in that one queue only. -/
theorem NtfnQB.uniq {σ : State Unit} (h : NtfnQB σ) {t n m : ObjRef} {x z : Notification}
    (hn : σ.kheap n = some (.notification x)) (ht : t ∈ x.ntfnObj.ntfnQueue)
    (hm : σ.kheap m = some (.notification z)) (ht' : t ∈ z.ntfnObj.ntfnQueue) : m = n := by
  obtain ⟨y, hy, hs⟩ := h n x t hn ht
  obtain ⟨y', hy', hs'⟩ := h m z t hm ht'
  rw [hy] at hy'; cases hy'
  rw [hs] at hs'; cases hs'; rfl

/-- **The consumer**: an active current thread is in no notification queue, so
ft3's entry premise `CtEntry` needs only "ct active". -/
theorem ctEntry_of {σ : State Unit} (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (h : NtfnQB σ) : CtEntry σ := by
  refine ⟨ha, h.not_queued fun y hy hb => ?_⟩
  have := ha y hy
  revert this hb; cases y.tcbState <;> simp [activeSt, isBoN]

/-- The interrupt form: active or idle. -/
theorem ctEntryI_of {σ : State Unit}
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ x.tcbState = .idleThreadState)
    (h : NtfnQB σ) : CtEntryI σ := by
  refine ⟨ha, h.not_queued fun y hy hb => ?_⟩
  rcases ha y hy with h1 | h1
  · revert h1 hb; cases y.tcbState <;> simp [activeSt, isBoN]
  · rw [h1] at hb; exact hb

/-- Every event: an active current thread suffices. -/
theorem ctEntryEv_of {σ : State Unit} (ev : Event)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) (h : NtfnQB σ) : CtEntryEv ev σ := by
  unfold CtEntryEv
  split
  · exact ctEntryI_of (fun x hx => Or.inl (ha x hx)) h
  · exact ctEntry_of ha h

/-- **NtfnQB at boot** (no notification exists). -/
theorem boot_ntfnQB : NtfnQB (initASt (Z := Unit)) := by
  intro n x t hn _
  simp only [initASt, initKheap, Function.update_apply] at hn
  split_ifs at hn <;> (try cases hn)
  all_goals (split_ifs at hn <;> cases hn)

/-! ## EpQB -/

/-- `t` is in some endpoint's queue. -/
def queuedE (σ : State Unit) (t : ObjRef) : Prop :=
  ∃ e x, σ.kheap e = some (.endpoint x) ∧ t ∈ x.epQueue

/-- **EpQB** (l4v `valid_ep`, the queue part): a thread in the queue of the
endpoint `e` is a TCB BlockedOnSend / BlockedOnReceive on `e`. -/
def EpQB (σ : State Unit) : Prop :=
  ∀ e x t, σ.kheap e = some (.endpoint x) → t ∈ x.epQueue →
    ∃ y, σ.kheap t = some (.tcb y) ∧ epBlocked y.tcbState = some e

theorem EpQB.not_queuedE {σ : State Unit} (h : EpQB σ) {t : ObjRef}
    (ht : ∀ y, σ.kheap t = some (.tcb y) → epBlocked y.tcbState = none) : ¬ queuedE σ t := by
  rintro ⟨e, x, he, hq⟩
  obtain ⟨y, hy, hs⟩ := h e x t he hq
  rw [ht y hy] at hs; cases hs

/-- An endpoint-queued thread is in that one queue only. -/
theorem EpQB.uniq {σ : State Unit} (h : EpQB σ) {t e m : ObjRef} {x z : Endpoint}
    (he : σ.kheap e = some (.endpoint x)) (ht : t ∈ x.epQueue)
    (hm : σ.kheap m = some (.endpoint z)) (ht' : t ∈ z.epQueue) : m = e := by
  obtain ⟨y, hy, hs⟩ := h e x t he ht
  obtain ⟨y', hy', hs'⟩ := h m z t hm ht'
  rw [hy] at hy'; cases hy'
  rw [hs] at hs'; cases hs'; rfl

/-- An endpoint-queued thread is a TCB not BlockedOnNotification. -/
theorem EpQB.not_boN {σ : State Unit} (h : EpQB σ) {t e : ObjRef} {x : Endpoint}
    (he : σ.kheap e = some (.endpoint x)) (ht : t ∈ x.epQueue) :
    ∃ y, σ.kheap t = some (.tcb y) ∧ ¬ isBoN y.tcbState := by
  obtain ⟨y, hy, hs⟩ := h e x t he ht
  refine ⟨y, hy, ?_⟩
  revert hs; cases y.tcbState <;> simp [epBlocked, isBoN]

/-- **EpQB at boot** (no endpoint exists). -/
theorem boot_epQB : EpQB (initASt (Z := Unit)) := by
  intro n x t hn _
  simp only [initASt, initKheap, Function.update_apply] at hn
  split_ifs at hn <;> (try cases hn)
  all_goals (split_ifs at hn <;> cases hn)

theorem epQueue_updateEpQueue (ep : Endpoint) (q : List ObjRef) (b : Bool) :
    (updateEpQueue ep q b).epQueue = q := by
  cases ep <;> cases b <;> rfl

/-! ## The carried form -/

/-- NtfnQB and EpQB, and the threads of `K` are in no notification queue, not
BlockedOnNotification (so a queue write adding a BlockedOnNotification thread
never adds one of `K`) and in no endpoint queue. -/
def NQ (K : List ObjRef) (σ : State Unit) : Prop :=
  (NtfnQB σ ∧ EpQB σ) ∧ ∀ u ∈ K, ¬ queued σ u ∧ (∀ y, σ.kheap u = some (.tcb y) → ¬ isBoN y.tcbState) ∧
    ¬ queuedE σ u

abbrev NQK {α : Type} (K : List ObjRef) (m : NonDet (State Unit) α) : Prop := IK (NQ K) m
abbrev NQKE {ε α : Type} (K : List ObjRef) (m : NonDetE (State Unit) ε α) : Prop := IKE (NQ K) m

theorem nq_nil_iff (σ : State Unit) : NQ [] σ ↔ NtfnQB σ ∧ EpQB σ :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ h => by simp at h⟩⟩

theorem nq_mono {K K' : List ObjRef} {σ : State Unit} (h : NQ K σ) (hK : ∀ u ∈ K', u ∈ K) : NQ K' σ :=
  ⟨h.1, fun u hu => h.2 u (hK u hu)⟩

/-- A thread with the three facts joins `K`. -/
theorem nq_consQ {K : List ObjRef} {σ : State Unit} (h : NQ K σ) {t : ObjRef} (h1 : ¬ queued σ t)
    (h2 : ∀ y, σ.kheap t = some (.tcb y) → ¬ isBoN y.tcbState) (h3 : ¬ queuedE σ t) : NQ (t :: K) σ := by
  refine ⟨h.1, fun u hu => ?_⟩
  rcases List.mem_cons.1 hu with rfl | hu
  · exact ⟨h1, h2, h3⟩
  · exact h.2 u hu

/-- A thread in a state other than BlockedOnNotification / BlockedOnSend /
BlockedOnReceive joins `K`. -/
theorem nq_cons {K : List ObjRef} {σ : State Unit} (h : NQ K σ) {t : ObjRef}
    (hb : ∀ y, σ.kheap t = some (.tcb y) → ¬ isBoN y.tcbState ∧ epBlocked y.tcbState = none) :
    NQ (t :: K) σ :=
  nq_consQ h (h.1.1.not_queued fun y hy => (hb y hy).1) (fun y hy => (hb y hy).1)
    (h.1.2.not_queuedE fun y hy => (hb y hy).2)

theorem nq_consR {K : List ObjRef} {σ : State Unit} (h : NQ K σ) {t : ObjRef} {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) (hs : ¬ isBoN x.tcbState) (he : epBlocked x.tcbState = none) :
    NQ (t :: K) σ :=
  nq_cons h fun y hy => by rw [hx] at hy; cases hy; exact ⟨hs, he⟩

theorem nq_tail {K : List ObjRef} {σ : State Unit} {t : ObjRef} (h : NQ (t :: K) σ) : NQ K σ :=
  nq_mono h fun _ h => List.mem_cons_of_mem _ h

theorem mem_filter_ne' {K : List ObjRef} {t u : ObjRef} (h : u ∈ K.filter (· ≠ t)) : u ∈ K ∧ u ≠ t := by
  simpa using h

/-! ## One heap write -/

/-- When a heap write at `p` (old object `o0`, new `o`) keeps `NQ`. -/
def NqOK (K : List ObjRef) (σ : State Unit) (p : ObjRef) (o0 o : KernelObject) : Prop :=
  (∀ y y', o0 = .tcb y → o = .tcb y' → y'.tcbState = y.tcbState ∨ (¬ queued σ p ∧ ¬ queuedE σ p)) ∧
  (∀ y, o0 = .tcb y → (∀ y', o ≠ .tcb y') → ¬ queued σ p ∧ ¬ queuedE σ p) ∧
  (∀ x', o = .notification x' → ∀ t ∈ x'.ntfnObj.ntfnQueue,
    ∃ x, o0 = .notification x ∧ t ∈ x.ntfnObj.ntfnQueue) ∧
  (∀ x', o = .endpoint x' → ∀ t ∈ x'.epQueue, ∃ x, o0 = .endpoint x ∧ t ∈ x.epQueue) ∧
  (p ∈ K → ∀ y', o = .tcb y' → isBoN y'.tcbState → ∃ y, o0 = .tcb y ∧ isBoN y.tcbState)

theorem nqok_tcb {K : List ObjRef} {σ : State Unit} {p : ObjRef} {y y' : Tcb} (hs : y'.tcbState = y.tcbState) :
    NqOK K σ p (.tcb y) (.tcb y') :=
  ⟨fun _ _ h1 h2 => (by cases h1; cases h2; exact Or.inl hs), fun _ _ h2 => absurd rfl (h2 y'),
    fun _ h => (by cases h), fun _ h => (by cases h), fun _ _ h hb => (by cases h; exact ⟨y, rfl, hs ▸ hb⟩)⟩

/-- A state write of a thread in no queue, the new state not BlockedOnNotification. -/
theorem nqok_sts {K : List ObjRef} {σ : State Unit} {p : ObjRef} {y y' : Tcb} (hq : ¬ queued σ p)
    (hqe : ¬ queuedE σ p) (hb : ¬ isBoN y'.tcbState) : NqOK K σ p (.tcb y) (.tcb y') :=
  ⟨fun _ _ _ _ => Or.inr ⟨hq, hqe⟩, fun _ _ _ => ⟨hq, hqe⟩, fun _ h => (by cases h), fun _ h => (by cases h),
    fun _ _ h hb' => by cases h; exact absurd hb' hb⟩

/-- A state write of a thread in no queue and not in `K` (any new state). -/
theorem nqok_stsK {K : List ObjRef} {σ : State Unit} {p : ObjRef} {y y' : Tcb} (hq : ¬ queued σ p)
    (hqe : ¬ queuedE σ p) (hK : p ∉ K) : NqOK K σ p (.tcb y) (.tcb y') :=
  ⟨fun _ _ _ _ => Or.inr ⟨hq, hqe⟩, fun _ _ _ => ⟨hq, hqe⟩, fun _ h => (by cases h), fun _ h => (by cases h),
    fun h => absurd h hK⟩

theorem nqok_ntfn {K : List ObjRef} {σ : State Unit} {p : ObjRef} {x0 x' : Notification}
    (hsub : ∀ u ∈ x'.ntfnObj.ntfnQueue, u ∈ x0.ntfnObj.ntfnQueue) : NqOK K σ p (.notification x0) (.notification x') :=
  ⟨fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ h u hu => (by cases h; exact ⟨x0, rfl, hsub u hu⟩),
    fun _ h => (by cases h), fun _ _ h => by cases h⟩

theorem nqok_ep {K : List ObjRef} {σ : State Unit} {p : ObjRef} {x0 x' : Endpoint}
    (hsub : ∀ u ∈ x'.epQueue, u ∈ x0.epQueue) : NqOK K σ p (.endpoint x0) (.endpoint x') :=
  ⟨fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h),
    fun _ h u hu => (by cases h; exact ⟨x0, rfl, hsub u hu⟩), fun _ _ h => by cases h⟩

theorem queued_update {σ : State Unit} {p : ObjRef} {o0 o : KernelObject} (hp : σ.kheap p = some o0)
    (h3 : ∀ x', o = .notification x' → ∀ t ∈ x'.ntfnObj.ntfnQueue,
      ∃ x, o0 = .notification x ∧ t ∈ x.ntfnObj.ntfnQueue)
    {u : ObjRef} (hu : queued { σ with kheap := Function.update σ.kheap p (some o) } u) : queued σ u := by
  obtain ⟨n, x, hn, hq⟩ := hu
  dsimp only at hn
  rw [Function.update_apply] at hn
  split_ifs at hn with e
  · subst e
    cases hn
    obtain ⟨x0, rfl, h0⟩ := h3 x rfl u hq
    exact ⟨n, x0, hp, h0⟩
  · exact ⟨n, x, hn, hq⟩

theorem queuedE_update {σ : State Unit} {p : ObjRef} {o0 o : KernelObject} (hp : σ.kheap p = some o0)
    (h3 : ∀ x', o = .endpoint x' → ∀ t ∈ x'.epQueue, ∃ x, o0 = .endpoint x ∧ t ∈ x.epQueue)
    {u : ObjRef} (hu : queuedE { σ with kheap := Function.update σ.kheap p (some o) } u) : queuedE σ u := by
  obtain ⟨n, x, hn, hq⟩ := hu
  dsimp only at hn
  rw [Function.update_apply] at hn
  split_ifs at hn with e
  · subst e
    cases hn
    obtain ⟨x0, rfl, h0⟩ := h3 x rfl u hq
    exact ⟨n, x0, hp, h0⟩
  · exact ⟨n, x, hn, hq⟩

theorem nq_update {K : List ObjRef} {σ : State Unit} {p : ObjRef} {o0 o : KernelObject} (h : NQ K σ)
    (hp : σ.kheap p = some o0) (hok : NqOK K σ p o0 o) :
    NQ K { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨hT, hS, hN, hE, hB⟩ := hok
  refine ⟨⟨fun n x t hn ht => ?_, fun n x t hn ht => ?_⟩, fun u hu =>
    ⟨fun hq => (h.2 u hu).1 (queued_update hp hN hq), fun y hy hb => ?_,
      fun hq => (h.2 u hu).2.2 (queuedE_update hp hE hq)⟩⟩
  · dsimp only at hn
    rw [Function.update_apply] at hn
    split_ifs at hn with e
    · subst e
      cases hn
      obtain ⟨x0, rfl, h0⟩ := hN x rfl t ht
      obtain ⟨y, hy, hs⟩ := h.1.1 n x0 t hp h0
      have htn : t ≠ n := by rintro rfl; rw [hp] at hy; cases hy
      refine ⟨y, ?_, hs⟩
      dsimp only; rw [Function.update_apply, if_neg htn]; exact hy
    · obtain ⟨y, hy, hs⟩ := h.1.1 n x t hn ht
      have hqt : queued σ t := ⟨n, x, hn, ht⟩
      by_cases et : t = p
      · subst et
        rw [hp] at hy; cases hy
        by_cases hoT : ∃ y', o = .tcb y'
        · obtain ⟨y', rfl⟩ := hoT
          rcases hT y y' rfl rfl with h1 | h1
          · exact ⟨y', by simp, by rw [h1, hs]⟩
          · exact absurd hqt h1.1
        · exact absurd hqt (hS y rfl fun y' e => hoT ⟨y', e⟩).1
      · refine ⟨y, ?_, hs⟩
        dsimp only; rw [Function.update_apply, if_neg et]; exact hy
  · dsimp only at hn
    rw [Function.update_apply] at hn
    split_ifs at hn with e
    · subst e
      cases hn
      obtain ⟨x0, rfl, h0⟩ := hE x rfl t ht
      obtain ⟨y, hy, hs⟩ := h.1.2 n x0 t hp h0
      have htn : t ≠ n := by rintro rfl; rw [hp] at hy; cases hy
      refine ⟨y, ?_, hs⟩
      dsimp only; rw [Function.update_apply, if_neg htn]; exact hy
    · obtain ⟨y, hy, hs⟩ := h.1.2 n x t hn ht
      have hqt : queuedE σ t := ⟨n, x, hn, ht⟩
      by_cases et : t = p
      · subst et
        rw [hp] at hy; cases hy
        by_cases hoT : ∃ y', o = .tcb y'
        · obtain ⟨y', rfl⟩ := hoT
          rcases hT y y' rfl rfl with h1 | h1
          · exact ⟨y', by simp, by rw [h1, hs]⟩
          · exact absurd hqt h1.2
        · exact absurd hqt (hS y rfl fun y' e => hoT ⟨y', e⟩).2
      · refine ⟨y, ?_, hs⟩
        dsimp only; rw [Function.update_apply, if_neg et]; exact hy
  · dsimp only at hy
    rw [Function.update_apply] at hy
    split_ifs at hy with e
    · subst e
      cases hy
      obtain ⟨y0, rfl, hb0⟩ := hB hu y rfl hb
      exact (h.2 u hu).2.1 y0 hp hb0
    · exact (h.2 u hu).2.1 y hy hb

/-- After a notification write at `n` whose new queue lacks `t`, `t` (queued at `n` before) is in no queue. -/
theorem not_queued_update {σ : State Unit} {n t : ObjRef} {x0 x' : Notification} (hσ : NtfnQB σ)
    (hn : σ.kheap n = some (.notification x0)) (ht0 : t ∈ x0.ntfnObj.ntfnQueue) (ht : t ∉ x'.ntfnObj.ntfnQueue) :
    ¬ queued { σ with kheap := Function.update σ.kheap n (some (.notification x')) } t := by
  rintro ⟨m, x, hm, hq⟩
  dsimp only at hm
  rw [Function.update_apply] at hm
  split_ifs at hm with e
  · cases hm; exact ht hq
  · exact e (hσ.uniq hn ht0 hm hq)

theorem nq_setObject_p {K : List ObjRef} (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : NQ K σ → ∀ o0, σ.kheap p = some o0 → aType o0 = aType o → NqOK K σ p o0 o) :
    IKp (NQ K) σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, e2⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at e2 hk; subst y2
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact nq_update hσ hk (ho hσ y1 hk hty)

/-- `setObject` of an object that is no TCB, no notification and no endpoint
with a queue (its type is kept, so the old one was no TCB). -/
theorem nq_setObject {K : List ObjRef} (p : ObjRef) (o : KernelObject) (h1 : ∀ y, o ≠ .tcb y)
    (h2 : ∀ x, o ≠ .notification x) (h4 : ∀ x, o = .endpoint x → x.epQueue = [])
    (h3 : ∀ y, aType (.tcb y) ≠ aType o) : NQK K (setObject (Z := Unit) p o) :=
  fun σ => nq_setObject_p p o σ fun _ o0 _ hty =>
    ⟨fun _ y' _ e => absurd e (h1 y'), fun y e _ => (by subst e; exact absurd hty (h3 y)),
      fun x' e => absurd e (h2 x'), fun x' e t ht => (by rw [h4 x' e] at ht; simp at ht),
      fun _ y' e => absurd e (h1 y')⟩

theorem simple_not_tcb {o : KernelObject} (hs : isSimpleType o) (y : Tcb) : o ≠ .tcb y := by
  rintro rfl; simp [isSimpleType, aType] at hs

theorem mem_setSimpleKo {α : Type} [Nonempty α] {f : α → KernelObject} {p : ObjRef} {e : α} {σ : State Unit}
    {y : Unit × State Unit} (h : y ∈ (setSimpleKo (Z := Unit) f p e σ).1) :
    ∃ o0, σ.kheap p = some o0 ∧ isSimpleType o0 ∧ isSimpleType (f e) ∧
      y.2 = { σ with kheap := Function.update σ.kheap p (some (f e)) } := by
  unfold setSimpleKo setObject at h
  obtain ⟨y1, hy1, h⟩ := h
  obtain ⟨hk, e2⟩ := mem_getObject hy1
  obtain ⟨o0, s1⟩ := y1
  simp only at hk e2; subst s1
  obtain ⟨z, ⟨hs, rfl⟩, h⟩ := h
  obtain ⟨z, ⟨-, rfl⟩, h⟩ := h
  obtain ⟨y3, hy3, h⟩ := h
  obtain ⟨hk3, e3⟩ := mem_getObject hy3
  obtain ⟨o3, s3⟩ := y3
  simp only at e3 hk3; subst s3
  rw [hk] at hk3; cases hk3
  obtain ⟨z, ⟨hty, rfl⟩, h⟩ := h
  obtain ⟨w, hw, h⟩ := h
  rw [Set.mem_singleton_iff.1 hw] at h
  refine ⟨o0, hk, hs, ?_, by rw [Set.mem_singleton_iff.1 h]⟩
  show aType (f e) ∈ _
  rw [← hty]; exact hs

/-- `set_simple_ko`, the new queue (if a notification or an endpoint) inside the old object's. -/
theorem nq_setSimpleKo_p {K : List ObjRef} {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α)
    (σ : State Unit)
    (he : NQ K σ → ∀ o0, σ.kheap p = some o0 → ∀ x', f e = .notification x' → ∀ t ∈ x'.ntfnObj.ntfnQueue,
      ∃ x, o0 = .notification x ∧ t ∈ x.ntfnObj.ntfnQueue)
    (hee : NQ K σ → ∀ o0, σ.kheap p = some o0 → ∀ x', f e = .endpoint x' → ∀ t ∈ x'.epQueue,
      ∃ x, o0 = .endpoint x ∧ t ∈ x.epQueue) :
    IKp (NQ K) σ (setSimpleKo (Z := Unit) f p e) := by
  intro hσ x hx
  obtain ⟨o0, hk, hs, hs', e2⟩ := mem_setSimpleKo hx
  rw [e2]
  exact nq_update hσ hk ⟨fun y _ e1 _ => absurd e1 (simple_not_tcb hs y),
    fun y e1 _ => absurd e1 (simple_not_tcb hs y), he hσ o0 hk, hee hσ o0 hk,
    fun _ y' e1 => absurd e1 (simple_not_tcb hs' y')⟩

/-- `set_simple_ko` of a reply, or a notification / endpoint with an empty queue. -/
theorem nq_setSimpleKo {K : List ObjRef} {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α)
    (he : ∀ x', f e = .notification x' → x'.ntfnObj.ntfnQueue = [])
    (hee : ∀ x', f e = .endpoint x' → x'.epQueue = []) :
    NQK K (setSimpleKo (Z := Unit) f p e) :=
  fun σ => nq_setSimpleKo_p f p e σ (fun _ _ _ x' hx t ht => by rw [he x' hx] at ht; simp at ht)
    (fun _ _ _ x' hx t ht => by rw [hee x' hx] at ht; simp at ht)

/-- `update_sk_obj_ref` of a field that is not the queue. -/
theorem nq_updateSkObjRef {K : List ObjRef} {α : Type} [Nonempty α] (Ck : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef)
    (hf : ∀ a x', Ck (f (fun _ => new) a) = .notification x' →
      ∃ x, Ck a = .notification x ∧ ∀ t ∈ x'.ntfnObj.ntfnQueue, t ∈ x.ntfnObj.ntfnQueue)
    (hfe : ∀ a x', Ck (f (fun _ => new) a) = .endpoint x' →
      ∃ x, Ck a = .endpoint x ∧ ∀ t ∈ x'.epQueue, t ∈ x.epQueue) :
    NQK K (updateSkObjRef (Z := Unit) Ck f ref new) := by
  unfold updateSkObjRef
  exact ik_getSimpleKo_bind fun σ a ha => nq_setSimpleKo_p _ _ _ σ (fun _ o0 hp x' hx t ht => by
    obtain ⟨x, hx0, hsub⟩ := hf a x' hx
    rw [ha] at hp; cases hp
    exact ⟨x, hx0, hsub t ht⟩) (fun _ o0 hp x' hx t ht => by
    obtain ⟨x, hx0, hsub⟩ := hfe a x' hx
    rw [ha] at hp; cases hp
    exact ⟨x, hx0, hsub t ht⟩)

/-- NQ and `t` in no notification queue and no endpoint queue. -/
def NQq (K : List ObjRef) (t : ObjRef) (σ : State Unit) : Prop := NQ K σ ∧ ¬ queued σ t ∧ ¬ queuedE σ t

/-- `tcb_ntfn_dequeue`: the queue shrinks, and the dequeued thread is in no
queue afterwards (by NtfnQB it was in this queue only). -/
theorem nq_tcbNtfnDequeue_post {K : List ObjRef} (t n : ObjRef) :
    HK (NQ K) (NQq K t) (tcbNtfnDequeue (Z := Unit) t n) := by
  intro σ hσ y hy
  unfold tcbNtfnDequeue at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst e1
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨hq, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  dsimp only at hy
  obtain ⟨o0, -, -, -, e⟩ := mem_setSimpleKo hy
  rw [e]
  have hsub : ∀ u ∈ (ntfnObjUpdate (fun _ => match removeAll t a.ntfnObj.ntfnQueue with
      | [] => Ntfn.idleNtfn
      | _ => Ntfn.waitingNtfn (removeAll t a.ntfnObj.ntfnQueue)) a).ntfnObj.ntfnQueue,
      u ∈ removeAll t a.ntfnObj.ntfnQueue := by
    intro u hu
    simp only [ntfnObjUpdate] at hu
    split at hu
    · simp [Ntfn.ntfnQueue] at hu
    · simpa only [Ntfn.ntfnQueue] using hu
  obtain ⟨yt, hyt, hst⟩ := hσ.1.1 n a t hk hq
  refine ⟨nq_update hσ hk (nqok_ntfn fun u hu => removeAll_sub (hsub u hu)),
    not_queued_update hσ.1.1 hk hq fun h => ?_, fun he => ?_⟩
  · have := (List.mem_filter.1 (hsub t h)).2
    simp at this
  · refine hσ.1.2.not_queuedE (fun y hy => ?_) (queuedE_update hk (fun x' h => by cases h) he)
    rw [hyt] at hy; cases hy; rw [hst]; rfl

theorem nq_tcbNtfnDequeue {K : List ObjRef} (t n : ObjRef) : NQK K (tcbNtfnDequeue (Z := Unit) t n) :=
  fun σ hσ y hy => (nq_tcbNtfnDequeue_post t n σ hσ y hy).1

theorem upd_ne {σ : State Unit} {p q : ObjRef} {o : KernelObject} (h : q ≠ p) :
    ({ σ with kheap := Function.update σ.kheap p (some o) } : State Unit).kheap q = σ.kheap q := by
  dsimp only; rw [Function.update_apply, if_neg h]

/-- `tcb_ep_dequeue`: the queue shrinks, and the dequeued thread joins `K`
(by EpQB it was BlockedOnSend / BlockedOnReceive on that endpoint, so in no
notification queue, and in no other endpoint queue). -/
theorem nq_tcbEpDequeue_post {K : List ObjRef} (t e : ObjRef) :
    HK (NQ K) (NQ (t :: K)) (tcbEpDequeue (Z := Unit) t e) := by
  intro σ hσ y hy
  unfold tcbEpDequeue at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst e1
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨hq, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  dsimp only at hy
  obtain ⟨o0, -, -, -, ee⟩ := mem_setSimpleKo hy
  rw [ee]
  have hsub : ∀ u ∈ (match removeAll t a.epQueue with
      | [] => Endpoint.idleEP
      | _ => updateEpQueue a (removeAll t a.epQueue) true).epQueue,
      u ∈ removeAll t a.epQueue := by
    intro u hu
    split at hu
    · simp [Endpoint.epQueue] at hu
    · rwa [epQueue_updateEpQueue] at hu
  obtain ⟨yt, hyt, hbt⟩ := hσ.1.2.not_boN hk hq
  have hte : t ≠ e := by rintro rfl; rw [hk] at hyt; cases hyt
  refine nq_consQ (nq_update hσ hk (nqok_ep fun u hu => removeAll_sub (hsub u hu))) ?_ ?_ ?_
  · intro hq'
    refine hσ.1.1.not_queued (fun y hy hb => ?_) (queued_update hk (fun x' h => by cases h) hq')
    rw [hyt] at hy; cases hy; exact hbt hb
  · intro y' hy'
    rw [upd_ne hte, hyt] at hy'; cases hy'; exact hbt
  · rintro ⟨m, x, hm, hmq⟩
    dsimp only at hm
    rw [Function.update_apply] at hm
    split_ifs at hm with em
    · cases hm
      have := (List.mem_filter.1 (hsub t hmq)).2
      simp at this
    · exact em (hσ.1.2.uniq hk hq hm hmq)

theorem nq_tcbEpDequeue {K : List ObjRef} (t e : ObjRef) : NQK K (tcbEpDequeue (Z := Unit) t e) :=
  fun σ hσ y hy => nq_tail (nq_tcbEpDequeue_post t e σ hσ y hy)

theorem mem_threadSet {f : Tcb → Tcb} {t : ObjRef} {σ : State Unit} {y : Unit × State Unit}
    (h : y ∈ (threadSet (Z := Unit) f t σ).1) :
    ∃ x, σ.kheap t = some (.tcb x) ∧ y.2 = { σ with kheap := Function.update σ.kheap t (some (.tcb (f x))) } := by
  unfold threadSet setObject at h
  obtain ⟨y1, hy1, h⟩ := h
  unfold NonDet.getsThe at hy1
  cases e : getTcb t σ with
  | none => rw [e] at hy1; exact hy1.elim
  | some x =>
    rw [e] at hy1
    rw [Set.mem_singleton_iff.1 hy1] at h
    obtain ⟨y3, hy3, h⟩ := h
    obtain ⟨-, e3⟩ := mem_getObject hy3
    obtain ⟨o3, s3⟩ := y3
    simp only at e3; subst s3
    obtain ⟨z, ⟨-, rfl⟩, h⟩ := h
    obtain ⟨w, hw, h⟩ := h
    rw [Set.mem_singleton_iff.1 hw] at h
    exact ⟨x, getTcb_kheap e, by rw [Set.mem_singleton_iff.1 h]⟩

section W
variable {K : List ObjRef}

theorem nq_threadSet (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, (f x).tcbState = x.tcbState) :
    NQK K (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => nq_setObject_p _ _ σ fun _ o0 hp _ => ?_
  rw [getTcb_kheap hx] at hp; cases hp
  exact nqok_tcb (hf x)

theorem nq_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : NQK K (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  refine ik_getsThe_bind fun x σ hx => nq_setObject_p _ _ σ fun _ o0 hp _ => ?_
  rw [getTcb_kheap hx] at hp; cases hp
  exact nqok_tcb rfl

theorem nq_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : NQK K (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (nq_setObject_p _ _ σ fun _ o0 hp _ => ?_) fun _ => ik_pure _
  rw [getTcb_kheap hx] at hp; cases hp
  exact nqok_tcb rfl

theorem nq_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : NQK K (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (nq_setObject_p _ _ σ fun _ o0 hp _ => ?_) fun _ => ?_
  · rw [getTcb_kheap hx] at hp; cases hp
    exact nqok_tcb rfl
  · ti_mach

theorem nq_setCap (c : Cap) (sl : CslotPtr) : NQK K (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · refine ikp_pure_bind (nq_setObject_p _ _ σ fun _ o0 hp _ => ?_)
      rw [hk] at hp; cases hp
      exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h),
        fun _ _ h => by cases h⟩
    · exact ikp_fail_bind
  · rename_i tcb
    have hq : ∀ o0, σ.kheap o = some o0 → ∀ y' : Tcb, y'.tcbState = tcb.tcbState →
        NqOK K σ o o0 (.tcb y') := by
      intro o0 hp y' hs
      rw [hk] at hp; cases hp
      exact nqok_tcb hs
    split
    · exact ikp_pure_bind (nq_setObject_p _ _ σ fun _ o0 hp _ => hq o0 hp _ rfl)
    split
    · exact ikp_pure_bind (nq_setObject_p _ _ σ fun _ o0 hp _ => hq o0 hp _ rfl)
    split
    · exact ikp_pure_bind (nq_setObject_p _ _ σ fun _ o0 hp _ => hq o0 hp _ rfl)
    split
    · exact ikp_pure_bind (nq_setObject_p _ _ σ fun _ o0 hp _ => hq o0 hp _ rfl)
    split
    · exact ikp_pure_bind (nq_setObject_p _ _ σ fun _ o0 hp _ => hq o0 hp _ rfl)
    split
    · exact ikp_pure_bind (nq_setObject_p _ _ σ fun _ o0 hp _ => hq o0 hp _ rfl)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem nq_doMachineOp {α : Type} (mop : NonDet MachineState α) : NQK K (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) _

theorem nq_doExtendedOp (eop : DetExtMonad Unit) : NQK K (doExtendedOp (Z := Unit) eop) :=
  ik_doExtendedOp (fun _ _ h => h) _

theorem nq_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbState = x.tcbState) : NQK K (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact nq_threadSet _ _ (h _)

end W

/-! ## The automation -/

set_option maxErrors 2000

macro "nq_side" : tactic => `(tactic| first
  | (intro _; rfl)
  | (intro _ _; rfl)
  | (intro _ h; cases h; done)
  | (intro _ h; cases h; rfl)
  | (intro _ h; cases h; simp [ntfnObjUpdate, Ntfn.ntfnQueue]; done)
  | (intro _ h; cases h; simp [Endpoint.epQueue]; done)
  | (intro _ _ h; cases h; done)
  | (intro _ _ h; cases h; exact ⟨_, rfl, fun _ h => h⟩)
  | (intro _ h; simp [aType] at h; done)
  | (intro _ h; simp [aType, aaType] at h; done)
  | (intro _ h; revert h; simp only [aType]; split <;> intro h <;> cases h))

/-- Membership of a thread in `K`. -/
macro "nq_mem" : tactic => `(tactic| first | assumption | (simp; done) | (exact List.mem_cons_of_mem _ (by assumption)) | (exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by assumption))) | (simp_all; done))

syntax "nq_leaf" : tactic
macro_rules | `(tactic| nq_leaf) => `(tactic| fail "no nq_leaf")

macro "nq_auto" : tactic => `(tactic| repeat' (first | nq_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_doMachineOp _)
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_doExtendedOp _)
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_setObject _ _ ?_ ?_ ?_ ?_) <;> nq_side))
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_setSimpleKo _ _ _ ?_ ?_) <;> nq_side))
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_threadSet _ _ ?_); nq_side))
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archThreadSet _ _)
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_asUser _ _)
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setMrs _ _ _)
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setCap _ _)
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_updateSkObjRef _ _ _ _ ?_ ?_) <;> nq_side))
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_tcbNtfnDequeue _ _)
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_tcbEpDequeue _ _)
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_optionUpdateThread _ _ _ ?_); intro _ _; rfl))

theorem nq_setThreadStateAct' {K : List ObjRef} (t : ObjRef) : NQK K (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct setSchedulerAction; nq_auto

/-- `set_thread_state` of a thread in no queue, the new state not BlockedOnNotification. -/
theorem nq_setThreadState_q {K : List ObjRef} (t : ObjRef) (ts : ThreadState) (hts : ¬ isBoN ts) :
    HK (NQq K t) (NQ (t :: K)) (setThreadState (Z := Unit) t ts) := by
  intro σ hσ y hy
  unfold setThreadState at hy
  obtain ⟨y1, h1, hy⟩ := hy
  obtain ⟨x, hx, e⟩ := mem_threadSet h1
  have h2 : NQ (t :: K) y1.2 := by
    rw [e]
    refine nq_consQ (nq_update hσ.1 hx (nqok_sts hσ.2.1 hσ.2.2 hts))
      (fun hq => hσ.2.1 (queued_update hx (fun x' h => by cases h) hq)) (fun z hz => ?_)
      (fun hq => hσ.2.2 (queuedE_update hx (fun x' h => by cases h) hq))
    simp only [Function.update_apply, if_pos rfl] at hz
    cases hz; exact hts
  exact nq_setThreadStateAct' t y1.2 h2 y hy

/-- `set_thread_state` of a thread of `K`. -/
theorem nq_setThreadState {K : List ObjRef} (t : ObjRef) (ts : ThreadState) (ht : t ∈ K) (hts : ¬ isBoN ts) :
    NQK K (setThreadState (Z := Unit) t ts) :=
  fun σ hσ y hy => nq_mono (nq_setThreadState_q t ts hts σ ⟨hσ, (hσ.2 t ht).1, (hσ.2 t ht).2.2⟩ y hy)
    fun u hu => List.mem_cons_of_mem _ hu

macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_setThreadState _ _ ?_ ?_) <;> first | exact fun h => h | nq_mem))

/-! ## Reads adding a thread to `K`; dequeue then state write -/

theorem ikp_nqcons {K : List ObjRef} {α : Type} {σ : State Unit} {t : ObjRef} {m : NonDet (State Unit) α}
    (ht : NQ K σ → ∀ y, σ.kheap t = some (.tcb y) → ¬ isBoN y.tcbState ∧ epBlocked y.tcbState = none)
    (hm : NQK (t :: K) m) : IKp (NQ K) σ m :=
  fun hσ y hy => nq_tail (hm σ (nq_cons hσ (ht hσ)) y hy)

theorem ik_nqhk_bind {K : List ObjRef} {α γ : Type} {t : ObjRef} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) γ} (hm : HK (NQ K) (NQ (t :: K)) m) (hg : ∀ a, NQK (t :: K) (g a)) :
    NQK K (m >>= g) :=
  fun σ hσ x ⟨y, hy, hx⟩ => nq_tail (hg y.1 y.2 (hm σ hσ y hy) x hx)

/-- `tcb_ntfn_dequeue t n; set_thread_state t ts; …`: `t` joins `K`. -/
theorem ik_nqdq_sts {K : List ObjRef} {γ : Type} (t n : ObjRef) (ts : ThreadState) (hts : ¬ isBoN ts)
    {g : Unit → NonDet (State Unit) γ} (hg : NQK (t :: K) (g ())) :
    NQK K (tcbNtfnDequeue (Z := Unit) t n >>= fun _ => setThreadState (Z := Unit) t ts >>= g) := by
  intro σ hσ x ⟨y, hy, z, hz, hx⟩
  exact nq_tail (hg z.2 (nq_setThreadState_q t ts hts y.2 (nq_tcbNtfnDequeue_post t n σ hσ y hy) z hz) x hx)

theorem ik_nqdq_sts' {K : List ObjRef} (t n : ObjRef) (ts : ThreadState) (hts : ¬ isBoN ts) :
    NQK K (tcbNtfnDequeue (Z := Unit) t n >>= fun _ => setThreadState (Z := Unit) t ts) := by
  intro σ hσ x ⟨y, hy, hx⟩
  exact nq_tail (nq_setThreadState_q t ts hts y.2 (nq_tcbNtfnDequeue_post t n σ hσ y hy) x hx)

macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine ik_nqdq_sts' _ _ _ ?_); exact fun h => h))
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine ik_nqdq_sts _ _ _ ?_ ?_); exact fun h => h))
macro_rules | `(tactic| nq_leaf) => `(tactic| (refine ik_nqhk_bind (nq_tcbEpDequeue_post _ _) fun _ => ?_))

/-- A state read: a state other than BlockedOnNotification / BlockedOnSend /
BlockedOnReceive adds the thread to `K`. -/
macro "nq_rds" : tactic => `(tactic| (show IK _ (getThreadState (Z := Unit) _ >>= _); unfold getThreadState; refine ik_threadGet_bind fun σ x hx => ?_; (try dsimp only); cases hs : x.tcbState <;> (try dsimp only) <;> first | (refine ikp_nqcons (fun hσ y hy => by rw [hx] at hy; cases hy; rw [hs]; exact ⟨fun h => h, rfl⟩) ?_) | (refine ikp_of_ik ?_ σ)))

end

end Fl4Proofs.P3.SInv
