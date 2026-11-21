/-
P3 (DESIGN.md §9), invariant line G1 (nq1): **NtfnQB across the queue
additions** (spec side only): a notification write whose new queue adds only a
thread BlockedOnNotification on that notification (`nq_ntfn_add`), so
`tcb_ntfn_append` / `reorder_ntfn` of such a thread, `set_priority` (a
BlockedOnNotification target is reordered in its queue; it is not in `K`),
`receive_signal_blocked` / `receive_signal` (the receiver, first in `K`,
becomes BlockedOnNotification and is appended: it leaves `K`). `nq2_auto`:
`nq_auto` with the state-read rule `nq_rds` and failing / impossible branches.
-/
import Fl4Proofs.P3.SpecInvNtfnQF6
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

variable {K : List ObjRef}

theorem upd_ne' {σ : State Unit} {p q : ObjRef} {o : KernelObject} (h : q ≠ p) :
    ({ σ with kheap := Function.update σ.kheap p (some o) } : State Unit).kheap q = σ.kheap q := by
  dsimp only; rw [Function.update_apply, if_neg h]

/-- `t` is a TCB BlockedOnNotification on `n`. -/
def TS (t n : ObjRef) (σ : State Unit) : Prop :=
  ∃ y, σ.kheap t = some (.tcb y) ∧ y.tcbState = .blockedOnNotification n

/-- A notification write whose new queue adds only a thread BlockedOnNotification on it. -/
theorem nq_ntfn_add {σ : State Unit} {n t : ObjRef} {x0 x' : Notification} (h : NQ K σ)
    (hn : σ.kheap n = some (.notification x0)) (ht : TS t n σ)
    (hsub : ∀ u ∈ x'.ntfnObj.ntfnQueue, u = t ∨ u ∈ x0.ntfnObj.ntfnQueue) :
    NQ K { σ with kheap := Function.update σ.kheap n (some (.notification x')) } := by
  have hne : ∀ u y, σ.kheap u = some (.tcb y) → u ≠ n := by
    rintro u y hu rfl; rw [hn] at hu; cases hu
  refine ⟨⟨fun m x u hm hu => ?_, fun m x u hm hu => ?_⟩, fun u hu => ⟨?_, fun y hy => ?_, ?_⟩⟩
  · by_cases e : m = n
    · subst e
      dsimp only at hm; rw [Function.update_apply, if_pos rfl] at hm; cases hm
      rcases hsub u hu with rfl | hu0
      · obtain ⟨y, hy, hs⟩ := ht
        exact ⟨y, (upd_ne' (hne _ _ hy)).trans hy, hs⟩
      · obtain ⟨y, hy, hs⟩ := h.1.1 m x0 u hn hu0
        exact ⟨y, (upd_ne' (hne _ _ hy)).trans hy, hs⟩
    · rw [upd_ne' e] at hm
      obtain ⟨y, hy, hs⟩ := h.1.1 m x u hm hu
      exact ⟨y, (upd_ne' (hne _ _ hy)).trans hy, hs⟩
  · have hmn : m ≠ n := by
      rintro rfl; dsimp only at hm; rw [Function.update_apply, if_pos rfl] at hm; cases hm
    rw [upd_ne' hmn] at hm
    obtain ⟨y, hy, hs⟩ := h.1.2 m x u hm hu
    exact ⟨y, (upd_ne' (hne _ _ hy)).trans hy, hs⟩
  · rintro ⟨m, x, hm, hq⟩
    by_cases e : m = n
    · subst e
      dsimp only at hm; rw [Function.update_apply, if_pos rfl] at hm; cases hm
      rcases hsub u hq with rfl | hu0
      · obtain ⟨y, hy, hs⟩ := ht
        exact (h.2 _ hu).2.1 y hy (by rw [hs]; trivial)
      · exact (h.2 u hu).1 ⟨m, x0, hn, hu0⟩
    · rw [upd_ne' e] at hm; exact (h.2 u hu).1 ⟨m, x, hm, hq⟩
  · by_cases e : u = n
    · subst e; dsimp only at hy; rw [Function.update_apply, if_pos rfl] at hy; cases hy
    · rw [upd_ne' e] at hy; exact (h.2 u hu).2.1 y hy
  · exact fun hq => (h.2 u hu).2.2 (queuedE_update hn (fun x' h => by cases h) hq)

/-- `t` is a TCB BlockedOnSend / BlockedOnReceive on `e`. -/
def TE (t e : ObjRef) (σ : State Unit) : Prop :=
  ∃ y, σ.kheap t = some (.tcb y) ∧ epBlocked y.tcbState = some e

/-- An endpoint write whose new queue adds only a thread blocked on it; that thread leaves `K`. -/
theorem nq_ep_add {σ : State Unit} {e t : ObjRef} {x0 x' : Endpoint} (h : NQ K σ)
    (he : σ.kheap e = some (.endpoint x0)) (ht : TE t e σ)
    (hsub : ∀ u ∈ x'.epQueue, u = t ∨ u ∈ x0.epQueue) :
    NQ (K.filter (· ≠ t)) { σ with kheap := Function.update σ.kheap e (some (.endpoint x')) } := by
  have hne : ∀ u y, σ.kheap u = some (.tcb y) → u ≠ e := by
    rintro u y hu rfl; rw [he] at hu; cases hu
  refine ⟨⟨fun m x u hm hu => ?_, fun m x u hm hu => ?_⟩, fun u hu => ⟨?_, fun y hy => ?_, ?_⟩⟩
  · have hme : m ≠ e := by
      rintro rfl; dsimp only at hm; rw [Function.update_apply, if_pos rfl] at hm; cases hm
    rw [upd_ne' hme] at hm
    obtain ⟨y, hy, hs⟩ := h.1.1 m x u hm hu
    exact ⟨y, (upd_ne' (hne _ _ hy)).trans hy, hs⟩
  · by_cases em : m = e
    · subst em
      dsimp only at hm; rw [Function.update_apply, if_pos rfl] at hm; cases hm
      rcases hsub u hu with rfl | hu0
      · obtain ⟨y, hy, hs⟩ := ht
        exact ⟨y, (upd_ne' (hne _ _ hy)).trans hy, hs⟩
      · obtain ⟨y, hy, hs⟩ := h.1.2 m x0 u he hu0
        exact ⟨y, (upd_ne' (hne _ _ hy)).trans hy, hs⟩
    · rw [upd_ne' em] at hm
      obtain ⟨y, hy, hs⟩ := h.1.2 m x u hm hu
      exact ⟨y, (upd_ne' (hne _ _ hy)).trans hy, hs⟩
  · obtain ⟨huK, -⟩ := mem_filter_ne' hu
    exact fun hq => (h.2 u huK).1 (queued_update he (fun x' h => by cases h) hq)
  · obtain ⟨huK, -⟩ := mem_filter_ne' hu
    by_cases eu : u = e
    · subst eu; dsimp only at hy; rw [Function.update_apply, if_pos rfl] at hy; cases hy
    · rw [upd_ne' eu] at hy; exact (h.2 u huK).2.1 y hy
  · obtain ⟨huK, hut⟩ := mem_filter_ne' hu
    rintro ⟨m, x, hm, hq⟩
    by_cases em : m = e
    · subst em
      dsimp only at hm; rw [Function.update_apply, if_pos rfl] at hm; cases hm
      rcases hsub u hq with rfl | hu0
      · exact hut rfl
      · exact (h.2 u huK).2.2 ⟨m, x0, he, hu0⟩
    · rw [upd_ne' em] at hm; exact (h.2 u huK).2.2 ⟨m, x, hm, hq⟩

/-- `tcb_append` (an ordered insert) reads only, and adds only `t`. -/
theorem nq_mem_tcbAppend {t : ObjRef} {qs : List ObjRef} {σ : State Unit} {y : List ObjRef × State Unit}
    (h : y ∈ (tcbAppend (Z := Unit) t qs σ).1) : y.2 = σ ∧ ∀ u ∈ y.1, u = t ∨ u ∈ qs := by
  have hs : y.2 = σ := (show IK (fun s => s = σ) (tcbAppend (Z := Unit) t qs) by
    unfold tcbAppend orderedInsert; repeat' (first | ik_step0 | ik_unfold)) σ rfl y h
  refine ⟨hs, ?_⟩
  unfold tcbAppend orderedInsert at h
  obtain ⟨z1, h1, h⟩ := h
  obtain ⟨z2, h2, h⟩ := h
  obtain ⟨z3, h3, h⟩ := h
  rw [Set.mem_singleton_iff.1 h3] at h
  obtain ⟨z4, h4, h⟩ := h
  rw [Set.mem_singleton_iff.1 h4] at h
  rw [Set.mem_singleton_iff.1 h]
  intro u hu
  rw [List.mem_map] at hu
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hu
  simp only [List.mem_append, List.mem_singleton] at hab
  rcases hab with (hab | hab) | hab
  · exact Or.inr (List.of_mem_zip ((List.takeWhile_sublist _).subset hab)).1
  · cases hab; exact Or.inl rfl
  · exact Or.inr (List.of_mem_zip ((List.dropWhile_sublist _).subset hab)).1

/-- `tcb_ntfn_append` of a thread BlockedOnNotification on that notification. -/
theorem nq_tcbNtfnAppend_p (t n : ObjRef) :
    HK (fun s => NQ K s ∧ TS t n s) (NQ K) (tcbNtfnAppend (Z := Unit) t n) := by
  intro σ ⟨hσ, ht⟩ y hy
  unfold tcbNtfnAppend at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst e1
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hzs, hzm⟩ := nq_mem_tcbAppend hz
  obtain ⟨qs', s2⟩ := z
  simp only at hzs hzm; subst hzs
  obtain ⟨o0, -, -, -, e⟩ := mem_setSimpleKo hy
  rw [e]
  exact nq_ntfn_add hσ hk ht fun u hu => hzm u hu

/-- `reorder_ntfn` of a thread BlockedOnNotification on that notification. -/
theorem nq_reorderNtfn_p (n t : ObjRef) :
    HK (fun s => NQ K s ∧ TS t n s) (NQ K) (reorderNtfn (Z := Unit) n t) := by
  intro σ ⟨hσ, ht⟩ y hy
  unfold reorderNtfn at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst e1
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hzs, hzm⟩ := nq_mem_tcbAppend hz
  obtain ⟨qs', s2⟩ := z
  simp only at hzs hzm; subst hzs
  obtain ⟨o0, -, -, -, e⟩ := mem_setSimpleKo hy
  rw [e]
  refine nq_ntfn_add hσ hk ht fun u hu => ?_
  rcases hzm u hu with h | h
  · exact Or.inl h
  · exact Or.inr (removeAll_sub h)

/-- `tcb_ep_append` of a thread blocked on that endpoint: it leaves `K`. -/
theorem nq_tcbEpAppend_p (t e : ObjRef) (b : Bool) :
    HK (fun s => NQ K s ∧ TE t e s) (NQ (K.filter (· ≠ t))) (tcbEpAppend (Z := Unit) t e b) := by
  intro σ ⟨hσ, ht⟩ y hy
  unfold tcbEpAppend at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst e1
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hzs, hzm⟩ := nq_mem_tcbAppend hz
  obtain ⟨qs', s2⟩ := z
  simp only at hzs hzm; subst hzs
  obtain ⟨o0, -, -, -, ee⟩ := mem_setSimpleKo hy
  rw [ee]
  exact nq_ep_add hσ hk ht fun u hu => hzm u (by rwa [epQueue_updateEpQueue] at hu)

/-- `reorder_ep` of a thread blocked on that endpoint: it leaves `K`. -/
theorem nq_reorderEp_p (e t : ObjRef) :
    HK (fun s => NQ K s ∧ TE t e s) (NQ (K.filter (· ≠ t))) (reorderEp (Z := Unit) e t) := by
  intro σ ⟨hσ, ht⟩ y hy
  unfold reorderEp at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst e1
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hzs, hzm⟩ := nq_mem_tcbAppend hz
  obtain ⟨qs', s2⟩ := z
  simp only at hzs hzm; subst hzs
  obtain ⟨o0, -, -, -, ee⟩ := mem_setSimpleKo hy
  rw [ee]
  refine nq_ep_add hσ hk ht fun u hu => ?_
  rw [epQueue_updateEpQueue] at hu
  rcases hzm u hu with h | h
  · exact Or.inl h
  · exact Or.inr (removeAll_sub h)

theorem kh_setThreadStateAct (t : ObjRef) (k : KHeap) :
    IK (fun s => s.kheap = k) (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct setSchedulerAction
  repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when))

theorem nq_filter_of {σ : State Unit} {t : ObjRef} (h : NQ K σ) : NQ (K.filter (· ≠ t)) σ :=
  nq_mono h fun _ hu => (mem_filter_ne' hu).1

/-- `set_priority`: a BlockedOnNotification target is reordered in its
notification queue; a BlockedOnSend / BlockedOnReceive target in its endpoint
queue (it leaves `K`: `reorder_ep` re-inserts it). -/
theorem nq_setPriority (t : ObjRef) (prio : Priority) :
    HK (NQ K) (NQ (K.filter (· ≠ t))) (setPriority (Z := Unit) t prio) := by
  unfold setPriority getThreadState
  refine hk_threadGet_bind fun σ x hx => ?_
  cases hs : x.tcbState
  case blockedOnNotification n =>
    try dsimp only
    rw [if_neg (by simp [runnable])]
    intro hσ y hy
    obtain ⟨y1, h1, hy⟩ := hy
    unfold threadSetPriority at h1
    have hb1 : NQ K y1.2 := nq_threadSet (fun tcb => { tcb with tcbPriority := prio }) t (fun _ => rfl) σ hσ y1 h1
    obtain ⟨x1, hx1, e1⟩ := mem_threadSet h1
    rw [hx] at hx1; cases hx1
    obtain ⟨y2, h2, hy⟩ := hy
    have e2 : y2.2 = y1.2 := by
      simp only [epBlocked, NonDet.maybeM] at h2; rw [Set.mem_singleton_iff.1 h2]
    simp only [ntfnBlocked, NonDet.maybeM] at hy
    rw [e2] at hy
    exact nq_filter_of (nq_reorderNtfn_p n t y1.2 ⟨hb1, ⟨{ x with tcbPriority := prio }, by rw [e1]; simp, by simp [hs]⟩⟩ y hy)
  case blockedOnSend e d =>
    try dsimp only
    rw [if_neg (by simp [runnable])]
    intro hσ y hy
    obtain ⟨y1, h1, hy⟩ := hy
    unfold threadSetPriority at h1
    have hb1 : NQ K y1.2 := nq_threadSet (fun tcb => { tcb with tcbPriority := prio }) t (fun _ => rfl) σ hσ y1 h1
    obtain ⟨x1, hx1, e1⟩ := mem_threadSet h1
    rw [hx] at hx1; cases hx1
    obtain ⟨y2, h2, hy⟩ := hy
    simp only [epBlocked, NonDet.maybeM] at h2
    have hb2 := nq_reorderEp_p e t y1.2 ⟨hb1, ⟨{ x with tcbPriority := prio }, by rw [e1]; simp, by simp [hs, epBlocked]⟩⟩ y2 h2
    simp only [ntfnBlocked, NonDet.maybeM] at hy
    rw [Set.mem_singleton_iff.1 hy]; exact hb2
  case blockedOnReceive e r d =>
    try dsimp only
    rw [if_neg (by simp [runnable])]
    intro hσ y hy
    obtain ⟨y1, h1, hy⟩ := hy
    unfold threadSetPriority at h1
    have hb1 : NQ K y1.2 := nq_threadSet (fun tcb => { tcb with tcbPriority := prio }) t (fun _ => rfl) σ hσ y1 h1
    obtain ⟨x1, hx1, e1⟩ := mem_threadSet h1
    rw [hx] at hx1; cases hx1
    obtain ⟨y2, h2, hy⟩ := hy
    simp only [epBlocked, NonDet.maybeM] at h2
    have hb2 := nq_reorderEp_p e t y1.2 ⟨hb1, ⟨{ x with tcbPriority := prio }, by rw [e1]; simp, by simp [hs, epBlocked]⟩⟩ y2 h2
    simp only [ntfnBlocked, NonDet.maybeM] at hy
    rw [Set.mem_singleton_iff.1 hy]; exact hb2
  all_goals
    simp only [runnable, epBlocked, ntfnBlocked, NonDet.maybeM, Bool.false_eq_true, ↓reduceIte]
    exact fun hσ y hy => nq_filter_of (ikp_of_ik (by nq_auto) σ hσ y hy)


/-- `receive_signal_blocked`: the receiver (in `K`) becomes BlockedOnNotification and is appended. -/
theorem nq_receiveSignalBlocked (thread n : ObjRef) (blk : Bool) (ht : thread ∈ K) :
    HK (NQ K) (NQ (K.filter (· ≠ thread))) (receiveSignalBlocked (Z := Unit) thread n blk) := by
  unfold receiveSignalBlocked
  split
  · intro σ hσ y hy
    obtain ⟨y1, h1, hy⟩ := hy
    unfold setThreadState at h1
    obtain ⟨y0, h0, h1⟩ := h1
    obtain ⟨x, hx, e0⟩ := mem_threadSet h0
    have hK' : thread ∉ K.filter (· ≠ thread) := by simp
    have hb0 : NQ (K.filter (· ≠ thread)) y0.2 := by
      rw [e0]; exact nq_update (nq_filter_of hσ) hx (nqok_stsK (hσ.2 thread ht).1 (hσ.2 thread ht).2.2 hK')
    have hk1 : y1.2.kheap = y0.2.kheap := kh_setThreadStateAct thread _ y0.2 rfl y1 h1
    have hb1 : NQ (K.filter (· ≠ thread)) y1.2 := nq_setThreadStateAct' thread y0.2 hb0 y1 h1
    have hts : TS thread n y1.2 := ⟨{ x with tcbState := .blockedOnNotification n }, by rw [hk1, e0]; simp, rfl⟩
    obtain ⟨y2, h2, hy⟩ := hy
    have hb2 := nq_tcbNtfnAppend_p thread n y1.2 ⟨hb1, hts⟩ y2 h2
    exact (nq_maybeReturnSc (Kq := K.filter (· ≠ thread)) n thread) y2.2 hb2 y hy
  · exact fun σ hσ y hy => nq_filter_of (nq_doNbrecvFailedTransfer _ σ hσ y hy)

theorem hk_getSimpleKo_bind {P Q : State Unit → Prop} {α β : Type} [Nonempty α] {C : α → KernelObject}
    {p : ObjRef} {k : α → NonDet (State Unit) β} (h : ∀ a, HK P Q (k a)) : HK P Q (getSimpleKo (Z := Unit) C p >>= k) := by
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨-, e⟩ := mem_getSimpleKo hz
  obtain ⟨a, s⟩ := z
  simp only at e; subst e
  exact h a _ hσ y hy

/-- `receive_signal`: an active notification is consumed; otherwise the receiver blocks. -/
theorem nq_receiveSignal (thread : ObjRef) (cap : Cap) (blk : Bool) (ht : thread ∈ K) :
    HK (NQ K) (NQ (K.filter (· ≠ thread))) (receiveSignal (Z := Unit) thread cap blk) := by
  unfold receiveSignal
  split
  · refine hk_bind (hk_of_ik (ik_pure _)) fun p => ?_
    refine hk_getSimpleKo_bind fun a => ?_
    (try dsimp only)
    split
    · exact hk_post (hk_of_ik (by nq_auto)) fun s h => nq_filter_of h
    · exact nq_receiveSignalBlocked thread _ blk ht
  · intro σ hσ y hy
    obtain ⟨y1, h1, -⟩ := hy
    exact h1.elim

/-- After `set_thread_state t ts` with `ts` blocked on `e`, `t` is blocked on `e`. -/
theorem te_setThreadState {t e : ObjRef} {ts : ThreadState} {σ : State Unit} {y : Unit × State Unit}
    (h : y ∈ (setThreadState (Z := Unit) t ts σ).1) (hts : epBlocked ts = some e) : TE t e y.2 := by
  unfold setThreadState at h
  obtain ⟨y0, h0, h1⟩ := h
  obtain ⟨x, hx, e0⟩ := mem_threadSet h0
  have hk1 : y.2.kheap = y0.2.kheap := kh_setThreadStateAct t _ y0.2 rfl y h1
  exact ⟨{ x with tcbState := ts }, by rw [hk1, e0]; simp, hts⟩

/-- A simple-object field write keeps every TCB. -/
theorem te_updateSkObjRef {α : Type} [Nonempty α] (Ck : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) {σ : State Unit}
    {t e : ObjRef} (ht : TE t e σ) {y : Unit × State Unit}
    (hy : y ∈ (updateSkObjRef (Z := Unit) Ck f ref new σ).1) : TE t e y.2 := by
  unfold updateSkObjRef at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨-, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at e1; subst e1
  obtain ⟨o0, hk, hs, -, ee⟩ := mem_setSimpleKo hy
  rw [ee]
  obtain ⟨x, hx, hb⟩ := ht
  have hne : t ≠ ref := by
    rintro rfl; rw [hx] at hk; cases hk; exact simple_not_tcb hs x rfl
  exact ⟨x, (upd_ne' hne).trans hx, hb⟩

/-- `send_ipc_blocked`: the sender (in `K`) becomes BlockedOnSend and is appended: it leaves `K`. -/
theorem nq_sendIpcBlocked (thread e : ObjRef) (badge : Badge) (g gr call : Bool) (ht : thread ∈ K) :
    HK (NQ K) (NQ (K.filter (· ≠ thread))) (sendIpcBlocked (Z := Unit) thread e badge g gr call) := by
  unfold sendIpcBlocked
  intro σ hσ y hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 : NQ K y1.2 := nq_setThreadState thread _ ht (by exact fun h => h) σ hσ y1 h1
  exact nq_tcbEpAppend_p thread e false y1.2 ⟨hb1, te_setThreadState h1 rfl⟩ y hy

/-- `receive_ipc_blocked`: the receiver (in `K`) becomes BlockedOnReceive and is appended: it leaves `K`. -/
theorem nq_receiveIpcBlocked (blk : Bool) (thread e : ObjRef) (reply : Option ObjRef) (ht : thread ∈ K) :
    HK (NQ K) (NQ (K.filter (· ≠ thread))) (receiveIpcBlocked (Z := Unit) blk thread e reply) := by
  unfold receiveIpcBlocked
  split
  · intro σ hσ y hy
    obtain ⟨y1, h1, hy⟩ := hy
    have hb1 : NQ K y1.2 := nq_setThreadState thread _ ht (by exact fun h => h) σ hσ y1 h1
    have hts : TE thread e y1.2 := te_setThreadState h1 rfl
    obtain ⟨y2, h2, hy⟩ := hy
    have hb2 : NQ K y2.2 ∧ TE thread e y2.2 := by
      cases reply with
      | none =>
        simp only [NonDet.maybeM] at h2
        rw [Set.mem_singleton_iff.1 h2]; exact ⟨hb1, hts⟩
      | some r =>
        simp only [NonDet.maybeM] at h2
        exact ⟨(by nq_auto : NQK K (setReplyObjRef (Z := Unit) replyTcbUpdate r (some thread))) y1.2 hb1 y2 h2,
          te_updateSkObjRef _ _ _ _ hts h2⟩
    exact nq_tcbEpAppend_p thread e true y2.2 hb2 y hy
  · exact fun σ hσ y hy => nq_filter_of (nq_doNbrecvFailedTransfer _ σ hσ y hy)

theorem nq_weak_nil {K : List ObjRef} (s : State Unit) (h : NQ K s) : NQ [] s :=
  nq_mono h fun _ h => by cases h

/-- The pre/post form of `ikp_nqcons`. -/
theorem hkp_nqcons {Q : State Unit → Prop} {α : Type} {σ : State Unit} {t : ObjRef} {m : NonDet (State Unit) α}
    (ht : NQ K σ → ∀ y, σ.kheap t = some (.tcb y) → ¬ isBoN y.tcbState ∧ epBlocked y.tcbState = none)
    (hm : HK (NQ (t :: K)) Q m) : HKp (NQ K) Q σ m :=
  fun hσ y hy => hm σ (nq_cons hσ (ht hσ)) y hy

/-- `nq_auto`, with the state-read rule, closing failing and impossible branches. -/
macro "nq2_auto" : tactic => `(tactic| repeat' (first | nq_leaf | (with_reducible exact ik_fail_bind) | nq_rds | (with_reducible apply ike_ite) | (with_reducible apply ike_whenE) | (with_reducible apply ike_unlessE) | (with_reducible apply ike_liftE) | (show IK _ (ite _ _ _); split <;> try (rename_i hsplit; simp at hsplit; done)) | (show IK _ (ite _ _ _ >>= _); split <;> try (rename_i hsplit; simp at hsplit; done)) | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless) | (exfalso; contradiction)))


/-- Leaves of `nqh_auto` (the pre/post lemmas of the functions that may block a thread). -/
syntax "nqh_leaf" : tactic
macro_rules | `(tactic| nqh_leaf) => `(tactic| fail "no nqh_leaf")

/-- Pre/post automation for the functions that may block a thread of `K` on an
endpoint (the post forgets `K`): a pre/post leaf, the whole remainder by
`nq2_auto`, a prefix by `nq2_auto`, or a split. -/
macro "nqh_auto" : tactic => `(tactic| repeat' (first
  | nqh_leaf
  | (refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_)
  | (unfold NonDet.when)
  | split
  | (exact hk_post (hk_of_ik (by nq2_auto)) nq_weak_nil)))

end

end Fl4Proofs.P3.SInv
