/-
P3 (DESIGN.md §9), invariant line G1 (rd8i): **`Sched.BlockedScActive`,
the remaining writers** (spec side only, outside the JAtZ cone; KENTRY-PLAN
rd8g handoff 1).

Each writer is stated at its own start state with the state facts it reads
(no ∀-states hypothesis):

* `NotQ t σ` (`t`, if a TCB, is not ipc-queued), `CBa t σ` (`t`'s SC, if any,
  is active: rd8e's `PA`).
* `bsa_updScT`: an SC write that may name a non-queued thread
  (`scTcb := some t`); `bsa_updScOff`: an SC write that deactivates an SC with
  no queued bound thread and an empty reply stack.
* **`ba_schedContextDonate_nq`** (an unbound SC to a non-queued thread),
  **`ba_maybeDonateSc_p`** (`NotQ t`), **`ba_sendSignal`**,
  **`ba_updateWaitingNtfn`** (NO hypothesis: the woken thread is set Running
  before the donation), **`ba_completeSignal_p`** (`NotQ tptr`).
* **`ba_bindScReply_p`** (`PA p`), **`ba_replyPush_p`** (`TA caller`,
  `CBa caller`).
* **`ba_refillNew`**, **`ba_refillUpdate`** (new `REFILL_MAX > 0`),
  **`ba_invokeSchedControlConfigureFlags`** (rd8c's `CfgD`: the decoded
  `REFILL_MAX ≥ MIN_REFILLS`).
* **`ba_schedContextSetInactive_p`** (no queued bound thread, empty stack).
* **`ba_schedContextBindTcb_p`** (`NotQ t ∨ PA p`: the decode's
  `¬ (ipc_queued ∧ ¬ released)`).
-/
import Fl4Proofs.P3.SpecInvRd8gG
import Fl4Proofs.P3.SpecInvRd8cB
open Classical

namespace Fl4Proofs.P3.SInvR.B8i
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g

noncomputable section

set_option maxHeartbeats 1000000

/-! ## State facts and their frames -/

/-- `t`, if a TCB, is not ipc-queued. -/
def NotQ (t : ObjRef) (σ : State Unit) : Prop :=
  ∀ x, σ.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = false

/-- `t`'s SC, if any, is active. -/
def CBa (t : ObjRef) (σ : State Unit) : Prop :=
  ∀ x c, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some c → PA c σ

theorem pa_sv {p : ObjRef} {s s' : State Unit} (h : PA p s) (hs : SVK.SVS s s') : PA p s' := by
  obtain ⟨y, n, hk, ha⟩ := h
  have e := hs.1 p
  rw [hk] at e
  obtain ⟨y', hy', -, hm, -⟩ := SVK.sv_sc (o := s'.kheap p) e
  exact ⟨y', n, hy', by show activeSc _ = true; rw [hm]; exact ha⟩

theorem ta_sv {t : ObjRef} {s s' : State Unit} (h : TA t s) (hs : SVK.SVS s s') : TA t s' := by
  intro q y n hq hy
  have e := hs.1 q
  rw [hq] at e
  obtain ⟨y0, hy0, -, hm, ht⟩ := SVK.sv_sc (o := s.kheap q) e.symm
  have := h q y0 n hy0 (by rw [ht]; exact hy)
  show activeSc _ = true; rw [← hm]; exact this

theorem cba_sv {t : ObjRef} {s s' : State Unit} (h : CBa t s) (hs : SVK.SVS s s') : CBa t s' := by
  intro x c hx hc
  have e := hs.1 t
  rw [hx] at e
  obtain ⟨x0, hx0, e0⟩ := SVK.sv_tcb (o := s.kheap t) e.symm
  exact pa_sv (h x0 c hx0 (e0.trans hc)) hs

/-! ## Combinators -/

section Comb
variable {P : State Unit → Prop}

theorem ikp_ro {α β : Type} {σ : State Unit} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : ∀ σ0 : State Unit, IK (fun s => s = σ0) m) (hg : ∀ a, IKp P σ (g a)) : IKp P σ (m >>= g) :=
  ikp_keep (fun _ hy => SInvQ.cq5_ro hm hy) hg

theorem ikp_ro' {α β : Type} {σ : State Unit} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : ∀ σ0 : State Unit, IK (fun s => s = σ0) m) (hg : ∀ a, IKp P σ (g a)) : IKp P σ (NonDet.bind m g) :=
  ikp_ro hm hg

theorem ik_bind_q {α β : Type} {Q : State Unit → Prop} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : IK P m) (hq : ∀ σ, ∀ y ∈ (m σ).1, Q y.2) (hg : ∀ a s, Q s → IKp P s (g a)) : IK P (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  exact hg y.1 y.2 (hq σ y hy) (hm σ hσ y hy) x hx

theorem ikp_bind_q {α β : Type} {Q : State Unit → Prop} {σ : State Unit} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β}
    (hm : IKp P σ m) (hq : ∀ y ∈ (m σ).1, Q y.2) (hg : ∀ a s, Q s → IKp P s (g a)) : IKp P σ (m >>= g) := by
  intro hσ x ⟨y, hy, hx⟩
  exact hg y.1 y.2 (hq y hy) (hm hσ y hy) x hx

theorem ikp_setObject (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (hb : P σ → P { σ with kheap := Function.update σ.kheap p (some o) }) :
    IKp P σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hb hσ

end Comb

/-! ## `NotQ` frames -/

theorem nq_updT {σ : State Unit} {t p : ObjRef} (h : NotQ t σ) {x y : Tcb} (hx : σ.kheap p = some (.tcb x))
    (h1 : y.tcbState = x.tcbState) : NotQ t { σ with kheap := Function.update σ.kheap p (some (.tcb y)) } := by
  intro x' hx'
  change Function.update σ.kheap p (some (KernelObject.tcb y)) t = _ at hx'
  by_cases e : t = p
  · subst e; rw [Function.update_self] at hx'; cases hx'; rw [h1]; exact h x hx
  · rw [Function.update_of_ne e] at hx'; exact h x' hx'

theorem nq_updN {σ : State Unit} {t p : ObjRef} (h : NotQ t σ) {o : KernelObject} (ho : ∀ y, o ≠ .tcb y) :
    NotQ t { σ with kheap := Function.update σ.kheap p (some o) } := by
  intro x' hx'
  change Function.update σ.kheap p (some o) t = _ at hx'
  by_cases e : t = p
  · subst e; rw [Function.update_self] at hx'; exact absurd (Option.some.inj hx') (ho x')
  · rw [Function.update_of_ne e] at hx'; exact h x' hx'

/-- After `set_thread_state t ts` with `ts` not ipc-queued, `NotQ t`. -/
theorem nq_setThreadState (t : ObjRef) (ts : ThreadState) (σ : State Unit) (y : Unit × State Unit)
    (hy : y ∈ (setThreadState (Z := Unit) t ts σ).1) (h : ipcQueuedThreadState ts = false) : NotQ t y.2 := by
  unfold setThreadState at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, -, e⟩ := SInv.mem_threadSet hz
  have k : y.2.kheap = z.2.kheap :=
    (show IK (fun s => s.kheap = z.2.kheap) (setThreadStateAct (Z := Unit) t) from by
      unfold setThreadStateAct setSchedulerAction; repeat' (first | ik_step0 | ik_unfold)) z.2 rfl y hy
  intro x' hx'
  rw [k, e] at hx'
  change Function.update σ.kheap t _ t = _ at hx'
  rw [Function.update_self] at hx'
  cases hx'
  exact h

theorem nq_asUser {α : Type} (t t' : ObjRef) (u : UserMonad α) (σ : State Unit) :
    IKp (NotQ t) σ (asUser (Z := Unit) t' u) := by
  unfold asUser
  refine ik_getsThe_bind (P := NotQ t) (fun x σ hx => ?_) σ
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (ikp_setObject _ _ σ fun h => nq_updT h (getTcb_kheap hx) rfl) fun _ => ik_pure _

theorem nq_threadSet (t t' : ObjRef) (f : Tcb → Tcb) (hf : ∀ x, (f x).tcbState = x.tcbState) (σ : State Unit) :
    IKp (NotQ t) σ (threadSet (Z := Unit) f t') := by
  unfold threadSet
  exact ik_getsThe_bind (P := NotQ t) (fun x σ hx => ikp_setObject _ _ σ fun h => nq_updT h (getTcb_kheap hx) (hf x)) σ

theorem nq_setSimpleKo {α : Type} [Nonempty α] (t : ObjRef) (f : α → KernelObject) (p : ObjRef) (e : α)
    (σ : State Unit) : IKp (NotQ t) σ (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hsimp, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨hk3, hs3⟩ := mem_getObject hy3
  obtain ⟨obj', y3⟩ := y3
  simp only at hk3 hs3 hsimp; subst hs3
  rw [hk] at hk3; cases hk3
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  have hsimp' : aType (f e) ∈ ({.aEndpoint, .aNTFN, .aReply} : Set AType) := by rw [← hty]; exact hsimp
  refine nq_updN hσ fun y ey => ?_
  rw [ey] at hsimp'; simp [aType] at hsimp'

/-! ## SC writes -/

/-- **An SC write that may name a non-queued thread.** -/
theorem bsa_updScT {σ : State Unit} (h : BSA σ) {p t : ObjRef} {x : SchedContext} {m : Nat}
    (hp : σ.kheap p = some (.schedContext x m)) (hn : NotQ t σ) (y : SchedContext) (n : Nat)
    (h1 : y.scTcb = x.scTcb ∨ y.scTcb = none ∨ y.scTcb = some t) (h2 : y.scReplies ≠ [] → x.scReplies ≠ [])
    (h3 : scActive x = true → scActive y = true) :
    BSA { σ with kheap := Function.update σ.kheap p (some (.schedContext y n)) } := by
  have hk : ∀ q, q ≠ p → (Function.update σ.kheap p (some (KernelObject.schedContext y n))) q = σ.kheap q :=
    fun q e => Function.update_of_ne e _ _
  have hkp : (Function.update σ.kheap p (some (KernelObject.schedContext y n))) p = some (.schedContext y n) :=
    Function.update_self _ _ _
  constructor
  · intro q y' n' t' x' hq hy ht hst
    change Function.update σ.kheap p (some (KernelObject.schedContext y n)) q = _ at hq
    change Function.update σ.kheap p (some (KernelObject.schedContext y n)) t' = _ at ht
    have etp : t' ≠ p := by rintro rfl; rw [hkp] at ht; cases ht
    rw [hk t' etp] at ht
    by_cases eq : q = p
    · rw [eq, hkp] at hq; cases hq
      rcases h1 with e | e | e
      · exact h3 (h.tcb p x m t' x' hp (e.symm.trans hy) ht hst)
      · rw [e] at hy; cases hy
      · rw [e] at hy; cases hy; rw [hn x' ht] at hst; cases hst
    · rw [hk q eq] at hq; exact h.tcb q y' n' t' x' hq hy ht hst
  · intro q y' n' hq hr
    change Function.update σ.kheap p (some (KernelObject.schedContext y n)) q = _ at hq
    by_cases eq : q = p
    · rw [eq, hkp] at hq; cases hq
      exact h3 (h.replies p x m hp (h2 hr))
    · rw [hk q eq] at hq; exact h.replies q y' n' hq hr

/-- **An SC write deactivating an SC** with no queued bound thread and no reply stack. -/
theorem bsa_updScOff {σ : State Unit} (h : BSA σ) (p : ObjRef) (y : SchedContext) (n : Nat)
    (h1 : ∀ t, y.scTcb = some t → NotQ t σ) (h2 : y.scReplies = []) :
    BSA { σ with kheap := Function.update σ.kheap p (some (.schedContext y n)) } := by
  have hk : ∀ q, q ≠ p → (Function.update σ.kheap p (some (KernelObject.schedContext y n))) q = σ.kheap q :=
    fun q e => Function.update_of_ne e _ _
  have hkp : (Function.update σ.kheap p (some (KernelObject.schedContext y n))) p = some (.schedContext y n) :=
    Function.update_self _ _ _
  constructor
  · intro q y' n' t' x' hq hy ht hst
    change Function.update σ.kheap p (some (KernelObject.schedContext y n)) q = _ at hq
    change Function.update σ.kheap p (some (KernelObject.schedContext y n)) t' = _ at ht
    have etp : t' ≠ p := by rintro rfl; rw [hkp] at ht; cases ht
    rw [hk t' etp] at ht
    by_cases eq : q = p
    · rw [eq, hkp] at hq; cases hq
      rw [h1 t' hy x' ht] at hst; cases hst
    · rw [hk q eq] at hq; exact h.tcb q y' n' t' x' hq hy ht hst
  · intro q y' n' hq hr
    change Function.update σ.kheap p (some (KernelObject.schedContext y n)) q = _ at hq
    by_cases eq : q = p
    · rw [eq, hkp] at hq; cases hq; exact absurd h2 hr
    · rw [hk q eq] at hq; exact h.replies q y' n' hq hr

theorem ba_updateSchedContext_T (p t : ObjRef) (f : SchedContext → SchedContext) (σ : State Unit) (hn : NotQ t σ)
    (hf : ∀ y, ((f y).scTcb = y.scTcb ∨ (f y).scTcb = none ∨ (f y).scTcb = some t) ∧
      ((f y).scReplies ≠ [] → y.scReplies ≠ []) ∧ (scActive y = true → scActive (f y) = true)) :
    IKp BSA σ (updateSchedContext (Z := Unit) p f) := by
  intro hσ x hx
  obtain ⟨y, n, hk, e⟩ := SInvB.mem_updateSchedContext hx
  rw [e]
  exact bsa_updScT hσ hk hn _ _ (hf y).1 (hf y).2.1 (hf y).2.2

theorem ba_updateSchedContext_act (p : ObjRef) (f : SchedContext → SchedContext) (hf : ∀ y, scActive (f y) = true) :
    BAK (updateSchedContext (Z := Unit) p f) :=
  fun σ => ba_updateSchedContext_p p f σ (fun y _ _ => hf y)

/-! ## Donation of an unbound SC to a non-queued thread -/

theorem ba_schedContextDonate_nq (p t : ObjRef) (σ : State Unit) (hn : NotQ t σ)
    (hf : ∀ y n, σ.kheap p = some (.schedContext y n) → y.scTcb = none) :
    IKp BSA σ (schedContextDonate (Z := Unit) p t) := by
  unfold schedContextDonate
  intro hσ r hr
  obtain ⟨⟨fo, s1⟩, h1, hr⟩ := hr
  obtain ⟨e1, sc, m, hsc, e2⟩ := SInvQ.cq5_mem_getScObjRef h1
  simp only at e1 e2; subst e2; subst s1
  have hfo : sc.scTcb = none := hf sc m hsc
  obtain ⟨z2, h2, hr⟩ := hr
  unfold NonDet.when at h2
  split at h2
  · rename_i hc; exact absurd hfo hc
  obtain rfl := Set.mem_singleton_iff.1 h2
  obtain ⟨z3, h3, hr⟩ := hr
  have b3 := ba_updateSchedContext_T p t (scTcbUpdate fun _ => some t) _ hn (fun _ => ⟨Or.inr (Or.inr rfl), id, id⟩) hσ z3 h3
  exact ba_threadSet (tcbSchedContextUpdate fun _ => some p) t (fun _ => rfl) z3.2 b3 r hr

/-- **`maybe_donate_sc t n`**, `t` not ipc-queued. -/
theorem ba_maybeDonateSc_p (t n : ObjRef) (σ : State Unit) (hn : NotQ t σ) :
    IKp BSA σ (maybeDonateSc (Z := Unit) t n) := by
  unfold maybeDonateSc
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun scOpt => ?_
  unfold NonDet.when
  split
  · refine ikp_ro' (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun nsc => ?_
    cases nsc with
    | none => exact ikp_of_ik (ik_pure _) σ
    | some scPtr =>
      simp only [NonDet.maybeM]
      intro hσ r hr
      obtain ⟨⟨st, s1⟩, h1, hr⟩ := hr
      obtain ⟨e1, sc, m, hsc, e2⟩ := SInvQ.cq5_mem_getScObjRef h1
      simp only at e1 e2; subst e2; subst s1
      dsimp only at hr
      split at hr
      · rename_i hc
        obtain ⟨z2, h2, hr⟩ := hr
        have b2 := ba_schedContextDonate_nq scPtr t _ hn (fun y k hy => by rw [hsc] at hy; cases hy; exact hc) hσ z2 h2
        exact ba_schedContextResume scPtr z2.2 b2 r hr
      · obtain rfl := Set.mem_singleton_iff.1 hr; exact hσ
  · exact ikp_of_ik (ik_pure _) σ

/-- **`update_waiting_ntfn`** (no hypothesis: the woken thread is Running at the donation). -/
theorem ba_updateWaitingNtfn (n : ObjRef) (q : List ObjRef) (b : Badge) :
    BAK (updateWaitingNtfn (Z := Unit) n q b) := by
  unfold updateWaitingNtfn
  refine ik_bind (by ba_auto) fun _ => ?_
  refine ik_pure_bind ?_
  refine ik_bind (ba_tcbNtfnDequeue _ _) fun _ => ?_
  refine ik_bind_q (Q := NotQ _) (ba_setThreadState _ _ rfl) (fun σ y hy => nq_setThreadState _ _ σ y hy rfl)
    fun _ s hq => ?_
  refine ikp_bind_q (Q := NotQ _) (ikp_of_ik (ba_asUser _ _) s) (fun y hy => nq_asUser _ _ _ s hq y hy)
    fun _ s hq => ?_
  refine ikp_bind (ba_maybeDonateSc_p _ _ s hq) fun _ => ?_
  ba_auto

/-- **`send_signal`** (no hypothesis). -/
theorem ba_sendSignal (n : ObjRef) (b : Badge) : BAK (sendSignal (Z := Unit) n b) := by
  unfold sendSignal
  refine ik_bind (by ba_auto) fun ntfn => ?_
  split
  · refine ik_bind (by ba_auto) fun st => ?_
    split
    · refine ik_bind (ba_cancelIpc _) fun _ => ?_
      refine ik_bind_q (Q := NotQ _) (ba_setThreadState _ _ rfl) (fun σ y hy => nq_setThreadState _ _ σ y hy rfl)
        fun _ s hq => ?_
      refine ikp_bind_q (Q := NotQ _) (ikp_of_ik (ba_asUser _ _) s) (fun y hy => nq_asUser _ _ _ s hq y hy)
        fun _ s hq => ?_
      refine ikp_bind (ba_maybeDonateSc_p _ _ s hq) fun _ => ?_
      ba_auto
    · ba_auto
  all_goals first | exact ba_updateWaitingNtfn _ _ _ | ba_auto

/-- **`complete_signal ntfn tptr`**, `tptr` not ipc-queued. -/
theorem ba_completeSignal_p (ntfn tptr : ObjRef) (σ : State Unit) (hn : NotQ tptr σ) :
    IKp BSA σ (completeSignal (Z := Unit) ntfn tptr) := by
  unfold completeSignal
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun nt => ?_
  split
  · refine ikp_bind_q (Q := NotQ tptr) (ikp_of_ik (ba_asUser _ _) σ) (fun y hy => nq_asUser _ _ _ σ hn y hy)
      fun _ s hq => ?_
    refine ikp_bind_q (Q := NotQ tptr) (ikp_of_ik (ba_setSimpleKo _ _ _) s)
      (fun y hy => nq_setSimpleKo _ _ _ _ s hq y hy) fun _ s hq => ?_
    refine ikp_bind (ba_maybeDonateSc_p _ _ s hq) fun _ => ?_
    ba_auto
  all_goals exact ikp_of_ik (by ba_auto) σ

/-! ## The call stack push -/

/-- **`bind_sc_reply p r`** of an active SC. -/
theorem ba_bindScReply_p (p r : ObjRef) (σ : State Unit) (hp : PA p σ) :
    IKp BSA σ (bindScReply (Z := Unit) p r) := by
  unfold bindScReply
  intro hσ y hy
  obtain ⟨⟨rs, s1⟩, h1, hy⟩ := hy
  have e1 : s1 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
  subst s1
  have tail : ∀ s : State Unit, BSA s → PA p s → ∀ y ∈ ((setScObjRef (Z := Unit) scRepliesUpdate p (r :: rs) >>=
      fun _ => setReplyObjRef (Z := Unit) replyScUpdate r (some p)) s).1, BSA y.2 := by
    intro s hs hp' y hy
    obtain ⟨z3, h3, hy⟩ := hy
    obtain ⟨y0, n0, hk0, ha0⟩ := hp'
    have b3 := ba_updateSchedContext_p p (scRepliesUpdate fun _ => r :: rs) s
      (fun y n hy => by rw [hk0] at hy; cases hy; exact ha0) hs z3 h3
    exact ba_updateSkObjRef _ _ _ _ z3.2 b3 y hy
  cases rs with
  | nil => dsimp only at hy; exact tail σ hσ hp y hy
  | cons r0 tl =>
    dsimp only at hy
    obtain ⟨z2, h2, hy⟩ := hy
    exact tail z2.2 (ba_updateSkObjRef _ _ _ _ _ hσ z2 h2) (pa_sv hp (sv_setReplyObjRef' _ _ _ _ z2 h2)) y hy

/-- **`reply_push caller callee r d`**: the caller's SCs active (`TA`), its own SC active (`CBa`) when it may donate. -/
theorem ba_replyPush_p (caller callee r : ObjRef) (d : Bool) (σ : State Unit) (hT : TA caller σ)
    (hC : d = true → CBa caller σ) : IKp BSA σ (replyPush (Z := Unit) caller callee r d) := by
  unfold replyPush
  intro hσ y hy
  obtain ⟨⟨sco, s1⟩, h1, hy⟩ := hy
  obtain ⟨x1, hx1, e1⟩ := SInvQ.q1_mem_threadGet (f := Tcb.tcbSchedContext) h1
  simp only [Prod.mk.injEq] at e1; obtain ⟨rfl, e1⟩ := e1; subst s1
  obtain ⟨⟨sce, s2⟩, h2, hy⟩ := hy
  obtain ⟨x2, -, e2⟩ := SInvQ.q1_mem_threadGet (f := Tcb.tcbSchedContext) h2
  simp only [Prod.mk.injEq] at e2; obtain ⟨rfl, e2⟩ := e2; subst s2
  obtain ⟨z3, h3, hy⟩ := hy
  have b3 : BSA z3.2 := ba_updateSkObjRef _ _ _ _ _ hσ z3 h3
  have v3 : SVK.SVS σ z3.2 := sv_setReplyObjRef' _ _ _ _ z3 h3
  obtain ⟨z4, h4, hy⟩ := hy
  have b4 : BSA z4.2 := ba_setThreadState_p caller _ z3.2 (ta_sv hT v3) b3 z4 h4
  have v4 : SVK.SVS σ z4.2 := v3.trans (SVK.sv_setThreadState' _ _ z3.2 z4 h4)
  unfold NonDet.when at hy
  split at hy
  · rename_i hc
    obtain ⟨hc1, -, hd⟩ := hc
    obtain ⟨c, hcs⟩ := Option.ne_none_iff_exists'.1 hc1
    have hp0 : PA c σ := hC hd x1 c hx1 hcs
    rw [hcs] at hy
    obtain ⟨z5, h5, hy⟩ := hy
    have b5 := ba_bindScReply_p c r z4.2 (pa_sv hp0 v4) b4 z5 h5
    have v5 := SVK.sv_bindScReply' c r z4.2 z5 h5
    exact ba_schedContextDonate c callee z5.2 (pa_sv (pa_sv hp0 v4) v5) b5 y hy
  · obtain rfl := Set.mem_singleton_iff.1 hy; exact b4

/-! ## Configure -/

theorem ba_refillNew (p : ObjRef) (mx : Nat) (b per : Ticks) (h : 0 < mx) :
    BAK (refillNew (Z := Unit) p mx b per) := by
  unfold refillNew
  refine ik_gets_bind fun σ => ikp_of_ik ?_ σ
  refine ik_bind (ba_updateSchedContext _ _ fun _ => ⟨Or.inl rfl, id, rfl⟩) fun _ => ?_
  refine ik_bind (ba_updateSchedContext _ _ fun _ => ⟨Or.inl rfl, id, rfl⟩) fun _ => ?_
  refine ik_bind (ba_updateSchedContext_act _ _ fun _ => ?_) fun _ => ?_
  · show activeSc mx = true; unfold activeSc; exact decide_eq_true h
  ba_auto

theorem ba_refillUpdate (p : ObjRef) (per b : Ticks) (mx : Nat) (h : 0 < mx) :
    BAK (refillUpdate (Z := Unit) p per b mx) := by
  unfold refillUpdate
  refine ik_bind (ba_updateSchedContext _ _ fun _ => ⟨Or.inl rfl, id, rfl⟩) fun _ => ?_
  refine ik_bind (ba_updateSchedContext_act _ _ fun _ => ?_) fun _ => ?_
  · show activeSc mx = true; unfold activeSc; exact decide_eq_true h
  ba_auto

/-- **The configure perform** under the decode's `CfgD`. -/
theorem ba_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) (h : CfgD (.invokeSchedControl iv)) :
    BAK (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  cases iv with
  | invokeSchedControlConfigureFlags p b per mr bd fl =>
    have h0 : 0 < mr := lt_of_lt_of_le (by decide) h.2
    have h2 : 0 < MIN_REFILLS := by decide
    unfold invokeSchedControlConfigureFlags
    repeat' (first
      | (with_reducible exact ba_refillNew _ _ _ _ h0)
      | (with_reducible exact ba_refillNew _ _ _ _ h2)
      | (with_reducible exact ba_refillUpdate _ _ _ _ h0)
      | ba_leaf | ik_step0)

/-! ## Deactivation -/

/-- **`sched_context_set_inactive p`** (no queued bound thread, empty stack). -/
theorem ba_schedContextSetInactive_p (p : ObjRef) (σ : State Unit)
    (hb : ∀ y n, σ.kheap p = some (.schedContext y n) → (∀ t, y.scTcb = some t → NotQ t σ) ∧ y.scReplies = []) :
    IKp BSA σ (schedContextSetInactive (Z := Unit) p) := by
  unfold schedContextSetInactive
  intro hσ r hr
  obtain ⟨z1, h1, hr⟩ := hr
  obtain ⟨y1, n1, hk1, e1⟩ := SInvB.mem_updateSchedContext h1
  have b1 : BSA z1.2 := ba_updateSchedContext _ (scRefillsUpdate fun _ => []) (fun _ => ⟨Or.inl rfl, id, rfl⟩) σ hσ z1 h1
  obtain ⟨z2, h2, hr⟩ := hr
  have b2 : BSA z2.2 := by
    obtain ⟨y2, n2, hk2, e2⟩ := SInvB.mem_updateSchedContext h2
    rw [e1] at hk2
    change Function.update σ.kheap p _ p = _ at hk2
    rw [Function.update_self] at hk2; cases hk2
    rw [e2]
    obtain ⟨h1', h2'⟩ := hb y1 n1 hk1
    refine bsa_updScOff b1 _ _ _ (fun t ht x hx => ?_) h2'
    rw [e1] at hx
    change Function.update σ.kheap p _ t = _ at hx
    by_cases et : t = p
    · subst et; rw [Function.update_self] at hx; cases hx
    · rw [Function.update_of_ne et] at hx; exact h1' t ht x hx
  obtain ⟨z3, h3, hr⟩ := hr
  have b3 : BSA z3.2 := ba_updateSchedContext _ (scBudgetUpdate fun _ => 0) (fun _ => ⟨Or.inl rfl, id, rfl⟩) z2.2 b2 z3 h3
  exact ba_updateSchedContext _ (scSporadicUpdate fun _ => false) (fun _ => ⟨Or.inl rfl, id, rfl⟩) z3.2 b3 r hr

/-! ## Binding -/

/-- **`sched_context_bind_tcb p t`**: `t` not queued, or `p` active. -/
theorem ba_schedContextBindTcb_p (p t : ObjRef) (σ : State Unit) (hb : NotQ t σ ∨ PA p σ) :
    IKp BSA σ (schedContextBindTcb (Z := Unit) p t) := by
  unfold schedContextBindTcb
  refine ikp_bind_q (Q := fun s => NotQ t s ∨ PA p s) (ikp_of_ik (ba_threadSet (tcbSchedContextUpdate fun _ => some p) t (fun _ => rfl)) σ)
    (fun y hy => ?_) fun _ s hq => ?_
  · obtain ⟨x1, hx1, e1⟩ := SInv.mem_threadSet hy
    rcases hb with hn | ⟨y0, n0, hk, ha⟩
    · left; rw [e1]; exact nq_updT hn hx1 rfl
    · right
      have hpt : p ≠ t := by rintro rfl; rw [hk] at hx1; cases hx1
      refine ⟨y0, n0, ?_, ha⟩
      rw [e1]; change Function.update σ.kheap t _ p = _; rw [Function.update_of_ne hpt]; exact hk
  refine ikp_bind ?_ fun _ => ?_
  · rcases hq with hn | ⟨y0, n0, hk, ha⟩
    · exact ba_updateSchedContext_T p t (scTcbUpdate fun _ => some t) s hn (fun _ => ⟨Or.inr (Or.inr rfl), id, id⟩)
    · exact ba_updateSchedContext_p p (scTcbUpdate fun _ => some t) s (fun y' n' hy => by rw [hk] at hy; cases hy; exact ha)
  ba_auto

/-! ## `send_ipc` -/

theorem sc_sv {t c : ObjRef} {x : Tcb} {s s' : State Unit} (hx : s.kheap t = some (.tcb x))
    (hc : x.tcbSchedContext = some c) (hs : SVK.SVS s s') :
    ∃ y, s'.kheap t = some (.tcb y) ∧ y.tcbSchedContext = some c := by
  have e := hs.1 t
  rw [hx] at e
  obtain ⟨y, hy, ey⟩ := SVK.sv_tcb (o := s'.kheap t) e
  exact ⟨y, hy, ey.trans hc⟩

/-- **`send_ipc`** by `thread`: its SCs active (`TA`), its own SC active (`CBa`),
and bound when it may donate without a call. -/
theorem ba_sendIpc_p (block call : Bool) (badge : Badge) (cg cgr cd : Bool) (thread epptr : ObjRef)
    (σ : State Unit) (hT : TA thread σ) (hC : cd = true → CBa thread σ)
    (hD : call = false → cd = true → ∃ x c, σ.kheap thread = some (.tcb x) ∧ x.tcbSchedContext = some c) :
    IKp BSA σ (sendIpc (Z := Unit) block call badge cg cgr cd thread epptr) := by
  unfold sendIpc
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun ep => ?_
  split
  · exact ba_sendIpcBlocked_p _ _ _ _ _ _ σ hT
  · exact ba_sendIpcBlocked_p _ _ _ _ _ _ σ hT
  · exact ikp_of_ik (ik_pure _) σ
  · exact ikp_of_ik (ik_pure _) σ
  · intro hσ y hy
    obtain ⟨z1, h1, hy⟩ := hy
    have b1 := ba_tcbEpDequeue _ _ σ hσ z1 h1
    have v1 := sv_tcbEpDequeue _ _ σ z1 h1
    obtain ⟨⟨st, s2⟩, h2, hy⟩ := hy
    have e2 : s2 = z1.2 := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h2
    subst s2
    dsimp only at hy
    split at hy
    · obtain ⟨z3, h3, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h3
      dsimp only at hy
      obtain ⟨z4, h4, hy⟩ := hy
      have b4 := ba_doIpcTransfer _ _ _ _ _ _ b1 z4 h4
      have v4 := SVK.sv_doIpcTransfer' _ _ _ _ _ _ z4 h4
      obtain ⟨z5, h5, hy⟩ := hy
      have b5 := ik_maybeM (fun _ => ba_replyUnlinkTcb _ _) _ _ b4 z5 h5
      have v5 := SVK.sv_maybeM (fun _ => SVK.sv_replyUnlinkTcb _ _) _ _ z5 h5
      have v : SVK.SVS σ z5.2 := (v1.trans v4).trans v5
      obtain ⟨⟨sco, s6⟩, h6, hy⟩ := hy
      obtain ⟨x6, -, e6⟩ := SInvQ.q1_mem_threadGet (f := Tcb.tcbSchedContext) h6
      simp only [Prod.mk.injEq] at e6; obtain ⟨rfl, e6⟩ := e6; subst s6
      obtain ⟨⟨flt, s7⟩, h7, hy⟩ := hy
      obtain ⟨x7, -, e7⟩ := SInvQ.q1_mem_threadGet (f := Tcb.tcbFault) h7
      simp only [Prod.mk.injEq] at e7; obtain ⟨rfl, e7⟩ := e7; subst s7
      dsimp only at hy
      split at hy
      · split at hy
        · obtain ⟨z8, h8, hy⟩ := hy
          have b8 := ba_replyPush_p thread _ _ cd z5.2 (ta_sv hT v) (fun hd => cba_sv (hC hd) v) b5 z8 h8
          exact (by (try dsimp only); ba_auto : BAK _) z8.2 b8 y hy
        · obtain ⟨z8, h8, hy⟩ := hy
          have b8 := ba_setThreadState thread .inactive rfl z5.2 b5 z8 h8
          exact (by (try dsimp only); ba_auto : BAK _) z8.2 b8 y hy
      · rename_i hnc
        obtain ⟨z8, h8, hy⟩ := hy
        have b8 : BSA z8.2 := by
          unfold NonDet.when at h8
          split at h8
          · rename_i hc
            have hcall : call = false := by
              cases call
              · rfl
              · exact absurd (Or.inl rfl) hnc
            obtain ⟨x0, c, hx0, hc0⟩ := hD hcall hc.1
            obtain ⟨x9, hx9, hc9⟩ := sc_sv hx0 hc0 v
            obtain ⟨⟨tsc, s9⟩, h9, h8⟩ := h8
            obtain ⟨x9', hx9', e9⟩ := SInvQ.q1_mem_threadGet (f := Tcb.tcbSchedContext) h9
            simp only [Prod.mk.injEq] at e9; obtain ⟨rfl, e9⟩ := e9; subst s9
            rw [hx9] at hx9'; cases hx9'
            rw [hc9] at h8
            exact ba_schedContextDonate c _ z5.2 (cba_sv (hC hc.1) v x9 c hx9 hc9) b5 z8 h8
          · obtain rfl := Set.mem_singleton_iff.1 h8; exact b5
        exact (by (try dsimp only); ba_auto : BAK _) z8.2 b8 y hy
    · obtain ⟨z3, h3, -⟩ := hy; exact h3.elim
  · exact ikp_of_ik (ik_fail) σ

end

end Fl4Proofs.P3.SInvR.B8i
