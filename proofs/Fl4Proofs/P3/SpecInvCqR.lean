/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ctq3): **TQ, T1 with l4v
`valid_ready_qs`' runnable half** (spec side only, outside the JAtZ cone):
every ready-queued thread is a runnable TCB of that queue's domain and
priority.

* `TQX X σ := RQd σ ∧ X σ.readyQueues` (`RQd` = T1 ∧ "queued ⇒ runnable";
  `X` an extra fact on the ready queues only, so heap writes keep it by
  definition: `TQ` = `TQX TT`, `TQU t` = "`t` is in no ready
  queue").
* Leaves: heap writes (a TCB write keeps domain and priority, and keeps the
  TCB runnable when it is queued: `tqx_setObject_p`), `set_simple_ko`,
  `thread_set` (domain, priority and state kept), `arch_thread_set`,
  `as_user`, `set_mrs`, `set_cap`, `tcb_sched_action` (an action adding only
  the thread, runnable at that state: `tqx_tcbSchedAction_p`; the dequeue
  needs nothing), `set_thread_state` (a runnable state, or a thread in no
  ready queue: `tqx_setThreadState_p`), `delete_objects` / `retype_region`
  under "no queued thread in the region / at the new addresses".
* Release-queue and scheduler-action writes are frames: TQ does not mention
  them (l4v's `valid_release_q` / `valid_sched_action` are not part of TQ;
  KENTRY-PLAN ctq3 says where they would be needed).
-/
import Fl4Proofs.P3.SpecInvCq
import Fl4Proofs.P3.SpecInvUt
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- **T1 and "queued ⇒ runnable"** (l4v `valid_ready_qs`: every member of
`ready_queues s d p` is an `etcb_at` of domain `d` and priority `p` and
`st_tcb_at runnable`). -/
abbrev RQd (σ : State Unit) : Prop :=
  ∀ d p t, t ∈ σ.readyQueues d p → ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbDomain = d ∧ x.tcbPriority = p ∧
    runnable x.tcbState = true

/-- `RQd` with an extra fact on the ready queues. -/
abbrev TQX (X : (Domain → Priority → ReadyQueue) → Prop) (σ : State Unit) : Prop := RQd σ ∧ X σ.readyQueues

/-- No extra fact (a constant, so that `TQX ?X` unifies with `TQ`). -/
def TT (_ : Domain → Priority → ReadyQueue) : Prop := True

/-- **TQ [J]** (the carried form). -/
abbrev TQ (σ : State Unit) : Prop := TQX TT σ

/-- `t` is in no ready queue. -/
abbrev NoQ (t : ObjRef) (rq : Domain → Priority → ReadyQueue) : Prop := ∀ d p, t ∉ rq d p

/-- TQ and `t` in no ready queue. -/
abbrev TQU (t : ObjRef) (σ : State Unit) : Prop := TQX (NoQ t) σ

abbrev TQK {α : Type} (m : NonDet (State Unit) α) : Prop := IK TQ m
abbrev TQKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE TQ m

theorem tq_t1 {σ : State Unit} (h : RQd σ) : T1 σ := fun d p t ht =>
  let ⟨x, hx, h1, h2, _⟩ := h d p t ht; ⟨x, hx, h1, h2⟩

/-- A thread that is not runnable is in no ready queue. -/
theorem rqd_noQ {σ : State Unit} (h : RQd σ) {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hr : runnable x.tcbState = false) : NoQ t σ.readyQueues := fun d p hp => by
  obtain ⟨x', hx', -, -, h3⟩ := h d p t hp
  rw [hx] at hx'; cases hx'; rw [hr] at h3; cases h3

/-- **TQ at boot** (empty queues). -/
theorem boot_tq : TQ (initASt (Z := Unit)) := ⟨fun _ _ _ h => (List.not_mem_nil h).elim, trivial⟩

/-! ## Heap writes -/

theorem rqd_update {σ : State Unit} (h : RQd σ) (p : ObjRef) (o : KernelObject)
    (ho : ∀ d pr, p ∈ σ.readyQueues d pr →
      ∃ x, o = .tcb x ∧ x.tcbDomain = d ∧ x.tcbPriority = pr ∧ runnable x.tcbState = true) :
    RQd { σ with kheap := Function.update σ.kheap p (some o) } := by
  intro d pr t ht
  by_cases e : t = p
  · subst e
    obtain ⟨x, rfl, h1, h2, h3⟩ := ho d pr ht
    exact ⟨x, by simp, h1, h2, h3⟩
  · obtain ⟨x, hx, h1, h2, h3⟩ := h d pr t ht
    exact ⟨x, by simp [Function.update_apply, e, hx], h1, h2, h3⟩

variable {X : (Domain → Priority → ReadyQueue) → Prop}

/-- `setObject`: a TCB write keeps the old TCB's domain and priority, and a
queued TCB stays runnable. -/
theorem tqx_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : RQd σ → ∀ x, σ.kheap p = some (.tcb x) → ∀ y, o = .tcb y →
      y.tcbDomain = x.tcbDomain ∧ y.tcbPriority = x.tcbPriority ∧
        ((∃ d pr, p ∈ σ.readyQueues d pr) → runnable y.tcbState = true)) :
    IKp (TQX X) σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine ⟨rqd_update hσ.1 p o fun d pr hp => ?_, hσ.2⟩
  obtain ⟨x0, hx0, h1, h2, -⟩ := hσ.1 d pr p hp
  rw [hk] at hx0; cases hx0
  obtain ⟨y, rfl⟩ := q1_aType_tcb hty.symm
  obtain ⟨e1, e2, e3⟩ := ho hσ.1 x0 hk y rfl
  exact ⟨y, rfl, e1.trans h1, e2.trans h2, e3 ⟨d, pr, hp⟩⟩

theorem tqx_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → False) :
    IK (TQX X) (setObject (Z := Unit) p o) :=
  fun σ => tqx_setObject_p p o σ fun _ _ _ y e => (ho y e).elim

/-- A TCB write keeping domain and priority, runnable if queued. -/
theorem tqx_setTcb_p (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (hy : y.tcbDomain = x.tcbDomain ∧ y.tcbPriority = x.tcbPriority ∧
      ((∃ d pr, p ∈ σ.readyQueues d pr) → runnable y.tcbState = true)) :
    IKp (TQX X) σ (setObject (Z := Unit) p (.tcb y)) :=
  tqx_setObject_p _ _ σ fun _ x0 hk y' e => by
    rw [hx] at hk; cases hk; cases e; exact hy

/-- A TCB write keeping domain, priority and state. -/
theorem tqx_setTcb_keep (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (h1 : y.tcbDomain = x.tcbDomain) (h2 : y.tcbPriority = x.tcbPriority) (h3 : y.tcbState = x.tcbState) :
    IKp (TQX X) σ (setObject (Z := Unit) p (.tcb y)) :=
  tqx_setObject_p _ _ σ fun hσ x0 hk y' e => by
    rw [hx] at hk; cases hk; cases e
    refine ⟨h1, h2, fun ⟨d, pr, hp⟩ => ?_⟩
    obtain ⟨x1, hx1, -, -, hr⟩ := hσ d pr p hp
    rw [hx] at hx1; cases hx1; rw [h3]; exact hr

/-- A TCB write at a thread in no ready queue (domain, priority and state free). -/
theorem tqx_setTcb_noQ (p : ObjRef) (y : Tcb) (σ : State Unit) (hq : NoQ p σ.readyQueues) :
    IKp (TQX X) σ (setObject (Z := Unit) p (.tcb y)) := by
  unfold setObject
  intro hσ x ⟨z, hz, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨y1, y2⟩ := z
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨rqd_update hσ.1 p _ fun d pr hp => (hq d pr hp).elim, hσ.2⟩

theorem tqx_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    IK (TQX X) (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo setObject
  intro σ hσ x ⟨y, hy, hx⟩
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
  refine ⟨rqd_update hσ.1 p _ fun d pr hp => ?_, hσ.2⟩
  exfalso
  obtain ⟨x0, hx0, -⟩ := hσ.1 d pr p hp
  rw [hk] at hx0; cases hx0
  simp [isSimpleType, aType] at hsimp

theorem tqx_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbDomain = x.tcbDomain ∧ (f x).tcbPriority = x.tcbPriority ∧ (f x).tcbState = x.tcbState) :
    IK (TQX X) (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx =>
    tqx_setTcb_keep _ x σ (getTcb_kheap hx) _ (hf x).1 (hf x).2.1 (hf x).2.2

/-- Any `thread_set` of a thread in no ready queue. -/
theorem tqx_threadSet_noQ (f : Tcb → Tcb) (t : ObjRef) (σ : State Unit) (hq : NoQ t σ.readyQueues) :
    IKp (TQX X) σ (threadSet (Z := Unit) f t) := by
  unfold threadSet
  intro hσ y ⟨z, hz, hy⟩
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    exact tqx_setTcb_noQ _ _ σ hq hσ y hy

theorem tqx_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) :
    IK (TQX X) (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => tqx_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl rfl rfl

theorem tqx_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : IK (TQX X) (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (tqx_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl rfl rfl) fun _ => ik_pure _

theorem tqx_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) :
    IK (TQX X) (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (tqx_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl rfl rfl) fun _ => ?_
  repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

theorem tqx_setCap (c : Cap) (sl : CslotPtr) : IK (TQX X) (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (tqx_setObject_p _ _ σ fun _ _ _ _ e => by cases e)
    · exact ikp_fail_bind
  · rename_i tcb
    split
    · exact ikp_pure_bind (tqx_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    split
    · exact ikp_pure_bind (tqx_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    split
    · exact ikp_pure_bind (tqx_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    split
    · exact ikp_pure_bind (tqx_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    split
    · exact ikp_pure_bind (tqx_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    split
    · exact ikp_pure_bind (tqx_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

/-- `detype` of a region holding no queued thread. -/
theorem tqx_detype (S : Set ObjRef) {σ : State Unit} (h : TQX X σ)
    (hS : ∀ d p t, t ∈ σ.readyQueues d p → t ∉ S) : TQX X (detype S σ) := by
  refine ⟨fun d p t ht => ?_, h.2⟩
  obtain ⟨x, hx, h1, h2, h3⟩ := h.1 d p t ht
  refine ⟨x, ?_, h1, h2, h3⟩
  show (if t ∈ S then none else σ.kheap t) = _
  rw [ite_eq_right_iff.2 fun h => absurd h (hS d p t ht), hx]

/-- `delete_objects` of a region holding no queued thread. -/
theorem tqx_deleteObjects_p (ptr : Word) (bits : Nat) (σ : State Unit)
    (hD : ∀ d p t, t ∈ σ.readyQueues d p → t ∉ SInvU.delR ptr bits) :
    IKp (TQX X) σ (deleteObjects (Z := Unit) ptr bits) := by
  intro hσ y hy
  obtain ⟨ms, e⟩ := SInvU.deleteObjects_out hy
  rw [e]
  exact tqx_detype _ hσ hD

theorem tqx_retype_kh {σ : State Unit} (ps : List ObjRef) (dO : KernelObject) (h : TQX X σ)
    (hF : ∀ q ∈ ps, ∀ d p, q ∉ σ.readyQueues d p) :
    TQX X { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } := by
  refine ⟨fun d p t ht => ?_, h.2⟩
  obtain ⟨x, hx, h1, h2, h3⟩ := h.1 d p t ht
  refine ⟨x, ?_, h1, h2, h3⟩
  show (ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap) t = _
  rw [SInvU.foldr_upd, if_neg fun hm => hF t hm d p ht, hx]

theorem mem_gets_q {β : Type} {g : State Unit → β} {σ : State Unit} {y : β × State Unit}
    (h : y ∈ ((NonDet.gets g : NonDet (State Unit) β) σ).1) : y = (g σ, σ) := Set.mem_singleton_iff.1 h

/-- `retype_region` at addresses no queued thread occupies. -/
theorem tqx_retypeRegionWith_p (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n o : Nat)
    (ty : ApiObjectType) (dev : Bool) (σ : State Unit)
    (hF : ∀ q ∈ SInvU.retPtrs ptr n (bA ty o), ∀ d p, q ∉ σ.readyQueues d p) :
    IKp (TQX X) σ (retypeRegionWith (Z := Unit) bA ptr n o ty dev) := by
  intro hσ y hy
  unfold retypeRegionWith at hy
  obtain ⟨z1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨z2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  show TQX X z3.2
  unfold NonDet.when at h3
  split at h3
  · obtain ⟨w1, hw1, h3⟩ := h3
    rw [mem_gets_q hw1] at h3
    obtain ⟨w2, hw2, h3⟩ := h3
    rw [mem_gets_q hw2] at h3
    obtain ⟨w3, hw3, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 hw3] at h3
    rw [Set.mem_singleton_iff.1 h3]
    exact tqx_retype_kh _ _ hσ hF
  · rw [Set.mem_singleton_iff.1 h3]; exact hσ

/-! ## `tcb_sched_action` -/

/-- **`tcb_sched_action`**: an action whose new queue holds old members and
the thread, the latter only when it is runnable at this state. -/
theorem tqx_tcbSchedAction_p (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) (σ : State Unit)
    (hact : RQd σ → ∀ q u, u ∈ act t q → u ∈ q ∨
      (u = t ∧ ∃ x, σ.kheap t = some (.tcb x) ∧ runnable x.tcbState = true))
    (hX : ∀ x, σ.kheap t = some (.tcb x) → X σ.readyQueues → X (fun d1 p1 =>
      if d1 = x.tcbDomain ∧ p1 = x.tcbPriority then act t (σ.readyQueues x.tcbDomain x.tcbPriority)
      else σ.readyQueues d1 p1)) :
    IKp (TQX X) σ (tcbSchedAction (Z := Unit) act t) := by
  intro hσ y hy
  obtain ⟨x, hx, e⟩ := q1_tsa_out hy
  rw [e]
  refine ⟨fun d p u hu => ?_, hX x hx hσ.2⟩
  dsimp only at hu
  split at hu
  · rename_i e
    obtain ⟨rfl, rfl⟩ := e
    rcases hact hσ.1 _ u hu with hu | ⟨rfl, x', hx', hr⟩
    · exact hσ.1 _ _ u hu
    · rw [hx] at hx'; cases hx'; exact ⟨x, hx, rfl, rfl, hr⟩
  · exact hσ.1 d p u hu

/-- The dequeue. -/
theorem tq_dequeue (t : ObjRef) : TQK (tcbSchedAction (Z := Unit) tcbSchedDequeue t) :=
  fun σ => tqx_tcbSchedAction_p _ t σ (fun _ q u hu => Or.inl (List.mem_filter.1 hu).1) fun _ _ _ => trivial

/-- **After a dequeue the thread is in no ready queue.** -/
theorem tq_dequeue_noQ (t : ObjRef) (σ : State Unit) (h : TQ σ) (y : Unit × State Unit)
    (hy : y ∈ (tcbSchedAction (Z := Unit) tcbSchedDequeue t σ).1) : TQU t y.2 :=
  ⟨(tq_dequeue t σ h y hy).1, (q1_dequeue_hk t σ (tq_t1 h.1) y hy).2⟩

/-- An enqueue / append of a thread runnable at this state. -/
theorem tq_enq_p (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) (σ : State Unit)
    (hact : ∀ q u, u ∈ act t q → u ∈ q ∨ u = t)
    (hr : ∃ x, σ.kheap t = some (.tcb x) ∧ runnable x.tcbState = true) :
    IKp TQ σ (tcbSchedAction (Z := Unit) act t) :=
  tqx_tcbSchedAction_p act t σ (fun _ q u hu => (hact q u hu).imp id fun e => ⟨e, hr⟩) fun _ _ _ => trivial

/-! ## Thread states -/

theorem tqx_setThreadStateAct (t : ObjRef) : IK (TQX X) (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct setSchedulerAction
  repeat' (first | ik_step0 | ik_unfold)

/-- **`set_thread_state`**: a runnable state, or a thread in no ready queue. -/
theorem tqx_setThreadState_p (t : ObjRef) (ts : ThreadState) (σ : State Unit)
    (h : runnable ts = true ∨ NoQ t σ.readyQueues) :
    IKp (TQX X) σ (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ikp_bind ?_ fun _ => tqx_setThreadStateAct t
  rcases h with h | h
  · unfold threadSet
    intro hσ y ⟨z, hz, hy⟩
    unfold NonDet.getsThe at hz
    cases e : getTcb t σ with
    | none => rw [e] at hz; exact hz.elim
    | some a =>
      rw [e] at hz
      obtain rfl := Set.mem_singleton_iff.1 hz
      exact tqx_setTcb_p _ a σ (getTcb_kheap e) { a with tcbState := ts } ⟨rfl, rfl, fun _ => h⟩ hσ y hy
  · exact tqx_threadSet_noQ _ t σ h

theorem tqx_setThreadState_r (t : ObjRef) (ts : ThreadState) (h : runnable ts = true) :
    IK (TQX X) (setThreadState (Z := Unit) t ts) :=
  fun σ => tqx_setThreadState_p t ts σ (Or.inl h)

/-- A thread that is not runnable at this state may get any state. -/
theorem tqx_setThreadState_nr (t : ObjRef) (ts : ThreadState) (σ : State Unit) (x : Tcb)
    (hx : σ.kheap t = some (.tcb x)) (hr : runnable x.tcbState = false) :
    IKp (TQX X) σ (setThreadState (Z := Unit) t ts) :=
  fun hσ => tqx_setThreadState_p t ts σ (Or.inr (rqd_noQ hσ.1 hx hr)) hσ

theorem tqx_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbDomain = x.tcbDomain ∧ (fn v x).tcbPriority = x.tcbPriority ∧
      (fn v x).tcbState = x.tcbState) :
    IK (TQX X) (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact tqx_threadSet _ _ (h _)

/-! ## `tq_auto` -/

macro "tq_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _; exact ⟨rfl, rfl, rfl⟩)
  | (intro _ _; exact ⟨rfl, rfl, rfl⟩)
  | rfl
  | (simp; done)
  | decide)

syntax "tq_leaf" : tactic
macro_rules | `(tactic| tq_leaf) => `(tactic| fail "no tq_leaf")

macro "tq_auto" : tactic => `(tactic| repeat' (first | tq_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| tq_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); tq_side))
macro_rules | `(tactic| tq_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); tq_side))
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| tq_leaf) => `(tactic| ((with_reducible refine tqx_setObject _ _ ?_); tq_side))
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tqx_setSimpleKo _ _ _)
macro_rules | `(tactic| tq_leaf) => `(tactic| ((with_reducible refine tqx_threadSet _ _ ?_); tq_side))
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tqx_archThreadSet _ _)
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tqx_asUser _ _)
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tqx_setMrs _ _ _)
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tqx_setCap _ _)
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tq_dequeue _)
macro_rules | `(tactic| tq_leaf) => `(tactic| ((with_reducible refine tqx_setThreadState_r _ _ ?_); tq_side))
macro_rules | `(tactic| tq_leaf) => `(tactic| ((with_reducible refine tqx_optionUpdateThread _ _ _ ?_); tq_side))
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tqx_setThreadStateAct _)

/-! ## `reschedule_required`, `possible_switch_to` -/

theorem ikp_strengthen {P P' : State Unit → Prop} {α : Type} {σ : State Unit} {m : NonDet (State Unit) α}
    (h : P σ → P' σ) (hm : IK P' m) (hw : ∀ s, P' s → P s) : IKp P σ m :=
  fun hσ x hx => hw _ (hm σ (h hσ) x hx)

/-- TQ and a fact on the heap only (kept by every ready-queue / scheduler-action write). -/
abbrev TQC (C : (ObjRef → Option KernelObject) → Prop) (σ : State Unit) : Prop := TQ σ ∧ C σ.kheap

/-- `t` is a runnable TCB of the heap. -/
abbrev RnH (t : ObjRef) (kh : ObjRef → Option KernelObject) : Prop :=
  ∃ x, kh t = some (.tcb x) ∧ runnable x.tcbState = true

theorem tqc_enq {C : (ObjRef → Option KernelObject) → Prop} (act : ObjRef → List ObjRef → List ObjRef)
    (t : ObjRef) (hact : ∀ q u, u ∈ act t q → u ∈ q ∨ u = t) (hC : ∀ kh, C kh → RnH t kh) :
    IK (TQC C) (tcbSchedAction (Z := Unit) act t) := by
  intro σ hσ y hy
  refine ⟨tq_enq_p act t σ hact (hC _ hσ.2) hσ.1 y hy, ?_⟩
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]; exact hσ.2

theorem tqc_deq {C : (ObjRef → Option KernelObject) → Prop} (t : ObjRef) :
    IK (TQC C) (tcbSchedAction (Z := Unit) tcbSchedDequeue t) := by
  intro σ hσ y hy
  refine ⟨tq_dequeue t σ hσ.1 y hy, ?_⟩
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]; exact hσ.2

theorem schedulable_rn {σ : State Unit} {t : ObjRef} (hs : schedulable t σ = true) : RnH t σ.kheap := by
  unfold schedulable at hs
  have hs' := of_decide_eq_true hs
  obtain ⟨h1, -⟩ := hs'
  unfold optPred optMapSome tcbsOf tcbsOfKh optMap at h1
  revert h1
  cases e : σ.kheap t with
  | none => simp
  | some o =>
    cases o <;> simp [tcbOf]
    rename_i x
    exact fun h => ⟨x, e, h⟩

/-- **`reschedule_required`** (the switch target is enqueued only after
`schedulable` read it runnable at the same state). -/
theorem tqc_rescheduleRequired (C : (ObjRef → Option KernelObject) → Prop) :
    IK (TQC C) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  refine ik_gets_bind fun σ => ?_
  dsimp only
  split
  · rename_i t _
    refine ikp_gets_bind ?_
    refine ikp_bind ?_ fun _ => by repeat' (first | ik_step0 | ik_unfold)
    unfold NonDet.when
    split
    · rename_i hs
      refine ikp_strengthen (P' := TQC (fun kh => C kh ∧ RnH t kh))
        (fun h => ⟨h.1, h.2, schedulable_rn hs⟩) ?_ fun _ h => ⟨h.1, h.2.1⟩
      repeat' (first | (with_reducible exact tqc_enq (C := fun kh => C kh ∧ RnH t kh) _ _ (q1_enq _) fun _ h => h.2) | ik_step0 | ik_unfold)
    · exact ikp_of_ik (ik_pure _) σ
  · exact ikp_of_ik (by repeat' (first | ik_step0 | ik_unfold)) σ

theorem tq_of_tqc {α : Type} {m : NonDet (State Unit) α} (h : IK (TQC fun _ => True) m) : TQK m :=
  fun σ hσ x hx => (h σ ⟨hσ, trivial⟩ x hx).1

theorem tq_rescheduleRequired : TQK (rescheduleRequired (Z := Unit)) := tq_of_tqc (tqc_rescheduleRequired _)
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tq_rescheduleRequired)

/-- **`possible_switch_to`** of a thread runnable at this state. -/
theorem tqc_possibleSwitchTo {C : (ObjRef → Option KernelObject) → Prop} (t : ObjRef)
    (hC : ∀ kh, C kh → RnH t kh) : IK (TQC C) (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo setSchedulerAction
  repeat' (first | (with_reducible exact tqc_enq _ _ (q1_enq _) hC) | (with_reducible exact tqc_rescheduleRequired _) | ik_step0 | ik_unfold)

theorem tq_possibleSwitchTo_p (t : ObjRef) (σ : State Unit) (hr : RnH t σ.kheap) :
    IKp TQ σ (possibleSwitchTo (Z := Unit) t) :=
  ikp_strengthen (P' := TQC (RnH t)) (fun h => ⟨h, hr⟩) (tqc_possibleSwitchTo t fun _ h => h) fun _ h => h.1

/-! ## Threads in no ready queue -/

/-- Any state for a thread in no ready queue. -/
theorem tqu_setThreadState (t : ObjRef) (ts : ThreadState) : IK (TQU t) (setThreadState (Z := Unit) t ts) :=
  fun σ hσ => tqx_setThreadState_p t ts σ (Or.inr hσ.2) hσ
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tqu_setThreadState _ _)

theorem tqu_threadSet (f : Tcb → Tcb) (t : ObjRef) : IK (TQU t) (threadSet (Z := Unit) f t) :=
  fun σ hσ => tqx_threadSet_noQ f t σ hσ.2 hσ

theorem ikq_threadGet_bind {P : State Unit → Prop} {β γ : Type} {f : Tcb → β} {t : ObjRef}
    {k : β → NonDet (State Unit) γ}
    (h : ∀ σ x, σ.kheap t = some (.tcb x) → IKp P σ (k (f x))) : IK P (threadGet (Z := Unit) f t >>= k) := by
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  exact h σ x hx hσ y hy

/-- The outcome of `thread_set`. -/
theorem q3_threadSet_out {f : Tcb → Tcb} {t : ObjRef} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (threadSet (Z := Unit) f t σ).1) :
    ∃ x, σ.kheap t = some (.tcb x) ∧ y.2.kheap t = some (.tcb (f x)) := by
  unfold threadSet at hy
  obtain ⟨z, hz, hy⟩ := hy
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    refine ⟨a, getTcb_kheap e, ?_⟩
    unfold setObject at hy
    obtain ⟨w, hw, hy⟩ := hy
    obtain ⟨hk, hs⟩ := mem_getObject hw
    obtain ⟨w1, w2⟩ := w
    simp only at hk hs; subst hs
    obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
    obtain ⟨v, hv, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hv] at hy
    rw [Set.mem_singleton_iff.1 hy]
    simp

/-! ## `set_priority`, `set_domain` -/

/-- **`set_priority` keeps TQ** (no premise: a thread that is not runnable is
in no ready queue, so the priority write needs no dequeue; a runnable one is
dequeued, written and enqueued again while still runnable). -/
theorem tq_setPriority (t : ObjRef) (prio : Priority) : TQK (setPriority (Z := Unit) t prio) := by
  unfold setPriority getThreadState threadSetPriority getTcbQueue
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  dsimp only at hy
  split at hy
  · rename_i hrun
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨x1, hx1, rfl⟩ := q1_mem_threadGet hz
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨x2, hx2, rfl⟩ := q1_mem_threadGet hz
    rw [hx] at hx1 hx2; cases hx1; cases hx2
    obtain ⟨z, ⟨w, hw, hz⟩, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hw
    obtain rfl := Set.mem_singleton_iff.1 hz
    obtain ⟨w, hw, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hw
    dsimp only at hy
    split at hy
    · obtain ⟨z1, hz1, hy⟩ := hy
      have h1 := tq_dequeue_noQ t σ hσ z1 hz1
      have hk1 : z1.2.kheap = σ.kheap := by
        obtain ⟨_, -, e⟩ := q1_tsa_out hz1; rw [e]
      obtain ⟨z2, hz2, hy⟩ := hy
      have h2 : TQU t z2.2 := tqx_threadSet_noQ _ t z1.2 h1.2 h1 z2 hz2
      have hr2 : RnH t z2.2.kheap := by
        obtain ⟨x', hx', e⟩ := q3_threadSet_out hz2
        rw [hk1, hx] at hx'; cases hx'
        exact ⟨_, e, hrun⟩
      obtain ⟨z3, hz3, hy⟩ := hy
      have h3 := tq_enq_p _ t z2.2 (q1_enq t) hr2 ⟨h2.1, trivial⟩ z3 hz3
      exact tq_rescheduleRequired _ h3 y hy
    · rename_i hn
      exact tqx_threadSet_noQ _ t σ (fun d p hp => by
        obtain ⟨x', hx', h1, h2, -⟩ := hσ.1 d p t hp
        rw [hx] at hx'; cases hx'
        subst h1; subst h2
        exact hn (Or.inl hp)) hσ y hy
  · rename_i hrun
    obtain ⟨z1, hz1, hy⟩ := hy
    have h1 := tqx_threadSet_noQ (X := TT) _ t σ
      (rqd_noQ hσ.1 hx (by simpa using hrun)) hσ z1 hz1
    refine (?_ : TQK _) z1.2 h1 y hy
    tq_auto
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tq_setPriority _ _)

/-- **`set_domain` keeps TQ** (dequeue, write, enqueue only if `schedulable`). -/
theorem tq_setDomain (t : ObjRef) (dom : Domain) : TQK (setDomain (Z := Unit) t dom) := by
  unfold setDomain threadSetDomain
  refine ik_gets_bind fun σ => ?_
  intro hσ y ⟨z1, hz1, hy⟩
  have h1 := tq_dequeue_noQ t σ hσ z1 hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  have h2 := tqx_threadSet_noQ (X := TT) _ t z1.2 h1.2 ⟨h1.1, trivial⟩ z2 hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz3
  obtain ⟨z4, hz4, hy⟩ := hy
  have h4 : TQ z4.2 := by
    unfold NonDet.when at hz4
    split at hz4
    · rename_i hs
      exact tq_enq_p _ t z2.2 (q1_enq t) (schedulable_rn hs) h2 z4 hz4
    · obtain rfl := Set.mem_singleton_iff.1 hz4; exact h2
  unfold NonDet.when at hy
  split at hy
  · exact tq_rescheduleRequired _ h4 y hy
  · obtain rfl := Set.mem_singleton_iff.1 hy; exact h4
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tq_setDomain _ _)

/-! ## Cancelling a blocked thread, `suspend` -/

theorem tqu_of {σ : State Unit} {t : ObjRef} {x : Tcb} (h : TQ σ) (hx : σ.kheap t = some (.tcb x))
    (hr : runnable x.tcbState = false) : TQU t σ := ⟨h.1, rqd_noQ h.1 hx hr⟩

/-- **`cancel_ipc`**: it writes only the state of a thread it read blocked. -/
theorem tq_cancelIpc (t : ObjRef) : TQK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState
  refine ikq_threadGet_bind fun σ x hx => ?_
  cases hs : x.tcbState
  case running | runningVM | inactive | restart | idleThreadState => exact ikp_of_ik (by tq_auto) σ
  all_goals
    refine ikp_strengthen (P' := TQU t) (fun h => tqu_of h hx (by rw [hs]; rfl)) ?_ fun _ h => ⟨h.1, trivial⟩
    tq_auto
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tq_cancelIpc _)

/-- **`suspend`** (it dequeues before making the thread Inactive). -/
theorem tq_suspend (t : ObjRef) : TQK (suspend (Z := Unit) t) := by
  unfold suspend
  refine ik_bind (tq_cancelIpc t) fun _ => ?_
  refine ik_bind (by tq_auto) fun _ => ?_
  refine ik_bind (by tq_auto) fun _ => ?_
  intro σ hσ y ⟨z1, hz1, hy⟩
  have h1 := tq_dequeue_noQ t σ hσ z1 hz1
  exact (show IK (TQU t) (do
    tcbReleaseRemove (Z := Unit) t
    schedContextCancelYieldTo t
    setThreadState t .inactive) by tq_auto) z1.2 h1 y hy |>.1 |> fun h => ⟨h, trivial⟩
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tq_suspend _)

/-! ## A thread's state across writes elsewhere -/

/-- `t` is a TCB that is not runnable. -/
abbrev NRH (t : ObjRef) (kh : ObjRef → Option KernelObject) : Prop :=
  ∃ x, kh t = some (.tcb x) ∧ runnable x.tcbState = false

/-- A non-TCB `setObject` keeping a heap fact that holds after every write of
a non-TCB object over an object of the same type. -/
theorem tqc_setObject_nt {C : (ObjRef → Option KernelObject) → Prop}
    (hC : ∀ kh p o0 o, C kh → kh p = some o0 → aType o0 = aType o → (∀ y, o ≠ .tcb y) →
      C (Function.update kh p (some o)))
    (p : ObjRef) (o : KernelObject) (ho : ∀ y, o = .tcb y → False) : IK (TQC C) (setObject (Z := Unit) p o) := by
  intro σ hσ y hy
  refine ⟨tqx_setObject p o ho σ hσ.1 y hy, ?_⟩
  unfold setObject at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨z1, z2⟩ := z
  simp only at hk hs; subst hs
  obtain ⟨w, ⟨hty, rfl⟩, hy⟩ := hy
  obtain ⟨v, hv, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hv] at hy
  rw [Set.mem_singleton_iff.1 hy]
  exact hC _ p z1 o hσ.2 hk hty fun y e => ho y e

theorem stH_upd {S : ThreadState → Prop} {t : ObjRef} (kh : ObjRef → Option KernelObject) (p : ObjRef)
    (o0 o : KernelObject) (h : ∃ x, kh t = some (.tcb x) ∧ S x.tcbState) (hp : kh p = some o0)
    (hty : aType o0 = aType o) (ho : ∀ y, o ≠ .tcb y) :
    ∃ x, Function.update kh p (some o) t = some (.tcb x) ∧ S x.tcbState := by
  obtain ⟨x, hx, hs⟩ := h
  by_cases e : t = p
  · subst e
    rw [hx] at hp; cases hp
    obtain ⟨y, rfl⟩ := q1_aType_tcb hty.symm
    exact (ho y rfl).elim
  · exact ⟨x, by rw [Function.update_apply, if_neg e, hx], hs⟩

theorem tqc_setObject_rn (t p : ObjRef) (o : KernelObject) (ho : ∀ y, o = .tcb y → False) :
    IK (TQC (RnH t)) (setObject (Z := Unit) p o) :=
  tqc_setObject_nt (fun kh p o0 o h hp hty ho => stH_upd (S := fun s => runnable s = true) kh p o0 o h hp hty ho) p o ho

theorem tqc_setObject_nr (t p : ObjRef) (o : KernelObject) (ho : ∀ y, o = .tcb y → False) :
    IK (TQC (NRH t)) (setObject (Z := Unit) p o) :=
  tqc_setObject_nt (fun kh p o0 o h hp hty ho => stH_upd (S := fun s => runnable s = false) kh p o0 o h hp hty ho) p o ho

/-- The outcome of `set_thread_state`. -/
theorem q3_setThreadState_out {t : ObjRef} {ts : ThreadState} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (setThreadState (Z := Unit) t ts σ).1) :
    ∃ x, σ.kheap t = some (.tcb x) ∧ y.2.kheap t = some (.tcb { x with tcbState := ts }) := by
  unfold setThreadState at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, e⟩ := q3_threadSet_out hz
  refine ⟨x, hx, ?_⟩
  have : IK (fun s => s.kheap t = some (.tcb { x with tcbState := ts })) (setThreadStateAct (Z := Unit) t) := by
    unfold setThreadStateAct setSchedulerAction; repeat' (first | ik_step0 | ik_unfold)
  exact this z.2 e y hy

/-- A write of a non-runnable state to a non-runnable thread. -/
theorem tqc_setThreadState_nr (t : ObjRef) (ts : ThreadState) (h : runnable ts = false) :
    IK (TQC (NRH t)) (setThreadState (Z := Unit) t ts) := by
  intro σ hσ y hy
  obtain ⟨x, hx, hr⟩ := hσ.2
  refine ⟨tqx_setThreadState_nr t ts σ x hx hr hσ.1 y hy, ?_⟩
  obtain ⟨x', hx', e⟩ := q3_setThreadState_out hy
  exact ⟨_, e, h⟩

/-- A runnable state, then the thread is a runnable TCB. -/
theorem tqc_setThreadState_r (t : ObjRef) (ts : ThreadState) (h : runnable ts = true) (σ : State Unit)
    (y : Unit × State Unit) (hσ : TQ σ) (hy : y ∈ (setThreadState (Z := Unit) t ts σ).1) : TQC (RnH t) y.2 := by
  refine ⟨tqx_setThreadState_r t ts h σ hσ y hy, ?_⟩
  obtain ⟨x', hx', e⟩ := q3_setThreadState_out hy
  exact ⟨_, e, h⟩

/-- **`reply_unlink_tcb`** (it asserts the thread blocked before making it Inactive). -/
theorem tq_replyUnlinkTcb (t r : ObjRef) : TQK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb
  refine ik_bind (by tq_auto) fun reply => ?_
  refine ik_bind (ik_assert _) fun _ => ?_
  unfold getThreadState
  refine ikq_threadGet_bind fun σ x hx => ?_
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨hP, rfl⟩ := hz
  have hr : runnable x.tcbState = false := by
    rcases hP with h | ⟨ep, d, h⟩ <;> rw [h] <;> rfl
  refine ((?_ : IK (TQC (NRH t)) _) σ ⟨hσ, x, hx, hr⟩ y hy).1
  repeat' (first | (with_reducible exact tqc_setThreadState_nr _ _ rfl) | ((with_reducible refine tqc_setObject_nr _ _ _ ?_); intro _ h; cases h) | ik_step0 | ik_unfold)
macro_rules | `(tactic| tq_leaf) => `(tactic| with_reducible exact tq_replyUnlinkTcb _ _)

end

end Fl4Proofs.P3.SInvQ
