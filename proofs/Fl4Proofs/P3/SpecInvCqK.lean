/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ctq2): **T1, the ready
queues' TCB half of l4v `valid_ready_qs`: every thread in ready queue
`(d, p)` is a TCB of domain `d` and priority `p`** (spec side only; imports
only Fl4Spec via SpecInvNativeScopeT, outside the JAtZ cone).

* `T1 σ := ∀ d p t, t ∈ readyQueues d p → ∃ x, kheap t = tcb x ∧
  x.tcbDomain = d ∧ x.tcbPriority = p` (ctnq1's T1; no distinctness is needed:
  `tcb_sched_dequeue` is a filter).
* Leaves (SpecInvQDomK's template): every heap write keeps T1 because
  `set_object` asserts the old and new object types agree (a non-TCB write
  hits no queued pointer) and every TCB write but `thread_set_priority` /
  `thread_set_domain` keeps both fields (`q1_threadSet` asks it);
  `tcb_sched_action` reads the thread's own domain and priority at the same
  state, so an enqueue lands in its own queue (`q1_tcbSchedAction`).
* Not leaves (handled by hand, or open: KENTRY-PLAN ctq2): `set_priority`,
  `set_domain` (`thread_set_priority` / `thread_set_domain`), `retype_region`
  (overwrites without a freeness check), `delete_objects` (`q1_detype` under
  "no queued thread in the region").
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- **T1 [J]: ready-queued threads are TCBs of that queue's domain and
priority** (l4v `valid_ready_qs`: `etcb_at (λt. tcb_priority t = p ∧
tcb_domain t = d)` for every member of `ready_queues s d p`). -/
abbrev T1 (σ : State Unit) : Prop :=
  ∀ d p t, t ∈ σ.readyQueues d p → ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbDomain = d ∧ x.tcbPriority = p

abbrev Q1K {α : Type} (m : NonDet (State Unit) α) : Prop := IK T1 m
abbrev Q1KE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE T1 m

/-- **T1 at boot** (empty queues). -/
theorem boot_t1 : T1 (initASt (Z := Unit)) := fun _ _ _ h => (List.not_mem_nil h).elim

/-! ## Heap updates -/

theorem q1_update {σ : State Unit} (h : T1 σ) (p : ObjRef) (o : KernelObject)
    (ho : ∀ d pr, p ∈ σ.readyQueues d pr → ∃ x, o = .tcb x ∧ x.tcbDomain = d ∧ x.tcbPriority = pr) :
    T1 { σ with kheap := Function.update σ.kheap p (some o) } := by
  intro d pr t ht
  by_cases e : t = p
  · subst e
    obtain ⟨x, rfl, h1, h2⟩ := ho d pr ht
    exact ⟨x, by simp, h1, h2⟩
  · obtain ⟨x, hx, h1, h2⟩ := h d pr t ht
    exact ⟨x, by simp [Function.update_apply, e, hx], h1, h2⟩

theorem q1_aType_tcb {o : KernelObject} (h : aType o = .aTCB) : ∃ y, o = .tcb y := by
  cases o with
  | tcb y => exact ⟨y, rfl⟩
  | cnode sz cs => by_cases hw : wellFormedCnodeN sz cs <;> simp [aType, hw] at h
  | schedContext y n => by_cases hw : validSchedContextSize n <;> simp [aType, hw] at h
  | _ => simp [aType] at h

/-- `setObject` from a state where a TCB write keeps the old TCB's domain and priority. -/
theorem q1_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : T1 σ → ∀ x, σ.kheap p = some (.tcb x) → ∀ y, o = .tcb y →
      y.tcbDomain = x.tcbDomain ∧ y.tcbPriority = x.tcbPriority) :
    IKp T1 σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine q1_update hσ p o fun d pr hp => ?_
  obtain ⟨x0, hx0, h1, h2⟩ := hσ d pr p hp
  rw [hk] at hx0; cases hx0
  obtain ⟨y, rfl⟩ := q1_aType_tcb hty.symm
  obtain ⟨e1, e2⟩ := ho hσ x0 hk y rfl
  exact ⟨y, rfl, e1.trans h1, e2.trans h2⟩

/-- A non-TCB `setObject`. -/
theorem q1_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → False) :
    Q1K (setObject (Z := Unit) p o) :=
  fun σ => q1_setObject_p p o σ fun _ _ _ y e => (ho y e).elim

/-- A TCB write keeping domain and priority. -/
theorem q1_setTcb_p (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (hy : y.tcbDomain = x.tcbDomain ∧ y.tcbPriority = x.tcbPriority) :
    IKp T1 σ (setObject (Z := Unit) p (.tcb y)) :=
  q1_setObject_p _ _ σ fun _ x0 hk y' e => by
    rw [hx] at hk; cases hk; cases e; exact hy

theorem q1_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    Q1K (setSimpleKo (Z := Unit) f p e) := by
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
  refine q1_update hσ p _ fun d pr hp => ?_
  exfalso
  obtain ⟨x0, hx0, -⟩ := hσ d pr p hp
  rw [hk] at hx0; cases hx0
  simp [isSimpleType, aType] at hsimp

theorem q1_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbDomain = x.tcbDomain ∧ (f x).tcbPriority = x.tcbPriority) :
    Q1K (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx => q1_setTcb_p _ x σ (getTcb_kheap hx) _ (hf x)

theorem q1_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) :
    Q1K (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => q1_setTcb_p _ x σ (getTcb_kheap hx) _ ⟨rfl, rfl⟩

theorem q1_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : Q1K (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (q1_setTcb_p _ x σ (getTcb_kheap hx) _ ⟨rfl, rfl⟩) fun _ => ik_pure _

/-- The rest of `setMrs` after the register write: IPC-buffer stores. -/
macro "q1_mach" : tactic => `(tactic| repeat' (first | ik_step0 |
  (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold))

theorem q1_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : Q1K (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (q1_setTcb_p _ x σ (getTcb_kheap hx) _ ⟨rfl, rfl⟩) fun _ => ?_
  q1_mach

theorem q1_setCap (c : Cap) (sl : CslotPtr) : Q1K (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (q1_setObject_p _ _ σ fun _ _ _ _ e => by cases e)
    · exact ikp_fail_bind
  · rename_i tcb
    split
    · exact ikp_pure_bind (q1_setTcb_p _ tcb σ hk _ ⟨rfl, rfl⟩)
    split
    · exact ikp_pure_bind (q1_setTcb_p _ tcb σ hk _ ⟨rfl, rfl⟩)
    split
    · exact ikp_pure_bind (q1_setTcb_p _ tcb σ hk _ ⟨rfl, rfl⟩)
    split
    · exact ikp_pure_bind (q1_setTcb_p _ tcb σ hk _ ⟨rfl, rfl⟩)
    split
    · exact ikp_pure_bind (q1_setTcb_p _ tcb σ hk _ ⟨rfl, rfl⟩)
    split
    · exact ikp_pure_bind (q1_setTcb_p _ tcb σ hk _ ⟨rfl, rfl⟩)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

/-- `detype` of a region holding no queued thread. -/
theorem q1_detype (S : Set ObjRef) {σ : State Unit} (h : T1 σ)
    (hS : ∀ d p t, t ∈ σ.readyQueues d p → t ∉ S) : T1 (detype S σ) := by
  intro d p t ht
  obtain ⟨x, hx, h1, h2⟩ := h d p t ht
  refine ⟨x, ?_, h1, h2⟩
  show (if t ∈ S then none else σ.kheap t) = _
  rw [ite_eq_right_iff.2 fun h => absurd h (hS d p t ht), hx]

/-! ## `tcb_sched_action` -/

theorem q1_mem_threadGet {β : Type} {f : Tcb → β} {t : ObjRef} {σ : State Unit} {y : β × State Unit}
    (h : y ∈ (threadGet (Z := Unit) f t σ).1) : ∃ x, σ.kheap t = some (.tcb x) ∧ y = (f x, σ) := by
  unfold threadGet at h
  obtain ⟨z, hz, hy⟩ := h
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    have hz' := Set.mem_singleton_iff.1 hz
    subst hz'
    exact ⟨a, getTcb_kheap e, Set.mem_singleton_iff.1 hy⟩

/-- **`tcb_sched_action` keeps T1** for an action whose new queue holds only
old members and the thread: the thread's domain and priority are read at the
same state, so it lands in its own queue. -/
theorem q1_tcbSchedAction (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef)
    (hact : ∀ q u, u ∈ act t q → u ∈ q ∨ u = t) : Q1K (tcbSchedAction (Z := Unit) act t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x', hx', rfl⟩ := q1_mem_threadGet hz
  rw [hx] at hx'; cases hx'
  obtain ⟨z, ⟨w, hw, hz⟩, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hw
  obtain rfl := Set.mem_singleton_iff.1 hz
  obtain ⟨w, hw, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hw
  obtain rfl := Set.mem_singleton_iff.1 hy
  intro d p u hu
  dsimp only at hu
  split at hu
  · rename_i e
    obtain ⟨rfl, rfl⟩ := e
    rcases hact _ u hu with hu | rfl
    · exact hσ _ _ u hu
    · exact ⟨x, hx, rfl, rfl⟩
  · exact hσ d p u hu

theorem q1_enq (t : ObjRef) : ∀ q u, u ∈ tcbSchedEnqueue t q → u ∈ q ∨ u = t := by
  intro q u hu
  unfold tcbSchedEnqueue at hu
  split at hu
  · rcases List.mem_cons.1 hu with rfl | h
    · exact Or.inr rfl
    · exact Or.inl h
  · exact Or.inl hu

theorem q1_app (t : ObjRef) : ∀ q u, u ∈ tcbSchedAppend t q → u ∈ q ∨ u = t := by
  intro q u hu
  unfold tcbSchedAppend at hu
  split at hu
  · rcases List.mem_append.1 hu with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.1 h)
  · exact Or.inl hu

theorem q1_deq (t : ObjRef) : ∀ q u, u ∈ tcbSchedDequeue t q → u ∈ q ∨ u = t := by
  intro q u hu
  unfold tcbSchedDequeue at hu
  exact Or.inl (List.mem_filter.1 hu).1

/-! ## The leaves and `q1_auto` -/

/-- The side conditions of the leaves. -/
macro "q1_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _; exact ⟨rfl, rfl⟩)
  | (intro _ _; exact ⟨rfl, rfl⟩)
  | exact q1_enq _ | exact q1_app _ | exact q1_deq _
  | (simp; done)
  | decide)

syntax "q1_leaf" : tactic
macro_rules | `(tactic| q1_leaf) => `(tactic| fail "no q1_leaf")

macro "q1_auto" : tactic => `(tactic| repeat' (first | q1_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| q1_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); q1_side))
macro_rules | `(tactic| q1_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); q1_side))
macro_rules | `(tactic| q1_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| q1_leaf) => `(tactic| ((with_reducible refine q1_setObject _ _ ?_); q1_side))
macro_rules | `(tactic| q1_leaf) => `(tactic| with_reducible exact q1_setSimpleKo _ _ _)
macro_rules | `(tactic| q1_leaf) => `(tactic| ((with_reducible refine q1_threadSet _ _ ?_); q1_side))
macro_rules | `(tactic| q1_leaf) => `(tactic| with_reducible exact q1_archThreadSet _ _)
macro_rules | `(tactic| q1_leaf) => `(tactic| with_reducible exact q1_asUser _ _)
macro_rules | `(tactic| q1_leaf) => `(tactic| with_reducible exact q1_setMrs _ _ _)
macro_rules | `(tactic| q1_leaf) => `(tactic| with_reducible exact q1_setCap _ _)
macro_rules | `(tactic| q1_leaf) => `(tactic| ((with_reducible refine q1_tcbSchedAction _ _ ?_); q1_side))

theorem q1_setThreadState (t : ObjRef) (ts : ThreadState) : Q1K (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (q1_threadSet _ _ fun _ => ⟨rfl, rfl⟩) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; q1_auto
macro_rules | `(tactic| q1_leaf) => `(tactic| with_reducible exact q1_setThreadState _ _)

theorem q1_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbDomain = x.tcbDomain ∧ (fn v x).tcbPriority = x.tcbPriority) :
    Q1K (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact q1_threadSet _ _ (h _)
macro_rules | `(tactic| q1_leaf) => `(tactic| ((with_reducible refine q1_optionUpdateThread _ _ _ ?_); q1_side))

end

end Fl4Proofs.P3.SInvQ
