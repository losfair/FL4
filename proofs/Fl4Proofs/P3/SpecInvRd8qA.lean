/-
P3 (DESIGN.md §9), invariant line G1 (rd8q): **rd8n's `VB` (l4v
`valid_blocked`) carried spec-side: the frame kit** (spec side only, outside
the JAtZ cone; KENTRY-PLAN rd8n handoff 1).

`VB σ` reads, of each TCB, its state (runnable or not) and its SC binding, of
each SC whether it is active, the release queue (via `schedulable`), the ready
queues, the current thread and the scheduler action. Writers make a thread
schedulable in two steps (l4v: `set_thread_state t Running; …;
possible_switch_to t`), so the kit carries the exception form

* **`VE E σ`**: `VB` for every thread outside `E` (l4v
  `valid_blocked_except_set`); `vb_ve : VB σ ↔ VE ⊥ σ`, `ve_mono`, `ve_of`,
  `ve_kh`, `ve_drop` (leave the exception set once `t` is queued, not
  schedulable, ct or the switch target), `VEA` (no switch-target exemption)
  and `ve_setAction`.
* **`OKV old o`** (a heap write `VE` allows: a TCB written runnable and bound
  was a TCB runnable and bound to the same SC; an SC written active was an
  active SC), **`ve_upd`**, `sched_upd` / `sched_upd_ne`.
* Leaves (`VEK E := IK (VE E)`): `ve_setObject(_p)`, `ve_setSimpleKo`,
  `ve_setTcb_keep`, `ve_threadSet` (state kept, binding kept or cleared),
  `ve_setThreadState` (to a state that is not runnable), `ve_setThreadStateAct`
  (no hypothesis: it only replaces `resumeCurThread`), `ve_archThreadSet`,
  `ve_asUser`, `ve_setMrs`, `ve_setCap`, `ve_optionUpdateThread`,
  `ve_updateSchedContext` (active only where it was), `ve_tcbSchedAction`
  (an action keeping every queued thread: enqueue / append),
  **`ve_rescheduleRequired`**, **`ve_possibleSwitchTo`** (both without a
  hypothesis).
* Exception-changing steps (`HT P Q m`: every outcome of `m` from a `P` state
  is a `Q` state): **`ht_threadSet_x`** / **`ht_setThreadState_x`** (any write
  of `t`'s TCB: `VE E → VE (E ∪ {t})`), **`ht_possibleSwitchTo`** (`VE (E ∪
  {t}) → VE E`), **`ht_dequeue`** / **`ht_tcbReleaseRemove`** (`VE E → VE (E
  ∪ {t})`), `ht_setSchedulerAction` (from `VEA`).
-/
import Fl4Proofs.P3.SpecInvRd8nC
open Classical

namespace Fl4Proofs.P3.SInvR.B8q
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The invariant with an exception set -/

/-- `VB` for the threads outside `E` (l4v `valid_blocked_except_set`). -/
def VE (E : ObjRef → Prop) (σ : State Unit) : Prop :=
  ∀ t, ¬E t → schedulable t σ = true → t ≠ σ.curThread → σ.schedulerAction ≠ .switchThread t →
    ∃ d p, t ∈ σ.readyQueues d p

/-- `VE` without the switch-target exemption. -/
def VEA (E : ObjRef → Prop) (σ : State Unit) : Prop :=
  ∀ t, ¬E t → schedulable t σ = true → t ≠ σ.curThread → ∃ d p, t ∈ σ.readyQueues d p

abbrev VEK (E : ObjRef → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (VE E) m
abbrev VEKE (E : ObjRef → Prop) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (VE E) m

/-- `t` added to the exception set. -/
abbrev Ins (E : ObjRef → Prop) (t : ObjRef) : ObjRef → Prop := fun u => E u ∨ u = t

theorem vb_ve {σ : State Unit} : B8n.VB σ ↔ VE (fun _ => False) σ :=
  ⟨fun h t _ => h t, fun h t => h t not_false⟩

theorem ve_mono {E E' : ObjRef → Prop} {σ : State Unit} (hE : ∀ t, E t → E' t) (h : VE E σ) : VE E' σ :=
  fun t ht => h t (fun e => ht (hE t e))

theorem ve_ins {E : ObjRef → Prop} {σ : State Unit} (t : ObjRef) (h : VE E σ) : VE (Ins E t) σ :=
  ve_mono (fun _ e => Or.inl e) h

theorem ve_of {E : ObjRef → Prop} {σ σ' : State Unit} (h : VE E σ) (hc : σ'.curThread = σ.curThread)
    (ha : σ'.schedulerAction = σ.schedulerAction)
    (hq : ∀ d p u, ¬E u → u ∈ σ.readyQueues d p → u ∈ σ'.readyQueues d p)
    (hs : ∀ t, ¬E t → schedulable t σ' = true → schedulable t σ = true) : VE E σ' := by
  intro t ht hs' hc' ha'
  obtain ⟨d, p, hm⟩ := h t ht (hs t ht hs') (by rw [← hc]; exact hc') (by rw [← ha]; exact ha')
  exact ⟨d, p, hq d p t ht hm⟩

theorem ve_kh {E : ObjRef → Prop} {σ σ' : State Unit} (h : VE E σ) (hk : σ'.kheap = σ.kheap)
    (hr : σ'.releaseQueue = σ.releaseQueue) (hc : σ'.curThread = σ.curThread)
    (ha : σ'.schedulerAction = σ.schedulerAction) (hq : σ'.readyQueues = σ.readyQueues) : VE E σ' :=
  ve_of h hc ha (fun d p u _ hu => by rw [hq]; exact hu)
    (fun t _ hs => by rw [Sched.schedulable_heap hk hr] at hs; exact hs)

/-- Leave the exception set: `t` is queued, not schedulable, ct or the switch target. -/
theorem ve_drop {E : ObjRef → Prop} {σ : State Unit} {t : ObjRef} (h : VE (Ins E t) σ)
    (ht : schedulable t σ = true → t ≠ σ.curThread → σ.schedulerAction ≠ .switchThread t →
      ∃ d p, t ∈ σ.readyQueues d p) : VE E σ := by
  intro u hu hs hc ha
  by_cases e : u = t
  · subst e; exact ht hs hc ha
  · exact h u (fun h' => h'.elim hu e) hs hc ha

theorem vea_of {E : ObjRef → Prop} {σ : State Unit} (h : VE E σ)
    (ht : ∀ u, σ.schedulerAction = .switchThread u → ¬E u → schedulable u σ = true → u ≠ σ.curThread →
      ∃ d p, u ∈ σ.readyQueues d p) : VEA E σ := by
  intro t hE hs hc
  by_cases e : σ.schedulerAction = .switchThread t
  · exact ht t e hE hs hc
  · exact h t hE hs hc e

theorem vea_nsw {E : ObjRef → Prop} {σ : State Unit} (h : VE E σ) (hn : ∀ u, σ.schedulerAction ≠ .switchThread u) :
    VEA E σ :=
  vea_of h fun u e => absurd e (hn u)

theorem ve_setAction {E : ObjRef → Prop} {σ : State Unit} (h : VEA E σ) (a : SchedulerAction) :
    VE E { σ with schedulerAction := a } :=
  fun t ht hs hc _ => h t ht hs hc

/-! ## Heap writes -/

/-- A heap write of `o` over `old` that `VE` allows. -/
def OKV (old : Option KernelObject) (o : KernelObject) : Prop :=
  (∀ y, o = .tcb y → runnable y.tcbState = true → ∀ c, y.tcbSchedContext = some c →
    ∃ x, old = some (.tcb x) ∧ runnable x.tcbState = true ∧ x.tcbSchedContext = some c) ∧
  (∀ y n, o = .schedContext y n → scActive y = true → ∃ x m, old = some (.schedContext x m) ∧ scActive x = true)

/-- A write that keeps every other thread's schedulability (the SC part of `OKV`). -/
theorem sched_upd_ne {σ : State Unit} {p : ObjRef} {o : KernelObject}
    (h2 : ∀ y n, o = .schedContext y n → scActive y = true →
      ∃ x m, σ.kheap p = some (.schedContext x m) ∧ scActive x = true) {t : ObjRef} (hne : t ≠ p)
    (h : schedulable t { σ with kheap := Function.update σ.kheap p (some o) } = true) : schedulable t σ = true := by
  obtain ⟨x, scp, y, n, hx, hsc, hrn, hy, ha, hq⟩ := Sched.schedulable_inv h
  dsimp only at hx hy hq
  rw [Function.update_apply] at hx hy
  rw [if_neg hne] at hx
  by_cases es : scp = p
  · rw [if_pos es] at hy
    obtain ⟨x', m, h0, ha0⟩ := h2 y n (Option.some.inj hy) ha
    rw [← es] at h0
    exact Sched.schedulable_of hx hsc hrn h0 ha0 hq
  · rw [if_neg es] at hy; exact Sched.schedulable_of hx hsc hrn hy ha hq

theorem sched_upd {σ : State Unit} {p : ObjRef} {o : KernelObject} (hp : OKV (σ.kheap p) o) {t : ObjRef}
    (h : schedulable t { σ with kheap := Function.update σ.kheap p (some o) } = true) : schedulable t σ = true := by
  by_cases e : t = p
  · obtain ⟨x, scp, y, n, hx, hsc, hrn, hy, ha, hq⟩ := Sched.schedulable_inv h
    dsimp only at hx hy hq
    rw [Function.update_apply] at hx hy
    rw [if_pos e] at hx
    obtain ⟨x0, h0, hr0, hc0⟩ := hp.1 x (Option.some.inj hx) hrn scp hsc
    have es : scp ≠ p := by
      intro es; rw [if_pos es] at hy
      have := (Option.some.inj hx).symm.trans (Option.some.inj hy)
      cases this
    rw [if_neg es] at hy
    subst e
    exact Sched.schedulable_of h0 hc0 hr0 hy ha hq
  · exact sched_upd_ne hp.2 e h

/-- **`VE` across one `OKV` heap write.** -/
theorem ve_upd {E : ObjRef → Prop} {σ : State Unit} (h : VE E σ) (p : ObjRef) (o : KernelObject)
    (hp : OKV (σ.kheap p) o) : VE E { σ with kheap := Function.update σ.kheap p (some o) } :=
  ve_of h rfl rfl (fun _ _ _ _ hu => hu) (fun _ _ hs => sched_upd hp hs)

/-- Any write of a TCB at `t`: `t` joins the exception set. -/
theorem ve_upd_tcb {E : ObjRef → Prop} {σ : State Unit} (h : VE E σ) (t : ObjRef) (y : Tcb) :
    VE (Ins E t) { σ with kheap := Function.update σ.kheap t (some (.tcb y)) } :=
  ve_of (ve_ins t h) rfl rfl (fun _ _ _ _ hu => hu) (fun u hu hs =>
    sched_upd_ne (fun _ _ e => by cases e) (fun e => hu (Or.inr e)) hs)

theorem okv_ntb {old : Option KernelObject} {o : KernelObject} (h1 : ∀ y, o ≠ .tcb y)
    (h2 : ∀ y n, o ≠ .schedContext y n) : OKV old o :=
  ⟨fun y e => absurd e (h1 y), fun y n e => absurd e (h2 y n)⟩

theorem okv_nts {old : Option KernelObject} {o : KernelObject} (ho : NTS o) : OKV old o := by
  refine okv_ntb (fun y e => ?_) (fun y n e => ?_) <;> (subst e; exact False.elim ho)

theorem okv_simple {old : Option KernelObject} {o : KernelObject}
    (h : aType o ∈ ({.aEndpoint, .aNTFN, .aReply} : Set AType)) : OKV old o := by
  refine okv_ntb (fun y e => ?_) (fun y n e => ?_) <;> subst e
  · simp [aType] at h
  · simp only [aType] at h; split_ifs at h <;> simp at h

/-- A TCB rewrite keeping the state and keeping or clearing the binding. -/
theorem okv_tcb {x y : Tcb} (h1 : y.tcbState = x.tcbState)
    (h2 : y.tcbSchedContext = x.tcbSchedContext ∨ y.tcbSchedContext = none) : OKV (some (.tcb x)) (.tcb y) := by
  refine ⟨fun y' e hr c hc => ?_, fun _ _ e => by cases e⟩
  cases e
  rcases h2 with h2 | h2
  · exact ⟨x, rfl, by rw [← h1]; exact hr, by rw [← h2]; exact hc⟩
  · rw [h2] at hc; cases hc

/-- A TCB written in a state that is not runnable. -/
theorem okv_nr {old : Option KernelObject} {y : Tcb} (h : runnable y.tcbState = false) : OKV old (.tcb y) := by
  refine ⟨fun y' e hr => ?_, fun _ _ e => by cases e⟩
  cases e; rw [h] at hr; cases hr

theorem okv_sc {y : SchedContext} {n : Nat} (f : SchedContext → SchedContext)
    (hf : scActive (f y) = true → scActive y = true) : OKV (some (.schedContext y n)) (.schedContext (f y) n) := by
  refine ⟨(fun _ e => by cases e), fun y' m e ha => ?_⟩
  cases e
  exact ⟨y, n, rfl, hf ha⟩

/-! ## Leaves -/

section Leaves
variable {E : ObjRef → Prop}

theorem ve_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit) (hp : OKV (σ.kheap p) o) :
    IKp (VE E) σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ve_upd hσ p o hp

/-- Any TCB write at `t` (exception form). -/
theorem ht_setObject_tcb (t : ObjRef) (y : Tcb) (σ : State Unit) (hσ : VE E σ) :
    ∀ x, x ∈ (setObject (Z := Unit) t (.tcb y) σ).1 → VE (Ins E t) x.2 := by
  unfold setObject
  intro x ⟨w, hw, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hw
  obtain ⟨y1, y2⟩ := w
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ve_upd_tcb hσ t y

theorem ve_setObject (p : ObjRef) (o : KernelObject) (ho : NTS o) : VEK E (setObject (Z := Unit) p o) :=
  fun σ => ve_setObject_p p o σ (okv_nts ho)

theorem ve_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    VEK E (setSimpleKo (Z := Unit) f p e) := by
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
  have hsimp' : aType (f e) ∈ ({.aEndpoint, .aNTFN, .aReply} : Set AType) := by rw [← hty]; exact hsimp
  exact ve_upd hσ p _ (okv_simple hsimp')

theorem ve_setTcb_keep (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (h1 : y.tcbState = x.tcbState) (h2 : y.tcbSchedContext = x.tcbSchedContext ∨ y.tcbSchedContext = none) :
    IKp (VE E) σ (setObject (Z := Unit) p (.tcb y)) :=
  ve_setObject_p _ _ σ (by rw [hx]; exact okv_tcb h1 h2)

theorem ve_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbState = x.tcbState ∧
      ((f x).tcbSchedContext = x.tcbSchedContext ∨ (f x).tcbSchedContext = none)) :
    VEK E (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx => ve_setTcb_keep _ x σ (getTcb_kheap hx) _ (hf x).1 (hf x).2

theorem ve_threadSet_nr (ts : ThreadState) (t : ObjRef) (h : runnable ts = false) :
    VEK E (threadSet (Z := Unit) (fun tcb => { tcb with tcbState := ts }) t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx => ve_setObject_p _ _ σ (okv_nr h)

/-- `set_thread_state_act` only replaces `resumeCurThread` by `chooseNewThread`: no exemption is lost. -/
theorem ve_setThreadStateAct (t : ObjRef) : VEK E (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  dsimp only at hx
  unfold NonDet.when at hx
  split at hx
  · rename_i hc
    unfold setSchedulerAction at hx
    rw [Set.mem_singleton_iff.1 hx]
    exact ve_setAction (vea_nsw hσ (fun u e => by rw [hc.2.1] at e; cases e)) _
  · rw [Set.mem_singleton_iff.1 hx]; exact hσ

theorem ve_setThreadState (t : ObjRef) (ts : ThreadState) (h : runnable ts = false) :
    VEK E (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ik_bind (ve_threadSet_nr ts t h) fun _ => ve_setThreadStateAct t

theorem ve_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : VEK E (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => ve_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl (Or.inl rfl)

theorem ve_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : VEK E (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (ve_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl (Or.inl rfl)) fun _ => ik_pure _

theorem ve_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : VEK E (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (ve_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl (Or.inl rfl)) fun _ => ?_
  repeat' (first | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_step0 | ik_unfold)

theorem ve_setCap (c : Cap) (sl : CslotPtr) : VEK E (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (ve_setObject_p _ _ σ (okv_ntb (fun _ e => by cases e) (fun _ _ e => by cases e)))
    · exact ikp_fail_bind
  · rename_i tcb
    split
    · exact ikp_pure_bind (ve_setTcb_keep _ tcb σ hk _ rfl (Or.inl rfl))
    split
    · exact ikp_pure_bind (ve_setTcb_keep _ tcb σ hk _ rfl (Or.inl rfl))
    split
    · exact ikp_pure_bind (ve_setTcb_keep _ tcb σ hk _ rfl (Or.inl rfl))
    split
    · exact ikp_pure_bind (ve_setTcb_keep _ tcb σ hk _ rfl (Or.inl rfl))
    split
    · exact ikp_pure_bind (ve_setTcb_keep _ tcb σ hk _ rfl (Or.inl rfl))
    split
    · exact ikp_pure_bind (ve_setTcb_keep _ tcb σ hk _ rfl (Or.inl rfl))
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem ve_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbState = x.tcbState ∧
      ((fn v x).tcbSchedContext = x.tcbSchedContext ∨ (fn v x).tcbSchedContext = none)) :
    VEK E (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact ve_threadSet _ _ (h _)

theorem ve_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, scActive (f y) = true → scActive y = true) : VEK E (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  dsimp only at hx
  split at hx
  · rename_i sc n
    refine ve_setObject_p _ _ _ ?_ hσ x hx
    rw [hk]; exact okv_sc f (hf sc)
  · exact hx.elim

end Leaves

/-! ## Hoare triples for the exception-changing steps -/

/-- Every outcome of `m` from a `P` state is a `Q` state (`HT P P m` is `IK P m`). -/
def HT (P Q : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ x, x ∈ (m σ).1 → Q x.2

theorem ht_ik {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : IK P m) : HT P P m := h

theorem ht_bind {P Q R : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : HT P R m) (hg : ∀ a, HT R Q (g a)) : HT P Q (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  exact hg y.1 y.2 (hm σ hσ y hy) x hx

theorem ht_conseq {P P' Q Q' : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α}
    (hP : ∀ σ, P' σ → P σ) (hQ : ∀ σ, Q σ → Q' σ) (h : HT P Q m) : HT P' Q' m :=
  fun σ hσ x hx => hQ _ (h σ (hP σ hσ) x hx)

/-- The outcomes of `tcb_sched_action f t`: one ready queue rewritten by `f t`. -/
theorem tsa_out {f : ObjRef → List ObjRef → List ObjRef} {t : ObjRef} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (tcbSchedAction (Z := Unit) f t σ).1) :
    ∃ d p, x.2 = { σ with readyQueues := fun d' p' => if d' = d ∧ p' = p then f t (σ.readyQueues d p) else σ.readyQueues d' p' } := by
  unfold tcbSchedAction getTcbQueue setTcbQueue at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨_, -, rfl⟩ := SInvQ.q1_mem_threadGet hy1
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain ⟨_, -, rfl⟩ := SInvQ.q1_mem_threadGet hy2
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨z, hz, hy3⟩ := hy3
  rw [Set.mem_singleton_iff.1 hz] at hy3
  rw [Set.mem_singleton_iff.1 hy3] at hx
  obtain ⟨y4, hy4, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy4] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨_, _, rfl⟩


theorem ht_apply {P Q : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} {σ : State Unit}
    {x : α × State Unit} (h : HT P Q m) (hσ : P σ) (hx : x ∈ (m σ).1) : Q x.2 := h σ hσ x hx

/-- Schedulability across a release-queue change that keeps `u` released. -/
theorem sched_relq {σ σ' : State Unit} {u : ObjRef} (hk : σ'.kheap = σ.kheap)
    (hr : u ∈ σ.releaseQueue → u ∈ σ'.releaseQueue) (h : schedulable u σ' = true) : schedulable u σ = true := by
  obtain ⟨x, scp, y, n, hx, hsc, hrn, hy, ha, hq⟩ := Sched.schedulable_inv h
  rw [hk] at hx hy
  exact Sched.schedulable_of hx hsc hrn hy ha (fun m => hq (hr m))

section Sched
variable {E : ObjRef → Prop}

/-- A queue action keeping every queued thread (enqueue / append). -/
theorem ve_tcbSchedAction (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef)
    (hf : ∀ q u, u ∈ q → u ∈ f t q) : VEK E (tcbSchedAction (Z := Unit) f t) := by
  intro σ hσ x hx
  obtain ⟨d, p, e⟩ := tsa_out hx
  rw [e]
  refine ve_of hσ rfl rfl (fun d' p' u _ hu => ?_) (fun _ _ hs => hs)
  dsimp only
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; exact hf _ _ hu
  · exact hu

theorem enq_mem (t : ObjRef) (q : List ObjRef) (u : ObjRef) (h : u ∈ q) : u ∈ tcbSchedEnqueue t q := by
  by_cases e : t ∈ q <;> simp [tcbSchedEnqueue, e, h]

theorem app_mem (t : ObjRef) (q : List ObjRef) (u : ObjRef) (h : u ∈ q) : u ∈ tcbSchedAppend t q := by
  by_cases e : t ∈ q <;> simp [tcbSchedAppend, e, h]

theorem enq_self (t : ObjRef) (q : List ObjRef) : t ∈ tcbSchedEnqueue t q := by
  by_cases e : t ∈ q <;> simp [tcbSchedEnqueue, e]

theorem ve_tcbSchedEnqueue (t : ObjRef) : VEK E (tcbSchedAction (Z := Unit) tcbSchedEnqueue t) :=
  ve_tcbSchedAction _ t (enq_mem t)

theorem ve_tcbSchedAppend (t : ObjRef) : VEK E (tcbSchedAction (Z := Unit) tcbSchedAppend t) :=
  ve_tcbSchedAction _ t (app_mem t)

/-- Enqueueing `t` puts `t` in a ready queue and keeps any `Q` that only needs the queues to grow. -/
theorem ht_enqueue (t : ObjRef) (Q : State Unit → Prop)
    (hQ' : ∀ σ (r : Domain → Priority → List ObjRef), Q σ → (∀ d p u, u ∈ σ.readyQueues d p → u ∈ r d p) →
      Q { σ with readyQueues := r }) :
    HT Q (fun s => Q s ∧ ∃ d p, t ∈ s.readyQueues d p) (tcbSchedAction (Z := Unit) tcbSchedEnqueue t) := by
  intro σ hσ x hx
  obtain ⟨d, p, e⟩ := tsa_out hx
  rw [e]
  refine ⟨hQ' σ _ hσ (fun d' p' u hu => ?_), d, p, ?_⟩
  · try dsimp only
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact enq_mem _ _ _ hu
    · exact hu
  · try dsimp only
    rw [if_pos ⟨rfl, rfl⟩]; exact enq_self _ _

/-- Enqueueing `t` takes `t` out of the exception set. -/
theorem ht_enqueue_x (t : ObjRef) : HT (VE (Ins E t)) (VE E) (tcbSchedAction (Z := Unit) tcbSchedEnqueue t) := by
  intro σ hσ x hx
  obtain ⟨h1, d, p, h2⟩ := ht_enqueue t (VE (Ins E t))
    (fun s r hs hr => ve_of hs rfl rfl (fun d p u _ h => hr d p u h) (fun _ _ h => h)) σ hσ x hx
  exact ve_drop h1 (fun _ _ _ => ⟨d, p, h2⟩)

/-- A read-only computation keeps any predicate (`SInvQ.ik_of_ro`). -/
macro "ro_auto" : tactic => `(tactic| (refine SInvQ.ik_of_ro fun _ => ?_; repeat' (first | ik_step0 | ik_unfold)))

theorem ro_getScRefillSufficient (P : State Unit → Prop) (p : ObjRef) (u : Nat) :
    IK P (getScRefillSufficient (Z := Unit) p u) := by ro_auto

theorem ro_getScRefillReady (P : State Unit → Prop) (p : ObjRef) : IK P (getScRefillReady (Z := Unit) p) := by ro_auto

/-- **`reschedule_required` keeps `VE E`** (the old switch target is enqueued when schedulable). -/
theorem ve_rescheduleRequired : VEK E (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  dsimp only at hx
  rcases heq : σ.schedulerAction with _ | t | _
  rotate_left
  · rw [heq] at hx
    dsimp only at hx
    obtain ⟨y2, hy2, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hy2] at hx
    dsimp only at hx
    obtain ⟨y3, hy3, hx⟩ := hx
    dsimp only [setSchedulerAction] at hx
    rw [Set.mem_singleton_iff.1 hx]
    have hpost : VE E y3.2 ∧ y3.2.schedulerAction = .switchThread t ∧
        (schedulable t y3.2 = true → ∃ d p, t ∈ y3.2.readyQueues d p) := by
      unfold NonDet.when at hy3
      split at hy3
      · have hR : (VE E y3.2 ∧ y3.2.schedulerAction = .switchThread t) ∧ ∃ d p, t ∈ y3.2.readyQueues d p := by
          refine ht_apply (P := fun s => VE E s ∧ s.schedulerAction = .switchThread t)
            (Q := fun s => (VE E s ∧ s.schedulerAction = .switchThread t) ∧ ∃ d p, t ∈ s.readyQueues d p)
            ?_ ⟨hσ, heq⟩ hy3
          refine ht_bind (ht_ik (SInvQ.ik_threadGet_any _ _ _)) fun scOpt => ?_
          refine ht_bind (ht_ik (ik_assertOpt _)) fun scp => ?_
          refine ht_bind (ht_ik (ro_getScRefillSufficient _ _ _)) fun _ => ?_
          refine ht_bind (ht_ik (ro_getScRefillReady _ _)) fun _ => ?_
          refine ht_bind (ht_ik (ik_assert _)) fun _ => ?_
          exact ht_enqueue t _ (fun s r hs hr => ⟨ve_of hs.1 rfl rfl (fun d p u _ h => hr d p u h) (fun _ _ h => h), hs.2⟩)
        exact ⟨hR.1.1, hR.1.2, fun _ => hR.2⟩
      · rename_i hs
        rw [Set.mem_singleton_iff.1 hy3]
        exact ⟨hσ, heq, fun h => absurd h hs⟩
    obtain ⟨h1, h2, h3⟩ := hpost
    refine ve_setAction (vea_of h1 fun u e _ hs _ => ?_) _
    rw [h2] at e
    injection e with e
    subst e
    exact h3 hs
  all_goals
    rw [heq] at hx
    dsimp only at hx
    first
      | (obtain ⟨y2, hy2, hx⟩ := hx; rw [Set.mem_singleton_iff.1 hy2] at hx; dsimp only at hx)
      | skip
    dsimp only [setSchedulerAction] at hx
    rw [Set.mem_singleton_iff.1 hx]
    exact ve_setAction (vea_nsw hσ fun u e => by rw [heq] at e; cases e) _

/-- **`possible_switch_to t` takes `t` out of the exception set** (enqueued, the switch target, or not
schedulable). -/
theorem ht_possibleSwitchTo (t : ObjRef) : HT (VE (Ins E t)) (VE E) (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨x0, hk0, rfl⟩ := SInvQ.q1_mem_threadGet hy
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx
  dsimp only at hx
  unfold NonDet.when at hx
  split at hx
  · obtain ⟨y3, hy3, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hy3] at hx
    obtain ⟨y4, hy4, hx⟩ := hx
    obtain ⟨_, -, rfl⟩ := SInvQ.q1_mem_threadGet hy4
    obtain ⟨y5, hy5, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hy5] at hx
    dsimp only at hx
    split_ifs at hx with h1 h2
    · exact ht_enqueue_x t σ hσ x hx
    · obtain ⟨y6, hy6, hx⟩ := hx
      exact ht_enqueue_x t _ (ve_rescheduleRequired (E := Ins E t) σ hσ y6 hy6) x hx
    · dsimp only [setSchedulerAction] at hx
      rw [Set.mem_singleton_iff.1 hx]
      have ha : σ.schedulerAction = .resumeCurThread := not_not.1 h2
      refine ve_drop (ve_setAction (vea_nsw hσ fun u e => by rw [ha] at e; cases e) _) fun _ _ h => absurd rfl h
  · rename_i hc
    rw [Set.mem_singleton_iff.1 hx]
    refine ve_drop hσ fun hs => absurd ?_ hc
    obtain ⟨x1, scp, y1, n, hx1, hsc, -, -, -, hq⟩ := Sched.schedulable_inv hs
    rw [hk0] at hx1; cases hx1
    exact ⟨(by rw [hsc]; exact fun e => by cases e), (by simp [inReleaseQueue, hq])⟩

theorem ve_possibleSwitchTo (t : ObjRef) : VEK E (possibleSwitchTo (Z := Unit) t) :=
  fun σ hσ => ht_possibleSwitchTo t σ (ve_ins t hσ)

/-- Any `thread_set` of `t`: `t` joins the exception set. -/
theorem ht_threadSet_x (f : Tcb → Tcb) (t : ObjRef) : HT (VE E) (VE (Ins E t)) (threadSet (Z := Unit) f t) := by
  unfold threadSet
  intro σ hσ x ⟨y, hy, hx⟩
  unfold NonDet.getsThe at hy
  cases e : getTcb t σ with
  | none => rw [e] at hy; exact hy.elim
  | some a =>
    rw [e] at hy
    rw [Set.mem_singleton_iff.1 hy] at hx
    exact ht_setObject_tcb t _ σ hσ x hx

theorem ht_setThreadState_x (t : ObjRef) (ts : ThreadState) :
    HT (VE E) (VE (Ins E t)) (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ht_bind (ht_threadSet_x _ t) fun _ => ht_ik (ve_setThreadStateAct t)

/-- Dequeueing `t`: `t` joins the exception set. -/
theorem ht_dequeue (t : ObjRef) : HT (VE E) (VE (Ins E t)) (tcbSchedAction (Z := Unit) tcbSchedDequeue t) := by
  intro σ hσ x hx
  obtain ⟨d, p, e⟩ := tsa_out hx
  rw [e]
  refine ve_of (ve_ins t hσ) rfl rfl (fun d' p' u hu hm => ?_) (fun _ _ hs => hs)
  dsimp only
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    unfold tcbSchedDequeue
    exact List.mem_filter.2 ⟨hm, decide_eq_true (fun e => hu (Or.inr e.symm))⟩
  · exact hm

/-- Removing `t` from the release queue: `t` joins the exception set. -/
theorem ht_tcbReleaseRemove (t : ObjRef) : HT (VE E) (VE (Ins E t)) (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  dsimp only at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain ⟨y3, hy3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy3] at hx
  dsimp only at hx
  have e2 : y2.2.kheap = σ.kheap ∧ y2.2.curThread = σ.curThread ∧ y2.2.schedulerAction = σ.schedulerAction ∧
      y2.2.readyQueues = σ.readyQueues := by
    unfold NonDet.when at hy2
    split at hy2 <;> (rw [Set.mem_singleton_iff.1 hy2]; exact ⟨rfl, rfl, rfl, rfl⟩)
  rw [Set.mem_singleton_iff.1 hx]
  refine ve_of (ve_ins t hσ) e2.2.1 e2.2.2.1 (fun d p u _ hu => by
    show u ∈ y2.2.readyQueues d p; rw [e2.2.2.2]; exact hu) (fun u hu hs => sched_relq (by exact e2.1) (fun m => ?_) hs)
  show u ∈ tcbSchedDequeue t σ.releaseQueue
  unfold tcbSchedDequeue
  exact List.mem_filter.2 ⟨m, decide_eq_true (fun e => hu (Or.inr e.symm))⟩

theorem ht_setSchedulerAction (a : SchedulerAction) : HT (VEA E) (VE E) (setSchedulerAction (Z := Unit) a) := by
  intro σ h x hx
  unfold setSchedulerAction at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ve_setAction h a

end Sched

/-! ## `ve_auto` -/

macro "ve_side" : tactic => `(tactic| first
  | trivial
  | rfl
  | (intro _; rfl)
  | (intro _ _; rfl)
  | (intro _; exact ⟨rfl, Or.inl rfl⟩)
  | (intro _; exact ⟨rfl, Or.inr rfl⟩)
  | (intro _ _; exact ⟨rfl, Or.inl rfl⟩)
  | (intro _ _; exact ⟨rfl, Or.inr rfl⟩)
  | (intro _ h; exact h)
  | (intro _ h; simp [scActive, activeSc, scRefillMaxUpdate] at h; done)
  | (intro _ h; cases h; done))

syntax "ve_leaf" : tactic
macro_rules | `(tactic| ve_leaf) => `(tactic| fail "no ve_leaf")

macro "ve_auto" : tactic => `(tactic| repeat' (first | ve_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| ve_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| ve_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| ve_leaf) => `(tactic| ((with_reducible refine ve_setObject _ _ ?_); ve_side))
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_setSimpleKo _ _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| ((with_reducible refine ve_threadSet _ _ ?_); ve_side))
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_archThreadSet _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_asUser _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_setMrs _ _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_setCap _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| ((with_reducible refine ve_setThreadState _ _ ?_); ve_side))
macro_rules | `(tactic| ve_leaf) => `(tactic| ((with_reducible refine ve_optionUpdateThread _ _ _ ?_); ve_side))
macro_rules | `(tactic| ve_leaf) => `(tactic| ((with_reducible refine ve_updateSchedContext _ _ ?_); ve_side))
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_setThreadStateAct _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_tcbSchedEnqueue _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_tcbSchedAppend _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_rescheduleRequired)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_possibleSwitchTo _)

end

end Fl4Proofs.P3.SInvR.B8q
