/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd2): **the frame kit of
`Rdy`** (spec side only, outside the `JAtZ` cone; KENTRY-PLAN rd1 handoff 2).

`Rdy` reads the heap only through (a) the existence and SC binding of every
TCB, (b) the state and fault of a `BlkR` TCB, (c) the refill list and refill
max of every SC; plus the ready queues, the switch target and the time.

* `OK1 old o`: writing `o` over `old` keeps (a)-(c): a TCB stays a TCB with
  the same binding, a new `BlkR` bound TCB was a `BlkR` TCB with that binding,
  the SC view (`SV`: refills, refill max) is unchanged. `rdy_of_view` /
  `rdy_upd`: `Rdy` across such a write, or across new queue members / a new
  switch target that are `RdyT`.
* Leaves: `rd_setObject_p` (state-pinned), `rd_setObject` (`NTS o`: no TCB,
  SC or CNode, so by `aType` the old object is neither TCB nor SC),
  `rd_setSimpleKo`, `rd_threadSet` (state / fault / binding kept),
  `rd_setThreadState` (to a state outside `BlkR`, `NB`), `rd_archThreadSet`,
  `rd_asUser`, `rd_setMrs`, `rd_setCap`, `rd_optionUpdateThread`,
  `rd_updateSchedContext` (refills / max kept), `rd_tsa_p` (queue action adding
  only an `RdyT` thread), `rd_dequeue`, `rd_setSchedulerAction_ns` (no switch
  target), `rd_setThreadStateAct`, `rd_tcbReleaseRemove`.
* By hand: **`rd_rescheduleRequired`** (it enqueues the switch target only
  after asserting it schedulable, sufficient and ready: `RdyT` from its own
  asserts, R2 not needed), **`rd_possibleSwitchTo_p`** (the target `RdyT` at
  that state: l4v's `released_ipc_queues` / caller fact).
* `rd_auto` drives the generated family SpecInvRdF1..F5.
-/
import Fl4Proofs.P3.SpecInvRdB
import Fl4Proofs.P3.SpecInvCqS
open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The view -/

abbrev RdK {α : Type} (m : NonDet (State Unit) α) : Prop := IK Rdy m
abbrev RdKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE Rdy m

/-- The SC view: refills, refill max and (rd6, for `RV`'s round-robin clause) period. -/
def SV (o : Option KernelObject) : Option (List Refill × Nat × Ticks) :=
  match o with
  | some (.schedContext y _) => some (y.scRefills, y.scRefillMax, y.scPeriod)
  | _ => none

theorem sv_some {o : Option KernelObject} {a : List Refill × Nat × Ticks} (h : SV o = some a) :
    ∃ y n, o = some (.schedContext y n) ∧ y.scRefills = a.1 ∧ y.scRefillMax = a.2.1 ∧ y.scPeriod = a.2.2 := by
  unfold SV at h
  split at h
  · cases h; exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  · cases h

/-- Writing `o` over `old` keeps what `Rdy` reads. -/
def OK1 (old : Option KernelObject) (o : KernelObject) : Prop :=
  (∀ x, old = some (.tcb x) → ∃ x', o = .tcb x' ∧ x'.tcbSchedContext = x.tcbSchedContext) ∧
  (∀ x', o = .tcb x' → BlkR x'.tcbState x'.tcbFault → x'.tcbSchedContext ≠ none →
    ∃ x, old = some (.tcb x) ∧ x.tcbSchedContext = x'.tcbSchedContext ∧ BlkR x.tcbState x.tcbFault) ∧
  SV (some o) = SV old

theorem rvs_congr {y z : SchedContext} (e1 : z.scRefills = y.scRefills) (e2 : z.scRefillMax = y.scRefillMax)
    (e3 : z.scPeriod = y.scPeriod) (h : RVs y) : RVs z := by
  unfold RVs refillHd at *; rw [e1, e2, e3]; exact h

/-- **`Rdy` across a view-keeping change** (new queue members / switch target `RdyT`). -/
theorem rdy_of_view {σ σ' : State Unit} (h : Rdy σ)
    (hT : ∀ t x, σ.kheap t = some (.tcb x) → ∃ x', σ'.kheap t = some (.tcb x') ∧
      x'.tcbSchedContext = x.tcbSchedContext)
    (hB : ∀ t x', σ'.kheap t = some (.tcb x') → BlkR x'.tcbState x'.tcbFault → x'.tcbSchedContext ≠ none →
      ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = x'.tcbSchedContext ∧ BlkR x.tcbState x.tcbFault)
    (hS : ∀ p, SV (σ'.kheap p) = SV (σ.kheap p)) (ht : σ'.curTime = σ.curTime) (hid : σ'.idleSc = σ.idleSc)
    (hq : ∀ d p t, t ∈ σ'.readyQueues d p → t ∈ σ.readyQueues d p ∨ RdyT σ t)
    (ha : ∀ t, σ'.schedulerAction = .switchThread t → σ.schedulerAction = .switchThread t ∨ RdyT σ t)
    (hrq : ∀ t, t ∈ σ'.releaseQueue → t ∈ σ.releaseQueue ∨ ActB σ t) :
    Rdy σ' := by
  have F : ∀ {t}, RdyT σ t → RdyT σ' t := by
    intro t ⟨x, c, y, n, hx, hc, hy, h1, h2⟩
    obtain ⟨x', hx', ex⟩ := hT t x hx
    have e2 : SV (σ'.kheap c) = some (y.scRefills, y.scRefillMax, y.scPeriod) := by rw [hS c, hy]; rfl
    obtain ⟨y', n', hy', ey1, ey2, -⟩ := sv_some e2
    refine ⟨x', c, y', n', hx', by rw [ex]; exact hc, hy', ?_, ?_⟩
    · show activeSc y'.scRefillMax = true
      rw [ey2]; exact h1
    · rw [ht]; unfold refillHd; rw [ey1]; exact h2
  have G : ∀ {t}, ActB σ t → ActB σ' t := by
    intro t ⟨x, c, y, n, hx, hc, hy, h1⟩
    obtain ⟨x', hx', ex⟩ := hT t x hx
    have e2 : SV (σ'.kheap c) = some (y.scRefills, y.scRefillMax, y.scPeriod) := by rw [hS c, hy]; rfl
    obtain ⟨y', n', hy', -, ey2, -⟩ := sv_some e2
    refine ⟨x', c, y', n', hx', by rw [ex]; exact hc, hy', ?_⟩
    show activeSc y'.scRefillMax = true
    rw [ey2]; exact h1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun d p t hm => ?_, fun t e => ?_, fun t x' c hx' hb hc => ?_, fun q z n hz hz' => ?_,
    fun t hm => (hrq t hm).elim (fun hm => G (h5 t hm)) G, fun z m hz => ?_⟩
  rotate_right
  · rw [hid] at hz
    have e2 : SV (σ.kheap σ.idleSc) = some (z.scRefills, z.scRefillMax, z.scPeriod) := by rw [← hS, hz]; rfl
    obtain ⟨y, k, hy, ey1, -, -⟩ := sv_some e2
    have ey : y.scRefills = z.scRefills := ey1
    have := h6 y k hy
    rw [ht]; unfold refillHd; rw [← ey]; exact this
  · rcases hq d p t hm with hm | hm
    · exact F (h1 d p t hm)
    · exact F hm
  · rcases ha t e with e | e
    · exact F (h2 t e)
    · exact F e
  · obtain ⟨x, hx, ex, hbx⟩ := hB t x' hx' hb (by rw [hc]; exact Option.some_ne_none c)
    exact F (h3 t x c hx hbx (by rw [ex]; exact hc))
  · have e2 : SV (σ.kheap q) = some (z.scRefills, z.scRefillMax, z.scPeriod) := by rw [← hS q, hz]; rfl
    obtain ⟨y, m, hy, ey1, ey2, ey3⟩ := sv_some e2
    have ha' : scActive y = true := by
      show activeSc y.scRefillMax = true
      rw [ey2]; exact hz'
    exact rvs_congr ey1.symm ey2.symm ey3.symm (h4 q y m hy ha')

/-- **`Rdy` across one `OK1` heap write.** -/
theorem rdy_upd {σ : State Unit} (h : Rdy σ) (p : ObjRef) (o : KernelObject) (hp : OK1 (σ.kheap p) o) :
    Rdy { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨p1, p2, p3⟩ := hp
  refine rdy_of_view h (fun t x hx => ?_) (fun t x' hx' hb hc => ?_) (fun q => ?_) rfl rfl
    (fun d q t hm => Or.inl hm) (fun t e => Or.inl e) (fun t hm => Or.inl hm)
  · by_cases e : t = p
    · subst e
      obtain ⟨x', rfl, ex⟩ := p1 x hx
      exact ⟨x', by simp, ex⟩
    · exact ⟨x, by show Function.update σ.kheap p (some o) t = _; rw [Function.update_of_ne e]; exact hx, rfl⟩
  · by_cases e : t = p
    · subst e
      have hx'' : o = .tcb x' := by simpa using hx'
      exact p2 x' hx'' hb hc
    · refine ⟨x', ?_, rfl, hb⟩
      have : Function.update σ.kheap p (some o) t = some (.tcb x') := hx'
      rwa [Function.update_of_ne e] at this
  · by_cases e : q = p
    · subst e; show SV (Function.update σ.kheap q (some o) q) = _; rw [Function.update_self]; exact p3
    · show SV (Function.update σ.kheap p (some o) q) = _; rw [Function.update_of_ne e]

/-! ## Heap writes -/

theorem rd_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit) (hp : OK1 (σ.kheap p) o) :
    IKp Rdy σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact rdy_upd hσ p o hp

/-- Neither a TCB, nor an SC, nor a CNode (so `aType` pins the old object). -/
def NTS : KernelObject → Prop
  | .tcb _ => False
  | .schedContext _ _ => False
  | .cnode _ _ => False
  | _ => True

theorem nts_old {o o' : KernelObject} (h : aType o' = aType o) (ho : NTS o) :
    (∀ x, o' ≠ .tcb x) ∧ SV (some o') = none := by
  cases o with
  | tcb x => exact False.elim ho
  | schedContext y n => exact False.elim ho
  | cnode sz cs => exact False.elim ho
  | _ =>
    cases o' with
    | tcb x => exfalso; simp [aType] at h
    | schedContext y n =>
      exfalso; simp only [aType] at h
      split_ifs at h <;> cases h
    | _ => exact ⟨(fun _ e => by cases e), rfl⟩

theorem nts_new {o : KernelObject} (ho : NTS o) : (∀ x, o ≠ .tcb x) ∧ SV (some o) = none := by
  cases o with
  | tcb x => exact False.elim ho
  | schedContext y n => exact False.elim ho
  | cnode sz cs => exact False.elim ho
  | _ => exact ⟨(fun _ e => by cases e), rfl⟩

theorem ok1_of_none {old : Option KernelObject} {o : KernelObject}
    (h1 : ∀ x, old ≠ some (.tcb x)) (h2 : SV old = none) (h3 : ∀ x, o ≠ .tcb x) (h4 : SV (some o) = none) :
    OK1 old o :=
  ⟨fun x hx => absurd hx (h1 x), fun x' hx' => absurd hx' (h3 x'), by rw [h4, h2]⟩

theorem rd_setObject (p : ObjRef) (o : KernelObject) (ho : NTS o) : IK Rdy (setObject (Z := Unit) p o) := by
  unfold setObject
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨a1, a2⟩ := nts_old hty ho
  obtain ⟨b1, b2⟩ := nts_new ho
  refine rdy_upd hσ p o (ok1_of_none (fun x e => ?_) (by rw [hk]; exact a2) b1 b2)
  rw [hk] at e; cases e; exact a1 x rfl

theorem simple_old {o : KernelObject} (h : aType o ∈ ({.aEndpoint, .aNTFN, .aReply} : Set AType)) :
    (∀ x, o ≠ .tcb x) ∧ SV (some o) = none := by
  cases o with
  | tcb x => exfalso; simp [aType] at h
  | schedContext y n =>
    exfalso; simp only [aType] at h
    split_ifs at h <;> simp at h
  | cnode sz cs =>
    exact ⟨(fun _ e => by cases e), rfl⟩
  | _ => exact ⟨(fun _ e => by cases e), rfl⟩

theorem rd_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    IK Rdy (setSimpleKo (Z := Unit) f p e) := by
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
  obtain ⟨a1, a2⟩ := simple_old hsimp
  have hsimp' : aType (f e) ∈ ({.aEndpoint, .aNTFN, .aReply} : Set AType) := by rw [← hty]; exact hsimp
  obtain ⟨b1, b2⟩ := simple_old hsimp'
  refine rdy_upd hσ p _ (ok1_of_none (fun x e => ?_) (by rw [hk]; exact a2) b1 b2)
  rw [hk] at e; cases e; exact a1 x rfl

/-- A TCB rewrite keeping state, fault and binding. -/
theorem ok1_tcb {x y : Tcb} (h1 : y.tcbState = x.tcbState) (h2 : y.tcbFault = x.tcbFault)
    (h3 : y.tcbSchedContext = x.tcbSchedContext) : OK1 (some (.tcb x)) (.tcb y) := by
  refine ⟨fun x0 e => ?_, fun x' e hb hc => ?_, rfl⟩
  · cases e; exact ⟨y, rfl, h3⟩
  · cases e; exact ⟨x, rfl, h3.symm, by rw [← h1, ← h2]; exact hb⟩

theorem rd_setTcb_keep (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (h1 : y.tcbState = x.tcbState) (h2 : y.tcbFault = x.tcbFault) (h3 : y.tcbSchedContext = x.tcbSchedContext) :
    IKp Rdy σ (setObject (Z := Unit) p (.tcb y)) :=
  rd_setObject_p _ _ σ (by rw [hx]; exact ok1_tcb h1 h2 h3)

theorem rd_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbState = x.tcbState ∧ (f x).tcbFault = x.tcbFault ∧
      (f x).tcbSchedContext = x.tcbSchedContext) :
    IK Rdy (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx =>
    rd_setTcb_keep _ x σ (getTcb_kheap hx) _ (hf x).1 (hf x).2.1 (hf x).2.2

/-- No `BlkR` state. -/
def NB : ThreadState → Prop
  | .blockedOnNotification _ => False
  | .blockedOnSend _ _ => False
  | .blockedOnReceive _ _ _ => False
  | _ => True

theorem nb_blk {ts : ThreadState} (h : NB ts) (f : Option Fault) : ¬ BlkR ts f := by
  rintro (⟨_, rfl⟩ | ⟨_, _, rfl, _⟩ | ⟨_, _, _, rfl⟩) <;> exact h

theorem rd_threadSet_nb (ts : ThreadState) (t : ObjRef) (h : NB ts) :
    IK Rdy (threadSet (Z := Unit) (fun tcb => { tcb with tcbState := ts }) t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => rd_setObject_p _ _ σ ?_
  rw [getTcb_kheap hx]
  refine ⟨fun x0 e => ?_, fun x' e hb _ => absurd hb ?_, rfl⟩
  · cases e; exact ⟨_, rfl, rfl⟩
  · cases e; exact nb_blk h _

/-! ## Scheduler action, queues -/

theorem rd_setSchedulerAction_ns (a : SchedulerAction) (h : ∀ t, a ≠ .switchThread t) :
    IK Rdy (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction
  intro σ hσ x hx
  rw [Set.mem_singleton_iff.1 hx]
  exact rdy_of_view hσ (fun t x hx => ⟨x, hx, rfl⟩) (fun t x hx hb _ => ⟨x, hx, rfl, hb⟩) (fun _ => rfl) rfl rfl
    (fun d p t hm => Or.inl hm) (fun t e => absurd e (h t)) (fun t hm => Or.inl hm)

theorem rd_setThreadStateAct (t : ObjRef) : IK Rdy (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct
  repeat' (first | (with_reducible exact rd_setSchedulerAction_ns _ fun _ h => by cases h) | ik_step0 | ik_unfold)

theorem rd_setThreadState (t : ObjRef) (ts : ThreadState) (h : NB ts) :
    IK Rdy (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ik_bind (rd_threadSet_nb ts t h) fun _ => rd_setThreadStateAct t

/-- **`tcb_sched_action`** adding only an `RdyT` thread. -/
theorem rd_tsa_p (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) (σ : State Unit)
    (hact : ∀ q u, u ∈ act t q → u ∈ q ∨ (u = t ∧ RdyT σ t)) :
    IKp Rdy σ (tcbSchedAction (Z := Unit) act t) := by
  intro hσ y hy
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]
  refine rdy_of_view hσ (fun t x hx => ⟨x, hx, rfl⟩) (fun t x hx hb _ => ⟨x, hx, rfl, hb⟩) (fun _ => rfl) rfl rfl
    (fun d p u hm => ?_) (fun t e => Or.inl e) (fun t hm => Or.inl hm)
  dsimp only at hm
  split at hm
  · rename_i hdp
    obtain ⟨rfl, rfl⟩ := hdp
    rcases hact _ _ hm with hm | ⟨rfl, hr⟩
    · exact Or.inl hm
    · exact Or.inr hr
  · exact Or.inl hm

theorem rd_dequeue (t : ObjRef) : IK Rdy (tcbSchedAction (Z := Unit) tcbSchedDequeue t) :=
  fun σ => rd_tsa_p _ t σ fun _ _ hu => Or.inl (List.mem_filter.1 hu).1

theorem rd_tcbReleaseRemove (t : ObjRef) : IK Rdy (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue
  refine ik_gets_bind fun σ => ?_
  intro hσ y ⟨z, hz, hy⟩
  have hz' : Rdy z.2 := by
    unfold NonDet.when at hz
    split at hz
    · rw [Set.mem_singleton_iff.1 hz]; exact rdy_congr hσ rfl rfl rfl rfl rfl fun _ h => h
    · rw [Set.mem_singleton_iff.1 hz]; exact hσ
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  rw [Set.mem_singleton_iff.1 hy]
  have hzq : z.2.releaseQueue = σ.releaseQueue := by
    unfold NonDet.when at hz
    split at hz
    · rw [Set.mem_singleton_iff.1 hz]
    · rw [Set.mem_singleton_iff.1 hz]
  refine rdy_congr hz' rfl rfl rfl rfl rfl fun u hu => ?_
  have hu' : u ∈ tcbSchedDequeue t σ.releaseQueue := hu
  rw [hzq]; exact (List.mem_filter.1 hu').1

/-! ## Other TCB writes -/

theorem rd_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : IK Rdy (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => rd_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl rfl rfl

theorem rd_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : IK Rdy (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (rd_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl rfl rfl) fun _ => ik_pure _

theorem rd_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : IK Rdy (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (rd_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl rfl rfl) fun _ => ?_
  repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

theorem rd_setCap (c : Cap) (sl : CslotPtr) : IK Rdy (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (rd_setObject_p _ _ σ (by rw [hk]; exact ⟨(fun _ e => by cases e),
        (fun _ e => by cases e), rfl⟩))
    · exact ikp_fail_bind
  · rename_i tcb
    split
    · exact ikp_pure_bind (rd_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    split
    · exact ikp_pure_bind (rd_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    split
    · exact ikp_pure_bind (rd_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    split
    · exact ikp_pure_bind (rd_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    split
    · exact ikp_pure_bind (rd_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    split
    · exact ikp_pure_bind (rd_setTcb_keep _ tcb σ hk _ rfl rfl rfl)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem rd_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbState = x.tcbState ∧ (fn v x).tcbFault = x.tcbFault ∧
      (fn v x).tcbSchedContext = x.tcbSchedContext) :
    IK Rdy (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact rd_threadSet _ _ (h _)

theorem rd_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scRefills = y.scRefills ∧ (f y).scRefillMax = y.scRefillMax ∧ (f y).scPeriod = y.scPeriod) :
    IK Rdy (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  dsimp only at hx
  split at hx
  · rename_i sc n
    refine rd_setObject_p _ _ _ ?_ hσ x hx
    rw [hk]
    refine ⟨(fun _ e => by cases e), (fun _ e => by cases e), ?_⟩
    show some ((f sc).scRefills, (f sc).scRefillMax, (f sc).scPeriod) = some (sc.scRefills, sc.scRefillMax, sc.scPeriod)
    rw [(hf sc).1, (hf sc).2.1, (hf sc).2.2]
  · exact hx.elim

/-! ## `rd_auto` -/

macro "rd_side" : tactic => `(tactic| first
  | trivial
  | (intro _; exact ⟨rfl, rfl, rfl⟩)
  | (intro _ _; exact ⟨rfl, rfl, rfl⟩)
  | (intro _; exact ⟨rfl, rfl⟩)
  | (intro _ h; cases h; done)
  | tq_side)

syntax "rd_leaf" : tactic
macro_rules | `(tactic| rd_leaf) => `(tactic| fail "no rd_leaf")

macro "rd_auto" : tactic => `(tactic| repeat' (first | rd_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| rd_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); tq_side))
macro_rules | `(tactic| rd_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); tq_side))
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| rd_leaf) => `(tactic| ((with_reducible refine rd_setObject _ _ ?_); rd_side))
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_setSimpleKo _ _ _)
macro_rules | `(tactic| rd_leaf) => `(tactic| ((with_reducible refine rd_threadSet _ _ ?_); rd_side))
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_archThreadSet _ _)
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_asUser _ _)
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_setMrs _ _ _)
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_setCap _ _)
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_dequeue _)
macro_rules | `(tactic| rd_leaf) => `(tactic| ((with_reducible refine rd_setThreadState _ _ ?_); rd_side))
macro_rules | `(tactic| rd_leaf) => `(tactic| ((with_reducible refine rd_optionUpdateThread _ _ _ ?_); rd_side))
macro_rules | `(tactic| rd_leaf) => `(tactic| ((with_reducible refine rd_updateSchedContext _ _ ?_); rd_side))
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_setThreadStateAct _)
macro_rules | `(tactic| rd_leaf) => `(tactic| ((with_reducible refine rd_setSchedulerAction_ns _ ?_); rd_side))
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_tcbReleaseRemove _)

/-! ## `reschedule_required`, `possible_switch_to` -/

theorem readRefillHead_nil {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills = []) :
    readRefillHead (Z := Unit) p σ = none := by
  show Option.bind (readSchedContext p σ) (fun sc => Option.bind (Lookup.oassert (sc.scRefills ≠ []) σ)
    (fun _ => Lookup.oreturn (refillHd sc) σ)) = _
  rw [Sched.readSchedContext_eq hk]
  simp [Lookup.oassert, hne, Lookup.ofail]

theorem mem_getScRefillReady {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) {w : Bool × State Unit}
    (h : w ∈ (getScRefillReady (Z := Unit) p σ).1) : w = (refillReady σ.curTime (refillHd y), σ) := by
  by_cases hne : y.scRefills = []
  · exfalso
    have e : readScRefillReady (Z := Unit) p σ = none := by
      show Option.bind (readRefillHead p σ) (fun h => Option.bind (Lookup.asks (fun s : State Unit => s.curTime) σ)
        (fun ct => Lookup.oreturn (refillReady ct h) σ)) = _
      rw [readRefillHead_nil hk hne]; rfl
    change w ∈ (NonDet.assertOpt (readScRefillReady (Z := Unit) p σ) σ).1 at h
    rw [e] at h; exact h
  · rw [Sched.getScRefillReady_eq hk hne] at h; exact Set.mem_singleton_iff.1 h

theorem mem_getScRefillSufficient {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (u : Ticks) {w : Bool × State Unit}
    (h : w ∈ (getScRefillSufficient (Z := Unit) p u σ).1) : w = (refillSufficient u (refillHd y), σ) := by
  by_cases hne : y.scRefills = []
  · exfalso
    have e : readScRefillSufficient (Z := Unit) p u σ = none := by
      show Option.bind (readRefillHead p σ) (fun h => Lookup.oreturn (refillSufficient u h) σ) = _
      rw [readRefillHead_nil hk hne]; rfl
    change w ∈ (NonDet.assertOpt (readScRefillSufficient (Z := Unit) p u σ) σ).1 at h
    rw [e] at h; exact h
  · rw [Sched.getScRefillSufficient_eq hk hne] at h; exact Set.mem_singleton_iff.1 h

/-- **`reschedule_required`**: the switch target is enqueued only after its own
asserts (schedulable, sufficient and ready), so it is `RdyT`. -/
theorem rd_rescheduleRequired : IK Rdy (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  refine ik_gets_bind fun σ => ?_
  try dsimp only
  split
  · rename_i t ht
    refine ikp_gets_bind ?_
    refine ikp_bind ?_ fun _ => rd_setSchedulerAction_ns _ fun _ h => by cases h
    refine ikp_when _ fun hs => ?_
    intro hσ r hr
    obtain ⟨xt, scp, y, n, hx, hsc, -, hy, hact, -⟩ := Sched.schedulable_inv hs
    obtain ⟨z, hz, hr⟩ := hr
    obtain ⟨x', hx', rfl⟩ := q1_mem_threadGet hz
    rw [hx] at hx'; cases hx'
    dsimp only at hr
    rw [hsc] at hr
    obtain ⟨z, hz, hr⟩ := hr
    obtain rfl : z = (scp, σ) := Set.mem_singleton_iff.1 hz
    obtain ⟨z, hz, hr⟩ := hr
    obtain rfl := mem_getScRefillSufficient hy 0 hz
    obtain ⟨z, hz, hr⟩ := hr
    obtain rfl := mem_getScRefillReady hy hz
    obtain ⟨z, ⟨hok, rfl⟩, hr⟩ := hr
    have hrd : refillReady σ.curTime (refillHd y) = true := by
      simp only [Bool.and_eq_true] at hok; exact hok.2
    exact rd_tsa_p _ t σ (fun q u hu => (q1_enq t q u hu).imp id fun e =>
      ⟨e, xt, scp, y, n, hx, hsc, hy, hact, hrd⟩) hσ r hr
  · exact ikp_of_ik (rd_setSchedulerAction_ns _ fun _ h => by cases h) σ
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_rescheduleRequired)

/-- The heap and the time, fixed. -/
abbrev KT (K : ObjRef → Option KernelObject) (T : Time) (σ : State Unit) : Prop := σ.kheap = K ∧ σ.curTime = T

theorem kt_rescheduleRequired (K : ObjRef → Option KernelObject) (T : Time) :
    IK (KT K T) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  repeat' (first | ik_step0 | ik_unfold)

theorem rdyT_kt {σ σ' : State Unit} {t : ObjRef} (h : RdyT σ t) (hk : σ'.kheap = σ.kheap)
    (ht : σ'.curTime = σ.curTime) : RdyT σ' t := by
  obtain ⟨x, c, y, n, hx, hc, hy, h1, h2⟩ := h
  exact ⟨x, c, y, n, by rw [hk]; exact hx, hc, by rw [hk]; exact hy, h1, by rw [ht]; exact h2⟩

/-- **`possible_switch_to`** of a thread `RdyT` at this state. -/
theorem rd_possibleSwitchTo_p (t : ObjRef) (σ : State Unit) (hR : RdyT σ t) :
    IKp Rdy σ (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef
  refine ikp_threadGet_bind fun x hx => ?_
  refine ikp_gets_bind ?_
  refine ikp_when _ fun _ => ?_
  refine ikp_gets_bind ?_
  refine ikp_threadGet_bind fun x' hx' => ?_
  refine ikp_gets_bind ?_
  try dsimp only
  split
  · exact rd_tsa_p _ t σ fun q u hu => (q1_enq t q u hu).imp id fun e => ⟨e, hR⟩
  · split
    · intro hσ y ⟨z, hz, hy⟩
      obtain ⟨e1, e2⟩ := kt_rescheduleRequired σ.kheap σ.curTime σ ⟨rfl, rfl⟩ z hz
      exact rd_tsa_p _ t z.2 (fun q u hu => (q1_enq t q u hu).imp id fun e => ⟨e, rdyT_kt hR e1 e2⟩)
        (rd_rescheduleRequired σ hσ z hz) y hy
    · unfold setSchedulerAction
      intro hσ y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact rdy_of_view hσ (fun t x hx => ⟨x, hx, rfl⟩) (fun t x hx hb _ => ⟨x, hx, rfl, hb⟩) (fun _ => rfl) rfl rfl
        (fun d p u hm => Or.inl hm) (fun u e => by cases e; exact Or.inr hR) (fun t hm => Or.inl hm)

end

end Fl4Proofs.P3.SInvR
