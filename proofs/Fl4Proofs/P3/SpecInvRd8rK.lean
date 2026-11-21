/-
P3 (DESIGN.md §9), invariant line G1 (rd8r, KENTRY-PLAN rd8p handoff 1):
**`HO`, the stepwise form of rd8p's `CurHold`: the leaves** (spec side only,
outside the JAtZ cone).

* **`HO s`**: every TCB bound to `cur_sc` is in a state `HS (t = ct)`: not
  blocked on an endpoint or a notification, and running / restart only when it
  is the current thread. `HO → CurHold` (`curHold_of_ho`): `BlkR` needs an
  endpoint or notification block. Unlike `CurHold`, `HO` does not read the
  fault, so `cancel_ipc`'s fault clear of a timeout-faulted sender (rd8f's
  one-step `BlkR`) keeps it, and it is stepwise invariant over the whole
  deletion cone together with nq2's `NQ []` (SpecInvRd8rC).
* Writers: a heap write keeping a TCB's SC and state or making the state
  quiet (`HS False`: inactive, BlockedOnReply, idle) or unbinding it
  (`ho_threadSet`); a write of a TCB not bound to `cur_sc` (`ho_threadSet_nh`,
  the restart helpers); the current thread's own write (`ho_threadSet_ct`, the
  Restart write of the invocation shell); `delete_objects` (detype only
  removes objects). `cur_sc` / `cur_thread` are written only by `schedule`.
* `ho_auto`: the driver of the generated family SpecInvRd8rF*.
-/
import Fl4Proofs.P3.SpecInvRd8pA
open Classical

namespace Fl4Proofs.P3.SInvR.B8r
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-- The state of a holder of `cur_sc`; `b`: it is the current thread. -/
def HS (b : Prop) : ThreadState → Prop
  | .blockedOnReceive _ _ _ => False
  | .blockedOnSend _ _ => False
  | .blockedOnNotification _ => False
  | .running => b
  | .runningVM => b
  | .restart => b
  | .inactive => True
  | .blockedOnReply _ => True
  | .idleThreadState => True

theorem HS.mono {b : Prop} {ts : ThreadState} (h : HS False ts) : HS b ts := by
  cases ts
  all_goals first | exact False.elim h | exact trivial

/-- The TCB part of `HO` for SC `c`. -/
abbrev HOT (c : ObjRef) (b : Prop) (y : Tcb) : Prop := y.tcbSchedContext = some c → HS b y.tcbState

/-- **`HO`** (module docstring). -/
def HO (s : State Unit) : Prop :=
  ∀ t x, s.kheap t = some (.tcb x) → HOT s.curSc (t = s.curThread) x

abbrev HOK {α : Type} (m : NonDet (State Unit) α) : Prop := IK HO m
abbrev HOKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE HO m

/-- **`HO` gives rd8p's `CurHold`.** -/
theorem curHold_of_ho {s : State Unit} (h : HO s) : B8p.CurHold s := by
  intro t x hx hc
  have hs := h t x hx hc
  refine ⟨fun hB => ?_, ?_⟩
  · rcases hB with ⟨n, e⟩ | ⟨e', d, e, -⟩ | ⟨e', r, d, e⟩ <;> rw [e] at hs <;> exact hs
  · revert hs
    cases x.tcbState
    all_goals first
      | (intro h; exact Or.inl h)
      | (intro _; exact Or.inr rfl)
      | (intro h; exact False.elim h)

/-- `t` is not bound to `cur_sc`. -/
def NH (t : ObjRef) (s : State Unit) : Prop :=
  ∀ x, s.kheap t = some (.tcb x) → x.tcbSchedContext ≠ some s.curSc

/-! ## The heap update of `set_object` -/

theorem ho_upd {σ : State Unit} (h : HO σ) (p : ObjRef) (o : KernelObject)
    (hty : ∀ y, o = .tcb y → ∃ x, σ.kheap p = some (.tcb x))
    (ho : ∀ x, σ.kheap p = some (.tcb x) → HOT σ.curSc (p = σ.curThread) x →
      ∀ y, o = .tcb y → HOT σ.curSc (p = σ.curThread) y) :
    HO { σ with kheap := Function.update σ.kheap p (some o) } := by
  intro t y hy
  show HOT σ.curSc (t = σ.curThread) y
  change Function.update σ.kheap p (some o) t = some (.tcb y) at hy
  by_cases e : t = p
  · subst e
    rw [Function.update_self] at hy
    have ho' : o = .tcb y := by injection hy
    obtain ⟨x, hx⟩ := hty y ho'
    exact ho x hx (h t x hx) y ho'
  · rw [Function.update_of_ne e] at hy
    exact h t y hy

theorem ho_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : ∀ x, σ.kheap p = some (.tcb x) → HOT σ.curSc (p = σ.curThread) x →
      ∀ y, o = .tcb y → HOT σ.curSc (p = σ.curThread) y) :
    IKp HO σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst y2
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine ho_upd hσ p o (fun y0 hy0 => ?_) ho
  obtain ⟨x0, e⟩ := R14.ck_aType hty y0 hy0
  exact ⟨x0, hk.trans (congrArg some e)⟩

theorem ho_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → False) :
    HOK (setObject (Z := Unit) p o) :=
  fun σ => ho_setObject_p p o σ fun _ _ _ y e => (ho y e).elim

theorem ho_setTcb_keep (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (h : ∀ c b, HOT c b x → HOT c b y) : IKp HO σ (setObject (Z := Unit) p (.tcb y)) :=
  ho_setObject_p _ _ σ fun x0 hk hc y0 e => by
    rw [hx] at hk; cases hk; cases e; exact h _ _ hc

theorem ho_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    HOK (setSimpleKo (Z := Unit) f p e) := by
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
  refine ho_upd hσ _ _ (fun y0 hy0 => ?_) (fun x0 hx0 _ _ _ => ?_)
  · obtain ⟨x0, e⟩ := R14.ck_aType hty y0 hy0
    exfalso
    dsimp only at e; subst e
    simp [isSimpleType, aType] at hsimp
  · exfalso
    rw [hk] at hx0; cases hx0
    simp [isSimpleType, aType] at hsimp

/-- A TCB update keeping `HOT` (SC kept or none; state kept or quiet). -/
theorem ho_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext ∨ (f x).tcbSchedContext = none)
    (hs : ∀ x, (f x).tcbState = x.tcbState ∨ HS False (f x).tcbState) :
    HOK (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => ho_setTcb_keep _ x σ (getTcb_kheap hx) _ fun c b hc hsc => ?_
  have hsc' : x.tcbSchedContext = some c := by
    rcases hf x with e | e
    · rw [← e]; exact hsc
    · rw [e] at hsc; cases hsc
  rcases hs x with e | e
  · rw [e]; exact hc hsc'
  · exact HS.mono e

/-- A TCB update (SC kept) of a thread not bound to `cur_sc`. -/
theorem ho_threadSet_nh (f : Tcb → Tcb) (t : ObjRef) (σ : State Unit)
    (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext) (hn : NH t σ) :
    IKp HO σ (threadSet (Z := Unit) f t) := by
  unfold threadSet
  intro hσ y ⟨z, hz, hy⟩
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    have hk := getTcb_kheap e
    refine ho_setObject_p t _ σ (fun x hx _ y' ey hsc => ?_) hσ y hy
    rw [hk] at hx; cases hx; cases ey
    exact absurd (by rw [← hf a]; exact hsc) (hn a hk)

/-- A TCB update (SC kept) of the current thread to a state it may hold. -/
theorem ho_threadSet_ct (f : Tcb → Tcb) (t : ObjRef) (σ : State Unit) (ht : t = σ.curThread)
    (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext) (hs : ∀ x, HS True (f x).tcbState) :
    IKp HO σ (threadSet (Z := Unit) f t) := by
  unfold threadSet
  intro hσ y ⟨z, hz, hy⟩
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    refine ho_setObject_p t _ σ (fun x hx _ y' ey _ => ?_) hσ y hy
    cases ey
    have h := hs a
    revert h
    subst ht
    cases (f a).tcbState
    all_goals first
      | (intro _; exact rfl)
      | (intro _; exact trivial)
      | (intro h; exact False.elim h)

theorem ho_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : HOK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => ho_setTcb_keep _ x σ (getTcb_kheap hx) _ fun _ _ h => h

theorem ho_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : HOK (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (ho_setTcb_keep _ x σ (getTcb_kheap hx) _ fun _ _ h => h) fun _ => ik_pure _

theorem ho_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : HOK (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (ho_setTcb_keep _ x σ (getTcb_kheap hx) _ fun _ _ h => h) fun _ => ?_
  repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

theorem ho_setCap (c : Cap) (sl : CslotPtr) : HOK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (ho_setObject_p _ _ σ fun _ _ _ _ e => by cases e)
    · exact ikp_fail_bind
  · rename_i tcb
    split
    · exact ikp_pure_bind (ho_setTcb_keep _ tcb σ hk _ fun _ _ h => h)
    split
    · exact ikp_pure_bind (ho_setTcb_keep _ tcb σ hk _ fun _ _ h => h)
    split
    · exact ikp_pure_bind (ho_setTcb_keep _ tcb σ hk _ fun _ _ h => h)
    split
    · exact ikp_pure_bind (ho_setTcb_keep _ tcb σ hk _ fun _ _ h => h)
    split
    · exact ikp_pure_bind (ho_setTcb_keep _ tcb σ hk _ fun _ _ h => h)
    split
    · exact ikp_pure_bind (ho_setTcb_keep _ tcb σ hk _ fun _ _ h => h)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem ho_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbSchedContext = x.tcbSchedContext) (h2 : ∀ v x, (fn v x).tcbState = x.tcbState) :
    HOK (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact ho_threadSet _ _ (fun x => Or.inl (h _ x)) (fun x => Or.inl (h2 _ x))

theorem ho_detype (S : Set ObjRef) {σ : State Unit} (h : HO σ) : HO (detype S σ) := by
  intro t x hx
  change (if t ∈ S then none else σ.kheap t) = some (.tcb x) at hx
  split at hx
  · cases hx
  · exact h t x hx

/-- **`delete_objects` keeps `HO`.** -/
theorem ho_deleteObjects (ptr : Word) (bits : Nat) : HOK (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  exact ik_bind (ik_doMachineOp (fun _ _ h => h) _) fun _ => ik_modify fun σ h => ho_detype _ h

/-! ## `set_thread_state` -/

theorem ho_sta (t : ObjRef) : HOK (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct
  repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when) | (unfold NonDet.unless))

/-- `set_thread_state` to a quiet state. -/
theorem ho_setThreadState (t : ObjRef) (ts : ThreadState) (h : HS False ts) :
    HOK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ik_bind (ho_threadSet _ _ (fun _ => Or.inl rfl) (fun _ => Or.inr h)) fun _ => ho_sta t

/-- `set_thread_state` of a thread not bound to `cur_sc`. -/
theorem ho_setThreadState_nh (t : ObjRef) (ts : ThreadState) (σ : State Unit) (hn : NH t σ) :
    IKp HO σ (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ikp_bind (ho_threadSet_nh _ _ σ (fun _ => rfl) hn) fun _ => ho_sta t

/-- `set_thread_state` of the current thread. -/
theorem ho_setThreadState_ct (t : ObjRef) (ts : ThreadState) (σ : State Unit) (ht : t = σ.curThread)
    (h : HS True ts) : IKp HO σ (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ikp_bind (ho_threadSet_ct _ _ σ ht (fun _ => rfl) fun _ => h) fun _ => ho_sta t

/-! ## `ho_auto` -/

syntax "ho_leaf" : tactic
macro_rules | `(tactic| ho_leaf) => `(tactic| fail "no ho_leaf")

macro "ho_hs" : tactic => `(tactic| exact trivial)

macro "ho_side" : tactic => `(tactic| first
  | (intro _; exact Or.inl rfl)
  | (intro _; exact Or.inr rfl)
  | (intro _; right; ho_hs)
  | (intro t ht; cases ht; done)
  | (intro _ _; rfl))

macro "ho_auto" : tactic => `(tactic| repeat' (first | ho_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| ho_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| ho_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| ho_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| ho_leaf) => `(tactic| ((with_reducible refine ho_setObject _ _ ?_); intro _ h; cases h))
macro_rules | `(tactic| ho_leaf) => `(tactic| with_reducible exact ho_setSimpleKo _ _ _)
macro_rules | `(tactic| ho_leaf) => `(tactic| ((with_reducible refine ho_threadSet _ _ ?_ ?_) <;> ho_side))
macro_rules | `(tactic| ho_leaf) => `(tactic| with_reducible exact ho_archThreadSet _ _)
macro_rules | `(tactic| ho_leaf) => `(tactic| with_reducible exact ho_asUser _ _)
macro_rules | `(tactic| ho_leaf) => `(tactic| with_reducible exact ho_setMrs _ _ _)
macro_rules | `(tactic| ho_leaf) => `(tactic| with_reducible exact ho_setCap _ _)
macro_rules | `(tactic| ho_leaf) => `(tactic| ((with_reducible refine ho_optionUpdateThread _ _ _ ?_ ?_) <;> (intro _ _; rfl)))
macro_rules | `(tactic| ho_leaf) => `(tactic| ((with_reducible refine ho_setThreadState _ _ ?_); ho_hs))
macro_rules | `(tactic| ho_leaf) => `(tactic| with_reducible exact ho_deleteObjects _ _)

end

end Fl4Proofs.P3.SInvR.B8r
