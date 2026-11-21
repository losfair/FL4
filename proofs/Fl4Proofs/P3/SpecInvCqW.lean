/-
P3 (DESIGN.md §9), invariant line G1 (ctq5): **at every kernel exit the
current thread is bound to `cur_sc`** (spec side only, outside the JAtZ cone).

* `CS g s`: the current thread's TCB has SC `g s.curSc`; `CurScT := CS some`
  (l4v `cur_sc_tcb_are_bound`, TCB side; with sb2's `ScSym` the SC's
  `sc_tcb` is the current thread, `scTcb_curSc`).
* Frames: a TCB write keeping `tcb_sched_context`, a non-TCB write, machine
  and field updates other than `cur_thread` / `cur_sc` (`cs_auto`).
* `schedule`'s every branch ends in `sc_and_timer`, whose
  `switch_sched_context` reads the current thread's SC (`assert_opt`: it is
  bound) and sets `cur_sc` to it; the rest of `sc_and_timer` and
  `activate_thread` keep `CS`.
* **`kentry_curScT c σ : ∀ y ∈ (fl4KernelEntrySyscall true c σ).1, CurScT y.2`**
  and **`kcall_curScT`** (every event): no premise. Hence **`kentry_ctSc`**:
  vi2/vi3's `CtSc` [J] holds at every state a kernel entry leaves.
-/
import Fl4Proofs.P3.SpecInvCqV
import Fl4Proofs.P3.SpecInvViH
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- The current thread's TCB is bound to `g cur_sc`. -/
abbrev CS (g : ObjRef → Option ObjRef) (s : State Unit) : Prop :=
  ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = g s.curSc

/-- **CurScT**: the current thread is bound to `cur_sc` (l4v
`cur_sc_tcb_are_bound`). -/
abbrev CurScT (s : State Unit) : Prop := CS some s

section
variable {g : ObjRef → Option ObjRef}

theorem cs_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : ∀ x y, σ.kheap p = some (.tcb x) → o = .tcb y → y.tcbSchedContext = x.tcbSchedContext) :
    IKp (CS g) σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst y2
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  intro x' hx'
  dsimp only at hx' ⊢
  by_cases e : σ.curThread = p
  · rw [e] at hx'
    simp at hx'
    subst hx'
    obtain ⟨x0, rfl⟩ := q1_aType_tcb hty
    rw [ho x0 x' hk rfl]; exact hσ x0 (by rw [e]; exact hk)
  · rw [Function.update_of_ne e] at hx'; exact hσ x' hx'

theorem cs_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → False) :
    IK (CS g) (setObject (Z := Unit) p o) :=
  fun σ => cs_setObject_p p o σ fun _ y _ e => (ho y e).elim

theorem cs_setTcb_keep (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (h : y.tcbSchedContext = x.tcbSchedContext) : IKp (CS g) σ (setObject (Z := Unit) p (.tcb y)) :=
  cs_setObject_p _ _ σ fun x0 y0 hk e => by
    rw [hx] at hk; cases hk; cases e; exact h

theorem cs_threadSet (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext) :
    IK (CS g) (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx => cs_setTcb_keep _ x σ (getTcb_kheap hx) _ (hf x)

theorem cs_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : IK (CS g) (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => cs_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl

theorem cs_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : IK (CS g) (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (cs_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl) fun _ => ik_pure _

theorem cs_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : IK (CS g) (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (cs_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl) fun _ => ?_
  repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

end

syntax "cs_leaf" : tactic
macro_rules | `(tactic| cs_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| cs_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| cs_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| cs_leaf) => `(tactic| ((with_reducible refine cs_setObject _ _ ?_); intro _ h; cases h))
macro_rules | `(tactic| cs_leaf) => `(tactic| ((with_reducible refine cs_threadSet _ _ ?_); intro _; rfl))
macro_rules | `(tactic| cs_leaf) => `(tactic| with_reducible exact cs_archThreadSet _ _)
macro_rules | `(tactic| cs_leaf) => `(tactic| with_reducible exact cs_asUser _ _)
macro_rules | `(tactic| cs_leaf) => `(tactic| with_reducible exact cs_setMrs _ _ _)

macro "cs_auto" : tactic => `(tactic| repeat' (first | cs_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

/-! ## The exit -/

theorem cs_activateThread (g : ObjRef → Option ObjRef) : IK (CS g) (activateThread (Z := Unit)) := by
  unfold activateThread; cs_auto

theorem cs_setNextInterrupt (g : ObjRef → Option ObjRef) : IK (CS g) (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; cs_auto

theorem cs_commitTime (g : ObjRef → Option ObjRef) : IK (CS g) (commitTime (Z := Unit)) := by
  unfold commitTime; cs_auto

theorem cs_unblock (g : ObjRef → Option ObjRef) (o : Option ObjRef) (a b : Option Bool) :
    IK (CS g) (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; cs_auto

/-- **`switch_sched_context`** binds `cur_sc` to the current thread's SC. -/
theorem curScT_switchSchedContext : PostK CurScT (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext
  intro σ y ⟨z, hz, hy⟩
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  unfold getTcbObjRef at hz
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  obtain ⟨a, ha, hy⟩ := hy
  obtain ⟨ha1, ha2⟩ := cq5_mem_assertOpt ha
  obtain ⟨scp, a2⟩ := a
  simp only at ha1 ha2; subst a2
  have h0 : CS (fun _ => some scp) σ := fun x' hx' => by rw [hx] at hx'; cases hx'; exact ha1
  obtain ⟨w, hw, hy⟩ := hy
  have hw' : CS (fun _ => some scp) w.2 := by rw [(cq5_mem_getSc hw).1]; exact h0
  obtain ⟨v, hv, hy⟩ := hy
  have hv' : CS (fun _ => some scp) v.2 := by
    refine (ik_when _ ?_) w.2 hw' v hv
    exact ik_bind (by cs_auto) fun _ => cs_unblock _ _ _ _
  obtain ⟨u, hu, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hu] at hy
  obtain ⟨r, hr, hy⟩ := hy
  have hr' : CS (fun _ => some scp) r.2 := (ik_when _ (cs_commitTime _)) v.2 hv' r hr
  rw [Set.mem_singleton_iff.1 hy]
  exact hr'

theorem post_bind_ik {Q : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : PostK Q m) (hg : ∀ a, IK Q (g a)) : PostK Q (m >>= g) := by
  intro s y ⟨z, hz, hy⟩
  exact hg z.1 z.2 (hm s z hz) y hy

theorem curScT_scAndTimer : PostK CurScT (scAndTimer (Z := Unit)) := by
  unfold scAndTimer
  refine post_bind_ik curScT_switchSchedContext fun _ => ?_
  cs_auto

/-- Every branch of **`schedule`** ends in `sc_and_timer`. -/
theorem curScT_schedule : PostK CurScT (schedule (Z := Unit)) := by
  unfold schedule
  refine post_bind fun _ => ?_
  refine post_bind fun _ => ?_
  refine post_bind fun _ => ?_
  refine post_bind fun _ => ?_
  refine post_bind fun _ => ?_
  try dsimp only
  split
  · exact curScT_scAndTimer
  · exact post_bind fun _ => post_bind fun _ => curScT_scAndTimer
  · exact post_bind fun _ => curScT_scAndTimer

theorem curScT_exit : PostK CurScT (fl4Awaken (Z := Unit) >>= fun _ => schedule >>= fun _ => activateThread) :=
  post_bind fun _ => post_bind_ik curScT_schedule fun _ => cs_activateThread _

theorem curScT_fl4CallKernel (rep : Bool) (ev : Event) : PostK CurScT (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  exact post_bind fun _ => curScT_exit

/-- **(b) `CurScT` after every syscall entry** (no premise). -/
theorem kentry_curScT (c : Syscall) (σ : State Unit) :
    ∀ y ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1, CurScT y.2 := by
  unfold fl4KernelEntrySyscall
  exact post_bind (fun _ => post_bind fun _ => curScT_fl4CallKernel true _) σ

/-- **(c) `CurScT` after every kernel event** (no premise). -/
theorem kcall_curScT (rep : Bool) (ev : Event) (σ : State Unit) :
    ∀ y ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, CurScT y.2 :=
  curScT_fl4CallKernel rep ev σ

/-- vi2/vi3's `CtSc` [J] follows. -/
theorem ctSc_of_curScT {σ : State Unit} (h : CurScT σ) : SInvI.CtSc σ :=
  fun x hx => by rw [h x hx]; exact fun e => by cases e

theorem kentry_ctSc (c : Syscall) (σ : State Unit) :
    ∀ y ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1, SInvI.CtSc y.2 :=
  fun y hy => ctSc_of_curScT (kentry_curScT c σ y hy)

end

end Fl4Proofs.P3.SInvQ
