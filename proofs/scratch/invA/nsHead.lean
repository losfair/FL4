/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §2/§4, invA): **NativeScope,
spec part: no thread is in `runningVM`**, kept by every spec step (spec side
only; imports only Fl4Spec via SpecInvNativeScopeT, outside the JAtZ cone).

* `NativeScopeS σ := TI nsQ σ` with `nsQ x := x.tcbState ≠ .runningVM`: the
  same statement as IpcLeaves' `NativeScope` (consumed at the top by
  `kernel_entryJ26P`'s `hNS` / `hNSR` [S], KENTRY-PLAN fin1); l4v has no
  counterpart (FL4's VT-x state, out of the native scope).
* The spec never writes `runningVM` (it only reads it, Fl4Spec/Ipc.lean:515):
  every `setThreadState` has a literal state other than `runningVM`, every
  other TCB write keeps `tcbState`, and a new TCB is `defaultTcb` (Inactive).
  So the writers are leaves with a side condition closed by `ns_side`:
  `setObject` / `setSimpleKo` / `threadSet` / `archThreadSet` / `asUser` /
  `setMrs` / `setCap` / `retypeRegion(With)` / `deleteObjects`
  (SpecInvNativeScopeT), `setThreadState` (`ts ≠ runningVM`),
  `optionUpdateThread`.
* The rest: one lemma per spec function reachable from
  `fl4KernelEntrySyscall`, bottom-up (`ns_auto`: the leaves, `ik_step0`,
  else unfold the head spec function). Generated from the spec's call graph
  (invA scratch gen.py, untracked); the recursive ones by hand.
* `kentry_nativeScope`: every outcome of the syscall entry from a
  `NativeScopeS` state is `NativeScopeS`; `kcall_nativeScope`: the same for
  `fl4CallKernel rep ev` for every event (interrupts, faults, timer);
  `boot_nativeScope`: the initial state `initASt`.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- A TCB not in `runningVM`. -/
def nsQ (x : Tcb) : Prop := x.tcbState ≠ .runningVM

/-- No thread is in `runningVM` (IpcLeaves' `NativeScope`). -/
abbrev NativeScopeS (σ : State Unit) : Prop := TI nsQ σ

abbrev NSK {α : Type} (m : NonDet (State Unit) α) : Prop := IK NativeScopeS m
abbrev NSKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE NativeScopeS m

/-- The side conditions of the TCB-writer leaves. -/
macro "ns_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _ hx; exact ⟨hx, hx, hx, hx, hx, hx⟩)
  | (intro _ _; simp [nsQ]; done)
  | (intro _ hx; simpa [nsQ] using hx)
  | (intro _ _ _; simp [nsQ]; done)
  | (intro _ _ hx; simpa [nsQ] using hx)
  | (simp; done)
  | (split <;> simp <;> done)
  | (simp [nsQ, defaultTcb]; done)
  | decide)

syntax "ns_leaf" : tactic
macro_rules | `(tactic| ns_leaf) => `(tactic| fail "no ns_leaf")

macro "ns_auto" : tactic => `(tactic| repeat' (first | ns_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_setObject _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ti_setSimpleKo _ _ _)
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_threadSet _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_archThreadSet _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_asUser _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_setMrs _ _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_setCap _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_retypeRegionWith _ _ _ _ _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_retypeRegion _ _ _ _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ti_deleteObjects _ _)

theorem ns_setThreadState (t : ObjRef) (ts : ThreadState) (h : ts ≠ .runningVM) :
    NSK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (ti_threadSet _ _ fun _ _ => h) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ns_setThreadState _ _ ?_); ns_side))

theorem ns_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, nsQ x → nsQ (fn v x)) : NSK (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact ti_threadSet _ _ (h _)
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ns_optionUpdateThread _ _ _ ?_); ns_side))

