/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, g1c): **OnlyIdle (l4v
`only_idle`): every TCB in `IdleThreadState` is the idle thread**, kept by every
spec step (spec side only; imports only Fl4Spec via SpecInvFaultTcbsT, outside
the JAtZ cone). g1b's handoff (KENTRY-PLAN g1b): the carried form of its [J]
premise `OnlyIdle`.

* `oiQ N p x := x.tcbState = .idleThreadState → p = N`, `OIS N := TP (oiQ N)`
  (SpecInvFaultTcbsT's pointer-dependent `TP`: the idle pointer `N` is exempt);
  `OnlyIdle σ ↔ OIS σ.idleThread σ` (SpecInvAllO, `onlyIdle_iff`).
* The spec writes `IdleThreadState` only in `initKheap` (grep Fl4Spec:
  Init.lean:97): every `setThreadState` has a literal state other than
  `IdleThreadState` (`oi_setThreadState`'s side condition `ts ≠ IdleThreadState`),
  every other TCB write keeps `tcbState`, and a new TCB is `defaultTcb`
  (Inactive). So every TCB writer is a `tp_*` leaf with a side condition closed
  by `oi_side`, as invA's NativeScope family (SpecInvNativeScopeF1).
* The rest: one lemma per spec function reachable from
  `fl4KernelEntrySyscall`, bottom-up (`oi_auto`), generated from the spec's
  call graph by invA's gen.py (scratch/g1c, untracked: `sh mkoi.sh`); the
  recursive ones by invA's manual.py texts. Parts 2-6: SpecInvAllO2..O6.
-/
import Fl4Proofs.P3.SpecInvFaultTcbsT
open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- A TCB in `IdleThreadState` sits at `N`. -/
def oiQ (N : ObjRef) (p : ObjRef) (x : Tcb) : Prop := x.tcbState = .idleThreadState → p = N

/-- Only the thread at `N` is in `IdleThreadState`. -/
abbrev OIS (N : ObjRef) (σ : State Unit) : Prop := TP (oiQ N) σ

variable {N : ObjRef}

abbrev OIK {α : Type} (N : ObjRef) (m : NonDet (State Unit) α) : Prop := IK (OIS N) m
abbrev OIKE {ε α : Type} (N : ObjRef) (m : NonDetE (State Unit) ε α) : Prop := IKE (OIS N) m

/-- The side conditions of the TCB-writer leaves. -/
macro "oi_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _ _ hx; exact ⟨hx, hx, hx, hx, hx, hx⟩)
  | (intro _ _; simp [oiQ, defaultTcb]; done)
  | (left; decide)
  | (left; simp; done)
  | (left; split <;> simp <;> done)
  | (intro _ _ _; simp [oiQ]; done)
  | (intro _ hx; simpa [oiQ] using hx)
  | (intro _ _ hx; simpa [oiQ] using hx)
  | (simp; done)
  | (split <;> simp <;> done)
  | (simp [oiQ, defaultTcb]; done)
  | decide)

syntax "oi_leaf" : tactic
macro_rules | `(tactic| oi_leaf) => `(tactic| fail "no oi_leaf")

macro "oi_auto" : tactic => `(tactic| repeat' (first | oi_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_setObject _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact tp_setSimpleKo _ _ _)
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_threadSet _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_archThreadSet _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_asUser _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_setMrs _ _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_setCap _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_retypeRegionWith _ _ _ _ _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_retypeRegion _ _ _ _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact tp_deleteObjects _ _)

/-- **`set_thread_state`** (hand lemma): any state but `IdleThreadState` (no spec
call site writes it: every site passes another literal), or the idle thread itself. -/
theorem oi_setThreadState (t : ObjRef) (ts : ThreadState) (h : ts ≠ .idleThreadState ∨ t = N) :
    OIK N (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (tp_threadSet _ _ fun _ _ hs => h.resolve_left (not_not.2 hs)) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine oi_setThreadState _ _ ?_); oi_side))

theorem oi_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, oiQ N t x → oiQ N t (fn v x)) : OIK N (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact tp_threadSet _ _ (h _)
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine oi_optionUpdateThread _ _ _ ?_); oi_side))

/-- **Retype** (hand lemma): a new TCB is `defaultTcb` (Inactive). -/
theorem oi_defaultTcb (p : ObjRef) (d : Domain) : oiQ N p (defaultTcb d) := by
  simp [oiQ, defaultTcb]

