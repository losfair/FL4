/-
P3 (DESIGN.md §9), invariant line G1 (invA2): **FaultTcbsS (l4v
`fault_tcbs_valid_states`) kept by the spec functions** (spec side only,
outside the JAtZ cone), with a list `L` of threads known to have no fault.

* `ftlQ L p x := ftsQ x ∧ (p ∈ L → x.tcbFault = none)`, `FTL L := TP (ftlQ L)`;
  `FTL [] σ ↔ FaultTcbsS σ`. Carrying `L` lets a wake-up to Running /
  Restart / a receive state of a thread `t ∈ L` keep the invariant
  (`ft_setThreadState`'s side condition: the new state is Inactive /
  BlockedOnSend / BlockedOnReply, or `t ∈ L`).
* Leaves: SpecInvFaultTcbsT's `tp_*` writers; every TCB write of the spec but
  the fault write of `sendFaultIpc` and the wake-ups keeps `ftlQ L`
  pointwise (fault cleared, or state and fault unchanged).
* The rest: one lemma per spec function by `ft_auto` (generated, as
  SpecInvNativeScopeF*; invA scratch gen.py), for every `L`; the functions
  with a wake-up or the fault write are proved by hand (SpecInvFaultTcbsW).
-/
import Fl4Proofs.P3.SpecInvFaultTcbsT
import Fl4Proofs.P3.SpecInvFaultTcbs
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- `ftsQ`, and no fault for the threads of `L`. -/
def ftlQ (L : List ObjRef) (p : ObjRef) (x : Tcb) : Prop := ftsQ x ∧ (p ∈ L → x.tcbFault = none)

/-- FaultTcbsS, and no fault at the threads of `L`. -/
abbrev FTL (L : List ObjRef) (σ : State Unit) : Prop := TP (ftlQ L) σ

theorem FTL.nil_iff (σ : State Unit) : FTL [] σ ↔ FaultTcbsS σ :=
  ⟨fun h p x hp => (h p x hp).1, fun h p x hp => ⟨h p x hp, fun h => nomatch h⟩⟩

variable {L : List ObjRef}

abbrev FTK {α : Type} (L : List ObjRef) (m : NonDet (State Unit) α) : Prop := IK (FTL L) m
abbrev FTKE {ε α : Type} (L : List ObjRef) (m : NonDetE (State Unit) ε α) : Prop := IKE (FTL L) m

/-- The side conditions of the TCB-writer leaves. -/
macro "ft_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _ _ hx; exact ⟨hx, hx, hx, hx, hx, hx⟩)
  | (intro _ _; exact ⟨fun h => absurd rfl h, fun _ => rfl⟩)
  | (intro _ _; exact ⟨fun h => absurd rfl h, fun _ => rfl⟩)
  | (exact Or.inl trivial)
  | (exact Or.inr (by simp; done))
  | (simp [ftlQ, ftsQ, faultTcbSt]; done)
  | (intro _ hx; simpa [ftlQ, ftsQ, faultTcbSt] using hx)
  | (intro _ _ hx; simpa [ftlQ, ftsQ, faultTcbSt] using hx))

syntax "ft_leaf" : tactic
macro_rules | `(tactic| ft_leaf) => `(tactic| fail "no ft_leaf")

macro "ft_auto" : tactic => `(tactic| repeat' (first | ft_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_setObject _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact tp_setSimpleKo _ _ _)
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_threadSet _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_archThreadSet _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_asUser _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_setMrs _ _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_setCap _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_retypeRegionWith _ _ _ _ _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_retypeRegion _ _ _ _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact tp_deleteObjects _ _)

/-- `set_thread_state`: a fault-holding state, or a thread known to have no fault. -/
theorem ft_setThreadState (t : ObjRef) (ts : ThreadState) (h : faultTcbSt ts ∨ t ∈ L) :
    FTK L (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (tp_threadSet _ _ fun x hx => ⟨fun hf => ?_, hx.2⟩) fun _ => ?_
  · rcases h with h | h
    · exact h
    · exact absurd (hx.2 h) hf
  · unfold setThreadStateAct setSchedulerAction; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine ft_setThreadState _ _ ?_); ft_side))

theorem ft_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, ftlQ L t x → ftlQ L t (fn v x)) : FTK L (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact tp_threadSet _ _ (h _)
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine ft_optionUpdateThread _ _ _ ?_); ft_side))

