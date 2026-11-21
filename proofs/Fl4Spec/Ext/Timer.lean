/-
FL4 differences (PORTING.md, "FL4 differences"): **FL4's TCB timers**
(l4h 0003, `seL4_TCB_SetTimer`; DESIGN.md's l4h table).

FL4 keeps a per-core tree of armed one-shot TCB deadlines; at every kernel
exit, before choosing the next thread, `sched::awaken` runs `timer::fire`,
which fires the expired timers (at most 32 per entry): each signals its
thread's bound notification with the timer's badge, if the thread has one,
and requests a timer reprogram. l4v has no such timers. The timer tree is
not modelled (as for `TCBSetTimer` in `Ext/Tcb`), so which timers expire is
not decided here:

* `fl4TimerSignal σ σ'`: one notification signal, l4v's `send_signal` with
  one outcome.
* `fl4TimerFire σ σ'`: one fired timer: `σ` or a signal of it, then
  `reprogram_timer := true` (FL4 sets its reprogram flag after every fired
  timer).
* `fl4TimerFires`: any finite sequence of fired timers (none included).
* `fl4Awaken`: the nondeterministic step with every `fl4TimerFires`
  outcome; it does not fail. `Ext/Entry`'s `fl4CallKernel` runs it before
  `schedule` (whose own `awaken` is l4v's release-queue one).

The ported modules are not changed.
-/
import Fl4Spec.Ipc
import Mathlib.Logic.Relation

namespace Fl4Spec

open Classical

noncomputable section

section
variable {Z : Type} [StateExt Z]

/-- One notification signal of a fired TCB timer: l4v's `send_signal` on
some notification and badge, with the one outcome `σ'`. -/
def fl4TimerSignal (σ σ' : State Z) : Prop :=
  ∃ n b, sendSignal n b σ = ({((), σ')}, False)

/-- One fired TCB timer (FL4's `timer::fire` loop body): its thread's bound
notification signalled if it has one (`fl4TimerSignal`), then the timer
reprogram requested. -/
def fl4TimerFire (σ σ' : State Z) : Prop :=
  ∃ σ1, (σ1 = σ ∨ fl4TimerSignal σ σ1) ∧ σ' = { σ1 with reprogramTimer := true }

/-- Any finite sequence of fired TCB timers. -/
def fl4TimerFires : State Z → State Z → Prop := Relation.ReflTransGen fl4TimerFire

/-- **FL4's TCB timer step** (the module docstring): any `fl4TimerFires`
outcome; it does not fail. -/
def fl4Awaken : SMonad Z Unit := fun σ => ({p | fl4TimerFires σ p.2}, False)

theorem mem_fl4Awaken {σ σ' : State Z} : ((), σ') ∈ (fl4Awaken σ).1 ↔ fl4TimerFires σ σ' := Iff.rfl

end

end

end Fl4Spec
