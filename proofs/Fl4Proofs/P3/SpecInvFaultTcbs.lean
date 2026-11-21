/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §2/§4, invA): **FaultTcbs: a
thread with a fault is not active** (l4v `fault_tcbs_valid_states`, the slice
the top consumes; spec side only, outside the JAtZ cone).

* `FaultTcbs σ := TI ftQ σ`, `ftQ x := x.tcbFault ≠ none → ¬ activeSt x.tcbState`
  (`activeSt`: Running or Restart, l4v `active`). l4v's
  `fault_tcbs_valid_states` is stronger (a faulted thread is Inactive,
  BlockedOnSend or BlockedOnReply); `FaultTcbsS` states that form and
  `FaultTcbsS.weak` gives `FaultTcbs`.
* Consumer at the top (KENTRY-PLAN fin1): `JEntryAt.cnf` (ct has no fault),
  from an active ct (`FaultTcbs.ct`).
* `boot_faultTcbs`, `boot_faultTcbsS`: the initial state (no TCB has a fault).
* Preservation over the syscall entry is NOT proved here (invA handoff): the
  weak form alone is not inductive (a faulted BlockedOnReceive thread woken by a
  send would break it), so the proof must carry `FaultTcbsS`, whose writers
  (`sendFaultIpc`'s fault write before the send blocks the sender, the wake-ups
  to Running/Restart in send/receive/reply/restart/cancel paths) need
  per-call-site Hoare reasoning (l4v's `fault_tcbs_valid_states` lemmas).
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

/-- l4v `active`: Running or Restart. -/
def activeSt : ThreadState → Prop
  | .running => True
  | .restart => True
  | _ => False

/-- A TCB with a fault is not active. -/
def ftQ (x : Tcb) : Prop := x.tcbFault ≠ none → ¬ activeSt x.tcbState

/-- Every thread with a fault is not active. -/
abbrev FaultTcbs (σ : State Unit) : Prop := TI ftQ σ

/-- l4v `fault_tcb_states`: Inactive, BlockedOnSend or BlockedOnReply. -/
def faultTcbSt : ThreadState → Prop
  | .inactive => True
  | .blockedOnSend _ _ => True
  | .blockedOnReply _ => True
  | _ => False

/-- l4v's form: a thread with a fault is Inactive, BlockedOnSend or BlockedOnReply. -/
def ftsQ (x : Tcb) : Prop := x.tcbFault ≠ none → faultTcbSt x.tcbState

/-- l4v `fault_tcbs_valid_states`. -/
abbrev FaultTcbsS (σ : State Unit) : Prop := TI ftsQ σ

theorem FaultTcbsS.weak {σ : State Unit} (h : FaultTcbsS σ) : FaultTcbs σ := by
  intro p x hp hf ha
  have := h p x hp hf
  revert this ha
  cases x.tcbState <;> simp [faultTcbSt, activeSt]

/-- An active current thread has no fault (`JEntryAt.cnf`'s form). -/
theorem FaultTcbs.ct {σ : State Unit} (h : FaultTcbs σ) {x : Tcb}
    (hx : σ.kheap σ.curThread = some (.tcb x)) (ha : activeSt x.tcbState) : x.tcbFault = none := by
  by_contra hf
  exact h _ x hx hf ha

/-- **FaultTcbsS at boot** (invA (d)). -/
theorem boot_faultTcbsS : FaultTcbsS (initASt (Z := Unit)) := by
  intro p x hp
  simp only [initASt, initKheap, Function.update_apply] at hp
  split_ifs at hp <;> (try cases hp) <;> (try (intro hf; exact absurd rfl hf))
  all_goals (split_ifs at hp <;> cases hp)

/-- **FaultTcbs at boot** (invA (d)). -/
theorem boot_faultTcbs : FaultTcbs (initASt (Z := Unit)) := boot_faultTcbsS.weak

end

end Fl4Proofs.P3.SInv
