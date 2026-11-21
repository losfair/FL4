/-
P3 (DESIGN.md §9), invariant line G1 (invC): **the domain-list frame of the
kernel entry's pieces** (SpecInvDomF's `DL`, over SpecInvDomG's leaves).

* The recursive functions: `rec_del` and `cap_revoke` (the least fixed point,
  `lfp_le_prefixed'`); FL4's TCB timers `fl4Awaken` (a reflexive transitive
  closure of `send_signal` outcomes).
* `fl4SyscallFaultIP`, `updateTimeStamp`, `checkBudgetRestart`, the receive,
  the yield, the fault handler, the preemption path, the invocation's front and
  decode (`dle_fl4Decode`), every perform but the Domain invocation's
  (`dle_fl4Perform`), `activateThread`, the non-syscall events
  (`dle_handleEvent_other`).
-/
import Fl4Proofs.P3.SpecInvDomG
open Classical

namespace Fl4Proofs.P3.SInvDom
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000



/-- FL4's TCB timers keep the domain list (their outcomes are `send_signal`
outcomes and `reprogram_timer` writes). -/
theorem dl_fl4Awaken : DL (fl4Awaken (Z := Unit)) := by
  intro σ x hx
  obtain ⟨u, s'⟩ := x
  have h : fl4TimerFires σ s' := hx
  show dlV s' = dlV σ
  clear hx
  induction h with
  | refl => rfl
  | tail _ h2 ih =>
    obtain ⟨σ1, h1, rfl⟩ := h2
    rw [← ih]
    rcases h1 with rfl | ⟨n, b, hs⟩
    · rfl
    · have e := dl_sendSignal' n b _ ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
      exact e
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_fl4Awaken)

/-- `whenE` with its decidability instance unified (not synthesized). -/
theorem dle_whenE' {ε : Type} (P : Prop) (inst : Decidable P) {m : NonDetE (State Unit) ε Unit} (h : DLE m) :
    DLE (@NonDetE.whenE _ _ P inst m) := by
  unfold NonDetE.whenE; split
  · exact h
  · exact dke_pure _
macro_rules | `(tactic| dl_leaf) => `(tactic| refine dle_whenE' _ _ ?_)

/-! ## The kernel entry's pieces -/

set_option maxHeartbeats 4000000 in
theorem dl_setThreadState (t : ObjRef) (ts : ThreadState) : DL (setThreadState (Z := Unit) t ts) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setThreadState _ _)

set_option maxHeartbeats 4000000 in
theorem dl_rescheduleRequired : DL (rescheduleRequired (Z := Unit)) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_rescheduleRequired)

set_option maxHeartbeats 4000000 in
theorem dl_fl4SyscallFaultIP (t : ObjRef) : DL (fl4SyscallFaultIP (Z := Unit) t) := by
  dl_auto

set_option maxHeartbeats 4000000 in
theorem dl_updateTimeStamp : DL (updateTimeStamp (Z := Unit)) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_updateTimeStamp)

set_option maxHeartbeats 4000000 in
theorem dl_checkBudgetRestart : DL (checkBudgetRestart (Z := Unit)) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_checkBudgetRestart)

set_option maxHeartbeats 4000000 in
theorem dl_handleFault (t : ObjRef) (f : Fault) : DL (handleFault (Z := Unit) t f) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_handleFault _ _)

set_option maxHeartbeats 4000000 in
theorem dl_handleRecv (b c : Bool) : DL (handleRecv (Z := Unit) b c) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_handleRecv _ _)

set_option maxHeartbeats 4000000 in
theorem dl_handleYield : DL (handleYield (Z := Unit)) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_handleYield)

set_option maxHeartbeats 4000000 in
theorem dl_preemptionPath : DL (preemptionPath (Z := Unit)) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_preemptionPath)

set_option maxHeartbeats 4000000 in
theorem dl_activateThread : DL (activateThread (Z := Unit)) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_activateThread)

set_option maxHeartbeats 4000000 in
theorem dl_getCapReg (r : Register) : DL (getCapReg (Z := Unit) r) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getCapReg _)

set_option maxHeartbeats 4000000 in
theorem dl_getMessageInfo (t : ObjRef) : DL (getMessageInfo (Z := Unit) t) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getMessageInfo _)

set_option maxHeartbeats 4000000 in
theorem dle_lookupCapAndSlot (t : ObjRef) (c : CapRef) : DLE (lookupCapAndSlot (Z := Unit) t c) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_lookupCapAndSlot _ _)

set_option maxHeartbeats 4000000 in
theorem dl_lookupIpcBuffer (b : Bool) (t : ObjRef) : DL (lookupIpcBuffer (Z := Unit) b t) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lookupIpcBuffer _ _)

set_option maxHeartbeats 4000000 in
theorem dle_lookupExtraCaps (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    DLE (lookupExtraCaps (Z := Unit) t b mi) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_lookupExtraCaps _ _ _)

set_option maxHeartbeats 4000000 in
theorem dl_getMrs (t : ObjRef) (b : Option ObjRef) (mi : MessageInfo) : DL (getMrs (Z := Unit) t b mi) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getMrs _ _ _)

set_option maxHeartbeats 4000000 in
theorem dl_replyFromKernel (t : ObjRef) (x : Data × List Data) : DL (replyFromKernel (Z := Unit) t x) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_replyFromKernel _ _)

set_option maxHeartbeats 4000000 in
theorem dl_fl4ReplyFromKernelError (r : Bool) (t : ObjRef) (x : Data × List Data) :
    DL (fl4ReplyFromKernelError (Z := Unit) r t x) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_fl4ReplyFromKernelError _ _ _)

set_option maxHeartbeats 4000000 in
theorem dl_getThreadState (t : ObjRef) : DL (getThreadState (Z := Unit) t) := by
  dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getThreadState _)

set_option maxHeartbeats 8000000 in
theorem dle_fl4Decode (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    DLE (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals dl_auto
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_fl4Decode _ _ _ _ _ _ _ _)

set_option maxHeartbeats 8000000 in
/-- Every perform but the Domain invocation's keeps the domain list. -/
theorem dle_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (h : ∀ d, inv ≠ .invokeDomain d) :
    DLE (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv with
  | invokeDomain d => exact absurd rfl (h d)
  | _ => simp only [fl4PerformInvocation]; dl_auto

set_option maxHeartbeats 8000000 in
/-- The non-syscall events keep the domain list. -/
theorem dle_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    DLE (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; dl_auto

end

end Fl4Proofs.P3.SInvDom
