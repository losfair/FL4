/-
P3 (DESIGN.md §9), invariant line G1 (rd8c): **`BindRel` from the decode to
the perform** (spec side only, outside the JAtZ cone; KENTRY-PLAN rd8b
handoff 2).

* `OkP σ P m`: every `.ok` outcome of `m` from `σ` satisfies `P` (combinators
  for steps that only read `σ`).
* `RdD σ inv`: an SC-to-TCB bind satisfies rd8b's `BindRel` at `σ`.
  **`okp_fl4DecodeRdD`**: every decode outcome from `σ` satisfies `RdD σ`
  (`decode_sched_context_bind` reads the SC, the TCB's SC, the thread state and
  `sc_released` at its start state and checks `sc_tcb = None`,
  `tcb_sched_context = None` and `¬ (ipc_queued_thread_state ∧ ¬ released)`;
  `BlkR` states are `ipc_queued`). sb2's `RNE` gives the released read.
* `bindRel_bk`: `BindRel` along the `BK` view (SpecInvRd8cV).
* **`bindRel_perform`**: a decoded bind satisfies `BindRel` at the perform
  (after `set_thread_state ct Restart`).
-/
import Fl4Proofs.P3.SpecInvRd8cV
import Fl4Proofs.P3.SpecInvSbX2
open Classical

namespace Fl4Proofs.P3.SInvR.B8c
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvB Fl4Proofs.P3.SInvE

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Pinned outcomes -/

def OkP {ε α : Type} (σ : State Unit) (P : α → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ a s, ((.ok a, s) : Except ε α × State Unit) ∈ (m.run σ).1 → P a

section OkPc
variable {ε α β : Type} {σ : State Unit}

theorem okp_of_okA {P : α → Prop} {m : NonDetE (State Unit) ε α} (h : OkA P m) : OkP σ P m :=
  fun a s hs => h σ a s hs

theorem okp_returnOk {P : α → Prop} {a : α} (h : P a) : OkP σ P (NonDetE.returnOk a : NonDetE (State Unit) ε α) :=
  okp_of_okA (okA_returnOk h)

theorem okp_throw {P : α → Prop} (e : ε) : OkP σ P (NonDetE.throwError e : NonDetE (State Unit) ε α) :=
  okp_of_okA (okA_throw e)

theorem okp_returnOk_bind {P : β → Prop} {a : α} {g : α → NonDetE (State Unit) ε β} (h : OkP σ P (g a)) :
    OkP σ P (NonDetE.returnOk a >>= g) := by
  intro c s hc
  rw [ExceptT.run_bind] at hc
  obtain ⟨z, hz, hc⟩ := hc
  obtain rfl := Set.mem_singleton_iff.1 hz
  exact h c s hc

theorem okp_throw_bind {P : β → Prop} (e : ε) {g : α → NonDetE (State Unit) ε β} :
    OkP σ P (NonDetE.throwError e >>= g) := by
  intro c s hc
  rw [ExceptT.run_bind] at hc
  obtain ⟨z, hz, hc⟩ := hc
  obtain rfl := Set.mem_singleton_iff.1 hz
  have e := Set.mem_singleton_iff.1 hc; simp at e

theorem okp_whenE_bind {P : β → Prop} {c : Prop} [Decidable c] {e : ε} {g : Unit → NonDetE (State Unit) ε β}
    (hg : ¬ c → OkP σ P (g ())) : OkP σ P (NonDetE.whenE c (NonDetE.throwError e) >>= g) := by
  unfold NonDetE.whenE
  by_cases hc : c
  · rw [if_pos hc]; exact okp_throw_bind e
  · rw [if_neg hc]; exact okp_returnOk_bind (hg hc)

theorem okp_liftE_bind {P : β → Prop} {Q : α → Prop} {m : NonDet (State Unit) α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ y ∈ (m σ).1, y.2 = σ ∧ Q y.1) (hg : ∀ a, Q a → OkP σ P (g a)) :
    OkP σ P (NonDetE.liftE m >>= g) := by
  intro b s hb
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hb
  · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz
    simp only [Except.ok.injEq] at ha
    obtain ⟨e2, hq⟩ := hm x hx
    rw [e2] at hy
    exact hg a (ha ▸ hq) b s hy
  · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz
    simp at he

theorem okp_ite {P : α → Prop} {c : Prop} [Decidable c] {m1 m2 : NonDetE (State Unit) ε α} (h1 : OkP σ P m1)
    (h2 : OkP σ P m2) : OkP σ P (if c then m1 else m2) := by
  split <;> assumption

theorem okp_liftME {P : β → Prop} {f : α → β} {m : NonDetE (State Unit) ε α} (h : OkP σ (fun a => P (f a)) m) :
    OkP σ P (NonDetE.liftME f m) := by
  unfold NonDetE.liftME
  intro b s hb
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, he⟩⟩ := SInvU.mem_bindE' hb
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    have e := Set.mem_singleton_iff.1 hy
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact h _ _ hz
  · simp at he

end OkPc

/-! ## The bind decode -/

/-- The decode's fact of an SC-to-TCB bind, at the decode's state. -/
def RdS (σ : State Unit) : SchedContextInvocation → Prop
  | .invokeSchedContextBind p (.threadCap t) => BindRel σ p t
  | _ => True

/-- **What the `Rdy` performs read from the decode**, at the decode's state. -/
def RdD (σ : State Unit) : Fl4Invocation → Prop
  | .invokeSchedContext iv => RdS σ iv
  | _ => True

theorem blkR_ipcQueued {ts : ThreadState} {f : Option Fault} (h : BlkR ts f) : ipcQueuedThreadState ts = true := by
  rcases h with ⟨_, rfl⟩ | ⟨_, _, rfl, _⟩ | ⟨_, _, _, rfl⟩ <;> rfl

theorem okp_decodeSchedContextBind (σ : State Unit) (hN : SInvB.RNE σ) (scPtr : ObjRef) (excaps : List Cap) :
    OkP σ (RdS σ) (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind
  refine okp_whenE_bind fun _ => okp_returnOk_bind ?_
  refine okp_liftE_bind (Q := fun sc => ∃ n, σ.kheap scPtr = some (.schedContext sc n))
    (fun y hy => SInvQ.cq5_mem_getSc hy) fun sc ⟨n, hsc⟩ => ?_
  (try dsimp only)
  split
  · rename_i tcbPtr heq
    refine okp_whenE_bind fun h1 => ?_
    refine okp_liftE_bind (Q := fun o => ∃ x, σ.kheap tcbPtr = some (.tcb x) ∧ o = x.tcbSchedContext)
      (fun y hy => ?_) fun o ⟨x, hx, ho⟩ => ?_
    · obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hy; exact ⟨rfl, x, hx, rfl⟩
    refine okp_whenE_bind fun h2 => ?_
    refine okp_liftE_bind (Q := fun st => st = x.tcbState) (fun y hy => ?_) fun st hst => ?_
    · obtain ⟨x', hx', rfl⟩ := SInvQ.q1_mem_threadGet hy; rw [hx] at hx'; cases hx'; exact ⟨rfl, rfl⟩
    refine okp_liftE_bind (Q := fun r => r = scReleased σ.curTime sc) (fun y hy => ?_) fun r hr => ?_
    · rw [Sched.getScReleased_eq hsc (fun ha => hN scPtr sc n hsc (Or.inr ha))] at hy
      obtain rfl := Set.mem_singleton_iff.1 hy; exact ⟨rfl, rfl⟩
    refine okp_whenE_bind fun h3 => okp_returnOk ?_
    rw [heq]
    show BindRel σ scPtr tcbPtr
    refine ⟨fun y n' hy => ?_, fun x' hx' => ?_⟩
    · rw [hsc] at hy; cases hy; exact not_not.1 h1
    · rw [hx] at hx'; cases hx'
      refine ⟨by rw [← ho]; exact not_not.1 h2, fun hb => ⟨sc, n, hsc, ?_⟩⟩
      have hq : ipcQueuedThreadState x.tcbState = true := blkR_ipcQueued hb
      subst hst; subst hr
      by_contra hn
      exact h3 ⟨hq, hn⟩
  · rename_i ntfnPtr bd rs heq
    rw [heq]
    refine okp_of_okA ?_
    okA_auto
  · exact okp_throw_bind _

theorem okp_decodeSchedContextInvocation (σ : State Unit) (hN : SInvB.RNE σ) (label : Data) (scPtr : ObjRef)
    (excaps : List Cap) : OkP σ (RdS σ) (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation
  split
  · exact okp_returnOk trivial
  · exact okp_decodeSchedContextBind σ hN scPtr excaps
  all_goals refine okp_of_okA ?_
  all_goals first
    | exact okA_throw _
    | (unfold decodeSchedContextUnbindObject; okA_auto)
    | (unfold decodeSchedContextYieldTo; okA_auto)
    | okA_auto

set_option maxHeartbeats 4000000 in
/-- **Every decoded invocation satisfies `RdD` of the decode's state.** -/
theorem okp_fl4DecodeRdD (σ : State Unit) (hN : SInvB.RNE σ) (fp : Bool) (label : Data) (args : List Data)
    (ci : CapRef) (sl : CslotPtr) (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkP σ (RdD σ) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | schedContextCap sc sz =>
    unfold fl4DecodeInvocation
    exact okp_ite (okp_throw _) (okp_liftME (okp_decodeSchedContextInvocation σ hN label sc _))
  | _ =>
    unfold fl4DecodeInvocation
    refine okp_of_okA ?_
    repeat' (first
      | exact okA_throw _ | exact okA_returnOk trivial
      | (exact okA_liftME (okA_triv fun _ => trivial))
      | (refine okA_ite ?_ ?_)
      | (unfold fl4DecodeTcbInvocation)
      | (dsimp only)
      | split)

/-! ## Along the view, to the perform -/

theorem scAt_iff {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat} :
    scAt σ p = some (y, n) ↔ σ.kheap p = some (.schedContext y n) := by
  unfold scAt
  constructor
  · intro h
    split at h
    · rename_i y' n' e; cases h; exact e
    · cases h
  · intro h; rw [h]

theorem tcbV_some {o : Option KernelObject} {a : ThreadState} {b : Option Fault} {c : Option ObjRef}
    (h : tcbV o = some (a, b, c)) :
    ∃ x, o = some (.tcb x) ∧ x.tcbState = a ∧ x.tcbFault = b ∧ x.tcbSchedContext = c := by
  rcases o with _ | o
  · simp [tcbV] at h
  · cases o <;> simp [tcbV] at h
    exact ⟨_, rfl, h.1, h.2.1, h.2.2⟩

theorem bindRel_bk {σ σ' : State Unit} {p t : ObjRef} (h : BKv σ' = BKv σ) (hB : BindRel σ p t) :
    BindRel σ' p t := by
  have h' := h
  unfold BKv at h'
  simp only [Prod.mk.injEq] at h'
  obtain ⟨hT, hS, hC⟩ := h'
  refine ⟨fun y n hy => hB.1 y n (scAt_iff.1 (by rw [← hS]; exact scAt_iff.2 hy)), fun x' hx' => ?_⟩
  have e := congrFun hT t
  try simp only at e
  rw [hx'] at e
  obtain ⟨x, hx, e1, e2, e3⟩ := tcbV_some e.symm
  obtain ⟨hn, hrel⟩ := hB.2 x hx
  refine ⟨by rw [← e3]; exact hn, fun hb => ?_⟩
  obtain ⟨y, n, hy, hr⟩ := hrel (by rw [e1, e2]; exact hb)
  exact ⟨y, n, scAt_iff.1 (by rw [hS]; exact scAt_iff.2 hy), by rw [hC]; exact hr⟩

/-- **A decoded SC-to-TCB bind satisfies `BindRel` at the perform** (after the shell's
`set_thread_state ct Restart`); `RNE` (sb2's `ScInv`) at the decode's state. -/
theorem bindRel_perform {σ : State Unit} (hN : SInvB.RNE σ) {fp : Bool} {label : Data} {args : List Data}
    {ci : CapRef} {sl : CslotPtr} {cap : Cap} {ex : List (Cap × CslotPtr)} {buf : Option ObjRef}
    {p t : ObjRef} {s : State Unit}
    (h : ((.ok (.invokeSchedContext (.invokeSchedContextBind p (.threadCap t))), s) :
        Except SyscallError Fl4Invocation × State Unit) ∈
      ((fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf).run σ).1)
    (c : ObjRef) {y : Unit × State Unit} (hy : y ∈ (setThreadState (Z := Unit) c .restart s).1) :
    BindRel y.2 p t := by
  have hD : BindRel σ p t := okp_fl4DecodeRdD σ hN fp label args ci sl cap ex buf _ s h
  have hV : BKv s = BKv σ := bk_fl4DecodeInvocation (V := BKv σ) fp label args ci sl cap ex buf σ rfl _ h
  exact bindRel_setThreadState (bindRel_bk hV hD) hy

end

end Fl4Proofs.P3.SInvR.B8c
