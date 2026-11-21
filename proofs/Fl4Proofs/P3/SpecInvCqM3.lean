/-
P3 (DESIGN.md §9), invariant line G1 (ctq15): **the decode facts the EB arms
take** (spec side only, outside the JAtZ cone; KENTRY-PLAN ctq13 "decode
facts", ctq12 handoff 6), each an `OkDAt` fact of `fl4DecodeInvocation` (the
form of SpecInvQDom's `okq_fl4Decode`):

* **`okd_fp`**: in the first phase (`fp = true`) the decoded invocation is an
  Endpoint / Notification / Reply / IRQ control / IRQ handler / Untyped / arch
  one (`FPArm`): thread, domain, SC, SchedControl and CNode caps are rejected.
  These arms keep `EB true` (or `EB k`); every other arm needs only `EB false`.
* **`okd_tcbP`**: a ThreadControlSched with an SC argument has a priority
  (`TcbP`: decode_set_sched_params is the only decode with an SC argument; the
  other two ThreadControlSched decodes pass `none`) — `eb_perfTcbSched`'s `hP`.
* **`okd_sc`** (`ScD`, at the decode's state): YieldTo's SC is bound to a
  thread other than ct (decode_sched_context_yield_to: `sc_tcb ≠ none`,
  `≠ some ct`; `YT`), and SC Bind's thread target has no SC
  (decode_sched_context_bind) — with ctq10's `ResSc`, `an_of_resSc` gives the
  bind arm's `AN t`.
* `ScD` is kept by every step keeping the current thread and sb2's binding
  frame (`scD_of_br`), e.g. the shell's `set_thread_state ct Restart`.
-/
import Fl4Proofs.P3.SpecInvCqM1
open Classical

namespace Fl4Proofs.P3.SInvQ.P15
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The facts -/

/-- The arms that may precede `handle_recv` in one entry. -/
def FPArm : Fl4Invocation → Prop
  | .invokeEndpoint .. => True
  | .invokeNotification .. => True
  | .invokeReply .. => True
  | .invokeIRQControl _ => True
  | .invokeIRQHandler _ => True
  | .invokeUntyped _ => True
  | .invokeArchObject _ => True
  | _ => False

/-- A ThreadControlSched with an SC argument has a priority. -/
def TcbP : Fl4Invocation → Prop
  | .invokeTCB (.threadControlSched _ _ _ _ p sc) => sc ≠ none → p ≠ none
  | _ => True

/-- The SC invocations' decode facts at a state. -/
def ScD (s : State Unit) : Fl4Invocation → Prop
  | .invokeSchedContext (.invokeSchedContextYieldTo sc) => YT s.curThread sc s.kheap
  | .invokeSchedContext (.invokeSchedContextBind _ c) =>
      ∀ t, c = .threadCap t → ∃ x, s.kheap t = some (.tcb x) ∧ x.tcbSchedContext = none
  | _ => True

/-! ## Combinators -/

section C
variable {ε α β : Type} {σ : State Unit}

theorem okdAt_triv {P : State Unit → α → Prop} {m : NonDetE (State Unit) ε α} (h : ∀ s a, P s a) :
    OkDAt σ P m := fun a s _ => h s a

/-- A lifted step, its outcomes. -/
theorem okdAt_liftE_bind_v {P : State Unit → β → Prop} {m : NonDet (State Unit) α} {g : α → NonDetE (State Unit) ε β}
    (hg : ∀ y ∈ (m σ).1, OkDAt y.2 P (g y.1)) : OkDAt σ P (NonDetE.liftE m >>= g) := by
  refine okdAt_bind fun a s h => ?_
  obtain ⟨x, hx, e⟩ := mem_liftE_inv' h
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact hg x hx

/-- A lifted read. -/
theorem okdAt_liftE_ro {P : State Unit → β → Prop} {m : NonDet (State Unit) α} {g : α → NonDetE (State Unit) ε β}
    (hro : ∀ σ0, IK (fun s => s = σ0) m) (hg : ∀ a, OkDAt σ P (g a)) : OkDAt σ P (NonDetE.liftE m >>= g) :=
  okdAt_liftE_bind_v fun y hy => by rw [hro σ σ rfl y hy]; exact hg _

end C

/-! ## The first phase -/

set_option maxHeartbeats 4000000 in
/-- **In the first phase the decoded invocation is an `FPArm` one.** -/
theorem okd_fp (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun _ inv => fp = true → FPArm inv) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases fp
  · exact okdAt_triv fun _ _ h => absurd h (by decide)
  unfold fl4DecodeInvocation
  split
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk (fun _ => trivial)
    | exact okdAt_liftME (fun _ _ _ _ => trivial)
    | (simp only [↓reduceIte])
    | (apply okdAt_ite))

/-! ## ThreadControlSched's priority -/

set_option maxHeartbeats 8000000 in
/-- **A decoded ThreadControlSched with an SC argument has a priority.** -/
theorem okd_tcbP (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun _ inv => TcbP inv) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try unfold fl4DecodeTcbInvocation
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk trivial
    | exact okdAt_liftME (fun _ _ _ => trivial)
    | (apply okdAt_ite)
    | (refine okdAt_liftME (g := Fl4Invocation.invokeTCB) ?_; unfold decodeTcbInvocation)
    | split)
  all_goals try unfold decodeReadRegisters
  all_goals try unfold decodeWriteRegisters
  all_goals try unfold decodeCopyRegisters
  all_goals try unfold decodeTcbConfigure
  all_goals try unfold decodeSetPriority
  all_goals try unfold decodeSetMcpriority
  all_goals try unfold decodeSetSchedParams
  all_goals try unfold decodeSetTimeoutEp
  all_goals try unfold decodeSetIpcBuffer
  all_goals try unfold decodeSetSpace
  all_goals try unfold decodeBindNotification
  all_goals try unfold decodeUnbindNotification
  all_goals try unfold decodeSetTlsBase
  all_goals try unfold decodeSetFlags
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk (by simp [TcbP])
    | exact okdAt_liftME (fun _ _ _ => by simp [TcbP])
    | (refine okdAt_bind fun _ _ _ => ?_)
    | (apply okdAt_ite)
    | split
    | (dsimp only))

/-! ## The SC invocations -/

theorem ro_getScObjRef (f : SchedContext → Option ObjRef) (p : ObjRef) (σ0 : State Unit) :
    IK (fun s => s = σ0) (getScObjRef (Z := Unit) f p) := by
  unfold getScObjRef getSchedContext; repeat' (first | ik_step0 | ik_unfold)

theorem ro_threadGet {β : Type} (f : Tcb → β) (t : ObjRef) (σ0 : State Unit) :
    IK (fun s => s = σ0) (threadGet (Z := Unit) f t) := by
  unfold threadGet; repeat' (first | ik_step0 | ik_unfold)

theorem ro_getThreadState (t : ObjRef) (σ0 : State Unit) : IK (fun s => s = σ0) (getThreadState (Z := Unit) t) := by
  unfold getThreadState; exact ro_threadGet _ _ _

theorem ro_getScReleased (p : ObjRef) (σ0 : State Unit) : IK (fun s => s = σ0) (getScReleased (Z := Unit) p) := by
  unfold getScReleased; repeat' (first | ik_step0 | ik_unfold)

theorem ro_getSchedContext (p : ObjRef) (σ0 : State Unit) : IK (fun s => s = σ0) (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext; repeat' (first | ik_step0 | ik_unfold)

/-- YieldTo: the SC's thread is not ct. -/
theorem okd_yieldTo (sc : ObjRef) (σ : State Unit) :
    OkDAt σ (fun s iv => ScD s (.invokeSchedContext iv)) (decodeSchedContextYieldTo (Z := Unit) sc) := by
  unfold decodeSchedContextYieldTo
  refine okdAt_liftE_bind_v fun y hy => ?_
  obtain ⟨ey, scv, n, hk, hv⟩ := cq5_mem_getScObjRef hy
  rw [ey]
  refine okdAt_whenE_bind _ _ fun _ => okdAt_gets_bind (okdAt_whenE_bind _ _ fun hne => ?_)
  refine okdAt_liftE_ro (ro_threadGet _ _) fun _ => okdAt_liftE_ro (ro_threadGet _ _) fun _ =>
    okdAt_whenE_bind _ _ fun _ => okdAt_liftE_ro (ro_threadGet _ _) fun _ =>
      okdAt_whenE_bind _ _ fun _ => okdAt_returnOk ?_
  intro y' n' u hk' hu e
  rw [hk] at hk'; cases hk'
  exact hne (by rw [hv, hu, e])

/-- SC Bind: a thread target has no SC. -/
theorem okd_scBind (sc : ObjRef) (ex : List Cap) (σ : State Unit) :
    OkDAt σ (fun s iv => ScD s (.invokeSchedContext iv)) (decodeSchedContextBind (Z := Unit) sc ex) := by
  unfold decodeSchedContextBind
  refine okdAt_whenE_bind _ _ fun _ => okdAt_returnOk_bind (okdAt_liftE_ro (ro_getSchedContext _) fun scv => ?_)
  split
  · rename_i t heq
    refine okdAt_whenE_bind _ _ fun _ => ?_
    unfold getTcbObjRef
    refine okdAt_liftE_bind_v fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hy
    refine okdAt_whenE_bind _ _ fun hn => okdAt_liftE_ro (ro_getThreadState _) fun _ =>
      okdAt_liftE_ro (ro_getScReleased _) fun _ => okdAt_whenE_bind _ _ fun _ => okdAt_returnOk ?_
    intro t' e
    rw [heq] at e; cases e
    exact ⟨x, hx, by simpa using hn⟩
  · rename_i heq
    repeat' (first | (refine okdAt_returnOk ?_) | (refine okdAt_bind fun _ _ _ => ?_) | (dsimp only))
    all_goals (intro t' e; rw [heq] at e; cases e)
  · first
      | exact okdAt_throw _
      | exact okdAt_bind fun _ _ h => by have e := Set.mem_singleton_iff.1 h; simp at e

/-- **The SC decode facts.** -/
theorem okd_scInv (label : Data) (sc : ObjRef) (ex : List Cap) (σ : State Unit) :
    OkDAt σ (fun s iv => ScD s (.invokeSchedContext iv)) (decodeSchedContextInvocation (Z := Unit) label sc ex) := by
  unfold decodeSchedContextInvocation
  split
  all_goals first
    | exact okd_scBind sc ex σ
    | exact okd_yieldTo sc σ
    | ((try unfold decodeSchedContextUnbindObject)
       repeat' (first
        | exact okdAt_throw _
        | exact okdAt_returnOk trivial
        | (refine okdAt_bind fun _ _ _ => ?_)
        | split
        | (dsimp only)))

set_option maxHeartbeats 4000000 in
/-- **The SC decode facts of every decoded invocation.** -/
theorem okd_sc (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun s inv => ScD s inv) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try unfold fl4DecodeTcbInvocation
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk trivial
    | exact okdAt_liftME (fun _ _ _ => trivial)
    | exact okdAt_liftME (okd_scInv _ _ _ σ)
    | (apply okdAt_ite)
    | split)

/-- `ScD` along a step keeping the current thread and the binding frame. -/
theorem scD_of_br {s s' : State Unit} {inv : Fl4Invocation} (h : ScD s inv) (hc : s'.curThread = s.curThread)
    (hb : SInvB.BR s.kheap s'.kheap) : ScD s' inv := by
  cases inv with
  | invokeSchedContext iv =>
    cases iv with
    | invokeSchedContextYieldTo sc =>
      show YT s'.curThread sc s'.kheap
      rw [hc]; exact yt_of_br h hb
    | invokeSchedContextBind p c =>
      intro t e
      obtain ⟨x, hx, hn⟩ := (h : ∀ t, c = .threadCap t → ∃ x, s.kheap t = some (.tcb x) ∧ x.tcbSchedContext = none) t e
      obtain ⟨x', hx', e'⟩ := hb.tcb t x hx
      exact ⟨x', hx', e'.trans hn⟩
    | _ => trivial
  | _ => trivial

end

end Fl4Proofs.P3.SInvQ.P15
