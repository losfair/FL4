/-
P3 (DESIGN.md §9): **which spec invocations can be preempted** (spec side
only; KENTRY-PLAN kp9).

* `NoErrE m`: no outcome of `m` is an error. Kept by `liftE`, `pure`, bind.
* `PreInv inv`: the invocations whose `perform_invocation` contains a
  preemption point: Untyped retype (the reset), CNode Revoke and Delete,
  TCB `ThreadControlCaps` and `ThreadControlSched` with a fault handler (the
  installs' `cap_delete`).
* `perform_noErr`: every other invocation's `fl4PerformInvocation` never
  returns `.error ()` (l4v: only `cap_revoke`, `cap_delete`, `reset_untyped`
  call `preemption_point`).
* `dec_noPre`: a cap other than a CNode, Untyped or Thread cap decodes to no
  `PreInv` invocation.
* `ErrRel.not_preempted`: `Preempted` is related to no spec syscall error.
-/
import Fl4Proofs.P3.DecodeTop
import Fl4Proofs.P3.HandleTopX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

namespace NoPre
open Fl4Spec

/-- No outcome of `m` is an error. -/
def NoErrE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ s y, y ∈ (m.run s).1 → ∀ e, y.1 ≠ .error e

theorem noErr_liftE {ε α : Type} (m : NonDet (State Unit) α) : NoErrE (NonDetE.liftE (ε := ε) m) := by
  intro s y hy e he
  unfold NonDetE.liftE at hy
  rw [ExceptT.run_lift] at hy
  obtain ⟨x, -, hx⟩ := hy
  rw [show y = (.ok x.1, x.2) from hx] at he
  cases he

theorem noErr_pure {ε α : Type} (a : α) : NoErrE (pure a : NonDetE (State Unit) ε α) := by
  intro s y hy e he
  rw [show y = (.ok a, s) from hy] at he
  cases he

theorem noErr_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    (hm : NoErrE m) (hf : ∀ a, NoErrE (f a)) : NoErrE (m >>= f) := by
  intro s y hy e he
  change y ∈ (NonDet.bind (ExceptT.run m) _ s).1 at hy
  obtain ⟨⟨r, s1⟩, hr, hy⟩ := hy
  cases r with
  | error e' => exact hm s _ hr e' rfl
  | ok a => exact hf a s1 y hy e he

/-- **The invocations with a preemption point** (module docstring). -/
def PreInv : Fl4Invocation → Prop
  | .invokeUntyped _ => True
  | .invokeCNode (.revokeCall _) => True
  | .invokeCNode (.deleteCall _) => True
  | .invokeTCB (.threadControlCaps ..) => True
  | .invokeTCB (.threadControlSched _ _ (some _) ..) => True
  | _ => False

theorem noErr_tcb (i : TcbInvocation) (hi : ¬ PreInv (.invokeTCB i)) : NoErrE (invokeTcb (Z := Unit) i) := by
  cases i with
  | threadControlCaps => exact (hi trivial).elim
  | threadControlSched t sl fh mcp pr sc =>
    cases fh with
    | some _ => exact (hi trivial).elim
    | none =>
      simp only [invokeTcb, installTcbCap]
      refine noErr_bind (noErr_pure _) fun _ => noErr_bind (noErr_liftE _) fun _ =>
        noErr_bind (noErr_liftE _) fun _ => noErr_bind (noErr_liftE _) fun _ => noErr_pure _
  | notificationControl t n => cases n <;> exact noErr_liftE _
  | _ => exact noErr_liftE _

/-- **Only `PreInv` invocations can be preempted** (module docstring). -/
theorem perform_noErr (b c d : Bool) (inv : Fl4Invocation) (h : ¬ PreInv inv) :
    NoErrE (fl4PerformInvocation (Z := Unit) b c d inv) := by
  cases inv with
  | invokeUntyped => exact (h trivial).elim
  | invokeTCB i => exact noErr_tcb i h
  | invokeFl4TCB i =>
    cases i <;> simp only [fl4PerformInvocation, invokeFl4Tcb, NonDetE.returnOk] <;>
      first | exact noErr_liftE _ | exact noErr_pure _ | (split <;> first | exact noErr_liftE _ | exact noErr_pure _)
  | invokeCNode i =>
    cases i with
    | revokeCall => exact (h trivial).elim
    | deleteCall => exact (h trivial).elim
    | cancelBadgedSendsCall cp =>
      simp only [fl4PerformInvocation, invokeCnode, NonDetE.returnOk]
      refine noErr_bind ?_ fun _ => noErr_pure _
      cases cp <;> first | exact noErr_liftE _ | skip
    | _ =>
      simp only [fl4PerformInvocation, invokeCnode, withoutPreemption, NonDetE.returnOk]
      exact noErr_bind (noErr_liftE _) fun _ => noErr_pure _
  | invokeIRQControl i =>
    simp only [fl4PerformInvocation, NonDetE.returnOk]
    refine noErr_bind ?_ fun _ => noErr_pure _
    cases i with
    | spec j =>
      cases j with
      | irqControl => exact noErr_liftE _
      | archIRQControl k => cases k <;> exact noErr_liftE _
    | ioapicRemapped => exact noErr_liftE _
  | invokeArchObject i =>
    cases i <;> first | exact noErr_liftE _ | skip
  | _ =>
    simp only [fl4PerformInvocation, withoutPreemption, NonDetE.returnOk] <;>
      first | exact noErr_liftE _ | exact noErr_bind (noErr_liftE _) fun _ => noErr_pure _

/-- Every `ok` outcome of `m` satisfies `P`. -/
def OkP {ε α : Type} (P : α → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ s y, y ∈ (m.run s).1 → ∀ a, y.1 = .ok a → P a

theorem okP_pure {ε α : Type} {P : α → Prop} {a : α} (h : P a) : OkP P (pure a : NonDetE (State Unit) ε α) := by
  intro s y hy a' e
  rw [show y = (.ok a, s) from hy] at e
  cases e; exact h

theorem okP_throw {ε α : Type} {P : α → Prop} {e : ε} : OkP P (throw e : NonDetE (State Unit) ε α) := by
  intro s y hy a' e'
  rw [show y = (.error e, s) from hy] at e'
  cases e'

theorem okP_liftME {ε α β : Type} {P : β → Prop} {f : α → β} {m : NonDetE (State Unit) ε α} (h : ∀ x, P (f x)) :
    OkP P (NonDetE.liftME f m) := by
  intro s y hy a e
  unfold NonDetE.liftME at hy
  change y ∈ (NonDet.bind (ExceptT.run m) _ s).1 at hy
  obtain ⟨⟨r, s1⟩, -, hy⟩ := hy
  cases r with
  | error e' => rw [show y = (.error e', s1) from hy] at e; cases e
  | ok x => rw [show y = (.ok (f x), s1) from hy] at e; cases e; exact h x

/-- **A cap other than a CNode, Untyped or Thread cap decodes to no
`PreInv` invocation** (module docstring). -/
theorem dec_noPre (fp : Bool) (lbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (hc : ∀ a b c, cap ≠ .cnodeCap a b c)
    (hu : ∀ a b c d, cap ≠ .untypedCap a b c d) (ht : ∀ a, cap ≠ .threadCap a) :
    OkP (fun inv => ¬ PreInv inv) (fl4DecodeInvocation (Z := Unit) fp lbl args ci sl cap ex buf) := by
  cases cap <;> simp only [fl4DecodeInvocation, NonDetE.returnOk, NonDetE.throwError] <;>
    first
    | exact (hc _ _ _ rfl).elim | exact (hu _ _ _ _ rfl).elim | exact (ht _ rfl).elim
    | exact okP_throw
    | exact okP_liftME fun _ => id
    | exact okP_pure fun h => h
    | (split <;> first | exact okP_throw | exact okP_pure id | exact okP_liftME fun _ => id)

theorem decOut_noPre {fp : Bool} {lbl : Data} {args : List Data} {ci : CapRef} {sl : CslotPtr} {cap : Cap}
    {ex : List (Cap × CslotPtr)} {buf : Option ObjRef} {σ : State Unit} {inv : Fl4Invocation}
    (hc : ∀ a b c, cap ≠ .cnodeCap a b c) (hu : ∀ a b c d, cap ≠ .untypedCap a b c d) (ht : ∀ a, cap ≠ .threadCap a)
    (h : DecOut (fl4DecodeInvocation (Z := Unit) fp lbl args ci sl cap ex buf) σ inv) : ¬ PreInv inv :=
  dec_noPre fp lbl args ci sl cap ex buf hc hu ht σ _ h.1 inv rfl

theorem okP_bind {ε α β : Type} {P : β → Prop} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    (hf : ∀ a, OkP P (f a)) : OkP P (m >>= f) := by
  intro s y hy b e
  change y ∈ (NonDet.bind (ExceptT.run m) _ s).1 at hy
  obtain ⟨⟨r, s1⟩, -, hy⟩ := hy
  cases r with
  | error e' => rw [show y = (.error e', s1) from hy] at e; cases e
  | ok a => exact hf a s1 y hy b e

theorem okP_liftME' {ε α β : Type} {Q : α → Prop} {P : β → Prop} {f : α → β} {m : NonDetE (State Unit) ε α}
    (hm : OkP Q m) (h : ∀ x, Q x → P (f x)) : OkP P (NonDetE.liftME f m) := by
  intro s y hy a e
  unfold NonDetE.liftME at hy
  change y ∈ (NonDet.bind (ExceptT.run m) _ s).1 at hy
  obtain ⟨⟨r, s1⟩, hr, hy⟩ := hy
  cases r with
  | error e' => rw [show y = (.error e', s1) from hy] at e; cases e
  | ok x => rw [show y = (.ok (f x), s1) from hy] at e; cases e; exact h x (hm s _ hr x rfl)

set_option maxHeartbeats 2000000 in
/-- **A CNode decode at a label other than Revoke and Delete** gives no
`PreInv` invocation. -/
theorem dec_cnode_noPre (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap)
    (hr : genInvocationType label ≠ .cnodeRevoke) (hd : genInvocationType label ≠ .cnodeDelete) :
    OkP (fun i => ¬ PreInv (.invokeCNode i)) (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation
  simp only [NonDetE.whenE, NonDetE.unlessE, NonDetE.returnOk, NonDetE.throwError]
  repeat' (first
    | exact okP_throw
    | exact okP_pure (fun h => h)
    | refine okP_bind fun _ => ?_
    | exact absurd ‹genInvocationType label = .cnodeRevoke› hr
    | exact absurd ‹genInvocationType label = .cnodeDelete› hd
    | split)

set_option maxHeartbeats 4000000 in
set_option linter.all false in
/-- **A TCB decode at a label other than the five installing ones** gives no
`PreInv` invocation (SetPriority and SetMCPriority decode to
`ThreadControlSched` without a fault handler). -/
theorem dec_tcb_noPre (label : Data) (args : List Data) (cap : Cap) (sl : CslotPtr) (excs : List (Cap × CslotPtr))
    (h1 : genInvocationType label ≠ .tcbConfigure) (h2 : genInvocationType label ≠ .tcbSetSchedParams)
    (h3 : genInvocationType label ≠ .tcbSetTimeoutEndpoint) (h4 : genInvocationType label ≠ .tcbSetIPCBuffer)
    (h5 : genInvocationType label ≠ .tcbSetSpace) :
    OkP (fun i => ¬ PreInv (.invokeTCB i)) (decodeTcbInvocation (Z := Unit) label args cap sl excs) := by
  delta decodeTcbInvocation
  generalize genInvocationType label = g at h1 h2 h3 h4 h5 ⊢
  cases g <;> dsimp only
  all_goals first
    | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 | exact absurd rfl h5
    | skip
  all_goals (try delta decodeReadRegisters); (try delta decodeWriteRegisters); (try delta decodeCopyRegisters)
  all_goals (try delta decodeSetPriority); (try delta decodeSetMcpriority); (try delta decodeBindNotification)
  all_goals (try delta decodeUnbindNotification); (try delta decodeSetTlsBase); (try delta decodeSetFlags)
  all_goals try simp only [NonDetE.whenE, NonDetE.unlessE, NonDetE.returnOk, NonDetE.throwError]
  all_goals repeat' (first
    | with_reducible exact okP_throw
    | (with_reducible refine okP_pure ?_); exact fun h => h
    | with_reducible refine okP_bind fun _ => ?_
    | split)

/-- **A Thread cap decode at a label other than the five installing ones**
gives no `PreInv` invocation. -/
theorem dec_thread_noPre (label : Data) (args : List Data) (cap : Cap) (sl : CslotPtr) (excs : List (Cap × CslotPtr))
    (buf : Option ObjRef)
    (h1 : genInvocationType label ≠ .tcbConfigure) (h2 : genInvocationType label ≠ .tcbSetSchedParams)
    (h3 : genInvocationType label ≠ .tcbSetTimeoutEndpoint) (h4 : genInvocationType label ≠ .tcbSetIPCBuffer)
    (h5 : genInvocationType label ≠ .tcbSetSpace) :
    OkP (fun i => ¬ PreInv i) (fl4DecodeTcbInvocation (Z := Unit) label args cap sl excs buf) := by
  unfold fl4DecodeTcbInvocation
  split
  · exact okP_liftME fun _ => fun h => h
  · split
    · exact okP_liftME fun _ => fun h => h
    · exact okP_liftME' (dec_tcb_noPre label args cap sl excs h1 h2 h3 h4 h5) fun _ h => h

end NoPre

theorem ErrRel.not_preempted {e' : Fl4Spec.SyscallError} : ¬ ErrRel .Preempted e' := by
  rintro (h | ⟨n, h, -⟩)
  · cases e' <;> exact h
  · cases h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **A `TopPostDMX` outcome is preempted only by a `PreInv` invocation**:
the error branch relates `Preempted` to no spec error, the invocation branch
has the spec's `.error ()`, which `perform_noErr` excludes. -/
theorem TopPostDMX.not_preempted {X : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S}
    {res : core.result.Result Unit error.Exc × S × A} (h : TopPostDMX (L := L) X σ blk call don m s res)
    (hnp : ∀ inv, DecOut m σ inv → ¬ NoPre.PreInv inv) : res.1 ≠ .Err .Preempted := by
  intro hr
  rcases h with ⟨e, h1, -, ⟨e', -, he⟩, -⟩ | ⟨inv, hd, σ1, -, y, hy, ⟨-, -, h3, -⟩, -⟩
  · rw [hr] at h1; cases h1; exact ErrRel.not_preempted he
  · rcases h3 with ⟨h3, -⟩ | ⟨-, h3⟩
    · rw [hr] at h3; cases h3
    · exact NoPre.perform_noErr blk call don inv (hnp inv hd) σ1 y hy () h3

end

end

end Fl4Proofs.P3
