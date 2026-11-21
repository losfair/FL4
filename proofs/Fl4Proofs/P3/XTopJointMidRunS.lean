/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch12 (1)): **`JMidRunHyp` from
the three perform cases sch11 left** (spec side only).

* `nV σ`: the notification view of the heap (the queue of every notification);
  `fV ct σ := (ctV ct σ, nV σ)`, `FV ct m := FK (fV ct) m`. `CtRs ct` and
  `NQ ct` read only `fV ct`. The front of the invocation (`getMessageInfo`,
  the cap / buffer / extra-cap lookups, `getMrs`, the first-phase decode)
  keeps `fV` (`fv_getMessageInfo`, `fve_midF`, `fve_midE`): they read
  objects and write only TCBs through `asUser` (by `set_object`'s type
  assertion a TCB stays a TCB, so no notification changes).
* `okAll_decodeFirst`: the first-phase decode yields only `FirstInv`
  invocations (no TCB/Domain/SchedContext/SchedControl/CNode invocation; l4v
  `decode_invocation_safe_invocation`).
* `perf_first`: the perform of every `FirstInv` invocation but `PerfW` keeps
  `CtRs` from `CtRs ∧ NQ` (endpoint: `pr_sendIpc` non-blocking non-calling;
  notification: `pr_sendSignal`; reply: `pr_doReplyTransfer`; IRQ control,
  IRQ ack and the arch invocations but ASID control by `KF`).
* `JMidPerfHyp` [W]: the `PerfW` cases (Untyped, IRQ handler set / clear, ASID
  control) keep `CtRs`, AT THE STATES WHERE THEIR PERFORM STARTS ON A RUN OF THE
  INVOCATION FROM THE ENTRY STATE (`MidPerfAt`), not for every state.
* `jMidRunHyp_of`: `JMidPerfHyp → JMidRunHyp`.
-/
import Fl4Proofs.P3.XTopJointMidRunP
import Fl4Proofs.P3.XTopJointMidRun
import Fl4Proofs.P3.PerformNil
import Fl4Proofs.P3.ScCharge7
open Classical

namespace Fl4Proofs.P3.MidRun
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-! ## Monad helpers -/

theorem mem_liftE_inv' {σ ε α : Type} {m : NonDet σ α} {s : σ} {y : Except ε α × σ}
    (h : y ∈ ((NonDetE.liftE (ε := ε) m).run s).1) : ∃ x ∈ (m s).1, y = (.ok x.1, x.2) := by
  unfold NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨x, hx, Set.mem_singleton_iff.1 hy⟩

theorem mem_bindE_inv' {σ ε α β : Type} {m : NonDetE σ ε α} {f : α → NonDetE σ ε β} {s : σ}
    {x : Except ε β × σ} (hx : x ∈ ((m >>= f).run s).1) :
    ∃ z ∈ (m.run s).1, (∃ a, z.1 = .ok a ∧ x ∈ ((f a).run z.2).1) ∨ (∃ e, z.1 = .error e ∧ x = (.error e, z.2)) := by
  rw [ExceptT.run_bind] at hx
  obtain ⟨z, hz, hxz⟩ := hx
  refine ⟨z, hz, ?_⟩
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok a => exact Or.inl ⟨a, rfl, hxz⟩
  | error e => exact Or.inr ⟨e, rfl, Set.mem_singleton_iff.1 hxz⟩

theorem post_bindE {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    {s : State Unit} {R Q : State Unit → Prop}
    (hm : ∀ z ∈ (m.run s).1, R z.2) (hRQ : ∀ s, R s → Q s)
    (hf : ∀ a s', (.ok a, s') ∈ (m.run s).1 → ∀ y ∈ ((f a).run s').1, Q y.2) :
    ∀ y ∈ ((m >>= f).run s).1, Q y.2 := by
  intro y hy
  obtain ⟨z, hz, ⟨a, ha, hy'⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
  · obtain ⟨r, s'⟩ := z
    simp only at ha; subst ha
    exact hf a s' hz y hy'
  · exact hRQ _ (hm z hz)

theorem post_liftE {ε α : Type} {m : NonDet (State Unit) α} {s : State Unit} {Q : State Unit → Prop}
    (h : ∀ x ∈ (m s).1, Q x.2) : ∀ y ∈ ((NonDetE.liftE (ε := ε) m).run s).1, Q y.2 := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_liftE_inv' hy
  exact h x hx

/-- **The spec's `syscall` shell, pointwise**: every outcome from `σ` is `Q`,
given the invariant `I` across the fault and error phases, the handlers
ending in `Q`, and the final phase ending in `Q` from every state it starts
in on a run from `σ`. -/
theorem syscall_post {α β γ : Type} {mF : FMonad Unit α} {hF : Fault → SMonad Unit γ}
    {mE : α → SEMonad Unit β} {hE : SyscallError → SMonad Unit γ} {mFin : β → PMonad Unit γ}
    {σ : State Unit} {I Q : State Unit → Prop}
    (h1 : ∀ w ∈ ((ExceptT.run mF) σ).1, I w.2)
    (h2 : ∀ f s, I s → ∀ v ∈ (hF f s).1, Q v.2)
    (h3 : ∀ a s, (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → ∀ w ∈ ((ExceptT.run (mE a)) s).1, I w.2)
    (h4 : ∀ e s, I s → ∀ v ∈ (hE e s).1, Q v.2)
    (h5 : ∀ a s b s', (.ok a, s) ∈ ((ExceptT.run mF) σ).1 → (.ok b, s') ∈ ((ExceptT.run (mE a)) s).1 →
      I s' → ∀ y ∈ ((mFin b).run s').1, Q y.2) :
    ∀ y ∈ ((syscall mF hF mE hE mFin).run σ).1, Q y.2 := by
  intro y hy
  unfold syscall withoutPreemption at hy
  obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE_inv' hy
  · obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hz
    simp only [Except.ok.injEq] at hr
    subst hr
    obtain ⟨r, s⟩ := w
    cases r with
    | error f =>
      obtain ⟨v, hv, rfl⟩ := mem_liftE_inv' hy
      exact h2 f s (h1 _ hw) v hv
    | ok a =>
      obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE_inv' hy
      · obtain ⟨w, hw', rfl⟩ := mem_liftE_inv' hz
        simp only [Except.ok.injEq] at hr
        subst hr
        obtain ⟨r, s'⟩ := w
        cases r with
        | error e =>
          obtain ⟨v, hv, rfl⟩ := mem_liftE_inv' hy
          exact h4 e s' (h3 a s hw _ hw') v hv
        | ok b => exact h5 a s b s' hw hw' (h3 a s hw _ hw') y hy
      · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz
        cases he
  · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz
    cases he

/-! ## The notification view -/

/-- The queue state of the notification at every reference. -/
def nV (σ : State Unit) (p : ObjRef) : Option Ntfn :=
  match σ.kheap p with
  | some (.notification n) => some n.ntfnObj
  | _ => none

/-- The current thread, `ct`'s state and fault, and every notification's queue. -/
def fV (ct : ObjRef) (σ : State Unit) : (ObjRef × Option (ThreadState × Option Fault)) × (ObjRef → Option Ntfn) :=
  (ctV ct σ, nV σ)

abbrev FV (ct : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := FK (fV ct) m

abbrev FVE (ct : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE (fV ct) m

theorem NQ.of_nV {ct : ObjRef} {σ σ' : State Unit} (e : nV σ' = nV σ) (h : NQ ct σ) : NQ ct σ' := by
  intro p n q hp hq
  have e2 := congrFun e p
  rcases hk : σ.kheap p with _ | k
  · simp [nV, hp, hk] at e2
  · cases k <;> simp [nV, hp, hk] at e2
    first
      | exact h p _ q hk (by rw [← e2]; exact hq)
      | exact h p _ q hk (by rw [e2]; exact hq)

/-- `CtRs ∧ NQ` is kept by every `fV`-frame. -/
theorem fv_I {ct : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : FV ct m) {σ : State Unit}
    (hI : CtRs ct σ ∧ NQ ct σ) : ∀ x ∈ (m σ).1, CtRs ct x.2 ∧ NQ ct x.2 := by
  intro x hx
  have e := h σ x hx
  unfold fV at e
  simp only [Prod.mk.injEq] at e
  exact ⟨CtRs.of_ctV e.1 hI.1, NQ.of_nV e.2 hI.2⟩

theorem fk_pair {β γ : Type} {f : State Unit → β} {g : State Unit → γ} {α : Type} {m : NonDet (State Unit) α}
    (h1 : FK f m) (h2 : FK g m) : FK (fun σ => (f σ, g σ)) m :=
  fun σ x hx => by simp only [h1 σ x hx, h2 σ x hx]

theorem nv_setObject_tcb (p : ObjRef) (y : Tcb) : FK nV (setObject (Z := Unit) p (.tcb y)) := by
  intro σ x hx
  obtain ⟨⟨k, hk, hA⟩, e⟩ := setObject_out hx
  obtain ⟨y', rfl⟩ := aType_eq_tcb (hA.trans (by simp [aType]))
  rw [e]
  funext q
  unfold nV
  simp only [Function.update_apply]
  by_cases hq : q = p
  · subst hq; simp [hk]
  · simp [hq]

section
variable {ct : ObjRef}

theorem nv_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : FK nV (asUser (Z := Unit) t u) := by
  unfold asUser
  repeat' (first | exact nv_setObject_tcb _ _ | dk_step0)

theorem fv_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : FV ct (asUser (Z := Unit) t u) :=
  fk_pair (kf_asUser t u) (nv_asUser t u)

theorem fv_doMachineOp {α : Type} (mop : NonDet MachineState α) : FV ct (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)

theorem fv_doExtendedOp (eop : DetExtMonad Unit) : FV ct (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)

theorem fv_getCap (sl : CslotPtr) : FV ct (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; dsimp only
  repeat' dk_step0

theorem fve_rab (p : Cap × CapRef) : FVE ct (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (fv_getCap _)) fun nc => ?_
        split
        · exact fve_rab _
        · exact dke_returnOk _
  · exact dke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega

end

open Lean Meta Elab Tactic in
/-- Unfold the spec function at the head of an `FK`/`FKE` goal. -/
elab "fv_unfold" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let args := t.getAppArgs
  if args.size == 0 then throwError "fv_unfold: no arguments"
  let m := args.back!
  let m := if m.isAppOf ``ExceptT.run then m.getAppArgs.back! else m
  match m.getAppFn with
  | .const n _ =>
    if (`Fl4Spec).isPrefixOf n && !(`Fl4Spec.NonDet).isPrefixOf n && !(`Fl4Spec.NonDetE).isPrefixOf n then
      evalTactic (← `(tactic| unfold $(mkIdent n):ident))
    else throwError "fv_unfold: {n} is not a spec function"
  | _ => throwError "fv_unfold: no head constant"

/-- An `FV` lemma of a spec function. -/
syntax "fv_leaf" : tactic
macro_rules | `(tactic| fv_leaf) => `(tactic| fail "no fv_leaf")
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fv_doMachineOp _)
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fv_doExtendedOp _)
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fv_asUser _ _)
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fv_getCap _)
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_rab _)

macro "fv_auto" : tactic => `(tactic| repeat' (first | fv_leaf | dk_step0 | fv_unfold))

/-! ## The front of the invocation -/

section
variable {ct : ObjRef}

set_option maxRecDepth 20000

theorem fve_lookupCapAndSlot (t : ObjRef) (c : CapRef) : FVE ct (lookupCapAndSlot (Z := Unit) t c) := by
  fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_lookupCapAndSlot _ _)

theorem fv_lookupIpcBuffer (b : Bool) (t : ObjRef) : FV ct (lookupIpcBuffer (Z := Unit) b t) := by
  fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fv_lookupIpcBuffer _ _)

theorem fve_lookupExtraCaps (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    FVE ct (lookupExtraCaps (Z := Unit) t b mi) := by
  fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_lookupExtraCaps _ _ _)

theorem fv_getMrs (t : ObjRef) (b : Option ObjRef) (mi : MessageInfo) : FV ct (getMrs (Z := Unit) t b mi) := by
  fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fv_getMrs _ _ _)

theorem fv_getMessageInfo (t : ObjRef) : FV ct (getMessageInfo (Z := Unit) t) := by
  fv_auto

theorem fve_decodeIrqControl (r : Bool) (label : Data) (args : List Data) (sl : CslotPtr) (ex : List Cap) :
    FVE ct (decodeFl4IrqControl (Z := Unit) r label args sl ex) := by
  fv_auto

theorem fve_decodeIrqHandler (label : Data) (irq : Irq) (ex : List (Cap × CslotPtr)) :
    FVE ct (decodeIrqHandlerInvocation (Z := Unit) label irq ex) := by
  fv_auto

theorem fve_decodeUntyped (label : Data) (args : List Data) (sl : CslotPtr) (cap : Cap) (ex : List Cap) :
    FVE ct (fl4DecodeUntypedInvocation (Z := Unit) label args sl cap ex) := by
  fv_auto

set_option maxHeartbeats 2000000 in
theorem fve_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    FVE ct (decodePdptInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePdptInvocation; fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodePdptInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem fve_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    FVE ct (decodePageDirectoryInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageDirectoryInvocation; fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodePageDirectoryInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem fve_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    FVE ct (decodePageTableInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageTableInvocation; fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodePageTableInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem fve_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    FVE ct (decodePageInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageInvocation; fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodePageInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem fve_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) :
    FVE ct (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodePortInvocation _ _ _)

set_option maxHeartbeats 2000000 in
theorem fve_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : ArchCap) (ex : List Cap) :
    FVE ct (decodeIoportControlInvocation (Z := Unit) label args slot cap ex) := by
  unfold decodeIoportControlInvocation; fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodeIoportControlInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem fve_decodePml4Flush (cap : ArchCap) :
    FVE ct (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodePml4Flush _)

set_option maxHeartbeats 2000000 in
theorem fve_decodeTestAndClearAccessed (cap : ArchCap) :
    FVE ct (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodeTestAndClearAccessed _)

set_option maxHeartbeats 2000000 in
theorem fve_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    FVE ct (decodeDeriveSubframe (Z := Unit) args cte cap ex) := by
  unfold decodeDeriveSubframe; fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodeDeriveSubframe _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem fve_archDecodeInvocation (label : Data) (args : List Data) (x : CapRef) (sl : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : FVE ct (archDecodeInvocation (Z := Unit) label args x sl cap ex) := by
  unfold archDecodeInvocation
  split
  all_goals fv_auto
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_archDecodeInvocation _ _ _ _ _ _)

theorem fve_archDecode (label : Data) (args : List Data) (x : CapRef) (sl : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : FVE ct (fl4ArchDecodeInvocation (Z := Unit) label args x sl cap ex) := by
  unfold fl4ArchDecodeInvocation
  split
  all_goals fv_auto

macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodeIrqControl _ _ _ _ _)
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodeIrqHandler _ _ _)
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_decodeUntyped _ _ _ _ _)
macro_rules | `(tactic| fv_leaf) => `(tactic| with_reducible exact fve_archDecode _ _ _ _ _ _)

set_option maxHeartbeats 2000000 in
/-- **The first-phase decode keeps `fV`.** -/
theorem fve_decodeFirst (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    FVE ct (fl4DecodeInvocation (Z := Unit) true label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try rw [if_pos rfl]
  all_goals fv_auto

end

/-- The fault phase of the invocation (`fl4HandleInvocationR`'s first
argument of `syscall`). -/
def midF (thread : ObjRef) (info : MessageInfo) (cptr : CapRef) :
    FMonad Unit (CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) := do
  let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot thread cptr
  let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
  let extracaps ← lookupExtraCaps thread buffer info
  NonDetE.returnOk (slot, cap, extracaps, buffer)

/-- The first-phase decode phase of the invocation. -/
def midE (thread : ObjRef) (info : MessageInfo) (cptr : CapRef) :
    CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef → SEMonad Unit Fl4Invocation :=
  fun (slot, cap, extracaps, buffer) => do
    let args ← NonDetE.liftE <| getMrs thread buffer info
    fl4DecodeInvocation true info.miLabel args cptr slot cap extracaps buffer

section
variable {ct : ObjRef}

set_option maxRecDepth 20000

theorem fve_midF (t : ObjRef) (info : MessageInfo) (cptr : CapRef) : FVE ct (midF t info cptr) := by
  unfold midF; fv_auto

theorem fve_midE (t : ObjRef) (info : MessageInfo) (cptr : CapRef) (a) : FVE ct (midE t info cptr a) := by
  obtain ⟨sl, cap, ex, buf⟩ := a
  unfold midE
  refine dke_bind (dke_liftE (fv_getMrs _ _ _)) fun _ => fve_decodeFirst _ _ _ _ _ _ _

end

/-! ## The first-phase invocations -/

/-- The invocations the first-phase decode can yield (no TCB, Domain,
SchedContext, SchedControl or CNode invocation). -/
def FirstInv : Fl4Invocation → Prop
  | .invokeTCB _ | .invokeFl4TCB _ | .invokeDomain _ | .invokeSchedContext _ | .invokeSchedControl _
  | .invokeCNode _ => False
  | _ => True

/-- **The first-phase decode yields only `FirstInv` invocations** (l4v
`decode_invocation_safe_invocation`). -/
theorem okAll_decodeFirst (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkAll FirstInv (fl4DecodeInvocation (Z := Unit) true label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try rw [if_pos rfl]
  all_goals repeat' (first
    | exact okAll_throw
    | exact okAll_returnOk True.intro
    | exact okAll_liftME (okAll_true _) (fun _ _ => True.intro)
    | (apply okAll_ite <;> intro _))

theorem okAll_midE (t : ObjRef) (info : MessageInfo) (cptr : CapRef) (a) : OkAll FirstInv (midE t info cptr a) := by
  obtain ⟨sl, cap, ex, buf⟩ := a
  unfold midE
  exact okAll_bind fun _ => okAll_decodeFirst _ _ _ _ _ _ _

/-- The performs `JMidPerfHyp` [W] covers: Untyped, IRQ handler set / clear,
ASID control. -/
def PerfW : Fl4Invocation → Prop
  | .invokeUntyped _ => True
  | .invokeIRQHandler (.setIRQHandler _ _ _) => True
  | .invokeIRQHandler (.clearIRQHandler _) => True
  | .invokeArchObject (.spec (.invokeASIDControl _)) => True
  | _ => False

section
variable {ct : ObjRef}

theorem pr_setThreadState_run (t : ObjRef) (ts : ThreadState) (hr : runnable ts = true) :
    PR ct (setThreadState (Z := Unit) t ts) := by
  by_cases ht : t = ct
  · subst ht
    unfold setThreadState
    refine pr_bind ?_ fun _ => pr_of_kf (by unfold setThreadStateAct setSchedulerAction; kf_auto)
    intro σ x hs ⟨⟨tcb, s1⟩, h1, hx⟩
    obtain ⟨e1, e1'⟩ := mem_getsThe' h1
    simp only at e1 e1'
    subst e1'
    obtain ⟨-, e⟩ := setObject_out hx
    rw [e]
    refine ⟨hs.1, fun x hx => ?_⟩
    simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hx
    subst hx
    exact ⟨hr, (hs.2 tcb (getTcb_some e1)).2⟩
  · exact pr_of_kf (kf_setThreadState t ts ht)

theorem nv_setThreadState (t : ObjRef) (ts : ThreadState) : FK nV (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState threadSet setThreadStateAct setSchedulerAction
  repeat' (first | exact nv_setObject_tcb _ _ | dk_step0)

theorem kfe_post {ε α : Type} {m : NonDetE (State Unit) ε α} (h : KFE ct m) {σ : State Unit} (hs : CtRs ct σ) :
    ∀ y ∈ (m.run σ).1, CtRs ct y.2 :=
  fun y hy => CtRs.of_ctV (h σ y hy) hs

theorem pr_post {α : Type} {m : NonDet (State Unit) α} (h : PR ct m) {σ : State Unit} (hs : CtRs ct σ) :
    ∀ y ∈ (m σ).1, CtRs ct y.2 :=
  fun y hy => h σ y hs hy

macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performPml4Flush _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performDeriveSubframe _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performTestAndClearAccessed _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performPageInvocation _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performPageTableInvocation _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performPageDirectoryInvocation _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performPdptInvocation _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performAsidPoolInvocation _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performIoPortInvocation _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performIoportControlInvocation _)

/-- **The perform of a first-phase invocation but `PerfW` keeps `CtRs`** from
`CtRs ∧ NQ` (module docstring). -/
theorem perf_first (don : Bool) (inv : Fl4Invocation) (hf : FirstInv inv) (hw : ¬ PerfW inv) {σ : State Unit}
    (hs : CtRs ct σ) (hq : NQ ct σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false don inv).run σ).1, CtRs ct y.2 := by
  cases inv with
  | invokeUntyped i => exact absurd trivial hw
  | invokeEndpoint ep badge g gr =>
    simp only [fl4PerformInvocation, withoutPreemption]
    exact post_liftE (pr_post (pr_bind (pr_of_kf (dk_gets _)) fun thread =>
      pr_bind (pr_sendIpc false false badge g gr don thread ep (Or.inr ⟨rfl, rfl⟩)) fun _ =>
        pr_of_kf (dk_pure _)) hs)
  | invokeNotification ep badge =>
    simp only [fl4PerformInvocation, withoutPreemption]
    have h1 := post_liftE (ε := Unit) (fun x hx => pr_sendSignal ep badge σ x hs hq hx)
    refine post_bindE (R := CtRs ct) h1 (fun _ h => h) fun _ s' hm y hy => ?_
    rw [NonDetE.returnOk, ExceptT.run_pure] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact h1 _ hm
  | invokeReply reply grant =>
    simp only [fl4PerformInvocation]
    exact post_liftE (pr_post (pr_bind (pr_of_kf (dk_gets _)) fun sender =>
      pr_bind (pr_doReplyTransfer sender reply grant) fun _ => pr_of_kf (dk_pure _)) hs)
  | invokeIRQControl i =>
    simp only [fl4PerformInvocation]
    exact kfe_post (by kf_auto) hs
  | invokeIRQHandler i =>
    cases i with
    | aCKIrq irq =>
      simp only [fl4PerformInvocation, invokeIrqHandler]
      exact kfe_post (by kf_auto) hs
    | _ => exact absurd trivial hw
  | invokeArchObject i =>
    cases i with
    | spec i =>
      cases i with
      | invokeASIDControl _ => exact absurd trivial hw
      | _ =>
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
        exact kfe_post (by kf_auto) hs
    | _ =>
      simp only [fl4PerformInvocation, fl4ArchPerformInvocation]
      exact kfe_post (by kf_auto) hs
  | _ => exact absurd hf id

end

/-! ## The shell -/

/-- **Where the perform of `inv` starts on a run of the first-phase
invocation from `σ`**: after the message-info read, the fault phase
(`midF`) and the decode phase (`midE`) with outcome `inv`, and
`setThreadState ct Restart`. -/
def MidPerfAt (cptr : CapRef) (σ : State Unit) (inv : Fl4Invocation) (σ1 : State Unit) : Prop :=
  ∃ info σa a σb σc, (info, σa) ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1 ∧
    ((.ok a, σb) : Except Fault _ × State Unit) ∈ ((midF σ.curThread info cptr).run σa).1 ∧
    ((.ok inv, σc) : Except SyscallError _ × State Unit) ∈ ((midE σ.curThread info cptr a).run σb).1 ∧
    ((), σ1) ∈ (setThreadState (Z := Unit) σ.curThread .restart σc).1

/-- **[W] The Untyped, IRQ handler set / clear and ASID control performs keep
the current thread runnable without a fault**, at the states where they
start on a run of ReplyRecv / NBSendRecv / NBSendWait's invocation from the
entry state `σ` (`MidPerfAt`; never for an arbitrary state: from an arbitrary
`CtRs` state an untyped retype may create a TCB at `ct`). l4v
`perform_invocation_not_blocking_not_calling_ct_active` for these cases:
`invoke_untyped` (the retyped region is free, `valid_untyped_inv`: `ct`'s TCB
lies outside it), `invoke_irq_handler` (`cap_delete_one` of a notification
cap: `cancel_all_signals` restarts only `BlockedOnNotification` threads, not
`ct`, which is `Restart`), `perform_asid_control_invocation`
(`delete_objects` + retype of a free untyped region). -/
def JMidPerfHyp (don : Bool) (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ inv σ1, MidPerfAt cptr σ inv σ1 → PerfW inv →
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false don inv).run σ1).1, CtRs σ.curThread y.2

set_option maxHeartbeats 1000000 in
/-- **The shell**: from `CtRs ∧ NQ` at the entry, every outcome of the
first-phase non-blocking non-calling invocation has `CtRs`. -/
theorem midRun_shell (rep don : Bool) (cptr : CapRef) (σ : State Unit) (hs : CtRs σ.curThread σ)
    (hq : NQ σ.curThread σ) (hW : JMidPerfHyp don cptr σ) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep false false don true cptr).run σ).1, CtRs σ.curThread y.2 := by
  intro y hy
  unfold fl4HandleInvocationR at hy
  obtain ⟨z, hz, ⟨t, ht, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE_inv' hy
  swap
  · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he
  obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hz
  obtain rfl : w = (σ.curThread, σ) := hw
  simp only [Except.ok.injEq] at ht
  subst ht
  obtain ⟨z, hz, ⟨info, hi, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE_inv' hy
  swap
  · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he
  obtain ⟨⟨info', σa⟩, hia, rfl⟩ := mem_liftE_inv' hz
  simp only [Except.ok.injEq] at hi
  subst hi
  have hIa := fv_I (fv_getMessageInfo (ct := σ.curThread) _) ⟨hs, hq⟩ _ hia
  refine syscall_post (mF := midF σ.curThread info' cptr) (mE := midE σ.curThread info' cptr)
    (I := fun s => CtRs σ.curThread s ∧ NQ σ.curThread s) (Q := CtRs σ.curThread)
    (fun w hw => fv_I (fve_midF _ _ _) hIa w hw) ?_
    (fun a s has w hw => fv_I (fve_midE _ _ _ a) (fv_I (fve_midF _ _ _) hIa _ has) w hw) ?_ ?_ y hy
  · intro f s hI v hv
    simp only [NonDet.when, Bool.false_eq_true, ↓reduceIte] at hv
    obtain rfl : v = ((), s) := hv
    exact hI.1
  · intro e s hI v hv
    simp only [NonDet.when, Bool.false_eq_true, ↓reduceIte] at hv
    obtain rfl : v = ((), s) := hv
    exact hI.1
  · intro a s b s' has hbs hI y hy
    have hFI : FirstInv b := okAll_midE _ _ _ a s _ hbs b rfl
    refine post_bindE (R := fun s => CtRs σ.curThread s ∧ NQ σ.curThread s) ?_ (fun _ h => h.1) ?_ y hy
    · unfold withoutPreemption
      exact post_liftE (Q := fun s => CtRs σ.curThread s ∧ NQ σ.curThread s) fun x hx =>
        ⟨pr_setThreadState_run _ _ rfl s' x hI.1 hx, NQ.of_nV (nv_setThreadState _ _ s' x hx) hI.2⟩
    intro u s1 h1 y hy
    obtain ⟨⟨u', s1'⟩, h1', e1⟩ := mem_liftE_inv' h1
    simp only [Prod.mk.injEq] at e1
    obtain ⟨-, rfl⟩ := e1
    have hI1 : CtRs σ.curThread s1 ∧ NQ σ.curThread s1 :=
      ⟨pr_setThreadState_run _ _ rfl s' _ hI.1 h1', NQ.of_nV (nv_setThreadState _ _ s' _ h1') hI.2⟩
    refine post_bindE (R := CtRs σ.curThread) ?_ (fun _ h => h) ?_ y hy
    · by_cases hw : PerfW b
      · exact hW b s1 ⟨info', σa, a, s, s', hia, has, hbs, h1'⟩ hw
      · exact perf_first don b hFI hw hI1.1 hI1.2
    intro r s2 h2 y hy
    have hs2 : CtRs σ.curThread s2 := by
      by_cases hw : PerfW b
      · exact hW b s1 ⟨info', σa, a, s, s', hia, has, hbs, h1'⟩ hw (.ok r, s2) h2
      · exact perf_first don b hFI hw hI1.1 hI1.2 (.ok r, s2) h2
    unfold withoutPreemption at hy
    refine post_liftE (pr_post ?_ hs2) y hy
    refine pr_gts_bind _ fun ts _ => ?_
    split
    · refine pr_bind (pr_of_kf (dk_pure _)) fun _ => ?_
      exact pr_setThreadState_run _ _ rfl
    · exact pr_of_kf (dk_pure _)

/-- **`JMidRunHyp` from `JMidPerfHyp` [W]** (module docstring). -/
theorem jMidRunHyp_of {rep don : Bool} {cptr : CapRef} {σ : State Unit} (hW : JMidPerfHyp don cptr σ) :
    JMidRunHyp rep don cptr σ := by
  intro hE y hy _
  have hs : CtRs σ.curThread σ := ⟨rfl, fun x hx => ⟨hE.run x hx, hE.nf x hx⟩⟩
  obtain ⟨e, h⟩ := midRun_shell rep don cptr σ hs hE.nq hW y hy
  intro x hx
  rw [e] at hx
  exact (h x hx).1

end

end Fl4Proofs.P3.MidRun

open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`MidEntry` at a system call's entry**: `run` from `JAtZ.curRun` and
`Entered`, `nq` from the notification relation (a runnable thread is in no
waiting queue, `not_in_ntfnQueue`, the notification and the TCB in the
relation's sets by `ObjCover`); `nf` is `JEntryAt.cnf`'s [J] fact (l4v
`fault_tcbs_valid_states`), passed in. -/
theorem JAtZ.midEntry {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hnf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none) : MidEntry σ := by
  have hrun := J.curRun.run hni
  refine ⟨hrun, hnf, fun p n q hp hq hm => ?_⟩
  obtain ⟨x, hk⟩ : ∃ x, σ.kheap σ.curThread = some (.tcb x) := by
    rcases J.cur with h | h
    · rw [hni.2] at h; cases h
    · obtain ⟨xt, hk, -⟩ := h.tcb; exact ⟨xt, hk⟩
  obtain ⟨t, ht, et⟩ := J.obj.tcb _ _ hk
  obtain ⟨n', hn', rfl⟩ := J.obj.ntfn _ _ hp
  have hR : NtfnStateRel Z.N Z.T (L.mem s) σ := J.xtop.fin.1.1.2.2.1
  have hr := hrun x hk
  rw [← et] at hk hm
  exact not_in_ntfnQueue hR ht hk hr n' hn' n hp (by rw [hq]; exact hm)

/-- **`handle_invocation_midJ` from `JMidPerfHyp` [W]**: `JMidRunHyp` by
`jMidRunHyp_of`, `MidEntry` by `JAtZ.midEntry` (with `Entered` and the
current thread's no-fault fact [J], `JEntryAt.cnf`'s). -/
theorem handle_invocation_midJP [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (can_donate : Bool) (cptr : U64)
    (info : msginfo.MessageInfo) (hinfo : msg.msg_info st s ct = ok info)
    (mi : Fl4Spec.MessageInfo) (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    (buf : U64) (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    (buffer : Option Fl4Spec.ObjRef)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
    (hr2 : ipc.lookup_extra_caps st s ct buf info = ok r2)
    (er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr)))
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False))
    (argsU : List U64)
    (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False))
    (hH : JEntryHyps (L := L) arI AR Z H Cs D s ar σ ct false false can_donate true cptr info mi buf buffer
      argsU r2 er)
    (hW : MidRun.JMidPerfHyp can_donate (Fl4Spec.toBl cptr.bv) σ) (hni : Entered σ)
    (hnf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none) :
    syscall.handle_invocation st arI s ar false false can_donate true cptr ⦃ res =>
      HIPostMid (L := L) arI AR σ can_donate (Fl4Spec.toBl cptr.bv) res ⦄ :=
  handle_invocation_midJ arI s ar σ J ct hct can_donate cptr info hinfo mi hmi buf hbuf buffer hbuffer r2 hr2 er her
    argsU hmrs hH (MidRun.jMidRunHyp_of hW) (J.midEntry hni hnf)

end

end

end Fl4Proofs.P3
