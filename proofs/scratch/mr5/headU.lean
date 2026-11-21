/-
P3 (DESIGN.md §9), untyped (KENTRY-PLAN mr5): **the Untyped invocation under
`MachPlat`** (mr4 NEXT (1)): UtResetLoopJM's `JAtZ.reset_loopJM` lifted
through the reset and the retype with a reset, so the Untyped decode ends in
`JAtPreMV` (what `hPre_ofZQIM` consumes) with no `PPPlat`.

* `UtRetPostJM`: XTopJointUt's `UtRetPostJ` with `JAtPreMV` after a
  preempted reset; `UtRetPostJ.toM` (an invocation whose spec side has no
  error outcome after the restart is never preempted: both posts agree);
  `NoErrAt`/`noErrAt_bind`/`noErrAt_liftE_single` (SpecNoPre's `NoErrE` at one
  state), `noErr_retypeNoReset` (the spec's retype without a reset has no error
  outcome), `noErrAt_retypeDev` (a reset of a device cap has none: l4v
  `reset_untyped_cap` clears and preempts only RAM caps).
* `JAtZ.reset_untypedJM`: UtResetTopJ's `JAtZ.reset_untypedJ` with `MachPlat`
  + `PPPlatA` + `MR`/`ValidMachineTime`/`ValidIrqMasks` at the start (the
  spec's `delete_objects` changes only the heap and memory, so the three hold
  at `delSt` by definition), the chunk loop by `JAtZ.reset_loopJM`, ending in
  `ResetJPostM`.
* `JAtZ.utResetJM`: UtRetResetJ's `JAtZ.utResetJ` likewise (the restart keeps
  the machine state, the clock and the interrupt table), ending in
  `UtRetPostJM`.
* `JUtRetHypDM`, `JAtZ.jUtRetHypM` (RAM caps: every native object type with a
  reset by `utResetJM`, without one by `JAtZ.jUtRetHyp`'s proved cases and
  `toM`), `JAtZ.jUtRetHypDevM` (device caps: `JAtZ.jUtRetHypDev` and `toM`,
  the reset of a device cap has no error outcome), and
  `decode_invocation_untypedJM` (XTopJointUt's decode, `XCapP` at
  `JAt`/`JAtPreMV`).

The native types only (`hNat`: XTopJointEntry's `JUtPath.vtx` [scope] keeps
the VT-x types 14..18 out, so UtRetResetJ's `JUtRetHypR2` [W] is not needed
here). No new premise.
-/
import Fl4Proofs.P3.UtResetLoopJM
import Fl4Proofs.P3.UtDevReset
import Fl4Proofs.P3.SpecNoPre
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec's retype: no error outcome without a RAM reset -/

namespace NoPre
open Fl4Spec

/-- No outcome of `m` from `s` is an error. -/
def NoErrAt {ε α : Type} (m : NonDetE (State Unit) ε α) (s : State Unit) : Prop :=
  ∀ y, y ∈ (m.run s).1 → ∀ e, y.1 ≠ .error e

theorem NoErrE.at {ε α : Type} {m : NonDetE (State Unit) ε α} (h : NoErrE m) (s : State Unit) : NoErrAt m s :=
  h s

theorem noErrAt_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    {s : State Unit} (hm : NoErrAt m s) (hf : ∀ x, x ∈ (m.run s).1 → ∀ a, x.1 = .ok a → NoErrAt (f a) x.2) :
    NoErrAt (m >>= f) s := by
  intro y hy e he
  change y ∈ (NonDet.bind (ExceptT.run m) _ s).1 at hy
  obtain ⟨⟨r, s1⟩, hr, hy⟩ := hy
  cases r with
  | error e' => exact hm _ hr e' rfl
  | ok a => exact hf _ hr a rfl y hy e he

theorem noErrAt_liftE_single {ε α β : Type} {m : NonDet (State Unit) α} {f : α → NonDetE (State Unit) ε β}
    {s : State Unit} {a : α} (hm : m s = ({(a, s)}, False)) (hf : NoErrAt (f a) s) :
    NoErrAt (NonDetE.liftE m >>= f) s := by
  refine noErrAt_bind ((noErr_liftE m).at s) fun x hx a' ha' => ?_
  unfold NonDetE.liftE at hx
  rw [ExceptT.run_lift] at hx
  obtain ⟨z, hz, hx⟩ := hx
  rw [hm] at hz
  have hz' : z = (a, s) := hz
  subst hz'
  rw [show x = (.ok a, s) from hx] at ha' ⊢
  cases ha'
  exact hf

/-- **The spec's retype without a reset has no error outcome.** -/
theorem noErr_retypeNoReset (b c d : Bool) (sl : CslotPtr) (base rb : Word) (t : ApiObjectType) (us : Nat)
    (slots : List CslotPtr) (dev : Bool) :
    NoErrE (fl4PerformInvocation (Z := Unit) b c d (.invokeUntyped (.retype sl false base rb t us slots dev))) := by
  simp only [fl4PerformInvocation, fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true,
    ↓reduceIte, NonDetE.returnOk]
  exact noErr_bind (noErr_bind (noErr_pure _) fun _ => noErr_liftE _) fun _ => noErr_pure _

/-- **A device cap's reset has no error outcome** (no clear, no preemption
point: `resetUntypedCap`'s `dev ∨ sz < resetChunkBits` branch). -/
theorem noErrAt_resetDev {sl : CslotPtr} {σ : State Unit} {pb : ObjRef} {sz fi : Nat}
    (hg : getCap (Z := Unit) sl σ = ({(.untypedCap true pb sz fi, σ)}, False)) :
    NoErrAt (resetUntypedCap (Z := Unit) sl) σ := by
  unfold resetUntypedCap
  refine noErrAt_liftE_single hg (NoErrE.at ?_ σ)
  simp only [NonDetE.returnOk, ndE_pure_bind, isDeviceUntypedCap, true_or, ↓reduceIte]
  split_ifs
  · exact noErr_pure _
  · repeat (first | exact noErr_pure _ | exact noErr_liftE _ | refine noErr_bind ?_ fun _ => ?_)

/-- **The spec's retype with a reset of a device cap has no error outcome.** -/
theorem noErrAt_retypeDev (b c d : Bool) {sl : CslotPtr} {σ : State Unit} {pb : ObjRef} {sz fi : Nat}
    (hg : getCap (Z := Unit) sl σ = ({(.untypedCap true pb sz fi, σ)}, False)) (base rb : Word)
    (t : ApiObjectType) (us : Nat) (slots : List CslotPtr) (dev : Bool) :
    NoErrAt (fl4PerformInvocation (Z := Unit) b c d (.invokeUntyped (.retype sl true base rb t us slots dev))) σ := by
  simp only [fl4PerformInvocation, fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte,
    NonDetE.returnOk]
  refine noErrAt_bind (noErrAt_bind (noErrAt_resetDev hg) fun _ _ _ _ => (noErr_liftE _).at _)
    fun _ _ _ _ => (noErr_pure _).at _

end NoPre

section
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **An untyped invocation's outcome at `J` under `MachPlat`**: XTopJointUt's
`UtRetPostJ` with `JAtPreMV` after a preempted reset. -/
def UtRetPostJM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (σ : Fl4Spec.State Unit)
    (blk call don : Bool) (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeUntyped inv)).run σ1).1, (∃ th' G',
      ((res.1 = .Ok () ∧ y.1 = .ok []) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
      DomRel (L.mem res.2.1) (L.ksb res.2.1) y.2 ∧ MdbOKV (L.ksb res.2.1) (L.mem res.2.1) G') ∧
      (if res.1 = .Err .Preempted then JAtPreMV (L := L) arI AR MR res.2.1 res.2.2 y.2
        else JAt (L := L) arI AR res.2.1 res.2.2 y.2)

variable {arI}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`UtRetPostJ` gives `UtRetPostJM` when the spec side cannot err** after
the restart (then FL4's outcome is not `Preempted`). -/
theorem UtRetPostJ.toM {σ : Fl4Spec.State Unit} {blk call don : Bool} {inv : Fl4Spec.UntypedInvocation}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : UtRetPostJ (L := L) arI AR σ blk call don inv res)
    (hne : ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      NoPre.NoErrAt (Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeUntyped inv)) σ1) :
    UtRetPostJM (L := L) arI AR MR σ blk call don inv res := by
  obtain ⟨σ1, hst, y, hy, hrel, hX⟩ := h
  have hok : res.1 ≠ .Err .Preempted := by
    intro hp
    obtain ⟨-, -, hc, -⟩ := hrel
    rcases hc with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [hp] at h1; cases h1
    · exact hne σ1 hst y hy () h2
  refine ⟨σ1, hst, y, hy, hrel, ?_⟩
  rw [if_neg hok] at hX ⊢
  exact hX

theorem utRetPostJM_of_body {σ σ1 : Fl4Spec.State Unit} {blk call don : Bool} {inv : Fl4Spec.UntypedInvocation}
    {res : core.result.Result Unit error.Exc × S × A}
    (hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h : UtBodyPost (L := L) arI AR σ1 inv res) : UtRetPostJM (L := L) arI AR MR σ blk call don inv res := by
  obtain ⟨σ', hrun, hok, ⟨th', G', hrel⟩, hJ⟩ := h
  refine ⟨σ1, hst1, (.ok [], σ'), perf_ut_mem blk call don hrun, ⟨th', G', Or.inl ⟨hok, rfl⟩, hrel⟩, ?_⟩
  rw [if_neg (by rw [hok]; simp)]
  exact hJ

theorem utRetPostJM_of_reset {σ σ1 σ2 : Fl4Spec.State Unit} {blk call don : Bool} {sl : Fl4Spec.CslotPtr}
    {base rb : Fl4Spec.Word} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A}
    (hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hr : ((.ok (), σ2) : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.resetUntypedCap (Z := Unit) sl).run σ1).1)
    (h : UtBodyPost (L := L) arI AR σ2 (.retype sl false base rb t us slots dev) res) :
    UtRetPostJM (L := L) arI AR MR σ blk call don (.retype sl true base rb t us slots dev) res := by
  obtain ⟨σ', hrun, hok, ⟨th', G', hrel⟩, hJ⟩ := h
  have hy := invoke_reset_ok Fl4Spec.fl4ObjBitsApi sl base rb t us slots dev hr (mem_of_run hrun)
  refine ⟨σ1, hst1, (.ok [], σ'), mem_bindE_ok hy (mem_returnOk []), ⟨th', G', Or.inl ⟨hok, rfl⟩, hrel⟩, ?_⟩
  rw [if_neg (by rw [hok]; simp)]
  exact hJ

theorem utRetPostJM_of_preempt {σ σ1 σ' : Fl4Spec.State Unit} {blk call don : Bool} {sl : Fl4Spec.CslotPtr}
    {base rb : Fl4Spec.Word} {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A}
    (hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hr : ((.error (), σ') : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.resetUntypedCap (Z := Unit) sl).run σ1).1)
    (he : res.1 = .Err .Preempted) (hpre : JAtPreMV (L := L) arI AR MR res.2.1 res.2.2 σ') {Z' : XSets}
    (hX : XTopAt (L := L) AR Z' res.2.1 res.2.2 σ') :
    UtRetPostJM (L := L) arI AR MR σ blk call don (.retype sl true base rb t us slots dev) res := by
  obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := hX.rel
  refine ⟨σ1, hst1, (.error (), σ'), mem_bindE_err (invoke_reset_err Fl4Spec.fl4ObjBitsApi sl base rb t us slots dev hr),
    ⟨Z'.th, Z'.G, Or.inr ⟨he, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, ?_⟩
  rw [if_pos he]
  exact hpre

end

