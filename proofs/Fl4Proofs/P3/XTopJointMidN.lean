/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch23b (c2)): **a
`chooseNewThread` mid state where the current thread has no SC** (`MidN`).
The receive leaves at such a state (XTopJointFaultN, XTopJointRecvSigN,
XTopJointRecvIpcN) are the resumed / `MidC` proofs with ct's SC field `none`
in place of `CurInv`:

* ct is in no release queue: `Sched.Inv.notRel_of_noSc` (sch22, `Inv.rel`);
* P1's `CanBlock` of ct: XTopJointRecvSig's `JAtZ.canBlockCurG`, whose `hsa`
  second disjunct is exactly a pending reschedule with ct SC-less (ct's SC
  word is `0`, so the bound-SC conjunct of `CanBlock` is vacuous):
  `JAtZ.canBlockCurMN`;
* `BlockedScActive` after ct blocks: no SC is bound to ct (`scBack_of` would
  give ct's SC field `some`), so the new blocked thread asks nothing.
-/
import Fl4Proofs.P3.XTopJointKEntry22M
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **A `chooseNewThread` mid state where ct has no SC** (module docstring). -/
def MidN (σ : Fl4Spec.State Unit) : Prop :=
  σ.curThread ≠ σ.idleThread ∧ CurRun σ ∧ σ.schedulerAction = .chooseNewThread ∧
    ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbSchedContext = none

theorem MidN.run {σ : Fl4Spec.State Unit} (h : MidN σ) : CurRun σ := h.2.1

theorem MidN.nr {σ : Fl4Spec.State Unit} (h : MidN σ) : σ.schedulerAction ≠ .resumeCurThread := by
  rw [h.2.2.1]; intro e; cases e

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **P1's `CanBlock` of the current thread at a `MidN` state** (module
docstring): `canBlockCurG`'s SC-less branch. -/
theorem JAtZ.canBlockCurMN
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrn : Fl4Spec.runnable x.tcbState = true)
    (hti : σ.curThread ≠ σ.idleThread) (hnr : ct.bv ∉ σ.releaseQueue) (hni : MidN σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) :
    P1.CanBlock st (P1.Heap.tcbs H) Ac s ct :=
  J.canBlockCurG ht hcur hk hrn hti hnr (Or.inr ⟨hni.2.2.1, hni.2.2.2 x (by rw [hcur]; exact hk)⟩) hnq

end

end

end Fl4Proofs.P3
