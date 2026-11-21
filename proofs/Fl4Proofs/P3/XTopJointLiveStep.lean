/-
P3 (DESIGN.md §9), CSpace (KENTRY-PLAN g2g (a')): **every run of primitive
steps keeps `LiveDN`** (StepSem's `Steps`), so each decode that ends through
`Steps` (the CNode copy family, IRQ / IO port control, IRQ handler, domain,
IO port) can end in `LiveDN` as well as `JAtZ`.

* StepSem's `slot` (an insert) now also gives the inserted cap non-null and
  no zombie, `cslot` (a CNode copy, move or rotate) gives `CnLive` (every
  written non-null cap has the shape of a non-null cap of the written slots
  before, and every such cap survives up to its shape) and the original bit
  of a written slot left null cleared (CnodeCopy's `NullSrc`,
  XTopCnode's `invoke_nullOrig`). `shape` keeps thread and zombie caps and a
  CNode cap's object (`refs_shape`, `shape_thread`, `shape_zombie`).
* `ZNoBlk`: no zombie names an object inside the kernel-state block (the IRQ
  node's CNodes; l4v: no cap names an IRQ node CNode, `valid_global_refs`).
  It replaces "no zombie names the destination CNode" when the destination
  is in the block (`DestLive`'s right disjunct, IRQHandler's insert).
* `JAtZ.schW_notDbg`: a scheduler step's word is no debug word.
* `LiveDN.wstep`: a step writing slot words only, at the slots `W` (each in a
  live CNode, `DestLive`), keeps `LiveDN` and `ZNoBlk`: from "every zombie
  after was one before" and "every non-null cap before survives up to its
  shape", the original bits off `W` kept and `W`'s null slots unoriginal.
* `QL` / `stepClosed_jatL`: `JAtZ ∧ LiveDN ∧ ZNoBlk` is closed under the
  primitive steps, each started from `J.addDeadSet hL.1.ztcb` and taken at the
  same dead set (XTopJointRest's `jowes_restartD`, `jowes_ksD`, and the
  `JOwesD` / `JOwesCsD` forms of `jowes_ins`, `jowes_cn`, `jowes_sched`);
  `Steps.jatL`.
-/
import Fl4Proofs.P3.XTopJointLiveIns
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **A step writing slot words at the slots `W` keeps `LiveDN` and
`ZNoBlk`** (module docstring; LiveFrame's `LiveDN.wstepX` at `J'`). -/
theorem LiveDN.wstep {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s))
    {G' : MdbGhost} {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (J' : JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ')
    (hD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D')
    (hid : σ'.idleThread = σ.idleThread) (hw : P1.WritesIn st s s' (InSlot Z.th))
    (W : List Fl4Spec.CslotPtr)
    (hW : ∀ sl ∈ W, ∃ p r, sl.1 = p.bv ∧ Z.th p = some (.cnode r) ∧ sl.2.length = r ∧
      DestLive Z.th (L.mem s) (L.ksb s) p)
    (hcW : ∀ y, IsSlot Z.th y → (∀ sl ∈ W, y ≠ cslotAddr sl) → capV (L.mem s') y = capV (L.mem s) y)
    (hoW : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ sl ∈ W)
    (hNO : ∀ sl ∈ W, capV (L.mem s') (cslotAddr sl) = .Null → σ'.isOriginalCap sl = false)
    (hZ : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s') y = .Zombie p zt n →
      ∃ y0, IsSlot Z.th y0 ∧ capV (L.mem s) y0 = .Zombie p zt n)
    (hK2 : ∀ y0, IsSlot Z.th y0 → capV (L.mem s) y0 ≠ .Null →
      ∃ y, IsSlot Z.th y ∧ capV (L.mem s') y ≠ .Null ∧ shape (capV (L.mem s') y) = shape (capV (L.mem s) y0)) :
    LiveDN (L := L) Z.th H Cs G' s' σ' ∧ ZNoBlk Z.th (L.mem s') (L.ksb s') :=
  LiveDN.wstepX J hLv hZB J'.xtop (fun p hp => J'.jcov.dead p (hD p hp)) hid hw W hW hcW hoW hNO hZ hK2

/-- **`JAtZ`, `LiveDN` and `ZNoBlk` after a run of primitive steps.** -/
theorem Steps.jatL (hAM : ARMask arI AR) {th : TypedHeap} {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit}
    (h : Steps (L := L) arI th s a σ s' a' σ') (hth : Z.th = th) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hL : LiveDN (L := L) Z.th H Cs Z.G s σ) (hZ : ZNoBlk Z.th (L.mem s) (L.ksb s)) :
    ∃ (G' : MdbGhost) (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ' ∧ LiveDN (L := L) Z.th H Cs G' s' σ' ∧
      ZNoBlk Z.th (L.mem s') (L.ksb s') :=
  let ⟨G', V', Ac', Lst', D', J', hZ'⟩ := Steps.jatZ arI hAM (jStepHyps arI) h hth J hZ
  ⟨G', V', Ac', Lst', D', J', J'.live, hZ'⟩

end

end

end Fl4Proofs.P3
