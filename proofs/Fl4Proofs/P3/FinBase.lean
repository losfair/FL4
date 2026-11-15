/-
P3 (DESIGN.md §9), CSpace: **the finality invariant's definitions**
(`FinInv`, `FinM`, `KTyped`, the object key `okey`, overlap `Ovl`), low in
the import order so that the CSpace operations above `MdbFull` can keep it.
See `FinDefs` for what it gives.
-/
import Fl4Proofs.P3.MdbFull
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## The object a cap names, as `same_object_as` compares it -/

inductive OKey where
  | ep (p : U64) | ntfn (p : U64) | reply (p : U64) | cnode (p r : U64) | thread (p : U64) | irq (i : U64)
  | sc (p sb : U64) | frame (p : U64) (sz : capability.FrameSize) (d : Bool) | pt (p : U64) | pd (p : U64)
  | pdpt (p : U64) | pml4 (p : U64) | pool (p : U64) | io (f l : U64)
  | vcpu (p : U64) | ept (p level : U64)

def okey : capability.Cap → Option OKey
  | .Endpoint p .. => some (.ep p)
  | .Notification p .. => some (.ntfn p)
  | .Reply p _ => some (.reply p)
  | .CNode p r _ _ => some (.cnode p r)
  | .Thread p => some (.thread p)
  | .IrqHandler i => some (.irq i)
  | .SchedContext p sb => some (.sc p sb)
  | .Frame p sz _ d .. => some (.frame p sz d)
  | .PageTable p .. => some (.pt p)
  | .PageDirectory p .. => some (.pd p)
  | .Pdpt p .. => some (.pdpt p)
  | .Pml4 p .. => some (.pml4 p)
  | .Vcpu p => some (.vcpu p)
  | .Ept p level .. => some (.ept p level)
  | .AsidPool p _ => some (.pool p)
  | .IoPort f l _ => some (.io f l)
  | _ => none


/-- Two abstract caps share a generic object reference. -/
def Ovl (a b : Fl4Spec.Cap) : Prop := Fl4Spec.genObjRefs a ∩ Fl4Spec.genObjRefs b ≠ ∅

theorem Ovl.symm {a b : Fl4Spec.Cap} (h : Ovl a b) : Ovl b a := by
  unfold Ovl at *; rwa [Set.inter_comm]

/-- The spec's CNodes and TCBs are FL4's: every well-formed CNode and every
TCB of the spec's heap is an object of the typed heap (so every slot the
spec can read is a slot of the typed heap). -/
def KTyped (th : TypedHeap) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ o : BitVec 64, (∀ r cs, σ.kheap o = some (.cnode r cs) → Fl4Spec.wellFormedCnodeN r cs →
      th ⟨o⟩ = some (.cnode r)) ∧ (∀ t, σ.kheap o = some (.tcb t) → th ⟨o⟩ = some .tcb)

/-- The MDB part of `FinInv` (see the header). -/
structure FinM (mem : U64 → U64) (G : MdbGhost) : Prop where
  conn : ∀ ch1 ∈ G.chains, ∀ ch2 ∈ G.chains, ∀ x ∈ ch1, ∀ y ∈ ch2,
    Ovl (absCap (capV mem x)) (absCap (capV mem y)) → ch1 = ch2
  key : ∀ x ∈ G.chains.flatten, ∀ y ∈ G.chains.flatten, x ≠ y →
    Ovl (absCap (capV mem x)) (absCap (capV mem y)) → isZb (capV mem x) = false → isZb (capV mem y) = false →
    ¬ (isFrame (capV mem x) = true ∧ isFrame (capV mem y) = true) →
    okey (capV mem x) = okey (capV mem y)
  fnest : ∀ x ∈ G.chains.flatten, ∀ y ∈ G.chains.flatten, x ≠ y → isFrame (capV mem x) = true →
    isFrame (capV mem y) = false → srM mem x y = true → okey (capV mem y) = okey (capV mem x)
  zfin : ∀ x ∈ G.chains.flatten, ∀ y ∈ G.chains.flatten, x ≠ y → isZb (capV mem x) = true →
    ¬ Ovl (absCap (capV mem x)) (absCap (capV mem y))

/-- What finality needs beyond the CSpace relation and `MdbInv` (see the
header). -/
structure FinInv (th : TypedHeap) (mem : U64 → U64) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop where
  kt : KTyped th σ
  fm : FinM mem G

end

end Fl4Proofs.P3
