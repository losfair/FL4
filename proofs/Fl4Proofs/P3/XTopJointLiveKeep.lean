/-
P3 (DESIGN.md §9), CSpace: **`LiveJ` and `DbgWF` across a deletion-loop step
that keeps the slots** (toward carrying XTopJointLive's `LiveJ` and DbgWF's
`DbgWF` through the loop instead of XTopJointDelR's `JDelParts.live`).

* `dbgNth_keep`: the debug list walked from a TCB (or `0`) is the same when
  the TCBs' `DEBUG_NEXT` words are (`DbgTz`: each link `0` or a TCB).
* `LiveJ.of_same`: a step keeping every slot (`SlotsSame`), the original
  bits, the spec's idle thread, the debug words (`DbgKeep`, XTopJointDbgKeep) and the dead TCBs
  (`DeadP`) keeps `LiveJ` at the same MDB ghost.
* `DbgWFL.of_keep`: `DbgKeep` and the affinities kept keep `DbgWFL` at the
  same lists; `JAtZ.dbgWF_keep`: the affinities from `JAtZ` before and after
  (`SchedCore.aff`: every TCB on the current core).
-/
import Fl4Proofs.P3.XTopJointDbgKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

/-- **A dead set joins the dead set** (as XTopJointFinThreadU's `JAtZ.addDead`). -/
theorem JAtZ.addDeadSet {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {E : Set U64}
    (hd : ∀ p ∈ E, DeadP (L := L) H s p) : JAtZ (L := L) arI AR Z H Cs Ac Lst (D ∪ E) s a σ :=
  { J with
    jcov := ⟨fun q k hq => (J.jcov.th q k hq).imp_right (Or.imp_left Or.inl),
      fun q k hq => (J.jcov.h q k hq).imp_right (Or.imp_left Or.inl),
      fun q hq => hq.elim (J.jcov.dead q) (hd q),
      J.jcov.ks, J.jcov.idleOut⟩
    kern := { J.kern with }
    zD := fun p hp => Or.inl (J.zD p hp) }


/-- **`DbgWFL` across a `JAtZ` step keeping the debug words** (the
affinities: every TCB on the current core before and after). -/
theorem JAtZ.dbgWF_keep {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {Z' : XSets} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (J' : JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' s' a' σ') (hZT : Z'.T = Z.T) (hZc : Z'.c = Z.c)
    {lst : U64 → List U64} (hW : DbgWFL (P1.Heap.tcbs H) Cs (L.mem s) (dbgHd (L := L) s) lst)
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') :
    DbgWFL (P1.Heap.tcbs H) Cs (L.mem s') (dbgHd (L := L) s') lst := by
  obtain ⟨Q0, R0, hc0, -⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q1, R1, hc1, -⟩ := J'.xtop.fin.1.1.1.lists
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  refine hW.of_keep hK fun y hy => ?_
  rw [hc1.aff y (by rw [hZT, hTe]; exact hy), hc0.aff y (by rw [hTe]; exact hy), hZc]

end

end

end Fl4Proofs.P3
