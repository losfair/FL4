/-
P3 (DESIGN.md §9), CSpace: **CNode Revoke and Delete with `DelHyp`
discharged**: `cnode_revoke_refines` and `cnode_delete_refines` with the
deletion proved (`delHyp_full`) and finality (`finalHyp_full`), leaving
the hypotheses of `DelRound` (the object-specific finalisations, the
preemption points, `post_cap_deletion`) and the bound `K` on CNode sizes.
-/
import Fl4Proofs.P3.DelFull
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem delE_restart {th : TypedHeap} {K : Nat} {s s1 : S} {σ σ1 : Fl4Spec.State Unit}
    (h : DelE (L := L) th K s σ) (hS : SlotsSame th (L.mem s) (L.mem s1)) (hK : KSub σ σ1) :
    DelE (L := L) th K s1 σ1 := by
  obtain ⟨hD, hB, hKT, hFM⟩ := h
  refine ⟨hD.of_same hS, fun G hM => ?_, hKT.sub hK, finM_same hFM hS⟩
  have hM0 : MdbLinks th (L.mem s) G := by
    refine hM.of_same (fun x hx => ?_)
    obtain ⟨h1, h2, h3, h4⟩ := hS x hx
    exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩
  rw [psiD_same hM0 hM hS]; exact hB G hM0

/-- **CNode Revoke**, decode and invoke, with the deletes of the children
proved. -/
theorem cnode_revoke_full [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeRevoke)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List Fl4Spec.Cap)
    (hI : MdbInv (L.mem s) G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hO : FinObjHyp (L := L) arI th) (hPP : PPHypD (L := L) arI th)
    (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hDE : DelE (L := L) th K s σ) :
    cnode.decode st arI s ar fl4_abi.label.CNodeRevoke length cap buf extra ⦃ res =>
      PInvPost (L := L) th σ G (Fl4Spec.decodeCnodeInvocation slbl (args.map UScalar.bv) a excaps) s
        (res.1, res.2.1) ⦄ := by
  have hfew : psiD (L.mem s) G < 2 ^ 64 - 1 := by
    have := hDE.2.1 G hM
    have : psiD (L.mem s) G ≤ psiD (L.mem s) G * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  exact cnode_revoke_refines arI th s ar σ G hR hV hP hM hC slbl hlbl length buf ct hct args hlen hargs cap a hca hcv
    extra excaps hI hact hcur htcb (DelE (L := L) th K) psiD psiD_slotsSame
    (delHyp_full arI th hP (finalHyp_full th hP) hO hPP hPD K hK hK6) (rppHyp_full arI th K hPP)
    (fun s1 σ1 hS h => delE_restart hDE hS (ksub_of_eq (setThreadState_nks _ _) h))
    (fun _ _ G1 hCR hE1 => ⟨hE1.2.2.1, hE1.2.2.2 G1 hCR.2.2.1⟩) hfew

/-- **CNode Delete**, decode and invoke, for any cap, with the deletion
proved. -/
theorem cnode_delete_full [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeDelete)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List Fl4Spec.Cap)
    (hI : MdbInv (L.mem s) G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hO : FinObjHyp (L := L) arI th) (hPP : PPHypD (L := L) arI th)
    (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hDE : DelE (L := L) th K s σ) :
    cnode.decode st arI s ar fl4_abi.label.CNodeDelete length cap buf extra ⦃ res =>
      PInvPost (L := L) th σ G (Fl4Spec.decodeCnodeInvocation slbl (args.map UScalar.bv) a excaps) s
        (res.1, res.2.1) ⦄ :=
  cnode_delete_refines arI th s ar σ G hR hV hP hM hC slbl hlbl length buf ct hct args hlen hargs cap a hca hcv
    extra excaps hI hact hcur htcb (DelE (L := L) th K) psiD (delHyp_full arI th hP (finalHyp_full th hP) hO hPP hPD K hK hK6)
    (fun s1 σ1 hS h => delE_restart hDE hS (ksub_of_eq (setThreadState_nks _ _) h))
    (fun _ _ G1 hCR hE1 => ⟨hE1.2.2.1, hE1.2.2.2 G1 hCR.2.2.1⟩)

end

end

end Fl4Proofs.P3
