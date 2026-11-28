/-
P3 (p3J gen 19): **the hand part of stage K of the stable-ghost interrupt chain** (as P3KFin is for P3KGen).

The stable-ghost finish `jat_finishJRNMSt` (StPostEv) passes its
`hFO : FpuOwnOK σ` to `jat_finishJRN`, which P3KGen's `specK` replaces by P3KFin's `jat_finishJRNI`
(`hFO : FinRootI`): a mechanical copy is rejected by the kernel. Here, by hand:

* **`jat_finishJRNMStQI`**: P3KFin's `jat_finishJRNMQI` (`ArchSwF'`, `hFO : FinRootI`, `MachPlatT`) with
  `jat_finishJRNI`'s last conjunct kept as `JStab Z H Cs` at the same outcome (what `jat_finishJRNMSt` adds to
  `jat_finishJRNM`).

P3JStIrqK maps `jat_finishJRNMSt` ↦ `jat_finishJRNMStQI` (collapse A, Q: formerly its `Fl4ProofsQ` copy); its callers pass the K records' `F.fo`
(`FinRootI`) unchanged. Premises: `jat_finishJRNMQI`'s; no new premise. No sorry. New module.
-/
import Fl4Proofs.P3.P3KFin
import Fl4Proofs.P3.StPostEv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`jat_finishJRNMQI` with the stable ghosts at the same outcome** (module docstring). -/
theorem jat_finishJRNMStQI {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hN : NativeScope σ)
    (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF' st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FinRootI arI AR σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR : MR a σ.machineState) :
    syscall.finish st arI s a ⦃ r => ∃ σ',
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) σ).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  refine WP.spec_mono (WP.spec_and (jat_finishJRNI s a σ J hN hd hnd hAT hVt hmb hA hAN hFO hsni hsend hT hTail hmax
    htu) (MKD.syscall_finish L.total hAT hKD hR)) ?_
  rintro r ⟨⟨_, σ', _, _, hmem, hRJ, V', Ac', Lst', D', J'⟩, hMR⟩
  exact ⟨σ', hmem, hRJ, msF_mrT hM hMR (congrArg Prod.fst (MachT.mtk_finish hmem)), Z.G, V', Ac', Lst', D', J'⟩

end

end

end Fl4Proofs.P3
