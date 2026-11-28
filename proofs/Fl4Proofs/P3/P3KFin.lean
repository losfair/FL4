/-
P3 (line p3J, gen 10): **the old finish chain on the g7e scheduler chain** (hand part of the U41 → U42
transport, P3KGen).

U41's cone runs, besides G7eTail's `kfin_tail_of` (g7e chain, `RootFr`), the pre-g7e path
`KFinAtR5 → KFinAtR31 → KFinAtR27 → KFinAtR` (records) → `jat_finishJRNM` / `jat_finishJRN` / `jat_finishJRP`
→ `jat_scheduleSR2ZRP` / `jat_scheduleFR2ZR` → `jat_scheduleWP0FZR` → ScNextDomCFR's `schedule_refinesWP0FR`,
which applies `ArchSwF`'s idle half at states without `IdleVt`. Here that path is moved onto the g7e chain:

* `FinRootR arI AR σ` (`IdleVt σ` [J], `ArchRefines` [P], `ARKeep`), `FinRootI` (`FpuOwnOK σ` [J] with it).
* Records `KFinAtR5I` / `KFinAtR31I` / `KFinAtR27I` (the originals with `arch : ArchSwF'` and a last field
  `rr : FinRootR`), `KFinAtRI` (`arch : ArchSwF'`, `fo : FinRootI`). Conversions `KFinAtR8.to5I` (from the
  transported `KFinAtR8` / `kfin_tail_of` of P3KGen1; `rr` from `KFinAtR8.idle` and the `hRef`/`hK` it is
  given), `KFinAtR5I.to31I`, `KFinAtR31I.to27I`, `KFinAtR27I.toRI` (`fo := ⟨fo, rr⟩`).
* **`jat_scheduleWP0FZRI`**: `jat_scheduleWP0FZR` with `hFO : FinRootI`, proved on the transported
  `schedule_refinesWP0FRA` (G7eChain on `ArchSwF'`): the fire result pinned (`spec_exists`), `RootFr` by
  `JAtZR.rootFr` at `IdleVt σ1` (`JAtZR.idleVt_fire`), the CR3 conjunct dropped. The non-g7e scheduler chain
  (`schedule_refinesWP0FR`, `cn_*0F`, `scnt_refines0F`, `sw_refinesF`) leaves U41's cone.
* `jat_scheduleFR2ZRI`, `jat_scheduleSR2ZRPI`, `jat_finishJRPI`, `jat_finishJRNI`, `jat_finishJRNMQI` (the
  irqfix copy's statement: `MachPlatT`, `msF_mrT`): text copies (`scratch/p3J/genK2.py`) with `hA : ArchSwF'`
  and `hFO : FinRootI`, the proofs passing them on unchanged.

Named premises: those of the copied lemmas, plus the fields of `FinRootR` (`IdleVt` [J], `ArchRefines` [P],
`ARKeep`), each supplied at `KFinAtR8.to5I` from premises its caller already has. No sorry.
-/

import Fl4Proofs.P3.P3KGen1
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The root facts of a finish state** the g7e scheduler chain needs (module docstring). -/
structure FinRootR (AR : A → Fl4Spec.Cr3 → Prop) (σ : Fl4Spec.State Unit) : Prop where
  /-- [J] `IdleVt` (INV-PLAN §1.U3L D7). -/
  idle : IdleVt σ
  /-- [P] `ArchRefines` (A15). -/
  ref : ArchRefines arI AR
  /-- [P] `ARKeep`. -/
  keep : ARKeep arI AR

/-- **`FpuOwnOK σ` with the root facts**: the old finish record's `fo`. -/
structure FinRootI (AR : A → Fl4Spec.Cr3 → Prop) (σ : Fl4Spec.State Unit) : Prop where
  /-- [J] the FPU owner is a TCB. -/
  fo : FpuOwnOK σ
  rr : FinRootR arI AR σ

structure KFinAtR31I (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  arch : ArchSwF' st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  sni : SniHyp st arI Z.N Z.T Z.C Z.c
  send : SendHyp st arI Z.N Z.T Z.C Z.c
  tail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄
  /-- [J] the idle TCB's vtable (`IdleVt`, from `KFinAtR8.idle`) and the arch premises `ArchRefines` [P] /
  `ARKeep` the g7e scheduler chain needs, carried to the old finish lemmas. -/
  rr : FinRootR arI AR σ

structure KFinAtR27I (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  vt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64
  arch : ArchSwF' st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  sni : SniHyp st arI Z.N Z.T Z.C Z.c
  send : SendHyp st arI Z.N Z.T Z.C Z.c
  tail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄
  /-- [J] the idle TCB's vtable (`IdleVt`, from `KFinAtR8.idle`) and the arch premises `ArchRefines` [P] /
  `ARKeep` the g7e scheduler chain needs, carried to the old finish lemmas. -/
  rr : FinRootR arI AR σ

structure KFinAtRI (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  vt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64
  arch : ArchSwF' st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  fo : FinRootI arI AR σ
  sni : SniHyp st arI Z.N Z.T Z.C Z.c
  send : SendHyp st arI Z.N Z.T Z.C Z.c
  tail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄

end

theorem msF_mrT {A : Type} {arI : machine.Arch A} {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlat arI MR)
    {a : A} {σ σ' : Fl4Spec.State Unit} (hR : MR a σ.machineState) (h : MachF.msF σ' = MachF.msF σ) :
    MR a σ'.machineState := by
  simp only [MachF.msF, Prod.mk.injEq] at h
  exact hM.frame a _ _ hR h.1 h.2.1 h.2.2.1 h.2.2.2.1

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- **FL4's `schedule` from `JAtZR`, with the domain switch, up to the FPU**
(module docstring): no `σ.domainTime ≠ 0`; instead `σ.domainTime ≠ 0 ∨
NdOK s σ` (NdOK's [J] facts at the entry), `ArchNdF` [P] and `FpuOwnOK σ`
[J] at the entry. -/
theorem jat_scheduleWP0FZRI {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI) (P : Fl4Spec.State Unit → Prop)
    (hP : ∀ σ1, Fires σ σ1 → P σ1) (hSig : SignalJHypZRP (L := L) arI P AR H Cs)
    (hA : ArchSwF' st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FinRootI arI AR σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' ∧ NtfnStateRel Z.N Z.T (L.mem r.1) σ' ∧ NSC Z.N Z.C σ' ∧ Inv σ' ∧
      CurInv σ' ∧ ActIdle σ' ∧ ∃ rf : S × A,
        ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
          JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 rf.1 rf.2 σ1) ∧
          timer.fire st arI s a = ok rf ∧ L.ksb rf.1 = L.ksb s ∧ FpuOwnOK σ1) ∧
        P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) ∧
        ∃ σ3 : Fl4Spec.State Unit, OffOK σ3 ∧ (RunM σ1 → RunW σ3) ∧
          Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False) ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hB := J.blk
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hSt : P0.StoreTotal st := P1.LawfulStore.total
  obtain ⟨⟨s1, a1⟩, hfr, ⟨σ1, V1, Ac1, Lst1, D1, h1, hd1, J1⟩, hk⟩ :=
    Fl4Proofs.P3.spec_exists (WP.spec_and (J.fireJ P hP hSig) (P1.timer.fire.kw hAT (P1.ibKeep_holds hAT) hNt s a hB J.bufAtJ))
  simp only [WP.uncurry'_pair] at hk
  have hfire : timer.fire st arI s a ⦃ r => ∃ σ1', Fires σ σ1' ∧ SchedRel st Z.N Z.T Z.C Z.c r.1 σ1' ∧
      NtfnStateRel Z.N Z.T (L.mem r.1) σ1' ∧ NSC Z.N Z.C σ1' ∧ SchedPreW0R Z.T Z.C σ1' ∧
      ((σ1'.domainTime ≠ 0 ∨ NdOK (L := L) r.1 σ1') ∧
        (∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb r.1).val ∨ (L.ksb r.1).val + 13568 ≤ n.val) ∧
        ((((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
          JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 r.1 r.2 σ1') ∧
          timer.fire st arI s a = ok r ∧ L.ksb r.1 = L.ksb s ∧ FpuOwnOK σ1') ∧ VsRootOK Z.T σ1' ∧
          (RootFr (L := L) AR Z.T (Z.mv Z.G V1).P Z.c r.1 r.2 σ1' ∧ AR r.2 σ1'.archState.x64CurrentCr3)))) ⦄ := by
    rw [hfr, WP.spec_ok]
    exact ⟨σ1, h1, J1.xtop.fin.1.1.1, J1.xtop.fin.1.1.2.2.1, J1.nsc, ⟨J1.inv, J1.cur, J1.off, J1.act, J1.own⟩,
      hd.imp (fun h => by rw [hd1]; exact h) (fun h => J.ndOK_fire h hk (fun b hb o ho h8 => (J.bufAtJ.1 b hb).ks o ho h8) h1), J1.nk,
      ⟨⟨V1, Ac1, Lst1, D1, J1⟩, rfl, hk.1, fpuOwnOK_firesZR J h1 J1.xtop.fin.1.1.2.2.1 hFO.fo⟩, J1.vsRootOK,
      J1.rootFr (J.idleVt_fire hAT hFO.rr.idle hfr h1 J1), J1.xtop.fin.1.1.2.2.2.2.2.2⟩
  refine WP.spec_mono (Fl4ProofsK.P3.Sched.schedule_refinesWP0FRA hFO.rr.ref hSt hAT hFO.rr.keep s a σ hS hR J.nsc hnd
    hfire (fun _ _ h => h.1.2.2.2) (fun _ _ h => h.2.1) (fun _ _ h => h.2.2) hA hAN hsni hsend hT) ?_
  rintro r ⟨σ1', σ', hF', hsc, h2, h3, h4, h5, h6, h7, rf, hPf, hw, σ3, h8, h9, h10, -⟩
  exact ⟨σ1', σ', hF', hsc, h2, h3, h4, h5, h6, h7, rf, hPf.1, hw, σ3, h8, h9, h10⟩

set_option maxHeartbeats 4000000 in
/-- **FL4's `schedule` refines the spec's at `J`, with the domain switch**
(module docstring): `jat_scheduleFRF` without `σ.domainTime ≠ 0`. -/
theorem jat_scheduleFR2ZRI {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (P : Fl4Spec.State Unit → Prop) (hP : ∀ σ1, Fires σ σ1 → P σ1) (hSig : SignalJHypZRP (L := L) arI P AR H Cs)
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
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
      (∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ') ∧ CurInv σ' ∧ CurRunW σ' ⦄ := by
  have h0Cs : 0#u64 ∈ Cs := J.kern.cs0
  have hB := J.blk
  obtain ⟨⟨Q, R, hq⟩, hBd, hXi, hSc, hSg⟩ := id hB
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    P1.nodeAt_aligned (hq.nodes 0#u64 h0Cs) (by simp) (by simp)
  -- g7a: the `DOM_SCHED_IDX` word stays 0 (SchedIdx)
  have hIdx := P1.sched.schedule.idx hAT (P1.ibKeep_holds hAT) hNt s a hB J.kern.ksbFit J.kern.ksbAl
    (J.kwApartJ (s' := s) rfl (fun c hc => J.blk.2.2.1.2.2.tm.npl c hc)) J.bufAtJ
    (fun s1 hf1 => fire_ks_of J.kern.ksbFit J.kern.ksbAl J.kern.hks J.kern.heap
      (J.kwApartJ (s' := s) rfl (fun c hc => J.blk.2.2.1.2.2.tm.npl c hc)) (fun c hc => J.blk.2.2.1.2.2.tm.npl c hc) hf1
      (fun b hb o ho h8 => (J.bufAtJ.1 b hb).ks o ho h8))
    (idxI_of J.xtop.rel.2.2.2.1 J.xtop.fin.1.1.1 hd)
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and
    (jat_scheduleWP0FZRI s a σ J hd hnd hAT P hP hSig hA hAN hFO hsni hsend hT)
    (P1.sched.schedule.kw hAT (P1.ibKeep_holds hAT) hNt s a hB J.bufAtJ)) (WP.spec_and (P1.sched.schedule.tinv hAT (P1.ibKeep_holds hAT) hNt s a Q R hq hBd hSc hXi hSg J.bufAtJ)
      hTail)) hIdx) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨⟨σ1, σ', hF, hsc, hS', hR', hN', hI', hC', hA', rf, ⟨⟨V1, Ac1, Lst1, D1, J1⟩, hfr, hkf, -⟩, hw, hrun⟩,
    hkw⟩, ⟨htinv, hRest⟩⟩, h24'⟩
  simp only [WP.uncurry'_pair] at hkw htinv h24'
  obtain ⟨rf', hrf', -, hkw⟩ := hkw
  obtain rfl : rf = rf' := by simpa using (hrf'.symm.trans hfr).symm
  have hTl := hRest rf σ1 σ' D1 hF hfr (Or.inl ⟨V1, Ac1, Lst1, D1, J1⟩) hsc hw hS' hI' hC' hA'
  obtain ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', -, -, -, -⟩ := htinv
  -- the fake pre-state
  have hkf1 := J1.kern.ksbFit
  have hka1 := J1.kern.ksbAl
  set kb := L.ksb rf.1 with hkb
  set s0 := ndF (L := L) rf.1 kb (L.mem s' (ksW kb 16#u64)) (L.mem s' (ksW kb 24#u64)) (L.mem s' (ksW kb 40#u64))
    with hs0
  set σ0 := ndFSt σ1 (L.mem s' (ksW kb 16#u64)).bv σ'.domainIndex with hσ0
  obtain ⟨Ac0, Lst0, D0, J0⟩ := J1.ndFJ (L.mem s' (ksW kb 16#u64)) (L.mem s' (ksW kb 24#u64))
    (L.mem s' (ksW kb 40#u64)) σ'.domainIndex (by rw [← hkf] at h24'; exact h24')
  have hw0 : P1.WritesIn st s0 s' (KFoot st Z.T Z.N Z.C Z.c s0 σ0) := ndF_writes σ'.domainIndex hkf1 hka1 hw
  have hk0 : L.ksb s0 = L.ksb rf.1 := ndF_ksb _ _ _ _ _
  have hks' : L.ksb s' = L.ksb s := hkw.1.trans hkf
  have hnA : L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb (hk0.trans hkf) _ _
  have hnA1 : L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb hkf _ _
  have hN0 := hq.nodes 0#u64 h0Cs
  have hdv : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val = L.nodeBase s 0#u64 + 88 := by
    rw [P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp), P1.debug_val]
  have hdbg0 : L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem rf.1 (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS) := by
    rw [hnA, hnA1, hs0]
    refine ndF_mem_ne _ _ _ _ hkf1 hka1 hal fun hb => ?_
    have h16 := ksW_val (kb := kb) (o := 16#u64) (by simp; omega)
    have h24 := ksW_val (kb := kb) (o := 24#u64) (by simp; omega)
    have h40 := ksW_val (kb := kb) (o := 40#u64) (by simp; omega)
    have hkbs : kb.val = (L.ksb s).val := by rw [hkf]
    unfold P1.LawfulStore.nodeBase at hdv
    rcases hb with e | e | e <;> have := congrArg UScalar.val e <;> simp at h16 h24 h40 <;> omega
  have hdbg : L.mem s' (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s0 (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) := by
    rw [hdbg0, P1.nodeAt_of_ksb hk0]
    exact hkw.mem_eq (by rw [hnA1]; exact hal) (P1.dbg0_not_schedW J1.blk h0Cs)
  have hdw : (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS).val ≠ (P1.stA (L.curW s')).val := by
    have hN0' := hq'.nodes 0#u64 h0Cs
    have hct : L.curW s' ∈ P1.Heap.tcbs H := hq'.curT
    have hv := P1.nodeAt_val hN0' (off := layout.node.DEBUG_TCBS) (by simp)
    have hsv := P1.field_val (hq'.tcbs _ hct) (K := 3328#u64) (by decide)
    have hdj := hN0'.disj _ hct
    have hv' : (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS).val = L.nodeBase s' 0#u64 + 88 := by
      rw [hnA, ← P1.nodeAt_of_ksb hks' 0#u64 layout.node.DEBUG_TCBS, hv, P1.debug_val]
    have hsv' : (P1.stA (L.curW s')).val = (L.curW s').val + 3328 := by
      rw [P1.stA_eq, hsv]; rfl
    rw [hv', hsv']
    have e12 : (2 : Nat) ^ 12 = 4096 := rfl
    rw [e12] at hdj
    omega
  obtain ⟨σ3, ho3, hr3, he3⟩ := hrun
  have hSch1 : SchS σ1 σ' := schs_schedule.of_eq hsc
  have hSch0 : SchS σ0 σ' := SchS.ndF hSch1 _ _
  have hK1 : SchStep (fun _ => False) σ0 σ' := hSch0.1
  have hL1 : LK (fun _ => False) σ0 σ' := lkm_schedule σ1 ((), σ') (by rw [hsc]; exact Set.mem_singleton _)
  have hik : σ'.idleThread = σ0.idleThread ∧ σ'.idleSc = σ0.idleSc :=
    ik_schedule σ1 ((), σ') (by rw [hsc]; exact Set.mem_singleton _)
  have hwT := WritesIn.tfoot_of_kfoot hw0
  have hSS : SlotsSame Z.th (L.mem s0) (L.mem s') :=
    slotsSame_of_iw J0.xtop.rel.1 J0.xtop.rel.2.2.2.2.2.1 J0.xtop.rel.2.2.2.2.2.2 hwT
      fun b hb => tfoot_iw J0.xtop.fin.1.1.1 hb
  obtain ⟨Qc, Rc, hcc, hsc'⟩ := hS'.lists
  obtain ⟨hth, hvt⟩ := hVt _ _ _ _ _ _ _ J0 _ hcc.curT
  have hcur : Vs.CurOK st Z.th s' σ' :=
    ⟨_, hsc'.curThread.symm, hth, fun p asid h => hvt p asid (by
      rwa [hSS.capAt ⟨_, 1, Or.inr ⟨hth, by decide⟩, rfl⟩] at h)⟩
  have hX' : XTopAt (L := L) AR (Z.mv Z.G V1) s' a' σ' :=
    xtop_sched_step J0.xtop J0.ip J0.nk hwT (ct := σ0.curThread)
      { hK1 with kh := fun p => (hK1.kh p).mono False.elim } hS' hR' hcur hTl.ar
  have hSOK0 := hSch0.2
  have hY1 : YieldRel Z.T Z.C (L.mem s') σ' :=
    (ScAll.of_k J0.xtop.fin.1.1.1 J0.rp J0.yld J0.mcp J0.call J0.rfree ⟨⟨hS', hR', hN', hI'⟩, hw0, hSOK0⟩).2.1
  have hdead : ∀ q ∈ D0, Sched.DeadP (L := L) H s' q := fun q hq =>
    J0.deadP_sch_step hX' hwT hK1 hL1 hA' (J0.ymd hS' hY1 ((hSOK0.ykeep rfl).dk q.bv)) (fun h => h)
      (J0.jcov.dead q hq)
  -- every debug word kept from the fake pre-state (`ndF` writes kernel-state words only)
  have hdk0 : P1.DbgKeep st (P1.Heap.tcbs H) Cs s0 s' := by
    have h1 := P1.dbgKeep_schedW J1.blk J1.kern.ksbFit hkw
    obtain ⟨⟨Qk, Rk, hqk⟩, -⟩ := J1.blk
    refine ⟨hkw.1.trans hk0.symm, fun b hb => ?_⟩
    have hb1 : P1.DbgW st (P1.Heap.tcbs H) Cs rf.1 b := P1.DbgW.ksb hk0 hb
    rw [h1.2 b hb1]
    refine (ndF_mem_ne _ _ _ _ hkf1 hka1 (P1.dbgW_aligned J1.blk hb1) fun hn => ?_).symm
    have h16 := ksW_val (kb := kb) (o := 16#u64) (by simp; omega)
    have h24 := ksW_val (kb := kb) (o := 24#u64) (by simp; omega)
    have h40 := ksW_val (kb := kb) (o := 40#u64) (by simp; omega)
    simp at h16 h24 h40
    have hbv : b.val = kb.val + 16 ∨ b.val = kb.val + 24 ∨ b.val = kb.val + 40 := by
      rcases hn with e | e | e <;> rw [e] <;> omega
    rcases hb1 with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
    · have hv := P1.field_val (hqk.tcbs y hy) (K := 3576#u64) (by simp)
      have ho := hqk.ksOut y hy
      rw [← hkb] at ho
      have h35 : (3576#u64 : U64).val = 3576 := by simp
      have e' : b.val = y.val + 3576 := by
        rw [e, show P1.dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, hv, h35]
      simp only [Nat.reducePow] at ho
      omega
    · have hv := P1.field_val (hqk.tcbs y hy) (K := 3584#u64) (by simp)
      have ho := hqk.ksOut y hy
      rw [← hkb] at ho
      have h35 : (3584#u64 : U64).val = 3584 := by simp
      have e' : b.val = y.val + 3584 := by
        rw [e, show P1.dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, hv, h35]
      simp only [Nat.reducePow] at ho
      omega
    · have hN := hqk.nodes c hc
      have hv : b.val = L.nodeBase rf.1 c + 88 := by
        rw [e, P1.nodeAt_val hN (off := layout.node.DEBUG_TCBS) (by simp), P1.debug_val]
      have hnb : L.nodeBase rf.1 c = (L.ksb rf.1).val + 13568 + c.val * 4288 := rfl
      rw [← hkb] at hnb
      omega
  have hT2 : SchTailHyps (L := L) AR (Z.mv Z.G V1) H Cs D0 s0 s' a' σ' Ac :=
    ⟨hcur, hTl.ar, hdbg, hdw, hdead,
      ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', hSg.ksb' hks'⟩, hdk0⟩
  obtain ⟨Lst', J'⟩ := J0.sch_tailS hSch0 hik hw0 hS' hR' hN' hI' hC' hA' (RunW.scAndTimer (hr3 J1.curRun) he3)
    (OffOK.scAndTimer ho3 he3) (bsa_schedule J1.bsa hsc) hT2
  exact ⟨σ1, σ', hF, hsc, ⟨J'.xtop.relTop, _, _, _, _, _, _, J'.toJ (Or.inr hC'), inferInstance⟩, ⟨V1, Ac, Lst', D0, J'⟩, hC',
    RunW.scAndTimer (hr3 J1.curRun) he3⟩

/-- **`jat_scheduleFR2ZR` with `SignalJHypZR` reduced to the waking signals**
(`signalJHyp_ofZR`, as `jat_scheduleSRF`), at the states satisfying `P` (g3b). -/
theorem jat_scheduleSR2ZRPI {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (P : Fl4Spec.State Unit → Prop) (hP : ∀ σ1, Fires σ σ1 → P σ1)
    (hW : SignalRestJHypZRP (L := L) arI P AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
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
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
      (∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ') ∧ CurInv σ' ∧ CurRunW σ' ⦄ :=
  jat_scheduleFR2ZRI s a σ J hd hnd hAT hVt P hP (signalJHyp_ofZR hAT P hW hmb) hA hAN hFO hsni hsend hT hTail

/-- **FL4's `finish` from `JAtZR`** (module docstring): `jat_finishJ2` with
`jat_scheduleSR2ZRP`, the signal and `RunningVM` cases only at the states the
path reaches (g3b): `P` along the fired timers (`hP`), `hvm` at the state
after `schedule`. -/
theorem jat_finishJRPI {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (P : Fl4Spec.State Unit → Prop) (hP : ∀ σ1, Fires σ σ1 → P σ1)
    (hW : SignalRestJHypZRP (L := L) arI P AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
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
    (hvm : ∀ σ1 σ2 s1 a1, Fires σ σ1 → Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ2)}, False) →
      JAt (L := L) arI AR s1 a1 σ2 → ∀ x, σ2.kheap σ2.curThread = some (.tcb x) → x.tcbState ≠ .runningVM) :
    syscall.finish st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), ((), σ1) ∈ (Fl4Spec.fl4Awaken (Z := Unit) σ).1 ∧
      (Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1 = ({((), σ')}, False) ∧
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) σ).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  refine P1.finish_of_old arI ?_
  unfold syscall.finish_old
  refine WP.spec_bind (jat_scheduleSR2ZRPI s a σ J hd hnd hAT hVt P hP hW hmb hA hAN hFO hsni hsend hT hTail) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, σ2, hF, hsc, -, ⟨V1, Ac1, Lst1, D1, J1R⟩, hC2, hcr⟩
  have J1 := J1R.toJ (Or.inr hC2)
  refine WP.spec_mono (J1.activateJV hAT hmax (htu a1) hcr (hvm σ1 σ2 _ _ hF hsc ⟨_, _, _, _, _, _, J1, inferInstance⟩)) ?_
  rintro r ⟨σ', ha, hRJ, V2, Ac2, Lst2, D2, J2, hnv⟩
  refine ⟨?_, J2.cur_not_vm hnv⟩
  have hsa : (Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1 = ({((), σ')}, False) := by
    rw [Notif.nd_bind_one hsc]; exact ha
  refine ⟨σ1, σ', mem_fl4Awaken_of hF, hsa, ⟨((), σ1), mem_fl4Awaken_of hF, ?_⟩, hRJ, V2, Ac2, Lst2, D2, J2⟩
  show ((), σ') ∈ ((Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1).1
  rw [hsa]; exact Set.mem_singleton _

set_option maxHeartbeats 4000000 in
/-- **FL4's `finish` from `JAtZR` with `NativeScope` at its own state** (module
docstring): `jat_finishJRP` at `P := NativeScope`: along the fired timers by
`ns_fl4Awaken` (the signal step's `RunningVM` case is then absurd), after
`schedule` by `ns_schedule` (`hvm`). -/
theorem jat_finishJRNI {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
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
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.finish st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), ((), σ1) ∈ (Fl4Spec.fl4Awaken (Z := Unit) σ).1 ∧
      (Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1 = ({((), σ')}, False) ∧
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) σ).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ :=
  jat_finishJRPI s a σ J hd hnd hAT hVt (fun σ1 => NativeScope σ1)
    (fun σ1 h => SInv.ns_fl4Awaken σ hN ((), σ1) (mem_fl4Awaken_of h))
    (fun _ _ _ _ _ _ _ _ _ _ _ hP _ _ ⟨_, t, tcb, _, hkt, hvm⟩ => absurd hvm (hP t tcb hkt)) hmb
    hA hAN hFO hsni hsend hT hTail hmax htu
    (fun σ1 σ2 _ _ hF hsc _ x hk =>
      SInv.ns_schedule σ1 (SInv.ns_fl4Awaken σ hN ((), σ1) (mem_fl4Awaken_of hF)) ((), σ2)
        (by rw [hsc]; exact Set.mem_singleton _) _ x hk)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`jat_finishJRN` with `MR` after** (module docstring). -/
theorem jat_finishJRNMQI {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
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
      RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ⦄ := by
  refine WP.spec_mono (WP.spec_and (jat_finishJRNI s a σ J hN hd hnd hAT hVt hmb hA hAN hFO hsni hsend hT hTail hmax
    htu) (MKD.syscall_finish L.total hAT hKD hR)) ?_
  rintro r ⟨⟨_, σ', _, _, hmem, hRJ, _⟩, hMR⟩
  exact ⟨σ', hmem, hRJ, msF_mrT hM hMR (congrArg Prod.fst (MachT.mtk_finish hmem))⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

theorem KFinAtR31I.to27I {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (F : KFinAtR31I (L := L) arI AR Z H Cs s a σ) : KFinAtR27I (L := L) arI AR Z H Cs s a σ :=
  ⟨F.hd, vtAsid_ofR arI AR Z H Cs, F.arch, F.archNd, F.sni, F.send, F.tail, F.rr⟩

theorem KFinAtR27I.toRI {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (F : KFinAtR27I (L := L) arI AR Z H Cs s a σ) (fo : FpuOwnOK σ) :
    KFinAtRI (L := L) arI AR Z H Cs s a σ :=
  ⟨F.hd, F.vt, F.arch, F.archNd, ⟨fo, F.rr⟩, F.sni, F.send, F.tail⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

structure KFinAtR5I (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  arch : ArchSwF' st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  tail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄
  /-- [J] the idle TCB's vtable (`IdleVt`, from `KFinAtR8.idle`) and the arch premises `ArchRefines` [P] /
  `ARKeep` the g7e scheduler chain needs, carried to the old finish lemmas. -/
  rr : FinRootR arI AR σ

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

theorem KFinAtR5I.to31I {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (hA : P0.ArchTotal arI) (hD : SetDlDet) (F : KFinAtR5I (L := L) arI AR Z H Cs s a σ) :
    KFinAtR31I (L := L) arI AR Z H Cs s a σ :=
  ⟨F.hd, F.arch, F.archNd, sniHyp_of hA hD, sendHyp_of hA, F.tail, F.rr⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

theorem KFinAtR8.to5I {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hK : ARKeep arI AR) (hRef : ArchRefines arI AR) (hD : SetDlDet) (hT : TimeAgree arI)
    (F : Fl4ProofsK.P3.SInvR.G5.KFinAtR8 (L := L) arI AR Z H Cs s a σ) (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hFO : FpuOwnOK σ) : KFinAtR5I (L := L) arI AR Z H Cs s a σ :=
  ⟨F.hd, F.arch, F.archNd,
    Fl4ProofsK.P3.SInvR.G5.kfin_tail_of J F.hd hnd hAT hK hRef F.arch F.archNd (sniHyp_of hAT hD) (sendHyp_of hAT) hT hFO F.idle, ⟨F.idle, hRef, hK⟩⟩

end

end

end Fl4Proofs.P3.SInvR.G5
