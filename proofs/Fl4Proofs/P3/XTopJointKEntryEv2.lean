/-
P3 (DESIGN.md §9), invariant line G4 (g4f, KENTRY-PLAN g4f; g4e's handoff):
**event entries at `J`**.

* `JAtZ.utCheckB`: FL4's `update_timestamp; check_budget` (the interrupt
  entry's prefix) at an `Entered` `JAtZ` state under `KBudgetB`, every
  outcome: l4v's `update_time_stamp; check_budget` returns the same flag and
  `JAtZ` holds after (XTopJointPP's `timestampJ` for the sufficient head,
  ScChargeH's `timestampJH` and the hole's `checkBudgetF` / `checkBudgetT` /
  `checkBudgetTR` for the charge: `budgetOkB`'s cases without the restart).
-/
import Fl4Proofs.P3.XTopJointKEntryEv
import Fl4Proofs.P3.SpecInvG4f
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## `update_timestamp; check_budget` at `J` -/


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`update_timestamp; check_budget` at an entry state** (module
docstring). -/
theorem JAtZ.utCheckB {s : S} {a : A} {σ0 : Fl4Spec.State Unit}
    (J0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ0) (hni0 : Entered σ0) (hBu : KBudgetB arI a σ0)
    (hNS0 : NativeScope σ0) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    (do let (s1, a1) ← sched.update_timestamp st arI s a; sched.check_budget st arI s1 a1) ⦃ r =>
      ∃ z ∈ ((Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudget) σ0).1, z.1 = r.1 ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2 ⦄ := by
  have hnow := hBu.now
  have hS := J0.xtop.fin.1.1.1
  have hR := J0.xtop.fin.1.1.2.2.1
  have hnow' : arI.now a ⦃ r => ∃ ms, Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getCurrentTime σ0 =
      ({(r.1.bv, { σ0 with machineState := ms })}, False) ∧ σ0.curTime ≤ r.1.bv ⦄ :=
    WP.spec_mono hnow fun _ ⟨ms, h1, h2, _⟩ => ⟨ms, h1, h2⟩
  refine WP.spec_bind (WP.spec_and (WP.spec_and (J0.timestampJ arI hAK hA hnd hnow) (J0.timestampJH hAK hA hnd hnow))
    (update_timestamp_refines s a σ0 hS hR J0.nsc hnd hnow')) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨σ1, h1, -, -, -, -, -, hum1, hO1, hJ1⟩, ⟨σ1', h1', -, -, -, -, -, hum1', -, hH⟩⟩,
    ⟨σ1'', h1'', hS1, -, -, hI1, hC1, -, -⟩⟩
  have e1 : σ1 = σ1' := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj (h1.symm.trans h1')).1)
  have e2 : σ1 = σ1'' := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj (h1.symm.trans h1'')).1)
  subst e1 e2
  have hsp0 : ∀ y, y ∈ (Fl4Spec.checkBudget (Z := Unit) σ1).1 →
      y ∈ ((Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudget) σ0).1 := by
    intro y hy; rw [Notif.nd_bind_one h1]; exact hy
  have Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s a σ0 s1 a1 σ1 := hH σ1.machineState a1 hum1' id
  have hI1 := hI1 J0.inv
  have hC1 := hC1 hBu.cur
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS1 hI1 hC1
  obtain ⟨-, -, -, -, ekh, ect, eact, eidle, -, -, -, -⟩ := Hh.sfacts
  obtain ⟨ms1, tm1, cn1, -, eσ1⟩ := Hh.spec
  have erq : σ1.readyQueues = σ0.readyQueues := by rw [eσ1]
  have ecs : σ1.curSc = σ0.curSc := by rw [eσ1]
  have hres1 : σ1.schedulerAction = .resumeCurThread := eact.trans hni0.2
  have hCH : CurInv σ1 := Hh.cur.resolve_left (by rw [hres1]; exact fun h => by cases h)
  have hni1 : σ1.curThread ≠ σ1.idleThread := by rw [ect, eidle]; exact hni0.1
  have hnsw1 : σ1.schedulerAction ≠ .switchThread σ1.curThread := by rw [hres1]; exact fun h => by cases h
  -- the charge (the head is insufficient)
  have hFalse : sched.check_budget st arI s1 a1 ⦃ r => r.1 = false →
      ∃ z ∈ (Fl4Spec.checkBudget (Z := Unit) σ1).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2 ⦄ := by
    by_cases hnt : NoTmoSend σ1
    · refine WP.spec_mono (Hh.checkBudgetF hA hCH hni1 hnsw1 (hmrt a1) (hmb a1) hnt) ?_
      rintro ⟨rb, s2, a2⟩ hB hf
      obtain ⟨ea, σ2, hcb, -, Lst2, J2⟩ := hB hf
      simp only at ea J2
      subst ea
      exact ⟨(false, σ2), by rw [hcb]; exact Set.mem_singleton _, rfl, Z, Ac, Lst2, D, J2⟩
    have hnq1 : ∀ d q, σ1.curThread ∉ σ1.readyQueues d q := by
      rcases hBu.tmo with hnt0 | hnq0
      · exact absurd (hnt0.of_eq ekh ect ecs) hnt
      · rw [ect, erq]; exact hnq0
    unfold NoTmoSend at hnt
    push_neg at hnt
    obtain ⟨⟨xt, hkt, hep⟩, ⟨y, m, hky, hy⟩⟩ := hnt
    have hper : ∀ x n, σ1.kheap σ1.curSc = some (.schedContext x n) → x.scPeriod ≠ 0 := fun x n h => by
      rw [hky] at h; cases h; exact hy
    obtain ⟨p, bd, rr, hth⟩ : ∃ p bd rr, xt.tcbTimeoutHandler = .endpointCap p bd rr := by
      revert hep; cases xt.tcbTimeoutHandler <;> simp [Fl4Spec.isEpCap]
    have hkt0 : σ0.kheap σ0.curThread = some (.tcb xt) := by rw [← ekh, ← ect]; exact hkt
    have hrr : xt.tcbState = .running ∨ xt.tcbState = .restart := by
      have hrun := J0.curRun.run hni0 xt hkt0
      have hvm := hNS0 _ xt hkt0
      revert hrun hvm; cases xt.tcbState <;> simp [Fl4Spec.runnable]
    by_cases hkl : ∃ l, σ1.kheap p = some (.endpoint (.recvEP l))
    · refine WP.spec_mono (Hh.checkBudgetTR hA hmax htu hCH hni1 (Or.inl hres1) hnq1 (hmrt a1) (hmb a1) hkt hrr
        hth hper hkl) ?_
      rintro r hB hf
      obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := hB hf
      exact ⟨z, hz, hz1, _, Ac', Lst', D', J'⟩
    · have hcb : ∀ xe, σ1.kheap p = some (.endpoint xe) → Endp.CanBlock false xe := fun xe h => by
        cases xe with
        | idleEP => trivial
        | sendEP q => rfl
        | recvEP q => exact absurd ⟨q, h⟩ hkl
      refine WP.spec_mono (Hh.checkBudgetT hA hCH hni1 hres1 hnq1 (hmrt a1) (hmb a1) hkt hrr hth hper hcb) ?_
      rintro r hB hf
      obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := hB hf
      exact ⟨z, hz, hz1, _, Ac', Lst', D', J'⟩
  refine WP.spec_mono (WP.spec_and (check_budgetT hA s1 a1 σ1 hS1 hscC hact (hmb a1)) hFalse) ?_
  rintro ⟨rb, s2, a2⟩ ⟨hT, hF⟩
  cases rb with
  | false =>
    obtain ⟨z, hz, hz1, Z', Ac', Lst', D', J'⟩ := hF rfl
    exact ⟨z, hsp0 z hz, hz1, Z', Ac', Lst', D', J'⟩
  | true =>
    obtain ⟨e, hb, hsuf⟩ := hT rfl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    have hOR1 : OffReady σ1 := hO1 hBu.off
    have hOK : OffOK σ1 := hOR1.ok hsuf
    have hOw : CurOwnW Z.T Z.C σ1 := Or.inl (curOwn_of_curInv hS1 hI1 hC1)
    obtain ⟨-, hJ⟩ := hJ1 σ1.machineState _ hum1 id
    obtain ⟨Ac', Lst', D', J'⟩ := hJ hOK hOw
    exact ⟨(true, σ1), hsp0 _ (by rw [checkBudget_suff hnd hb]; exact Set.mem_singleton _), rfl, Z, Ac', Lst', D', J'⟩

end


/-! ## `handle_interrupt` at `J` with `MR` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

theorem setWidth8_eq {w : U64} {i : Fl4Spec.Irq} (hwi : w.val = i.toNat) : w.bv.setWidth 8 = i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth]
  show w.val % 2 ^ 8 = _
  rw [hwi]; exact Nat.mod_eq_of_lt i.isLt

set_option maxHeartbeats 16000000 in
/-- **MRPath's `handleIrqJIAN` with `MR` after** (module docstring): the masks
FL4 writes are the spec's (`MachPlat.mask`), the acknowledgements and the
signal keep `MR` (`MachPlat.ack`, MachKeep's `MRKeep`; the spec's
`sendSignal` keeps `msF`). -/
theorem JAtZ.handleIrqJIM (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlatA arI AR)
    (hM : MachPlat arI MR) (hK : MRKeep arI MR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hN : NativeScope σ) (hR : MR a σ.machineState)
    (w : U64) (i : Fl4Spec.Irq) (hwi : w.val = i.toNat) (hw256 : w.val < 256) (h126 : w.val ≠ 126)
    (h127 : w.val ≠ 127) :
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      σ.interruptStates i = .irqInactive ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ∧
          MR r.2 z.2.machineState ⦄ := by
  have hX := J.xtop
  have hIR : IrqRel (L.mem s) (L.ksb s) σ := hX.fin.1.1.2.2.2.1
  have hARa : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  have hiw : (BitVec.ofNat 8 w.val : Fl4Spec.Irq) = i := by
    apply BitVec.eq_of_toNat_eq; simp [hwi]
  have hwb : w.bv.setWidth 8 = i := setWidth8_eq hwi
  have hmaskM : ∀ (a0 a1 : A) (σ0 : Fl4Spec.State Unit), MR a0 σ0.machineState →
      arI.mask_irq a0 w true = ok a1 → MR a1 (maskMs σ0 i true).machineState := by
    intro a0 a1 σ0 h0 he
    have hm := hM.mask a0 w true σ0.machineState h0 hw256
    rw [he, WP.spec_ok, hwb] at hm
    exact hm
  -- the acknowledgement keeps `JAt` and `MR`
  have hack : ∀ (s1 : S) (a1 : A) (z : Unit × Fl4Spec.State Unit),
      z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1 → JAt (L := L) arI AR s1 a1 z.2 → MR a1 z.2.machineState →
      (do let a2 ← arI.ack_irq a1 w; ok (s1, a2)) ⦃ r =>
        σ.interruptStates i = .irqInactive ∨
          ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ∧
            MR r.2 z.2.machineState ⦄ := by
    rintro s1 a1 z hz ⟨Z1, H1, Cs1, Ac1, Lst1, D1, J1⟩ hm1
    refine WP.spec_bind (WP.spec_and (hIP.ackAR a1 w _ J1.xtop.fin.1.1.2.2.2.2.2.2) (hM.ack a1 w _ hm1)) ?_
    rintro a2 ⟨hA2, hM2⟩
    obtain ⟨Lst2, J2⟩ := J1.msArJ z.2.machineState a2 rfl (fun _ => hA2)
    exact (WP.spec_ok _).2 (Or.inr ⟨z, hz, ⟨Z1, H1, Cs1, Ac1, Lst2, D1, J2⟩, hM2⟩)
  unfold interrupt.handle_interrupt
  rw [irq_max_eq]
  simp only [bind_ok]
  by_cases hbig : w > 127#u64
  · -- above FL4's maximum
    rw [if_pos hbig]
    have hgt : i > Fl4Spec.maxIRQ := by
      have : 127 < w.val := hbig
      show (125 : BitVec 8) < i
      rw [BitVec.lt_def]; simp; omega
    obtain ⟨a1, ha1⟩ := maskIrq_total arI hAT a w true
    have hm1 := hmaskM a a1 σ hR ha1
    rw [ha1]
    simp only [bind_ok]
    have hA1 : AR a1 σ.archState.x64CurrentCr3 := hARI.mask _ _ _ hARa (Or.inr (Or.inl ⟨w, true, ha1⟩))
    obtain ⟨Lst1, J1⟩ := J.msArJ (maskMs σ i true).machineState a1 rfl (fun _ => hA1)
    exact hack s a1 _ (mem_hi_big hgt σ) ⟨Z, H, Cs, Ac, Lst1, D, J1⟩ hm1
  · rw [if_neg hbig]
    have hw : w.val ≤ 125 := by
      have : ¬ 127 < w.val := hbig
      omega
    have hw128 : w.val < 128 := by omega
    have hle : ¬ i > Fl4Spec.maxIRQ := by
      show ¬ (125 : BitVec 8) < i
      rw [BitVec.lt_def]; simp; omega
    have hst : σ.interruptStates i = irqSt (L.mem s (irqStA (L.ksb s) w)) := by
      rw [← hiw]; exact hIR.st w hw128
    rw [irq_state_eq']
    simp only [bind_ok, irqSig_eq, irqTimer_eq, irqIpi_eq, irqInactive_eq]
    set v := L.mem s (irqStA (L.ksb s) w) with hv
    -- the branches before the acknowledgement
    have key : ∀ m : Result (S × A), m ⦃ r => σ.interruptStates i = .irqInactive ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ∧
          MR r.2 z.2.machineState ⦄ →
        (do let (s1, a1) ← m; let a2 ← arI.ack_irq a1 w; ok (s1, a2)) ⦃ r =>
          σ.interruptStates i = .irqInactive ∨
            ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ∧
              MR r.2 z.2.machineState ⦄ := by
      intro m hm
      refine WP.spec_bind hm ?_
      rintro ⟨s1, a1⟩ (hf | ⟨z, hz, hJ1, hm1⟩)
      · refine WP.spec_bind (hAT.ack_irq a1 w) ?_
        intro a2 _
        exact (WP.spec_ok _).2 (Or.inl hf)
      · exact hack s1 a1 z hz hJ1 hm1
    refine key _ ?_
    by_cases h1 : v = 1#u64
    · -- a signal line
      rw [if_pos h1]
      have hsig : σ.interruptStates i = .irqSignal := by rw [hst, h1]; rfl
      have hL : IntLayout Z.th (L.ksb s) := J.intL
      have hnode := hL.node w hw128
      obtain ⟨cs, hkc, hwf, hsl⟩ := hX.rel.2.1.1.cnode _ 0 hnode
      obtain ⟨c, ac, hcap, hcs, hCR⟩ := hsl [] rfl
      rw [show slotAddr (nodeA (L.ksb s) w).bv (Fl4Spec.ofBl []) = nodeA (L.ksb s) w from
        cslotAddr_nil _] at hcap
      have hgc : Fl4Spec.getCap (Z := Unit) (σ.interruptIrqNode i, []) σ = ({(ac, σ)}, False) := by
        rw [← hiw, hIR.node w hw128]; exact getCap_cnode hkc hwf hcs
      have hac : ac = absCap c := hCR.abs
      rw [irq_slot_eq]
      simp only [bind_ok]
      rw [slot_cap_eq, hcap]
      simp only [bind_ok]
      -- the mask after the cap's case
      have hmask : ∀ (s3 : S) (a2 : A) (σ1 : Fl4Spec.State Unit),
          ((), σ1) ∈ (Fl4Spec.NonDet.when (Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac)
            (Fl4Spec.sendSignal (Z := Unit) (Fl4Spec.objRefOf ac) (Fl4Spec.capEpBadge ac)) σ).1 →
          JAt (L := L) arI AR s3 a2 σ1 → MR a2 σ1.machineState →
          (do let a3 ← arI.mask_irq a2 w true; ok (s3, a3)) ⦃ r =>
            σ.interruptStates i = .irqInactive ∨
              ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ∧
                MR r.2 z.2.machineState ⦄ := by
        rintro s3 a2 σ1 h1' ⟨Z1, H1, Cs1, Ac1, Lst1, D1, J1⟩ hm2
        obtain ⟨a3, ha3⟩ := maskIrq_total arI hAT a2 w true
        have hm3 := hmaskM a2 a3 σ1 hm2 ha3
        rw [ha3]
        simp only [bind_ok, WP.spec_ok]
        have hA3 := hARI.mask _ _ _ J1.xtop.fin.1.1.2.2.2.2.2.2 (Or.inr (Or.inl ⟨w, true, ha3⟩))
        obtain ⟨Lst3, J3⟩ := J1.msArJ (maskMs σ1 i true).machineState a3 rfl (fun _ => hA3)
        exact Or.inr ⟨((), maskMs σ1 i true), mem_hi_signal hle hsig hgc h1', ⟨Z1, H1, Cs1, Ac1, Lst3, D1, J3⟩,
          hm3⟩
      have hnone : ∀ (hP : ¬ (Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac)),
          (do let a3 ← arI.mask_irq a w true; ok (s, a3)) ⦃ r =>
            σ.interruptStates i = .irqInactive ∨
              ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ∧
                MR r.2 z.2.machineState ⦄ :=
        fun hP => hmask s a σ (mem_when_false hP _ σ) ⟨Z, H, Cs, Ac, Lst, D, J⟩ hR
      cases c with
      | Notification p b sd rv =>
        cases sd with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
          exact hnone (by rw [hac]; simp [absCap, Fl4Spec.isNtfnCap, Fl4Spec.capRights, Fl4Spec.AllowSend, rightsOf])
        | true =>
          simp only [↓reduceIte]
          have hP : Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac := by
            rw [hac]; exact ⟨rfl, rfl⟩
          have hobj : Fl4Spec.objRefOf ac = p.bv := by rw [hac]; rfl
          have hbd : Fl4Spec.capEpBadge ac = b.bv := by rw [hac]; rfl
          have hwhen : ∀ σ1, ((), σ1) ∈ (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ).1 →
              ((), σ1) ∈ (Fl4Spec.NonDet.when (Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac)
                (Fl4Spec.sendSignal (Z := Unit) (Fl4Spec.objRefOf ac) (Fl4Spec.capEpBadge ac)) σ).1 := by
            intro σ1 h; unfold Fl4Spec.NonDet.when; rw [if_pos hP, hobj, hbd]; exact h
          have hA : AbsSlot Z.th ((nodeA (L.ksb s) w).bv, []) := ⟨_, rfl, Or.inl hnode⟩
          have hpN := (J.slotN hA (by rw [cslotAddr_nil]; exact hcap)).1
          refine WP.spec_bind (WP.spec_and (J.signal_atN hAT hmb hN p b hpN)
            (MK.notification_send_signal L.total hAT hK hR)) ?_
          rintro ⟨s2, a2⟩ ⟨⟨σ', V', Ac', Lst'', D', hsp, -, J'⟩, hm2⟩
          have hmem : ((), σ') ∈ (Fl4Spec.sendSignal (Z := Unit) p.bv b.bv σ).1 := by rw [hsp]; rfl
          have hmF := MachF.mfk_sendSignal' p.bv b.bv σ _ hmem
          exact hmask s2 a2 σ' (hwhen σ' hmem) ⟨_, H, Cs, Ac', Lst'', D', J'⟩ (msF_mr hM hm2 hmF)
      | _ =>
        simp only [bind_ok]
        exact hnone (by rw [hac]; simp [absCap, Fl4Spec.isNtfnCap])
    rw [if_neg h1]
    by_cases h2 : v = 2#u64
    · -- the timer line
      rw [if_pos h2]
      have htm : σ.interruptStates i = .irqTimer := by rw [hst, h2]; rfl
      step with P1.LawfulStore.cur_cpu_spec as ⟨cc, ecc⟩
      step with P1.obj.node_set.spec as ⟨s2, es2⟩
      step with P1.obj.node_set.spec as ⟨s3, es3⟩
      subst es2 es3 ecc
      have J2 := J.reprogramJ
      obtain ⟨Ac3, Lst3, D3, J3⟩ := J2.armedJ (L.cpu_wr _ _ _) 0#u64
      try simp only [WP.spec_ok]
      exact Or.inr ⟨_, mem_hi_timer hle htm, ⟨Z, H, Cs, Ac3, Lst3, D3, J3⟩, hR⟩
    rw [if_neg h2]
    by_cases h3 : v = 3#u64
    · -- an IPI state on a line other than the IPI lines: reserved, nothing
      rw [if_pos h3]
      have hres : σ.interruptStates i = .irqReserved := by rw [hst, h3]; rfl
      unfold smp.handle_ipi
      rw [irq_resched_eq]
      have hne : ¬ w = 127#u64 := fun e => h127 (by rw [e]; rfl)
      simp only [bind_ok, hne, ↓reduceIte, WP.spec_ok]
      exact Or.inr ⟨_, mem_hi_reserved hle hres, ⟨Z, H, Cs, Ac, Lst, D, J⟩, hR⟩
    rw [if_neg h3]
    by_cases h0 : v = 0#u64
    · -- an inactive line: the spec fails
      have hin : σ.interruptStates i = .irqInactive := by rw [hst, h0]; rfl
      obtain ⟨a1, ha1⟩ := maskIrq_total arI hAT a w true
      simp only [h0, ↓reduceIte, ha1, bind_ok, WP.spec_ok]
      exact Or.inl hin
    · have hres : σ.interruptStates i = .irqReserved := by
        rw [hst]; unfold irqSt; simp [h0, h1, h2]
      simp only [h0, ↓reduceIte, bind_ok, WP.spec_ok]
      exact Or.inr ⟨_, mem_hi_reserved hle hres, ⟨Z, H, Cs, Ac, Lst, D, J⟩, hR⟩

end


/-! ## `SInvXFip` discharged -/

/-- **`SInvXFip` at every `SInvX` state** (SpecInvG4f's `sinvWR_fip`). -/
theorem sinvX_fip {σ : Fl4Spec.State Unit} (hX : SInvX σ) : SInvXFip σ :=
  fun w hw => SInvR.G4f.sinvWR_fip hX w hw

/-! ## The interrupt entry -/

section Spec
open Fl4Spec

/-- The spec's interrupt event up to the handler (`handleEvent .interrupt`). -/
theorem mem_irqEv {σ σ3 : State Unit} {z : Bool × State Unit} {z' : Unit × State Unit} {i : Irq}
    (hz : z ∈ ((updateTimeStamp (Z := Unit) >>= fun _ => checkBudget) σ).1)
    (hga : doMachineOp (Z := Unit) (getActiveIRQ false) z.2 = ({(some i, σ3)}, False))
    (hz' : z' ∈ (handleInterrupt (Z := Unit) i σ3).1) :
    ((.ok (), z'.2) : Except Unit Unit × State Unit) ∈ ((handleEvent (Z := Unit) .interrupt).run σ).1 := by
  show _ ∈ ((withoutPreemption (Z := Unit) (do updateTimeStamp; let _ ← checkBudget; maybeHandleInterrupt false)).run σ).1
  obtain ⟨u, hu, hc⟩ := mem_bind_elim hz
  exact mem_liftE (x := z') (mem_bind_nd hu (mem_bind_nd hc (mem_bind_nd (x := (some i, σ3)) (by rw [hga]; rfl) hz')))

/-- An outcome of the event's `handleE` then of the finish is an outcome of `fl4CallKernel`. -/
theorem mem_kcall {σ σ' : State Unit} {ev : Event} {x : Except Unit Unit × State Unit}
    (hx : x ∈ ((NonDetE.handleE (fl4HandleEvent (Z := Unit) true ev) (fun _ => withoutPreemption preemptionPath)).run σ).1)
    (hT : ((), σ') ∈ ((fl4Awaken (Z := Unit) >>= fun _ => schedule >>= fun _ => activateThread) x.2).1) :
    ((), σ') ∈ (fl4CallKernel (Z := Unit) true ev σ).1 := by
  unfold fl4CallKernel
  exact mem_bind_nd hx hT

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **[P] The hardware interrupt an interrupt entry runs on** (module
docstring): before `handle_interrupt_entry` the hardware has taken the line
`w` (the vector the entry is called with), which is the line the spec's
`getActiveIRQ false` reports at the entry state (masks and IRQ oracle
position; the clock read and the budget check keep both); the arch state the
entry starts from (`a'`) is related to the machine state after that read
(l4v: the IRQ oracle advanced once), and keeps the CR3 relation. `w` is a
vector below 256, not one of FL4's two IPI vectors (one core, [S]). Asked at
the one entry state of the step. -/
structure IrqHw (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (a a' : A)
    (σ : Fl4Spec.State Unit) (w : U64) : Prop where
  line : ∃ i, gaiLine false σ.machineState = some i ∧ w.val = i.toNat
  lt : w.val < 256
  n126 : w.val ≠ 126
  n127 : w.val ≠ 127
  mr : MR a' (gaiState σ.machineState)
  ar : ∀ c, AR a c → AR a' c

variable (arI) in
/-- FL4's interrupt entry up to the handler, at `(s, a)`, ended in `(s', a')`. -/
def KFrontI (s : S) (a : A) (w : U64) (s' : S) (a' : A) : Prop :=
  (do let (_, s2, a2) ← (do let (s1, a1) ← sched.update_timestamp st arI s a; sched.check_budget st arI s1 a1)
      interrupt.handle_interrupt st arI s2 a2 w) = ok (s', a')

theorem handle_interrupt_entry_eq (s : S) (a : A) (w : U64) :
    syscall.handle_interrupt_entry st arI s a w =
      (do let (_, s2, a2) ← (do let (s1, a1) ← sched.update_timestamp st arI s a; sched.check_budget st arI s1 a1)
          let (s3, a3) ← interrupt.handle_interrupt st arI s2 a2 w
          syscall.finish st arI s3 a3) := by
  unfold syscall.handle_interrupt_entry
  rw [Std.bind_assoc]
  rfl

theorem nowAgree_gai (hM : MachPlat arI MR) {a : A} {σ : Fl4Spec.State Unit}
    (hR : MR a (gaiState σ.machineState)) (hV : ValidMachineTime σ) : NowAgree arI a σ := by
  unfold NowAgree
  refine WP.spec_mono (hM.now a _ hR) ?_
  rintro r ⟨hv, -⟩
  have hv' : r.1.bv = gctVal σ.machineState := hv
  refine ⟨gctState σ.machineState, ?_, ?_, rfl⟩
  · rw [hv']; exact doMachineOp_single (getCurrentTime_eq _)
  · rw [hv']; exact vmt_le_gct hV

theorem ut_cb_mr (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hA : P0.ArchTotal arI) {a : A}
    {ms : Fl4Spec.MachineState} (hR : MR a ms) (s : S) :
    (do let (s1, a1) ← sched.update_timestamp st arI s a; sched.check_budget st arI s1 a1) ⦃ r =>
      MR r.2.2 (gctState ms) ⦄ := by
  refine WP.spec_bind (update_timestamp_mr hM hR s) ?_
  rintro ⟨s1, a1⟩ h1
  exact MK.sched_check_budget L.total hA hK h1

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **`JEvRef` of the interrupt entry from a non-idle thread** (module
docstring): FL4's `handle_interrupt_entry` at the hardware's arch state `a'`
(`IrqHw` [P]) ends, related (`RJ`, `MR`), in an outcome of the spec's
`.interrupt` event. Inputs: `JAtZ`, `SInvX`, `ct ≠ idle` at the entry state,
the platform bundle [P] of the syscall top, and `hFin`, the finish bundle
`KFinAtR31` asked at the pre-finish states of this run (as the syscall top's
`hFin`). -/
theorem jEvRef_irq {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a a' : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    {w : U64} (hI : IrqHw AR MR a a' σ w)
    (hFin : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true .interrupt)
        (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
      ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a'' : A),
        KFrontI (st := st) arI s a' w s' a'' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a'' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a'' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_interrupt_entry st arI s a' w ⦃ r =>
      ∃ σ', EvOut false .interrupt σ σ' ∧ RJM (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  obtain ⟨i, hgl, hwi⟩ := hI.line
  have hni := hX.entered hct
  have hS := hX.sb
  have hNS : NativeScope σ := hS.1.1.ns
  have hMK := hKD.toK
  obtain ⟨Lst0, J0⟩ := J.msArJ σ.machineState a' rfl (hI.ar _)
  have J0' : JAtZ (L := L) arI AR Z H Cs Ac Lst0 D s a' σ := J0
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hBu : KBudgetB arI a' σ := ⟨nowAgree_gai hM hI.mr hS.1.1.vmt, hC, hX.offReady, Or.inr hX.ctQ⟩
  -- the FPU-owner fact at the event's outcomes
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJEv (ev := .interrupt) hS (fun h => absurd rfl h)).ctAct
  have hNQ : NQ [σ.curThread] σ := nq_cons ((nq_nil_iff σ).2 ⟨hS.1.1.nq, hS.1.1.epq⟩) fun x hx => by
    rw [hx0] at hx; cases hx
    rcases ha0 with h1 | ⟨-, h1⟩
    · exact ok_of_active h1
    · rw [h1]; exact ⟨fun h => h, rfl⟩
  have hFN : FN [] σ := ⟨⟨(il_nil_iff σ).2 hS.1.1.live, nq_weak_nil _ hNQ⟩, hS.1.1.ft⟩
  rw [handle_interrupt_entry_eq]
  refine WP.spec_bind (spec_and_eq (WP.spec_and (J0'.utCheckB hni hBu hNS hARI.toARKeep hA hnd hmrt hmb hmax htu)
    (ut_cb_mr hM hMK hA hI.mr s)) fun _ h => h) ?_
  rintro ⟨b, s2, a2⟩ ⟨⟨⟨z, hz, -, Z2, Ac2, Lst2, D2, J2⟩, hM2⟩, heq1⟩
  -- the spec state after the budget check, then after the IRQ read
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ.machineState))
  have hz0 := hz
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hz0
  rw [hE] at hu
  have eu : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hms : σu.machineState = gctState σ.machineState := by rw [eu]
  have his : σu.interruptStates = σ.interruptStates := by rw [eu]
  have hk := MachF.mfk_checkBudget σu _ h2
  have hVu : ValidIrqMasks σu := by
    intro j hj; rw [hms]; exact hS.1.1.vim j (his ▸ hj)
  have hV2 : ValidIrqMasks z.2 := msF_vim hVu hk
  have hk' := hk
  simp only [MachF.msF, Prod.mk.injEq] at hk'
  obtain ⟨k1, k2, k3, k4, -⟩ := hk'
  have hgl2 : gaiLine false z.2.machineState = some i := by
    rw [gaiLine_congr (ms := σ.machineState) (by rw [k1, hms]; rfl) (by rw [k2, hms]; rfl)]; exact hgl
  set σ3 : Fl4Spec.State Unit := { z.2 with machineState := gaiState z.2.machineState } with hσ3
  have hga : Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ false) z.2 = ({(some i, σ3)}, False) := by
    rw [doMachineOp_single (getActiveIRQ_eq false z.2.machineState), hgl2]
  have hR3 : MR a2 σ3.machineState := hM.frame a2 _ _ hM2
    (by show z.2.machineState.irqMasks = _; rw [k1, hms]; rfl)
    (by show z.2.machineState.irqState + 1 = _; rw [k2, hms]; rfl)
    (by show z.2.machineState.timeState = _; rw [k3, hms]; rfl)
    (by show z.2.machineState.lastMachineTime = _; rw [k4, hms]; rfl)
  obtain ⟨Lst3, J3⟩ := J2.msArJ (gaiState z.2.machineState) a2 rfl id
  have hN2 : NativeScope z.2 := ik_bind ns_updateTimeStamp (fun _ => ns_checkBudget) σ hNS z hz
  have hN3 : NativeScope σ3 := SInvN.ns_of_kheap rfl hN2
  have hact3 : σ3.interruptStates i ≠ .irqInactive := by
    intro hin
    have h1 := hV2 i hin
    rw [gaiLine_unmasked hgl2] at h1
    cases h1
  refine WP.spec_bind (spec_and_eq (J3.handleIrqJIM hARI hA hIA hM hMK hmb hN3 hR3 w i hwi hI.lt hI.n126 hI.n127)
    fun _ h => h) ?_
  rintro ⟨s3, a3⟩ ⟨hP, heq2⟩
  rcases hP with hin | ⟨z', hz', ⟨Z3, H3, Cs3, Ac3, Lst4, D3, J4⟩, hM3⟩
  · exact absurd hin hact3
  have hEv := mem_irqEv hz hga hz'
  have hx := mem_handleE_ok (h := fun _ => Fl4Spec.withoutPreemption (Z := Unit) Fl4Spec.preemptionPath) hEv
  have hN4 : NativeScope z'.2 := ns_handleEvent .interrupt σ hNS _ hEv
  have hfo : FpuOwnOK z'.2 := fpuOwnOK_of_ft (fo_handleEvent_int σ hFN _ hEv).2
  have hfr : KFrontI (st := st) arI s a' w s3 a3 := by
    unfold KFrontI; rw [heq1]; simp only [bind_ok]; exact heq2
  have F := ((hFin _ hx Z3 H3 Cs3 Ac3 Lst4 D3 s3 a3 hfr J4.toR).to27).toR hfo
  exact WP.spec_mono (jat_finishJRNM s3 a3 z'.2 J4.toR hN4 F.hd hnd hA F.vt hmb F.arch F.archNd F.fo F.sni F.send hT
    F.tail hmax htu hM hKD hM3) fun r ⟨σ', hmem, hRJ, hM'⟩ => ⟨σ', mem_kcall hx hmem, hRJ, hM'⟩

end


/-! ## The user-exception and VM-fault entries -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

variable (arI) in
/-- FL4's fault entry up to the finish (`budget_ok`, then the fault branch `B`). -/
def KFrontF2 (B : S → A → Result (S × A)) (s : S) (a : A) (s' : S) (a' : A) : Prop :=
  (do let (b, s1, a1) ← syscall.budget_ok st arI s a; if b then B s1 a1 else ok (s1, a1)) = ok (s', a')

variable (arI) in
/-- **[W] The fault branch of a fault entry at `J`** (module docstring): at a
budget-checked state of this run (`budget_ok` returned `true` at `(s1, a1)`,
the spec's check at `σb`), FL4's branch `B` (the current thread's
`handle_fault` with the entry's fault) ends related to an outcome of the
spec's branch `G` (`handleFault` of the current thread with the spec's fault):
`JAtZR` at some ghosts and `MR`. The joint `handle_fault` exists only for cap
faults (`JAtZ.faultHypJZ`, `CapFaultCorr`); l4v: `handle_fault_corres` for
the fault kinds of `handleUserLevelFault` / `handleVMFaultEvent`. -/
def JFltHyp (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (B : S → A → Result (S × A)) (G : Fl4Spec.SMonad Unit Unit) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (σb : Fl4Spec.State Unit) (s1 : S) (a1 : A) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
    (true, σb) ∈ (specBudget σ).1 → syscall.budget_ok st arI s a = ok (true, s1, a1) →
    JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 a1 σb → MR a1 σb.machineState →
    B s1 a1 ⦃ r => ∃ z ∈ (G σb).1, (∃ (Z' : XSets) (H' : P1.Heap) (Cs' Ac'' : Set U64) (Lst'' : U64 → List U64)
      (D'' : Set U64), JAtZR (L := L) arI AR Z' H' Cs' Ac'' Lst'' D'' r.1 r.2 z.2) ∧ MR r.2 z.2.machineState ⦄

open Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvF in
set_option maxHeartbeats 16000000 in
/-- **A fault entry at `J`** (module docstring): `budget_ok`, the fault
branch under `JFltHyp` [W], then the finish under `hFin` (the syscall top's
`KFinAtR31` at the pre-finish states of this run). -/
theorem jEvRef_flt {ev : Fl4Spec.Event} {G : Fl4Spec.SMonad Unit Unit} {B : S → A → Result (S × A)}
    (hev : Fl4Spec.handleEvent (Z := Unit) ev = Fl4Spec.withoutPreemption (do
      Fl4Spec.updateTimeStamp; let restart ← Fl4Spec.checkBudgetRestart; Fl4Spec.NonDet.when restart G))
    (hsc : ∀ c, ev ≠ .syscallEvent c) (hin : ev ≠ .interrupt)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hB : JFltHyp (L := L) arI AR MR Z H Cs B G s a σ)
    (hFin : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
        (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
      ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF2 (st := st) arI B s a s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    (do let (b, s1, a1) ← syscall.budget_ok st arI s a
        let (s2, a2) ← if b then B s1 a1 else ok (s1, a1)
        syscall.finish st arI s2 a2) ⦃ r =>
      ∃ σ', EvOut false ev σ σ' ∧ RJM (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  have hni := hX.entered hct
  have hS := hX.sb
  have hNS : NativeScope σ := hS.1.1.ns
  have hMK := hKD.toK
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hBu : KBudgetB arI a σ := ⟨hM.nowAgree hR hS.1.1.vmt, hC, hX.offReady, Or.inr hX.ctQ⟩
  -- the FPU-owner fact and `NativeScope` at the event's outcomes
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJ hS hct).ctAct
  have hNQ : NQ [σ.curThread] σ := nq_cons ((nq_nil_iff σ).2 ⟨hS.1.1.nq, hS.1.1.epq⟩) fun x hx => by
    rw [hx0] at hx; cases hx; exact ok_of_active ha0
  have hL : IL [σ.curThread] σ := il_consT ((il_nil_iff σ).2 hS.1.1.live) (hS.1.1.live _ x0 hx0 (live_of_active ha0))
  have hFo : ∀ y ∈ ((Fl4Spec.handleEvent (Z := Unit) ev).run σ).1, FpuOwnOK y.2 := fun y hy =>
    fpuOwnOK_of_ft (fo_handleEvent_other σ.curThread ev hsc hin σ ⟨⟨⟨hL, nq_weak_nil _ hNQ⟩, hS.1.1.ft⟩, rfl⟩ y hy).2
  have fin : ∀ (s2 : S) (a2 : A) (y : Fl4Spec.State Unit),
      ((.ok (), y) : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.handleEvent (Z := Unit) ev).run σ).1 →
      KFrontF2 (st := st) arI B s a s2 a2 →
      (∃ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s2 a2 y) → MR a2 y.machineState →
      syscall.finish st arI s2 a2 ⦃ r => ∃ σ', EvOut false ev σ σ' ∧ RJM (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
    rintro s2 a2 y hE hfr ⟨Z', H', Cs', Ac', Lst', D', J'⟩ hMy
    have hE' : ((.ok (), y) : Except Unit Unit × Fl4Spec.State Unit) ∈
        ((Fl4Spec.fl4HandleEvent (Z := Unit) true ev).run σ).1 := by
      rw [Fl4Spec.fl4HandleEvent_other true ev hsc]; exact hE
    have hx := mem_handleE_ok (h := fun _ => Fl4Spec.withoutPreemption (Z := Unit) Fl4Spec.preemptionPath) hE'
    have F := ((hFin _ hx Z' H' Cs' Ac' Lst' D' s2 a2 hfr J').to27).toR (hFo _ hE)
    exact WP.spec_mono (jat_finishJRNM s2 a2 y J' (ns_handleEvent ev σ hNS _ hE) F.hd hnd hA F.vt hmb F.arch F.archNd
      F.fo F.sni F.send hT F.tail hmax htu hM hKD hMy) fun r ⟨σ', hmem, hRJ, hM'⟩ => ⟨σ', mem_kcall hx hmem, hRJ, hM'⟩
  refine WP.spec_bind (spec_and_eq (WP.spec_and (J.budgetOkB hni hBu hNS hARI.toARKeep hA hnd hmrt hmb hmax htu)
    (budget_ok_mr hM hMK hA hR s)) fun _ h => h) ?_
  rintro ⟨b, s1, a1⟩ ⟨⟨⟨hTr, hFa⟩, hM1⟩, heq⟩
  cases b with
  | false =>
    obtain ⟨⟨b', σb⟩, hz, hz1, Z', Ac', Lst', D', J'⟩ := hFa rfl
    simp only at hz1; subst hz1
    have hMb := (budget_mr_at hM hnd hz hM1 hS.1.1.vim).1
    have hE : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ ((Fl4Spec.handleEvent (Z := Unit) ev).run σ).1 := by
      rw [hev]
      obtain ⟨u, hu, hc⟩ := mem_bind_elim hz
      exact mem_liftE (x := ((), σb)) (mem_bind_nd hu (mem_bind_nd hc (mem_when_false (by simp) _ σb)))
    have hfr : KFrontF2 (st := st) arI B s a s1 a1 := by
      unfold KFrontF2; rw [heq, bind_ok]; rfl
    show (do let (s2, a2) ← (if false = true then B s1 a1 else ok (s1, a1)); syscall.finish st arI s2 a2) ⦃ _ ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    exact fin s1 a1 σb hE hfr ⟨Z', H, Cs, Ac', Lst', D', J'.toR⟩ hMb
  | true =>
    obtain ⟨σb, he, -, -, -, -, -, -, -, Ac', Lst', D', J'⟩ := hTr rfl
    have hb : (true, σb) ∈ (specBudget σ).1 := by unfold specBudget; rw [he]; exact Set.mem_singleton _
    have hMb := (budget_mr_at hM hnd hb hM1 hS.1.1.vim).1
    show (do let (s2, a2) ← (if true = true then B s1 a1 else ok (s1, a1)); syscall.finish st arI s2 a2) ⦃ _ ⦄
    rw [if_pos rfl]
    refine WP.spec_bind (spec_and_eq (hB σb s1 a1 Ac' Lst' D' hb heq J' hMb) fun _ h => h) ?_
    rintro ⟨s2, a2⟩ ⟨⟨z', hz', hJ', hM2⟩, heq2⟩
    have hE : ((.ok (), z'.2) : Except Unit Unit × Fl4Spec.State Unit) ∈
        ((Fl4Spec.handleEvent (Z := Unit) ev).run σ).1 := by
      rw [hev]
      obtain ⟨u, hu, hc⟩ := mem_bind_elim hb
      refine mem_liftE (x := z') (mem_bind_nd hu (mem_bind_nd hc ?_))
      show z' ∈ (Fl4Spec.NonDet.when (true = true) G σb).1
      unfold Fl4Spec.NonDet.when; rw [if_pos rfl]; exact hz'
    have hfr : KFrontF2 (st := st) arI B s a s2 a2 := by
      unfold KFrontF2; rw [heq]; simp only [bind_ok, ↓reduceIte]; exact heq2
    exact fin s2 a2 z'.2 hE hfr hJ' hM2

/-- **`JEvRef` of the user-exception entry** under `JFltHyp` [W] for the
current thread's `handle_fault` of `UserException n c` against the spec's
`handleFault` of `userException (n &&& mask 32) (c &&& mask 28)` (an argument
agreement: FL4 sends `number` / `code` unmasked; the x86 vector and error
code are below those bounds). -/
theorem jEvRef_user {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (n c : U64)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState)
    (hB : JFltHyp (L := L) arI AR MR Z H Cs
      (fun s1 a1 => do let t ← sched.cur_thread st s1; faults.handle_fault st arI s1 a1 t (.UserException n c))
      (do let t ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
          Fl4Spec.handleFault t (.userException (n.bv &&& Fl4Spec.mask 32) (c.bv &&& Fl4Spec.mask 28))) s a σ)
    (hFin : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true (.userLevelFault n.bv c.bv))
        (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
      ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF2 (st := st) arI
          (fun s1 a1 => do let t ← sched.cur_thread st s1; faults.handle_fault st arI s1 a1 t (.UserException n c))
          s a s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    JEvRef (L := L) arI AR MR (.user n c) false (.userLevelFault n.bv c.bv) s a σ :=
  jEvRef_flt rfl (fun _ h => by cases h) (fun h => by cases h) J hX hct hR hB hFin hARI hA hnd hM hKD hmrt hmb hT hmax
    htu

/-- **`JEvRef` of the VM-fault entry** under `JFltHyp` [W] for FL4's branch
(the fault from the address and error code, then `handle_fault`) against the
spec's (`handleVmFault`'s machine fault address and error register, caught by
`handleFault`): the [P] agreement of the hardware's `addr` / `code` with the
spec's reads is part of that premise. -/
theorem jEvRef_vmf {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (ad c : U64) (ft : Fl4Spec.VMFaultType)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState)
    (hB : JFltHyp (L := L) arI AR MR Z H Cs
      (fun s1 a1 => do
        let t ← sched.cur_thread st s1
        let i ← c >>> 4#i32
        let i1 ← lift (i &&& 1#u64)
        let f ← vspace.vm_fault ad c (i1 != 0#u64)
        faults.handle_fault st arI s1 a1 t f)
      (do let t ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
          Fl4Spec.NonDetE.catch (Fl4Spec.handleVmFault t ft) (Fl4Spec.handleFault t)) s a σ)
    (hFin : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true (.vmFaultEvent ft))
        (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
      ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
        KFrontF2 (st := st) arI
          (fun s1 a1 => do
            let t ← sched.cur_thread st s1
            let i ← c >>> 4#i32
            let i1 ← lift (i &&& 1#u64)
            let f ← vspace.vm_fault ad c (i1 != 0#u64)
            faults.handle_fault st arI s1 a1 t f)
          s a s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    JEvRef (L := L) arI AR MR (.vmf ad c) false (.vmFaultEvent ft) s a σ :=
  jEvRef_flt rfl (fun _ h => by cases h) (fun h => by cases h) J hX hct hR hB hFin hARI hA hnd hM hKD hmrt hmb hT hmax
    htu

end


/-! ## The induction with the covered events -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The finish bundle of an event at its pre-finish states** (the syscall
top's `hFin` shape, the FL4 states restricted by `Kf` to this run's). -/
def KFinEv (ev : Fl4Spec.Event) (Kf : S → A → Prop) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
    ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
      Kf s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 → KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2

/-- FL4's user-exception branch. -/
abbrev brU (n c : U64) : S → A → Result (S × A) :=
  fun s1 a1 => do let t ← sched.cur_thread st s1; faults.handle_fault st arI s1 a1 t (.UserException n c)

/-- The spec's user-exception branch. -/
abbrev brUS (n c : U64) : Fl4Spec.SMonad Unit Unit :=
  do let t ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
     Fl4Spec.handleFault t (.userException (n.bv &&& Fl4Spec.mask 32) (c.bv &&& Fl4Spec.mask 28))

/-- FL4's VM-fault branch. -/
abbrev brV (ad c : U64) : S → A → Result (S × A) :=
  fun s1 a1 => do
    let t ← sched.cur_thread st s1
    let i ← c >>> 4#i32
    let i1 ← lift (i &&& 1#u64)
    let f ← vspace.vm_fault ad c (i1 != 0#u64)
    faults.handle_fault st arI s1 a1 t f

/-- The spec's VM-fault branch. -/
abbrev brVS (ft : Fl4Spec.VMFaultType) : Fl4Spec.SMonad Unit Unit :=
  do let t ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
     Fl4Spec.NonDetE.catch (Fl4Spec.handleVmFault t ft) (Fl4Spec.handleFault t)

/-- **The reachable joint states with syscall, hardware-interrupt and event
steps** (module docstring): `irq` is the interrupt entry run at the arch state
`a1` the hardware left (`IrqHw` [P]); `event` is `JReachE.event` without
`SInvXFip` (now `sinvX_fip`). -/
inductive JReachE2 : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SInvX σ → MR a σ.machineState → JReachE2 s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachE2 s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → JReachE2 s' a' σ'
  | irq {s : S} {a a1 : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (w : U64) :
      JReachE2 s a σ → IrqHw AR MR a a1 σ w → syscall.handle_interrupt_entry st arI s a1 w = ok (s', a') →
      EvOut false .interrupt σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachE2 s' a' σ'
  | event {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (e : KEv)
      (fip : Bool) (ev : Fl4Spec.Event) :
      JReachE2 s a σ → KEvSpec e fip ev → (ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) →
      e.run st arI s a = ok (s', a') → EvOut fip ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachE2 s' a' σ'

variable {arI AR MR}

/-- Every `JReachE` state is a `JReachE2` state. -/
theorem JReachE.toE2 {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachE (L := L) arI AR MR s a σ) :
    JReachE2 (L := L) arI AR MR s a σ := by
  induction h with
  | @start s a σ Z H Cs Ac Lst D J hX hR => exact JReachE2.start J hX hR
  | @step s a σ s' a' σ' n c _ hct hn hv hy hRJ ih => exact JReachE2.step n c ih hct hn hv hy hRJ
  | @event s a σ s' a' σ' e fip ev _ hK hev _ hv hO hRJ ih => exact JReachE2.event e fip ev ih hK hev hv hO hRJ

/-- **The invariant** of `JReachE2`: `JAtZ` at some ghosts, `SInvX`, `MR`. -/
theorem jreach_invE2 (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachE2 (L := L) arI AR MR s a σ) :
    (∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) ∧ SInvX σ ∧ MR a σ.machineState := by
  induction h with
  | @start s a σ Z H Cs Ac Lst D J hX hR => exact ⟨⟨_, _, _, _, _, _, J⟩, hX, hR⟩
  | @step s a σ s' a' σ' n c _ hct _ _ hy hRJ ih => exact ⟨hRJ.1.2, kentry_sinvX hnd c ih.2.1 hct _ hy, hRJ.2⟩
  | @irq s a a1 σ s' a' σ' w _ _ _ hO hRJ ih =>
    exact ⟨hRJ.1.2, kcall_sinvX hnd true .interrupt ih.2.1 (fun h => absurd rfl h) _ hO, hRJ.2⟩
  | @event s a σ s' a' σ' e fip ev _ _ hev _ hO hRJ ih =>
    exact ⟨hRJ.1.2, sinvX_evOut hnd ih.2.1 hev (fun _ => sinvX_fip ih.2.1) hO, hRJ.2⟩

set_option maxHeartbeats 8000000 in
/-- **Refinement at every reachable state: syscalls, interrupts, user
exceptions, VM faults, and the remaining events** (module docstring). At a
`JReachE2` state, at the ghosts `jreach_invE2` gives: (i) the syscall entry
(`kernel_entryJ37N`'s per-state premises); (ii) the interrupt entry from a
non-idle thread at the hardware's arch state, given `IrqHw` [P] and the
finish bundle at its pre-finish states (no `JEvRef`); (iii) the user-exception
and (iv) VM-fault entries from a non-idle thread, given `JFltHyp` [W] (the
fault branch) and the finish bundle (no `JEvRef`); (v) every event with its
`JEvRef` [W] (needed only for the unknown-syscall / `int $N` entries and an
interrupt in the idle thread; no `SInvXFip`). Each ends in a related outcome
with `SInvX` and `MR`, which is again reachable. -/
theorem kernel_entry_reachE2 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachE2 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ MR a σ.machineState ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKV35 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            JDispMRI (L := L) arI AR MR s' a' σb n c) →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        (n = fl4_abi.syscall.SysReplyRecv →
          FastRR (L := L) (arI := arI) s a n (fun r => KPostMS (L := L) arI AR MR c σ r)) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            JReachE2 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), σ.curThread ≠ σ.idleThread → IrqHw AR MR a a1 σ w →
        KFinEv (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE2 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread →
        JFltHyp (L := L) arI AR MR Z H Cs (brU (st := st) arI n c) (brUS n c) s a σ →
        KFinEv (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE2 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread →
        JFltHyp (L := L) arI AR MR Z H Cs (brV (st := st) arI ad c) (brVS ft) s a σ →
        KFinEv (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE2 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (e : KEv) (fip : Bool) (ev : Fl4Spec.Event), KEvSpec e fip ev →
        (ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) →
        JEvRef (L := L) arI AR MR e fip ev s a σ →
        e.run st arI s a ⦃ r => ∃ σ', EvOut fip ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE2 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hX, hR⟩ := jreach_invE2 hnd hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hR, fun n c hct hn hflag hK hDM hFin hFast => ?_,
    fun w a1 hct hI hFin => ?_, fun n c hct hB hFin => ?_, fun ad c ft hct hB hFin => ?_,
    fun e fip ev hK hev hE => ?_⟩
  · have hE := kernel_entryJ37N (MR := MR) s a σ J hct hR hX n c hn hflag hK hDM hFin hARI hA hnd hM hKD hPA hIA
      hmrt hmb hT hmax htu hRef hPI hFast
    obtain ⟨⟨s', a'⟩, hv, σ', hy, hRJ, hM', hX'⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    exact ⟨σ', hy, hRJ, hX', hM', JReachE2.step n c hJ hct hn hv hy ⟨hRJ, hM'⟩⟩
  · have hE := jEvRef_irq J hX hct hI hFin hARI hA hnd hM hKD hIA hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, kcall_sinvX hnd true .interrupt hX (fun h => absurd rfl h) _ hO, hRJM.2,
      JReachE2.irq w hJ hI hv hO hRJM⟩
  · have hE := jEvRef_user n c J hX hct hR hB hFin hARI hA hnd hM hKD hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [show syscall.handle_user_exception st arI s a n c = (KEv.user n c).run st arI s a from rfl, hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun h => by cases h) hO, hRJM.2,
      JReachE2.event (.user n c) false _ hJ (KEvSpec.user n c) (fun _ => hct) hv hO hRJM⟩
  · have hE := jEvRef_vmf ad c ft J hX hct hR hB hFin hARI hA hnd hM hKD hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [show syscall.handle_vm_fault st arI s a ad c = (KEv.vmf ad c).run st arI s a from rfl, hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun h => by cases h) hO, hRJM.2,
      JReachE2.event (.vmf ad c) false _ hJ (KEvSpec.vmf ad c ft) (fun _ => hct) hv hO hRJM⟩
  · obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, sinvX_evOut hnd hX hev (fun _ => sinvX_fip hX) hO, hRJM.2,
      JReachE2.event e fip ev hJ hK hev hv hO hRJM⟩

end

end

end Fl4Proofs.P3
