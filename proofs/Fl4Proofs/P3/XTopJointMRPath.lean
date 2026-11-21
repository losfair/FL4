/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr2): **the preemption path's IRQ
take and handler under `MachPlat`, ending in `PPQJI`** (no `IrqPlat`, no
`IrqPlatI`).

* `modelArch_mrKeep`: the model platform satisfies MachKeep's `MRKeep` [P].
* `ValidIrqMasks σ` [J] (l4v `valid_irq_masks`: an `IRQInactive` line is
  masked in the machine state; seL4 masks a line when it becomes inactive:
  `set_irq_state IRQInactive` with `maskInterrupt`). With `MachPlat.take` (the
  reported line is the spec's `getActiveIRQ` line, which is unmasked) it
  replaces sch12's `IrqPlatI.act` (stated at every `JAt` state, satisfiable
  only by a platform that never raises a line: `irqPlatI_of` derives it from
  `IrqPlat.take`).
* `JAtZ.handleIrqJIA` / `JAtZ.handleIrqJJA` / `jIrqHypJ_ofA`: XTopJointIrqZI's
  `handleIrqJI`, XTopJointIrqZR's `handleIrqJJ` / `jIrqHypJ_of` with
  `IrqPlatA` (they use only `ackAR`). Scripted copies (the statements differ
  only in the platform bundle).
* `afterInv_of_mcsIM`: XTopJointIrqZI's `afterInv_of_mcsI` with `MR r.2
  σ'.ms ∧ ValidIrqMasks σ'` after the MCS preemption point asked in its
  hypothesis, `MachPlat.takeAt` for `IrqPlat.take`, `IrqPlatA` for the rest.
-/
import Fl4Proofs.P3.MachKeep
import Fl4Proofs.P3.XTopJointMRMcs
import Fl4Proofs.P3.XTopJointIrqZJ
import Fl4Proofs.P3.ScSignalJN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The model platform satisfies `MRKeep`** for every predicate (its
operations other than the reads return the arch state unchanged). -/
theorem modelArch_mrKeep {C : Type} (AR : Fl4Spec.MachineState → C → Prop) : MRKeep modelArch AR where
  set_deadline _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  send_reschedule _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  remote_stall _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_flush _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_release _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_sanitise _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_reload _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  vcpu_barrier _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h

/-- **[J] l4v `valid_irq_masks`** (module docstring). -/
def ValidIrqMasks (σ : Fl4Spec.State Unit) : Prop :=
  ∀ i, σ.interruptStates i = .irqInactive → σ.machineState.irqMasks i = true

/-- **The spec's reported line is not inactive under `ValidIrqMasks`.** -/
theorem gai_active {σ : Fl4Spec.State Unit} (hV : ValidIrqMasks σ) {irq : Option Fl4Spec.Irq}
    {ms : Fl4Spec.MachineState}
    (h : Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ true) σ =
      ({(irq, { σ with machineState := ms })}, False)) (i : Fl4Spec.Irq) (hi : irq = some i) :
    σ.interruptStates i ≠ .irqInactive := by
  rw [doMachineOp_single (getActiveIRQ_eq true σ.machineState)] at h
  have e := Set.singleton_eq_singleton_iff.1 (Prod.mk.inj h).1
  have e2 : gaiLine true σ.machineState = irq := (Prod.mk.inj e).1
  rw [hi] at e2
  intro hin
  have h1 := gaiLine_unmasked e2
  rw [hV i hin] at h1
  cases h1

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- `handleIrqJI` with `IrqPlatA` (module docstring), `NativeScope` at its own
state (g3b). -/
theorem JAtZ.handleIrqJIAN (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlatA arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hN : NativeScope σ)
    (w : U64) (i : Fl4Spec.Irq) (hwi : w.val = i.toNat) (h126 : w.val ≠ 126) (h127 : w.val ≠ 127) :
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      σ.interruptStates i = .irqInactive ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hX := J.xtop
  have hIR : IrqRel (L.mem s) (L.ksb s) σ := hX.fin.1.1.2.2.2.1
  have hARa : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  have hiw : (BitVec.ofNat 8 w.val : Fl4Spec.Irq) = i := by
    apply BitVec.eq_of_toNat_eq; simp [hwi]
  -- the acknowledgement keeps `JAt`
  have hack : ∀ (s1 : S) (a1 : A) (z : Unit × Fl4Spec.State Unit),
      z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1 → JAt (L := L) arI AR s1 a1 z.2 →
      (do let a2 ← arI.ack_irq a1 w; ok (s1, a2)) ⦃ r =>
        σ.interruptStates i = .irqInactive ∨
          ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
    rintro s1 a1 z hz ⟨Z1, H1, Cs1, Ac1, Lst1, D1, J1⟩
    refine WP.spec_bind (hIP.ackAR a1 w _ J1.xtop.fin.1.1.2.2.2.2.2.2) ?_
    intro a2 hA2
    obtain ⟨Lst2, J2⟩ := J1.msArJ z.2.machineState a2 rfl (fun _ => hA2)
    exact (WP.spec_ok _).2 (Or.inr ⟨z, hz, Z1, H1, Cs1, Ac1, Lst2, D1, J2⟩)
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
    rw [ha1]
    simp only [bind_ok]
    have hA1 : AR a1 σ.archState.x64CurrentCr3 := hARI.mask _ _ _ hARa (Or.inr (Or.inl ⟨w, true, ha1⟩))
    obtain ⟨Lst1, J1⟩ := J.msArJ (maskMs σ i true).machineState a1 rfl (fun _ => hA1)
    exact hack s a1 _ (mem_hi_big hgt σ) ⟨Z, H, Cs, Ac, Lst1, D, J1⟩
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
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ →
        (do let (s1, a1) ← m; let a2 ← arI.ack_irq a1 w; ok (s1, a2)) ⦃ r =>
          σ.interruptStates i = .irqInactive ∨
            ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
      intro m hm
      refine WP.spec_bind hm ?_
      rintro ⟨s1, a1⟩ (hf | ⟨z, hz, hJ1⟩)
      · refine WP.spec_bind (hAT.ack_irq a1 w) ?_
        intro a2 _
        exact (WP.spec_ok _).2 (Or.inl hf)
      · exact hack s1 a1 z hz hJ1
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
          JAt (L := L) arI AR s3 a2 σ1 →
          (do let a3 ← arI.mask_irq a2 w true; ok (s3, a3)) ⦃ r =>
            σ.interruptStates i = .irqInactive ∨
              ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
        rintro s3 a2 σ1 h1' ⟨Z1, H1, Cs1, Ac1, Lst1, D1, J1⟩
        obtain ⟨a3, ha3⟩ := maskIrq_total arI hAT a2 w true
        rw [ha3]
        simp only [bind_ok, WP.spec_ok]
        have hA3 := hARI.mask _ _ _ J1.xtop.fin.1.1.2.2.2.2.2.2 (Or.inr (Or.inl ⟨w, true, ha3⟩))
        obtain ⟨Lst3, J3⟩ := J1.msArJ (maskMs σ1 i true).machineState a3 rfl (fun _ => hA3)
        exact Or.inr ⟨((), maskMs σ1 i true), mem_hi_signal hle hsig hgc h1', Z1, H1, Cs1, Ac1, Lst3, D1, J3⟩
      have hnone : ∀ (hP : ¬ (Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac)),
          (do let a3 ← arI.mask_irq a w true; ok (s, a3)) ⦃ r =>
            σ.interruptStates i = .irqInactive ∨
              ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ :=
        fun hP => hmask s a σ (mem_when_false hP _ σ) ⟨Z, H, Cs, Ac, Lst, D, J⟩
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
          refine WP.spec_bind (J.signal_atN hAT hmb hN p b hpN) ?_
          rintro ⟨s2, a2⟩ ⟨σ', V', Ac', Lst'', D', hsp, -, J'⟩
          exact hmask s2 a2 σ' (hwhen σ' (by rw [hsp]; rfl)) ⟨_, H, Cs, Ac', Lst'', D', J'⟩
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
      exact Or.inr ⟨_, mem_hi_timer hle htm, Z, H, Cs, Ac3, Lst3, D3, J3⟩
    rw [if_neg h2]
    by_cases h3 : v = 3#u64
    · -- an IPI state on a line other than the IPI lines: reserved, nothing
      rw [if_pos h3]
      have hres : σ.interruptStates i = .irqReserved := by rw [hst, h3]; rfl
      unfold smp.handle_ipi
      rw [irq_resched_eq]
      have hne : ¬ w = 127#u64 := fun e => h127 (by rw [e]; rfl)
      simp only [bind_ok, hne, ↓reduceIte, WP.spec_ok]
      exact Or.inr ⟨_, mem_hi_reserved hle hres, Z, H, Cs, Ac, Lst, D, J⟩
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
      exact Or.inr ⟨_, mem_hi_reserved hle hres, Z, H, Cs, Ac, Lst, D, J⟩

/-- `handleIrqJIAN` from the ∀-form `hNS` (the pre-g3b statement). -/
theorem JAtZ.handleIrqJIA (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlatA arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (w : U64) (i : Fl4Spec.Irq) (hwi : w.val = i.toNat) (h126 : w.val ≠ 126) (h127 : w.val ≠ 127) :
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      σ.interruptStates i = .irqInactive ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ :=
  J.handleIrqJIAN hARI hAT hIP hmb (hNS s a σ ⟨Z, H, Cs, Ac, Lst, D, s, a, σ, J.toHole⟩) w i hwi h126 h127

set_option maxHeartbeats 16000000 in
/-- `handleIrqJJ` with `IrqPlatA` (module docstring). -/
theorem JAtZ.handleIrqJJAN (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlatA arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : NativeScope σ)
    (w : U64) (i : Fl4Spec.Irq) (hwi : w.val = i.toNat) (h126 : w.val ≠ 126) (h127 : w.val ≠ 127) :
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hX := J.xtop
  have hIR : IrqRel (L.mem s) (L.ksb s) σ := hX.fin.1.1.2.2.2.1
  have hARa : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  have hiw : (BitVec.ofNat 8 w.val : Fl4Spec.Irq) = i := by
    apply BitVec.eq_of_toNat_eq; simp [hwi]
  -- the acknowledgement keeps `JAt`
  have hack : ∀ (s1 : S) (a1 : A) (z : Unit × Fl4Spec.State Unit),
      z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1 → JAt (L := L) arI AR s1 a1 z.2 →
      (do let a2 ← arI.ack_irq a1 w; ok (s1, a2)) ⦃ r =>
        (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
          ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
    rintro s1 a1 z hz ⟨Z1, H1, Cs1, Ac1, Lst1, D1, J1⟩
    refine WP.spec_bind (hIP.ackAR a1 w _ J1.xtop.fin.1.1.2.2.2.2.2.2) ?_
    intro a2 hA2
    obtain ⟨Lst2, J2⟩ := J1.msArJ z.2.machineState a2 rfl (fun _ => hA2)
    exact (WP.spec_ok _).2 (Or.inr ⟨z, hz, Z1, H1, Cs1, Ac1, Lst2, D1, J2⟩)
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
    rw [ha1]
    simp only [bind_ok]
    have hA1 : AR a1 σ.archState.x64CurrentCr3 := hARI.mask _ _ _ hARa (Or.inr (Or.inl ⟨w, true, ha1⟩))
    obtain ⟨Lst1, J1⟩ := J.msArJ (maskMs σ i true).machineState a1 rfl (fun _ => hA1)
    exact hack s a1 _ (mem_hi_big hgt σ) ⟨Z, H, Cs, Ac, Lst1, D, J1⟩
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
    have key : ∀ m : Result (S × A), m ⦃ r => (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ →
        (do let (s1, a1) ← m; let a2 ← arI.ack_irq a1 w; ok (s1, a2)) ⦃ r =>
          (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
            ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
      intro m hm
      refine WP.spec_bind hm ?_
      rintro ⟨s1, a1⟩ (hf | ⟨z, hz, hJ1⟩)
      · refine WP.spec_bind (hAT.ack_irq a1 w) ?_
        intro a2 _
        exact (WP.spec_ok _).2 (Or.inl hf)
      · exact hack s1 a1 z hz hJ1
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
          JAt (L := L) arI AR s3 a2 σ1 →
          (do let a3 ← arI.mask_irq a2 w true; ok (s3, a3)) ⦃ r =>
            (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
              ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
        rintro s3 a2 σ1 h1' ⟨Z1, H1, Cs1, Ac1, Lst1, D1, J1⟩
        obtain ⟨a3, ha3⟩ := maskIrq_total arI hAT a2 w true
        rw [ha3]
        simp only [bind_ok, WP.spec_ok]
        have hA3 := hARI.mask _ _ _ J1.xtop.fin.1.1.2.2.2.2.2.2 (Or.inr (Or.inl ⟨w, true, ha3⟩))
        obtain ⟨Lst3, J3⟩ := J1.msArJ (maskMs σ1 i true).machineState a3 rfl (fun _ => hA3)
        exact Or.inr ⟨((), maskMs σ1 i true), mem_hi_signal hle hsig hgc h1', Z1, H1, Cs1, Ac1, Lst3, D1, J3⟩
      have hnone : ∀ (hP : ¬ (Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac)),
          (do let a3 ← arI.mask_irq a w true; ok (s, a3)) ⦃ r =>
            (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
              ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ :=
        fun hP => hmask s a σ (mem_when_false hP _ σ) ⟨Z, H, Cs, Ac, Lst, D, J⟩
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
          refine WP.spec_bind (J.signal_atN hAT hmb hN p b hpN) ?_
          rintro ⟨s2, a2⟩ ⟨σ', V', Ac', Lst'', D', hsp, -, J'⟩
          exact hmask s2 a2 σ' (hwhen σ' (by rw [hsp]; rfl)) ⟨_, H, Cs, Ac', Lst'', D', J'⟩
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
      exact Or.inr ⟨_, mem_hi_timer hle htm, Z, H, Cs, Ac3, Lst3, D3, J3⟩
    rw [if_neg h2]
    by_cases h3 : v = 3#u64
    · -- an IPI state on a line other than the IPI lines: reserved, nothing
      rw [if_pos h3]
      have hres : σ.interruptStates i = .irqReserved := by rw [hst, h3]; rfl
      unfold smp.handle_ipi
      rw [irq_resched_eq]
      have hne : ¬ w = 127#u64 := fun e => h127 (by rw [e]; rfl)
      simp only [bind_ok, hne, ↓reduceIte, WP.spec_ok]
      exact Or.inr ⟨_, mem_hi_reserved hle hres, Z, H, Cs, Ac, Lst, D, J⟩
    rw [if_neg h3]
    by_cases h0 : v = 0#u64
    · -- an inactive line: the spec fails
      have hin : σ.interruptStates i = .irqInactive := by rw [hst, h0]; rfl
      obtain ⟨a1, ha1⟩ := maskIrq_total arI hAT a w true
      simp only [h0, ↓reduceIte, ha1, bind_ok, WP.spec_ok]
      exact Or.inl (fail_hi_inactive hle hin)
    · have hres : σ.interruptStates i = .irqReserved := by
        rw [hst]; unfold irqSt; simp [h0, h1, h2]
      simp only [h0, ↓reduceIte, bind_ok, WP.spec_ok]
      exact Or.inr ⟨_, mem_hi_reserved hle hres, Z, H, Cs, Ac, Lst, D, J⟩

/-- `JAtZ.handleIrqJJAN` from the ∀-form `hNS` (the pre-g3e statement). -/
theorem JAtZ.handleIrqJJA (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlatA arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (w : U64) (i : Fl4Spec.Irq) (hwi : w.val = i.toNat) (h126 : w.val ≠ 126) (h127 : w.val ≠ 127) :
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ :=
  J.handleIrqJJAN hARI hAT hIP hmb (hNS s a σ ⟨Z, H, Cs, Ac, Lst, D, s, a, σ, J.toHole⟩) w i hwi h126 h127


/-- **`JIrqHypJ` from `IrqPlatA`** (`jIrqHypJ_of` with `IrqPlatA`). -/
theorem jIrqHypJ_ofA (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlatA arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) :
    JIrqHypJ (L := L) arI AR := by
  intro s a σ w i hJ hwi _ h126 h127
  obtain ⟨Z, H, Cs, Ac, Lst, D, J⟩ := hJ
  exact J.handleIrqJJA hARI hAT hIP hmb hNS w i hwi h126 h127

/-- **`JIrqHypJ` per state from `IrqPlatA`** (g3e): at every `JAt` state with
`NativeScope` there, no ∀-form `hNS`. -/
theorem jIrqHypJ_ofAN (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlatA arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (w : U64) (i : Fl4Spec.Irq),
    JAt (L := L) arI AR s a σ → NativeScope σ → w.val = i.toNat → σ.machineState.irqMasks i = false →
    w.val ≠ 126 → w.val ≠ 127 →
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  intro s a σ w i hJ hN hwi _ h126 h127
  obtain ⟨Z, H, Cs, Ac, Lst, D, J⟩ := hJ
  exact J.handleIrqJJAN hARI hAT hIP hmb hN w i hwi h126 h127

set_option maxHeartbeats 16000000 in
/-- **`afterInv_of_mcsI` under `MachPlat`** (module docstring), `NativeScope` at the
state after the MCS part from `hmcs` (g3b). -/
theorem afterInv_of_mcsIMN {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hmcs : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧ NativeScope σ' ⦄)
    (hM : MachPlat arI MR) (hIP : IrqPlatA arI AR) (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI)
    (hmbA : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQJI (L := L) arI AR σ (r.2.1, r.2.2) ⦄ := by
  unfold syscall.after_invocation
  refine WP.spec_bind hmcs ?_
  rintro ⟨s1, a1⟩ ⟨σ', hm, hmf, ⟨Z', H', Cs', Ac', Lst', D', J'⟩, hR1, hVI, hN'⟩
  have hAR1 : AR a1 σ'.archState.x64CurrentCr3 := J'.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (hM.takeAt hR1) (hIP.takeAR a1 _ hAR1)) (hIP.noIpi a1)) ?_
  rintro ⟨w, a2⟩ ⟨⟨⟨irq, ms, hIq, hnone, hsome, hum, -⟩, hAR2⟩, h126, h127⟩
  obtain ⟨Lst2, J2⟩ := J'.msArJ ms a2 hum (fun _ => hAR2)
  unfold syscall.check_interrupt
  by_cases hw : w = syscall.NO_IRQ
  · have hirq : irq = none := hnone.1 hw
    subst hirq
    have e : (w != syscall.NO_IRQ) = false := by simp [hw]
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine (WP.spec_ok _).2 ⟨rfl, ⟨((), { σ' with machineState := ms }),
      hm _ (mem_maybeHandle_none hIq), ⟨Z', H', Cs', Ac', Lst2, D', J2⟩⟩⟩
  · obtain ⟨i, rfl⟩ : ∃ i, irq = some i := by
      cases irq with
      | none => exact absurd (hnone.2 rfl) hw
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hwi, hmask⟩ := hsome i rfl
    have e : (w != syscall.NO_IRQ) = true := by simpa using hw
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [↓reduceIte]
    refine WP.spec_bind (J2.handleIrqJIAN hARI hAT hIP hmbA hN' w i hwi h126 h127) ?_
    rintro ⟨s2, a3⟩ (hf | ⟨z, hz, hJ⟩)
    · exact absurd hf (gai_active hVI hIq i rfl)
    · exact (WP.spec_ok _).2 ⟨rfl, ⟨z, hm _ (mem_maybeHandle_some hIq hz), hJ⟩⟩


/-- `afterInv_of_mcsIMN` from the ∀-form `hNS` (the pre-g3b statement). -/
theorem afterInv_of_mcsIM {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hmcs : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ⦄)
    (hM : MachPlat arI MR) (hIP : IrqPlatA arI AR) (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI)
    (hmbA : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQJI (L := L) arI AR σ (r.2.1, r.2.2) ⦄ :=
  afterInv_of_mcsIMN (WP.spec_mono hmcs fun r ⟨σ', h1, h2, ⟨Z', H', Cs', Ac', Lst', D', J'⟩, hR, hV⟩ =>
    ⟨σ', h1, h2, ⟨Z', H', Cs', Ac', Lst', D', J'⟩, hR, hV,
      hNS r.1 r.2 σ' ⟨Z', H', Cs', Ac', Lst', D', r.1, r.2, σ', J'.toHole⟩⟩) hM hIP hARI hAT hmbA e

end

end

end Fl4Proofs.P3
