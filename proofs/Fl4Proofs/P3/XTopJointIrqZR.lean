/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch10 (2)): **`handle_interrupt`
from a `JAt` state ends in `JAt`** (l4v `handle_interrupt_invs`), and the
covered preemption path with `JAt` after in every branch.

XTopJointIrq's `JHole.handleIrqJ` ends in a bare `XTopAt`; XTopJointPreemptZ's
`jIrqHypZ_of` applies it to a `JAt` state. From a `JAtZ` state every branch of
FL4's `handle_interrupt` keeps `JAtZ` (copies; XTopJointIrq / XTopJointPreempt*
untouched):

* a line above FL4's maximum: mask and acknowledgement, arch operations and the
  spec's machine-state mask (`JAtZ.msArJ`);
* the signal line: `signalJHyp_of` already ends in `JAtZ`, then the mask;
* the timer line: `REPROGRAM := 1` (`JAtZ.reprogramJ`, ScFireJ) and
  `ARMED := 0`, a scheduler step with the spec unchanged (`armed_schedStep`:
  `SchedRel.set_armed`, the node word is in `SFootI`, P1's `nodew_bxc` for
  `BlkOK`; `JAtZ.armedJ` by `JAtZ.schedJ`);
* reserved/IPI lines: nothing; an inactive line: the spec fails.

`JIrqHypJ` / `jIrqHypJ_of` (no premise beyond `jIrqHypZ_of`'s);
`JHole.afterInvJZJ` / `afterInv_of_mcsJ`: XTopJointPreemptZ/I's
`afterInvJZ` / `afterInv_of_mcs` with `PPQJ` after (spec failure or `JAt`, no
`XTopAt` disjunct); `RestE`: the holes `JPreemptRestHypE` [W] (kp14) covers;
`PPQC`: `PPQJ`, or `PPQ` at a `RestE` hole; `hPre_ofZEC`,
`dispatch_invokeJEPZEC`: XTopJointPreemptE's `hPre_ofZE` / `dispatch_invokeJEPZE`
ending in `PPQC` (every covered branch through `afterInvJZJ` / `afterInv_of_mcsJ`).
-/
import Fl4Proofs.P3.XTopJointKEntry4
import Fl4Proofs.P3.XTopJointPreemptE
import Fl4Proofs.P3.SchedArmed
import Fl4Proofs.P1.QueueEntry
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The node's `ARMED` word written, the spec unchanged, is a scheduler
step** (module docstring). -/
theorem armed_schedStep {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} {c : U64} (hc : L.cpu s = c)
    (v : U64) : SchedStep (L := L) th s σ (L.wr s (L.nodeAt s c layout.node.ARMED) v) σ := by
  subst hc
  refine ⟨by constructor <;> rfl, fun N T C c _ hS _ => ?_, SchedQOK.refl σ, ?_⟩
  · obtain ⟨Q, R0, hcc, -⟩ := hS.lists
    have hN := hcc.node
    rw [hcc.cur]
    have hA : P1.Aligned (L.nodeAt s c layout.node.ARMED) :=
      P1.nodeAt_aligned hN (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])
    have hv := P1.nodeAt_val hN (off := layout.node.ARMED) (by simp [layout.node.ARMED])
    have h80 : layout.node.ARMED.val = 80 := by simp [layout.node.ARMED]
    have hw' : P1.WritesIn st s (L.wr s (L.nodeAt s c layout.node.ARMED) v) (Sched.SFootI st T c s) :=
      (P1.writesIn_wr hA).mono fun b hb => by
        subst hb
        refine Or.inr ⟨?_, ?_, ?_⟩ <;> rw [hv, h80] <;> omega
    exact ⟨(hS.set_armed v).1, hw'.mono fun b hb => hb.elim Or.inl fun h => Or.inr (Or.inl h),
      fun hD => domRel_iff.1 ((domRel_iff.2 hD).of_same (domSame_of_sfootI hS hw') rfl rfl)⟩
  · intro T Cs Ω H Sg Rp Scs Nt Z Ac _ h
    exact (P1.nodew_bxc (o := layout.node.ARMED) (v := v) h.bxi (by simp [layout.node.ARMED, P1.LowFree])
      (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])).1.1.blk

/-- **The `ARMED` write at `J`** (module docstring). -/
theorem JAtZ.armedJ {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {c : U64} (hc : L.cpu s = c) (v : U64) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' (L.wr s (L.nodeAt s c layout.node.ARMED) v) a σ :=
  J.schedJ (armed_schedStep hc v)

variable (arI) in
/-- **`handle_interrupt` at `J` from a `JAt` state, `JAt` after** (l4v
`handle_interrupt_invs`; module docstring). -/
def JIrqHypJ (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (w : U64) (i : Fl4Spec.Irq),
    JAt (L := L) arI AR s a σ → w.val = i.toNat → σ.machineState.irqMasks i = false →
    w.val ≠ 126 → w.val ≠ 127 →
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄

set_option maxHeartbeats 16000000 in
/-- **`handle_interrupt` from a `JAtZ` state** (module docstring; the
branches of XTopJointIrq's `JHole.handleIrqJ` at `JAtZ`). -/
theorem JAtZ.handleIrqJJN (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlat arI AR)
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

/-- `JAtZ.handleIrqJJN` from the ∀-form `hNS` (the pre-g3e statement). -/
theorem JAtZ.handleIrqJJ (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlat arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (w : U64) (i : Fl4Spec.Irq) (hwi : w.val = i.toNat) (h126 : w.val ≠ 126) (h127 : w.val ≠ 127) :
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ :=
  J.handleIrqJJN hARI hAT hIP hmb (hNS s a σ ⟨Z, H, Cs, Ac, Lst, D, s, a, σ, J.toHole⟩) w i hwi h126 h127


/-- **`JIrqHypJ` from the platform facts alone** (module docstring). -/
theorem jIrqHypJ_of (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlat arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) :
    JIrqHypJ (L := L) arI AR := by
  intro s a σ w i hJ hwi _ h126 h127
  obtain ⟨Z, H, Cs, Ac, Lst, D, J⟩ := hJ
  exact J.handleIrqJJ hARI hAT hIP hmb hNS w i hwi h126 h127

/-- **`JIrqHypJ` per state** (g3e): at every `JAt` state with `NativeScope`
there, no ∀-form `hNS`. -/
theorem jIrqHypJ_ofN (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlat arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (w : U64) (i : Fl4Spec.Irq),
    JAt (L := L) arI AR s a σ → NativeScope σ → w.val = i.toNat → σ.machineState.irqMasks i = false →
    w.val ≠ 126 → w.val ≠ 127 →
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  intro s a σ w i hJ hN hwi _ h126 h127
  obtain ⟨Z, H, Cs, Ac, Lst, D, J⟩ := hJ
  exact J.handleIrqJJN hARI hAT hIP hmb hN w i hwi h126 h127

variable (arI) in
/-- What the covered preemption path ends in, `JAt` in every branch: a spec
failure or an outcome of `preemption_path` from `σ1` with `JAt` after. -/
def PPQJ (AR : A → Fl4Spec.Cr3 → Prop) (σ1 : Fl4Spec.State Unit) (r : S × A) : Prop :=
  (Fl4Spec.preemptionPath (Z := Unit) σ1).2 ∨ ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1,
    JAt (L := L) arI AR r.1 r.2 z.2

theorem PPQJ.toPPQ {σ1 : Fl4Spec.State Unit} {r : S × A} (h : PPQJ (L := L) arI AR σ1 r) :
    PPQ (L := L) arI AR σ1 r := by
  rcases h with h | ⟨z, hz, ⟨Z, H, Cs, Ac, Lst, D, J⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨z, hz, Or.inl ⟨Z, H, Cs, Ac, Lst, D, _, _, _, J.toHole⟩⟩

set_option maxHeartbeats 16000000 in
/-- **`JHole.afterInvJZ` with `JAt` after a handled line** (module docstring). -/
theorem JHole.afterInvJZJ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR) (hIrq : JIrqHypJ (L := L) arI AR) (hcov : PPCov σ ∨ PPCovT σ) (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQJ (L := L) arI AR σ (r.2.1, r.2.2) ⦄ := by
  unfold syscall.after_invocation
  refine WP.spec_bind (Hh.mcsPPJZ hT hAT hnd hmrt hmb hcov) ?_
  rintro ⟨s1, a1⟩ ⟨σ', hm, hmf, Z', H', Cs', Ac', Lst', D', J'⟩
  have hAR1 : AR a1 σ'.archState.x64CurrentCr3 := J'.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (hIP.take a1 σ') (hIP.takeAR a1 _ hAR1)) (hIP.noIpi a1)) ?_
  rintro ⟨w, a2⟩ ⟨⟨⟨irq, ms, hIq, hnone, hsome, hum⟩, hAR2⟩, h126, h127⟩
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
    refine (WP.spec_ok _).2 ⟨rfl, Or.inr ⟨((), { σ' with machineState := ms }),
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
    refine WP.spec_bind (hIrq s1 a2 _ w i ⟨Z', H', Cs', Ac', Lst2, D', J2⟩ hwi hmask h126 h127) ?_
    rintro ⟨s2, a3⟩ (hf | ⟨z, hz, hJ⟩)
    · exact (WP.spec_ok _).2 ⟨rfl, Or.inl (hmf (fail_maybeHandle_some hIq hf))⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Or.inr ⟨z, hm _ (mem_maybeHandle_some hIq hz), hJ⟩⟩

set_option maxHeartbeats 16000000 in
/-- **`afterInv_of_mcs` with `JAt` after a handled line** (module docstring). -/
theorem afterInv_of_mcsJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hmcs : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ⦄)
    (hIP : IrqPlat arI AR) (hIrq : JIrqHypJ (L := L) arI AR) (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQJ (L := L) arI AR σ (r.2.1, r.2.2) ⦄ := by
  unfold syscall.after_invocation
  refine WP.spec_bind hmcs ?_
  rintro ⟨s1, a1⟩ ⟨σ', hm, hmf, Z', H', Cs', Ac', Lst', D', J'⟩
  have hAR1 : AR a1 σ'.archState.x64CurrentCr3 := J'.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (hIP.take a1 σ') (hIP.takeAR a1 _ hAR1)) (hIP.noIpi a1)) ?_
  rintro ⟨w, a2⟩ ⟨⟨⟨irq, ms, hIq, hnone, hsome, hum⟩, hAR2⟩, h126, h127⟩
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
    refine (WP.spec_ok _).2 ⟨rfl, Or.inr ⟨((), { σ' with machineState := ms }),
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
    refine WP.spec_bind (hIrq s1 a2 _ w i ⟨Z', H', Cs', Ac', Lst2, D', J2⟩ hwi hmask h126 h127) ?_
    rintro ⟨s2, a3⟩ (hf | ⟨z, hz, hJ⟩)
    · exact (WP.spec_ok _).2 ⟨rfl, Or.inl (hmf (fail_maybeHandle_some hIq hf))⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Or.inr ⟨z, hm _ (mem_maybeHandle_some hIq hz), hJ⟩⟩

/-- **The holes `JPreemptRestHypE` covers** (kp14): outside `PPCov ∨ PPCovT ∨
PPCovI`, `CurInv`, a schedulable current thread, an insufficient head. -/
def RestE (σ : Fl4Spec.State Unit) : Prop :=
  ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) ∧ CurInv σ ∧ Fl4Spec.schedulable σ.curThread σ = true ∧
    ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true)

variable (arI) in
/-- **What the preemption path ends in, the covered cases at `JAt`**: `PPQJ`,
or (only at a hole of `RestE`, `JPreemptRestHypE`'s domain) `PPQ`. -/
def PPQC (AR : A → Fl4Spec.Cr3 → Prop) (σ1 : Fl4Spec.State Unit) (r : S × A) : Prop :=
  PPQJ (L := L) arI AR σ1 r ∨ (RestE σ1 ∧ PPQ (L := L) arI AR σ1 r)

theorem PPQC.toPPQ {σ1 : Fl4Spec.State Unit} {r : S × A} (h : PPQC (L := L) arI AR σ1 r) :
    PPQ (L := L) arI AR σ1 r :=
  h.elim PPQJ.toPPQ And.right

/-- **`hPre_ofZE` ending in `PPQC`** (module docstring). -/
theorem hPre_ofZEC (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypE (L := L) arI AR) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQC (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 _ h
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, hTs⟩, hni, hns, hfr, hct, hcg⟩ :=
    jAtPre_holeL hARI.toARKeep hA hnd hP h
  have hIrq := jIrqHypJ_of hARI hA hIP hP.minBudget hNS
  by_cases hc : PPCov σ1 ∨ PPCovT σ1
  · exact WP.spec_mono (Hh.afterInvJZJ hTs hA hnd (hmrt a1) (hP.minBudget a1) hIP hIrq hc _)
      fun _ h => Or.inl h.2
  by_cases hi : PPCovI σ1
  · exact WP.spec_mono (afterInv_of_mcsJ (Hh.mcsPPJI hi) hIP hIrq _) fun _ h => Or.inl h.2
  by_cases hC : CurInv σ1
  · cases hsc : Fl4Spec.schedulable σ1.curThread σ1 with
    | true =>
      by_cases hsuf : ∀ y n, σ1.kheap σ1.curSc = some (.schedContext y n) →
          Fl4Spec.refillSufficient σ1.consumedTime (Fl4Spec.refillHd y) = true
      · exact WP.spec_mono (afterInv_of_mcsJ (Hh.mcsPPJS hTs hA hnd (hP.minBudget a1) hC hni hsc hsuf)
          hIP hIrq _) fun _ h => Or.inl h.2
      · have hnc : ¬ (PPCov σ1 ∨ PPCovT σ1 ∨ PPCovI σ1) :=
          fun h' => h'.elim (fun h2 => hc (Or.inl h2)) fun h2 => h2.elim (fun h3 => hc (Or.inr h3)) hi
        exact WP.spec_mono (hRest s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩
          (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hni hns hfr hct hcg hC hsc hsuf hnc)
          fun _ h => Or.inr ⟨⟨hnc, hC, hsc, hsuf⟩, h⟩
    | false =>
      exact WP.spec_mono (afterInv_of_mcsJ (Hh.mcsPPJC hA (hmrt a1) (hP.minBudget a1) hC hni hns hsc)
        hIP hIrq _) fun _ h => Or.inl h.2
  · have hsch : Fl4Spec.schedulable σ1.curThread σ1 = false := by
      cases e : Fl4Spec.schedulable σ1.curThread σ1 with
      | false => rfl
      | true => exact absurd (curInv_of_sched hct e) hC
    exact WP.spec_mono (afterInv_of_mcsJ (Hh.mcsPPJU hA (hmrt a1) (hP.minBudget a1) hC hct hfr hcg hsch hi)
      hIP hIrq _) fun _ h => Or.inl h.2

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPZE` ending in `PPQC`** (module docstring). -/
theorem dispatch_invokeJEPZEC [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypE (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQC (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZEC hARI hA hnd hPP hmrt hIP hNS hRest)

end

end

end Fl4Proofs.P3
