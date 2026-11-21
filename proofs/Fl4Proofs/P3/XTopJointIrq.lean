/-
P3 (DESIGN.md §9): **`handle_interrupt` at `J`** (XTopJointPreempt's
`JIrqHyp`, l4v `handle_interrupt_corres`): FL4's `interrupt::handle_interrupt`
of a pending, unmasked line against the spec's `handle_interrupt`, from a
`JHoleAt` state (what the preemption path reaches), `XTopAt` after.

The correspondence, line by line (FL4's state word against the spec's
`interrupt_states`, IntRel's `irqSt`):
* a line above FL4's `irq::MAX` (127): FL4 masks and acknowledges it (arch
  operations), the spec too (`irq > maxIRQ`, 125 < i: machine operations);
* `IRQ_INACTIVE` (0): the spec fails (l4v excludes it by `valid_irq_masks`);
  the failure disjunct of `JIrqHyp` covers it;
* `IRQ_TIMER` (2): FL4 sets the node's `REPROGRAM` word and clears its
  `ARMED` word (l4h 0006: no deadline armed), the spec sets
  `reprogram_timer` (`ackDeadlineIRQ` is a no-op); `ARMED` is read by no
  relation (SchedArmed's `SchedRel.set_armed`); `XTopAt` by `xtop_sc_step`
  from the hole (node words are `TFoot` words);
* `IRQ_IPI` (3) and any other word: the spec's `irqReserved`
  (`handle_reserved_irq`, a no-op); FL4's `handle_ipi` does nothing for a
  line other than `RESCHEDULE_IPI` (127). DECISION: the IPI lines 126/127
  never reach `handle_interrupt` -- XTopJointPreempt's `IrqPlat.noIpi` [P]
  (one core: l4v's model is uniprocessor, seL4 C raises IPIs only with
  `ENABLE_SMP_SUPPORT`). With them excluded FL4's IPI state is the spec's
  reserved state on every other line;
* `IRQ_SIGNAL` (1): the IRQ node slot's cap (IntRel's `IrqRel.node`,
  `IntLayout.node`: a radix-0 CNode of the typed heap, so the slot relation
  gives the spec's cap); a notification cap with the send right: FL4's and
  the spec's `send_signal`, then the line masked; any other cap: only the
  mask. The signal at `J` (ScSignalJ's `signalJHyp_of`) needs `JAtZ` at the
  hole: `JHole.toJ` gives it when `OffOK` and `CurOwnW` hold there. The
  rest is named, `JIrqSigHyp` [W] (below).

Premises of `jIrqHyp_of`: `ARIface` (the mask keeps `AR`), `IrqPlat`
(`ackAR`), `ArchTotal`, `MIN_BUDGET` [P] (as elsewhere), `hNS` [S]
(`NativeScope` at `JHoleAt` states: no thread `RunningVM`; VT-x is outside
the native scope, DESIGN §5/§9; it discharges ScSignalJ's `SignalRestJHyp`)
and `JIrqSigHyp` [W]: the signal from a `JHole` at which `OffOK σ ∧ CurOwnW`
fails (a hole after a time update whose current head is not ready for the
consumed time: l4v's `cur_sc_offset_ready`, not carried by `JHole`; the
frames-from-the-base proof of `send_signal`, as ScChargeH/T do for the
charge, is not done).

`JPreemptRestHypN` [W]: XTopJointPreempt's `JPreemptRestHyp` at states in
the native scope (`NativeScope σ`; a `RUNNING_VM` current thread is the
scope premise `hNS` [S]); `jPreemptRestHyp_of` gives the old premise.

`hPre_ofI` / `dispatch_invokeJPI` / `dispatch_invokeJEPI`: XTopJointPreempt's
`hPre_of` / `dispatch_invokeJP` / `dispatch_invokeJEP` with `JIrqHyp`
replaced by these premises and `JPreemptRestHyp` by `JPreemptRestHypN`.
-/
import Fl4Proofs.P3.XTopJointPreempt
import Fl4Proofs.P3.SchedArmed
import Fl4Proofs.P3.ScSignalJ
import Fl4Proofs.P3.ScSignalJN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- The machine's IRQ mask of line `i` set to `b`. -/
def maskMs (σ : State Unit) (i : Irq) (b : Bool) : State Unit :=
  { σ with machineState := { σ.machineState with irqMasks := Function.update σ.machineState.irqMasks i b } }

theorem mem_dmo_ack (i : Irq) (σ : State Unit) : ((), σ) ∈ (doMachineOp (Z := Unit) (ackInterrupt i) σ).1 := by
  unfold doMachineOp ackInterrupt
  refine mem_bind_nd (x := (σ.machineState, σ)) rfl ?_
  refine mem_bind_nd (x := (((), σ.machineState), σ)) ⟨rfl, rfl⟩ ?_
  refine mem_bind_nd (x := ((), { σ with machineState := σ.machineState })) (Set.mem_singleton _) ?_
  rfl

theorem mem_dmo_mask (i : Irq) (b : Bool) (σ : State Unit) :
    ((), maskMs σ i b) ∈ (doMachineOp (Z := Unit) (maskInterrupt b i) σ).1 := by
  unfold doMachineOp maskInterrupt
  refine mem_bind_nd (x := (σ.machineState, σ)) rfl ?_
  refine mem_bind_nd (x := (((), (maskMs σ i b).machineState), σ)) ⟨rfl, rfl⟩ ?_
  refine mem_bind_nd (x := ((), maskMs σ i b)) (Set.mem_singleton _) ?_
  rfl

/-- A line above `maxIRQ`: masked and acknowledged. -/
theorem mem_hi_big {i : Irq} (h : i > maxIRQ) (σ : State Unit) :
    ((), maskMs σ i true) ∈ (handleInterrupt (Z := Unit) i σ).1 := by
  unfold handleInterrupt
  rw [if_pos h]
  unfold doMachineOp maskInterrupt ackInterrupt
  refine mem_bind_nd (x := (σ.machineState, σ)) rfl ?_
  refine mem_bind_nd (x := (((), (maskMs σ i true).machineState), σ))
    ⟨mem_bind_nd (x := ((), (maskMs σ i true).machineState)) rfl rfl, rfl⟩ ?_
  refine mem_bind_nd (x := ((), maskMs σ i true)) (Set.mem_singleton _) ?_
  rfl

/-- An inactive line: the spec fails. -/
theorem fail_hi_inactive {i : Irq} (h : ¬ i > maxIRQ) {σ : State Unit}
    (hst : σ.interruptStates i = .irqInactive) : (handleInterrupt (Z := Unit) i σ).2 := by
  unfold handleInterrupt
  rw [if_neg h]
  refine Or.inr ⟨(.irqInactive, σ), by show _ ∈ ({(σ.interruptStates i, σ)} : Set _); rw [hst]; rfl, ?_⟩
  exact Or.inl trivial

/-- A reserved line: nothing but the acknowledgement. -/
theorem mem_hi_reserved {i : Irq} (h : ¬ i > maxIRQ) {σ : State Unit}
    (hst : σ.interruptStates i = .irqReserved) : ((), σ) ∈ (handleInterrupt (Z := Unit) i σ).1 := by
  unfold handleInterrupt
  rw [if_neg h]
  refine mem_bind_nd (x := (.irqReserved, σ)) (by show _ ∈ ({(σ.interruptStates i, σ)} : Set _); rw [hst]; rfl) ?_
  exact mem_bind_nd (x := ((), σ)) rfl (mem_dmo_ack i σ)

/-- The timer line: `reprogram_timer` set. -/
theorem mem_hi_timer {i : Irq} (h : ¬ i > maxIRQ) {σ : State Unit}
    (hst : σ.interruptStates i = .irqTimer) :
    ((), { σ with reprogramTimer := true }) ∈ (handleInterrupt (Z := Unit) i σ).1 := by
  unfold handleInterrupt
  rw [if_neg h]
  refine mem_bind_nd (x := (.irqTimer, σ)) (by show _ ∈ ({(σ.interruptStates i, σ)} : Set _); rw [hst]; rfl) ?_
  refine mem_bind_nd (x := ((), σ)) (by unfold ackDeadlineIRQ; exact mem_dmo_ack deadlineIRQ σ) ?_
  exact mem_bind_nd (x := ((), { σ with reprogramTimer := true })) (Set.mem_singleton _) (mem_dmo_ack i _)

/-- A signal line: the handler's notification signalled (when its cap is a
notification cap with the send right), then the line masked. -/
theorem mem_hi_signal {i : Irq} (h : ¬ i > maxIRQ) {σ σ1 : State Unit}
    (hst : σ.interruptStates i = .irqSignal) {ac : Cap}
    (hcap : getCap (Z := Unit) (σ.interruptIrqNode i, []) σ = ({(ac, σ)}, False))
    (h1 : ((), σ1) ∈ (NonDet.when (isNtfnCap ac ∧ AllowSend ∈ capRights ac)
      (sendSignal (Z := Unit) (objRefOf ac) (capEpBadge ac)) σ).1) :
    ((), maskMs σ1 i true) ∈ (handleInterrupt (Z := Unit) i σ).1 := by
  unfold handleInterrupt
  rw [if_neg h]
  refine mem_bind_nd (x := (.irqSignal, σ)) (by show _ ∈ ({(σ.interruptStates i, σ)} : Set _); rw [hst]; rfl) ?_
  refine mem_bind_nd (x := ((σ.interruptIrqNode i, []), σ)) rfl ?_
  refine mem_bind_nd (x := (ac, σ)) (by rw [hcap]; rfl) ?_
  refine mem_bind_nd (x := ((), σ1)) h1 ?_
  exact mem_bind_nd (x := ((), maskMs σ1 i true)) (by unfold archMaskIrqSignal; exact mem_dmo_mask i true σ1)
    (mem_dmo_ack i _)

/-- `when` with a false condition. -/
theorem mem_when_false {P : Prop} [Decidable P] (hP : ¬ P) (m : NonDet (State Unit) Unit) (σ : State Unit) :
    ((), σ) ∈ (NonDet.when P m σ).1 := by
  unfold NonDet.when; rw [if_neg hP]; rfl

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- `XTopAt` at another machine state (same memory) and arch state. -/
theorem XTopAt.msAR {s : S} {a : A} {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ)
    (ms : Fl4Spec.MachineState) (a' : A) (hum : ms.underlyingMemory = σ.machineState.underlyingMemory)
    (hAR : AR a' σ.archState.x64CurrentCr3) : XTopAt (L := L) AR Z s a' { σ with machineState := ms } :=
  hX.frameStep (P1.WritesIn.refl s (fun _ => False)) (fun _ h => h.elim) (fun _ h => h.elim) (fun _ h => h.elim) id
    rfl rfl rfl rfl hum rfl rfl (hX.fin.1.1.1.spec_congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    ⟨hX.fin.1.1.2.2.2.1.st, hX.fin.1.1.2.2.2.1.node⟩ hX.fin.1.1.2.2.2.2.1 hX.rel.2.2.2.1 hAR

theorem irq_state_eq' (s : S) (irq : U64) :
    interrupt.irq_state st s irq = ok (L.mem s (irqStA (L.ksb s) irq)) := by
  unfold interrupt.irq_state obj.ks_get
  simp only [state_off_eq, L.ks_base_eq, lift, L.read_eq, bind_ok]
  rfl

theorem irqSig_eq : interrupt.IRQ_SIGNAL = 1#u64 := by unfold interrupt.IRQ_SIGNAL; rfl
theorem irqTimer_eq : interrupt.IRQ_TIMER = 2#u64 := by unfold interrupt.IRQ_TIMER; rfl
theorem irqIpi_eq : interrupt.IRQ_IPI = 3#u64 := by unfold interrupt.IRQ_IPI; rfl
theorem irqInactive_eq : interrupt.IRQ_INACTIVE = 0#u64 := by unfold interrupt.IRQ_INACTIVE; rfl

theorem irq_max_eq : layout.irq.MAX = ok 127#u64 := by
  obtain ⟨v, hv, rfl⟩ := spec_exists P0.Consts.layout.irq.MAX.spec; exact hv

theorem irq_resched_eq : layout.irq.RESCHEDULE_IPI = ok 127#u64 := by
  obtain ⟨v, hv, rfl⟩ := spec_exists P0.Consts.layout.irq.RESCHEDULE_IPI.spec; exact hv

variable (arI) in
/-- **The signal of an IRQ line from a hole that is not `JAtZ`** [W]
(module docstring): from a `JHole` at which `OffOK ∧ CurOwnW` fails, the
handler slot of a line holding a notification cap with the send right,
FL4's `send_signal` refines the spec's (`XTopAt` after). l4v: part of
`handle_interrupt_corres` (`send_signal_corres` under `invs`); here a proof
gap (the frames-from-the-base `send_signal`), not a missing invariant. -/
def JIrqSigHyp (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s0 : S) (a0 : A)
    (σ0 : Fl4Spec.State Unit) (s : S) (a : A) (σ : Fl4Spec.State Unit) (w n badge : U64) (r : Bool),
    JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ → ¬ (OffOK σ ∧ CurOwnW Z.T Z.C σ) →
    w.val < 128 → capAt (L.mem s) (nodeA (L.ksb s) w) = ok (.Notification n badge true r) →
    notification.send_signal st arI s a n badge ⦃ r' =>
      ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).1, ∃ Z', XTopAt (L := L) AR Z' r'.1 r'.2 z.2 ⦄

set_option maxHeartbeats 16000000 in
/-- **`handle_interrupt` from one `JHole`** (module docstring): the signal
from the hole when it is not `JAtZ` (`¬ (OffOK ∧ CurOwnW)`) is the premise
`hSig` of this hole only (`jIrqHyp_of` passes `JIrqSigHyp`; from a `JAtZ`
state it is vacuous, XTopJointPreemptZ). -/
theorem JHole.handleIrqJN (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlat arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ)
    (hN : NativeScope σ)
    (hSig : ¬ (OffOK σ ∧ CurOwnW Z.T Z.C σ) → ∀ (w n badge : U64) (r : Bool),
      w.val < 128 → capAt (L.mem s) (nodeA (L.ksb s) w) = ok (.Notification n badge true r) →
      notification.send_signal st arI s a n badge ⦃ r' =>
        ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).1, ∃ Z', XTopAt (L := L) AR Z' r'.1 r'.2 z.2 ⦄)
    (w : U64) (i : Fl4Spec.Irq) (hwi : w.val = i.toNat) (h126 : w.val ≠ 126) (h127 : w.val ≠ 127) :
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄ := by
  have hX := Hh.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hIR : IrqRel (L.mem s) (L.ksb s) σ := hX.fin.1.1.2.2.2.1
  have hARa : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  have hks : L.ksb s = L.ksb s0 := Hh.ws.1
  have hiw : (BitVec.ofNat 8 w.val : Fl4Spec.Irq) = i := by
    apply BitVec.eq_of_toNat_eq; simp [hwi]
  -- the acknowledgement keeps `XTopAt`
  have hack : ∀ (s1 : S) (a1 : A) (z : Unit × Fl4Spec.State Unit) (Z' : XSets),
      z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1 → XTopAt (L := L) AR Z' s1 a1 z.2 →
      (do let a2 ← arI.ack_irq a1 w; ok (s1, a2)) ⦃ r =>
        (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
          ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄ := by
    intro s1 a1 z Z' hz hX1
    refine WP.spec_bind (hIP.ackAR a1 w _ hX1.fin.1.1.2.2.2.2.2.2) ?_
    intro a2 hA2
    exact (WP.spec_ok _).2 (Or.inr ⟨z, hz, Z', hX1.arch hA2⟩)
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
    exact hack s a1 _ Z (mem_hi_big hgt σ) (hX.msAR _ a1 rfl hA1)
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
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄ →
        (do let (s1, a1) ← m; let a2 ← arI.ack_irq a1 w; ok (s1, a2)) ⦃ r =>
          (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
            ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄ := by
      intro m hm
      refine WP.spec_bind hm ?_
      rintro ⟨s1, a1⟩ (hf | ⟨z, hz, Z', hX1⟩)
      · refine WP.spec_bind (hAT.ack_irq a1 w) ?_
        intro a2 _
        exact (WP.spec_ok _).2 (Or.inl hf)
      · exact hack s1 a1 z Z' hz hX1
    refine key _ ?_
    by_cases h1 : v = 1#u64
    · -- a signal line
      rw [if_pos h1]
      have hsig : σ.interruptStates i = .irqSignal := by rw [hst, h1]; rfl
      have hL : IntLayout Z.th (L.ksb s) := by rw [hks]; exact Hh.j0.intL
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
      have hmask : ∀ (s3 : S) (a2 : A) (σ1 : Fl4Spec.State Unit) (Z' : XSets),
          ((), σ1) ∈ (Fl4Spec.NonDet.when (Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac)
            (Fl4Spec.sendSignal (Z := Unit) (Fl4Spec.objRefOf ac) (Fl4Spec.capEpBadge ac)) σ).1 →
          XTopAt (L := L) AR Z' s3 a2 σ1 →
          (do let a3 ← arI.mask_irq a2 w true; ok (s3, a3)) ⦃ r =>
            (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
              ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄ := by
        intro s3 a2 σ1 Z' h1' hX1
        obtain ⟨a3, ha3⟩ := maskIrq_total arI hAT a2 w true
        rw [ha3]
        simp only [bind_ok, WP.spec_ok]
        have hA3 := hARI.mask _ _ _ hX1.fin.1.1.2.2.2.2.2.2 (Or.inr (Or.inl ⟨w, true, ha3⟩))
        exact Or.inr ⟨((), maskMs σ1 i true), mem_hi_signal hle hsig hgc h1', Z', hX1.msAR _ a3 rfl hA3⟩
      have hnone : ∀ (hP : ¬ (Fl4Spec.isNtfnCap ac ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights ac)),
          (do let a3 ← arI.mask_irq a w true; ok (s, a3)) ⦃ r =>
            (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
              ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄ :=
        fun hP => hmask s a σ Z (mem_when_false hP _ σ) hX
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
          by_cases hO : OffOK σ ∧ CurOwnW Z.T Z.C σ
          · obtain ⟨Lst', J⟩ := Hh.toJ hO.1 hO.2
            have hA : AbsSlot Z.th ((nodeA (L.ksb s) w).bv, []) := ⟨_, rfl, Or.inl hnode⟩
            have hpN := (J.slotN hA (by rw [cslotAddr_nil]; exact hcap)).1
            refine WP.spec_bind (J.signal_atN hAT hmb hN p b hpN) ?_
            rintro ⟨s2, a2⟩ ⟨σ', V', Ac', Lst'', D', hsp, -, J'⟩
            exact hmask s2 a2 σ' _ (hwhen σ' (by rw [hsp]; rfl)) J'.xtop
          · refine WP.spec_bind (hSig hO w p b rv hw128 hcap) ?_
            rintro ⟨s2, a2⟩ ⟨z, hz, Z', hX2⟩
            exact hmask s2 a2 z.2 Z' (hwhen z.2 hz) hX2
      | _ =>
        simp only [bind_ok]
        exact hnone (by rw [hac]; simp [absCap, Fl4Spec.isNtfnCap])
    rw [if_neg h1]
    by_cases h2 : v = 2#u64
    · -- the timer line
      rw [if_pos h2]
      have htm : σ.interruptStates i = .irqTimer := by rw [hst, h2]; rfl
      obtain ⟨Q, R0, hc, -⟩ := hS.lists
      step with P1.LawfulStore.cur_cpu_spec as ⟨cc, ecc⟩
      step with P1.obj.node_set.spec as ⟨s2, es2⟩
      step with P1.obj.node_set.spec as ⟨s3, es3⟩
      subst es2 es3 ecc
      rw [hc.cur]
      have hN : P1.NodePlaced st Z.T s Z.c := hc.node
      obtain ⟨hS2, hF2, -⟩ := hS.set_reprogram
      set s2 := L.wr s (L.nodeAt s Z.c layout.node.REPROGRAM) 1#u64 with hs2
      have hk2 : L.ksb s2 = L.ksb s := L.ksb_wr _ _ _
      have hna : L.nodeAt s2 Z.c layout.node.ARMED = L.nodeAt s Z.c layout.node.ARMED :=
        nodeAt_ksb hk2 _ _
      obtain ⟨hS3, hF3⟩ := hS2.set_armed 0#u64
      rw [hna] at hS3 hF3 ⊢
      set s3 := L.wr s2 (L.nodeAt s Z.c layout.node.ARMED) 0#u64 with hs3
      have hw2 : P1.WritesIn st s s2 (SFoot st Z.T Z.c s) :=
        sfoot_wr_node hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) _
      have hw3 : P1.WritesIn st s2 s3 (SFoot st Z.T Z.c s2) := by
        have := sfoot_wr_node (nodePlaced_ksb hN hk2) (o := layout.node.ARMED) (by simp [layout.node.ARMED])
          (by simp [layout.node.ARMED]) 0#u64
        rw [hna] at this; exact this
      have hw : P1.WritesIn st s s3 (TFoot st Z.T Z.N Z.C Z.c s σ) :=
        (Sched.WritesIn.sfoot_trans hw2 hw3).mono fun _ h => Or.inl (Or.inl h)
      have hR3 : NtfnStateRel Z.N Z.T (L.mem s3) { σ with reprogramTimer := true } :=
        hR.frame hS.placed (fun b hb hf => (hF3 b hb hf).trans (hF2 b hb hf))
          (by exact KView.refl σ)
      have hK : ScTKw (fun p => p = σ.curThread) σ { σ with reprogramTimer := true } :=
        ⟨fun p => OTK.refl _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hNk : ∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val := by
        rw [hks]; exact Hh.j0.nk
      have hX3 : XTopAt (L := L) AR Z s3 a { σ with reprogramTimer := true } :=
        xtop_sc_step hX Hh.j0.ip hNk hw hK hS3 hR3 id
      try simp only [WP.spec_ok]
      exact Or.inr ⟨_, mem_hi_timer hle htm, Z, hX3⟩
    rw [if_neg h2]
    by_cases h3 : v = 3#u64
    · -- an IPI state on a line other than the IPI lines: reserved, nothing
      rw [if_pos h3]
      have hres : σ.interruptStates i = .irqReserved := by rw [hst, h3]; rfl
      unfold smp.handle_ipi
      rw [irq_resched_eq]
      have hne : ¬ w = 127#u64 := fun e => h127 (by rw [e]; rfl)
      simp only [bind_ok, hne, ↓reduceIte, WP.spec_ok]
      exact Or.inr ⟨_, mem_hi_reserved hle hres, Z, hX⟩
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
      exact Or.inr ⟨_, mem_hi_reserved hle hres, Z, hX⟩

/-- `JHole.handleIrqJN` from the ∀-form `hNS` (the pre-g3e statement). -/
theorem JHole.handleIrqJ (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlat arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ)
    (hSig : ¬ (OffOK σ ∧ CurOwnW Z.T Z.C σ) → ∀ (w n badge : U64) (r : Bool),
      w.val < 128 → capAt (L.mem s) (nodeA (L.ksb s) w) = ok (.Notification n badge true r) →
      notification.send_signal st arI s a n badge ⦃ r' =>
        ∃ z ∈ (Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ).1, ∃ Z', XTopAt (L := L) AR Z' r'.1 r'.2 z.2 ⦄)
    (w : U64) (i : Fl4Spec.Irq) (hwi : w.val = i.toNat) (h126 : w.val ≠ 126) (h127 : w.val ≠ 127) :
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄ :=
  Hh.handleIrqJN hARI hAT hIP hmb (hNS s a σ ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hSig w i hwi h126 h127


/-- **`handle_interrupt` at `J`** (module docstring): `JIrqHyp` from the
premises named there (`JHole.handleIrqJ` with `JIrqSigHyp`). -/
theorem jIrqHyp_of (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlat arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hSig : JIrqSigHyp (L := L) arI AR) :
    JIrqHyp (L := L) arI AR := by
  intro s a σ w i hJ hwi _ h126 h127
  obtain ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩ := hJ
  exact Hh.handleIrqJ hARI hAT hIP hmb hNS
    (fun hO w' n b r h1 h2 => hSig Z H Cs Ac Lst D s0 a0 σ0 s a σ w' n b r Hh hO h1 h2) w i hwi h126 h127

/-- **`JIrqHyp` per state** (g3e): at every `JHoleAt` state with
`NativeScope` there, no ∀-form `hNS`. -/
theorem jIrqHyp_ofN (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlat arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hSig : JIrqSigHyp (L := L) arI AR) :
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (w : U64) (i : Fl4Spec.Irq),
    JHoleAt (L := L) arI AR s a σ → NativeScope σ → w.val = i.toNat → σ.machineState.irqMasks i = false →
    w.val ≠ 126 → w.val ≠ 127 →
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄ := by
  intro s a σ w i hJ hN hwi _ h126 h127
  obtain ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩ := hJ
  exact Hh.handleIrqJN hARI hAT hIP hmb hN
    (fun hO w' n b r h1 h2 => hSig Z H Cs Ac Lst D s0 a0 σ0 s a σ w' n b r Hh hO h1 h2) w i hwi h126 h127

variable (arI) in
/-- **`JPreemptRestHyp` in the native scope** [W] (module docstring): the
preemption path at the `JHoleAt` states outside `PPCov ∨ PPCovT` where no
thread is `RunningVM` (that case is the scope premise `hNS` [S]). -/
def JPreemptRestHypN (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
    ¬ (PPCov σ ∨ PPCovT σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHyp_of
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (h : JPreemptRestHypN (L := L) arI AR) : JPreemptRestHyp (L := L) arI AR :=
  fun s a σ hJ hc => h s a σ hJ (hNS s a σ hJ) hc

/-- **`invoke_afterJ`'s `hPre` without `JIrqHyp`** (module docstring). -/
theorem hPre_ofI (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hSig : JIrqSigHyp (L := L) arI AR) (hRest : JPreemptRestHypN (L := L) arI AR) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ :=
  hPre_of hARI.toARKeep hA hnd hP hmrt hIP (jIrqHyp_of hARI hA hIP hP.minBudget hNS hSig)
    (jPreemptRestHyp_of hNS hRest)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJP` without `JIrqHyp`**. -/
theorem dispatch_invokeJPI [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hSig : JIrqSigHyp (L := L) arI AR) (hRest : JPreemptRestHypN (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofI hARI hA hnd hPP hmrt hIP hNS hSig hRest)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEP` without `JIrqHyp`**. -/
theorem dispatch_invokeJEPI [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hSig : JIrqSigHyp (L := L) arI AR) (hRest : JPreemptRestHypN (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofI hARI hA hnd hPP hmrt hIP hNS hSig hRest)

end

end

end Fl4Proofs.P3
