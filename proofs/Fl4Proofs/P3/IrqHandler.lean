/-
P3 (DESIGN.md §9), interrupts: **the IRQHandler invocations** (FL4
`interrupt::decode_irq_handler`, labels 34..36: `Ack`, `SetNotification`,
`Clear`) against l4v `decode_irq_handler_invocation`, then `set_thread_state
Restart` and `invoke_irq_handler` (as `handle_invocation` runs them).

`Ack` unmasks the IRQ (the spec's machine op, FL4's arch op `mask_irq`,
assumed total). `SetNotification` and `Clear` delete the cap in the IRQ's
node slot (`delete_one_keep`: a notification cap or nothing there,
`IrqSlotOK`); `SetNotification` then inserts the given notification cap
(`insert_full`). The IRQ node slots are radix-0 CNodes of the typed heap
(`IntLayout`, `IrqRel`); the invoked cap's IRQ is one FL4 has (< 128); the
extra cap's slot is a CNode slot (`ExtraSRel`) other than the IRQ's node
slot (the IRQ node is not in any user CSpace).

Errors: FL4's `SysErrRel`, plus `InvalidCapability` (`ErrRel`).
-/
import Fl4Proofs.P3.IntRel
import Fl4Proofs.P3.DelOne
import Fl4Proofs.P3.CnodeCopy
import Fl4Proofs.P3.StepSem
import Fl4Proofs.P3.TcbCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- Syscall errors, with invalid-capability errors. -/
def ErrRel (e : error.Exc) (e' : Fl4Spec.SyscallError) : Prop :=
  SysErrRel e e' ∨ ∃ n : U64, e = .Sys (.InvalidCapability n) ∧ e' = .invalidCapability n.val

/-- The first extra cap: none (`extra[0]` null, no caps), or the cap of a
slot of a CNode of the typed heap, with its slot. -/
def ExtraSRel (th : TypedHeap) (mem : U64 → U64) (x0 : U64) (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop :=
  (x0 = 0#u64 ∧ cps = []) ∨
  (x0 ≠ 0#u64 ∧ ∃ ps rs idxs rest, th ps = some (.cnode rs) ∧ idxs.length = rs ∧ x0 = cslotAddr (ps.bv, idxs) ∧
    cps = (absCap (capV mem x0), (ps.bv, idxs)) :: rest)

/-- An IRQ node slot holds nothing or a notification cap. -/
def IrqSlotOK (mem : U64 → U64) (x : U64) : Prop :=
  capV mem x = .Null ∨ ∃ p b w r, capV mem x = .Notification p b w r

@[simp] theorem lbl_ack_val : fl4_abi.label.IRQAckIRQ.val = 34 := by simp [fl4_abi.label.IRQAckIRQ]
@[simp] theorem lbl_set_val : fl4_abi.label.IRQSetIRQHandler.val = 35 := by simp [fl4_abi.label.IRQSetIRQHandler]
@[simp] theorem lbl_clear_val : fl4_abi.label.IRQClearIRQHandler.val = 36 := by
  simp [fl4_abi.label.IRQClearIRQHandler]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The run of an IRQHandler invocation** (StepSem's `Steps`, or the
caller's restart, the deletion of a notification cap from a CNode slot, then
primitive steps): a notification cap's deletion is no primitive step, so it
is recorded here for each relation to prove with its own invariant
(XTopIrqH's `IrqSteps.xtop` from `XDelNtfnHyp`, XTopJointIrqL at `J` with
the entry's `LiveJ`). -/
def IrqSteps (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A)
    (σ' : Fl4Spec.State Unit) : Prop :=
  Steps (L := L) arI th s ar σ s' a' σ' ∨
  ∃ (ct : U64) (s2 : S) (σ1 : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r : Bool) (s3 : S) (a3 : A)
    (σ3 : Fl4Spec.State Unit), sched.cur_thread st s = ok ct ∧ sched.set_thread_state st s ct sched.TS_RESTART = ok s2 ∧
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    Steps (L := L) arI th s ar σ s2 ar σ1 ∧ AbsSlot th sl ∧ (∃ q, sl.1 = q.bv ∧ th q = some (.cnode sl.2.length)) ∧
    capV (L.mem s2) (cslotAddr sl) = .Notification p b w r ∧
    cdt.delete_one st arI s2 ar (cslotAddr sl) = ok (s3, a3) ∧
    ((), σ3) ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ1).1 ∧ Steps (L := L) arI th s3 a3 σ3 s' a' σ'

/-- The outcome of an IRQHandler invocation against a spec decode `m`: the
same error with the state unchanged, or an invocation after which (with
`set_thread_state Restart` first) `invoke_irq_handler` has an outcome in a
related state, with `FinInv`; with the kernel-global base kept, the run
from `(s, ar, σ)` (`IrqSteps`). -/
def HPost (th : TypedHeap) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.IrqHandlerInvocation)
    (s : S) (ar : A) : core.result.Result Unit error.Exc × S × A → Prop
  | (.Err e, s', a') => s' = s ∧ (∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∧ a' = ar
  | (.Ok (), s', a') => ∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      ∃ σ' G', ((), σ') ∈ (Fl4Spec.invokeIrqHandler (Z := Unit) inv σ1).1 ∧ CRel th (L.mem s') σ' G' ∧
        FinInv th (L.mem s') σ' G' ∧ MdbStep (L.mem s) G (L.mem s') G' ∧
        (L.ksb s' = L.ksb s → CurRun σ → IrqSteps (L := L) arI th s ar σ s' a' σ')

/-- **`IrqSteps` through `delete_one` of a null or notification cap** after
the caller's restart (a null cap's deletion changes nothing: `Steps`). -/
theorem IrqSteps.of_del {th : TypedHeap} {s s2 s3 s' : S} {ar a3 a' : A}
    {σ σ1 σ3 σ' : Fl4Spec.State Unit} {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hs2 : sched.set_thread_state st s ct sched.TS_RESTART = ok s2)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (h1 : Steps (L := L) arI th s ar σ s2 ar σ1)
    (hR : StateRel th (L.mem s2) σ1) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl)
    (hcn : ∃ q, sl.1 = q.bv ∧ th q = some (.cnode sl.2.length))
    (hk : capV (L.mem s2) (cslotAddr sl) = .Null ∨
      ∃ p b w r, capV (L.mem s2) (cslotAddr sl) = .Notification p b w r)
    (hrun : cdt.delete_one st arI s2 ar (cslotAddr sl) = ok (s3, a3))
    (hm : ((), σ3) ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ1).1)
    (h2 : Steps (L := L) arI th s3 a3 σ3 s' a' σ') : IrqSteps (L := L) arI th s ar σ s' a' σ' := by
  rcases hk with hk | ⟨p, b, w, r, hk⟩
  · obtain ⟨c, ac, hc, hca, hg⟩ := hR.abs_cap hA
    rw [hca.abs] at hg
    have hcv := capV_of_capAt hc
    rw [hcv] at hk; subst hk
    have e1 : cdt.delete_one st arI s2 ar (cslotAddr sl) = ok (s2, ar) := by
      unfold cdt.delete_one
      rw [slot_cap_eq, hc]
      simp only [bind_ok, cap_is_null_eq, isNullB, ↓reduceIte]
    rw [e1] at hrun
    simp only [ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    have e2 : Fl4Spec.capDeleteOne (Z := Unit) sl σ1 = ({((), σ1)}, False) := by
      unfold Fl4Spec.capDeleteOne
      rw [nd_bind_one hg]
      simp [absCap, Fl4Spec.NonDet.unless, Fl4Spec.NonDet.pure]
    rw [e2] at hm
    have e3 := (Prod.mk.inj (Set.mem_singleton_iff.1 hm)).2
    subst e3
    exact Or.inl (h1.trans arI h2)
  · exact Or.inr ⟨ct, s2, σ1, sl, p, b, w, r, s3, a3, σ3, hct, hs2, hst, h1, hA, hcn, hk, hrun, hm, h2⟩

/-- **`Ack`.** -/
theorem irq_ack_refines (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hP : Placed th)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .irqAckIRQ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (irq : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    interrupt.decode_irq_handler st arI s ar fl4_abi.label.IRQAckIRQ irq extra ⦃ res =>
      HPost (L := L) arI th σ G (Fl4Spec.decodeIrqHandlerInvocation slbl (BitVec.ofNat 8 irq.val) cps) s ar res ⦄ := by
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  unfold interrupt.decode_irq_handler
  rw [hct]; simp only [bind_ok, ↓reduceIte]
  have hts := set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact
  obtain ⟨s2, hs2, hS⟩ := spec_exists hts
  rw [hs2]; simp only [bind_ok]
  obtain ⟨a', ha'⟩ := hmask ar irq false
  rw [ha']; simp only [bind_ok, WP.spec_ok]
  obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
  have hk' := hk
  rw [← hcur] at hk
  obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, hcd1, hio1⟩ := restart_rel hR hV hM hC hS hk .restart
  refine ⟨.aCKIrq (BitVec.ofNat 8 irq.val), ?_, σ1, hst, ?_⟩
  · unfold Fl4Spec.decodeIrqHandlerInvocation; rw [hlbl]; rfl
  · let ms' : Fl4Spec.MachineState := { σ1.machineState with
      irqMasks := Function.update σ1.machineState.irqMasks (BitVec.ofNat 8 irq.val) false }
    have hstp : CurRun σ → Steps (L := L) arI th s ar σ s2 a' { σ1 with machineState := ms' } := fun hC =>
      (Steps.restart arI hcur hk' htcb hs2 hst hC).trans arI
        ((Steps.ksSpec arI (σ := σ1) (σ' := { σ1 with machineState := ms' }) (by constructor <;> rfl) rfl rfl
          (fun h => ⟨h.st, h.node⟩) (fun h => h)).trans arI (Steps.arch arI (Or.inr (Or.inl ⟨irq, false, ha'⟩))))
    refine ⟨{ σ1 with machineState := ms' }, G, ?_, ?_⟩
    · show _ ∈ (Fl4Spec.doMachineOp _ σ1).1
      unfold Fl4Spec.doMachineOp Fl4Spec.maskInterrupt
      refine mem_bind_nd (x := (σ1.machineState, σ1)) rfl ?_
      refine mem_bind_nd (x := (((), ms'), σ1)) ⟨rfl, rfl⟩ ?_
      refine mem_bind_nd (x := ((), { σ1 with machineState := ms' })) (Set.mem_singleton _) ?_
      rfl
    · exact ⟨crel_same ⟨hR1, hV1, hM1, hC1, MdbInv.of_same hM hI hS⟩ (SlotsSame.refl _ _) rfl rfl rfl,
        hFI.of_same hM hS ((ksub_of_eq (setThreadState_nks _ _) hst).trans (KSub.of_kheap rfl)), MdbStep.of_same hM hS,
        fun _ hC => Or.inl (hstp hC)⟩

/-- **The IRQ node slot's deletion after the caller's restart** (what
`Clear` and `SetNotification` need of `delete_one`): from the restarted
state (FL4's `set_thread_state Restart`, the spec's), with `DState` there,
FL4's `delete_one` of the IRQ's node slot refines `cap_delete_one` with
`DState` after, the slot emptied and the other slots kept. From DelOne's
`delete_one_keep` (`irqDelOK_of`, with `FinObjHyp`/`PostDelHyp`/
`NtfnKeepHyp`), or at `J` from XTopJointDelR's `delete_oneJ`
(XTopJointIrqDel). -/
def IrqDelOK (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (ct irq : U64) : Prop :=
  ∀ s2 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s2 →
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    DState (L := L) th s2 σ1 G →
    cdt.delete_one st arI s2 ar (nodeA (L.ksb s) irq) ⦃ r =>
      (∃ σ' G', ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) ((nodeA (L.ksb s) irq).bv, []) σ1).1 ∧
        DState (L := L) th r.1 σ' G' ∧ MdbStep (L.mem s2) G (L.mem r.1) G') ∧
      capV (L.mem r.1) (nodeA (L.ksb s) irq) = .Null ∧
      ∀ y, IsSlot th y → y ≠ nodeA (L.ksb s) irq → capV (L.mem r.1) y = capV (L.mem s2) y ⦄

/-- `IrqDelOK` from DelOne's `delete_one_keep` (the deletion's ∀-state
premises `FinObjHyp`, `PostDelHyp`, `NtfnKeepHyp`). -/
theorem irqDelOK_of (th : TypedHeap) (hP : Placed th)
    (hO : FinObjHyp (L := L) arI th) (hPD : PostDelHyp (L := L) arI th) (hK : NtfnKeepHyp (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hL : IntLayout th (L.ksb s))
    (ct : U64) (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (irq : U64) (hirq : irq.val < 128) (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq)) :
    IrqDelOK (L := L) arI th s ar σ G ct irq := by
  intro s2 σ1 hs2 _ hDS1
  have hS : SlotsSame th (L.mem s) (L.mem s2) := by
    have h := set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact
    rw [hs2, WP.spec_ok] at h; exact h
  have hA : AbsSlot th ((nodeA (L.ksb s) irq).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node irq hirq)⟩
  have hns : IsSlot th (nodeA (L.ksb s) irq) := by have := hA.isSlot; rwa [cslotAddr_nil] at this
  have hok3 : capV (L.mem s2) (cslotAddr ((nodeA (L.ksb s) irq).bv, [])) = .Null ∨
      ∃ p b w r, capV (L.mem s2) (cslotAddr ((nodeA (L.ksb s) irq).bv, [])) = .Notification p b w r := by
    rw [cslotAddr_nil, hS.capV hns]; exact hok
  have h := delete_one_keep arI th hP (finalHyp_full th hP) hO hPD hK s2 ar σ1 G hDS1 hA hok3
  rw [cslotAddr_nil] at h; exact h

/-- **`Clear`.** -/
theorem irq_clear_refinesD (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .irqClearIRQHandler)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (irq : U64) (hirq : irq.val < 128) (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (hDel : IrqDelOK (L := L) arI th s ar σ G ct irq)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    interrupt.decode_irq_handler st arI s ar fl4_abi.label.IRQClearIRQHandler irq extra ⦃ res =>
      HPost (L := L) arI th σ G (Fl4Spec.decodeIrqHandlerInvocation slbl (BitVec.ofNat 8 irq.val) cps) s ar res ⦄ := by
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ := hDS
  unfold interrupt.decode_irq_handler
  have n1 : ¬ fl4_abi.label.IRQClearIRQHandler = fl4_abi.label.IRQAckIRQ := by rw [u64_eq_iff]; simp
  have n2 : ¬ fl4_abi.label.IRQClearIRQHandler = fl4_abi.label.IRQSetIRQHandler := by rw [u64_eq_iff]; simp
  rw [hct]; simp only [bind_ok, n1, n2, ↓reduceIte]
  have hts := WP.spec_and (set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact)
    (set_thread_state_ksb s ct sched.TS_RESTART)
  obtain ⟨s2, hs2, hS, hkb⟩ := spec_exists hts
  rw [hs2]; simp only [bind_ok, irq_slot_eq, hkb]
  obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
  have hk' := hk
  rw [← hcur] at hk
  obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, hcd1, hio1⟩ := restart_rel hR hV hM hC hS hk .restart
  have hkeep := setThreadState_keeps hk hst
  have hA : AbsSlot th ((nodeA (L.ksb s) irq).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node irq hirq)⟩
  have hns : IsSlot th (nodeA (L.ksb s) irq) := by have := hA.isSlot; rwa [cslotAddr_nil] at this
  have hok2 : IrqSlotOK (L.mem s2) (nodeA (L.ksb s) irq) := by
    unfold IrqSlotOK; rw [hS.capV hns]; exact hok
  have hDS1 : DState (L := L) th s2 σ1 G := ⟨⟨hR1, hV1, hM1, hC1, MdbInv.of_same hM hI hS⟩, hD.of_same hS,
    hFI.of_same hM hS (ksub_of_eq (setThreadState_nks _ _) hst)⟩
  have hok3 : capV (L.mem s2) (cslotAddr ((nodeA (L.ksb s) irq).bv, [])) = .Null ∨
      ∃ p b w r, capV (L.mem s2) (cslotAddr ((nodeA (L.ksb s) irq).bv, [])) = .Notification p b w r := by
    have h := hok2; unfold IrqSlotOK at h; simpa only [cslotAddr_nil] using h
  have := hDel s2 σ1 hs2 hst hDS1
  have hrun := spec_self this
  refine WP.spec_bind (WP.spec_and this hrun) ?_
  rintro ⟨s3, a3⟩ ⟨⟨⟨σ', G', hdel, hDS3, hmS3⟩, -, -⟩, hr3⟩
  apply (WP.spec_ok (core.result.Result.Ok (), s3, a3)).mpr
  have hdel' : ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) ((nodeA (L.ksb s) irq).bv, []) σ1).1 := hdel
  refine ⟨.clearIRQHandler (BitVec.ofNat 8 irq.val), ?_, σ1, hst, σ', G', ?_, hDS3.1, hDS3.2.2,
    MdbStep.same_left hM hS hmS3, fun _ hC => IrqSteps.of_del arI hct hs2 hst
      (Steps.restart arI hcur hk' htcb hs2 hst hC) hR1 hA ⟨_, rfl, by simpa using hL.node irq hirq⟩ hok3
      (by rw [cslotAddr_nil]; exact hr3) hdel' (Steps.arch arI (Or.inl rfl))⟩
  · unfold Fl4Spec.decodeIrqHandlerInvocation; rw [hlbl]; rfl
  · show _ ∈ ((Fl4Spec.getIrqSlot _ >>= fun sl => Fl4Spec.capDeleteOne sl) σ1).1
    refine mem_bind_nd (x := ((σ1.interruptIrqNode (BitVec.ofNat 8 irq.val), []), σ1)) rfl ?_
    rw [hkeep.1, hIR.node irq hirq]
    exact hdel

/-- **`SetNotification`.** -/
theorem irq_set_refinesD (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .irqSetIRQHandler)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (irq : U64) (hirq : irq.val < 128) (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (hDel : IrqDelOK (L := L) arI th s ar σ G ct irq)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hxn : x0 ≠ nodeA (L.ksb s) irq) (hFR : MdbOKV (L.ksb s) (L.mem s) G) :
    interrupt.decode_irq_handler st arI s ar fl4_abi.label.IRQSetIRQHandler irq extra ⦃ res =>
      HPost (L := L) arI th σ G (Fl4Spec.decodeIrqHandlerInvocation slbl (BitVec.ofNat 8 irq.val) cps) s ar res ⦄ := by
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ := hDS
  have hdec : Fl4Spec.decodeIrqHandlerInvocation (Z := Unit) slbl (BitVec.ofNat 8 irq.val) cps =
      (if cps ≠ [] then
        (let (cap, slot) := Fl4Spec.the cps.head?
         if Fl4Spec.isNtfnCap cap ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights cap
         then Fl4Spec.NonDetE.returnOk (.setIRQHandler (BitVec.ofNat 8 irq.val) cap slot)
         else Fl4Spec.NonDetE.throwError (.invalidCapability 0))
       else Fl4Spec.NonDetE.throwError .truncatedMessage) := by
    unfold Fl4Spec.decodeIrqHandlerInvocation; rw [hlbl]; rfl
  unfold interrupt.decode_irq_handler
  have n1 : ¬ fl4_abi.label.IRQSetIRQHandler = fl4_abi.label.IRQAckIRQ := by rw [u64_eq_iff]; simp
  rw [hct]; simp only [bind_ok, n1, ↓reduceIte, hx0, is_null_eq]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, ps, rs, idxs, rest, hps, hls, hxe, rfl⟩
  · simp only [decide_true, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
    refine ⟨rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, rfl⟩
    rw [hdec]; simp only [ne_eq, not_true_eq_false, ↓reduceIte]; rfl
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, capAt_capV, bind_ok]
  have hdec2 : Fl4Spec.decodeIrqHandlerInvocation (Z := Unit) slbl (BitVec.ofNat 8 irq.val)
      ((absCap (capV (L.mem s) x0), (ps.bv, idxs)) :: rest) =
      if Fl4Spec.isNtfnCap (absCap (capV (L.mem s) x0)) ∧
          Fl4Spec.AllowSend ∈ Fl4Spec.capRights (absCap (capV (L.mem s) x0))
      then Fl4Spec.NonDetE.returnOk (.setIRQHandler (BitVec.ofNat 8 irq.val) (absCap (capV (L.mem s) x0)) (ps.bv, idxs))
      else Fl4Spec.NonDetE.throwError (.invalidCapability 0) := by
    rw [hdec, if_pos (List.cons_ne_nil _ _)]; rfl
  -- the cap must be a notification cap with send rights
  generalize hcx : capV (L.mem s) x0 = c at hdec2 ⊢
  by_cases hgood : ∃ p b r, c = .Notification p b true r
  · obtain ⟨p, b, r, rfl⟩ := hgood
    have h12 : Fl4Spec.isNtfnCap (absCap (.Notification p b true r)) = true ∧
        Fl4Spec.AllowSend ∈ Fl4Spec.capRights (absCap (.Notification p b true r)) :=
      ⟨rfl, show (true = true) from rfl⟩
    rw [if_pos h12] at hdec2
    simp only [↓reduceIte]
    -- `set_thread_state`
    have hts := WP.spec_and (set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact)
      (set_thread_state_ksb s ct sched.TS_RESTART)
    obtain ⟨s2, hs2, hS, hkb⟩ := spec_exists hts
    rw [hs2]; simp only [bind_ok, irq_slot_eq, hkb]
    obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
    have hk' := hk
    rw [← hcur] at hk
    obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, hcd1, hio1⟩ := restart_rel hR hV hM hC hS hk .restart
    have hkeep := setThreadState_keeps hk hst
    have hA : AbsSlot th ((nodeA (L.ksb s) irq).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node irq hirq)⟩
    have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
    have hns : IsSlot th (nodeA (L.ksb s) irq) := by have := hA.isSlot; rwa [cslotAddr_nil] at this
    have hok2 : IrqSlotOK (L.mem s2) (nodeA (L.ksb s) irq) := by
      unfold IrqSlotOK; rw [hS.capV hns]; exact hok
    have hDS1 : DState (L := L) th s2 σ1 G := ⟨⟨hR1, hV1, hM1, hC1, MdbInv.of_same hM hI hS⟩, hD.of_same hS,
    hFI.of_same hM hS (ksub_of_eq (setThreadState_nks _ _) hst)⟩
    have hok3 : capV (L.mem s2) (cslotAddr ((nodeA (L.ksb s) irq).bv, [])) = .Null ∨
        ∃ p b w r, capV (L.mem s2) (cslotAddr ((nodeA (L.ksb s) irq).bv, [])) = .Notification p b w r := by
      have h := hok2; unfold IrqSlotOK at h; simpa only [cslotAddr_nil] using h
    have := hDel s2 σ1 hs2 hst hDS1
    have hrun := spec_self this
    refine WP.spec_bind (WP.spec_and this hrun) ?_
    rintro ⟨s3, a3⟩ ⟨⟨⟨σ2, G2, hdel, ⟨⟨hR3, hV3, hM3, hC3, hI3⟩, hD3, hFI3⟩, hmS3⟩, hnull, hoth⟩, hr3⟩
    simp only [uncurry_apply_pair]
    -- the insertion
    have hxs : IsSlot th x0 := by rw [hxe]; exact hAs.isSlot
    have hsrc3 : capAt (L.mem s3) (cslotAddr (ps.bv, idxs)) = ok (.Notification p b true r) := by
      rw [capAt_capV, ← hxe, hoth x0 hxs hxn, hS.capV hxs, hcx]
    have hdst3 : capAt (L.mem s3) (cslotAddr ((nodeA (L.ksb s) irq).bv, [])) = ok .Null := by
      rw [capAt_capV, cslotAddr_nil, hnull]
    have he : EncWf (capability.Cap.Notification p b true r) := by
      have := capAt_capV (L.mem s) x0
      rw [hcx, capAt_words] at this; exact decode_encWf this
    have hins := insert_full_fin th s3 σ2 G2 hR3 hV3 hP hM3 hC3 hI3 hFI3 hps (hL.node irq hirq) hls (rd := 0)
      (idxd := []) rfl hsrc3 (by simp) hdst3 (.Notification p b true r) _ ⟨trivial, rfl⟩ (hV3.abs hAs hsrc3) he (by simp) rfl
      (Or.inl rfl) (by simp [isUt]) (by simp [isZb]) rfl (fun _ _ _ _ _ _ => trivial)
    rw [cslotAddr_nil, ← hxe] at hins
    have hsrcx : capAt (L.mem s3) x0 = ok (.Notification p b true r) := by rw [hxe]; exact hsrc3
    have hsrcm : x0 ∈ G2.chains.flatten := (hM3.members _).2 ⟨hxs, _, hsrcx, by simp⟩
    have hdestm : nodeA (L.ksb s) irq ∉ G2.chains.flatten := by
      intro h; obtain ⟨-, c0, h0, hn⟩ := (hM3.members _).1 h
      rw [capAt_capV, hnull] at h0
      exact hn (eq_of_ok_eq h0).symm
    have hnx : nextOf (L.mem s3) x0 = 0#u64 ∨ IsSlot th (nextOf (L.mem s3) x0) := by
      rcases hM3.next_mem hsrcm with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ((hM3.members _).1 h).1
    refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and hins (insert_caps_nofull hP s3 G2 hM3 hsrcm hns hdestm hsrcx
      (.Notification p b true r) he rfl)) (Vs.insert_frame2 hP s3 (.Notification p b true r) x0 _ hxs hns _ hsrcx hnx))
      (insert_delinv hP s3 G2 hM3 hD3 hsrcm hns hdestm hsrcx (.Notification p b true r) he rfl (by simp) rfl)) ?_
    rintro s4 ⟨⟨⟨⟨σ', G', hci, hR', hV', hM', hC', hI', hFI', hSti⟩, hcap4⟩, hF4⟩, hD4⟩
    rw [WP.spec_ok]
    have hmst : MdbStep (L.mem s) G (L.mem s4) G' :=
      (MdbStep.same_left hM hS hmS3).trans (hSti (fun h => absurd h (by simp [isUt])))
    refine ⟨.setIRQHandler (BitVec.ofNat 8 irq.val) (absCap (.Notification p b true r)) (ps.bv, idxs),
      by rw [hdec2]; rfl, σ1, hst, σ', G', ?_, ⟨hR', hV', hM', hC', hI'⟩, hFI', hmst, fun hks hC => ?_⟩
    swap
    · have hk3 : L.ksb s3 = L.ksb s := hF4.1.symm.trans hks
      refine IrqSteps.of_del arI hct hs2 hst (Steps.restart arI hcur hk' htcb hs2 hst hC) hR1 hA
        ⟨_, rfl, by simpa using hL.node irq hirq⟩ hok3 (by rw [cslotAddr_nil]; exact hr3) hdel
        (Steps.insert arI hP hps (hL.node irq hirq) (idxd := []) rfl hci hF4 ⟨hR', hV', hM', hC', hI'⟩ hFI'
          (by rw [hk3]; exact hmst.okv hFR) (fun y hy hne => ?_) hdst3
          (fun p sb fi d h => ?_)
          (typedKept_set hcap4 (Or.inr ⟨x0, hxs, by rw [capV_of_capAt hsrcx]⟩))
          (Or.inr fun k hk => by
            rw [hL.node irq hirq] at hk; cases hk
            rw [hk3, nodeA_val hL.fit hirq]; simp only [objSize]; omega) (fun _ => hD4)
          (fun _ _ _ _ _ _ => by rw [cslotAddr_nil, hcap4 _ hns, if_pos rfl]; trivial)
          (fun _ _ => by rw [cslotAddr_nil, hcap4 _ hns, if_pos rfl]; trivial)
          (fun _ => by rw [cslotAddr_nil, hcap4 _ hns, if_pos rfl]; trivial)
          (by rw [cslotAddr_nil, hcap4 _ hns, if_pos rfl]; exact fun h => by cases h)
          (fun _ _ _ h => by rw [cslotAddr_nil, hcap4 _ hns, if_pos rfl] at h; cases h))
      · rw [hcap4 y hy, if_neg (by rwa [cslotAddr_nil] at hne)]
      · rw [cslotAddr_nil, hcap4 _ hns, if_pos rfl] at h; cases h
    show _ ∈ ((Fl4Spec.getIrqSlot _ >>= fun irqSlot => Fl4Spec.capDeleteOne irqSlot >>= fun _ =>
      Fl4Spec.capInsert _ _ irqSlot) σ1).1
    refine mem_bind_nd (x := ((σ1.interruptIrqNode (BitVec.ofNat 8 irq.val), []), σ1)) rfl ?_
    rw [hkeep.1, hIR.node irq hirq]
    refine mem_bind_nd (x := ((), σ2)) hdel ?_
    rw [hci]; rfl
  · have hbad : ¬ (Fl4Spec.isNtfnCap (absCap c) = true ∧ Fl4Spec.AllowSend ∈ Fl4Spec.capRights (absCap c)) := by
      rintro ⟨h1, h2⟩
      apply hgood
      cases c <;> simp [absCap, Fl4Spec.isNtfnCap] at h1
      rename_i p b w r
      refine ⟨p, b, r, ?_⟩
      have : w = true := h2
      rw [this]
    rw [if_neg hbad] at hdec2
    have hfin : ∀ e : core.result.Result Unit error.Exc, e = .Err (.Sys (.InvalidCapability 0#u64)) →
        HPost (L := L) arI th σ G (Fl4Spec.decodeIrqHandlerInvocation slbl (BitVec.ofNat 8 irq.val)
          ((absCap c, (ps.bv, idxs)) :: rest)) s ar (e, s, ar) := by
      rintro e rfl
      exact ⟨rfl, ⟨_, by rw [hdec2]; rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, rfl⟩
    cases c <;> simp only [error.invalid_cap, bind_ok, WP.spec_ok] <;>
      first
      | exact hfin _ rfl
      | (rename_i p b w r
         cases w
         · simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
           exact hfin _ rfl
         · exact absurd ⟨p, b, r, rfl⟩ hgood)

/-- **`Clear`** (with DelOne's ∀-state deletion premises, `irqDelOK_of`). -/
theorem irq_clear_refines (th : TypedHeap) (hP : Placed th)
    (hO : FinObjHyp (L := L) arI th) (hPD : PostDelHyp (L := L) arI th) (hK : NtfnKeepHyp (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .irqClearIRQHandler)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (irq : U64) (hirq : irq.val < 128) (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    interrupt.decode_irq_handler st arI s ar fl4_abi.label.IRQClearIRQHandler irq extra ⦃ res =>
      HPost (L := L) arI th σ G (Fl4Spec.decodeIrqHandlerInvocation slbl (BitVec.ofNat 8 irq.val) cps) s ar res ⦄ :=
  irq_clear_refinesD arI th hP s ar σ G hDS hL hIR slbl hlbl ct hct hcur htcb hact irq hirq hok
    (irqDelOK_of arI th hP hO hPD hK s ar σ G hL ct htcb hact irq hirq hok) extra cps

/-- **`SetNotification`** (with DelOne's ∀-state deletion premises, `irqDelOK_of`). -/
theorem irq_set_refines (th : TypedHeap) (hP : Placed th)
    (hO : FinObjHyp (L := L) arI th) (hPD : PostDelHyp (L := L) arI th) (hK : NtfnKeepHyp (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .irqSetIRQHandler)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (irq : U64) (hirq : irq.val < 128) (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 cps)
    (hxn : x0 ≠ nodeA (L.ksb s) irq) (hFR : MdbOKV (L.ksb s) (L.mem s) G) :
    interrupt.decode_irq_handler st arI s ar fl4_abi.label.IRQSetIRQHandler irq extra ⦃ res =>
      HPost (L := L) arI th σ G (Fl4Spec.decodeIrqHandlerInvocation slbl (BitVec.ofNat 8 irq.val) cps) s ar res ⦄ :=
  irq_set_refinesD arI th hP s ar σ G hDS hL hIR slbl hlbl ct hct hcur htcb hact irq hirq hok
    (irqDelOK_of arI th hP hO hPD hK s ar σ G hL ct htcb hact irq hirq hok) extra x0 hx0 cps hex hxn hFR

/-- **Any other label**: `IllegalOperation`. -/
theorem irq_other_refines (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit) {G : MdbGhost}
    (lbl : U64) (h1 : lbl.val ≠ 34) (h2 : lbl.val ≠ 35) (h3 : lbl.val ≠ 36)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl ≠ .irqAckIRQ ∧
      Fl4Spec.genInvocationType slbl ≠ .irqSetIRQHandler ∧ Fl4Spec.genInvocationType slbl ≠ .irqClearIRQHandler)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (irq : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    interrupt.decode_irq_handler st arI s ar lbl irq extra ⦃ res =>
      HPost (L := L) arI th σ G (Fl4Spec.decodeIrqHandlerInvocation slbl (BitVec.ofNat 8 irq.val) cps) s ar res ⦄ := by
  unfold interrupt.decode_irq_handler
  have n1 : ¬ lbl = fl4_abi.label.IRQAckIRQ := by rw [u64_eq_iff]; simpa using h1
  have n2 : ¬ lbl = fl4_abi.label.IRQSetIRQHandler := by rw [u64_eq_iff]; simpa using h2
  have n3 : ¬ lbl = fl4_abi.label.IRQClearIRQHandler := by rw [u64_eq_iff]; simpa using h3
  rw [hct]; simp only [bind_ok, n1, n2, n3, ↓reduceIte, error.illegal, WP.spec_ok]
  refine ⟨rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, rfl⟩
  unfold Fl4Spec.decodeIrqHandlerInvocation
  rw [if_neg hlbl.1, if_neg hlbl.2.1, if_neg hlbl.2.2]; rfl

end

end

end Fl4Proofs.P3
