/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN fin1): **`kernel_entryJ26P`, the
final top: the MachPlat line (`kernel_entryJ25P`, KBudgetB, JPathAtM) with no
[W] premise on the mid path.** `KDispHypsKV25`'s mid bundle asked
`MidRun.JMidPerfHypQ` [W] and sch23b's receive leaves `JMidLeavesHyp14` [W].
Both are now derived at each dispatch state σb (an `Entered` state by
`BudgetAt.enteredP`) from the joint invariant and two [J] facts:

* `JMidPerfHypQ`, `JMidPerfHypB` by sch28's `jMidPerfHypQ_of2` /
  `jMidPerfHypB_of2` from `MidRun.JPerfRegHyp` [J] (l4v `valid_untyped_inv` /
  `valid_aci`) and `MidRun.JPerfIrqSlotHyp` [J] (l4v `valid_irq_node`), with
  `CQ ∧ NQ` from `JAtZ.midCQ`;
* the first-phase fact `CtOK` by sch23's `jMidChooseFact` (`CQ`, `NQ`,
  `CurInv` from `JAtZ.cur`, `Sched.Inv` from `JAtZ.inv`, the two PerfW facts),
  then `JMidLeavesHyp17` by sch29's `jMidLeavesHyp17_of` (every receive leaf
  proved), and down the existing conversions `jMidLeavesHyp_of17` / `_of16` /
  `_of15` to `JMidLeavesHyp14`.

* `KDispHypsKV26` (mid: `JEntryGlobM`, `JEntryAt`, `JPathAtM`, `JPerfRegHyp ∧
  JPerfIrqSlotHyp` [J], `JMidVfhHyp` [J], `JVtxHypMU` [S]); `.to25`.
* NEW TOP `kernel_entryJ26P` (wrapper over J25P); `j26P_platform`
  (non-vacuity of the platform premises: `j25P_platform`).
-/
import Fl4Proofs.P3.XTopJointKEntry25P
import Fl4Proofs.P3.XTopJointKEntry27MD
import Fl4Proofs.P3.XTopJointPerfK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KDispHypsKV25` with no [W] at the mid state** (module docstring). -/
structure KDispHypsKV26 (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    (MidRun.JPerfRegHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
      MidRun.JPerfIrqSlotHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ) ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct

variable {arI} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`KDispHypsKV25` from `KDispHypsKV26`** at an `Entered` dispatch state
(module docstring). -/
theorem KDispHypsKV26.to25 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (h : KDispHypsKV26 (L := L) arI AR MR Z H Cs D s a σ n c) :
    KDispHypsKV25 (L := L) arI AR MR Z H Cs D s a σ n c where
  inv := h.inv
  recv := h.recv
  mid := fun ct rg sr cr hct hm => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.mid ct rg sr cr hct hm
    obtain ⟨hs, hq⟩ := J.midCQ hni h2
    have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
    have hQ := MidRun.jMidPerfHypQ_of2 (don := true) hs hq h4.1 h4.2
    have hB := MidRun.jMidPerfHypB_of2 (don := true) hs hq h4.1 h4.2
    have hF := MidRun.jMidChooseFact true true _ σ hs hq hC J.inv hQ hB
    exact ⟨h1, h2, h3, hQ, h5, jMidLeavesHyp_of15 hAT hmax htu (jMidLeavesHyp_of16 hAT hmb
      (jMidLeavesHyp_of17 hAT hmax htu hmb hF (jMidLeavesHyp17_of hAT hmax htu hmb hF))), h6⟩

set_option maxHeartbeats 4000000 in
/-- **The final top: the P line with no [W] on the mid path** (module
docstring): `kernel_entryJ25P` with `KDispHypsKV26` (mid: `JPerfRegHyp` [J],
`JPerfIrqSlotHyp` [J], `JMidVfhHyp` [J], `JVtxHypMU` [S]; no receive-leaf or
PerfW premise). -/
theorem kernel_entryJ26P [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsKV26 (L := L) arI AR MR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ25P s a σ J hni hR hVI n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' =>
      (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to25 hA hmax htu hmb J' (hBA.enteredP hnd hni))
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hNS hNSR hT hmax htu

/-- **The platform premises of `kernel_entryJ26P` are satisfiable** (the same
as J25P's: `j25P_platform`). -/
theorem j26P_platform :
    MachPlat modelArch modelMR ∧ MRKeepD modelArch modelMR ∧
      ∀ (ms : Fl4Spec.MachineState) (i : Fl4Spec.Irq), gaiLine true ms = some i →
        modelArch.take_pending_irq ms ⦃ r => r.1 ≠ syscall.NO_IRQ ∧ r.1.val = i.toNat ⦄ :=
  j25P_platform

end

end

end Fl4Proofs.P3
