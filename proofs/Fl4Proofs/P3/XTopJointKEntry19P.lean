/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr7): **`kernel_entryJ19P`**,
XTopJointKEntry18P's `kernel_entryJ18P` on the newest receive premise: the mid
receive leaves asked as sch21's `JMidLeavesHyp12` [W] (XTopJointKEntry21M)
instead of sch18's `JMidLeavesHyp7`, converted per dispatch state by
`jMidLeavesHyp_of12` … `jMidLeavesHyp_of8` (as mr5's J16P did for
`JMidLeavesHyp7`). So the P line carries the narrowest receive premise
(`kernel_entryJ21M`'s), no `PPPlat`/`IrqPlat`, and `JPreDecHypK` only for VT-x
Untyped retypes.

* `KDispHypsKV12 K`: `KDispHypsKV7 K` with `JMidLeavesHyp12`; `.to7`.
* `kernel_entryJ19P`; `j19P_platform` (non-vacuity of the platform premises:
  `MachPlat`, `MRKeepD`, interrupts raised; as `j13P_platform`).
-/
import Fl4Proofs.P3.XTopJointKEntry18P
import Fl4Proofs.P3.XTopJointKEntry21M
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KDispHypsKV7` with sch21's mid receive leaves** (module docstring). -/
structure KDispHypsKV12 (K : capability.Cap → List U64 → Prop) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JPreDecHypK (L := L) arI K AR MR Z H Cs D s a σ ct
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidLeavesHyp12 (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JPreDecHypK (L := L) arI K AR MR Z H Cs D s a σ ct

variable {arI} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`KDispHypsKV7` from `KDispHypsKV12`** (sch21 … sch19's conversions). -/
theorem KDispHypsKV12.to7 {K : capability.Cap → List U64 → Prop} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKV12 (L := L) arI K AR MR Z H Cs D s a σ n c) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    KDispHypsKV7 (L := L) arI K AR MR Z H Cs D s a σ n c where
  inv := h.inv
  recv := h.recv
  mid := fun ct rg sr cr hct hm => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h.mid ct rg sr cr hct hm
    exact ⟨h1, h2, h3, h4, h5, jMidLeavesHyp_of8 hAT (jMidLeavesHyp_of9 hAT (jMidLeavesHyp_of10 hAT
      (jMidLeavesHyp_of11 hAT hmax htu (jMidLeavesHyp_of12 hAT h6)))), h7⟩

set_option maxHeartbeats 4000000 in
/-- **The P line on the newest receive premise** (module docstring):
`kernel_entryJ18P` with `KDispHypsKV12 PreKind18` (mid receive leaves asked as
sch21's `JMidLeavesHyp12`). -/
theorem kernel_entryJ19P [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsKV12 (L := L) arI PreKind18 AR MR Z' H' Cs' D' s' a' σb n c)
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
  kernel_entryJ18P s a σ J hni hR hVI n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' => (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to7 hA hmax htu)
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hNS hNSR hT hmax htu


/-- **The platform premises of `kernel_entryJ19P` are satisfiable** by a
platform that raises interrupts (`j13P_platform` with `modelArch_mrKeepD`). -/
theorem j19P_platform :
    MachPlat modelArch modelMR ∧ MRKeepD modelArch modelMR ∧
      ∀ (ms : Fl4Spec.MachineState) (i : Fl4Spec.Irq), gaiLine true ms = some i →
        modelArch.take_pending_irq ms ⦃ r => r.1 ≠ syscall.NO_IRQ ∧ r.1.val = i.toNat ⦄ :=
  ⟨j13P_platform.1, modelArch_mrKeepD _, j13P_platform.2.2⟩

end

end

end Fl4Proofs.P3
