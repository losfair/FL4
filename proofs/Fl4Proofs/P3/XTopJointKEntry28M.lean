/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN fin1): **`kernel_entryJ28M`:
`kernel_entryJ27M` with the two PerfW premises [W] replaced by the two [J]
facts.** sch29's `KDispHyps27M` asked `MidRun.JMidPerfHypQ` [W] and
`MidRun.JMidPerfHypB` [W] at the mid state; sch28's `jMidPerfHypQ_of2` /
`jMidPerfHypB_of2` (XTopJointPerfI) give both from `MidRun.JPerfRegHyp` [J]
(XTopJointPerfW: the Untyped / ASID control region avoids ct and every bound
SC; l4v `valid_untyped_inv` / `valid_aci`) and `MidRun.JPerfIrqSlotHyp` [J]
(XTopJointPerfI: the IRQ node slots hold null or notification caps; l4v
`valid_irq_node` + the IRQ handler slots), with `CQ ∧ NQ` at the dispatch
state from `JAtZ.midCQ` and `BudgetAt.enteredP` (as sch28 did for J25MP).

* `KDispHyps28M` (mid: entry facts, `JPerfRegHyp ∧ JPerfIrqSlotHyp` [J],
  `JMidVfhHyp` [J]; no [W]); `.to27M`; NEW TOP `kernel_entryJ28M`.

The budget premise `hB` is the M line's `KBudget` (inherited from
`kernel_entryJ9M`): its `tmo` field is the one budtr found FALSE in reachable
states (mr8 finding). The P line (`kernel_entryJ26P`, XTopJointKEntry26P)
carries budtr's `KBudgetB` instead; it is the final top. Re-proving the M
line's entry on `KBudgetB` would copy kernel_entryJ9M's body (as mr9 did for
J13PB), which this wrapper does not.
-/
import Fl4Proofs.P3.XTopJointKEntry27MD
import Fl4Proofs.P3.XTopJointPerfK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The dispatch premises with no [W] at the mid state** (module
docstring): `KDispHyps27M` with `JMidPerfHypQ ∧ JMidPerfHypB` [W] replaced by
`JPerfRegHyp ∧ JPerfIrqSlotHyp` [J]. -/
structure KDispHyps28M (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlob (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlob (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    (MidRun.JPerfRegHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
      MidRun.JPerfIrqSlotHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ) ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ

variable {arI}

/-- **`KDispHyps27M` from `KDispHyps28M`** at an `Entered` dispatch state
(`JAtZ.midCQ`, then `jMidPerfHypQ_of2` / `jMidPerfHypB_of2`). -/
theorem KDispHyps28M.to27M {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (h : KDispHyps28M (L := L) arI AR Z H Cs D s a σ n c) : KDispHyps27M (L := L) arI AR Z H Cs D s a σ n c where
  inv := h.inv
  recv := h.recv
  mid := fun ct rg sr cr hct hm => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.mid ct rg sr cr hct hm
    obtain ⟨hs, hq⟩ := J.midCQ hni h2
    exact ⟨h1, h2, h3, MidRun.jMidPerfHypQ_of2 hs hq h4.1 h4.2, MidRun.jMidPerfHypB_of2 hs hq h4.1 h4.2, h5⟩

set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ27M`
with `KDispHyps28M` (mid: entry facts, `JPerfRegHyp` [J], `JPerfIrqSlotHyp`
[J], `JMidVfhHyp` [J]; no [W]) for `KDispHyps27M` (module docstring). -/
theorem kernel_entryJ28M [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps28M (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ27M s a σ J hni n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' =>
      (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to27M J' (hBA.enteredP hnd hni))
    hFin hARI hA hnd hPP hmrt hmb hIP hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
