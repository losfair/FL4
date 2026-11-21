/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch28): **`kernel_entryJ25MP`:
`kernel_entryJ25M` with `JMidPerfHypQ` [W] replaced by the two [J] facts**
`MidRun.JPerfRegHyp` (XTopJointPerfW: the Untyped / ASID control region
avoids ct and every bound SC) and `MidRun.JPerfIrqSlotHyp` (XTopJointPerfI:
the IRQ node slots hold null or notification caps), both at the `MidPerfAt`
states only.

* `BudgetAt.enteredP`: the dispatch state `σb` of the entry is `Entered` when
  the entry state is (the `FaultIP` write changes only ct's TCB, the time
  stamp only the machine state and the clock, and a `check_budget_restart`
  answering `true` nothing: ScEntryRd's `checkBudgetRestart_true`). This is
  sch26's missing export (KEntry.lean derived it inline from the J-side
  budget post).
* `KDispHyps25MP`: `KDispHyps25M` with `mid`'s `JMidPerfHypQ` [W] replaced
  by `JPerfRegHyp ∧ JPerfIrqSlotHyp` [J]; `.to25M` (from `JAtZ` and
  `Entered` at the dispatch state: `JAtZ.midCQ` gives `CQ ∧ NQ`, then
  `MidRun.jMidPerfHypQ_of2`).
* NEW TOP `kernel_entryJ25MP`.
-/
import Fl4Proofs.P3.XTopJointKEntry25MD
import Fl4Proofs.P3.XTopJointPerfI
import Fl4Proofs.P3.XTopJointMachRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The entry's dispatch state is `Entered`** (module docstring). -/
theorem BudgetAt.enteredP (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hni : Entered σ)
    (h : BudgetAt σ σb true) : Entered σb := by
  obtain ⟨σ0, h0, hb⟩ := h
  have e0 : σ0.curThread = σ.curThread ∧ σ0.idleThread = σ.idleThread ∧
      σ0.schedulerAction = σ.schedulerAction := by
    cases hk : σ.kheap σ.curThread with
    | none =>
      exfalso
      unfold Fl4Spec.fl4SyscallFaultIP Fl4Spec.asUser at h0
      obtain ⟨y, hy, -⟩ := h0
      have := MidRun.getTcb_some (MidRun.mem_getsThe' hy).1
      rw [hk] at this; cases this
    | some o =>
      cases o with
      | tcb x =>
        rw [fl4SyscallFaultIP_eq hk] at h0
        obtain rfl := congrArg Prod.snd (Set.mem_singleton_iff.1 h0)
        exact ⟨rfl, rfl, rfl⟩
      | _ =>
        exfalso
        unfold Fl4Spec.fl4SyscallFaultIP Fl4Spec.asUser at h0
        obtain ⟨y, hy, -⟩ := h0
        have := MidRun.getTcb_some (MidRun.mem_getsThe' hy).1
        rw [hk] at this; cases this
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ0.machineState))
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hb
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hb' : σb = σu := Sched.checkBudgetRestart_true h2 rfl
  rw [hb', e]
  show σ0.curThread ≠ σ0.idleThread ∧ σ0.schedulerAction = .resumeCurThread
  rw [e0.1, e0.2.1, e0.2.2]
  exact hni

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The dispatch premises with the PerfW facts as [J] region / IRQ slot
facts** (module docstring). -/
structure KDispHyps25MP (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
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
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidLeavesHyp16 (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ

variable {arI}

theorem KDispHyps25MP.to25M {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (h : KDispHyps25MP (L := L) arI AR Z H Cs D s a σ n c) : KDispHyps25M (L := L) arI AR Z H Cs D s a σ n c where
  inv := h.inv
  recv := h.recv
  mid := fun ct rg sr cr hct hm => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.mid ct rg sr cr hct hm
    obtain ⟨hs, hq⟩ := J.midCQ hni h2
    exact ⟨h1, h2, h3, MidRun.jMidPerfHypQ_of2 hs hq h4.1 h4.2, h5, h6⟩

set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ25M`
with `KDispHyps25MP` (mid: entry facts, `JPerfRegHyp` [J], `JPerfIrqSlotHyp`
[J], `JMidVfhHyp` [J], `JMidLeavesHyp16` [W]) for `KDispHyps25M` (module
docstring). -/
theorem kernel_entryJ25MP [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps25MP (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
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
  kernel_entryJ25M s a σ J hni n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' =>
      (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to25M J' (hBA.enteredP hnd hni))
    hFin hARI hA hnd hPP hmrt hmb hIP hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
