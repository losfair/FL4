/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch29): **`kernel_entryJ27M`:
the mid premise on the receive leaves is gone.** `JMidLeavesHyp17` [W]
(XTopJointKEntry26MD) asked the endpoint receive at a `chooseNewThread`
mid state with `¬ CurInv` only at the reply-push SC donation to ct
(`IpcPushDon`). XTopJointRecvIpcPushDonD proves every endpoint receive at a
`MidN` state (`jRecvIpcUDD`, `jRecvIpcLinkDD`), the donation included, and
`jMidChooseFact`'s `CtOK` gives `MidN` there (`not_ctSc_of`, `midN_of`).

* `JRecvLeavesRN17.of_ok`: `JRecvLeavesRN17` from `CtOK` alone (what
  KENTRY-PLAN sch27 called `JRecvLeavesRN18 = {}`: no premise is left on the
  receive leaves).
* `jMidLeavesHyp17_of`: `JMidLeavesHyp17` from the first-phase fact.
* `KDispHyps27M` (mid: `JMidPerfHypQ` [W], `JMidPerfHypB` [W], `JMidVfhHyp`
  [J]; no leaf premise); `.to26M` (`jMidChooseFact` from the dispatch state,
  as `KDispHyps26M.to25M`); NEW TOP `kernel_entryJ27M`.
-/
import Fl4Proofs.P3.XTopJointKEntry26MD
import Fl4Proofs.P3.XTopJointRecvIpcPushDonD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **The receive leaves at a non-resumed mid state from `CtOK`** (module
docstring): every endpoint receive at `MidN`, the reply-push donation
included. -/
theorem JRecvLeavesRN17.of_ok (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hok : MidRun.CtOK σ) : JRecvLeavesRN17 (L := L) arI AR Z.th ct s a σ where
  ipc := fun p b sd g gr rc rc' hpE hrc hHd hHr ho hC _ => by
    have hN : MidN σ := midN_of hni1 hrun ho (not_ctSc_of hok hC)
    obtain ⟨hcur, -⟩ := J.curEq hct
    have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
    rcases hrc with ⟨h0, h0'⟩ | ⟨hcr, q, g', e, xr, hkr⟩
    · exact jRecvIpcUDD hAT hmax hmb htu J hctT hcur hN hnq p b sd g gr rc rc' hpE (Or.inl ⟨h0, h0'⟩)
        hHd hHr (Or.inl h0)
    · subst e
      by_cases hi0 : L.mem s (Endp.rTcbA q) = 0#u64
      · exact jRecvIpcUDD hAT hmax hmb htu J hctT hcur hN hnq p b sd g gr _ rc' hpE
          (Or.inr ⟨hcr, q, g', rfl, xr, hkr⟩) hHd hHr (Or.inr ⟨q, g', rfl, hi0⟩)
      · exact jRecvIpcLinkDD hAT hmax hmb htu J hctT hcur hN hnq p b sd g gr q g' rc' hpE hcr hkr hHd
          (hHr q g' rfl) hi0

/-- **`JMidLeavesHyp17` from the first-phase fact** (module docstring). -/
theorem jMidLeavesHyp17_of (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hF : ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1,
      MidRun.CtOK y.2) : JMidLeavesHyp17 (L := L) arI AR cptr σ := by
  intro y hy _ _ hnq _ _ s1 a1 _ hrun hni1 Z H Cs Ac Lst D J ct hct
  exact JRecvLeavesRN17.of_ok hAT hmax hmb (htu a1) J hct hni1 hrun hnq (hF y hy)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The dispatch premises without a leaf premise at the mid state**
(module docstring). -/
structure KDispHyps27M (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlob (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlob (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    MidRun.JMidPerfHypB true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ

variable {arI}

/-- **`KDispHyps26M` from `KDispHyps27M`** at an `Entered` dispatch state:
`jMidChooseFact` from `JAtZ.midCQ`, `JAtZ.cur`, `JAtZ.inv`, then
`jMidLeavesHyp17_of`. -/
theorem KDispHyps27M.to26M (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {n : I64} {c : Fl4Spec.Syscall} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (h : KDispHyps27M (L := L) arI AR Z H Cs D s a σ n c) : KDispHyps26M (L := L) arI AR Z H Cs D s a σ n c where
  inv := h.inv
  recv := h.recv
  mid := fun ct rg sr cr hct hm => by
    obtain ⟨h1, h2, h3, h4, hB, h5⟩ := h.mid ct rg sr cr hct hm
    obtain ⟨hs, hq⟩ := J.midCQ hni h2
    have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
    exact ⟨h1, h2, h3, h4, hB, h5, jMidLeavesHyp17_of hAT hmax htu hmb
      (MidRun.jMidChooseFact true true _ σ hs hq hC J.inv h4 hB)⟩

set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ26M`
with `KDispHyps27M` (mid: entry facts, `JMidPerfHypQ` [W], `JMidPerfHypB`
[W], `JMidVfhHyp` [J]; no receive-leaf premise) for `KDispHyps26M` (module
docstring). -/
theorem kernel_entryJ27M [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps27M (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
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
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  obtain ⟨x, hk, -⟩ := (J.xtop.irelK J.ks J.buf).1.tcb _ hctT
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  exact kernel_entryJ26M s a σ J hni n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' =>
      (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to26M hA hmax htu hmb J' (BudgetAt.entered hnd hk' hni hBA))
    hFin hARI hA hnd hPP hmrt hmb hIP hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
