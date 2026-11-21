/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch20): **`kernel_entryJ18M`:
the notification receive at a `chooseNewThread` mid state with `CurInv`.**
`JMidLeavesHyp8` [W] (XTopJointKEntry17M) asked every receive leaf under
`chooseNewThread`. Where `CurInv` holds there the notification receive is
`jRecvSigHypC2_of` (XTopJointRecvSigC). `JRecvLeavesRN9` asks the notification
receive only under `chooseNewThread ∧ ¬ CurInv` (in reachable states: ct
without an SC, below), the endpoint receive and the cap fault under
`chooseNewThread` as before; `.toRN8`; `JMidLeavesHyp9` [W] = `JMidLeavesHyp8`
concluding `JRecvLeavesRN9`, `jMidLeavesHyp_of9`, `KDispHyps18M`, `.to17M`,
NEW TOP `kernel_entryJ18M`.

Why `¬ CurInv` means "ct has no SC" at these states (sch20 STEP 1): the first
phase is ReplyRecv / NBSendRecv / NBSendWait's invocation with
`firstPhase = true`, and the first-phase decode yields only `FirstInv`
invocations (`okAll_decodeFirst`; FL4 `decode_invocation`'s `first_phase`
checks, C seL4 c98d70ad objecttype.c `decodeInvocation`: thread, domain,
SchedContext, SchedControl and CNode caps are rejected in the first phase).
None of Untyped, endpoint send, notification signal, reply, IRQ control /
handler, arch invocations binds an SC to ct, moves ct to the release queue
or changes the current SC; the only way ct loses `CurInv` while runnable is
giving its SC away (an endpoint send donating to a passive receiver, a reply
returning a donated SC).
-/
import Fl4Proofs.P3.XTopJointKEntry17M
import Fl4Proofs.P3.XTopJointRecvSigC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JRecvLeavesRN8` with the notification receive asked only where
`CurInv` fails** (module docstring). -/
structure JRecvLeavesRN9 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    σ.schedulerAction = .chooseNewThread →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) th s (.Notification p b w rd) → σ.schedulerAction = .chooseNewThread → ¬ CurInv σ →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' → σ.schedulerAction = .chooseNewThread →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **[W] The receive leaves at a non-resumed mid state, the notification
receive narrowed to `¬ CurInv`** (module docstring): `JMidLeavesHyp8`
concluding `JRecvLeavesRN9`. -/
def JMidLeavesHyp9 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN9 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN8` from `JRecvLeavesRN9`**: the notification receive at
a `chooseNewThread` state with `CurInv` by `jRecvSigHypC2_of`. -/
theorem JRecvLeavesRN9.toRN8 (hAT : P0.ArchTotal arI)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (h : JRecvLeavesRN9 (L := L) arI AR Z.th ct s a σ) : JRecvLeavesRN8 (L := L) arI AR Z.th ct s a σ where
  ipc := h.ipc
  flt := h.flt
  sig := fun p b w rd ac hcr hex hHd ho => by
    by_cases hC : CurInv σ
    · obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      have hE : MidC σ := ⟨hni1, hrun, ho, hC⟩
      exact jRecvSigHypC2_of hAT J hctT hcur hE hE.nr hnq p b w rd ac hcr hex hHd
    · exact h.sig p b w rd ac hcr hex hHd ho hC

/-- **`JMidLeavesHyp8` from `JMidLeavesHyp9`** (module docstring). -/
theorem jMidLeavesHyp_of9 (hAT : P0.ArchTotal arI)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp9 (L := L) arI AR cptr σ) : JMidLeavesHyp8 (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN8 hAT J hct hni1 hrun hnq

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The dispatch premises with `JMidLeavesHyp9`** (module docstring). -/
structure KDispHyps18M (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
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
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidLeavesHyp9 (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ

variable {arI}

theorem KDispHyps18M.to17M (hAT : P0.ArchTotal arI)
    {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHyps18M (L := L) arI AR Z H Cs D s a σ n c) : KDispHyps17M (L := L) arI AR Z H Cs D s a σ n c where
  inv := h.inv
  recv := h.recv
  mid := fun ct rg sr cr hct hm => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.mid ct rg sr cr hct hm
    exact ⟨h1, h2, h3, h4, h5, jMidLeavesHyp_of9 hAT h6⟩

set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ17M`
with `KDispHyps18M` (mid: entry facts, `JMidPerfHypQ` [W], `JMidVfhHyp` [J],
`JMidLeavesHyp9` [W]) for `KDispHyps17M` (module docstring). -/
theorem kernel_entryJ18M [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps18M (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
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
  kernel_entryJ17M s a σ J hni n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' => (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to17M hA)
    hFin hARI hA hnd hPP hmrt hmb hIP hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
