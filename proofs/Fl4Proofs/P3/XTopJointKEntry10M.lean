/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch15): **`kernel_entryJ10M`:
`JMidRecvHypS` narrowed to the receive leaves.** sch14's `JMidRecvHypS` [W]
asked the whole `handle_recv` at a mid state with a pending switch or
reschedule. Its frame is proved here: `handle_recvJR` is `handle_recvJ`
(XTopJointDispatch) with the post `RJR` (`RelTopM` and `JAtZR`) and no
`Entered` premise: the registers, the cap lookup, the looked-up caps' objects
and the bound TCB of a notification are read from `JAtZ` alone (they never
used `hni`); only the three leaves are named (`JRecvLeavesR`: `receive_ipc`,
`receive_signal`, `handle_fault` of a cap fault, each ending in `RJR`).

* `JMidLeavesHyp` [W] (narrows `JMidRecvHypS`): `JRecvLeavesRN` at the `.ok`
  outcomes of the first phase from the dispatch state whose action is not
  `resumeCurThread`, at every `JAtZ` witness of the mid state, given `hnq`,
  "no switch to ct", `hvfh`, `CurRun` and ct not idle there. l4v:
  `receive_ipc_corres` / `receive_signal_corres` / `handle_fault_corres`
  inside `handle_recv_corres` under `scheduler_act_sane` at that state. True
  in reachable states (each leaf is a part of `JMidRecvHypS`'s receive: the
  leaves are exactly what `handle_recv_refinesH` asks besides the proved
  lookups). Removal: per leaf, the KENTRY-PLAN sch15 handoff (switch case
  via `MidE` and `JAtZR` copies of the blocking leaves; chooseNewThread case
  CurInv-free).
* `JRecvLeavesRN`: the leaves `JMidLeavesHyp` asks, with the notification
  receive only under `SigOpen` (a pending reschedule, or the SC return):
  at a switch mid state the other notification receives are proved
  (XTopJointRecvSigM's `jRecvSigHypM_of`; `JRecvLeavesRN.full`).
* `jMidRecvHypS_of : JMidLeavesHyp → JMidRecvHypS`, `KDispHyps10M` (mid with
  `JMidLeavesHyp` for `JMidRecvHypS`), `KDispHyps10M.to9M`, NEW TOP
  `kernel_entryJ10M` = `kernel_entryJ9M` with `KDispHyps10M`.
-/
import Fl4Proofs.P3.XTopJointRecvSigM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The three leaves of a blocking `handle_recv` ending in `RJR`**
(module docstring; `RecvLeavesH` without the proved `bound`, the held caps
`JHeld`). -/
structure JRecvLeavesR (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) th s (.Notification p b w rd) →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- The notification receives `JRecvLeavesRN` still asks: under a pending
reschedule, or the SC return (a non-active notification whose SC is the
current SC); the rest of a switch mid state is `jRecvSigHypM_of`. -/
def SigOpen (σ : Fl4Spec.State Unit) (p : U64) : Prop :=
  σ.schedulerAction = .chooseNewThread ∨ ∃ x, σ.kheap p.bv = some (.notification x) ∧
    (∀ b', x.ntfnObj ≠ .activeNtfn b') ∧ x.ntfnSc = some σ.curSc

/-- **`JRecvLeavesR` with the notification receive narrowed to `SigOpen`**
(module docstring). -/
structure JRecvLeavesRN (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) th s (.Notification p b w rd) → SigOpen σ p →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **[W] The receive leaves at a mid state with a pending switch or
reschedule** (module docstring). -/
def JMidLeavesHyp (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 8000000 in
/-- **`handle_recv` (blocking) at `J` ending in `RJR`**, from the three
leaves (module docstring): `handle_recvJ`'s proof without `hni`/`hnq`/`hvfh`
(only its fault leaf read them). -/
theorem handle_recvJR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (canReply : Bool)
    (hLv : JRecvLeavesR (L := L) arI AR Z.th ct s a σ) :
    syscall.handle_recv st arI s a true canReply ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true canReply σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hctT hks
  have hR := J.xtop.rel.2.1.1
  have hV := J.xtop.rel.2.1.2.1
  refine handle_recv_refinesH (RJR (L := L) arI AR) (JHeld (L := L) Z.th s) s a σ true canReply ct hct hcur hks
    (by rw [← regIdx_cap]; exact hxs.regs _) (by rw [← regIdx_reply]; exact hxs.regs _)
    (fun cptr => lookup_cap_refines Z.th s σ hR hV ct htcb cptr)
    (fun cptr => WP.spec_mono (lookup_cap_held Z.th s σ hR hV ct htcb cptr) fun r hr c hc => ⟨?_, hr c hc⟩)
    ⟨hLv.ipc, hLv.sig, recv_bound_leaf hI.1 J.obj, hLv.flt⟩
  obtain ⟨y, hy, hcv⟩ := hr c hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  cases c with
  | Endpoint p b x1 x2 x3 x4 =>
    obtain ⟨xe, hke, -⟩ := hI.1.ep p (J.hset.1 p ((hJ.typed _ hy).1 p b x1 x2 x3 x4 hcv))
    exact ⟨xe, hke⟩
  | Reply p g =>
    obtain ⟨xr, hkr, -⟩ := hI.1.reply p (J.hset.2.2 p ((hJ.typed _ hy).2.2 p g hcv))
    exact ⟨xr, hkr⟩
  | Notification p b w r =>
    obtain ⟨xn, hkn, -⟩ := hI.1.ntfn p (J.capN ⟨y, b, w, r, hy, hcv⟩).1
    exact ⟨xn, hkn⟩
  | _ => trivial

/-- **The full leaves from the narrowed ones** at a non-resumed mid state
(a switch to another thread or a reschedule): `jRecvSigHypM_of` for the
notification receives outside `SigOpen`. -/
theorem JRecvLeavesRN.full (hAT : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hsc : σ.schedulerAction ≠ .switchThread σ.curThread) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (h : JRecvLeavesRN (L := L) arI AR Z.th ct s a σ) : JRecvLeavesR (L := L) arI AR Z.th ct s a σ where
  ipc := h.ipc
  flt := h.flt
  sig := fun p b w rd ac hcr hex hHd => by
    by_cases ho : SigOpen σ p
    · exact h.sig p b w rd ac hcr hex hHd ho
    · obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      have hE : MidE σ := by
        refine ⟨hni1, hrun, Or.inr ?_⟩
        cases e : σ.schedulerAction with
        | resumeCurThread => exact absurd e hsw
        | chooseNewThread => exact absurd (Or.inl e) ho
        | switchThread u => exact ⟨u, rfl, fun hu => hsc (by rw [e, hu])⟩
      exact jRecvSigHypM_of hAT J hctT hcur hE hsw hnq p b w rd ac hcr hex hHd fun hx => ho (Or.inr hx)

/-- **`JMidRecvHypS` from `JMidLeavesHyp`** (module docstring). -/
theorem jMidRecvHypS_of (hAT : P0.ArchTotal arI) {cptr : Fl4Spec.CapRef} {cr : Bool} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp (L := L) arI AR cptr σ) : JMidRecvHypS (L := L) arI AR cptr cr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hM
  obtain ⟨hR, ⟨Z, H, Cs, Ac, Lst, D, J⟩, hrun, hni1⟩ := hM
  have hct := cur_thread_eq (L := L) s1
  exact handle_recvJR s1 a1 y.2 J hct cr ((hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J _ hct).full
    hAT J hct hni1 hrun ha hsw hnq)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The dispatch premises with the mid receive narrowed to its leaves**
(module docstring). -/
structure KDispHyps10M (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
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
    JMidLeavesHyp (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ

variable {arI}

theorem KDispHyps10M.to9M (hAT : P0.ArchTotal arI) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (h : KDispHyps10M (L := L) arI AR Z H Cs D s a σ n c) :
    KDispHyps9M (L := L) arI AR Z H Cs D s a σ n c where
  inv := h.inv
  recv := h.recv
  mid := fun ct rg sr cr hct hm => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.mid ct rg sr cr hct hm
    exact ⟨h1, h2, h3, h4, h5, jMidRecvHypS_of hAT h6⟩

set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ9M`
with `KDispHyps10M` (mid: entry facts, `JMidPerfHypQ` [W], `JMidVfhHyp` [J],
`JMidLeavesHyp` [W]) for `KDispHyps9M` (module docstring). -/
theorem kernel_entryJ10M [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps10M (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
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
  kernel_entryJ9M s a σ J hni n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' => (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to9M hA)
    hFin hARI hA hnd hPP hmrt hmb hIP hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
