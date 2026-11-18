/-
P3 (DESIGN.md §9), CSpace and TCB: **the CSpace side's cap leaves on `JAt`**
(the fold's re-scoping, plan §0): each leaf takes `JAtZ` at its start state
in place of its bundle (`XTopAt`, `KsApart`, `CurRun`, the typed heap's TCBs
in `Z.T`, `DelInv`, `DelBound`, `McpRel`, `IPlaced`, the scheduler-action
word outside the objects), through `JointAt`'s projections; the redundant
premises of the plan's §2 are derived (the CSpace relation, `FinInv`,
`MdbOKV`, the IRQ and IO relations, the caller's TCB, the arch mask from
`ARIface`, `mask_irq` from `ArchTotal`, the invoked cap's `CapWf` and
`CapValid` from the CSpace relation).

* `CsGlobal`: the deletions' [W]/[P]/[global] premises in one place (the
  object finalisations `XFinHyps` [W], the preemption point `XPreemptHyp`
  [W], the kernel-state layout at the `XTopAt` states [P], `DelInv` at the
  `XTopAt` states [global]); `CsGlobal.postDel` and `CsGlobal.delNtfn`
  discharge `XPostDelHyp` and `XDelNtfnHyp` (XTopPostDel, XTopDelOne).
* `decode_invocation_cnodeJAt`: the CNode cap.
* `decode_invocation_threadJAt`: the Thread cap (TcbXRest from the IPC/Sc
  leaves `TcbXIpc`; every label proved or a named premise).
-/
import Fl4Proofs.P3.ScJoint
import Fl4Proofs.P3.XTopFinIrq
import Fl4Proofs.P3.XTopPortIn
import Fl4Proofs.P3.XTopIrqH
import Fl4Proofs.P3.XTopTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The deletions' premises not at one state** (module docstring). -/
structure CsGlobal (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  /-- The object finalisations at `XTop` [W] (the IPC, scheduler, VSpace and
  VT-x sides'; `irq` from `xFinIrq_of`). -/
  fin : XFinHyps (L := L) arI AR th
  /-- The preemption point at `XTop` [W]. -/
  pre : XPreemptHyp (L := L) arI AR th
  /-- The kernel-state block's interrupt and IO-port layout [P]. -/
  lay : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ →
    IntLayout th (L.ksb s) ∧ IoLayout th (L.ksb s)
  /-- `DelInv` at the `XTopAt` states [global]. -/
  delI : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ → DelInv th (L.mem s)

theorem maskIrq_total (hT : P0.ArchTotal arI) : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a' := by
  intro a irq b
  obtain ⟨a', h, -⟩ := spec_exists (hT.mask_irq a irq b)
  exact ⟨a', h⟩

theorem freeIrq_total (hT : P0.ArchTotal arI) : ∀ (a : A) (irq : U64), ∃ a', arI.irq_free a irq = ok a' := by
  intro a irq
  obtain ⟨a', h, -⟩ := spec_exists (hT.irq_free a irq)
  exact ⟨a', h⟩

theorem CsGlobal.postDel {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hG : CsGlobal (L := L) arI AR th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) : XPostDelHyp (L := L) arI AR th :=
  xPostDelHyp_of arI hARI.toMask hG.lay (maskIrq_total arI hT) (freeIrq_total arI hT)

theorem CsGlobal.delNtfn [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hG : CsGlobal (L := L) arI AR th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI) : XDelNtfnHyp (L := L) arI AR th :=
  xDelNtfnHyp_of arI (fun Z h => h ▸ hG.fin.ntfn) (hG.postDel arI hARI hT) hG.delI

/-- The invoked cap's well-formedness and validity, from the CSpace
relation. -/
theorem slot_cap_wf {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {sl : Fl4Spec.CslotPtr} (hAs : AbsSlot Z.th sl) {c : capability.Cap}
    (hc : capV (L.mem s) (cslotAddr sl) = c) : CapWf c ∧ CapValid Z.th c := by
  have hca : capAt (L.mem s) (cslotAddr sl) = ok c := by rw [capAt_capV, hc]
  obtain ⟨c', ac, hc', hcr, -⟩ := hX.rel.2.1.1.abs_cap hAs
  rw [hca] at hc'; cases eq_of_ok_eq hc'
  exact ⟨hcr.1, hX.rel.2.1.2.1.abs hAs hca⟩

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The other cores' timer words on `JAt`** (`OtherTmOK`): each other
core's node misses `H`'s objects (`JKern.hnd`), which hold the slots' CNodes
and TCBs (`JPlaced`), the sets' objects (`zH`), the SCs (`JPlaced.sc`) and the
arch objects (`SpecCover.arch`); it lies below the ASID table (`JKern.csLt`)
and misses the IPC-buffer words (`nodeB`). -/
theorem JAtZ.otherTmOK {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    OtherTmOK (L := L) Z Cs s σ := by
  intro c' hc' e
  have hX := J.xtop
  have K := J.kern
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hTe : Z.T = P1.Heap.tcbs H :=
    Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩
  have hNP : P1.NodePlaced st Z.T s c' := by rw [hTe]; exact P1.TInv.nodes J.blk c' hc'
  have hlt := K.csLt c' hc'
  have hnb : L.nodeBase s c' = (L.ksb s).val + 13568 + c'.val * 4288 := rfl
  have hout : ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ L.nodeBase s c' ∨ L.nodeBase s c' + 4288 ≤ p.val :=
    fun p k hp => K.hnd p k hp c' hc'
  refine ⟨hNP, fun o ho => ?_⟩
  have hv := P1.nodeAt_val hNP (off := o) (by omega)
  have hb : L.nodeBase s c' ≤ (L.nodeAt s c' o).val ∧ (L.nodeAt s c' o).val + 8 ≤ L.nodeBase s c' + 4288 := by
    rw [hv]; omega
  -- a word in an object of `H` of `2 ^ k.bits` bytes is not in the node
  have miss : ∀ p k, H p = some k → ¬ (p.val ≤ (L.nodeAt s c' o).val ∧ (L.nodeAt s c' o).val < p.val + 2 ^ k.bits) :=
    fun p k hp ⟨h1, h2⟩ => by rcases hout p k hp with h | h <;> omega
  have hVs := hX.fin.2.1
  have hPt := hX.fin.2.2.1
  have arch : ∀ q : U64, (∃ ao, σ.kheap q.bv = some (.archObj ao)) →
      ¬ (q.val ≤ (L.nodeAt s c' o).val ∧ (L.nodeAt s c' o).val < q.val + 4096) := by
    rintro q ⟨ao, hq⟩ ⟨h1, h2⟩
    obtain ⟨n, hn, hH⟩ := J.cover.arch _ ao hq
    have : (4096 : Nat) ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn; simpa using this
    exact miss q _ hH ⟨h1, by simp only [P1.HKind.bits]; omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- no VSpace object
    rintro (⟨q, r, hq, h1, h2⟩ | ⟨t, ht, h1, h2⟩ | ⟨q, hq, h1, h2⟩ | ⟨h1, h2⟩)
    · exact miss q _ (hJ.cnode q r hq) ⟨h1, by simp only [P1.HKind.bits]; rw [pow_add]; omega⟩
    · exact miss t _ ((hJ.tcb t).1 ht) ⟨h1, by simp only [P1.HKind.bits]; omega⟩
    · refine arch q ?_ ⟨h1, h2⟩
      rcases hq with hq | hq | hq | hq | hq
      · obtain ⟨f, hf, -⟩ := hVs.pool q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l4 q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l3 q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l2 q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l1 q hq; exact ⟨_, hf⟩
    · rw [hnb] at hb; omega
  · -- no endpoint-relation word
    rintro (⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hwp, h⟩)
    · exact miss e _ (J.zH.2.1 e he) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
    · exact miss r _ (J.zH.2.2.1 r hr) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
    · obtain ⟨h1, h2⟩ := h; unfold Endp.TOffN at h2
      exact miss t _ (J.zH.1 t ht) ⟨h1, by simp only [P1.HKind.bits]; omega⟩
    · unfold Endp.TL at h
      exact miss t _ (J.zH.1 t ht) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
    · have := J.nodeB wp hwp c' hc'; rw [← h] at this; omega
  · -- no notification-relation word
    rintro (⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩)
    · exact miss n _ (J.zH.2.2.2 n hn) ⟨h1, by simp only [P1.HKind.bits]; omega⟩
    · have hv' := nfootT_val (hX.fin.1.1.1.placed.tcb t ht) h
      exact miss t _ (J.zH.1 t ht) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
  · -- no SC word
    intro sc hsc x n hk ⟨h1, h2⟩
    obtain ⟨-, hH⟩ := hJ.sc sc x n (J.c0 sc hsc) hk
    exact miss sc _ hH ⟨h1, by simp only [P1.HKind.bits]; omega⟩

/-- **`TimerInsHyp` on `JAt`** (P1's `set_thread_state.restart_ok` and
`timer.insert.foot` at `JAtZ.blk`; the current thread runnable, so neither
blocked nor waiting for a reply). -/
theorem JAtZ.timerIns {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    {ct p : U64} (hct : sched.cur_thread st s = ok ct) (hp : p ∈ Z.T) :
    TimerInsHyp (L := L) Z.T Cs s ct p := by
  intro s1 d b hs1
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have hctT : ct ∈ Z.T := J.thT ct (J.xtop.curTcb hcur).1
  obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb ct hctT
  rw [hk] at hk'; cases hk'
  have hnbr : ¬ P1.BlockedR (L.mem s (P1.stA ct)) := fun hb => by
    have hq := Sched.blockedR_queued hR.st hb
    cases hx : x.tcbState <;> simp_all [Fl4Spec.runnable, Fl4Spec.ipcQueuedThreadState]
  have hTe : Z.T = P1.Heap.tcbs H := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩
  rw [hTe] at hctT hp ⊢
  obtain ⟨hb1, -⟩ := P1.sched.set_thread_state.restart_ok (Es := ∅) J.blk hctT (fun h => hnbr (Or.inl h))
    (fun h => hnbr (Or.inr h)) hs1
  exact WP.spec_mono (P1.timer.insert.foot s1 p d b hb1 hp) fun s' h => ⟨h.2.2.1, h.2.2.2⟩

set_option maxHeartbeats 4000000 in
/-- **The CNode cap on `JAt`** (`decode_invocation_cnodeX`): `JAtZ` at the
decode's start; the invoked slot's cap; the CSpace globals (`CsGlobal`), the
arch interface (`ARIface`, `ArchTotal`) [P]; CancelBadgedSends' caller code
below 3 (`NativeScope`'s, [P]) and its facts at every `XTopAt` sets of the
state ([global]: `KsApart`, `BufWordRel`, `IPlaced`, the endpoint among the
endpoints), and at the spec state the endpoints' queued threads' facts,
`ScBack`, `ActReady` (`EpQPre`), the current thread not the switch target; the copies' extra caps (`ExtraRel2`). -/
theorem decode_invocation_cnodeJAt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (p r gs g : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .CNode p r gs g)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel2 Z.th (L.mem s) x0 x1 (excaps.map Prod.fst))
    (hrun : ∀ xt, σ.kheap ct.bv = some (.tcb xt) → tsCode xt.tcbState < 3)
    (hZ : ∀ Z' : XSets, XTopAt (L := L) AR Z' s ar σ → KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s) ∧
      BufWordRel Z'.T (L.mem s) σ ∧ IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B)
    (hQ : ∀ e, Sched.EpQPre σ e)
    (hE : ∀ (Z' : XSets) (e b : U64) (sl : Fl4Spec.CslotPtr), XTopAt (L := L) AR Z' s ar σ → AbsSlot Z.th sl →
      capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z'.E)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr sl) (.CNode p r gs g) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨hwf, hcv⟩ := slot_cap_wf hX hAs hsc
  obtain ⟨K, hK, hK6, hDE⟩ := J.delE
  exact decode_invocation_cnodeX arI hARI.toMask s ar σ hX J.ks (J.curRun.run hni) J.thT (hG.delNtfn arI hARI hT) hG.fin hG.pre
    (hG.postDel arI hARI hT) K hK hK6 hDE lbl slbl hlbl length buf ct hct args hlen hargs p r gs g hwf hcv
    ⟨cslotAddr sl, hAs.isSlot, hsc⟩ extra x0 x1 hx0 hx1 excaps hex J.kern.act hcur hrun
    (fun Z' hX' => let ⟨h1, h2, h3⟩ := hZ Z' hX'
      ⟨h1, h2, h3, hX'.fin.1.cur_mem hcur.symm⟩) hQ (fun u hu => by rw [hni.2] at hu; cases hu) hE (cslotAddr sl) blk call don fp ci sl buffer

set_option maxHeartbeats 4000000 in
/-- **The Thread cap on `JAt`** (`decode_invocation_threadXL`, with
`tcbXOpen_of`): `JAtZ` at the decode's start; the invoked slot's cap; the
CSpace globals, the arch interface [P]; at every `XTopAt` state of the typed
heap [global]: `ActReady` (at `WX`), `BufWordRel`, the IPC-buffer caps
(`IpcBufCapOK`, `BufCover`, `BufPlaced`) and `FlagsRel`; the decode's own
facts (the extra caps, the SC cap's object among the SCs when present (`hcapC`, l4v
`valid_cap`: `JAtZ` relates no SC cap to an SC object; the thread and
notification caps' objects from `XcRel` and `JPlaced`),
the target not idle, the argument reads, the remote stall the identity [P],
the core's `CUR_THREAD` word outside the objects); the IPC/Sc leaves
(`TcbXIpc`), the arguments (`ArgRel` [J], five), GetBreakpoint's read (`GetBpHyp`
[P]), SetFlags' FPU release (`FpuRelXHyp` [P]), ReadFPU's user-frame write (`FpuFrameXHyp`
[W], `fpuFrameX_of`), SetTimer's footprint from P1's (`JAtZ.timerIns`, `JAtZ.otherTmOK`). -/
theorem decode_invocation_threadJAt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hA : ∀ s a σ G, WX (L := L) AR Z.th s a σ G → Notif.ActReady σ)
    (hBT : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → BufWordRel Z'.T (L.mem s') σ')
    (hOK : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.IpcBufCapOK σ')
    (hBC : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → Endp.BufCover Z'.T Z'.B σ')
    (hBPl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    (hFl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' → FlagsRel Z'.T (L.mem s') σ')
    (lbl length : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (argsU : List U64) (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl)
    (hsc : capV (L.mem s) (cslotAddr sl) = .Thread p)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (hNative : lbl ≠ fl4_abi.label.TCBSetEPTRoot)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hpI : p ≠ L.idleW s)
    (x0 x1 x2 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (hx2 : Aeneas.Std.Array.index_usize extra 2#usize = ok x2)
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5) (hGb : GetBpHyp (st := st) s ct p)
    (hFpu : FpuRelXHyp (L := L) arI AR Z.th p ct)
    (hI : TcbXIpc (L := L) arI AR Z.th s ar σ p ct buf argsU blk call don)
    (hFr : ∀ (x ptr offset r : U64) (sz : capability.FrameSize) (m ep : Bool) (asid va : U64),
      capV (L.mem s) x = .Frame ptr sz r false m ep asid va → FpuPass true offset r sz →
      FpuFrameXHyp (L := L) AR Z p (core.num.U64.wrapping_add ptr offset)) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr sl) (.Thread p) blk call don fp buf extra slbl
      (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  -- the first extra cap, when present, is in a CNode slot of the typed heap (`XcRel`)
  have hsl0 : x0 ≠ 0#u64 → ∃ sl0, AbsSlot Z.th sl0 ∧ x0 = cslotAddr sl0 := by
    intro hx
    have h0 := hXc.2 0 x0 rfl
    obtain ⟨e, he⟩ : ∃ e, excaps[0]? = some e := by
      rcases excaps with _ | ⟨e, rest⟩
      · exact absurd (h0.1.2 (by simp)) hx
      · exact ⟨e, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 e he
    exact ⟨e.2, ⟨ps, hpe, Or.inl hps⟩, hxe⟩
  have hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T := by
    intro hx q hc
    obtain ⟨sl0, hA0, hxe⟩ := hsl0 hx
    exact J.thT q (show CapValid Z.th (.Thread q) from
      hX.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hc]))
  have hcapN : x0 ≠ 0#u64 → ∀ q b w r, capV (L.mem s) x0 = .Notification q b w r → q ∈ Z.N := by
    intro hx q b w r hc
    obtain ⟨sl0, hA0, hxe⟩ := hsl0 hx
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact J.hset.2.1 q ((hJ.typed x0 (hxe ▸ hA0.isSlot)).2.1 q b w r hc).2
  have hp : Z.th p = some .tcb := (slot_cap_wf hX hAs hsc).2
  have hpT := J.thT p hp
  exact decode_invocation_threadXL arI s ar σ hX J.ks (J.curRun.run hni) J.thT J.del hG.fin hG.pre (hG.postDel arI hARI hT)
    J.bound hA hBT J.ip lbl length p hp blk call don fp buf extra ct hct hcur slbl hlbl argsU hlen hargs ci sl hAs
    excaps buffer hext hstall' hNative J.kern.act hcw hpI x0 x1 x2 hx0 hx1 hx2 hXc hnc hnc0 J.mcp hcapT hcapC J.c0
    hcapN (fun i hi => hA5 i (by omega)) hI
    (tcbXOpen_of arI s ar σ hX J.ks (J.curRun.run hni) J.thT J.del hBT J.ip hOK hBC hBPl hFl lbl length p hp blk call don buf
      extra ct hct hcur slbl hlbl argsU hlen hargs ci sl excaps buffer hext hstall' J.kern.act
      (fun i hi => hA5 i (by omega)) hGb hFpu
      (tcbXOpen4_of arI s ar σ hX (J.curRun.run hni) J.thT J.del lbl length p hp blk call don buf extra ct hct hcur slbl hlbl
        (argsU.map UScalar.bv) ci sl excaps buffer hext hstall' J.kern.act hA5
        (tcbXOpen3_of arI hARI.toARKeep s ar σ hX (J.curRun.run hni) J.thT J.del lbl length p hp blk call don buf extra ct hct
          hcur slbl hlbl argsU hlen hargs ci sl excaps buffer hext hstall' J.kern.act x0 x1 x2 hx0 hXc hFr
          (tcbXOpen1_of arI s ar σ hX J.ks (J.curRun.run hni) J.del lbl length p blk call don buf extra ct hct hcur slbl hlbl
            argsU hlen hargs ci sl excaps buffer hext hstall' J.kern.act J.otherTmOK (J.timerIns arI hni hct hpT)))))

set_option maxHeartbeats 4000000 in
/-- **The IRQ control cap on `JAt`** (`decode_invocation_irq_controlX`; the
CSpace relation, `FinInv`, `MdbOKV`, `IrqRel`, the caller's TCB, the arch
mask and `mask_irq` derived): beyond `JAtZ`, the CSpace globals, the arch
interface [P], `HandlersActive` [J], the IOAPIC relation (`ArchIrqRel` [P]),
the scheduler-action word apart from the IRQ states, the invoked slot. -/
theorem decode_invocation_irq_controlJAt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hHA : HandlersActive (L.mem s) (L.ksb s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hAR : ArchIrqRel arI ar σ) (blk call don fp : Bool) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IrqControl blk call don fp buf
      extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  exact decode_invocation_irq_controlX arI hARI.toMask Z.th s ar σ Z.G
    (hG.lay Z s ar σ rfl hX).1 hHA lbl slbl hlbl hrm length buf ct
    hct args hlen hargs hcur J.kern.act hact2 extra x0 hx0 excaps hex hps hls hsrcC nA hnum hnA
    (maskIrq_total arI hT) hAR rfl rfl hX J.ks (J.curRun.run hni) J.thT (hG.delNtfn arI hARI hT) blk call don fp ci buffer

set_option maxHeartbeats 4000000 in
/-- **The IO port control cap on `JAt`** (`decode_invocation_ioport_controlX`;
the CSpace relation, `FinInv`, `MdbOKV`, `IoRel`, the caller's TCB derived):
beyond `JAtZ`, the CSpace globals, the arch interface [P], `IoPortsAlloc`
[J], the scheduler-action word apart from the bitmap, the invoked slot. -/
theorem decode_invocation_ioport_controlJAt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hPA : IoPortsAlloc (L.mem s) (L.ksb s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IoPortControl blk call don fp buf
      extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  exact decode_invocation_ioport_controlX arI hARI.toMask Z.th s ar σ Z.G
    (hG.lay Z s ar σ rfl hX).2 hPA lbl slbl hlbl length buf ct
    hct args hlen hargs hcur J.kern.act hact3 extra x0 hx0 excaps hex hps hls hsrcC rfl rfl hX J.ks
    (J.curRun.run hni) J.thT (hG.delNtfn arI hARI hT) blk call don fp ci buffer

set_option maxHeartbeats 4000000 in
/-- **An IO port cap on `JAt`** (`decode_invocation_ioportXT`; the port
range's bounds from the invoked cap's `CapWf`, `port_in`/`port_out` total
from `ArchTotal`): beyond `JAtZ`, the CSpace globals, the arch interface
[P], the value read (`PortInVal` [P]) when called. -/
theorem decode_invocation_ioportJAt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : PortLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (first last : U64)
    (hsc : capV (L.mem s) (cslotAddr sl) = .IoPort first last 0#u64) (call : Bool)
    (hval : call = true → PortInVal arI)
    (blk don fp : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ci : Fl4Spec.CapRef)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr sl) (.IoPort first last 0#u64) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨⟨-, hl, hfl⟩, -⟩ := slot_cap_wf hX hAs hsc
  have hin : ∀ (a : A) p z, ∃ v a', arI.port_in a p z = ok (v, a') := by
    intro a p z
    obtain ⟨⟨v, a'⟩, h, -⟩ := spec_exists (hT.port_in a p z)
    exact ⟨v, a', h⟩
  have hout : ∀ (a : A) p z d, ∃ a', arI.port_out a p z d = ok a' := by
    intro a p z d
    obtain ⟨a', h, -⟩ := spec_exists (hT.port_out a p z d)
    exact ⟨a', h⟩
  exact decode_invocation_ioportXT arI hARI.toMask s ar σ lbl slbl hlbl length buf ct hct args hlen hargs hcur hX
    J.kern.act first last hfl (by simpa using hl) call hin hout hval J.ks (J.curRun.run hni) J.thT (hG.delNtfn arI hARI hT)
    (cslotAddr sl) blk don fp extra ci sl excaps buffer

set_option maxHeartbeats 4000000 in
/-- **An IRQ handler cap on `JAt`** (`decode_invocation_irq_handlerX`; the
CSpace state, `IrqRel`, `MdbOKV`, the caller's TCB, `mask_irq` and the IRQ's
bound (`CapWf`) derived): beyond `JAtZ`, the CSpace globals, the arch
interface [P], the CSpace-level deletion premises (`FinObjHyp`, `PostDelHyp`,
`NtfnKeepHyp`) [W], the IRQ's node slot (`IrqSlotOK` [J]), SetIRQHandler's
extra cap, the domain schedule's placement and P1's deletion facts, the
invoked slot. -/
theorem decode_invocation_irq_handlerJAt [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hG : CsGlobal (L := L) arI AR Z.th)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hO : FinObjHyp (L := L) arI Z.th) (hPD : PostDelHyp (L := L) arI Z.th) (hK : NtfnKeepHyp (L := L) arI Z.th)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = irqHLabelOf lbl)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (irq : U64) (hsc : capV (L.mem s) (cslotAddr sl) = .IrqHandler irq)
    (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : lbl.val = 35 → ExtraSRel Z.th (L.mem s) x0 excaps) (hxn : lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq)
    (hD : DomPlaced (L := L) Z.th s) (hP1 : IrqDelP1 (L := L) s ct irq)
    (length buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length (cslotAddr sl) (.IrqHandler irq) blk call don fp buf extra
      slbl args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hirq : irq.val < 128 := (slot_cap_wf hX hAs hsc).1
  exact decode_invocation_irq_handlerX arI hARI.toMask Z.th hX.rel.1 hO hPD hK s ar σ Z.G J.dstate
    (hG.lay Z s ar σ rfl hX).1 hX.fin.1.1.2.2.2.1 lbl slbl hlbl ct hct hcur (hX.curTcb hcur).1 J.kern.act
    (maskIrq_total arI hT) irq hirq hok extra x0 hx0 excaps hex hxn hX.rel.2.2.2.2.1 hD hP1 rfl hX J.ks (J.curRun.run hni)
    J.thT (hG.delNtfn arI hARI hT) length (cslotAddr sl) buf blk call don fp args ci sl buffer

end

end

end Fl4Proofs.P3
