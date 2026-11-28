/-
P3 (p3J gen 30): **`DispStabFootL` restated over its leaf classes; the receive class reduced to the endpoint
receive** (the notification receive, the cap faults, the lookup and the bound-TCB read proved).

* **`RecvRelSF Z H Cs s0`**: the relation one `handle_recv` leaf ends in, from the dispatch state `s0`:
  `RelTopM`, `JStabR Z H Cs` (StPostMid; stable ghosts, receive exit form) and the run writes only
  `ProjW H Cs s0`.
* **`handle_recvJSt`**: XTopJointDispatch's `handle_recvJ` at `RecvRelSF` (IpcRecvTopH's `handle_recv_refinesH`,
  the registers, the lookup and the caps' objects as there): the notification leaf by P3JSigSt's
  `jRecvSigStFt` (no premise), the cap fault by StPostFault's `JAtZ.faultHypJZGSt` with P3JMcFlt's `faultProjW`
  (no premise), the bound TCB by IpcLeaves' `recv_bound_leaf`; the endpoint leaf named (`hIpc`, the
  `RecvLeavesH.ipc` shape at `RecvRelSF`).
* **`RecvIpcStFt` [J]**: that endpoint leaf at a dispatch state (`JAtZ (Z.mv Z.G V) H Cs`, `Entered`, the
  current thread in no ready queue, `CKI`, `RR`): FL4's `receive_ipc` on an endpoint cap with the receive right
  held in a slot, with a null or a held reply cap, ends at an outcome of the spec's `receiveIpc` in
  `RecvRelSF Z H Cs`. Justification (not refuted): the non-stable `receive_ipc` at `J` is proved with no
  premise (XTopJointRecvIpcLink's `jRecvIpcHypL_of`), and its sub-leaves build their exits at `Z.mv Z.G V'`
  with the entry's `H`, `Cs` (StPostRecvBlk did two of them verbatim); on `CKI` there is no buffer frame cap, so
  the transfer writes registers only (gen 27's `xferOKRS_nb`, `U = ∅`), and every other write is a word of an
  `H` TCB / endpoint / reply / SC / notification, the kernel-state block or a node of `Cs` (`ProjW`). Missing:
  stable copies of the ~20 receive sub-leaves and a KWN footprint walk of `receive_ipc` (none exists in P1/P2).
* **`dispRecv_stFt`**: the receive class of P3JSysSt's `DispStabFootAt` (`RecvSys n bl cr`,
  `c = recvSysOf bl cr`) from `RecvIpcStFt` at the dispatch states and `SInvX` at the entry state: `Entered`
  (`BudgetAt.entered`), the ready queues and `valid_fault_handler` at the dispatch state (`BudgetAt.shape27`,
  `SInvAll.sinvB_disp`, as `KDispHypsKV27.to26`), `handle_recvJSt`, `MR` by XTopJointKEntry37's
  `dispatch_recv_mr` (`MRKeepD`) and `MachT.mtk_handleRecvG` (`msF_mrT`).
* **`DispStabFootLv` [J]**: the leaves of `DispStabFootL` not yet proved, as a structure: `inv` (the invoking
  class, `InvSys`), `mid` (`MidSys`: ReplyRecv / NBSendRecv / NBSendWait) — each `DispStabFootAt` under
  `DispStabFootL`'s case conditions — and `recvIpc` (`RecvIpcStFt` at every dispatch state of the entry).
  **`dispStabFootL_of_Lv`**: `DispStabFootLv → DispStabFootL` (the receive class by `dispRecv_stFt`, Yield
  excluded by `DispStabFootL`'s own condition).
* **`kernel_entry_runMcWKR_sysLv`**: the native syscall clause, `RunMcWKR` → `RunMcWKR`, with `DispStabFootLv`
  only (+ the platform globals of P3JSysLeaf's `kernel_entry_runMcWKR_sysL`).

Narrowing honesty: the `inv` / `mid` fields are `DispStabFootL` restricted (implied by it); `recvIpc` is not
implied by `DispStabFootL` (it speaks of a sub-call of the dispatch), it implies the receive class of it. The
remaining [J] content is exactly: the invoking class, the mid class, and the endpoint receive.

(p3J gen 51) **`handle_recvJStL`**: `handle_recvJSt`'s shell generalised in place (no `Entered`, the notification
and cap-fault leaves named at `RecvRelSF` as the endpoint leaf); `handle_recvJSt` is now its instance (statement
unchanged).

Named premises: `RecvIpcStFt` [J], `DispStabFootLv` [J] (above). No sorry. New module; no existing statement
changed.
-/
import Fl4Proofs.P3.P3JSysLeaf
import Fl4Proofs.P3.P3JSigSt
import Fl4Proofs.P3.StPostEv
import Fl4Proofs.P3.XTopJointKEntry37
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop)

/-- (p3J gen 30) **The relation a `handle_recv` leaf ends in, from the dispatch state `s0`** (module docstring). -/
def RecvRelSF (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s0 : S) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) :
    Prop :=
  RelTopM (L := L) s1 σ1 ∧ JStabR (L := L) arI AR Z H Cs s1 a1 σ1 ∧
    P1.WritesIn st s0 s1 (Mc.ProjW (L := L) H Cs s0)

/-- (p3J gen 30) **The endpoint leaf of `handle_recv` at `RecvRelSF`** (the `RecvLeavesH.ipc` shape). -/
def RecvIpcLeafSF (Z : XSets) (H : P1.Heap) (Cs : Set U64) (ct : U64) (blocking : Bool) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) Z.th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc) →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) blocking rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) blocking rc' σ).1,
        RecvRelSF (L := L) arI AR Z H Cs s r.1 r.2 z.2 ⦄

/-- (p3J gen 30) **`RecvIpcStFt` [J]**: the endpoint receive at a dispatch state, stable, with its footprint
(module docstring). -/
def RecvIpcStFt (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s a σ → Entered σ →
    (∀ d p, σ.curThread ∉ σ.readyQueues d p) → SInvCk.CKI σ → SInvRr.RR σ →
    ∀ ct, sched.cur_thread st s = ok ct → ∀ blocking : Bool,
      RecvIpcLeafSF (L := L) arI AR Z H Cs ct blocking s a σ

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- `JStab` gives `JStabR`. -/
theorem jStab_toR {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JStab (L := L) arI AR Z H Cs s a σ) :
    JStabR (L := L) arI AR Z H Cs s a σ := by
  obtain ⟨G, V, Ac, Lst, D, J⟩ := h
  exact ⟨G, V, Ac, Lst, D, J.toR⟩

set_option maxHeartbeats 8000000 in
/-- (p3J gen 51) **`handle_recv` at a dispatch state, stable, with its footprint, all three leaves named** (the
shell of `handle_recvJSt` without `Entered`: the notification leaf `hSig` and the cap-fault leaf `hFlt` at
`RecvRelSF` are hypotheses like the endpoint leaf `hIpc`; the registers, the lookup, the looked-up caps' objects and
the bound TCB are read from `J` alone). `handle_recvJSt` is its instance. -/
theorem handle_recvJStL (hAT : P0.ArchTotal arI) {V : XVs} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s a σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (blocking canReply : Bool)
    (hIpc : RecvIpcLeafSF (L := L) arI AR Z H Cs ct blocking s a σ)
    (hSig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
      JHeld (L := L) Z.th s (.Notification p b w rd) →
      notification.receive_signal st arI s a ct p blocking ⦃ r =>
        ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac blocking σ).1,
          RecvRelSF (L := L) arI AR Z H Cs s r.1 r.2 z.2 ⦄)
    (hFlt : ∀ cptr lf lf', LookupFaultRel lf lf' →
      faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
        ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv
          (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
          RecvRelSF (L := L) arI AR Z H Cs s r.1 r.2 z.2 ⦄) :
    syscall.handle_recv st arI s a blocking canReply ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) blocking canReply σ).1,
        RecvRelSF (L := L) arI AR Z H Cs s r.1 r.2 z.2 ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ (Z.mv Z.G V).T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hctT hks
  have hR := J.xtop.rel.2.1.1
  have hV := J.xtop.rel.2.1.2.1
  refine handle_recv_refinesH (RecvRelSF (L := L) arI AR Z H Cs s) (JHeld (L := L) Z.th s) s a σ blocking canReply
    ct hct hcur hks
    (by rw [← regIdx_cap]; exact hxs.regs _) (by rw [← regIdx_reply]; exact hxs.regs _)
    (fun cptr => lookup_cap_refines Z.th s σ hR hV ct htcb cptr)
    (fun cptr => WP.spec_mono (lookup_cap_held Z.th s σ hR hV ct htcb cptr) fun r hr c hc => ⟨?_, hr c hc⟩)
    ⟨hIpc, hSig, recv_bound_leaf hI.1 J.obj, hFlt⟩
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

set_option maxHeartbeats 8000000 in
/-- (p3J gen 30) **`handle_recv` at a dispatch state, stable, with its footprint, the endpoint leaf named**
(module docstring). -/
theorem handle_recvJSt (hAT : P0.ArchTotal arI) {V : XVs} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s a σ) [VxE (Z.mv Z.G V)] (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (hC : SInvCk.CKI σ) (blocking canReply : Bool)
    (hIpc : RecvIpcLeafSF (L := L) arI AR Z H Cs ct blocking s a σ) :
    syscall.handle_recv st arI s a blocking canReply ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) blocking canReply σ).1,
        RecvRelSF (L := L) arI AR Z H Cs s r.1 r.2 z.2 ⦄ := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ (Z.mv Z.G V).T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hSig := jRecvSigStFt hAT J hctT hcur hni hnq blocking
  have hFlt : ∀ cptr lf lf', LookupFaultRel lf lf' →
      faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
        ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv
          (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
          RecvRelSF (L := L) arI AR Z H Cs s r.1 r.2 z.2 ⦄ := by
    intro cptr lf lf' h
    have h1 := J.faultHypJZGSt hAT hni hct hnq hvfh (f := .Cap cptr true lf)
      (f' := .capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf')
      (Or.inl ⟨cptr, true, lf, lf', rfl, by rw [ofBl_toBl64], h⟩)
    have h2 := Mc.faultProjW hAT J hC hni hnq hct (.Cap cptr true lf)
    refine WP.spec_mono (WP.spec_and h1 h2) ?_
    rintro r ⟨⟨z, hz, hr1, hr2⟩, hW⟩
    exact ⟨z, hz, hr1, jStab_toR (JStab.mv hr2), hW⟩
  exact handle_recvJStL hAT s a σ J hct blocking canReply hIpc
    (fun p b w rd ac hcr hex hHd => WP.spec_mono (hSig p b w rd ac hcr hex hHd)
      (fun r ⟨⟨z, hz, hr1, hr2⟩, hW⟩ => ⟨z, hz, hr1, jStab_toR (JStab.mv hr2), hW⟩)) hFlt

set_option maxHeartbeats 4000000 in
/-- (p3J gen 30) **`dispatch_syscall` for the receiving syscalls at a dispatch state, stable, with its
footprint** (`handle_recvJSt`; the if-chain as XTopJointDispatch's `dispatch_recvJ`). -/
theorem dispatch_recvJSt (hAT : P0.ArchTotal arI) {V : XVs} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s a σ) [VxE (Z.mv Z.G V)] (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    (hC : SInvCk.CKI σ) (number : I64) (bl cr : Bool) (hn : RecvSys number bl cr)
    (hIpc : RecvIpcLeafSF (L := L) arI AR Z H Cs ct bl s a σ) :
    syscall.dispatch_syscall st arI s a number ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) bl cr σ).1, RecvRelSF (L := L) arI AR Z H Cs s r.1 r.2 z.2 ⦄ := by
  have h := handle_recvJSt hAT s a σ J hni hct hnq hvfh hC bl cr hIpc
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.CAP) ?_
  rintro c0 -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.REPLY) ?_
  rintro c1 -
  rcases hn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysCall; decide)]
    rw [if_pos rfl]; exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysRecv; decide)]
    rw [if_pos rfl]; exact h
  · rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysNBRecv; decide)]
    rw [if_pos rfl]; exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysNBRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysWait; decide)]
    rw [if_pos rfl]; exact h

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (p3J gen 30) **The receive class of `DispStabFoot` from the endpoint leaf** (module docstring). -/
theorem dispRecv_stFt (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) {σ : Fl4Spec.State Unit} (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    {Z : XSets} [VxE Z] {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} {n : I64} {bl cr : Bool}
    (hn : RecvSys n bl cr)
    (hIpc : ∀ σb, BudgetAt σ σb true → ∀ (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
      RecvIpcStFt (L := L) arI AR Z H Cs s' a' σb) :
    DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (recvSysOf bl cr) := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMb hCb hRRb
  obtain ⟨x0, hk0, -⟩ := hX.sb.1.2
  have hnib := BudgetAt.entered hnd hk0 (hX.entered hct) hBA
  obtain ⟨-, ek, ect, -, -, eq⟩ := BudgetAt.shape27 hnd hk0 hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  obtain ⟨hvfh, -⟩ := SInvAll.sinvB_disp (x' := Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2))
    hX.sb hct hk0 rfl rfl ek' ect
  have hq : ∀ d p, σb.curThread ∉ σb.readyQueues d p := by rw [ect, eq]; exact hX.ctQ
  have hct' := cur_thread_eq (L := L) s'
  generalize L.mem s' (L.nodeAt s' (L.cpu s') layout.node.CUR_THREAD) = ct at hct'
  have hI := hIpc σb hBA s' a' hKF V' Ac' Lst' D' J' hnib hq hCb hRRb ct hct' bl
  have hD := dispatch_recvJSt hA s' a' σb J' hnib hct' hq hvfh hCb n bl cr hn hI
  have hM := dispatch_recv_mr (L := L) (s := s') hKD hA hn hMb
  refine WP.spec_mono (WP.spec_and hD hM) ?_
  rintro r ⟨⟨z, hz, -, hJS, hW⟩, hMr⟩
  unfold DispPostSt
  rw [fl4HandleSyscall_recv]
  refine ⟨⟨_, mem_liftE (ε := Unit) hz, Or.inl ⟨rfl, hJS, ?_⟩⟩, hW⟩
  exact msF_mrT hMT hMr (congrArg Prod.fst (MachT.mtk_handleRecvG bl cr _ z hz))

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 30) **`DispStabFootLv` [J]**: the leaves of `DispStabFootL` not yet proved (module docstring). -/
structure DispStabFootLv (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- The invoking class (`SysSend`, `SysNBSend`, `SysCall`). -/
  inv : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (invSysOf call bl)
  /-- The mid class (`SysReplyRecv`, `SysNBSendRecv`, `SysNBSendWait`). -/
  mid : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n c
  /-- The endpoint receive at every dispatch state of the entry (`RecvIpcStFt`). -/
  recvIpc : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → σ.curThread ≠ σ.idleThread → SysFlag (L := L) s →
      ∀ σb, BudgetAt σ σb true → ∀ (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        RecvIpcStFt (L := L) arI AR Z H Cs s' a' σb

variable {arI AR MR}

/-- (p3J gen 30) **`DispStabFootLv → DispStabFootL`** (module docstring). -/
theorem dispStabFootL_of_Lv (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLv (L := L) arI AR MR s a σ) : DispStabFootL (L := L) arI AR MR s a σ := by
  intro hR Z H Cs Ac Lst D J hV n c hct hn hny hfl hk6
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · exact h.inv hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6
  · obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact dispRecv_stFt hA hnd (MachPlatF.toT hM hIp) hKD hX hct hr (h.recvIpc hR Z H Cs Ac Lst D J hV hct hfl)
  · exact absurd rfl hny
  · exact h.mid hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6

set_option maxHeartbeats 4000000 in
/-- (p3J gen 30) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLv` only** (`hLv` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLv [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLv : DispStabFootLv (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysL hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootL_of_Lv hA hnd hM hIp hKD hLv)

end

end Fl4Proofs.P3.Mc
