/-
P3 (p3J gen 32): **the mid class of `DispStabFootLw` split into its invocation half and its receive half; the
receive at a resumed mid state proved**.

ReplyRecv / NBSendRecv / NBSendWait run (`dispatch_syscall`) `handle_invocation false false true true cptr` on the
cap in the REPLY / NBSEND_RECV_DEST register, `after_invocation`, and, when that returns `true` (the invocation
returned `Ok`), `handle_recv true cr`. The spec runs `DispMid sr cr` (XTopJointKEntry8): the register read,
`fl4HandleInvocationR true false false true true cptr`, `handleRecv true cr`.

* **`MidStF σm`**: the spec facts of a mid state the receive reads: the current thread not idle, in no ready
  queue, its fault handler valid, `CKI`, `CurRun`, no switch to it pending (the non-stable chain's
  `JMidPerfHypQ` [W] / `JMidVfhHyp` [J] content, XTopJointKEntry9M, and the spec invariant `CKI`).
* **`MidInvPost Z H Cs cptr σb s0`**: the post of the invocation half from a dispatch state `s0` (spec `σb`): the
  run writes only `ProjW H Cs s0`, and for some outcome `y` of the spec's first phase either FL4 returned `Ok`,
  `y` is `ok`, and `JStab Z H Cs` and `MR` hold at `y.2`; or `y` is the preempted `error` and FL4's
  `after_invocation` from there returns `false` at an outcome of `preemptionPath y.2` with `JStab Z H Cs`, `MR`
  and footprint `ProjW H Cs s0`.
* **`MidInvStFt` [J]**: at every dispatch state of the entry (as `DispStabFootAt`: `BudgetAt σ σb true`,
  `KFrontB`, `JAtZ (Z.mv Z.G V')`, `MR`, `CKI`, `RR`) the invocation half ends in `MidInvPost`.
* **`MidSpecAt` [J]** (spec only): at every dispatch state `σb` of the entry with `CKI`, for every cap pointer,
  every `ok` outcome of the spec's first phase has `MidStF`.
* **`MidRecvSw` [J]**: at the same dispatch states, at every `ok` outcome `y` of the spec's first phase whose
  action is **not** `resumeCurThread` (a switch to another thread or a reschedule is pending), at every FL4 state
  `JAtZ (Z.mv G V) H Cs` related to `y.2` with `MidStF y.2`, `handle_recv true cr` ends in `RecvRelSF Z H Cs`.
* **`recvIpcFtE`**: P3JRecvFtTop's `recvIpcFt_holds` at a `JAtZ Z` state directly (no `RR`, any `Z`).
* **`handle_recvMidSt`**: at a resumed mid state (`Entered`), `handle_recv true cr` in `RecvRelSF Z H Cs`, proved:
  P3JRecvCls's `handle_recvJSt` at `Z.mv G V`, the endpoint leaf by P3JRecvSt's `jRecvIpcHypL_ofSt` with
  `recvIpcFtE`.
* **`dispMid_stFt`**: the mid class of `DispStabFootAt` from `MidInvStFt` and `MidRecvSw` (the if-chain and the
  spec composition as XTopJointKEntry38's `mid_invRecvJMUNM` / `dispatch_midJMUNM`; footprints composed by
  P3JMcIrqH's `WritesIn.projW_trans`).
* **`DispStabFootLm` [J]** {inv, midInv, midSpec, midRecvSw}; **`dispStabFootLw_of_Lm`**; top
  **`kernel_entry_runMcWKR_sysLm`** (globals as `_sysLw`).

Narrowing honesty: `inv` is verbatim from `DispStabFootLw`. `midInv`, `midSpec` and `midRecvSw` are statements about
sub-calls of the dispatch (like gen 30's `recvIpc`): together they imply the old `mid` field (`dispMid_stFt`),
but **they are not implied by it**. Justification that they are not false on reachable states: the invocation
half's stable post with footprint is the part of the old `mid` before the receive (the receive keeps `H`, `Cs`);
`MidStF`'s facts are the non-stable chain's mid-state facts (`JMidPerfHypQ`'s `CQ`: l4v
`perform_invocation_not_blocking_not_calling_ct_active`, `ct_not_in_q`, `scheduler_act_sane`; `JMidVfhHyp`:
`valid_objs`; `CKI` is a spec invariant of every step, P3JCk*); `midRecvSw` is the stable-ghost form of the
non-stable `JMidRecvHypS` [W] / `JMidLeavesHyp` [W] (XTopJointKEntry9M/10M), restricted to the same states
(outcomes of the first phase with a pending switch or reschedule), with footprint `ProjW` (the receive writes only
`H` objects, the kernel-state block and nodes of `Cs`, as `recvIpcProjW`). Removed from the [J] content: the
receive at a resumed mid state, and the dispatch skeleton of the mid class.

(p3J gen 51) **`recvIpcFtB`**: `recvIpcFtE` generalised in place from `Entered` to P1's `CanBlock` of the current
thread; `recvIpcFtE` is now its instance (statement unchanged).

Named premises: `MidInvStFt` [J], `MidSpecAt` [J], `MidRecvSw` [J], `DispStabFootLm` [J] (above). No sorry. New module; no
existing statement changed.
-/
import Fl4Proofs.P3.P3JRecvFtTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 32) **The spec facts of a mid state the receive reads** (module docstring). -/
structure MidStF (σ : Fl4Spec.State Unit) : Prop where
  ni : σ.curThread ≠ σ.idleThread
  nq : ∀ d p, σ.curThread ∉ σ.readyQueues d p
  vfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler
  cki : SInvCk.CKI σ
  run : CurRun σ
  nsw : σ.schedulerAction ≠ .switchThread σ.curThread

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 32) **The post of the mid class's invocation half** (module docstring). -/
def MidInvPost (Z : XSets) (H : P1.Heap) (Cs : Set U64) (cptr : Fl4Spec.CapRef) (σb : Fl4Spec.State Unit) (s0 : S)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  P1.WritesIn st s0 res.2.1 (Mc.ProjW (L := L) H Cs s0) ∧
  ∃ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σb).1,
    (res.1 = .Ok () ∧ y.1 = .ok () ∧ JStab (L := L) arI AR Z H Cs res.2.1 res.2.2 y.2 ∧
      MR res.2.2 y.2.machineState) ∨
    (y.1 = .error () ∧ syscall.after_invocation st arI res.2.1 res.2.2 res.1 ⦃ r => r.1 = false ∧
      (∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) y.2).1,
        JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 z.2 ∧ MR r.2.2 z.2.machineState) ∧
      P1.WritesIn st s0 r.2.1 (Mc.ProjW (L := L) H Cs s0) ⦄)

/-- (p3J gen 32) **`MidInvStFt` [J]**: the mid class's invocation half at every dispatch state of the entry, stable,
with its footprint (module docstring). -/
def MidInvStFt (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (c : Fl4Spec.Syscall) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    KFrontB (L := L) arI s a s' a' → JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
    MR a' σb.machineState → SInvCk.CKI σb → SInvRr.RR σb →
    ∀ ct rg sr cr, sched.cur_thread st s' = ok ct → MidSysR n c rg sr cr →
      syscall.handle_invocation st arI s' a' false false true true (L.mem s' (Endp.regA ct rg)) ⦃ res =>
        MidInvPost (L := L) arI AR MR Z H Cs (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv) σb s' res ⦄

/-- (p3J gen 32) **`MidSpecAt` [J]** (spec only): `MidStF` at every `ok` outcome of the spec's first phase from
every dispatch state of the entry (module docstring). -/
def MidSpecAt (σ : Fl4Spec.State Unit) : Prop :=
  ∀ σb, BudgetAt σ σb true → SInvCk.CKI σb → ∀ cptr : Fl4Spec.CapRef,
    ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σb).1, y.1 = .ok () →
      MidStF y.2

/-- (p3J gen 32) **`MidRecvSw` [J]**: the receive at a mid state with a pending switch or reschedule, stable, with
its footprint (module docstring). -/
def MidRecvSw (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (c : Fl4Spec.Syscall) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    KFrontB (L := L) arI s a s' a' → JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
    MR a' σb.machineState → SInvCk.CKI σb → SInvRr.RR σb →
    ∀ ct rg sr cr, sched.cur_thread st s' = ok ct → MidSysR n c rg sr cr →
    ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true
        (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv)).run σb).1, y.1 = .ok () →
      y.2.schedulerAction ≠ .resumeCurThread → MidStF y.2 →
      ∀ (G : MdbGhost) (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s1 : S) (a1 : A),
        JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s1 a1 y.2 →
        syscall.handle_recv st arI s1 a1 true cr ⦃ r => ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true cr y.2).1,
          RecvRelSF (L := L) arI AR Z H Cs s1 r.1 r.2 z.2 ⦄

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 51) **The endpoint receive's footprint at a `JAtZ` state where the current thread can block** (P1
`CanBlock`; no `Entered`). `recvIpcFtE` is its instance. -/
theorem recvIpcFtB (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
    {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) {ct : U64} (hcb : P1.CanBlock st (P1.Heap.tcbs H) Ac s ct) (blocking : Bool) (p b : U64)
    (sd g gr : Bool) (rc : capability.Cap)
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr)) (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) blocking rc ⦃ r =>
      P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  obtain ⟨y, hy, hcv⟩ := hHd
  have hHe : H p = some .ep := (hJ.typed _ hy).1 p b sd true g gr hcv
  have hcap : ∀ q g', rc = .Reply q g' → q ∈ P1.Heap.replies H := by
    intro q g' e
    obtain ⟨y', hy', hcv'⟩ := hHr q g' e
    rw [e] at hcv'
    exact (hJ.typed _ hy').2.2 q g' hcv'
  refine WP.spec_mono (recvIpcProjW hA J.kern.heap (noBufCap_cki J hC) (bufApart_blk J.blk) s a ct _ blocking rc p
    Q0 R0 h0 hB0 hX0 hS0 hSg0 hcb rfl hHe hcap (fun n hn => hn) (P1.BufK.refl s)) ?_
  rintro ⟨s', a'⟩ hW
  simpa only [WP.uncurry'_pair] using hW

set_option maxHeartbeats 4000000 in
/-- (p3J gen 32) **The endpoint receive's footprint at a `JAtZ` state** (`recvIpcFt_holds` at any `Z`, no `RR`). -/
theorem recvIpcFtE (hA : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
    {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hni : Entered σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (hC : SInvCk.CKI σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (blocking : Bool) (p b : U64) (sd g gr : Bool) (rc : capability.Cap)
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr)) (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) blocking rc ⦃ r =>
      P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  obtain ⟨hcur, x, hk, hrn⟩ := J.curRunnable hni hct
  exact recvIpcFtB hA J hC (J.canBlockCur (TopSR.cur_mem J.xtop.fin.1 hcur.symm) hcur hk hrn hni hnq) blocking p b sd g
    gr rc hHd hHr

set_option maxHeartbeats 8000000 in
/-- (p3J gen 32) **The receive at a resumed mid state, stable, with its footprint** (module docstring). -/
theorem handle_recvMidSt (hA : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {Z : XSets} [VxE Z] {H : P1.Heap} {Cs : Set U64} {G : MdbGhost} {V : XVs} {Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s1 : S} {a1 : A} {σm : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s1 a1 σm) (hni : Entered σm) (hF : MidStF σm) (cr : Bool) :
    syscall.handle_recv st arI s1 a1 true cr ⦃ r => ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true cr σm).1,
      RecvRelSF (L := L) arI AR Z H Cs s1 r.1 r.2 z.2 ⦄ := by
  have hct := cur_thread_eq (L := L) s1
  generalize L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ (Z.mv G V).T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hIpc : RecvIpcLeafSF (L := L) arI AR (Z.mv G V) H Cs ct true s1 a1 σm := by
    intro p b sd g gr rc rc' hpE hrc hHd hHr
    have h1 := jRecvIpcHypL_ofSt hA hmax (htu a1) J hctT hcur hni hF.nq true p b sd g gr rc rc' hpE hrc hHd hHr
    have h2 := recvIpcFtE hA J hni hF.nq hF.cki hct true p b sd g gr rc hHd hHr
    refine WP.spec_mono (WP.spec_and h1 h2) ?_
    rintro r ⟨⟨z, hz, hr1, hr2⟩, hW⟩
    exact ⟨z, hz, hr1, jStab_toR (JStab.mv hr2), hW⟩
  refine WP.spec_mono (handle_recvJSt (Z := Z.mv G V) (V := V) hA s1 a1 σm J hni hct hF.nq hF.vfh hF.cki true cr
    hIpc) ?_
  rintro r ⟨z, hz, hr1, hr2, hW⟩
  exact ⟨z, hz, hr1, JStabR.mv hr2, hW⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- (p3J gen 32) **The mid run at a dispatch state from its two halves** (module docstring;
XTopJointKEntry38's `mid_invRecvJMUNM` shape). -/
theorem mid_invRecvSt (hA : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) {Z : XSets} [VxE Z] {H : P1.Heap} {Cs : Set U64} {V' : XVs} {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) {ct : U64}
    (hct : sched.cur_thread st s' = ok ct) {n : I64} {c : Fl4Spec.Syscall} {rg : U64} {sr : Fl4Spec.Register}
    {cr : Bool} (hn : MidSysR n c rg sr cr)
    (hInv : syscall.handle_invocation st arI s' a' false false true true (L.mem s' (Endp.regA ct rg)) ⦃ res =>
        MidInvPost (L := L) arI AR MR Z H Cs (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv) σb s' res ⦄)
    (hSp : ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true
        (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv)).run σb).1, y.1 = .ok () → MidStF y.2)
    (hSw : ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true
        (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv)).run σb).1, y.1 = .ok () →
      y.2.schedulerAction ≠ .resumeCurThread → MidStF y.2 →
      ∀ (G : MdbGhost) (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s1 : S) (a1 : A),
        JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s1 a1 y.2 →
        syscall.handle_recv st arI s1 a1 true cr ⦃ r => ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true cr y.2).1,
          RecvRelSF (L := L) arI AR Z H Cs s1 r.1 r.2 z.2 ⦄) :
    (do
      let (r, s1, a1) ← syscall.handle_invocation st arI s' a' false false true true (L.mem s' (Endp.regA ct rg))
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 r
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ r =>
      DispPostSt (L := L) arI AR MR Z H Cs c σb s' r ⦄ := by
  have hrg := hn.reg
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ (Z.mv Z.G V').T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hcp : Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs sr) =
      Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv := by
    rw [← hrg, hxs.regs]; rfl
  have hk' : σb.kheap σb.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hreg := mem_getCapReg hk' sr
  rw [hcp] at hreg
  unfold DispPostSt
  rw [fl4HandleSyscall_mid hn]
  refine WP.spec_bind hInv ?_
  rintro ⟨r, s1, a1⟩ hP
  obtain ⟨hW1, ⟨y1, σm⟩, hy, hc⟩ := hP
  rcases hc with ⟨hr1, hy1, hJs, hMm⟩ | ⟨hy1, hAI⟩
  · dsimp only at hr1 hy1 hJs hMm
    subst hr1 hy1
    have hF : MidStF σm := hSp _ hy rfl
    show (do
      let (b, s2, a2) ← syscall.after_invocation st arI s1 a1 (.Ok ())
      if b then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    rw [show syscall.after_invocation st arI s1 a1 (.Ok ()) = ok (true, s1, a1) by
      unfold syscall.after_invocation; rfl, bind_ok]
    show (if true = true then syscall.handle_recv st arI s1 a1 true cr else ok (s1, a1)) ⦃ _ ⦄
    rw [if_pos rfl]
    obtain ⟨G1, V1, Ac1, Lst1, D1, J1⟩ := hJs
    have hRS : syscall.handle_recv st arI s1 a1 true cr ⦃ r =>
        ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true cr σm).1, RecvRelSF (L := L) arI AR Z H Cs s1 r.1 r.2 z.2 ⦄ := by
      by_cases ha : σm.schedulerAction = .resumeCurThread
      · exact handle_recvMidSt hA hmax htu J1 ⟨hF.ni, ha⟩ hF cr
      · exact hSw _ hy rfl ha hF G1 V1 Ac1 Lst1 D1 s1 a1 J1
    refine WP.spec_mono (WP.spec_and hRS (MKD.syscall_handle_recv L.total hA hKD hMm)) ?_
    rintro r ⟨⟨z, hz, -, hJR, hW2⟩, hMz⟩
    exact ⟨⟨(.ok z.1, z.2), mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_ok hy (mem_liftE hz)),
      Or.inl ⟨rfl, hJR, msF_mrT hMT hMz (congrArg Prod.fst (MachT.mtk_handleRecvG true cr _ z hz))⟩⟩,
      hW1.projW_trans hW2⟩
  · dsimp only at hy1 hAI
    subst hy1
    refine WP.spec_bind hAI ?_
    rintro ⟨b, s2, a2⟩ ⟨hb, ⟨z, hz, hJz, hMz⟩, hW2⟩
    dsimp only at hb; subst hb
    show (if false = true then syscall.handle_recv st arI s2 a2 true cr else ok (s2, a2)) ⦃ _ ⦄
    rw [if_neg (by decide), WP.spec_ok]
    exact ⟨⟨_, mem_bindE_ok (mem_liftE (ε := Unit) hreg) (mem_bindE_err hy), Or.inr ⟨rfl, z, hz, hJz, hMz⟩⟩, hW2⟩

set_option maxHeartbeats 8000000 in
/-- (p3J gen 32) **`dispatch_syscall` for the mid syscalls at a dispatch state from the two halves** (the if-chain
as XTopJointKEntry38's `dispatch_midJMUNM`). -/
theorem dispatch_midSt (hA : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) {Z : XSets} [VxE Z] {H : P1.Heap} {Cs : Set U64} {V' : XVs} {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) {ct : U64}
    (hct : sched.cur_thread st s' = ok ct) {number : I64} {c : Fl4Spec.Syscall} {rg : U64} {sr : Fl4Spec.Register}
    {cr : Bool} (hn : MidSysR number c rg sr cr)
    (hInv : syscall.handle_invocation st arI s' a' false false true true (L.mem s' (Endp.regA ct rg)) ⦃ res =>
        MidInvPost (L := L) arI AR MR Z H Cs (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv) σb s' res ⦄)
    (hSp : ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true
        (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv)).run σb).1, y.1 = .ok () → MidStF y.2)
    (hSw : ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true
        (Fl4Spec.toBl (L.mem s' (Endp.regA ct rg)).bv)).run σb).1, y.1 = .ok () →
      y.2.schedulerAction ≠ .resumeCurThread → MidStF y.2 →
      ∀ (G : MdbGhost) (V : XVs) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s1 : S) (a1 : A),
        JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s1 a1 y.2 →
        syscall.handle_recv st arI s1 a1 true cr ⦃ r => ∃ z ∈ (Fl4Spec.handleRecv (Z := Unit) true cr y.2).1,
          RecvRelSF (L := L) arI AR Z H Cs s1 r.1 r.2 z.2 ⦄) :
    syscall.dispatch_syscall st arI s' a' number ⦃ r => DispPostSt (L := L) arI AR MR Z H Cs c σb s' r ⦄ := by
  have h := mid_invRecvSt hA hmax htu hMT hKD J hct hn hInv hSp hSw
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' ct layout.reg.CAP) ?_
  rintro c0 -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' ct layout.reg.REPLY) ?_
  rintro c1 rfl
  rcases hn with ⟨rfl, -, rfl, -, rfl⟩ | ⟨rfl, -, rfl, -, rfl⟩ | ⟨rfl, -, rfl, -, rfl⟩
  · rw [if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysReplyRecv ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SysNBWait; decide), if_pos rfl]
    exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysNBWait; decide), if_neg (show fl4_abi.syscall.SysNBSendRecv ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysNBSendRecv fl4_abi.syscall.SysReplyRecv; decide), if_pos rfl]
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' ct layout.reg.NBSEND_RECV_DEST) ?_
    rintro c2 rfl
    exact h
  · rw [if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysSend; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBSend; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysCall; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysWait; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBWait; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysReplyRecv; decide), if_neg (show fl4_abi.syscall.SysNBSendWait ≠ fl4_abi.syscall.SysNBSendRecv by unfold fl4_abi.syscall.SysNBSendWait fl4_abi.syscall.SysNBSendRecv; decide), if_pos rfl]
    exact h

set_option maxHeartbeats 8000000 in
/-- (p3J gen 32) **The mid class of `DispStabFootAt` from its two halves** (module docstring). -/
theorem dispMid_stFt (hA : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) {Z : XSets} [VxE Z] {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hm : MidSys n c)
    (hI : MidInvStFt (L := L) arI AR MR Z H Cs s a σ n c) (hP : MidSpecAt σ)
    (hS : MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c) :
    DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J' hMb hCb hRRb
  obtain ⟨rg, sr, cr, hn⟩ := midSysR_of hm
  have hct' := cur_thread_eq (L := L) s'
  generalize L.mem s' (L.nodeAt s' (L.cpu s') layout.node.CUR_THREAD) = ct at hct'
  exact dispatch_midSt hA hmax htu hMT hKD J' hct' hn
    (hI σb hBA V' Ac' Lst' D' s' a' hKF J' hMb hCb hRRb ct rg sr cr hct' hn) (hP σb hBA hCb _)
    (hS σb hBA V' Ac' Lst' D' s' a' hKF J' hMb hCb hRRb ct rg sr cr hct' hn)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 32) **`DispStabFootLm` [J]**: the invoking class, and the mid class's two halves (module docstring). -/
structure DispStabFootLm (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- The invoking class (`SysSend`, `SysNBSend`, `SysCall`), verbatim from `DispStabFootLw`. -/
  inv : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n (invSysOf call bl)
  /-- The mid class's invocation half (`MidInvStFt`), under the mid field's conditions. -/
  midInv : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidInvStFt (L := L) arI AR MR Z H Cs s a σ n c
  /-- The mid class's mid-state spec facts (`MidSpecAt`, spec only), same conditions. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- The mid class's receive at a mid state with a pending switch or reschedule (`MidRecvSw`), same conditions. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 32) **`DispStabFootLm → DispStabFootLw`** (module docstring). -/
theorem dispStabFootLw_of_Lm (hA : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLm (L := L) arI AR MR s a σ) : DispStabFootLw (L := L) arI AR MR s a σ where
  inv := h.inv
  mid := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    haveI := hV
    exact dispMid_stFt hA hmax htu (MachPlatF.toT hM hIp) hKD hm
      (h.midInv hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6) (h.midSpec hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
      (h.midRecvSw hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 32) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLm` only** (`hLm` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLm [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLm : DispStabFootLm (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLw hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLw_of_Lm hA hmax htu hM hIp hKD hLm)

end

end

end Fl4Proofs.P3.Mc
