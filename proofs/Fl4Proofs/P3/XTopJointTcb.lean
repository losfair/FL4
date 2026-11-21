/-
P3 (DESIGN.md §9), TCB: **the Thread cap at `JAt`, label by label**
(`decode_invocation_threadJ_step`, in the shape of the CNode cap's
`decode_invocation_cnodeJ_stepsL`).

* Every label (no Thread-cap label is left open: no per-op `JPostHyp`, no
  X-level `TcbXIpc`) through `decode_invocation_threadX` at `X := JAt`: the
  labels of no TCB invocation (and the fast-path flag's decode error) are the
  spec's `IllegalOperation` with the state unchanged (`tcb_illegalX`, `JAt`
  at the start); the labels proved here, each with its decode errors at the
  start's `JAtZ`:
  - Suspend (`tcb_suspendJ`: `JAtZ.restartJ`, then `JAtZ.suspendJ` with the
    four cancel steps);
  - WriteRegisters (`tcb_write_regsJ`: the caller's restart, then
    XTopJointWriteRegs' `JAtZ.writeRegsJ`: the register loops at `J`, the
    restart PC, `post_modify_registers`, the optional `JAtZ.restartTcbJ`;
    the caller's buffer mapped (from FL4's `lookup_ipc_buffer` and
    `BufCover`) and the arguments after the restart (`JAtZ.argsRestart`:
    the restart writes the state and action words only, apart from the
    caller's registers and buffer words), the platform's `MIN_BUDGET` [P]);
  - CopyRegisters (`tcb_copy_regsJ`: the caller's restart, the target out
    of the dead set by its cap (`JAtZ.undead`), then XTopJointCopyRegs'
    `JAtZ.copyRegsJ`: the source's suspend (`JAtZ.suspendJD`), the target's
    restart (`JAtZ.restartTcbJD`, also when the source was the current
    thread and a reschedule is pending), the copy loops and the tail; the source not idle
    (`hidS`, from `SpecGlob.idle` at the entry), the platform's `MIN_BUDGET` [P]);
  - Resume (`tcb_resumeJ`: the restart, then XTopJointRestart's
    `JAtZ.restartTcbJ` with the four cancel steps, the target's cap the
    invoked slot's; the platform's `MIN_BUDGET` [P]);
  - UnbindNotification (`tcb_unbind_ntfnJ`: the restart, `JAtZ.unbindNJ`);
  - Set/UnsetBreakpoint (`tcb_set_bpJ`, `tcb_unset_bpJ`: the restart, the
    debug words by `JAtZ.dbgWrJ`, the spec state kept);
  - ReadRegisters (`tcb_read_regsJ`: the restart, then XTopJointReadRegs'
    `JAtZ.readRegsJ`: the source's suspend by `JAtZ.suspendJ`, the copy
    loops at `JAtZ`, `JAtZ.rrTailJ`);
  - SetTLSBase (`tcb_set_tlsJ`: the restart, `JAtZ.regWrJ`, the reschedule
    as a scheduler step `JAtZ.schedJ`);
  - BindNotification (`tcb_bind_ntfnJ`: the decode's checks at the start,
    the restart, XTopJointTcbMisc's `JAtZ.bindNJ`: the spec frame `BKY`,
    the thread and the notification leaving the dead set, covered by their
    caps);
  - WriteFPU (`tcb_write_fpuJ`: XTopTcbFpu's `fpu_refinesX` at `JAt`; the
    restart, the FPU operations by `JAtZ.archJ` [`ARKeep`], the copy into
    the FPU image by XTopJointTcbMisc's `JAtZ.copyFpuJ`);
  - ReadFPU (`tcb_read_fpuJ`: the same checks, the restart, `fpu_flush`,
    the copy of the FPU image into the frame by XTopJointReadFpu's
    `JAtZ.copyFrameJ`, from `FpuFrameJHyp` at the start (a theorem of `JAtZ`,
    `JAtZ.fpuFrameJ`): the frame's bytes lie in spec user frames (its words IPC-buffer words by `FrameCover`); the
    frame missing `H`'s other objects, the TCBs among them, is
    `JPlaced.cobj`; the spec's step `fl4FpuToFrame` changes only those
    2696 bytes of the user memory);
  - SetTimer (`tcb_set_timerJ`: the restart, `timer::insert` by P1's
    `timer.insert.foot` and ScFireJ's `JAtZ.tmw_step`);
  - SetMCPriority (`tcb_set_mcpJ`: the decode's authority MCP by `McpRel`,
    the restart, the `MCP` word by XTopJointTcbSched's `JAtZ.mcpWrJ`);
  - SetPriority (`tcb_set_prioJ`: the same decode, the restart, then
    `set_priority` at `J` by XTopJointTcbPrio's `JAtZ.setPrioJ`);
  - GetBreakpoint (`tcb_get_bpJ`: the restart, then XTopJointData's data
    reply tail: the five words by `JAtZ.setmrJ`, `MR4` a buffer word by
    `JAtZ.userWrJ`, then `JAtZ.replyTailJ`; `XTop`'s facts by the same steps
    at `RInv` and `data_tail_core`, `WP.spec_and`);
  - SetTimeoutEndpoint and SetSpace (XTopJointTcbInstall's
    `tcb_set_timeoutJ`, `tcb_set_spaceJ`: the restart, the cap installs at
    the deletion loop's invariant by `thread_control_capsJ`, `JAtPre` after
    a preempted delete);
  - SetSchedParams (XTopJointTcbSsp's `tcb_set_sched_paramsJ`: the decode,
    the restart, the fault handler's install at the deletion loop's
    invariant with the other slots kept (`install_fhJ`), `set_mcp`,
    `set_priority` (`JAtZ.setPrioJS`), then `unbind_tcb` (`JAtZ.unbindTcbJ`)
    or `bind_tcb` (`JAtZ.bindTcbJ`); the spec's install by
    `install_sched`; named: the platform's `TimeAgree` [P]). The conclusion is `XCapP` at `JAt`, `JAtPre`
    (`XCap.toP` for the other labels); the installs' deletion from the
    loop's steps (`JDelParts`, the platform's `PPPlat` [P], `hRd0` [J] for
    `PPR0`), as `decode_invocation_cnodeJ_stepsL`.
* `JAtZ.restartJ` (XTopJointTcbInstall): the caller's restart at `J` (`jowes_restart`, no premise).
* `JAtZ.reg_frameG`, `JAtZ.dbgWrJ`: XTopJointRegFrame's register frame
  widened to the TCBs' debug words (offsets 448..512, read by no relation),
  and one debug word written at `J`.
* `JAtZ.schedJ` (now in XTopJointCopyRegs): a scheduler step at `J` (`jowes_sched`).
-/
import Fl4Proofs.P3.XTopJointDelR
import Fl4Proofs.P3.XTopJointReply
import Fl4Proofs.P3.XTopJointData
import Fl4Proofs.P3.XTopJointReadRegs
import Fl4Proofs.P3.XTopJointTcbMisc
import Fl4Proofs.P3.XTopJointTcbPrio
import Fl4Proofs.P3.XTopJointRestart
import Fl4Proofs.P3.XTopJointCopyRegs
import Fl4Proofs.P3.XTopJointTcbInstall
import Fl4Proofs.P3.XTopJointReadFpu
import Fl4Proofs.P3.XTopJointTcbSsp
import Fl4Proofs.P3.XTopJointTcbInsL
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
  {s : S} {ar : A} {σ : Fl4Spec.State Unit}

/-- The target, not FL4's idle word, is not the spec's idle thread. -/
theorem JAtZ.ne_idle (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {p : U64} (hpI : p ≠ L.idleW s) :
    p.bv ≠ σ.idleThread := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have ei : L.idleW s = nodeW st s Z.c layout.node.IDLE_THREAD := by
    unfold P1.LawfulStore.idleW nodeW; rw [hc.cur]
  intro e
  exact hpI (Eq.symm (by rw [ei]; apply P1.eq_of_bv; rw [← hs.idleTh, ← e]))


end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

open Fl4Proofs.P1 in
set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across a register step with debug words** (XTopJointRegFrame's
`JAtZ.reg_frameF`, the write set widened by the TCBs' debug words, offsets
448..512: TCB words outside every relation, as the register words). -/
theorem JAtZ.reg_frameG (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64}
    (hI3 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hw : P1.WritesIn st s s' (fun b => RegFW Z.T Z.C b ∨ ∃ y ∈ Z.T,
      (y.val + 448 ≤ b.val ∧ b.val < y.val + 512) ∨ b.val = y.val + 3456)) (hA : QKY σ σ') (hyk : YKeep σ σ') (hInv : Inv σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s)) :
    ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst D s' a σ' := by
  have hI := J.xtop.irelK J.ks J.buf
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw fun b hb => by
    rcases hb with ((hb | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩) | ⟨y, hy, ⟨h1, h2⟩ | h1⟩
    · obtain ⟨y, hy, h1, h2⟩ := hb
      exact Or.inr (Or.inr (Or.inl ⟨y, hy, h1, by omega⟩))
    · obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs q hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hq, x0, n0, hk0, hx0.in_obj (hx0.hdr (K := 8#u64) (by simp) (by simp)).2⟩))))))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
  have hwF : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hw.mono fun b hb => by
    rcases hb with ((⟨y, hy, k1, k2⟩ | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩) | ⟨y, hy, ⟨k1, k2⟩ | k1⟩
    · exact Or.inr ⟨y, hy, b.val - y.val, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inl (KFoot.of_sw (sw_hdr hS hq (K := 8#u64) (by simp) (by simp) (by decide)))
    · exact Or.inr ⟨y, hy, 3376, by omega, by omega, by omega, by omega, by omega, hb⟩
    · exact Or.inr ⟨y, hy, b.val - y.val, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr ⟨y, hy, 3456, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hck : Fl4Proofs.P3.CKeep σ σ' := hA.ckeepP
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 hAR hF.1 hck.cdt hck.orig hck.ks hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hwF
  have ck := hA.callKeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hA.khrb
  have hDbg := J.kw_dbg (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hKd := J.kw_dbgKeep (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hI3.2.2.1
  have hAI3 : ActIdle σ' := hA.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_qk hA hS3 hI3.1 hwF k3 hAI3.1 (J.yld.frame k2 hyk) hyk
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hA.szKeep q.bv y n hq) hks (J.finW_irq hwF)
      (J.idleW_keep hS3 hA.idle hA.isc).2⟩
  have hkern := J.kern_keep hks hwF.2.1 hS3 hA.ct hA.csc (fun sl h => Or.inl (by rw [← hA.orig]; exact h))
    (by rw [hA.arch])
    (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac' Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 hyk, J.mcp.frame k1 hA.mcpKeep, J.buf.frame kb hA.bufKeep, hRP',
      J.apart.sc_frame hks hA.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 hA.idle hA.isc), hkern,
      J.finW_utc hwF hF.1 hA.cdt hA.orig hA.arch hDbg, hA.nsc J.nsc, hInv, hA.cur J.cur, hA.own J.own, hA.off J.off,
      hAI3, hA.bsa J.bsa, hA.isorted J.isorted, hA.curRunM J.curRun, hblk⟩
  have hC0 := JCs.same J hF.1 hA.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hwF (fun b hb => Ipc.FinW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => Ipc.FinW.nv J.xtop.fin.1.1.1 hb) hA.arch (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hA.szKeep hF.1 hA.kback hA.ipcFr hC R hKd hck.orig (J.idleW_keep hS3 hA.idle hA.isc).1 J.zD⟩

open Fl4Proofs.P1 in
set_option maxHeartbeats 8000000 in
/-- **A debug word of a TCB written at `J`** (`JAtZ.reg_frameG` with the
spec state kept: `XTopAt.tcbWrA`, `IRel` by `XTopAt.irelK`, P1's `BlkOK` by
`blk_rf`, its footprint by `foot_field`). -/
theorem JAtZ.dbgWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (wa : U64)
    (Kv : Nat) (hK : 448 ≤ Kv ∧ Kv < 512 ∧ Kv % 8 = 0) (hwav : wa.val = t.val + Kv) (v : U64) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s wa v) a σ := by
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hta := hT t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hT
  set K : U64 := ⟨BitVec.ofNat 64 Kv⟩ with hKdef
  have hKv : K.val = Kv := by
    show (BitVec.ofNat 64 Kv).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hKt : (core.num.U64.wrapping_add t K).val = t.val + K.val := tfield_val hta (by omega)
  have hreq : wa = core.num.U64.wrapping_add t K := UScalar.eq_of_val_eq (by rw [hwav, hKt, hKv])
  subst hreq
  have hwa : P1.Aligned (core.num.U64.wrapping_add t K) := P1.field_aligned hta (by omega) (by omega)
  have hw : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (· = core.num.U64.wrapping_add t K) :=
    P1.writesIn_wr hwa
  have hblk := (P1.blk_rf J.blk (hw.mono fun b hb => Or.inl ⟨t, htH, K, by omega, by omega, hb⟩)).1
  have hfoot : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (P1.KW st (P1.Heap.tcbs H) Cs
      (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) ∅ s) :=
    P1.foot_field hTH htH (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
  have hX' := J.xtop.tcbWrA ht _ Kv (Or.inr (Or.inr (Or.inl hK))) (by rw [hKt, hKv]) v
  have hks : L.ksb (L.wr s (core.num.U64.wrapping_add t K) v) = L.ksb s := hw.1
  have hwF : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) :=
    hw.mono fun b hb => Or.inr ⟨t, ht, Kv, by omega, by omega, by omega, by omega, by omega, by rw [hb, hKt, hKv]⟩
  obtain ⟨-, -, kb, -, -⟩ := J.finW_keeps hwF
  have hA : QKY σ σ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun p => Or.inl rfl⟩
  have hBW : BufWordRel Z.T (L.mem (L.wr s (core.num.U64.wrapping_add t K) v)) σ := J.buf.frame kb hA.bufKeep
  have hI3 := hX'.irelK (by rw [hks]; exact J.ks) hBW
  exact J.reg_frameG hI3 (hw.mono fun b hb => Or.inr ⟨t, ht, Or.inl ⟨by rw [hb, hKt, hKv]; omega,
    by rw [hb, hKt, hKv]; omega⟩⟩) hA (YKeep.of_kheap rfl) J.inv hblk hfoot

open Fl4Proofs.P1 in
set_option maxHeartbeats 8000000 in
/-- **A TCB's flags at `J`** (SetFlags' write): FL4's flags word (offset 3456,
read by no relation of `JAtZ`; P1's `BlkOK` by `plainW_all`) and the spec's
`tcb_flags` (`XTopAt.bufSpec`, a quiet step `QKY`), by `JAtZ.reg_frameG`. -/
theorem JAtZ.flagsWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (w : U64) (nf : Fl4Spec.TcbFlags) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s (core.num.U64.wrapping_add t 3456#u64) w) a
      (updK σ t.bv (.tcb { x with tcbFlags := nf })) := by
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hta := hT t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hKt : (core.num.U64.wrapping_add t 3456#u64).val = t.val + 3456 := Notif.tfield_val hta (by decide)
  have hwa : P1.Aligned (core.num.U64.wrapping_add t 3456#u64) := P1.field_aligned hta (by decide) (by decide)
  have hw : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t 3456#u64) w)
      (· = core.num.U64.wrapping_add t 3456#u64) := P1.writesIn_wr hwa
  obtain ⟨hblk, hfoot, -⟩ := P1.plainW_all (K := 3456#u64) (v := w) J.blk htH (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hX' := (J.xtop.tcbWrA ht _ 3456 (Or.inr (Or.inr (Or.inr rfl))) hKt w).bufSpec (tcbFlagsStep_upd hk nf)
  have hks : L.ksb (L.wr s (core.num.U64.wrapping_add t 3456#u64) w) = L.ksb s := hw.1
  have hwF : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t 3456#u64) w)
      (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) :=
    hw.mono fun b hb => Or.inr ⟨t, ht, 3456, by omega, by omega, by omega, by omega, by omega, by rw [hb, hKt]⟩
  obtain ⟨-, -, kb, -, -⟩ := J.finW_keeps hwF
  have hA : QKY σ (updK σ t.bv (.tcb { x with tcbFlags := nf })) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q => ?_⟩
    by_cases e : q = t.bv
    · subst e; exact Or.inr (Or.inl ⟨x, { x with tcbFlags := nf }, hk, by simp [updK], rfl⟩)
    · exact Or.inl (by simp [updK, e])
  have hyk : YKeep σ (updK σ t.bv (.tcb { x with tcbFlags := nf })) := by
    refine ⟨fun q y hq => ?_, fun q y n hq => ?_, fun q y n hq => ?_⟩
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq; exact ⟨{ x with tcbFlags := nf }, by simp [updK], rfl⟩
      · exact ⟨y, by simp [updK, e, hq], rfl⟩
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq
      · exact ⟨y, by simp [updK, e, hq], rfl⟩
    · by_cases e : q = t.bv
      · subst e; simp [updK] at hq
      · exact ⟨y, by simpa [updK, e] using hq, rfl⟩
  have hBW : BufWordRel Z.T (L.mem (L.wr s (core.num.U64.wrapping_add t 3456#u64) w))
      (updK σ t.bv (.tcb { x with tcbFlags := nf })) := J.buf.frame kb hA.bufKeep
  have hI3 := hX'.irelK (by rw [hks]; exact J.ks) hBW
  exact J.reg_frameG hI3 (hw.mono fun b hb => Or.inr ⟨t, ht, Or.inr (by rw [hb, hKt])⟩) hA hyk
    (J.inv.updSame hk rfl rfl (Or.inl rfl)) hblk hfoot

set_option maxHeartbeats 8000000 in
/-- **`JAtZ.fpuReleaseJ` with the facts the reply tail reads**: the current
thread and every TCB's state kept by the spec's outcome. -/
theorem JAtZ.fpuReleaseJ' (hK : ARKeep arI AR) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64}
    (ht : t ∈ Z.T) :
    arI.fpu_release a t ⦃ a' => ∃ σ', ((), σ') ∈ (Fl4Spec.fpuRelease (Z := Unit) t.bv σ).1 ∧
      σ'.curThread = σ.curThread ∧
      (∀ q y, σ.kheap q = some (.tcb y) → ∃ y', σ'.kheap q = some (.tcb y') ∧ y'.tcbState = y.tcbState) ∧
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s a' σ' ⦄ := by
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_mono (hK.fpu_release a t _ hAR) ?_
  intro a' hAR'
  obtain ⟨Q, R0, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨x, hk, -⟩ := hs.tcb t ht
  obtain ⟨ta, ms, o, hr, hum, hm⟩ := Sched.fpuRelease_outF hk
  obtain ⟨V1, J1⟩ := J.tcbArchJ ht hk ta hr
  refine ⟨_, hm, rfl, fun q y hq => ?_, V1, J1.arFrS (arFr_fpuOwner _ ms o) (J1.xtop.fpuOwner ms o hum hAR')⟩
  by_cases e : q = t.bv
  · subst e; rw [hk] at hq; cases hq; exact ⟨{ x with tcbArch := ta }, by simp [updK], rfl⟩
  · exact ⟨y, by simp [updK, e, hq], rfl⟩

/-- Two register writes of a TCB to different registers commute (the spec
side of FL4's reply-register order). -/
theorem setReg_comm (x : Fl4Spec.Tcb) {a b : Fl4Spec.Register} (h : a ≠ b) (u v : Fl4Spec.Word) :
    Notif.setReg (Notif.setReg x a u) b v = Notif.setReg (Notif.setReg x b v) a u := by
  simp only [Notif.setReg, Notif.setRegUc, Fl4Spec.archTcbContextGet, Fl4Spec.archTcbContextSet]
  rw [Function.update_comm h]

set_option maxHeartbeats 8000000 in
/-- **FL4's `configure_single_stepping` at `J`** (as `css_xtop`): the debug
words `SS_ENABLED`, `SS_COUNT` (`JAtZ.dbgWrJ`); with no instruction count, the
target's `FLAGS` register (`JAtZ.regWrJ`), against the spec's `cssState`. -/
theorem JAtZ.cssJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hpT : p ∈ Z.T)
    {xp : Fl4Spec.Tcb} (hkp : σ.kheap p.bv = some (.tcb xp)) (bp n : U64) :
    debug.configure_single_stepping st arI s a p bp n false ⦃ r => r.1 = false ∧ r.2.2 = a ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D r.2.1 a (cssState σ p.bv xp n.bv) ⦄ := by
  have hpf := (J.ip.e.tcb p hpT).fits
  unfold debug.configure_single_stepping
  by_cases hn : n = 0#u64
  · subst hn
    simp only [↓reduceIte, set_debug_reg_wr, bind_ok]
    obtain ⟨V2, J2⟩ := J.dbgWrJ hpT (dbgA p debug.SS_ENABLED) (448 + 48) (by omega)
      (by rw [dbgA_val (by omega) (by unfold debug.SS_ENABLED; decide)]; unfold debug.SS_ENABLED; simp) 0#u64
    simp only [Std.bind_assoc]
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec _ p layout.reg.FLAGS) ?_
    rintro i rfl
    rw [eflags_tf_eq]; simp only [bind_ok, lift]
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ p layout.reg.FLAGS _) ?_
    rintro s3 rfl
    simp only [set_debug_reg_wr, bind_ok, WP.spec_ok]
    set s2 := L.wr s (dbgA p debug.SS_ENABLED) 0#u64
    obtain ⟨x2, hk2, hx2⟩ := J2.xtop.fin.1.1.2.1.tcb p hpT
    rw [hkp] at hk2; cases hk2
    have hXr := reg_wr_irel J2.ip (J2.xtop.irelK J2.ks J2.buf) hpT hkp Fl4Spec.Register.flags (by decide)
      (L.mem s2 (regA p layout.reg.FLAGS) &&& ~~~256#u64)
    obtain ⟨V3, J3⟩ := J2.regWrJ hpT hkp Fl4Spec.Register.flags
      (L.mem s2 (regA p layout.reg.FLAGS) &&& ~~~256#u64) hXr
    rw [regIdx_flags] at J3
    obtain ⟨V4, J4⟩ := J3.dbgWrJ hpT (dbgA p debug.SS_COUNT) (448 + 56) (by omega)
      (by rw [dbgA_val (by omega) (by unfold debug.SS_COUNT; decide)]; unfold debug.SS_COUNT; simp) 0#u64
    have hflag : (L.mem s2 (regA p layout.reg.FLAGS) &&& ~~~256#u64).bv =
        xp.tcbArch.tcbContext.userRegs .flags &&& tfMask := by
      rw [UScalar.bv_and, ← regIdx_flags]
      exact congrArg₂ (· &&& ·) (hx2.regs .flags) (by rfl)
    have e : cssState σ p.bv xp (0#u64).bv =
        Notif.updK σ p.bv (.tcb (Notif.setReg xp Fl4Spec.Register.flags
          (L.mem s2 (regA p layout.reg.FLAGS) &&& ~~~256#u64).bv)) := by
      unfold cssState; rw [if_pos (show U64.bv 0#u64 = (0 : Fl4Spec.Word) from rfl), hflag]
    refine ⟨by first | rfl | trivial, by first | rfl | trivial, V4, ?_⟩
    rw [e]; exact J4
  · simp only [hn, ↓reduceIte, set_debug_reg_wr, bind_ok, WP.spec_ok]
    obtain ⟨V2, J2⟩ := J.dbgWrJ hpT (dbgA p debug.SS_ENABLED) (448 + 48) (by omega)
      (by rw [dbgA_val (by omega) (by unfold debug.SS_ENABLED; decide)]; unfold debug.SS_ENABLED; simp) 1#u64
    obtain ⟨V3, J3⟩ := J2.dbgWrJ hpT (dbgA p debug.SS_COUNT) (448 + 56) (by omega)
      (by rw [dbgA_val (by omega) (by unfold debug.SS_COUNT; decide)]; unfold debug.SS_COUNT; simp) n
    have e : cssState σ p.bv xp n.bv = σ := by
      unfold cssState; rw [if_neg (fun h => hn (UScalar.eq_of_val_eq (by
        have := congrArg BitVec.toNat h; simpa using this)))]
    refine ⟨by first | rfl | trivial, by first | rfl | trivial, V3, ?_⟩
    rw [e]; exact J3

set_option maxHeartbeats 8000000 in
/-- **The single-word reply tail at `J`** (ConfigureSingleStepping's, called):
FL4's `MR0`, then `reply_words` (badge, message info), then `Running`
(`JAtZ.regWrJ` three times, `JAtZ.runJ`); the spec's `reply_from_kernel` in
its own register order (`setReg_comm`), so the spec's success tail. -/
theorem JAtZ.replyWords1J (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart) (v : U64) :
    (do
      let s4 ← tcb.reply_words st (L.wr s (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v) ct 1#u64
      let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a)) ⦃ res =>
        ∀ z ∈ (specTail true ct.bv [v.bv] σ).1, JAt (L := L) arI AR res.2.1 res.2.2 z.2 ⦄ := by
  set s1 := L.wr s (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) v
  have hRW : tcb.reply_words st s1 ct 1#u64 ⦃ s3 => ∃ w : U64,
      s3 = L.wr (L.wr s1 (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
        (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w ∧
      w.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 1, 0, 0, 0⟩ ⦄ := by
    unfold tcb.reply_words
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s1 ct layout.reg.BADGE 0#u64) ?_
    rintro s2 rfl
    unfold msginfo.MessageInfo.new
    simp only [bind_ok]
    refine WP.spec_mono (Endp.set_msg_info_spec _ ct 0#u64 1#u64 (by decide)) ?_
    rintro s3 ⟨w, rfl, hw⟩
    refine ⟨w, ?_, by rw [hw]; exact msg_info_one_bv⟩
    rw [Endp.regIdx_badge, Endp.regIdx_msgInfo]
  refine WP.spec_bind hRW ?_
  rintro s3 ⟨w, rfl, hw⟩
  -- MR0
  have hX1 := reg_wr_irel J.ip (J.xtop.irelK J.ks J.buf) hct hk (Endp.mrIdx 0) (by decide) v
  obtain ⟨V1, J1⟩ := J.regWrJ hct hk (Endp.mrIdx 0) v hX1
  set x1 := setReg x (Endp.mrIdx 0) v.bv with hx1
  have hk1 : (updK σ ct.bv (.tcb x1)).kheap ct.bv = some (.tcb x1) := by simp [updK]
  -- the badge
  have hXb := badge_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hct hk1 0#u64
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V2, J2⟩ := J1.regWrJ hct hk1 Fl4Spec.badge_register 0#u64 hXb
  set x2 := setReg x1 Fl4Spec.badge_register (0#u64 : U64).bv with hx2
  have hk2 : (updK (updK σ ct.bv (.tcb x1)) ct.bv (.tcb x2)).kheap ct.bv = some (.tcb x2) := by simp [updK]
  -- the message info
  have hX3 := reg_wr_irel J2.ip (J2.xtop.irelK J2.ks J2.buf) hct hk2 Fl4Spec.msg_info_register (by decide) w
  obtain ⟨V3, J3⟩ := J2.regWrJ hct hk2 Fl4Spec.msg_info_register w hX3
  have hxC : setReg x2 Fl4Spec.msg_info_register w.bv = Endp.replyTcb x v.bv := by
    rw [hw, hx2, hx1, setReg_comm x (show Endp.mrIdx 0 ≠ Fl4Spec.badge_register by decide)]
    rfl
  rw [updK_updK, updK_updK, hxC] at J3
  have hkC : (updK σ ct.bv (.tcb (Endp.replyTcb x v.bv))).kheap ct.bv = some (.tcb (Endp.replyTcb x v.bv)) := by
    simp [updK]
  refine WP.spec_bind (J3.runJ hct hkC hrs) ?_
  rintro s4 ⟨Lst', D', J4⟩
  refine (WP.spec_ok _).2 fun z hz => ?_
  rw [specTail_restart hk hrs true v.bv] at hz
  simp only [↓reduceIte] at hz
  rw [Notif.setThreadState_eq .running hkC] at hz
  rw [Set.mem_singleton_iff.1 hz]
  exact ⟨_, _, _, _, _, _, J4⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The Suspend label at `JAt`** (as `tcb_suspendX`): the caller's restart
(`JAtZ.restartJ`), then `JAtZ.suspendJ` with the four cancel steps
(`jCancel_send`, `jCancel_ntfn`, `jCancel_reply`; `jCancel_recv` from
`recvReplyHyp_holds`). -/
theorem tcb_suspendJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (hpI : p ≠ L.idleW s) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSuspend)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (c : tcb.Ctx) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBSuspend p c blk call don slbl args ci sl
      excaps buffer := by
  have hdec : (specDec false slbl args ci sl (.Thread p) excaps buffer).run σ =
      ({(.ok (.invokeTCB (.suspend p.bv)), σ)}, False) := by
    show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    apply run_liftME_ok
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]; rfl
  have hid0 := J.ne_idle hpI
  obtain ⟨s1, σ1, x, hrc1, hst, -, -, -, hns, hid1, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  unfold TcbOKX
  rw [decode_suspend_eq arI s ar p c hstall, hrc1]
  simp only [bind_ok]
  refine WP.spec_bind (J1.suspendJ (jCancel_send arI) (jCancel_ntfn arI) (jCancel_recv arI)
    (jCancel_reply arI) hpT (fun u h => (hns u h).elim) (by rw [hid1]; exact hid0)) ?_
  rintro ⟨s2, a2⟩ ⟨-, σ', hsus, V, Ac', Lst', D', J2⟩
  refine (WP.spec_ok _).2 ?_
  have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.suspend p.bv))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
    exact mem_liftE (x := ([], σ')) (mem_bind_nd (x := ((), σ')) (by rw [hsus]; exact Set.mem_singleton _) rfl)
  exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
    J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac', Lst', D', J2⟩⟩

set_option maxHeartbeats 8000000 in
/-- **The Resume label at `JAt`** (as `tcb_resumeX`): the caller's restart
(`JAtZ.restartJ`; the slots kept, so the target's cap still in the invoked
slot; the current thread `Restart`, `CurInv` by `restart_mid`), then
XTopJointRestart's `JAtZ.restartTcbJ` with the four cancel steps and the
platform's `MIN_BUDGET` [P] (as IpcCapJ). -/
theorem tcb_resumeJ (hAT : P0.ArchTotal arI)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (x0 : U64) (hxS : IsSlot Z.th x0) (hcap : capAt (L.mem s) x0 = ok (.Thread p))
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbResume)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (c : tcb.Ctx) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBResume p c blk call don slbl args ci sl
      excaps buffer := by
  have hdec : (specDec false slbl args ci sl (.Thread p) excaps buffer).run σ =
      ({(.ok (.invokeTCB (.resume p.bv)), σ)}, False) := by
    show (Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer).run σ = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    apply run_liftME_ok
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]; rfl
  obtain ⟨s1, σ1, x, hrc1, hst, hk, hcur, -, hns, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain ⟨-, x', hk', hrun⟩ := J.curRunnable hni hct
  rw [hk] at hk'; cases hk'
  -- the slots kept by the caller's restart
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := XTopAt.restart J.xtop hcur hk hrun
    rw [hs1, WP.spec_ok] at h; exact h.2.1
  have hcap1 : capAt (L.mem s1) x0 = ok (.Thread p) := by
    rw [capAt_capV, hSS.capV hxS, ← capAt_capV]; exact hcap
  unfold TcbOKX
  rw [decode_resume_eq arI s ar p c hstall, hrc1]
  simp only [bind_ok]
  refine WP.spec_bind (J1.restartTcbJ hAT (jCancel_send arI) (jCancel_ntfn arI) (jCancel_recv arI)
    (jCancel_reply arI) (hmb ar) hpT hxS hcap1 (fun u h => hns u h)) ?_
  rintro ⟨s2, a2⟩ ⟨-, σ', hres, V, Ac', Lst', D', J2⟩
  refine (WP.spec_ok _).2 ?_
  have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.resume p.bv))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
    exact mem_liftE (x := ([], σ')) (mem_bind_nd (x := ((), σ')) (by rw [hres]; exact Set.mem_singleton _) rfl)
  exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
    J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac', Lst', D', J2⟩⟩

set_option maxHeartbeats 8000000 in
/-- **The WriteRegisters label at `JAt`** (as `tcb_write_regsX`): TcbCtl's
decode, the caller's restart (`JAtZ.restartJ`; the slots kept, so the
target's cap still in the invoked slot; `CurInv` by `restart_mid`), then
XTopJointWriteRegs' `JAtZ.writeRegsJ` (the register loops, the restart PC,
`post_modify_registers`, the optional `JAtZ.restartTcbJ`). Named, as
IpcWriteRegsJ's `writeRegsXHypJ`: the caller's buffer mapped (`hbuf`) and
the syscall arguments after the caller's restart (`hargs1`) [W, front end];
the platform's `MIN_BUDGET` [P]. -/
theorem tcb_write_regsJ (hAT : P0.ArchTotal arI)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ)
    (p : U64) (hpT : p ∈ Z.T) (x0 : U64) (hxS : IsSlot Z.th x0) (hcap : capAt (L.mem s) x0 = ok (.Thread p))
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbWriteRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hbuf : buf ≠ 0#u64 → ∃ sp, BufMap Z.B buf sp)
    (hargs1 : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s1 ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBWriteRegisters p ⟨length, buf, call, slot, extra⟩
      blk call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hctT : ct ∈ Z.T := J.thT ct (hX.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeWriteRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_write_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_write_registers
  by_cases h1 : length < 2#u64
  · simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    have : args.length < 2 := by scalar_tac
    match args, this with
    | [], _ => rfl
    | [_], _ => rfl
  simp only [h1, ↓reduceIte]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  obtain ⟨i, hi, hiv⟩ := spec_exists (U64.sub_spec (x := length) (y := 2#u64) (by scalar_tac))
  have hrl : rest.length = length.val - 2 := by simp at hlen; scalar_tac
  have hiv' : i.val = length.val - 2 := by rw [hiv.1]; rfl
  rw [ha0, ha1]; simp only [bind_ok, hi]
  have hsp : (Fl4Spec.decodeWriteRegisters (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv)) =
      (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
        (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) >>= fun _ => do
        let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
        Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation)
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
          ((rest.map UScalar.bv).take (Fl4Spec.unat y1.bv)) Fl4Spec.ArchDefaultExtraRegisters)) := by
    simp only [Fl4Spec.decodeWriteRegisters, List.map_cons, retOk_bind]
  rw [hsp]
  have hun : Fl4Spec.unat y1.bv = y1.val := by simp [Fl4Spec.unat]
  by_cases hw : i < y1
  · simp only [hw, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    rw [whenE_pos (by rw [hun, List.length_map, hrl]; have h' : i.val < y1.val := hw; omega)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [hw, ↓reduceIte, hct, bind_ok, tcb_eq_ct]
  have hy1 : y1.val ≤ rest.length := by have h' : ¬ i.val < y1.val := hw; omega
  have hwh : (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
      (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) : Fl4Spec.SEMonad Unit Unit).run σ =
      ({(.ok (), σ)}, False) := by
    rw [whenE_neg (by rw [hun, List.length_map]; omega)]; rfl
  by_cases hpc : p = ct
  · subst hpc
    simp only [decide_true, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inl
    refine ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩
    apply run_liftME_err
    rw [run_bind_ok hwh, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
      s.curThread) rfl), whenE_pos (by show p.bv = σ.curThread; rw [hcur])]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
      (Fl4Spec.NonDetE.whenE ((rest.map UScalar.bv).length < Fl4Spec.unat y1.bv)
        (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage) >>= fun _ => do
        let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
        Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation)
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
          ((rest.map UScalar.bv).take (Fl4Spec.unat y1.bv)) Fl4Spec.ArchDefaultExtraRegisters))).run σ =
      ({(.ok (.invokeTCB (.writeRegisters p.bv (Fl4Spec.testBit y0.bv 0)
        ((((y0 :: y1 :: rest).drop 2).map UScalar.bv).take y1.val) Fl4Spec.ArchDefaultExtraRegisters)), σ)},
        False) := by
    apply run_liftME_ok
    rw [run_bind_ok hwh, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
      s.curThread) rfl), whenE_neg (by show ¬ p.bv = σ.curThread; rw [hcur, bv_eq_iff']; exact hpc),
      retOk_bind, hun]
    rfl
  -- the caller's restart
  obtain ⟨s1, σ1, x, hrc1, hst, hk, -, -, hns, -, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain ⟨-, x', hk', hrun⟩ := J.curRunnable hni hct
  rw [hk] at hk'; cases hk'
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := XTopAt.restart J.xtop hcur hk hrun
    rw [hs1, WP.spec_ok] at h; exact h.2.1
  have hcap1 : capAt (L.mem s1) x0 = ok (.Thread p) := by
    rw [capAt_capV, hSS.capV hxS, ← capAt_capV]; exact hcap
  have hcur1 : σ1.curThread = ct.bv := hct1.trans hcur
  rw [hrc1]; simp only [bind_ok, lift]
  -- the arguments after the restart
  set V := (((y0 :: y1 :: rest).drop 2).map UScalar.bv).take y1.val with hV
  have hVn : V.length = y1.val := by simp [hV]; omega
  obtain ⟨sp, hbm⟩ : ∃ sp, buf ≠ 0#u64 → BufMap Z.B buf sp := by
    by_cases hb : buf = 0#u64
    · exact ⟨0, fun h => absurd hb h⟩
    · obtain ⟨sp, h⟩ := hbuf hb; exact ⟨sp, fun _ => h⟩
  have hargsV : ∀ (j : Nat) (i2 : U64), i2.val = j + 2 → j < y1.val →
      ∃ w, msg.syscall_arg st s1 ct buf i2 = ok w ∧ w.bv = V[j]! := by
    intro j i2 hi2 hj
    have hjl : j + 2 < (y0 :: y1 :: rest).length := by simp; omega
    refine ⟨(y0 :: y1 :: rest)[j + 2], hargs1 s1 hs1 i2 _ (by rw [hi2]; exact List.getElem?_eq_getElem hjl), ?_⟩
    have hjV : j < V.length := by omega
    rw [getElem!_pos V j hjV]
    simp only [hV, List.getElem_take, List.getElem_map, List.getElem_drop]
    congr 2; omega
  refine WP.spec_bind (J1.writeRegsJ hAT (jCancel_send arI) (jCancel_ntfn arI) (jCancel_recv arI)
    (jCancel_reply arI) (hmb ar) hpT hpc hcur1 hctT hxS hcap1 (fun u h => hns u h) hbm
    ((y0 &&& 1#u64) != 0#u64) y1 hVn hargsV) ?_
  rintro ⟨s2, a2⟩ ⟨-, σ', hsp, V', Ac', Lst', D', J2⟩
  refine (WP.spec_ok _).2 ?_
  have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.writeRegisters p.bv
        (Fl4Spec.testBit y0.bv 0) V Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) _).run σ1).1
    rw [invokeTcb_wr, ← and1_ne0]
    exact mem_liftE (x := ([], σ')) (mem_bind_nd (by rw [hsp]; exact Set.mem_singleton _) (Set.mem_singleton _))
  exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
    J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac', Lst', D', J2⟩⟩

set_option maxHeartbeats 8000000 in
/-- **The CopyRegisters label at `JAt`** (as `tcb_copy_regsX`): TcbCtl's
decode with the source the first extra cap's thread, the caller's restart
(`JAtZ.restartJ`, `Entered` after by `restart_mid`), the target out of the
dead set by its cap in the invoked slot (`JAtZ.undead`, the slots kept by
the restart), then XTopJointCopyRegs' `JAtZ.copyRegsJ`. Named: the
source not idle (`hidS`), the platform's `MIN_BUDGET` [P]. -/
theorem tcb_copy_regsJ (hAT : P0.ArchTotal arI)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ)
    (hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
      q ≠ L.idleW s)
    (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbCopyRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall' : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th ssl) (hsc : capV (L.mem s) (cslotAddr ssl) = .Thread p)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBCopyRegisters p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_copy_eq arI s ar p _ (hstall' p), hdec0]
  unfold tcb.decode_copy_registers tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  have htr : args = [] ∨ excaps = [] →
      (ok ((.Err (.Sys .TruncatedMessage) : core.result.Result Unit error.Exc), s, ar) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMX (L := L) (JAt (L := L) arI AR) σ blk
        call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeCopyRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) (excaps.map Prod.fst)))
        s res ⦄ := by
    intro h
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    rcases h with rfl | rfl
    · exact copy_trunc0 σ _ _
    · cases args with
      | nil => exact copy_trunc0 σ _ _
      | cons y0 rest => exact copy_trunc1 σ _ _ _
  by_cases h0 : x0 = 0#u64
  · have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact htr (Or.inr (List.eq_nil_of_length_eq_zero (by omega)))
  by_cases hl : length < 1#u64
  · simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, show ¬ (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 by
        show ¬ length >= 1#u64; scalar_tac]
    exact htr (Or.inl (List.eq_nil_of_length_eq_zero (by scalar_tac)))
  simp only [h0, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    show (⟨length, buf, call, cslotAddr ssl, extra⟩ : tcb.Ctx).length >= 1#u64 by show length >= 1#u64; scalar_tac]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args, hlen with
    | y0 :: rest, _ => exact ⟨_, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, cslotAddr ssl, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  rw [ha0]; simp only [bind_ok, thread_arg_eq]
  obtain ⟨e0, he0, hxe0, he01, ps0, hps0, hps01⟩ := hXc.get hx0' h0
  obtain ⟨erest, rfl⟩ : ∃ erest, excaps = e0 :: erest := by
    match excaps, he0 with
    | a :: r, h => simp at h; exact ⟨r, by rw [h]⟩
  have hsp : (Fl4Spec.decodeCopyRegisters (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv)
      ((e0 :: erest).map Prod.fst)) =
      ((match absCap (capV (L.mem s) x0) :: erest.map Prod.fst with
        | .threadCap q :: _ => Fl4Spec.NonDetE.returnOk q
        | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>= fun q =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.copyRegisters p.bv q (Fl4Spec.testBit y0.bv 0)
          (Fl4Spec.testBit y0.bv 1) (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3)
          Fl4Spec.ArchDefaultExtraRegisters)) := by
    rw [List.map_cons, List.map_cons, copy_spec, he01]
    rfl
  rw [hsp]
  rcases copy_src_rel (capV (L.mem s) x0) (erest.map Prod.fst) (σ := σ) with ⟨src, hsrc, hrun⟩ | ⟨hsrc, hrun⟩
  · rw [hsrc]
    simp only [hstall' src, bind_ok]
    obtain ⟨s1, σ1, x, hrc1, hst, hk, -, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    obtain ⟨-, x', hk', hrun'⟩ := J.curRunnable hni hct
    rw [hk] at hk'; cases hk'
    refine let_pair2 s ar (fun s1 a1 => do let s2 ← tcb.restart_caller st s1; tcb.copy_registers st arI s2 a1 p src y0)
      _ ?_
    rw [hrc1]; simp only [bind_ok]
    have hthr : capV (L.mem s) x0 = .Thread src := by
      revert hsrc; cases capV (L.mem s) x0 <;> simp [threadArgF]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        ((match absCap (capV (L.mem s) x0) :: erest.map Prod.fst with
          | .threadCap q :: _ => Fl4Spec.NonDetE.returnOk q
          | _ => Fl4Spec.NonDetE.throwError (.invalidCapability 1) : Fl4Spec.SEMonad Unit Fl4Spec.ObjRef) >>=
          fun q => Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.copyRegisters p.bv q (Fl4Spec.testBit y0.bv 0)
            (Fl4Spec.testBit y0.bv 1) (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3)
            Fl4Spec.ArchDefaultExtraRegisters))).run σ =
        ({(.ok (.invokeTCB (.copyRegisters p.bv src.bv (Fl4Spec.testBit y0.bv 0) (Fl4Spec.testBit y0.bv 1)
          (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3) Fl4Spec.ArchDefaultExtraRegisters)), σ)}, False) := by
      apply run_liftME_ok
      exact (run_bind_ok hrun _).trans rfl
    have hA0 : AbsSlot Z.th e0.2 := ⟨ps0, hps01, Or.inl hps0⟩
    have hxs : IsSlot Z.th x0 := by rw [hxe0]; exact hA0.isSlot
    have hsrcT : src ∈ Z.T := J.thT src (show CapValid Z.th (.Thread src) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe0, capAt_capV, hthr]))
    have hsI : src.bv ≠ σ1.idleThread := by rw [hid1]; exact J.ne_idle (hidS e0.2 src hA0 (by rw [← hxe0]; exact hthr))
    -- the slots kept by the caller's restart: the target's cap, so the target out of the dead set
    have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := by
      have h := XTopAt.restart J.xtop hcur hk hrun'
      rw [hs1, WP.spec_ok] at h; exact h.2.1
    have hcap1 : capAt (L.mem s1) (cslotAddr ssl) = ok (.Thread p) := by
      rw [capAt_capV, hSS.capV hAs.isSlot, hsc]
    have hC := J.curInv (by rw [hni.2]; simp)
    have hcs : Fl4Spec.schedulable σ.curThread σ = true := ct_schedulable hC J.act J.inv (hcur ▸ hk) hrun'
    obtain ⟨hres1, -, -, -, -⟩ := restart_mid hcur hk (hcur ▸ hcs) hni.2 hC J.off J.act J.inv
    have hEn1 : Entered σ1 := ⟨by rw [hct1, hid1]; exact hni.1, by rw [he1]; exact hres1⟩
    refine WP.spec_mono ((J1.undead hAs.isSlot hcap1 hpT).copyRegsJ hAT (jCancel_send arI) (jCancel_ntfn arI)
      (jCancel_recv arI) (jCancel_reply arI) (hmb ar) hEn1 hsrcT hpT hsI (fun h => h.2 rfl) y0) ?_
    rintro ⟨r2, s2, a2⟩ ⟨hr2, -, σ', hsp, V', Ac', Lst', D', J2⟩
    simp only at hr2; subst hr2
    have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
        ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.copyRegisters p.bv src.bv
          (Fl4Spec.testBit y0.bv 0) (Fl4Spec.testBit y0.bv 1) (Fl4Spec.testBit y0.bv 2) (Fl4Spec.testBit y0.bv 3)
          Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 := by
      show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) _).run σ1).1
      rw [invokeTcb_cr]
      exact mem_liftE (x := ([], σ')) (mem_bind_nd (by rw [hsp]; exact Set.mem_singleton _) (Set.mem_singleton _))
    exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
      J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac', Lst', D', J2⟩⟩
  · rw [hsrc]
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
    exact run_liftME_err (run_bind_error hrun _)

set_option maxHeartbeats 8000000 in
/-- **The UnbindNotification label at `JAt`** (as `tcb_unbind_ntfnX`): the
bound check; when bound, the caller's restart (`JAtZ.restartJ`, the bound
word kept: the spec's restart keeps the thread's binding), then
`JAtZ.unbindNJ`. -/
theorem tcb_unbind_ntfnJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbUnbindNotification)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (length buf : U64) (call : Bool) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBUnbindNotification p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl excaps buffer := by
  have hX := J.xtop
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  show (do
    let i ← obj.Tcb.bound_ntfn st p s
    if (i : U64).val = (0#u64).val then do
        let r ← error.illegal Unit
        ok (r, s, ar)
      else do
        let s2 ← tcb.restart_caller st s
        let s3 ← notification.unbind_notification st s2 p
        ok (core.result.Result.Ok (), s3, ar)) ⦃ r => TopPostDMX (L := L) (JAt (L := L) arI AR) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeUnbindNotification (Z := Unit) (Fl4Spec.Cap.threadCap p.bv))) s r ⦄
  rw [tcb_bound_eq]
  simp only [bind_ok, ← u64_eq_iff]
  obtain ⟨xp, hkp, hxp⟩ := hX.fin.1.1.2.1.tcb p hpT
  have hbp : xp.tcbBoundNotification = Notif.optRef (L.mem s (P1.boundA p)) := hxp.bound
  have hsp0 : (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv)).run σ =
      ((match Notif.optRef (L.mem s (P1.boundA p)) with
        | none => Fl4Spec.NonDetE.throwError .illegalOperation
        | some _ => Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit) >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.notificationControl p.bv none)).run σ := by
    simp only [Fl4Spec.decodeUnbindNotification]
    rw [lE_bind (m := Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbBoundNotification p.bv)
      (Notif.threadGet_eq _ hkp), hbp]
    generalize Notif.optRef (L.mem s (P1.boundA p)) = o
    cases o <;> rfl
  by_cases hb0 : L.mem s (P1.boundA p) = 0#u64
  · simp only [hb0, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact run_throw_bind _ _ _
  simp only [hb0, ↓reduceIte]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
      (Fl4Spec.decodeUnbindNotification (Z := Unit) (.threadCap p.bv))).run σ =
      ({(.ok (.invokeTCB (.notificationControl p.bv none)), σ)}, False) := by
    apply run_liftME_ok
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact (congrArg (fun m : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation => m.run σ) (retOk_bind () _)).trans rfl
  obtain ⟨s1, σ1, x, hrc1, hst, hk, -, he1, -, -, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  -- the bound word after the restart, through the spec (the restart keeps the binding)
  have hb1 : L.mem s1 (P1.boundA p) ≠ 0#u64 := by
    intro h1
    obtain ⟨xp1, hkp1, hxp1⟩ := J1.xtop.fin.1.1.2.1.tcb p hpT
    have hb1' : xp1.tcbBoundNotification = Notif.optRef (L.mem s1 (P1.boundA p)) := hxp1.bound
    have b1 : xp1.tcbBoundNotification = none := by rw [hb1', h1]; simp [Notif.optRef]
    have b0 : xp.tcbBoundNotification ≠ none := by rw [hbp]; simp [Notif.optRef, hb0]
    apply b0
    rw [he1, stsAct_kheap, updK_kheap] at hkp1
    by_cases hpc : p.bv = ct.bv
    · rw [hpc, Function.update_self] at hkp1
      rw [hpc, hk] at hkp
      cases hkp; cases hkp1; exact b1
    · rw [Function.update_of_ne hpc, hkp] at hkp1
      cases hkp1; exact b1
  rw [hrc1]; simp only [bind_ok]
  refine WP.spec_bind (J1.unbindNJ hpT hb1) ?_
  rintro s3 ⟨σ', hun, -, -, -, V, Ac', Lst', D', J2⟩
  refine (WP.spec_ok _).2 ?_
  have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
        (.invokeTCB (.notificationControl p.bv none))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
    exact mem_liftE (x := ([], σ')) (mem_bind_nd (x := ((), σ')) (by rw [hun]; exact Set.mem_singleton _) rfl)
  exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
    J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac', Lst', D', J2⟩⟩

set_option maxHeartbeats 8000000 in
/-- **The UnsetBreakpoint label at `JAt`** (as `tcb_unset_bpX`): the
argument by `ArgRel` [J], the caller's restart (`JAtZ.restartJ`), the two
debug words (`JAtZ.dbgWrJ`); the spec keeps its state. -/
theorem tcb_unset_bpJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .unsetBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 1)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBUnsetBreakpoint p ⟨length, buf, call, slot, extra⟩
      blk call don slbl args ci sl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [decode_unset_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  rw [hbp]; simp only [bind_ok]; rw [check_bp_eq]
  simp only [bind_ok]
  have hsp : (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv).run σ =
      (Fl4Spec.fl4CheckBpNum (Z := Unit) bp.bv >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.unsetBreakpoint p.bv bp.bv)).run σ := by
    unfold Fl4Spec.decodeFl4UnsetBreakpoint
    exact run_bind_ok hbs _
  by_cases hb : bp ≥ 4#u64
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, bp_err⟩, hJ0⟩)
    apply run_liftME_err
    rw [hsp]
    exact run_bind_error (by rw [checkBp_run, if_pos hb]) _
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨s1, σ1, x, hrc1, hst1, -, -, -, -, -, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    rw [hrc1]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4UnsetBreakpoint (Z := Unit) buffer p.bv)).run σ =
        ({(.ok (.invokeFl4TCB (.unsetBreakpoint p.bv bp.bv)), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp, run_bind_ok (by rw [checkBp_run, if_neg hb])]
      rfl
    have hbpv : bp.val < 4 := by
      have : ¬ (4 ≤ bp.val) := fun h => hb (by scalar_tac)
      omega
    have hpf := (J1.ip.e.tcb p hpT).fits
    refine WP.spec_bind (unset_bp_wr s1 p bp hbpv) ?_
    rintro s2 ⟨v, rfl⟩
    obtain ⟨V2, J2⟩ := J1.dbgWrJ hpT (dbgA p 5#u64) (448 + 40) (by omega)
      (by rw [dbgA_val (by omega) (by decide)]; simp) v
    obtain ⟨V3, J3⟩ := J2.dbgWrJ hpT (dbgA p bp) (448 + 8 * bp.val) (by omega)
      (by rw [dbgA_val (i := bp) (by omega) (by omega)]; omega) 0#u64
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ1), rfl,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1, J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1,
        J3.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D1, J3⟩⟩)

set_option maxHeartbeats 8000000 in
/-- **The SetBreakpoint label at `JAt`** (as `tcb_set_bpX`): FL4's checks
against the spec's (the five arguments by `ArgRel` [J]), the caller's restart
(`JAtZ.restartJ`), the two debug words (`JAtZ.dbgWrJ`); the spec keeps its
state. -/
theorem tcb_set_bpJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .setBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 5)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBSetBreakpoint p ⟨length, buf, call, slot, extra⟩
      blk call don slbl args ci sl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [decode_setbp_eq arI s ar p _ hstall, hdec0]
  have hc : (⟨length, buf, call, slot, extra⟩ : tcb.Ctx).buf = buf := rfl
  obtain ⟨bp, h0, g0⟩ := arg_rel hA hct hcur _ hc 0#u64 (by decide)
  obtain ⟨vaddr, h1, g1⟩ := arg_rel hA hct hcur _ hc 1#u64 (by decide)
  obtain ⟨ty, h2, g2⟩ := arg_rel hA hct hcur _ hc 2#u64 (by decide)
  obtain ⟨size, h3, g3⟩ := arg_rel hA hct hcur _ hc 3#u64 (by decide)
  obtain ⟨rw, h4, g4⟩ := arg_rel hA hct hcur _ hc 4#u64 (by decide)
  rw [set_bp_checked_eq s p _ h0 h1 h2 h3 h4]
  have hsp := set_bp_spec_run σ buffer p.bv g0 g1 g2 g3 g4
  have hrel := bpErr_rel bp vaddr ty size rw
  cases hF : bpErrF bp vaddr ty size rw with
  | some e =>
    cases hS : bpErrS bp vaddr.bv ty.bv size.bv rw.bv with
    | none => rw [hF, hS] at hrel; exact hrel.elim
    | some e' =>
      rw [hF, hS] at hrel
      dsimp only at hrel
      dsimp only
      simp only [bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨e, rfl, rfl, ⟨e', ?_, hrel⟩, hJ0⟩)
      apply run_liftME_err
      rw [hsp, hS]
  | none =>
    cases hS : bpErrS bp vaddr.bv ty.bv size.bv rw.bv with
    | some e' => rw [hF, hS] at hrel; exact hrel.elim
    | none =>
    have hbpv := bpErrF_bp hF
    simp only
    obtain ⟨s1, σ1, x, hrc1, hst1, -, -, -, -, -, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    rw [hrc1]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetBreakpoint (Z := Unit) buffer p.bv)).run σ =
        ({(.ok (.invokeFl4TCB (.setBreakpoint p.bv bp.bv vaddr.bv ty.bv size.bv rw.bv)), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp, hS]
    have hpf := (J1.ip.e.tcb p hpT).fits
    have hin : (do
        let s2 ← debug.set_breakpoint st s1 p bp vaddr ty size rw
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2)) ⦃ x =>
          ∃ v, x = (.Ok (), L.wr (L.wr s1 (dbgA p bp) vaddr) (dbgA p 5#u64) v) ⦄ :=
      WP.spec_bind (set_bp_wr (st := st) s1 p bp vaddr ty size rw) (fun s2 ⟨v, h⟩ => (WP.spec_ok _).2 ⟨v, by rw [h]⟩)
    refine WP.spec_bind hin ?_
    rintro x ⟨v, rfl⟩
    obtain ⟨V2, J2⟩ := J1.dbgWrJ hpT (dbgA p bp) (448 + 8 * bp.val) (by omega)
      (by rw [dbgA_val (i := bp) (by omega) (by omega)]; omega) vaddr
    obtain ⟨V3, J3⟩ := J2.dbgWrJ hpT (dbgA p 5#u64) (448 + 40) (by omega)
      (by rw [dbgA_val (by omega) (by decide)]; simp) v
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ1), rfl,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1, J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1,
        J3.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D1, J3⟩⟩)

set_option maxHeartbeats 8000000 in
/-- **The SetTLSBase label at `JAt`** (as `tcb_set_tlsX`): the caller's
restart (`JAtZ.restartJ`), the `TLS_BASE` register (`JAtZ.regWrJ`), and for
the current thread `reschedule_required` as a scheduler step
(`JAtZ.schedJ`; `ActReady` from the `JAtZ` after the write, `Sched.Inv.actReady`); the
current-thread word outside the objects [P]. -/
theorem tcb_set_tlsJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ)
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetTLSBase)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcw : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBSetTLSBase p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hX := J.xtop
  have hP := hX.rel.1
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (hX.curTcb hcur).1
  have hact := J.kern.act
  have hpT : p ∈ Z.T := J.thT p hp
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : (specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer) =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetTlsBase (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val, lbl_tcbUnbindNotification_val, lbl_tcbSetBreakpoint_val,
    lbl_tcbGetBreakpoint_val, lbl_tcbUnsetBreakpoint_val, lbl_tcbConfigureSingleStepping_val,
    lbl_tcbSetTLSBase_val, lbl_tcbSetEPTRoot_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  refine let_pair_spec s ar (fun s1 => tcb.decode_set_tls_base st s1 p ⟨length, buf, call, slot, extra⟩) _ ?_
  unfold tcb.decode_set_tls_base
  by_cases h1 : length < 1#u64
  · simp only [if_pos h1, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inl
    refine ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩
    apply run_liftME_err
    unfold Fl4Spec.decodeSetTlsBase
    rw [whenE_pos (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [if_neg h1]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
      (Fl4Spec.decodeSetTlsBase (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv))).run σ =
      ({(.ok (.invokeTCB (.setTLSBase p.bv y0.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeSetTlsBase
    rw [whenE_neg (by simp), retOk_bind]
    show (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.setTLSBase p.bv (Fl4Spec.ucast 64 y0.bv)) :
      Fl4Spec.SEMonad Unit _).run σ = _
    rw [ucast64_self]; rfl
  rw [harg]; simp only [bind_ok]
  obtain ⟨s1, σ1, x0, hrc1, hst1, -, -, -, -, -, hcur1', hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have hc1 := set_thread_state_cases (L := L) s ct sched.TS_RESTART
  rw [hs1, WP.spec_ok] at hc1
  rw [hrc1]; simp only [bind_ok]
  obtain ⟨w, hw, hwb⟩ := sanitise_tls y0
  rw [hw]; simp only [bind_ok, set_reg_tls_eq]
  -- the current thread is unchanged
  have hctv : L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct := by
    have := cur_thread_spec' (L := L) s; rw [hct, WP.spec_ok] at this; exact this.symm
  have hpf := hP.fits p _ hp
  have hcf := hP.fits ct _ htcb
  have hpa := hP.align p _ hp
  have hca := hP.align ct _ htcb
  simp only [objSize] at hpf hcf
  have hstv : (stA ct).val = ct.val + 3328 := by
    rw [stA_eq, wordOf_val (by simp; omega)]; simp
  have hcs2 : sched.cur_thread st (L.wr s1 (tlsA p) w) = ok ct := by
    rw [cur_thread_eq]
    simp only [P1.nodeAt_wr, L.cpu_wr]
    have hcwA : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := hcw.1
    have hn1 : L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD = L.nodeAt s (L.cpu s) layout.node.CUR_THREAD := by
      rcases hc1 with rfl | rfl <;> simp
    rw [hn1, L.mem_wr_ne (by unfold P1.Aligned; rw [tlsA_val (by omega)]; omega) hcwA
      (fun e => out_ne hcw hp (w := tlsA p) (by rw [tlsA_val (by omega)]; omega) e)]
    rcases hc1 with rfl | rfl
    · rw [L.mem_wr_ne (by unfold P1.Aligned; rw [hstv]; omega) hcwA
        (fun e => out_ne hcw htcb (by rw [hstv]; omega) e), hctv]
    · rw [L.mem_wr_ne hact.1 hcwA (fun e => cur_ne_action s e.symm),
        L.mem_wr_ne (by unfold P1.Aligned; rw [hstv]; omega) hcwA
        (fun e => out_ne hcw htcb (by rw [hstv]; omega) e), hctv]
  rw [hcs2]; simp only [bind_ok, obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]
  -- the spec: the target's TCB, its register at `J`
  have hcur1 : σ1.curThread = ct.bv := by rw [hcur1', hcur]
  obtain ⟨x, hkx, -⟩ := J1.xtop.fin.1.1.2.1.tcb p hpT
  have htl : tlsA p = regA p (regIdx Fl4Spec.tlsBaseRegister) := by
    unfold tlsA regA layout.tcb.REGS; rfl
  have hXr := reg_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hpT hkx Fl4Spec.tlsBaseRegister (by decide) w
  obtain ⟨V2, J2⟩ := J1.regWrJ hpT hkx Fl4Spec.tlsBaseRegister w hXr
  rw [← htl] at J2
  by_cases hpc : p = ct
  · subst hpc
    simp only [decide_true, ↓reduceIte]
    have hA2 : Notif.ActReady _ := J2.inv.actReady
    obtain ⟨σ', hres, hK', hdl', hds'⟩ := rescheduleRequired_k hA2
    have hS := J2.xtop.fin.1.1.1
    have hN := J2.xtop.fin.1.1.2.2.1
    obtain ⟨s3, hrun3, ⟨σ3, he3, -, -, -, -⟩, hw⟩ := spec_exists (WP.spec_and
      (Sched.reschedule_required_refines _ _ hN hS hA2) (Sched.reschedule_required_sfootI hS))
    rw [hrun3]; simp only [bind_ok]
    rw [hres] at he3
    have e3 : σ3 = σ' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he3))).2.symm
    subst σ3
    obtain ⟨Ac3, Lst3, D3, J3⟩ := J2.schedJ (schedStep_resched hA2 hrun3 hres hK' hdl' hds')
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ'), ?_,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1, J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1,
        J3.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac3, Lst3, D3, J3⟩⟩)
    refine invoke_tls_mem (y := ((), σ')) hkx y0.bv ?_ blk call don
    rw [← hwb, hcur1]
    simp only [Fl4Spec.NonDet.when, if_pos trivial]
    rw [hres]; rfl
  · have hne : decide (p = ct) = false := by simp [hpc]
    rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], _), ?_,
      ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1, J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1,
        J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D1, J2⟩⟩)
    refine invoke_tls_mem (y := ((), Notif.updK σ1 p.bv (.tcb (Notif.setReg x Fl4Spec.tlsBaseRegister w.bv))))
      hkx y0.bv ?_ blk call don
    have : ¬ p.bv = σ1.curThread := fun e => hpc (UScalar.eq_of_val_eq (by
      rw [hcur1] at e; have := congrArg BitVec.toNat e; simpa using this))
    rw [← hwb]
    simp only [Fl4Spec.NonDet.when, if_neg this]
    exact Set.mem_singleton _

set_option maxHeartbeats 8000000 in
/-- **The ConfigureSingleStepping label at `JAt`** (as `tcb_single_stepX`):
the arguments by `ArgRel` [J], the caller's restart (`JAtZ.restartJ`),
`JAtZ.cssJ`, then the data tail of `[0]`: `XTop`'s facts by
`nodata_tail_xtop`/`data_tail_xtop`, `JAt` by `JAtZ.runJ` /
`JAtZ.replyWords1J` on the same program (the spec's tail a singleton). -/
theorem tcb_single_stepJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .configureSingleStepping)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 2)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKRX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBConfigureSingleStepping p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xc, hkc⟩ := hX.curTcb hcur
  have hpT : p ∈ Z.T := J.thT p hp
  have hctT : ct ∈ Z.T := J.thT ct htcb
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKRX
  rw [decode_step_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  obtain ⟨n, hn, hns⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 1#u64 (by decide)
  unfold tcb.decode_configure_single_stepping
  rw [hct]; simp only [bind_ok]; rw [hbp]; simp only [bind_ok]; rw [hn]; simp only [bind_ok]
  obtain ⟨s1, σ1, x0, hrc1, hst1, hk0, -, hσ1, -, -, hcu1, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  rw [hkc] at hk0; cases hk0
  have hkc1 : σ1.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
    rw [hσ1, Notif.stsAct_kheap]; simp [Notif.updK]
  rw [hrc1]; simp only [bind_ok]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
      (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv)).run σ =
      ({(.ok (.invokeFl4TCB (.configureSingleStepping p.bv bp.bv n.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeFl4ConfigureSingleStepping
    rw [run_bind_ok (show (Fl4Spec.fl4Arg (Z := Unit) buffer 0).run σ = _ from hbs),
      run_bind_ok (show (Fl4Spec.fl4Arg (Z := Unit) buffer 1).run σ = _ from hns)]
    rfl
  obtain ⟨xp, hkp, -⟩ := J1.xtop.fin.1.1.2.1.tcb p hpT
  refine WP.spec_bind (J1.cssJ hpT hkp bp n) ?_
  rintro ⟨consumed, s2, a2⟩ ⟨hcons, ha2, V2, J2⟩
  simp only at hcons ha2 J2
  subst hcons ha2
  set Z2 : XSets := Z.mv Z.G V2 with hZ2
  have hX2 := J2.xtop
  obtain ⟨xy, hky, hrsy⟩ := css_tcb hkp hkc1 n.bv
  have hcurY : ct.bv = (cssState σ1 p.bv xp n.bv).curThread := by
    unfold cssState; split <;> (show ct.bv = σ1.curThread; rw [hcu1, hcur])
  have htcb2 : Z2.th ct = some .tcb := htcb
  have hact2 : OutsideObjects Z2.th (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) := J2.kern.act
  have hy := css_mem (bp := bp.bv) hkp n.bv
  have hy' : (.ok [0], cssState σ1 p.bv xp n.bv) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
      (.invokeFl4TCB (.configureSingleStepping p.bv bp.bv n.bv))).run σ1).1 := hy
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hJt : (do
        let s5 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2)) ⦃ res =>
          ∀ z ∈ (specTail false ct.bv [0] (cssState σ1 p.bv xp n.bv)).1, JAt (L := L) arI AR res.2.1 res.2.2 z.2 ⦄ := by
      refine WP.spec_bind (J2.runJ hctT hky (by rw [hrsy])) ?_
      rintro s5 ⟨Lst', D', J5⟩
      refine (WP.spec_ok _).2 fun z hz => ?_
      rw [specTail_restart hky (by rw [hrsy]) false 0] at hz
      simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rw [Notif.setThreadState_eq .running hky] at hz
      rw [Set.mem_singleton_iff.1 hz]
      exact ⟨_, _, _, _, _, _, J5⟩
    refine WP.spec_mono (WP.spec_and (nodata_tail_xtop hX2 hcurY hky (by rw [hrsy]) hact2 [0]) hJt) ?_
    rintro res ⟨⟨hres, hne, z, hz, hRT, -⟩, hJ5⟩
    exact Or.inr ⟨hres, hne, _, DecOut.of_eq hdec, σ1, hst1, [0], _, hy', z, hz, hRT, hJ5 z hz⟩
  · simp only [↓reduceIte]
    refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s2 true ct L.total) ?_
    rintro bf -
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hI0 : Vs.RInv (L := L) Z2.th Z2.P Z2.L4 Z2.L3 Z2.L2 Z2.L1 Z2.N Z2.T Z2.C Z2.E Z2.R Z2.B Z2.c AR Z2.G s2 a2
        (MrS (cssState σ1 p.bv xp n.bv) ct.bv xy (Endp.ipcBufOf true xy) []) := by
      rw [MrS_nil hky]; exact hX2.toRInv
    have tail : (do
        let (len, s3) ← msg.set_mr st s2 ct bf 0#u64 0#u64
        let s4 ← tcb.reply_words st s3 ct len
        let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2)) ⦃ res =>
          TopPostRMX (L := L) (JAt (L := L) arI AR) σ blk true don (Fl4Spec.NonDetE.liftME
            Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv))
            ct s res ⦄ := by
      have hset : msg.set_mr st s2 ct bf 0#u64 0#u64 ⦃ r =>
          r = (1#u64, L.wr s2 (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) 0#u64) ⦄ := by
        unfold msg.set_mr
        have h4 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by unfold msg.N_MSG_REGISTERS; decide
        simp only [h4, ↓reduceIte]
        refine WP.spec_bind (Endp.msg_register_spec 0#u64 (by decide)) ?_
        rintro r0 rfl
        refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ ct _ 0#u64) ?_
        rintro s2' rfl
        simp only [lift, bind_ok, WP.spec_ok]
        rfl
      refine WP.spec_bind (WP.spec_and (setmr_reg_inv _ ct htcb2 hcurY xy _ bf s2 a2 [] hI0 0#u64 rfl (by decide)
        0#u64) hset) ?_
      rintro ⟨len, s3⟩ ⟨⟨hlen, hI3, hk3, hc3⟩, he3⟩
      simp only [Prod.mk.injEq] at hlen hI3 hk3 hc3 he3
      obtain ⟨rfl, rfl⟩ := he3
      refine WP.spec_mono (WP.spec_and (data_tail_xtop hX2 hcurY hky (by rw [hrsy]) hact2 hI3 hk3 hc3 (by decide)
        (fun _ _ z hz => by simp [Endp.mrPairs] at hz) 1#u64
        (by cases Endp.ipcBufOf true xy <;> simp [mrLen]) (by decide))
        (J2.replyWords1J hctT hky (by rw [hrsy]) 0#u64)) ?_
      rintro res ⟨⟨hres, hne, z, hz, hRT, -⟩, hJ5⟩
      exact Or.inr ⟨hres, hne, _, DecOut.of_eq hdec, σ1, hst1, [0], _, hy', z, hz, hRT, hJ5 z hz⟩
    split <;> first | exact tail | (split <;> exact tail)

variable {arI} in
/-- **`FlagsRel` across the caller's restart**: `set_thread_state ct Restart`
writes the caller's state word (offset 3328) and maybe the current core's
scheduler-action word (outside the objects, `JKern.act`), no flags word
(offset 3456 of a TCB of `T`, the TCBs disjoint); the spec changes the
caller's state only. -/
theorem JAtZ.flagsRestart {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hFl : FlagsRel Z.T (L.mem s) σ)
    {ct : U64} (hth : Z.th ct = some .tcb) {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x))
    {s1 : S} (h1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1) :
    FlagsRel Z.T (L.mem s1) (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) := by
  have hc := set_thread_state_cases (st := st) s ct sched.TS_RESTART
  rw [h1, WP.spec_ok] at hc
  have hPl := J.xtop.rel.1
  have hctT := J.thT ct hth
  have hta : P1.TcbAddr ct := J.ip.e.tcb ct hctT
  have hstv : (stA ct).val = ct.val + 3328 := stA_val hPl hth
  have hal_st : P1.Aligned (stA ct) := by unfold P1.Aligned; rw [hstv]; have := hta.align; omega
  have hact := J.kern.act
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  refine FlagsRel.frame hFl (fun t ht => ?_) (fun q y hq => ?_)
  · have htt : P1.TcbAddr t := J.ip.e.tcb t ht
    have htth : Z.th t = some .tcb := (hJ.tcb t).2 (J.zH.1 t ht)
    have hfv : (tFlagsWA t).val = t.val + 3456 := Notif.tfield_val htt (by decide)
    have hfa : P1.Aligned (tFlagsWA t) := P1.field_aligned htt (by decide) (by decide)
    have n1 : (tFlagsWA t).val ≠ (stA ct).val := by
      rw [hfv, hstv]
      by_cases e : t = ct
      · subst e; omega
      · have := hPl.disj t ct .tcb .tcb htth hth e
        simp only [objSize] at this; omega
    have n2 : (tFlagsWA t).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val := by
      intro e
      exact hact.2 t .tcb htth ⟨by omega, by simp only [objSize]; omega⟩
    rcases hc with rfl | rfl
    · exact L.mem_wr_ne hal_st hfa (Ne.symm n1)
    · rw [L.mem_wr_ne hact.1 hfa (Ne.symm n2)]; exact L.mem_wr_ne hal_st hfa (Ne.symm n1)
  · rw [Notif.stsAct_kheap]
    by_cases e : q = ct.bv
    · subst e; rw [hk] at hq; cases hq
      exact ⟨{ x with tcbState := .restart }, by simp [Notif.updK], rfl⟩
    · exact ⟨y, by simp [Notif.updK, e, hq], rfl⟩

set_option maxHeartbeats 16000000 in
/-- **The SetFlags label at `JAt`** (as `tcb_set_flagsX`): the caller's
restart (`JAtZ.restartJ`), FL4's flags read (`FlagsRel` at the entry state
[J], across the restart by `JAtZ.flagsRestart`) and write with the spec's `set_flags` (`JAtZ.flagsWrJ`), the FPU
release when the FPU is disabled (`JAtZ.fpuReleaseJ'`, `ARKeep` [P]), then
the data tail of the new flags word (`XTop`'s facts by the XTop tails, `JAt`
by `JAtZ.runJ` / `JAtZ.replyWords1J`). -/
theorem tcb_set_flagsJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ)
    (hFl : FlagsRel Z.T (L.mem s) σ)
    (p : U64) (hp : Z.th p = some .tcb) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetFlags)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (hK : ARKeep arI AR)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKRX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBSetFlags p ⟨length, buf, call, slot, extra⟩
      blk call don slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xc, hkc⟩ := hX.curTcb hcur
  have hpT : p ∈ Z.T := J.thT p hp
  have hctT : ct ∈ Z.T := J.thT ct htcb
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  unfold TcbOKRX
  rw [decode_flags_eq arI s ar p _ hstall, setFlags_dec slbl hlbl]
  by_cases h1 : length < 2#u64
  · unfold tcb.decode_set_flags
    simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage,
      setFlags_trunc σ p.bv _ (by rw [List.length_map, ← hlen]; scalar_tac), Or.inl trivial⟩, hJ0⟩)
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  obtain ⟨s1, σ1, x0, hrc1, hst1, hk0, -, hσ1, -, -, hcu1, hss1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  rw [hkc] at hk0; cases hk0
  have hX1 := J1.xtop
  have hFl1 : FlagsRel Z.T (L.mem s1) σ1 := by rw [hσ1]; exact J.flagsRestart hFl htcb hkc hss1
  have hkc1 : σ1.kheap ct.bv = some (.tcb { xc with tcbState := .restart }) := by
    rw [hσ1, Notif.stsAct_kheap]; simp [Notif.updK]
  have hcurY1 : σ1.curThread = ct.bv := by rw [hcu1, hcur]
  have hdec := DecOut.of_eq (setFlags_ok σ p.bv y0.bv y1.bv (rest.map UScalar.bv))
  unfold tcb.decode_set_flags
  simp only [h1, ↓reduceIte]
  rw [hct]; simp only [bind_ok]; rw [ha0]; simp only [bind_ok]; rw [ha1]; simp only [bind_ok]
  rw [hrc1]; simp only [bind_ok]
  rw [flags_eq]; simp only [bind_ok, lift, set_flags_eq]
  -- the flags, both sides
  obtain ⟨xp, hkp, hfp⟩ := hFl1 p hpT
  set f := L.mem s1 (tFlagsWA p)
  set f2 := (f &&& ~~~y0) ||| (y1 &&& fl4_abi.consts.tcb_flag.MASK) with hf2
  set nf : Fl4Spec.TcbFlags := xp.tcbFlags \ Fl4Spec.wordToTcbFlags y0.bv ∪ Fl4Spec.wordToTcbFlags y1.bv with hnf
  have hW2 : Fl4Spec.wordToTcbFlags f2.bv = nf := by
    rw [hnf, ← hfp, hf2, flags_mask_eq, UScalar.bv_or, UScalar.bv_and, UScalar.bv_and, UScalar.bv_not]
    exact flags_new _ _ _
  obtain ⟨V2, J2⟩ := J1.flagsWrJ hpT hkp f2 nf
  set s2 := L.wr s1 (core.num.U64.wrapping_add p 3456#u64) f2
  set σ2 := Notif.updK σ1 p.bv (.tcb { xp with tcbFlags := nf })
  have hts : Fl4Spec.setFlags (Z := Unit) p.bv nf σ1 = ({((), σ2)}, False) := Notif.threadSet_eq _ hkp
  have hcur2 : σ2.curThread = ct.bv := hcurY1
  have hkc2 : ∃ y, σ2.kheap ct.bv = some (.tcb y) ∧ y.tcbState = .restart := by
    by_cases e : ct.bv = p.bv
    · rw [e] at hkc1 ⊢
      have e2 := Fl4Spec.KernelObject.tcb.inj (Option.some.inj (hkp.symm.trans hkc1))
      exact ⟨{ xp with tcbFlags := nf }, by simp [σ2, Notif.updK], by rw [e2]⟩
    · exact ⟨{ xc with tcbState := .restart }, by simp [σ2, Notif.updK, Function.update_of_ne e, hkc1], rfl⟩
  have hfpu : ((f2 &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) != 0#u64) = true ↔
      Fl4Spec.TcbFlag.fpuDisabled ∈ nf := by
    rw [← hW2, w2f_mem, ← and1_ne]
    have key : ∀ x : U64, (x &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) = 0#u64 ↔ x.bv &&& 1 = 0 := by
      intro x; rw [← bv_eq_iff']
      show UScalar.bv (x &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) = UScalar.bv 0#u64 ↔ _
      rw [UScalar.bv_and]; unfold fl4_abi.consts.tcb_flag.FPU_DISABLED; rfl
    simp only [bne_iff_ne, ne_eq, key]
  -- the tail, from the spec's state after the FPU step
  have tail : ∀ (a1 : A) (σ3 : Fl4Spec.State Unit) (Z3 : XSets) (Ac3 : Set U64) (Lst3 : U64 → List U64)
      (D3 : Set U64),
      ((), σ3) ∈ (Fl4Spec.NonDet.when (Fl4Spec.TcbFlag.fpuDisabled ∈ nf) (Fl4Spec.fpuRelease (Z := Unit) p.bv)
        σ2).1 → JAtZ (L := L) arI AR Z3 H Cs Ac3 Lst3 D3 s2 a1 σ3 → Z3.th = Z.th → σ3.curThread = ct.bv →
      (∃ y, σ3.kheap ct.bv = some (.tcb y) ∧ y.tcbState = .restart) →
      (if call = true then (do
        let buf ← msg.lookup_ipc_buffer st s2 true ct
        let (len, s3) ← msg.set_mr st s2 ct buf 0#u64 f2
        let s4 ← tcb.reply_words st s3 ct len
        let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a1))
      else (do
        let s3 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a1))) ⦃ res =>
        TopPostRMX (L := L) (JAt (L := L) arI AR) σ blk call don (Fl4Spec.NonDetE.liftME
          Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4SetFlags (Z := Unit)
            ((y0 :: y1 :: rest).map UScalar.bv) p.bv)) ct s res ⦄ := by
    intro a1 σ3 Z3 Ac3 Lst3 D3 h3 J3 hth3 hcur3 ⟨y3, hk3, hrs3⟩
    have hX3 := J3.xtop
    have hmem : (.ok [f2.bv], σ3) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
        (.invokeFl4TCB (.setFlags p.bv y0.bv y1.bv))).run σ1).1 := by
      show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
      refine mem_liftE (x := ([f2.bv], σ3)) ?_
      show ([f2.bv], σ3) ∈ ((do
        let flags ← Fl4Spec.threadGet (Z := Unit) Fl4Spec.Tcb.tcbFlags p.bv
        let newFlags ← pure (flags \ Fl4Spec.wordToTcbFlags y0.bv ∪ Fl4Spec.wordToTcbFlags y1.bv)
        Fl4Spec.setFlags p.bv newFlags
        Fl4Spec.NonDet.when (Fl4Spec.TcbFlag.fpuDisabled ∈ newFlags) (Fl4Spec.fpuRelease p.bv)
        let w ← Fl4Spec.NonDet.select {w | Fl4Spec.wordToTcbFlags w = newFlags}
        return [w]) σ1).1
      rw [Notif.nd_bind_one (Notif.threadGet_eq _ hkp), Notif.nd_pure_bind', Notif.nd_bind_one hts]
      exact mem_bind_nd (x := ((), σ3)) (by convert h3) (mem_bind_nd (x := (f2.bv, σ3)) (y := ([f2.bv], σ3)) ⟨hW2, rfl⟩
        (Set.mem_singleton _))
    have hcurY : ct.bv = σ3.curThread := hcur3.symm
    have htcb3 : Z3.th ct = some .tcb := by rw [hth3]; exact htcb
    have hact3 : OutsideObjects Z3.th (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) := J3.kern.act
    have hctT3 : ct ∈ Z3.T := J3.thT ct htcb3
    cases call
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hJt : (do
          let s5 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a1)) ⦃ res =>
            ∀ z ∈ (specTail false ct.bv [f2.bv] σ3).1, JAt (L := L) arI AR res.2.1 res.2.2 z.2 ⦄ := by
        refine WP.spec_bind (J3.runJ hctT3 hk3 hrs3) ?_
        rintro s5 ⟨Lst', D', J5⟩
        refine (WP.spec_ok _).2 fun z hz => ?_
        rw [specTail_restart hk3 hrs3 false f2.bv] at hz
        simp only [Bool.false_eq_true, ↓reduceIte] at hz
        rw [Notif.setThreadState_eq .running hk3] at hz
        rw [Set.mem_singleton_iff.1 hz]
        exact ⟨_, _, _, _, _, _, J5⟩
      refine WP.spec_mono (WP.spec_and (nodata_tail_xtop hX3 hcurY hk3 hrs3 hact3 [f2.bv]) hJt) ?_
      rintro res ⟨⟨hres, hne, z, hz, hRT, -⟩, hJ5⟩
      exact Or.inr ⟨hres, hne, _, hdec, σ1, hst1, [f2.bv], σ3, hmem, z, hz, hRT, hJ5 z hz⟩
    · simp only [↓reduceIte]
      refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s2 true ct L.total) ?_
      rintro bf -
      have hI0 : Vs.RInv (L := L) Z3.th Z3.P Z3.L4 Z3.L3 Z3.L2 Z3.L1 Z3.N Z3.T Z3.C Z3.E Z3.R Z3.B Z3.c AR Z3.G s2 a1
          (MrS σ3 ct.bv y3 (Endp.ipcBufOf true y3) []) := by
        rw [MrS_nil hk3]; exact hX3.toRInv
      have hset : msg.set_mr st s2 ct bf 0#u64 f2 ⦃ r =>
          r = (1#u64, L.wr s2 (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) f2) ⦄ := by
        unfold msg.set_mr
        have h4 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by unfold msg.N_MSG_REGISTERS; decide
        simp only [h4, ↓reduceIte]
        refine WP.spec_bind (Endp.msg_register_spec 0#u64 (by decide)) ?_
        rintro r0 rfl
        refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ ct _ f2) ?_
        rintro s2' rfl
        simp only [lift, bind_ok, WP.spec_ok]
        rfl
      refine WP.spec_bind (WP.spec_and (setmr_reg_inv _ ct htcb3 hcurY y3 _ bf s2 a1 [] hI0 0#u64 rfl (by decide) f2)
        hset) ?_
      rintro ⟨len, s3⟩ ⟨⟨hlen, hI3, hk3', hc3'⟩, he3⟩
      simp only [Prod.mk.injEq] at hlen hI3 hk3' hc3' he3
      obtain ⟨rfl, rfl⟩ := he3
      refine WP.spec_mono (WP.spec_and (data_tail_xtop hX3 hcurY hk3 hrs3 hact3 hI3 hk3' hc3'
        (by simp [Fl4Spec.msgMaxLength]) (fun _ _ z hz => by simp [Endp.mrPairs] at hz) 1#u64
        (by cases Endp.ipcBufOf true y3 <;> simp [mrLen]) (by decide))
        (J3.replyWords1J hctT3 hk3 hrs3 f2)) ?_
      rintro res ⟨⟨hres, hne, z, hz, hRT, -⟩, hJ5⟩
      exact Or.inr ⟨hres, hne, _, hdec, σ1, hst1, [f2.bv], σ3, hmem, z, hz, hRT, hJ5 z hz⟩
  by_cases hF : ((f2 &&& fl4_abi.consts.tcb_flag.FPU_DISABLED) != 0#u64) = true
  · simp only [hF, ↓reduceIte]
    refine WP.spec_bind (J2.fpuReleaseJ' hK hpT) ?_
    rintro a1 ⟨σ3, h3, hc3, hst3, V3, J3⟩
    obtain ⟨y2, hky2, hrs2⟩ := hkc2
    obtain ⟨y3, hky3, hrs3⟩ := hst3 _ y2 hky2
    refine tail a1 σ3 _ _ _ _ ?_ J3 rfl (by rw [hc3]; exact hcur2) ⟨y3, hky3, by rw [hrs3, hrs2]⟩
    unfold Fl4Spec.NonDet.when; rw [if_pos (hfpu.1 hF)]; exact h3
  · simp only [Bool.not_eq_true] at hF
    simp only [hF, Bool.false_eq_true, ↓reduceIte]
    refine tail ar σ2 _ _ _ _ ?_ J2 rfl hcur2 hkc2
    unfold Fl4Spec.NonDet.when
    rw [if_neg (fun h => by have := hfpu.2 h; rw [hF] at this; cases this)]
    exact Set.mem_singleton _


set_option maxHeartbeats 8000000 in
/-- **The BindNotification label at `JAt`** (as `tcb_bind_ntfnX`): the decode's
checks at the start's `JAtZ` (the notification cap's object among the
notifications by `JAtZ.capN`), then the caller's restart (`JAtZ.restartJ`, the
slots kept: `restart_dstate`) and XTopJointTcbMisc's `JAtZ.bindNJ` (the thread
and the notification covered by the invoked thread cap and the extra cap). -/
theorem tcb_bind_ntfnJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbBindNotification)
    (length buf : U64)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    {xT : U64} (hxT : IsSlot Z.th xT) (hcT : capV (L.mem s) xT = .Thread p)
    (call : Bool) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBBindNotification p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl args ci sl excaps buffer := by
  have hX := J.xtop
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hcapN : x0 ≠ 0#u64 → ∀ q b w r, capV (L.mem s) x0 = .Notification q b w r → q ∈ Z.N := by
    intro hx q b w r hc
    obtain ⟨e, -, ex, -, ps, hps, he⟩ := hXc.get (show [x0, x1, x2][0]? = some x0 from rfl) hx
    exact (J.capN ⟨x0, b, w, r, by rw [ex]; exact AbsSlot.isSlot (th := Z.th) (sl := e.2) ⟨ps, he, Or.inl hps⟩,
      hc⟩).1
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeBindNotification (Z := Unit) (.threadCap p.bv) excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  have hNR : Notif.NtfnStateRel Z.N Z.T (L.mem s) σ := hX.fin.1.1.2.2.1
  have hNP : Notif.NPlaced Z.T Z.N := hX.fin.1.1.1.placed
  have hbnd : ∀ xp, σ.kheap p.bv = some (.tcb xp) → xp.tcbBoundNotification = Notif.optRef (L.mem s (P1.boundA p)) := by
    intro xp hk
    obtain ⟨xp', hkp', hxp⟩ := hX.fin.1.1.2.1.tcb p hpT
    rw [hk] at hkp'; cases hkp'; exact hxp.bound
  unfold TcbOKX tcb.decode
  rw [hstall, hdec0]
  simp only [bind_ok, u64_eq_iff, lbl_tcbSetEPTRoot_val, lbl_tcbReadRegisters_val, lbl_tcbWriteRegisters_val, lbl_tcbCopyRegisters_val,
    lbl_tcbConfigure_val, lbl_tcbSetPriority_val, lbl_tcbSetMCPriority_val, lbl_tcbSetSchedParams_val,
    lbl_tcbSetTimeoutEndpoint_val, lbl_tcbSetIPCBuffer_val, lbl_tcbSetSpace_val, lbl_tcbSuspend_val,
    lbl_tcbResume_val, lbl_tcbBindNotification_val]
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  refine let_pair_spec s ar (fun s1 => tcb.decode_bind_notification st s1 p ⟨length, buf, call, slot, extra⟩) _ ?_
  unfold tcb.decode_bind_notification tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  obtain ⟨xp, hkp, -⟩ := hX.fin.1.1.2.1.tcb p hpT
  have hbp := hbnd xp hkp
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length = 0 := by have := ((hXc.2 0 x0 hx0').1).1 h0; omega
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    simp only [Fl4Spec.decodeBindNotification]
    rw [whenE_pos hl]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hXc.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  have hhd : excaps.head? = some e := by rw [List.head?_eq_getElem?]; exact he
  simp only [h0, ↓reduceIte, show length >= 0#u64 from by scalar_tac, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, tcb_bound_eq]
  -- the spec up to the bound-notification check
  have hsp0 : ∀ (k : Option Fl4Spec.ObjRef → Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation),
      ((Fl4Spec.NonDetE.whenE (excaps.length = 0) (Fl4Spec.NonDetE.throwError .truncatedMessage) >>= fun _ =>
        Fl4Spec.NonDetE.liftE (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbBoundNotification p.bv) >>= k) :
          Fl4Spec.SEMonad Unit _).run σ = (k (Notif.optRef (L.mem s (P1.boundA p)))).run σ := by
    intro k
    rw [whenE_neg hexl, retOk_bind,
      lE_bind (m := Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbBoundNotification p.bv)
        (Notif.threadGet_eq _ hkp), hbp]
  by_cases hb0 : L.mem s (P1.boundA p) = 0#u64
  swap
  · -- already bound
    simp only [bne_iff_ne, ne_eq, hb0, not_false_eq_true, ↓reduceIte, error.illegal, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    simp only [Fl4Spec.decodeBindNotification]
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [hb0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hsp1 : (Fl4Spec.decodeBindNotification (Z := Unit) (.threadCap p.bv) excaps).run σ = (do
      let (ntfnptr, rights) ← (match (absCap (capV (L.mem s) x0)) with
        | .notificationCap ptr _ r => Fl4Spec.NonDetE.returnOk (ptr, r)
        | _ => Fl4Spec.NonDetE.throwError .illegalOperation : Fl4Spec.SEMonad Unit _)
      Fl4Spec.NonDetE.whenE (Fl4Spec.AllowRecv ∉ rights) <| Fl4Spec.NonDetE.throwError .illegalOperation
      let ntfn ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getNotification ntfnptr
      match ntfn.ntfnObj, ntfn.ntfnBoundTcb with
      | .idleNtfn, none => Fl4Spec.NonDetE.returnOk ()
      | .activeNtfn _, none => Fl4Spec.NonDetE.returnOk ()
      | _, _ => Fl4Spec.NonDetE.throwError .illegalOperation
      Fl4Spec.NonDetE.returnOk <| Fl4Spec.TcbInvocation.notificationControl p.bv (some ntfnptr)).run σ := by
    simp only [Fl4Spec.decodeBindNotification]
    rw [hsp0]
    simp only [Notif.optRef, hb0, ↓reduceIte]
    rw [retOk_bind, hhd, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc
    cases cc <;> rfl
  unfold tcb.bindable_ntfn
  rw [slot_cap_eq, capAt_capV]
  simp only [bind_ok]
  cases hc : capV (L.mem s) x0
  case Notification q b w r =>
    rw [hc] at hsp1
    simp only [absCap] at hsp1
    rw [retOk_bind] at hsp1
    have hqN := hcapN h0 q b w r hc
    obtain ⟨xn, hkn, hrn⟩ := hNR.ntfn q hqN
    by_cases hr : r = true
    swap
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
      apply run_liftME_err
      rw [hsp1, whenE_pos (by simp only [allowRecv_mem]; exact hr)]
      exact run_throw_bind _ _ _
    rw [whenE_neg (by simp only [allowRecv_mem, not_not]; exact hr), retOk_bind] at hsp1
    simp only [hr, ↓reduceIte, ntfn_head_eq, bind_ok]
    have hbt := hrn.bound
    have hob := hrn.obj
    by_cases hh : L.mem s (P1.epHeadA q) = 0#u64
    swap
    · -- a waiting notification
      simp only [bne_iff_ne, ne_eq, hh, not_false_eq_true, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
      apply run_liftME_err
      rw [hsp1]; dsimp only
      rw [lE_bind (m := Fl4Spec.getNotification (Z := Unit) q.bv) (Notif.getNotification_eq hkn)]
      have hw : ∃ qs, xn.ntfnObj = .waitingNtfn qs := by
        revert hob
        cases xn.ntfnObj with
        | idleNtfn => intro hob; exact absurd (by have := hob.2.head; simpa [Notif.qOf] using this) hh
        | activeNtfn b => intro hob; exact absurd (by have := hob.2.1.head; simpa [Notif.qOf] using this) hh
        | waitingNtfn qs => intro _; exact ⟨qs, rfl⟩
      obtain ⟨qs, hqs⟩ := hw
      rw [hqs]
      exact run_throw_bind _ _ _
    simp only [hh, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ntfn_bound_eq, bind_ok]
    have hnw : ∀ qs, xn.ntfnObj ≠ .waitingNtfn qs := by
      intro qs hq
      rw [hq] at hob
      obtain ⟨-, xs, hxs, -, hqr, -⟩ := hob
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hxs
      have h1 := hqr.head
      have := hqr.ne0 hNP.tcb y (by simp)
      simp only [Notif.qOf, List.headD_cons] at h1
      rw [hh] at h1
      exact this h1.symm
    by_cases hnb : L.mem s (Notif.nBoundA q) = 0#u64
    swap
    · -- a bound notification
      simp only [bne_iff_ne, ne_eq, hnb, not_false_eq_true, ↓reduceIte, error.illegal, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
      apply run_liftME_err
      rw [hsp1]; dsimp only
      rw [lE_bind (m := Fl4Spec.getNotification (Z := Unit) q.bv) (Notif.getNotification_eq hkn), hbt]
      simp only [Notif.optRef, hnb, ↓reduceIte]
      generalize xn.ntfnObj = o
      cases o <;> exact run_throw_bind _ _ _
    simp only [hnb, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeBindNotification (Z := Unit) (.threadCap p.bv) excaps)).run σ =
        ({(.ok (.invokeTCB (.notificationControl p.bv (some q.bv))), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp1]; dsimp only
      rw [lE_bind (m := Fl4Spec.getNotification (Z := Unit) q.bv) (Notif.getNotification_eq hkn), hbt]
      simp only [Notif.optRef, hnb, ↓reduceIte]
      cases ho : xn.ntfnObj with
      | waitingNtfn qs => exact absurd ho (hnw qs)
      | idleNtfn => exact (congrArg (fun m : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation => m.run σ) (retOk_bind () _)).trans rfl
      | activeNtfn b => exact (congrArg (fun m : Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation => m.run σ) (retOk_bind () _)).trans rfl
    have hx0s : IsSlot Z.th x0 := by
      obtain ⟨e, -, ex, -, ps, hps, he⟩ := hXc.get hx0' h0
      rw [ex]; exact AbsSlot.isSlot (th := Z.th) (sl := e.2) ⟨ps, he, Or.inl hps⟩
    have hq0 : q ≠ 0#u64 := (J.capN ⟨x0, b, w, r, hx0s, hc⟩).2
    obtain ⟨s1, σ1, -, hrc1, hst, -, -, -, -, -, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    obtain ⟨hcur, -⟩ := J.curEq hct
    obtain ⟨s1', σ1', hrc', -, -, hSS, -⟩ := restart_dstate Z.th hX.rel.1 s σ Z.G
      ⟨hX.rel.2.1, J.del, hX.rel.2.2.1⟩ ct hct hcur (hX.curTcb hcur).1 J.kern.act
    have e1 : s1' = s1 := by
      have := hrc'.symm.trans hrc1
      simpa using this
    subst e1
    have hcT1 : capAt (L.mem s1') xT = ok (.Thread p) := by rw [capAt_capV, hSS.capV hxT, hcT]
    have hcN1 : capAt (L.mem s1') x0 = ok (.Notification q b w r) := by rw [capAt_capV, hSS.capV hx0s, hc]
    refine leaf_assoc ?_
    rw [hrc1]; simp only [bind_ok]
    refine WP.spec_bind (J1.bindNJ hpT hqN hq0 hxT hcT1 hx0s hcN1) ?_
    rintro s2 ⟨σ', hbn, V, D', J2⟩
    refine (WP.spec_ok _).2 ?_
    have hz : ((.ok [], σ') : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
        ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
          (.invokeTCB (.notificationControl p.bv (some q.bv)))).run σ1).1 := by
      show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1).1
      exact mem_liftE (x := ([], σ')) (mem_bind_nd (x := ((), σ')) (by rw [hbn]; exact Set.mem_singleton _) rfl)
    exact Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst, _, hz, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1, J2.xtop.rel.2.1,
      J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D', J2⟩⟩
  all_goals
    rw [hc] at hsp1
    simp only [error.illegal, bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    rw [hsp1]
    exact run_throw_bind _ _ _

set_option maxHeartbeats 8000000 in
/-- **The SetTimer label at `JAt`** (as `tcb_set_timerX`): the length check,
the caller's restart (`JAtZ.restartJ`), then `timer::insert` by P1's
`timer.insert.foot` (footprint `TmW`, `BlkOK` after, `REPROGRAM` kept or
set) and ScFireJ's `JAtZ.tmw_step`, the spec's reprogram flag chosen as
FL4's (`setTimer_memB`). -/
theorem tcb_set_timerJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .setTimer)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBSetTimer p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4SetTimer (Z := Unit) (args.map UScalar.bv) p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [decode_timer_eq arI s ar p _ hstall, hdec0]
  by_cases h1 : length < 2#u64
  · simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeFl4SetTimer
    rw [whenE_pos (by rw [List.length_map, ← hlen]; scalar_tac)]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  simp only [h1, ↓reduceIte]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  rw [ha0, ha1]; simp only [bind_ok]
  obtain ⟨s1, σ1, -, hrc1, hst1, -, -, -, -, -, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  rw [hrc1]; simp only [bind_ok]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
      (Fl4Spec.decodeFl4SetTimer (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) p.bv)).run σ =
      ({(.ok (.invokeFl4TCB (.setTimer p.bv y0.bv y1.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeFl4SetTimer
    rw [whenE_neg (by simp), retOk_bind]
    rfl
  have hTe : Z.T = P1.Heap.tcbs H := J1.tcbs_eq.1
  have hpH : p ∈ P1.Heap.tcbs H := by rw [← hTe]; exact hpT
  have hc1 : L.cpu s1 = Z.c := by obtain ⟨Q, R0, hc, -⟩ := J1.xtop.fin.1.1.1.lists; exact hc.cur
  refine WP.spec_bind (P1.timer.insert.foot s1 p y0 y1 J1.blk.tinv hpH) ?_
  rintro s2 ⟨hblk2, -, hw, hR⟩
  rw [hc1] at hw hR
  have hw' : P1.WritesIn st s1 s2 (TmW (L := L) Z.T Cs Z.c s1) :=
    hw.mono fun b hb => by unfold TmW; rw [hTe]; exact hb
  obtain ⟨r, J2⟩ := J1.tmw_step hw' hR hblk2
  refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], _),
    setTimer_memB blk call don σ1 p.bv y0.bv y1.bv r, ⟨Z.th, Z.G, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1,
      J2.xtop.rel.2.1, J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨Z, H, Cs, Ac1, Lst1, D1, J2⟩⟩)

set_option maxHeartbeats 8000000 in
/-- **The WriteFPU label at `JAt`** (as `tcb_fpuX` with `toFrame` false):
XTopTcbFpu's `fpu_refinesX` at `X := JAt` (the checks, the decode errors at
the start's `JAtZ`), the work at `J`: the caller's restart
(`JAtZ.restartJ`), `fpu_flush`, the copy into the target's FPU image
(XTopJointTcbMisc's `JAtZ.copyFpuJ`), `fpu_sanitise`, `fpu_reload` (the arch
relation kept: `ARKeep` [P], already a top-level premise; `JAtZ.archJ`), the
spec state the restart's. -/
theorem tcb_write_fpuJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (hK : ARKeep arI AR) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .writeFpu)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBWriteFPU p ⟨length, buf, call, slot, extra⟩
      blk call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (hX.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, J.del, hX.rel.2.2.1⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) false (args.map UScalar.bv) p.bv excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [(decode_fpu_eq arI s ar p _ hstall).2, hdec0]
  refine fpu_refinesX arI (JAt (L := L) arI AR) (fun _ _ _ ⟨Z', _, _, _, _, _, J'⟩ => ⟨Z', J'.xtop⟩) Z.th hX.rel.1
    s ar σ Z.G hDS hX.rel.2.2.2.2.1 p false length buf ct hct args hlen hargs hcur htcb J.kern.act call slot extra
    x0 x1 x2 hx0 excaps hXc ⟨Z, H, Cs, Ac, Lst, D, J⟩ blk don ?_
  intro s1 σ1 x ptr offset r asid va m ep sz hs1 hst1 hx hxn hl ho hc hpass
  obtain ⟨s1', σ1', -, hrc1, hst1', -, -, -, -, -, -, hs1', Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have e1 : s1' = s1 := by
    have := hs1'.symm.trans hs1
    simpa using this
  have e2 : σ1' = σ1 := by
    rw [hcur] at hst1'
    have h := (Prod.mk.inj (hst1'.symm.trans hst1)).1
    exact congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 h)
  subst e1 e2
  have hAR1 := J1.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨hr1, hr3, hm, hlt, hrm⟩ := hpass
  have hvk : capability.VM_KERNEL_ONLY = 1#u64 := by simp only [capability.VM_KERNEL_ONLY]
  have hvrw : capability.VM_READ_WRITE = 3#u64 := by simp only [capability.VM_READ_WRITE]
  obtain ⟨z, hzv, hzf⟩ := fshift_eq sz
  have hge : (⟨length, buf, call, slot, extra⟩ : tcb.Ctx).length >= 1#u64 := by scalar_tac
  have hsz : fl4_abi.consts.FPU_STATE_SIZE + 7#u64 = ok 2703#u64 := by
    unfold fl4_abi.consts.FPU_STATE_SIZE
    obtain ⟨v, hv, hvv⟩ := spec_exists (U64.add_spec (x := 2696#u64) (y := 7#u64) (by scalar_tac))
    rw [hv]; congr 1; apply UScalar.eq_of_val_eq; rw [hvv]; rfl
  have hwd : (2703#u64 : U64) / 8#u64 = ok 337#u64 := by
    obtain ⟨v, hv, hvv⟩ := spec_exists (U64.div_spec (x := 2703#u64) (y := 8#u64) (by decide))
    rw [hv]; congr 1; apply UScalar.eq_of_val_eq; rw [hvv]; rfl
  unfold tcb.fpu_transfer
  rw [extra_eq _ 0#usize (by decide) hx]
  simp only [hxn, ↓reduceIte, hge, bind_ok]
  rw [ho]; simp only [bind_ok]; rw [slot_cap_eq, capAt_capV, hc]; simp only [bind_ok, hvk, hvrw, hzf]
  simp only [Bool.false_eq_true, ↓reduceIte, hr1]
  have hp' : offset.val % 64 = 0 ∧ offset.val < z.val ∧ 2696 ≤ z.val - offset.val := by
    unfold FpuPass.fl4Spec_fpu Fl4Spec.fl4FpuStateSize at hrm
    exact ⟨hm, hzv ▸ hlt, hzv ▸ hrm⟩
  rw [off_pass _ _ offset z hp']
  rw [hrc1]; simp only [bind_ok]
  refine WP.spec_bind (hK.fpu_flush ar p _ hAR1) fun a1 ha1 => ?_
  simp only [hsz, hwd, bind_ok, lift, obj.Tcb.fpu_addr]
  refine WP.spec_bind ((J1.archJ ha1).copyFpuJ hpT _) ?_
  rintro s2 ⟨V2, J2⟩
  try simp only [Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (hK.fpu_sanitise a1 p _ ha1) fun a2 ha2 => ?_
  refine WP.spec_bind (hK.fpu_reload a2 p _ ha2) fun a3 ha3 => ?_
  exact (WP.spec_ok _).2 ⟨rfl, σ1', rfl, ⟨_, H, Cs, Ac1, Lst1, D1, J2.archJ ha3⟩⟩

set_option maxHeartbeats 16000000 in
/-- **The ReadFPU label at `JAt`** (as `tcb_fpuX` with `toFrame` true):
XTopTcbFpu's `fpu_refinesX` at `X := JAt` (the checks, the decode errors at
the start's `JAtZ`), the work at `J`: the caller's restart
(`JAtZ.restartJ`), `fpu_flush` (`ARKeep` [P]; `JAtZ.archJ`), the copy of the
target's FPU image into the frame (XTopJointReadFpu's `JAtZ.copyFrameJ`: the
frame cap's range misses `H`'s non-`other` objects, `JPlaced.cobj`, hence the
TCBs; the frame's bytes in spec user frames from `FpuFrameJHyp` at the start, a
theorem of `JAtZ` (`JAtZ.fpuFrameJ`, from `fcap`), carried across the restart), the spec's step `fl4FpuToFrame` at the user memory FL4's copy leaves
(`fpuToFrame_mem`). -/
theorem tcb_read_fpuJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (hK : ARKeep arI AR)
    (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .readFpu)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hFJ : FpuFrameJHyp (L := L) Z s σ x0)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBReadFPU p ⟨length, buf, call, slot, extra⟩
      blk call don slbl (args.map UScalar.bv) ci sl excaps buffer := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have htcb := (hX.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, J.del, hX.rel.2.2.1⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4FpuTransfer (Z := Unit) true (args.map UScalar.bv) p.bv excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKX
  rw [(decode_fpu_eq arI s ar p _ hstall).1, hdec0]
  refine fpu_refinesX arI (JAt (L := L) arI AR) (fun _ _ _ ⟨Z', _, _, _, _, _, J'⟩ => ⟨Z', J'.xtop⟩) Z.th hX.rel.1
    s ar σ Z.G hDS hX.rel.2.2.2.2.1 p true length buf ct hct args hlen hargs hcur htcb J.kern.act call slot extra
    x0 x1 x2 hx0 excaps hXc ⟨Z, H, Cs, Ac, Lst, D, J⟩ blk don ?_
  intro s1 σ1 x ptr offset r asid va m ep sz hs1 hst1 hx hxn hl ho hc hpass
  have hxx : x = x0 := by
    have h := hx.symm.trans hx0
    exact Fl4Proofs.P3.ok_inj (h : (ok x : Result U64) = ok x0)
  subst hxx
  -- the frame cap's slot, alignment and placement
  obtain ⟨sl0, hA0, hxe⟩ : ∃ sl0, AbsSlot Z.th sl0 ∧ x = cslotAddr sl0 := by
    have h0 := hXc.2 0 x rfl
    obtain ⟨e, he⟩ : ∃ e, excaps[0]? = some e := by
      rcases excaps with _ | ⟨e, rest⟩
      · exact absurd (h0.1.2 (by simp)) hxn
      · exact ⟨e, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 e he
    exact ⟨e.2, ⟨ps, hpe, Or.inl hps⟩, hxe⟩
  have hal : ptr.val % 2 ^ frameBitsN sz = 0 := (show CapValid Z.th (.Frame ptr sz r false m ep asid va) from
    hX.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hc]))
  obtain ⟨h4096, hp8, hpfit⟩ := frame_fit hal
  obtain ⟨hbs, hts⟩ := frame_topF (sz := sz) r false m ep asid va hal
  have hFA : Sched.FrApartH H (.Frame ptr sz r false m ep asid va) := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have := hJ.cobj x (by rw [hxe]; exact hA0.isSlot); rw [hc] at this; exact this
  have hU := hFJ sl0 hA0 hxe ptr sz r m ep asid va hc
  -- the restart
  obtain ⟨s1', σ1', xt, hrc1, hst1', hkt, -, e1σ, -, -, -, hs1', Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have e1 : s1' = s1 := by
    have := hs1'.symm.trans hs1
    simpa using this
  have e2 : σ1' = σ1 := by
    rw [hcur] at hst1'
    have h := (Prod.mk.inj (hst1'.symm.trans hst1)).1
    exact congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 h)
  subst e1 e2
  have hU1 : ∀ a : Nat, ptr.val ≤ a → a < ptr.val + 2 ^ frameBitsN sz → _root_.Fl4Proofs.P3.UFr σ1' a :=
    fun a h1 h2 => _root_.Fl4Proofs.P3.UFr.keep (fun o vms hko => by
      have hne : o ≠ ct.bv := fun e => by rw [e, hkt] at hko; cases hko
      rw [e1σ, stsAct_kheap, Notif.updK_kheap, Function.update_of_ne hne]; exact hko) (hU a h1 h2)
  have hAR1 := J1.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨hr1, hr3, hm, hlt, hrm⟩ := hpass
  have hvk : capability.VM_KERNEL_ONLY = 1#u64 := by simp only [capability.VM_KERNEL_ONLY]
  have hvrw : capability.VM_READ_WRITE = 3#u64 := by simp only [capability.VM_READ_WRITE]
  obtain ⟨z, hzv, hzf⟩ := fshift_eq sz
  have hge : (⟨length, buf, call, slot, extra⟩ : tcb.Ctx).length >= 1#u64 := by scalar_tac
  have hsz : fl4_abi.consts.FPU_STATE_SIZE + 7#u64 = ok 2703#u64 := by
    unfold fl4_abi.consts.FPU_STATE_SIZE
    obtain ⟨v, hv, hvv⟩ := spec_exists (U64.add_spec (x := 2696#u64) (y := 7#u64) (by scalar_tac))
    rw [hv]; congr 1; apply UScalar.eq_of_val_eq; rw [hvv]; rfl
  have hwd : (2703#u64 : U64) / 8#u64 = ok 337#u64 := by
    obtain ⟨v, hv, hvv⟩ := spec_exists (U64.div_spec (x := 2703#u64) (y := 8#u64) (by decide))
    rw [hv]; congr 1; apply UScalar.eq_of_val_eq; rw [hvv]; rfl
  unfold tcb.fpu_transfer
  rw [extra_eq _ 0#usize (by decide) hx0]
  simp only [hxn, ↓reduceIte, hge, bind_ok]
  rw [ho]; simp only [bind_ok]; rw [slot_cap_eq, capAt_capV, hc]; simp only [bind_ok, hvk, hvrw, hzf]
  simp only [Bool.false_eq_true, ↓reduceIte, hr1]
  have hp' : offset.val % 64 = 0 ∧ offset.val < z.val ∧ 2696 ≤ z.val - offset.val := by
    unfold FpuPass.fl4Spec_fpu Fl4Spec.fl4FpuStateSize at hrm
    exact ⟨hm, hzv ▸ hlt, hzv ▸ hrm⟩
  try simp only [↓reduceIte, hr3 rfl, bne_self_eq_false, Bool.false_eq_true]
  rw [off_pass _ _ offset z hp']
  rw [hrc1]; simp only [bind_ok]
  refine WP.spec_bind (hK.fpu_flush ar p _ hAR1) fun a1 ha1 => ?_
  simp only [hsz, hwd, bind_ok, lift, obj.Tcb.fpu_addr]
  -- the frame's 2696 bytes at `f`
  have hrm' : 2696 ≤ 2 ^ frameBitsN sz - offset.val := hrm
  have hfv : (core.num.U64.wrapping_add ptr offset).val = ptr.val + offset.val := by
    simp only [core.num.U64.wrapping_add_val_eq]
    simp [U64.size, U64.numBits]
    omega
  refine WP.spec_bind ((J1.archJ ha1).copyFrameJ _ (core.num.U64.wrapping_add ptr offset)
    (by rw [hfv]; omega) (by rw [hfv]; omega) (fun q k hq hk => ?_)
    (fun a h1 h2 => hU1 a (by rw [hfv] at h1; omega) (by rw [hfv] at h2; omega))) ?_
  · rcases hFA q k hq hk with e | e
    · right; rw [hbs] at e; rw [hfv]; omega
    · left; rw [hts] at e; rw [hfv]; omega
  rintro s2 ⟨um, hag, J2⟩
  try simp only [↓reduceIte]
  refine (WP.spec_ok _).2 ⟨rfl, Endp.setUm σ1' um, ?_, ⟨Z, H, Cs, Ac1, Lst1, D1, J2⟩⟩
  show _ ∈ ((Fl4Spec.NonDetE.liftE _).run σ1').1
  refine mem_liftE (x := ([], Endp.setUm σ1' um)) ?_
  refine mem_bind_nd (x := ((), Endp.setUm σ1' um)) ?_ (Set.mem_singleton_iff.2 rfl)
  have hfb : (core.num.U64.wrapping_add ptr offset).bv = ptr.bv + offset.bv := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add]
    show (core.num.U64.wrapping_add ptr offset).val = (ptr.val + offset.val) % 2 ^ 64
    rw [hfv]; exact (Nat.mod_eq_of_lt (by omega)).symm
  exact dmo_ex _ σ1' (fpuToFrame_mem _ σ1'.machineState um fun b hb => hag b (by rw [hfb]; exact hb))

set_option maxHeartbeats 32000000 in
/-- **The GetBreakpoint label at `JAt`** (as `tcb_get_bpX`): the breakpoint
number's check, the caller's restart (`JAtZ.restartJ`), the read (`GetBpHyp`
[P]), then the data tail of the five words, each step at `RInv` (for
`XTop`'s facts, `data_tail_core`) and at `JAtZ` (`JAtZ.setmrJ`, the buffer
word `MR4` by `JAtZ.userWrJ` with `JAtZ.bufWord`; `JAtZ.replyTailJ`). -/
theorem tcb_get_bpJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ)
    (p : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .getBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 1) (hG : GetBpHyp (st := st) s ct p)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKRX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBGetBreakpoint p
      ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xc, hkc⟩ := hX.curTcb hcur
  have hctT : ct ∈ Z.T := J.thT ct htcb
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKRX
  rw [decode_getbp_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  have hsp : (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv).run σ =
      (Fl4Spec.fl4CheckBpNum (Z := Unit) bp.bv >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.getBreakpoint p.bv bp.bv)).run σ := by
    unfold Fl4Spec.decodeFl4GetBreakpoint
    exact run_bind_ok hbs _
  unfold tcb.decode_get_breakpoint
  rw [hct]; simp only [bind_ok]; rw [hbp]; simp only [bind_ok]; rw [check_bp_eq]
  by_cases hb : bp ≥ 4#u64
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, bp_err⟩, ⟨Z, H, Cs, Ac, Lst, D, J⟩⟩)
    apply run_liftME_err
    rw [hsp]
    exact run_bind_error (by rw [checkBp_run, if_pos hb]) _
  simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨s1, σ1, x0, hrc1, hst1, hk0, -, hσ1, -, -, hcu1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  rw [hkc] at hk0; cases hk0
  set xr : Fl4Spec.Tcb := { xc with tcbState := .restart }
  have hkc1 : σ1.kheap ct.bv = some (.tcb xr) := by
    rw [hσ1, Notif.stsAct_kheap]; simp [Notif.updK, xr]
  have hcurY : ct.bv = σ1.curThread := by rw [hcu1, hcur]
  have hX1 := J1.xtop
  have hact1 : OutsideObjects Z.th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) := J1.kern.act
  rw [hrc1]; simp only [bind_ok]
  obtain ⟨r1, hr1⟩ := hG s1 bp hs1
  rw [hr1]; simp only [bind_ok]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
      (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)).run σ =
      ({(.ok (.invokeFl4TCB (.getBreakpoint p.bv bp.bv)), σ)}, False) := by
    apply run_liftME_ok
    rw [hsp, run_bind_ok (by rw [checkBp_run, if_neg hb])]
    rfl
  have hy : ∀ rr : List Fl4Spec.Data, rr.length = 5 → (.ok rr, σ1) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit)
      blk call don (.invokeFl4TCB (.getBreakpoint p.bv bp.bv))).run σ1).1 :=
    fun rr h => mem_liftE (x := (rr, σ1)) ⟨h, rfl⟩
  refine WP.spec_bind (Pₘ := fun x : core.result.Result Unit error.Exc × S =>
    TopPostRMX (L := L) (JAt (L := L) arI AR) σ blk call don (Fl4Spec.NonDetE.liftME
      Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)) ct s
      (x.1, x.2, ar)) ?_ fun x hx => (WP.spec_ok _).2 hx
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (WP.spec_and (nodata_tail_core hX1 hcurY hkc1 rfl hact1 [0, 0, 0, 0, 0])
      (J1.runJ hctT hkc1 rfl)) ?_
    rintro s2 ⟨⟨hne, z, hz, hRT, -⟩, Lst', D', J5⟩
    refine (WP.spec_ok _).2 (Or.inr ⟨rfl, hne, _, DecOut.of_eq hdec, σ1, hst1, _, σ1, hy _ rfl, z, hz, hRT, ?_⟩)
    have hrs1 : xr.tcbState = .restart := rfl
    unfold specTail at hz
    rw [nd_bind_one (Notif.getThreadState_eq hkc1)] at hz
    simp only [hrs1] at hz
    rw [Endp.nd_when_false (by simp), Notif.nd_pure_bind', Notif.setThreadState_eq .running hkc1] at hz
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨_, _, _, _, _, _, J5⟩
  · simp only [↓reduceIte]
    have hOK1 := J1.xferH.1
    obtain ⟨x', hk', hwx⟩ := J1.buf ct hctT
    rw [hkc1] at hk'; cases hk'
    refine WP.spec_bind (lookup_buf_full s1 σ1 hX1.rel.2.1.1 hX1.rel.2.1.2.1 htcb hkc1 hOK1 true) ?_
    rintro bf ⟨hw0, hwp⟩
    have hbm : ∀ q, Endp.ipcBufOf true xr = some q → Endp.BufMap Z.B bf q := fun q hq =>
      J1.xferH.2.1 ct hctT xr true q hkc1 hq bf (hwp hwx q hq)
    have hBP1 := J1.xferH.2.2
    have hWOK : ∀ q, Endp.ipcBufOf true xr = some q → ∀ i : U64, i.val < 128 →
        BufWordOK H σ1 (Endp.fl4BufA bf i) := fun q hq i hi =>
      J1.bufWord hOK1 htcb hkc1 hq i.val hi (by rw [fl4BufA_bv, hwp hwx q hq])
    have hI0 : Vs.RInv (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR Z.G s1 ar
        (MrS σ1 ct.bv xr (Endp.ipcBufOf true xr) []) := by
      rw [MrS_nil hkc1]; exact hX1.toRInv
    have J0 : JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 s1 ar (MrS σ1 ct.bv xr (Endp.ipcBufOf true xr) []) := by
      rw [MrS_nil hkc1]; exact J1
    refine WP.spec_bind (WP.spec_and (setmr_reg_inv σ1 ct htcb hcurY xr _ bf s1 ar [] hI0 0#u64 rfl (by decide)
      r1.vaddr) (J0.setmrJ hctT hkc1 bf hw0 hbm hBP1 hWOK 0#u64 rfl (by decide) r1.vaddr)) ?_
    rintro ⟨l2, s2⟩ ⟨⟨-, hI2, hk2, hc2⟩, -, -, V2, J2⟩
    simp only at hI2 hk2 hc2 J2
    refine WP.spec_bind (WP.spec_and (setmr_reg_inv σ1 ct htcb hcurY xr _ bf s2 ar _ hI2 1#u64 rfl (by simp) r1.ty)
      (J2.setmrJ hctT hkc1 bf hw0 hbm (hBP1.mono hk2 fun _ _ _ h => h) hWOK 1#u64 rfl (by simp) r1.ty)) ?_
    rintro ⟨l3, s3⟩ ⟨⟨-, hI3, hk3, hc3⟩, -, -, V3, J3⟩
    simp only at hI3 hk3 hc3 J3
    refine WP.spec_bind (WP.spec_and (setmr_reg_inv σ1 ct htcb hcurY xr _ bf s3 ar _ hI3 2#u64 rfl (by simp) r1.size)
      (J3.setmrJ hctT hkc1 bf hw0 hbm (hBP1.mono (hk3.trans hk2) fun _ _ _ h => h) hWOK 2#u64 rfl (by simp)
        r1.size)) ?_
    rintro ⟨l4, s4⟩ ⟨⟨-, hI4, hk4, hc4⟩, -, -, V4, J4⟩
    simp only at hI4 hk4 hc4 J4
    refine WP.spec_bind (WP.spec_and (setmr_reg_inv σ1 ct htcb hcurY xr _ bf s4 ar _ hI4 3#u64 rfl (by simp) r1.rw)
      (J4.setmrJ hctT hkc1 bf hw0 hbm (hBP1.mono (hk4.trans (hk3.trans hk2)) fun _ _ _ h => h) hWOK 3#u64 rfl
        (by simp) r1.rw)) ?_
    rintro ⟨l5, s5⟩ ⟨⟨-, hI5, hk5, hc5⟩, -, -, V5, J5⟩
    simp only at hI5 hk5 hc5 J5
    have hks5 : L.ksb s5 = L.ksb s1 := hk5.trans (hk4.trans (hk3.trans hk2))
    have hcp5 : L.cpu s5 = L.cpu s1 := hc5.trans (hc4.trans (hc3.trans hc2))
    have hBP5 : Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s5 σ1 := hBP1.mono hks5 (fun _ _ _ h => h)
    have tail : ∀ v : U64, (do
        let (len, s6) ← msg.set_mr st s5 ct bf 4#u64 v
        let s7 ← tcb.reply_words st s6 ct len
        let s8 ← sched.set_thread_state st s7 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s8)) ⦃ res =>
          TopPostRMX (L := L) (JAt (L := L) arI AR) σ blk true don (Fl4Spec.NonDetE.liftME
            Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)) ct s
            (res.1, res.2, ar) ⦄ := by
      intro v
      refine WP.spec_bind (WP.spec_and (Vs.setmr_inv σ1 ct htcb hcurY hkc1 _ bf hw0 hbm s5 ar _ hI5 hBP5 4#u64 rfl
        (by simp) v) (J5.setmrJ hctT hkc1 bf hw0 hbm hBP5 hWOK 4#u64 rfl (by simp) v)) ?_
      rintro ⟨len, s6⟩ ⟨⟨hlen, hI6, hk6, hc6⟩, -, -, V6, J6⟩
      simp only at hlen hI6 hk6 hc6 J6
      have hfr : ∀ q, Endp.ipcBufOf true xr = some q → ∀ z ∈ Endp.mrPairs
          ([] ++ [r1.vaddr.bv] ++ [r1.ty.bv] ++ [r1.size.bv] ++ [r1.rw.bv] ++ [v.bv]),
          (Endp.bufAddr q z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q z.1) σ1 :=
        fun q hq z hz => ⟨Endp.bufAddr_aligned hX1.fin.1.2.ep (hbm q hq) z.1,
          buf_frame_of_ok hOK1 hkc1 hq z.1 (mrPairs_lt hz)⟩
      have hl5 : ([] ++ [r1.vaddr.bv] ++ [r1.ty.bv] ++ [r1.size.bv] ++ [r1.rw.bv] ++ [v.bv]).length = 5 := rfl
      have hn128 : len.val < 128 := by rw [hlen]; cases Endp.ipcBufOf true xr <;> simp [mrLen]
      show (do
        let s7 ← tcb.reply_words st s6 ct len
        let s8 ← sched.set_thread_state st s7 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s8)) ⦃ _ ⦄
      rw [← Std.bind_assoc]
      refine WP.spec_bind (WP.spec_and (data_tail_core hX1 hcurY hkc1 rfl hact1 hI6 (hk6.trans hks5)
        (hc6.trans hcp5) (by rw [hl5]; decide) hfr len (by rw [hlen]; simp) hn128)
        (J6.replyTailJ hctT hkc1 rfl (by rw [hl5]; decide) hfr len (by rw [hlen]; simp) hn128)) ?_
      rintro s8 ⟨⟨hne, z, hz, hRT, -⟩, hJ8⟩
      exact (WP.spec_ok _).2 (Or.inr ⟨rfl, hne, _, DecOut.of_eq hdec, σ1, hst1, _, σ1, hy _ hl5, z, hz, hRT,
        hJ8 z hz⟩)
    split
    · exact tail 1#u64
    · exact tail 0#u64


set_option maxHeartbeats 8000000 in
/-- **The ReadRegisters label at `JAt`** (as `tcb_read_regsX`): TcbCtl's
decode, the caller's restart (`JAtZ.restartJ`), then XTopJointReadRegs'
`JAtZ.readRegsJ` (the source's suspend, the copy loops, the reply tail). -/
theorem tcb_read_regsJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (hpI : p ≠ L.idleW s) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbReadRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKRX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBReadRegisters p ⟨length, buf, call, slot, extra⟩
      blk call don slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have htcb := (hX.curTcb hcur).1
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeReadRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKRX
  rw [decode_read_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_read_registers
  by_cases h1 : length < 2#u64
  · simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    have : args.length < 2 := by scalar_tac
    match args, this with
    | [], _ => rfl
    | [_], _ => rfl
  simp only [h1, ↓reduceIte]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp at h; scalar_tac
    | [_], h => exfalso; simp at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  rw [ha0, ha1]; simp only [bind_ok, nregs_eq]
  have hsp : ∀ (k : Unit → Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation),
      (Fl4Spec.decodeReadRegisters (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv)) =
      (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20) >>= fun _ => do
        let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
        Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError .illegalOperation)
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
          Fl4Spec.ArchDefaultExtraRegisters)) := by
    intro _
    simp only [Fl4Spec.decodeReadRegisters, List.map_cons, nregs_spec, retOk_bind]
  rw [hsp (fun _ => Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.suspend 0))]
  have hrng := range20_iff y1
  by_cases hr : 1 ≤ y1.val ∧ y1.val ≤ 20
  · have hn1 : ¬ y1 < 1#u64 := by scalar_tac
    have hn2 : ¬ y1 > 20#u64 := by scalar_tac
    simp only [hn1, hn2, ↓reduceIte, hct, bind_ok, tcb_eq_ct]
    have hrc : (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20)).run σ = ({(.ok (), σ)}, False) := by
      unfold Fl4Spec.rangeCheck Fl4Spec.NonDetE.unlessE; rw [if_pos (hrng.2 hr)]; rfl
    by_cases hpc : p = ct
    · subst hpc
      simp only [decide_true, ↓reduceIte, error.illegal, bind_ok]
      refine (WP.spec_ok _).2 ?_
      apply Or.inl
      refine ⟨_, rfl, rfl, ⟨.illegalOperation, ?_, Or.inl trivial⟩, hJ0⟩
      apply run_liftME_err
      rw [run_bind_ok hrc, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
        s.curThread) rfl), whenE_pos (by show p.bv = σ.curThread; rw [hcur])]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨s1, σ1, x1, hrc1, hst1, hk1, -, hσ1, hns, hid1, hcu1, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
      have hkc1 : σ1.kheap ct.bv = some (.tcb { x1 with tcbState := .restart }) := by
        rw [hσ1, Notif.stsAct_kheap]; simp [Notif.updK]
      rw [hrc1]; simp only [bind_ok, lift]
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20) >>= fun _ => do
            let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
            Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError .illegalOperation)
            Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
              Fl4Spec.ArchDefaultExtraRegisters))).run σ =
          ({(.ok (.invokeTCB (.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
            Fl4Spec.ArchDefaultExtraRegisters)), σ)}, False) := by
        apply run_liftME_ok
        rw [run_bind_ok hrc, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
          s.curThread) rfl), whenE_neg (by show ¬ p.bv = σ.curThread; rw [hcur, bv_eq_iff']; exact hpc), retOk_bind]
        rfl
      refine WP.spec_bind (J1.readRegsJ (blk := blk) (don := don) hns
        (by rw [hid1]; exact J.ne_idle hpI) (by rw [hcu1]; exact hcur) hkc1 rfl hpc hpT y0 y1) ?_
      rintro ⟨s2, a2⟩ ⟨hne, rr, σy, hm, z, hz, hRz, hXz⟩
      exact (WP.spec_ok _).2 (Or.inr ⟨rfl, hne, _, DecOut.of_eq hdec, σ1, hst1, rr, σy, hm, z, hz, hRz, hXz⟩)
  · have hrc : (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20)).run σ =
        ({(.error (.rangeError 1 (BitVec.ofNat 64 20)), σ)}, False) := by
      unfold Fl4Spec.rangeCheck Fl4Spec.NonDetE.unlessE; rw [if_neg (fun h => hr (hrng.1 h))]; rfl
    have herr : ErrRel (.Sys (.RangeError 1#u64 20#u64)) (.rangeError 1 (BitVec.ofNat 64 20)) :=
      Or.inl ⟨rfl, rfl⟩
    by_cases hn1 : y1 < 1#u64
    · simp only [hn1, ↓reduceIte, error.range, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, herr⟩, hJ0⟩)
      exact run_liftME_err (run_bind_error hrc _)
    · have hn2 : y1 > 20#u64 := by scalar_tac
      simp only [hn1, hn2, ↓reduceIte, error.range, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, herr⟩, hJ0⟩)
      exact run_liftME_err (run_bind_error hrc _)


set_option maxHeartbeats 8000000 in
/-- **The SetMCPriority label at `JAt`** (as `tcb_set_mcpX`): the decode with
the authority's MCP by `JAtZ`'s `McpRel` and the authority among the TCBs
(`hcapT`, from the slots' caps), the caller's restart (`JAtZ.restartJ`), the
target's `MCP` word and `tcb_mcpriority` (`JAtZ.mcpWrJ`). -/
theorem tcb_set_mcpJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetMCPriority)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBSetMCPriority p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hX := J.xtop
  have hM := J.mcp
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetMcpriority (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_mcp_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_priority tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_pos (Or.inr (by omega))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hXc.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  by_cases h1 : length >= 1#u64
  swap
  · simp only [h0, ↓reduceIte, if_neg h1, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_pos (Or.inl (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  simp only [h0, ↓reduceIte, if_pos h1, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  · obtain ⟨q, hq⟩ := hth
    rw [thread_arg_thread s 1#u64 hq]
    simp only [bind_ok, check_prio_eq]
    obtain ⟨xq, hkq, hmq⟩ := hM q (hcapT h0 q hq)
    have hu : (Fl4Spec.ucast 64 xq.tcbMcpriority) = (L.mem s (mcpA q)).bv := by
      apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast, hmq]
      have := xq.tcbMcpriority.isLt; omega
    have hspec1 : (Fl4Spec.decodeSetMcpriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
          (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) >>= fun _ =>
          (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none
            (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none none) : Fl4Spec.SEMonad Unit _)).run σ := by
      have he1' : e.1 = .threadCap q.bv := by rw [he1, hq]; rfl
      unfold Fl4Spec.decodeSetMcpriority
      rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1']
      show ((Fl4Spec.NonDetE.returnOk q.bv : Fl4Spec.SEMonad Unit _) >>= _).run σ = _
      rw [retOk_bind]
      have hcp : (Fl4Spec.checkPrio (Z := Unit) (Fl4Spec.the (List.map UScalar.bv (y0 :: rest))[0]?) q.bv).run σ =
          (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
            (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) : Fl4Spec.SEMonad Unit Unit).run σ := by
        unfold Fl4Spec.checkPrio
        rw [lE_bind (Notif.threadGet_eq _ hkq), hu]; rfl
      rw [ExceptT.run_bind, nd_bind_congr hcp, ExceptT.run_bind]; rfl
    by_cases hgt : y0 > L.mem s (mcpA q)
    · rw [ite_eq_left hgt]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hgt)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 _) :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [ite_eq_right hgt]
      simp only [bind_ok]
      obtain ⟨s1, σ1, x1, hrc, hst1, -, -, -, -, -, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
      rw [hrc]; simp only [bind_ok, tcs_mcp]
      refine (WP.spec_ok _).2 ?_
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetMcpriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none none)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hgt), retOk_bind]; rfl
      have hlt : y0.val < 256 := by
        have := xq.tcbMcpriority.isLt
        have h2 : ¬ (L.mem s (mcpA q)).val < y0.val := hgt
        omega
      obtain ⟨x, hkx, -⟩ := J1.xtop.fin.1.1.2.1.tcb p hpT
      obtain ⟨V2, J2⟩ := J1.mcpWrJ hpT hkx y0 (Fl4Spec.ucast 8 y0.bv)
        (by rw [Ipc.ucast8_specPrio, Sched.specPrio_toNat hlt])
      refine Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], _), ?_, ⟨_, _, Or.inl ⟨rfl, rfl⟩, J2.xtop.rel.1,
        J2.xtop.rel.2.1, J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D1, J2⟩⟩
      rw [invoke_mcp_run hkx]; exact Set.mem_singleton _
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetMcpriority
    rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
          Fl4Spec.SEMonad Unit Fl4Spec.ObjRef)) rfl _


set_option maxHeartbeats 8000000 in
/-- **The SetPriority label at `JAt`** (as `tcb_set_prioX`): the decode with
the authority's MCP by `JAtZ`'s `McpRel` and the authority among the TCBs
(`hcapT`), the caller's restart (`JAtZ.restartJ`), then `set_priority` at
`J` (XTopJointTcbPrio's `JAtZ.setPrioJ`, the current thread's facts by
`JAtZ.prioCur` with `CurInv` carried across the restart, `CurInv.restart`). -/
theorem tcb_set_prioJ (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (p : U64) (hpT : p ∈ Z.T) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetPriority)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (ssl : Fl4Spec.CslotPtr)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 x2 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps)
    (hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T)
    (blk don : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBSetPriority p
      ⟨length, buf, call, cslotAddr ssl, extra⟩ blk call don slbl (args.map UScalar.bv) ci ssl excaps buffer := by
  have hX := J.xtop
  have hM := J.mcp
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci ssl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetPriority (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv) ssl excaps) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) ssl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKX
  rw [decode_prio_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_set_priority tcb.extra_with_length
  rw [extra_eq _ 0#usize (by decide) hx0]
  have hx0' : [x0, x1, x2][0]? = some x0 := rfl
  by_cases h0 : x0 = 0#u64
  · -- no extra cap: truncated
    have hl : excaps.length ≤ 0 := ((hXc.2 0 x0 hx0').1).1 h0
    simp only [h0, ↓reduceIte, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_pos (Or.inr (by omega))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨e, he, hxe, he1, ps, hps, hps1⟩ := hXc.get hx0' h0
  have hexl : excaps.length ≠ 0 := by
    have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (List.mem_of_getElem? he)); omega
  by_cases h1 : length >= 1#u64
  swap
  · simp only [h0, ↓reduceIte, if_neg h1, bind_ok, error.truncated, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.truncatedMessage, ?_, Or.inl trivial⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_pos (Or.inl (show (args.map UScalar.bv).length = 0 by rw [List.length_map, ← hlen]; scalar_tac))]
    exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.truncatedMessage :
      Fl4Spec.SEMonad Unit Unit)) rfl _
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  have harg := tcb_arg_eq s ⟨length, buf, call, cslotAddr ssl, extra⟩ hct (hargs 0#u64 y0 (by simp))
  simp only [h0, ↓reduceIte, if_pos h1, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, harg]
  by_cases hth : ∃ q, capV (L.mem s) x0 = .Thread q
  · obtain ⟨q, hq⟩ := hth
    rw [thread_arg_thread s 1#u64 hq]
    simp only [bind_ok, check_prio_eq]
    obtain ⟨xq, hkq, hmq⟩ := hM q (hcapT h0 q hq)
    have hu : (Fl4Spec.ucast 64 xq.tcbMcpriority) = (L.mem s (mcpA q)).bv := by
      apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast, hmq]
      have := xq.tcbMcpriority.isLt; omega
    have hspec1 : (Fl4Spec.decodeSetPriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
        excaps).run σ = (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
          (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) >>= fun _ =>
          (Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none none
            (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none) : Fl4Spec.SEMonad Unit _)).run σ := by
      have he1' : e.1 = .threadCap q.bv := by rw [he1, hq]; rfl
      unfold Fl4Spec.decodeSetPriority
      rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1']
      show ((Fl4Spec.NonDetE.returnOk q.bv : Fl4Spec.SEMonad Unit _) >>= _).run σ = _
      rw [retOk_bind]
      have hcp : (Fl4Spec.checkPrio (Z := Unit) (Fl4Spec.the (List.map UScalar.bv (y0 :: rest))[0]?) q.bv).run σ =
          (Fl4Spec.NonDetE.whenE (y0.bv > (L.mem s (mcpA q)).bv)
            (Fl4Spec.NonDetE.throwError (.rangeError 0 (L.mem s (mcpA q)).bv)) : Fl4Spec.SEMonad Unit Unit).run σ := by
        unfold Fl4Spec.checkPrio
        rw [lE_bind (Notif.threadGet_eq _ hkq), hu]; rfl
      rw [ExceptT.run_bind, nd_bind_congr hcp, ExceptT.run_bind]; rfl
    by_cases hgt : y0 > L.mem s (mcpA q)
    · rw [ite_eq_left hgt]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.rangeError 0 (L.mem s (mcpA q)).bv, ?_, Or.inl ⟨rfl, rfl⟩⟩, hJ0⟩)
      apply run_liftME_err
      rw [hspec1, whenE_pos (by rw [GT.gt, ← u64_lt_bv]; exact hgt)]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 _) :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · rw [ite_eq_right hgt]
      simp only [bind_ok]
      obtain ⟨s1, σ1, x1, hrc, hst1, hk1, hcur1, e1, hsw1, hid1, hct1, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
      have hlt : y0.val < 256 := by
        have := xq.tcbMcpriority.isLt
        have h2 : ¬ (L.mem s (mcpA q)).val < y0.val := hgt
        omega
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.decodeSetPriority (Z := Unit) ((y0 :: rest).map UScalar.bv) (.threadCap p.bv) ssl
            excaps)).run σ = ({(.ok (.invokeTCB (Fl4Spec.TcbInvocation.threadControlSched p.bv ssl none none
              (some (Fl4Spec.ucast 8 y0.bv, q.bv)) none)), σ)}, False) := by
        apply run_liftME_ok
        rw [hspec1, whenE_neg (by rw [GT.gt, ← u64_lt_bv]; exact hgt), retOk_bind]; rfl
      -- the current thread's invariants after the restart
      have hC1 : Sched.CurInv σ1 := by
        have hC0 := J.curInv (by rw [hni.2]; intro h; cases h)
        have h := hC0.restart (xt := x1) (by rw [hcur1]; exact hk1)
        rw [hcur1] at h
        rw [e1]; exact h
      have hne1 : σ1.curThread ≠ σ1.idleThread := by rw [hct1, hid1]; exact hni.1
      obtain ⟨hc1, hp1⟩ := J1.prioCur hne1 hC1 hpT
      rw [hrc]; simp only [bind_ok, tcs_prio]
      refine WP.spec_bind (J1.setPrioJ (fun u h => hsw1 u h) hpT y0 hlt hc1 hp1) ?_
      rintro s2 ⟨σ2, hm2, V2, J2⟩
      refine (WP.spec_ok _).2 (Or.inr ⟨_, DecOut.of_eq hdec, σ1, hst1, (.ok [], σ2), ?_, ⟨_, _, Or.inl ⟨rfl, rfl⟩,
        J2.xtop.rel.1, J2.xtop.rel.2.1, J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩,
        ⟨_, H, Cs, Ac1, Lst1, D1, J2⟩⟩)
      refine invoke_prio_mem ssl _ q.bv blk call don (y := ((), σ2)) ?_
      rw [hm2]; exact Set.mem_singleton _
  · have hne : ∀ r, absCap (capV (L.mem s) x0) ≠ .threadCap r := fun r h => by
      obtain ⟨q, hq, -⟩ := absCap_thread h; exact hth ⟨q, hq⟩
    rw [thread_arg_other s 1#u64 (fun q h => hth ⟨q, h⟩)]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨.invalidCapability 1, ?_, Or.inr ⟨1#u64, rfl, rfl⟩⟩, hJ0⟩)
    apply run_liftME_err
    unfold Fl4Spec.decodeSetPriority
    rw [whenE_neg (by simp [hexl]), retOk_bind, retOk_bind, he, the_some, he1]
    generalize absCap (capV (L.mem s) x0) = cc at hne ⊢
    cases cc
    all_goals first
      | exact absurd rfl (hne _)
      | exact run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.invalidCapability 1) :
          Fl4Spec.SEMonad Unit Fl4Spec.ObjRef)) rfl _


end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The syscall arguments read only the caller's message registers and
buffer words** (`msg::syscall_arg`: the first four from registers, the rest
from buffer word `i + 1`). -/
theorem syscall_arg_keep {s s' : S} {ct buf i : U64}
    (hr : ∀ g : Fl4Spec.Register, L.mem s' (regA ct (regIdx g)) = L.mem s (regA ct (regIdx g)))
    (hb : buf ≠ 0#u64 → L.mem s' (fl4BufA buf (core.num.U64.wrapping_add i 1#u64)) =
      L.mem s (fl4BufA buf (core.num.U64.wrapping_add i 1#u64))) :
    msg.syscall_arg st s' ct buf i = msg.syscall_arg st s ct buf i := by
  have hreg : ∀ g : Fl4Spec.Register, obj.Tcb.reg st ct s' (regIdx g) = obj.Tcb.reg st ct s (regIdx g) := by
    intro g
    unfold obj.Tcb.reg
    simp only [lift, bind_ok, L.read_eq]
    exact congrArg ok (hr g)
  unfold msg.syscall_arg
  split
  · unfold msg.msg_register
    split_ifs
    · rw [show layout.reg.R10 = regIdx (mrIdx 0) by unfold layout.reg.R10; rfl]; simp only [bind_ok]; exact hreg _
    · rw [show layout.reg.R8 = regIdx (mrIdx 1) by unfold layout.reg.R8; rfl]; simp only [bind_ok]; exact hreg _
    · rw [show layout.reg.R9 = regIdx (mrIdx 2) by unfold layout.reg.R9; rfl]; simp only [bind_ok]; exact hreg _
    · rw [show layout.reg.R15 = regIdx (mrIdx 3) by unfold layout.reg.R15; rfl]; simp only [bind_ok]; exact hreg _
  · split
    · rename_i hb0
      unfold msg.buf_get
      simp only [lift, bind_ok, L.read_eq]
      exact congrArg ok (hb (by simpa using hb0))
    · rfl

set_option maxHeartbeats 4000000 in
/-- **The syscall arguments after the caller's restart** (WriteRegisters
reads them after `set_thread_state ct Restart`): that step writes the
caller's state word and maybe the current core's scheduler-action word
(IntRel's `set_thread_state_cases`). The caller's message registers are
other words of its TCB, outside the node (`JKern.hnd`); its mapped buffer
words (`BufMap`, in `B`) lie apart from the TCBs (`EPlaced.bt`) and from the
kernel-state block up to the end of the current core's node
(`BufPlaced.far`). An index below 127 keeps the buffer word among the 128
mapped ones. -/
theorem JAtZ.argsRestart {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hBP : BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ)
    {ct buf : U64} (hctT : ct ∈ Z.T) (hth : Z.th ct = some .tcb)
    {sp : Fl4Spec.Word} (hbm : buf ≠ 0#u64 → BufMap Z.B buf sp) {i : U64} (hi : i.val < 127)
    {s1 : S} (h1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1) :
    msg.syscall_arg st s1 ct buf i = msg.syscall_arg st s ct buf i := by
  have hc := set_thread_state_cases (st := st) s ct sched.TS_RESTART
  rw [h1, WP.spec_ok] at hc
  have hta : P1.TcbAddr ct := J.ip.e.tcb ct hctT
  have hal := hta.align
  have hstv : (stA ct).val = ct.val + 3328 := stA_val J.xtop.rel.1 hth
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hcq, -⟩ := hS.lists
  have hcpu : L.cpu s = Z.c := hcq.cur
  have ho : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
  have ho8 : layout.node.SCHED_ACTION.val % 8 = 0 := by simp [layout.node.SCHED_ACTION]
  have hav := Sched.nodeAt_val' (s := s) J.kern.nodeFit ho
  have hkal := J.kern.ksbAl
  have hal_st : P1.Aligned (stA ct) := by unfold P1.Aligned; rw [hstv]; omega
  have hal_act : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    unfold P1.Aligned; rw [hav]; omega
  have key : ∀ b : U64, P1.Aligned b → b.val ≠ (stA ct).val →
      b.val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val → L.mem s1 b = L.mem s b := by
    intro b hb n1 n2
    rcases hc with rfl | rfl
    · exact L.mem_wr_ne hal_st hb (Ne.symm n1)
    · rw [L.mem_wr_ne hal_act hb (Ne.symm n2)]; exact L.mem_wr_ne hal_st hb (Ne.symm n1)
  have hnd := J.kern.hnd ct _ (J.zH.1 ct hctT) (L.cpu s) J.kern.cpuCs
  simp only [P1.HKind.bits, P1.LawfulStore.nodeBase, Nat.reducePow] at hnd
  apply syscall_arg_keep
  · intro g
    have hr := regA_val hta (regIdx_lt g)
    have := regIdx_lt g
    exact key _ (by unfold P1.Aligned; rw [hr]; omega) (by rw [hr, hstv]; omega) (by rw [hr, hav]; omega)
  · intro hb0
    have hi1 : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := by
      have := i.hBounds
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at this ⊢
      omega
    have hw := hbm hb0 (core.num.U64.wrapping_add i 1#u64) (by rw [hi1]; omega)
    set j := core.num.U64.wrapping_add i 1#u64
    have h8 : (fl4BufA buf j).val % 8 = 0 := (J.ip.e.balign _ hw).1
    have hbt : (fl4BufA buf j).val < ct.val ∨ ct.val + 4096 ≤ (fl4BufA buf j).val := J.ip.e.bt _ hw ct hctT
    have hfar : (fl4BufA buf j).val + 8 ≤ (L.ksb s).val ∨ L.nodeBase s Z.c + 4288 ≤ (fl4BufA buf j).val :=
      hBP.far _ hw
    simp only [P1.LawfulStore.nodeBase] at hfar
    rw [← hcpu] at hfar
    exact key (fl4BufA buf j) h8 (by rw [hstv]; omega) (by rw [hav]; omega)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **A Thread cap at an FL4 label other than the five installing ones**
decodes to no invocation with a preemption point (`specDec_thread_noPre`). -/
theorem thread_noPre_of {slbl : Fl4Spec.Data} {lbl : U64}
    (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (h : lbl.val ≠ 5 ∧ lbl.val ≠ 8 ∧ lbl.val ≠ 9 ∧ lbl.val ≠ 10 ∧ lbl.val ≠ 11)
    {fp : Bool} {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit}
    {p : U64} :
    ∀ inv, DecOut (specDec fp slbl args ci sl (.Thread p) excaps buffer) σ inv → ¬ NoPre.PreInv inv := by
  have key : ∀ g, tcbLabelOf lbl = g → (g = .tcbConfigure → lbl.val = 5) ∧ (g = .tcbSetSchedParams → lbl.val = 8) ∧
      (g = .tcbSetTimeoutEndpoint → lbl.val = 9) ∧ (g = .tcbSetIPCBuffer → lbl.val = 10) ∧
      (g = .tcbSetSpace → lbl.val = 11) := by
    intro g hg
    subst hg
    unfold tcbLabelOf
    by_cases h2 : lbl.val = 2
    · rw [if_pos h2]; simp [h2]
    rw [if_neg h2]
    by_cases h3 : lbl.val = 3
    · rw [if_pos h3]; simp [h3]
    rw [if_neg h3]
    by_cases h4 : lbl.val = 4
    · rw [if_pos h4]; simp [h4]
    rw [if_neg h4]
    by_cases h5 : lbl.val = 5
    · rw [if_pos h5]; simp [h5]
    rw [if_neg h5]
    by_cases h6 : lbl.val = 6
    · rw [if_pos h6]; simp [h6]
    rw [if_neg h6]
    by_cases h7 : lbl.val = 7
    · rw [if_pos h7]; simp [h7]
    rw [if_neg h7]
    by_cases h8 : lbl.val = 8
    · rw [if_pos h8]; simp [h8]
    rw [if_neg h8]
    by_cases h9 : lbl.val = 9
    · rw [if_pos h9]; simp [h9]
    rw [if_neg h9]
    by_cases h10 : lbl.val = 10
    · rw [if_pos h10]; simp [h10]
    rw [if_neg h10]
    by_cases h11 : lbl.val = 11
    · rw [if_pos h11]; simp [h11]
    rw [if_neg h11]
    by_cases h12 : lbl.val = 12
    · rw [if_pos h12]; simp [h12]
    rw [if_neg h12]
    by_cases h13 : lbl.val = 13
    · rw [if_pos h13]; simp [h13]
    rw [if_neg h13]
    by_cases h14 : lbl.val = 14
    · rw [if_pos h14]; simp [h14]
    rw [if_neg h14]
    by_cases h15 : lbl.val = 15
    · rw [if_pos h15]; simp [h15]
    rw [if_neg h15]
    by_cases h20 : lbl.val = 20
    · rw [if_pos h20]; simp [h20]
    rw [if_neg h20]
    by_cases h21 : lbl.val = 21
    · rw [if_pos h21]; simp [h21]
    rw [if_neg h21]
    simp
  obtain ⟨k1, k2, k3, k4, k5⟩ := h
  refine specDec_thread_noPre ?_ ?_ ?_ ?_ ?_ <;> intro e
  · exact k1 ((key _ (hlbl.symm.trans e)).1 rfl)
  · exact k2 ((key _ (hlbl.symm.trans e)).2.1 rfl)
  · exact k3 ((key _ (hlbl.symm.trans e)).2.2.1 rfl)
  · exact k4 ((key _ (hlbl.symm.trans e)).2.2.2.1 rfl)
  · exact k5 ((key _ (hlbl.symm.trans e)).2.2.2.2 rfl)

set_option maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
/-- **The Thread cap, `JAt` after** (module docstring): every label proved at
`J` (no per-op `JPostHyp`, no X-level `TcbXIpc`). -/
theorem decode_invocation_threadJ_step [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (hFl : FlagsRel Z.T (L.mem s) σ) (hfnz : FrNZ Z.th (L.mem s))
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
    (hXc : XcRel Z.th (L.mem s) x0 x1 x2 excaps) (hnc : NcHyp (st := st) Z.th s σ x0 x1 x2)
    (hnc0 : ∀ sl : Fl4Spec.CslotPtr, AbsSlot Z.th sl → x0 = cslotAddr sl → isUt (capV (L.mem s) x0) = true →
      NoChildrenRel (st := st) s σ x0 sl)
    (hcapC : x1 ≠ 0#u64 → ∀ q b, capV (L.mem s) x1 = .SchedContext q b → q ∈ Z.C)
    (hA5 : ArgRel (st := st) s σ ct buf buffer 5) (hGb : GetBpHyp (st := st) s ct p)
    (hFJ : lbl = fl4_abi.label.TCBReadFPU → FpuFrameJHyp (L := L) Z s σ x0)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hidS : ∀ (sl' : Fl4Spec.CslotPtr) q, AbsSlot Z.th sl' → capV (L.mem s) (cslotAddr sl') = .Thread q →
      q ≠ L.idleW s)
    (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf) (hl : argsU.length ≤ 120)
    (hJDP : JDelParts (L := L) arI AR Z.th) (hsg : SpecGlob σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hTA : TimeAgree arI) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.Thread p)
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ Z.T := J.thT p hp
  -- WriteRegisters: the caller's buffer mapped (`lookup_buf_full`, `BufCover`), the arguments after its restart
  have hcur : σ.curThread = ct.bv := (J.curEq hct).1
  have hctH : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hctT : ct ∈ Z.T := J.thT ct hctH
  have hbm : buf ≠ 0#u64 → ∃ sp, BufMap Z.B buf sp := by
    intro hb0
    obtain ⟨x, hk, hwx⟩ := J.buf ct hctT
    have hL := lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 hctH hk (J.xferH.1) false
    rw [hbuf, WP.spec_ok] at hL
    cases hq : Endp.ipcBufOf false x with
    | none => exact absurd (hL.1.2 hq) hb0
    | some q => exact ⟨q, J.xferH.2.1 ct hctT x false q hk hq buf (hL.2 hwx q hq)⟩
  have hWR : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s1 ct buf i = ok x := by
    intro s1 h1 i x hx
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hx
    obtain ⟨sp, hsp⟩ : ∃ sp, buf ≠ 0#u64 → BufMap Z.B buf sp := by
      by_cases hb : buf = 0#u64
      · exact ⟨0, fun h => absurd hb h⟩
      · obtain ⟨sp, h⟩ := hbm hb; exact ⟨sp, fun _ => h⟩
    rw [J.argsRestart (J.xferH.2.2) hctT hctH hsp (by omega) h1]
    exact hargs i x hx
  -- the cap installs' deletion at `J` (as `decode_invocation_cnodeJ_stepsL`)
  have hHp := tcbInsW_wjl (L := L) (Z := Z) (H := H) (Cs := Cs) arI hT hJDP.archRef hJDP.arKeep hJDP.vt
    hJDP.thr hnd hPP hARI.toMask
  have hP0 := J.ppr0_start arI hni hRd0 hnq
  have hR : RestartWJ (st := st) Z s ar σ (WJL (L := L) arI AR Z H Cs (L.ksb s)) :=
    fun _ hct s1 σ1 h1 h2 => WJL.restart arI J hni hsg hP0 hLv hct s1 σ1 h1 h2
  by_cases h9 : lbl = fl4_abi.label.TCBSetTimeoutEndpoint
  · subst h9
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_timeoutJ arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
        (hstall' p) call sl hAs extra x0 x1 x2 hx0 excaps hXc _ blk don ci buffer)
  by_cases h11 : lbl = fl4_abi.label.TCBSetSpace
  · subst h11
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_spaceJ arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct
        argsU hlen hargs (hstall' p) call sl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc blk don ci buffer)
  by_cases h10 : lbl = fl4_abi.label.TCBSetIPCBuffer
  · subst h10
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_ipcJ arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct
        hct argsU hlen hargs (hstall' p) call sl hAs extra x0 x1 x2 hx0 excaps hXc hnc0 hfnz blk don ci buffer)
  by_cases h5 : lbl = fl4_abi.label.TCBConfigure
  · subst h5
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_configureJ arI s ar σ J hni hsg hP0 hHp hR p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct
        hct argsU hlen hargs (hstall' p) call sl hAs extra x0 x1 x2 hx0 hx1 hx2 excaps hXc hnc hfnz blk don ci buffer)
  -- the first extra cap's thread among the TCBs (as `decode_invocation_threadJAt`)
  have hcapT : x0 ≠ 0#u64 → ∀ q, capV (L.mem s) x0 = .Thread q → q ∈ Z.T := by
    intro hx q hc
    have h0 := hXc.2 0 x0 rfl
    obtain ⟨e, he⟩ : ∃ e, excaps[0]? = some e := by
      rcases excaps with _ | ⟨e, rest⟩
      · exact absurd (h0.1.2 (by simp)) hx
      · exact ⟨e, rfl⟩
    obtain ⟨hxe, -, ps, hps, hpe⟩ := h0.2 e he
    have hA0 : AbsSlot Z.th e.2 := ⟨ps, hpe, Or.inl hps⟩
    exact J.thT q (show CapValid Z.th (.Thread q) from
      J.xtop.rel.2.1.2.1.abs hA0 (by rw [← hxe, capAt_capV, hc]))
  by_cases h8 : lbl = fl4_abi.label.TCBSetSchedParams
  · subst h8
    exact xcapP_of_tcb arI s ar σ hJ0 _ length (cslotAddr sl) p blk call don fp buf extra ct hct slbl _ ci sl excaps
      buffer (tcb_set_sched_paramsJ arI s ar σ J hni hsg hP0 hHp hR hT hARI.toARKeep hTA p hp slbl
        (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hpI (hstall' p) call sl hAs hsc extra
        x0 x1 x2 hx0 hx1 hx2 excaps hXc hcapT hcapC blk don ci buffer)
  have hv : ∀ {c : U64}, lbl ≠ c → lbl.val ≠ c.val := fun hn e => hn (UScalar.eq_of_val_eq e)
  have hnpT := thread_noPre_of (fp := fp) (args := argsU.map UScalar.bv) (ci := ci) (sl := sl) (excaps := excaps)
    (buffer := buffer) (σ := σ) (p := p) hlbl
    ⟨by have := hv h5; simpa [fl4_abi.label.TCBConfigure] using this,
      by have := hv h8; simpa [fl4_abi.label.TCBSetSchedParams] using this,
      by have := hv h9; simpa [fl4_abi.label.TCBSetTimeoutEndpoint] using this,
      by have := hv h10; simpa [fl4_abi.label.TCBSetIPCBuffer] using this,
      by have := hv h11; simpa [fl4_abi.label.TCBSetSpace] using this⟩
  refine XCap.toPN arI (decode_invocation_threadX arI s ar σ hJ0 lbl length (cslotAddr sl) p blk call don fp buf extra
    ct hct slbl hlbl _ ci sl excaps buffer hext (hstall' p) hNative
    {
      readRegisters := fun h => by
        subst h
        exact tcb_read_regsJ arI s ar σ J hni p hpT hpI slbl (by rw [hlbl]; simp [tcbLabelOf])
          length buf ct hct argsU hlen hargs (hstall' p) call (cslotAddr sl) extra blk don ci sl excaps buffer,
      writeRegisters := fun h => by
        subst h
        exact tcb_write_regsJ arI hT hmb s ar σ J hni p hpT (cslotAddr sl) hAs.isSlot (by rw [capAt_capV, hsc]) slbl
          (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen hargs hbm hWR (hstall' p) call
          (cslotAddr sl) extra blk don ci sl excaps buffer,
      copyRegisters := fun h => by
        subst h
        exact tcb_copy_regsJ arI hT hmb s ar σ J hni hidS p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf
          ct hct argsU hlen hargs hstall' call sl hAs hsc extra x0 x1 x2 hx0 excaps hXc blk don ci buffer,
      configure := fun h => absurd h h5,
      setPriority := fun h => by
        subst h
        exact tcb_set_prioJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen
          hargs (hstall' p) call sl extra x0 x1 x2 hx0 excaps hXc hcapT blk don ci buffer,
      setMCPriority := fun h => by
        subst h
        exact tcb_set_mcpJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU hlen
          hargs (hstall' p) call sl extra x0 x1 x2 hx0 excaps hXc hcapT blk don ci buffer,
      setSchedParams := fun h => absurd h h8,
      setTimeoutEndpoint := fun h => absurd h h9,
      setIPCBuffer := fun h => absurd h h10,
      setSpace := fun h => absurd h h11,
      suspend := fun h => by
        subst h
        exact tcb_suspendJ arI s ar σ J hni p hpT hpI slbl (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) ct hct _
          blk call don _ ci sl excaps buffer,
      resume := fun h => by
        subst h
        exact tcb_resumeJ arI hT hPP.minBudget s ar σ J hni p hpT (cslotAddr sl) hAs.isSlot (by rw [capAt_capV, hsc]) slbl
          (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) ct hct _ blk call don _ ci sl excaps buffer,
      bindNotification := fun h => by
        subst h
        exact tcb_bind_ntfnJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf (hstall' p) ct
          hct hAs.isSlot hsc call (cslotAddr sl) extra x0 x1 x2 hx0 excaps hXc blk don _ ci sl buffer,
      unbindNotification := fun h => by
        subst h
        exact tcb_unbind_ntfnJ arI s ar σ J hni p hpT slbl (by rw [hlbl]; simp [tcbLabelOf]) (hstall' p) ct hct
          length buf call (cslotAddr sl) extra blk don _ ci sl excaps buffer,
      setBreakpoint := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setBreakpoint by
          simp [tcbExtOf])
        exact tcb_set_bpJ arI s ar σ J hni p hpT slbl hg he length buf ct hct (hstall' p) buffer hA5 call
          (cslotAddr sl) extra blk don _ ci sl excaps,
      getBreakpoint := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .getBreakpoint by
          simp [tcbExtOf])
        exact tcb_get_bpJ arI s ar σ J hni p slbl hg he length buf ct hct (hstall' p) buffer
          (fun i hi => hA5 i (by omega)) hGb call (cslotAddr sl) extra blk don _ ci sl excaps,
      unsetBreakpoint := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .unsetBreakpoint by
          simp [tcbExtOf])
        exact tcb_unset_bpJ arI s ar σ J hni p hpT slbl hg he length buf ct hct
          (hstall' p) buffer (fun i hi => hA5 i (by omega)) call (cslotAddr sl) extra blk don _ ci sl excaps,
      configureSingleStepping := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf])
          (show tcbExtOf _ = some .configureSingleStepping by simp [tcbExtOf])
        exact tcb_single_stepJ arI s ar σ J hni p hp slbl hg he length buf ct hct (hstall' p) buffer
          (fun i hi => hA5 i (by omega)) call (cslotAddr sl) extra blk don _ ci sl excaps,
      setTLSBase := fun h => by
        subst h
        exact tcb_set_tlsJ arI s ar σ J hni p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU
          hlen hargs hcw (hstall' p) call (cslotAddr sl) extra blk don ci sl excaps buffer,
      setFlags := fun h => by
        subst h
        exact tcb_set_flagsJ arI s ar σ J hni hFl p hp slbl (by rw [hlbl]; simp [tcbLabelOf]) length buf ct hct argsU
          hlen hargs (hstall' p) hARI.toARKeep call (cslotAddr sl) extra blk don ci sl excaps buffer,
      readFPU := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .readFpu by
          simp [tcbExtOf])
        exact tcb_read_fpuJ arI s ar σ J hni hARI.toARKeep p hpT slbl hg he length buf ct hct argsU hlen hargs
          (hstall' p) call (cslotAddr sl) extra x0 x1 x2 hx0 excaps hXc (hFJ rfl) blk don ci sl buffer,
      writeFPU := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .writeFpu by
          simp [tcbExtOf])
        exact tcb_write_fpuJ arI s ar σ J hni hARI.toARKeep p hpT slbl hg he length buf ct hct argsU hlen hargs
          (hstall' p) call (cslotAddr sl) extra x0 x1 x2 hx0 excaps hXc blk don ci sl buffer,
      setTimer := fun h => by
        subst h
        obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf]) (show tcbExtOf _ = some .setTimer by
          simp [tcbExtOf])
        exact tcb_set_timerJ arI s ar σ J hni p hpT slbl hg he length buf ct hct argsU hlen hargs (hstall' p) call
          (cslotAddr sl) extra blk don ci sl excaps buffer }) hnpT

end

end

end Fl4Proofs.P3
