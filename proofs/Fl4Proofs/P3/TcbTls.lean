/-
P3 (DESIGN.md §9), TCB invocations: **`SetTLSBase`** (`tcb_set_tls_refines`),
`TcbOK` at FL4's label `TCBSetTLSBase`, against l4v's `decode_set_tls_base`
and `invoke_tcb (SetTLSBase ..)`.

FL4 sets the caller's state to `Restart`, writes the target's `FS_BASE`
register word (offset `256 + 8·22` = 432 of the TCB, past its slots) with
the sanitised value, and calls `reschedule_required` when the target is the
current thread. The spec's `as_user` writes the register of the target's
user context (its caps unchanged). The scheduler step, `reschedule_required`
on both sides, is the hypothesis `TlsResHyp` (for the scheduler's proofs).
-/
import Fl4Proofs.P3.TcbDecode
import Fl4Proofs.P3.IoPortTop
import Fl4Proofs.P3.NtfnSpec
import Fl4Proofs.P3.CancelKSub
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The TCB word of register `TLS_BASE` (`FS_BASE`, 22). -/
def tlsA (t : U64) : U64 :=
  core.num.U64.wrapping_add (core.num.U64.wrapping_add t 256#u64) (core.num.U64.wrapping_mul 22#u64 8#u64)

theorem tlsA_val {t : U64} (h : t.val + 4096 ≤ 2 ^ 64) : (tlsA t).val = t.val + 432 := by
  unfold tlsA
  rw [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
  simp [U64.size, U64.numBits]; omega

/-- FL4's `regs::sanitise` of `TLS_BASE` is the spec's `sanitise_register`
of `FS_BASE`. -/
theorem sanitise_tls (v : U64) : ∃ w : U64, regs.sanitise layout.reg.TLS_BASE v = ok w ∧
    w.bv = Fl4Spec.sanitiseRegister false Fl4Spec.tlsBaseRegister v.bv := by
  unfold regs.sanitise
  simp only [layout.reg.TLS_BASE, layout.reg.FS_BASE, layout.reg.FAULT_IP, layout.reg.NEXT_IP, layout.reg.FLAGS,
    u64_eq_iff]
  simp only [show (22#u64 : U64).val = 22 from rfl, show (17#u64 : U64).val = 17 from rfl,
    show (14#u64 : U64).val = 14 from rfl, show (13#u64 : U64).val = 13 from rfl, Nat.reduceEqDiff, ↓reduceIte]
  unfold Fl4Spec.sanitiseRegister Fl4Spec.tlsBaseRegister
  simp only [reduceCtorEq, or_true, ↓reduceIte, or_false]
  have e1 : (140737488355327 : BitVec 64).toNat = 140737488355327 := rfl
  have e2 : (18446603336221196288 : BitVec 64).toNat = 18446603336221196288 := rfl
  have g1 : v > 140737488355327#u64 ↔ v.bv > 140737488355327 := by
    rw [GT.gt, GT.gt, BitVec.lt_def, e1, UScalar.bv_toNat]; scalar_tac
  have g2 : v < 18446603336221196288#u64 ↔ v.bv < 18446603336221196288 := by
    rw [BitVec.lt_def, e2, UScalar.bv_toNat]; scalar_tac
  simp only [← g1, ← g2]
  by_cases h1 : v > 140737488355327#u64 <;> by_cases h2 : v < 18446603336221196288#u64 <;>
    simp only [h1, h2, and_self, and_true, and_false, ↓reduceIte, bind_ok] <;> exact ⟨_, rfl, rfl⟩


theorem let_pair_spec {α β γ : Type} (x : α) (y : β) (f : α → Result (γ × α)) (Q : γ × α × β → Prop)
    (h : (do let (r, s2) ← f x; ok (r, s2, y)) ⦃ res => Q res ⦄) :
    (let (s1, a1) := (x, y); do let (r, s2) ← f s1; ok (r, s2, a1)) ⦃ res => Q res ⦄ := h

theorem ucast64_self (x : BitVec 64) : Fl4Spec.ucast 64 x = x := by simp [Fl4Spec.ucast]

/-! ## The spec -/

section
open Fl4Spec

theorem ksub_updK_tcb {σ : State Unit} {t : ObjRef} {x y : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    KSub σ (Notif.updK σ t (.tcb y)) := by
  intro o
  by_cases ho : o = t
  · subst ho
    refine ⟨fun r cs h _ => ?_, fun _ _ => ⟨x, hk⟩, fun h => ?_⟩
    · simp [Notif.updK] at h
    · rw [hk] at h; cases h
  · simp only [Notif.updK, Function.update_of_ne ho]; exact KSub.refl σ o

/-- The CSpace relation does not look at a TCB's registers. -/
theorem StateRel.set_reg {th : TypedHeap} {m : U64 → U64} {σ : State Unit} (hR : StateRel th m σ)
    {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (r : Register) (v : Word) :
    StateRel th m (Notif.updK σ t (.tcb (Notif.setReg x r v))) := by
  refine ⟨fun p rr hp => ?_, fun t' ht' => ?_⟩
  · obtain ⟨cs, hk', hwf, hs⟩ := hR.cnode p rr hp
    have hne : p.bv ≠ t := by intro e; rw [e, hk] at hk'; cases hk'
    exact ⟨cs, by simp only [Notif.updK, Function.update_of_ne hne]; exact hk', hwf, hs⟩
  · obtain ⟨tcb', hk', hs⟩ := hR.tcb t' ht'
    by_cases he : t'.bv = t
    · rw [he, hk] at hk'
      cases hk'
      exact ⟨Notif.setReg x r v, by simp only [Notif.updK, he, Function.update_self], fun i hi => hs i hi⟩
    · exact ⟨tcb', by simp only [Notif.updK, Function.update_of_ne he]; exact hk', hs⟩

theorem setThreadState_curThread {σ σ1 : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    {ts : ThreadState} (h : setThreadState (Z := Unit) t ts σ = ({((), σ1)}, False)) : σ1.curThread = σ.curThread := by
  have e : setThreadState (Z := Unit) t ts σ =
      ({((), Notif.stsAct (Notif.updK σ t (.tcb { x with tcbState := ts })) t)}, False) := by
    unfold setThreadState
    rw [Notif.nd_bind_one (Notif.threadSet_eq _ hk)]
    exact Notif.setThreadStateAct_eq _ _
  rw [e] at h
  have := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h))).2
  subst this
  unfold Notif.stsAct; split_ifs <;> rfl

/-- The spec's `SetTLSBase` invocation: `as_user` at the target, then
`reschedule_required` if it is the current thread. -/
theorem invoke_tls_mem {σ1 : State Unit} {t : ObjRef} {x : Tcb} (hk : σ1.kheap t = some (.tcb x)) (v : Word)
    {y : Unit × State Unit}
    (hy : y ∈ ((NonDet.when (t = σ1.curThread) rescheduleRequired)
      (Notif.updK σ1 t (.tcb (Notif.setReg x tlsBaseRegister (sanitiseRegister false tlsBaseRegister v))))).1)
    (blk call don : Bool) :
    ((.ok [], y.2) : Except Unit (List Data) × State Unit) ∈
      ((fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.setTLSBase t v))).run σ1).1 := by
  show _ ∈ ((NonDetE.liftE _).run σ1).1
  refine mem_liftE (x := ([], y.2)) ?_
  refine mem_bind_nd (x := (false, σ1)) rfl ?_
  refine mem_bind_nd (x := ((), _)) (by rw [Notif.asUser_setRegister_eq _ _ hk]; rfl) ?_
  refine mem_bind_nd (x := (σ1.curThread, _)) rfl ?_
  exact mem_bind_nd hy rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem set_reg_tls_eq (s : S) (t v : U64) :
    obj.Tcb.set_reg st t s layout.reg.TLS_BASE v = ok (L.wr s (tlsA t) v) := by
  unfold obj.Tcb.set_reg
  simp [lift, L.write_eq, tlsA, layout.tcb.REGS, layout.reg.TLS_BASE, layout.reg.FS_BASE]

/-- The register write keeps the slot words (offset 432, past the slots). -/
theorem tls_slots {th : TypedHeap} (hP : Placed th) (s : S) {t : U64} (v : U64) (ht : th t = some .tcb) :
    SlotsSame th (L.mem s) (L.mem (L.wr s (tlsA t) v)) := by
  have htf := hP.fits t _ ht
  have hta := hP.align t _ ht
  have hv : (tlsA t).val = t.val + 432 := tlsA_val (by simp [objSize] at htf; omega)
  refine slotsSame_wr hP s v (by unfold P1.Aligned; rw [hv]; omega) (fun a ha => ?_)
  obtain ⟨p, k, hk, h1, h2, h3⟩ := slot_in_object hP ha
  rw [hv]
  by_cases hpt : p = t
  · subst hpt; rw [ht] at hk; cases hk
    have := h3 rfl; simp [tcbSlots] at this; omega
  · have e4 : objSize ObjKind.tcb = 4096 := rfl
    rcases hP.disj p t k .tcb hk ht hpt with h | h <;> omega

theorem cur_thread_eq (s : S) :
    sched.cur_thread st s = ok (L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)) := by
  obtain ⟨v, hv, rfl⟩ := spec_exists (cur_thread_spec' (L := L) s); exact hv

theorem cur_ne_action (s : S) :
    (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val := by
  unfold P1.LawfulStore.nodeAt
  rw [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_add_val_eq]
  simp only [layout.node.CUR_THREAD, layout.node.SCHED_ACTION]
  simp [U64.size, U64.numBits]; omega

/-- A word of a TCB of the typed heap is not a word outside every object. -/
theorem out_ne {th : TypedHeap} {A0 t : U64} (hO : OutsideObjects th A0) (ht : th t = some .tcb) {w : U64}
    (hw : t.val ≤ w.val ∧ w.val < t.val + 4096) : w.val ≠ A0.val := by
  have := hO.2 t _ ht
  have e4 : objSize ObjKind.tcb = 4096 := rfl
  rw [e4] at this; omega

/-- **The scheduler step of SetTLSBase** (for the scheduler's proofs):
FL4's `reschedule_required` after the restart and the register write of the
current thread, and the spec's `reschedule_required` after `as_user`. -/
def TlsResHyp (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  ∀ s1 σ1 (x : Fl4Spec.Tcb) (v : U64), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) → σ1.kheap ct.bv = some (.tcb x) →
    sched.reschedule_required st (L.wr s1 (tlsA ct) v) ⦃ s3 =>
      SlotsSame th (L.mem (L.wr s1 (tlsA ct) v)) (L.mem s3) ∧
      ∃ y ∈ (Fl4Spec.rescheduleRequired (Z := Unit)
          (Notif.updK σ1 ct.bv (.tcb (Notif.setReg x Fl4Spec.tlsBaseRegister v.bv)))).1,
        y.2.kheap = (Notif.updK σ1 ct.bv (.tcb (Notif.setReg x Fl4Spec.tlsBaseRegister v.bv))).kheap ∧
        y.2.cdt = σ1.cdt ∧ y.2.isOriginalCap = σ1.isOriginalCap ⦄

/-- **`tcb::decode` at `TCBSetTLSBase`** (`TcbOK`): the spec's
`decode_set_tls_base`, the restart and `invoke_tcb (SetTLSBase ..)`, with
the CSpace relation and `FinInv` after. -/
theorem tcb_set_tls_refines (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (p : U64) (hp : th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetTLSBase)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcw : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (hres : TlsResHyp (L := L) th s σ ct)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKF (L := L) arI s ar σ fl4_abi.label.TCBSetTLSBase p ⟨length, buf, call, slot, extra⟩ blk call don slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  have hdec0 : (specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer) =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeSetTlsBase (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKF tcb.decode
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
    refine ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩
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
  unfold tcb.restart_caller; rw [hct]; simp only [bind_ok]
  obtain ⟨s1, hs1, hS1, hc1⟩ := spec_exists (WP.spec_and
    (set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact) (set_thread_state_cases s ct sched.TS_RESTART))
  rw [hs1]; simp only [bind_ok]
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
  -- the spec: restart, then the target's TCB
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
  obtain ⟨σ1, hst1, hR1, hV1, hM1, hC1, hcdt1, hio1⟩ := restart_rel hR hV hM hC hS1 (t := ct.bv) hkt .restart
  have hcur1 : σ1.curThread = ct.bv := by rw [setThreadState_curThread hkt hst1, hcur]
  obtain ⟨x, hkx, -⟩ := hR1.tcb p hp
  have hS2 := tls_slots (L := L) hP s1 w hp
  have hS12 := hS1.trans hS2
  have hR2 := (hR1.set_reg hkx Fl4Spec.tlsBaseRegister w.bv).of_caps (fun a ha => hS2.capAt ha)
  have hK2 : KSub σ (Notif.updK σ1 p.bv (.tcb (Notif.setReg x Fl4Spec.tlsBaseRegister w.bv))) :=
    (ksub_of_eq (setThreadState_nks _ _) hst1).trans (ksub_updK_tcb hkx)
  by_cases hpc : p = ct
  · subst hpc
    simp only [decide_true, ↓reduceIte]
    obtain ⟨s3, hs3, hS3, y, hy, hk3, hcdt3, hio3⟩ := spec_exists (hres s1 σ1 x w hs1 hst1 hkx)
    rw [hs3]; simp only [bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inr
    have hS := hS12.trans hS3
    refine ⟨_, DecOut.of_eq hdec, σ1, by rw [hcur]; exact hst1, (.ok [], y.2), ?_, th, G,
      Or.inl ⟨rfl, [], rfl⟩, hP, ⟨(hR2.of_kheap hk3).of_caps (fun a ha => hS3.capAt ha),
        hV1.of_caps (fun a ha => (hS2.trans hS3).capAt ha),
        hM1.of_same (hS2.trans hS3), hC1.of_same (hS2.trans hS3) hcdt3 hio3,
        MdbInv.of_same hM hI hS⟩,
      hFI.of_same hM hS (hK2.trans (KSub.of_kheap hk3)), MdbOKV.of_same hM hS hFR⟩
    refine invoke_tls_mem hkx y0.bv ?_ blk call don
    rw [← hwb, hcur1]
    simp only [Fl4Spec.NonDet.when, if_pos trivial]
    exact hy
  · have hne : decide (p = ct) = false := by simp [hpc]
    rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine (WP.spec_ok _).2 ?_
    apply Or.inr
    refine ⟨_, DecOut.of_eq hdec, σ1, by rw [hcur]; exact hst1, (.ok [], _), ?_, th, G,
      Or.inl ⟨rfl, [], rfl⟩, hP, ⟨hR2, hV1.of_caps (fun a ha => hS2.capAt ha), hM1.of_same hS2,
        hC1.of_same hS2 rfl rfl, MdbInv.of_same hM hI hS12⟩, hFI.of_same hM hS12 hK2, MdbOKV.of_same hM hS12 hFR⟩
    refine invoke_tls_mem (y := ((), Notif.updK σ1 p.bv (.tcb (Notif.setReg x Fl4Spec.tlsBaseRegister w.bv))))
      hkx y0.bv ?_ blk call don
    have : ¬ p.bv = σ1.curThread := fun e => hpc (UScalar.eq_of_val_eq (by
      rw [hcur1] at e; have := congrArg BitVec.toNat e; simpa using this))
    rw [← hwb]
    simp only [Fl4Spec.NonDet.when, if_neg this]
    exact Set.mem_singleton _

end

end

end Fl4Proofs.P3
