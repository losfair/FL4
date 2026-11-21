/-
P3 (DESIGN.md §9): **`handle_invocation`'s reply tails at `J`** (for
XTopJointEntry's `handle_invocation_refinesJ`, replacing HandleTopX's
`ReplyHypMX` at `JAt`):

* `JAtZ.flTailJ`: FL4's success tail for an empty result (`flTail`: when the
  current thread is still `Restart`, `reply_success_empty` when called, then
  `Running`) against the spec's `specTail _ _ []`, from `JAtZ` with the
  thread current to `JAt` (the badge and message-info writes by
  `JAtZ.replyTailJ` with no words, `Running` by `JAtZ.runJ`).
* `setmrs_lf_gen`, `error_mrs_gen`: ReplyFailX's `setmrs_lf_inv` /
  `error_mrs_inv` for any invariant `I` of the state and the words so far
  that `set_mr` of the next word keeps.
* `JAtZ.replyErrJ`: FL4's `reply_error` (the badge, `error_mrs` by
  `error_mrs_gen` with `JAtZ.setmrJ`, the debug word of
  `KERNEL_INVOCATION_REPORT_ERROR_IPC` by `JAtZ.userWrJ`, the message info)
  against the spec's `fl4ReplyFromKernelError true` (`fl4ReplyErr_eq`), from
  `JAtZ` with the thread current to `JAt`; the buffer facts from the `JAtZ` state
  itself (BufJ's `JAtZ.xferH`).
* `JAtZ.replyFailJ`: the error reply when called (`ReplyHypMX.fail`'s
  program), at `JAt`.
-/
import Fl4Proofs.P3.XTopJointData
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## `error_mrs` for any invariant kept by `set_mr` -/

section ErrMrsGen
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable (ct : U64) (buf : Option Fl4Spec.ObjRef) (w : U64) (I : S → List Fl4Spec.Word → Prop)
  (step : ∀ (s1 : S) (ms1 : List Fl4Spec.Word), I s1 ms1 → ∀ (i : U64), i.val = ms1.length →
    ms1.length < 120 → ∀ v : U64, msg.set_mr st s1 ct w i v ⦃ r => r.1.val = mrLen buf (ms1.length + 1) ∧
      I r.2 (ms1 ++ [v.bv]) ⦄)

include step in
set_option maxHeartbeats 4000000 in
/-- **`set_mrs_lookup_failure_at` from MR 1** keeps `I` (ReplyFailX's
`setmrs_lf_inv`). -/
theorem setmrs_lf_gen (s : S) (ms : List Fl4Spec.Word) (hms : ms.length = 1) (hI : I s ms)
    (lf : error.LookupFault) (lf' : Fl4Spec.LookupFailure) (hlf : LookupFaultRel lf lf') :
    faults.set_mrs_lookup_failure_at st s ct w lf 1#u64 ⦃ r =>
      r.1.val = mrLen buf (ms ++ Fl4Spec.msgFromLookupFailure lf').length ∧
      I r.2 (ms ++ Fl4Spec.msgFromLookupFailure lf') ⦄ := by
  unfold faults.set_mrs_lookup_failure_at faults.set_mrs_lookup_failure
  cases lf with
  | InvalidRoot =>
    cases lf' <;> (try simp only [LookupFaultRel] at hlf)
    simp only [error.LookupFault.type_code, bind_ok]
    refine WP.spec_bind (step s ms hI 1#u64 (by rw [hms]; rfl) (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨h1, h2⟩
    show (ok (i1, s1) : Result (U64 × S)) ⦃ _ ⦄
    rw [WP.spec_ok]
    have hl : ms ++ Fl4Spec.msgFromLookupFailure .invalidRoot = ms ++ [(fl4_abi.consts.lookup.InvalidRoot).bv] := by
      simp [Fl4Spec.msgFromLookupFailure, fl4_abi.consts.lookup.InvalidRoot]
    rw [hl]
    exact ⟨by rw [h1]; simp, h2⟩
  | MissingCapability bl =>
    cases lf' <;> (try simp only [LookupFaultRel] at hlf)
    rename_i n
    simp only [error.LookupFault.type_code, bind_ok]
    refine WP.spec_bind (step s ms hI 1#u64 (by rw [hms]; rfl) (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨-, h2⟩
    simp only [lift, bind_ok]
    have e2 : (core.num.U64.wrapping_add (1#u64 : U64) 1#u64).val = (ms ++ [(fl4_abi.consts.lookup.MissingCapability).bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_mono (step s1 _ h2 _ e2 (by simp [hms]) bl) ?_
    rintro ⟨i2, s2⟩ ⟨g1, g2⟩
    have hl : ms ++ Fl4Spec.msgFromLookupFailure (.missingCapability n) =
        ms ++ [(fl4_abi.consts.lookup.MissingCapability).bv] ++ [bl.bv] := by
      simp [Fl4Spec.msgFromLookupFailure, hlf, fl4_abi.consts.lookup.MissingCapability]
    rw [hl]
    exact ⟨by rw [g1]; simp, g2⟩
  | DepthMismatch found left =>
    cases lf' <;> (try simp only [LookupFaultRel] at hlf)
    rename_i n m
    simp only [error.LookupFault.type_code, bind_ok]
    refine WP.spec_bind (step s ms hI 1#u64 (by rw [hms]; rfl) (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨-, h2⟩
    simp only [lift, bind_ok]
    have e2 : (core.num.U64.wrapping_add (1#u64 : U64) 1#u64).val = (ms ++ [(fl4_abi.consts.lookup.DepthMismatch).bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_bind (step s1 _ h2 _ e2 (by simp [hms]) left) ?_
    rintro ⟨i2, s2⟩ ⟨-, g2⟩
    have e3 : (core.num.U64.wrapping_add (1#u64 : U64) 2#u64).val =
        (ms ++ [(fl4_abi.consts.lookup.DepthMismatch).bv] ++ [left.bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_mono (step s2 _ g2 _ e3 (by simp [hms]) found) ?_
    rintro ⟨i3, s3⟩ ⟨k1, k2⟩
    have hl : ms ++ Fl4Spec.msgFromLookupFailure (.depthMismatch n m) =
        ms ++ [(fl4_abi.consts.lookup.DepthMismatch).bv] ++ [left.bv] ++ [found.bv] := by
      simp [Fl4Spec.msgFromLookupFailure, hlf.1, hlf.2, fl4_abi.consts.lookup.DepthMismatch]
    rw [hl]
    exact ⟨by rw [k1]; simp, k2⟩
  | GuardMismatch g left gs =>
    cases lf' <;> (try simp only [LookupFaultRel] at hlf)
    rename_i n gl
    have hg : g.val < 2 ^ gs.val := hlf.2.2.1
    simp only [error.LookupFault.type_code, bind_ok]
    refine WP.spec_bind (step s ms hI 1#u64 (by rw [hms]; rfl) (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨-, h2⟩
    simp only [lift, bind_ok]
    have e2 : (core.num.U64.wrapping_add (1#u64 : U64) 1#u64).val = (ms ++ [(fl4_abi.consts.lookup.GuardMismatch).bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_bind (step s1 _ h2 _ e2 (by simp [hms]) left) ?_
    rintro ⟨i2, s2⟩ ⟨-, g2⟩
    have e3 : (core.num.U64.wrapping_add (1#u64 : U64) 2#u64).val =
        (ms ++ [(fl4_abi.consts.lookup.GuardMismatch).bv] ++ [left.bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_bind (step s2 _ g2 _ e3 (by simp [hms]) g) ?_
    rintro ⟨i3, s3⟩ ⟨-, k2⟩
    have e4 : (core.num.U64.wrapping_add (1#u64 : U64) 3#u64).val =
        (ms ++ [(fl4_abi.consts.lookup.GuardMismatch).bv] ++ [left.bv] ++ [g.bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_mono (step s3 _ k2 _ e4 (by simp [hms]) gs) ?_
    rintro ⟨i4, s4⟩ ⟨j1, j2⟩
    have hgb : Fl4Spec.ofBl gl = g.bv := by
      rw [hlf.2.1, ofBl_bitsOf_eq, Nat.mod_eq_of_lt hg]; exact BitVec.eq_of_toNat_eq (by simp)
    have hgl : gl.length = gs.val := by rw [hlf.2.1, length_bitsOf]
    have hl : ms ++ Fl4Spec.msgFromLookupFailure (.guardMismatch n gl) =
        ms ++ [(fl4_abi.consts.lookup.GuardMismatch).bv] ++ [left.bv] ++ [g.bv] ++ [gs.bv] := by
      simp only [Fl4Spec.msgFromLookupFailure, hgb, hgl, hlf.1, List.append_assoc, List.cons_append,
        List.nil_append, fl4_abi.consts.lookup.GuardMismatch, ofNat_val]
      rfl
    rw [hl]
    exact ⟨by rw [j1]; simp, j2⟩

include step in
set_option maxHeartbeats 8000000 in
/-- **`error_mrs` keeps `I`** (ReplyFailX's `error_mrs_inv`): the words of
`msg_from_syscall_error`. -/
theorem error_mrs_gen (s : S) (hI : I s []) (e : error.SysError) (e' : Fl4Spec.SyscallError)
    (he : ErrRel (.Sys e) e') :
    syscall.error_mrs st s ct w e ⦃ r =>
      r.1.val = mrLen buf (Fl4Spec.msgFromSyscallError e').2.length ∧
      I r.2 (Fl4Spec.msgFromSyscallError e').2 ⦄ := by
  have one : ∀ (v : U64) (ms : List Fl4Spec.Word), ms = [v.bv] →
      msg.set_mr st s ct w 0#u64 v ⦃ r => r.1.val = mrLen buf ms.length ∧ I r.2 ms ⦄ := by
    rintro v ms rfl
    exact step s [] hI 0#u64 rfl (by simp) v
  unfold syscall.error_mrs
  rcases he with h | ⟨n, he, rfl⟩
  swap
  · cases he
    exact one n _ (by simp [Fl4Spec.msgFromSyscallError, ofNat_val])
  cases e <;> cases e' <;> simp only [SysErrRel] at h
  case InvalidArgument.invalidArgument arg n =>
    exact one arg _ (by simp [Fl4Spec.msgFromSyscallError, h, ofNat_val])
  case IllegalOperation.illegalOperation =>
    rw [WP.spec_ok]; exact ⟨by cases buf <;> simp [Fl4Spec.msgFromSyscallError, mrLen], hI⟩
  case AlignmentError.alignmentError =>
    rw [WP.spec_ok]; exact ⟨by cases buf <;> simp [Fl4Spec.msgFromSyscallError, mrLen], hI⟩
  case TruncatedMessage.truncatedMessage =>
    rw [WP.spec_ok]; exact ⟨by cases buf <;> simp [Fl4Spec.msgFromSyscallError, mrLen], hI⟩
  case DeleteFirst.deleteFirst =>
    rw [WP.spec_ok]; exact ⟨by cases buf <;> simp [Fl4Spec.msgFromSyscallError, mrLen], hI⟩
  case RevokeFirst.revokeFirst =>
    rw [WP.spec_ok]; exact ⟨by cases buf <;> simp [Fl4Spec.msgFromSyscallError, mrLen], hI⟩
  case NotEnoughMemory.notEnoughMemory b b' =>
    exact one b _ (by simp [Fl4Spec.msgFromSyscallError, h])
  case RangeError.rangeError mn mx mn' mx' =>
    refine WP.spec_bind (step s [] hI 0#u64 rfl (by simp) mn) ?_
    rintro ⟨i1, s1⟩ ⟨-, h2⟩
    refine WP.spec_mono (step s1 _ h2 1#u64 (by simp) (by simp) mx) ?_
    rintro r ⟨g1, g2⟩
    have hl : (Fl4Spec.msgFromSyscallError (.rangeError mn' mx')).2 = [] ++ [mn.bv] ++ [mx.bv] := by
      simp [Fl4Spec.msgFromSyscallError, h.1, h.2]
    rw [hl]
    exact ⟨by rw [g1]; simp, g2⟩
  case FailedLookup.failedLookup src lf src' lf' =>
    obtain ⟨rfl, hlf⟩ := h
    have core : ∀ v : U64, v.bv = (if src' then 1 else 0) →
        (do
          let (_, s1) ← msg.set_mr st s ct w 0#u64 v
          faults.set_mrs_lookup_failure_at st s1 ct w lf 1#u64) ⦃ r =>
        r.1.val = mrLen buf (Fl4Spec.msgFromSyscallError (.failedLookup src' lf')).2.length ∧
        I r.2 (Fl4Spec.msgFromSyscallError (.failedLookup src' lf')).2 ⦄ := by
      intro v hv
      refine WP.spec_bind (step s [] hI 0#u64 rfl (by simp) v) ?_
      rintro ⟨i1, s1⟩ ⟨-, h2⟩
      have hl : (Fl4Spec.msgFromSyscallError (.failedLookup src' lf')).2 =
          ([] ++ [v.bv]) ++ Fl4Spec.msgFromLookupFailure lf' := by
        simp [Fl4Spec.msgFromSyscallError, hv]
      rw [hl]
      exact setmrs_lf_gen ct buf w I step s1 _ (by simp) h2 lf lf' hlf
    cases src'
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact core 0#u64 (by simp)
    · simp only [↓reduceIte]
      exact core 1#u64 (by simp)

end ErrMrsGen

/-! ## The reply tails at `J` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **FL4's success tail for an empty result at `J`** (module docstring). -/
theorem JAtZ.flTailJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hcur : σ.curThread = ct.bv)
    (call : Bool) :
    flTail (st := st) ct call s a ⦃ res => res.1 = .Ok () ∧
      ∃ z ∈ (specTail call ct.bv [] σ).1, RelTopM (L := L) res.2.1 z.2 ∧ JAt (L := L) arI AR res.2.1 res.2.2 z.2 ⦄ := by
  have hct : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  obtain ⟨htcb, x, hk⟩ := J.xtop.curTcb hcur
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb ct hct
  rw [hk] at hk0; cases hk0
  have hst : (L.mem s (tStA ct)).val = tsCode x.tcbState := hTR.st
  have hss : (L.mem s (P1.stA ct)).val = tsCode x.tcbState := by rw [P1.stA_eq, ← tStA_eq, hst]
  unfold flTail
  refine WP.spec_bind (tcb_state_spec' (st := st) s ct) ?_
  rintro i rfl
  by_cases hr : L.mem s (stA ct) = sched.TS_RESTART
  · rw [if_pos hr]
    have hrs : x.tcbState = .restart := by
      apply tsCode_two
      rw [← hss]
      show (L.mem s (stA ct)).val = 2
      rw [hr]; unfold sched.TS_RESTART; rfl
    rw [specTail_nil hk call, if_pos hrs]
    cases call
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
      refine WP.spec_bind (J.runJ hct hk hrs) ?_
      rintro s2 ⟨Lst', D', J2⟩
      refine (WP.spec_ok _).2 ⟨rfl, ((), stsAct (updK σ ct.bv (.tcb { x with tcbState := .running })) ct.bv), ?_,
        J2.xtop.relTop, _, _, _, _, _, _, J2⟩
      rw [Notif.setThreadState_eq .running hk]; exact Set.mem_singleton _
    · simp only [↓reduceIte]
      have J0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (MrS σ ct.bv x (Endp.ipcBufOf true x) []) := by
        rw [MrS_nil hk]; exact J
      have hR := J0.replyTailJ hct hk hrs (by simp) (fun p _ z hz => by simp [Endp.mrPairs] at hz) 0#u64
        (by cases Endp.ipcBufOf true x <;> rfl) (by decide)
      have e : msg.reply_success_empty st s ct = tcb.reply_words st s ct 0#u64 := by
        unfold msg.reply_success_empty tcb.reply_words; rfl
      rw [e, ← Std.bind_assoc]
      refine WP.spec_bind hR ?_
      intro s5 h5
      have hkN : (Notif.updK σ ct.bv (.tcb (Endp.replyTcbNil x))).kheap ct.bv = some (.tcb (Endp.replyTcbNil x)) := by
        simp [Notif.updK]
      have hz : ((), stsAct (updK (Notif.updK σ ct.bv (.tcb (Endp.replyTcbNil x))) ct.bv
          (.tcb { Endp.replyTcbNil x with tcbState := .running })) ct.bv) ∈
          (specTail true ct.bv [] σ).1 := by
        rw [specTail_nil hk true, if_pos hrs]
        simp only [↓reduceIte]
        rw [Notif.setThreadState_eq .running hkN]; exact Set.mem_singleton _
      have hJ := h5 _ hz
      obtain ⟨Z5, H5, Cs5, Ac5, Lst5, D5, J5⟩ := hJ
      refine (WP.spec_ok _).2 ⟨rfl, _, ?_, J5.xtop.relTop, Z5, H5, Cs5, Ac5, Lst5, D5, J5⟩
      rw [Notif.setThreadState_eq .running hkN]; exact Set.mem_singleton _
  · rw [if_neg hr]
    have hrs : x.tcbState ≠ .restart := by
      intro h
      apply hr
      apply UScalar.eq_of_val_eq
      show (L.mem s (P1.stA ct)).val = _
      rw [hss, h]; unfold sched.TS_RESTART; rfl
    refine (WP.spec_ok _).2 ⟨rfl, ((), σ), ?_, J.xtop.relTop, Z, H, Cs, Ac, Lst, D, J⟩
    rw [specTail_nil hk call, if_neg hrs]; exact Set.mem_singleton _

set_option maxHeartbeats 64000000 in
/-- **FL4's `reply_error` at `J`** (module docstring). -/
theorem JAtZ.replyErrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (hcur : σ.curThread = ct.bv) (e : error.SysError) (e' : Fl4Spec.SyscallError)
    (he : ErrRel (.Sys e) e') :
    syscall.reply_error st s ct e ⦃ s2 =>
      ∃ z ∈ (Fl4Spec.fl4ReplyFromKernelError (Z := Unit) true ct.bv (Fl4Spec.msgFromSyscallError e') σ).1,
        RelTopM (L := L) s2 z.2 ∧ JAt (L := L) arI AR s2 a z.2 ⦄ := by
  have hct : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  obtain ⟨htcb, x, hk⟩ := J.xtop.curTcb hcur
  obtain ⟨x', hk', hwx⟩ := J.buf ct hct
  rw [hk] at hk'; cases hk'
  have hOK0 := J.xferH.1
  have hBP0 := J.xferH.2.2
  have hmsl : (Fl4Spec.msgFromSyscallError e').2.length ≤ 5 := msgErr_len e'
  have hflag : fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC = true := by
    unfold fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC; rfl
  have hdm : syscall.DEBUG_MESSAGE_START + 1#u64 = ok 7#u64 := by
    unfold syscall.DEBUG_MESSAGE_START; rfl
  unfold syscall.reply_error
  refine WP.spec_bind (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 htcb hk hOK0 true) ?_
  rintro w ⟨hw0, hwp⟩
  have hbm : ∀ q, Endp.ipcBufOf true x = some q → Endp.BufMap Z.B w q := fun q hq =>
    J.xferH.2.1 ct hct x true q hk hq w (hwp hwx q hq)
  have hfr : ∀ p, Endp.ipcBufOf true x = some p →
      ∀ k, k < 128 → (Endp.bufAddr p k).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p k) σ :=
    fun p hp k hk128 => ⟨Endp.bufAddr_aligned J.xtop.fin.1.2.ep (hbm p hp) k, buf_frame_of_ok hOK0 hk hp k hk128⟩
  have hspec := fl4ReplyErr_eq hk (Fl4Spec.msgFromSyscallError e').1 (Fl4Spec.msgFromSyscallError e').2
    (by omega) hfr
  suffices hsuf : (do
      let s1 ← obj.Tcb.set_reg st ct s layout.reg.BADGE 0#u64
      let (len, s2) ← syscall.error_mrs st s1 ct w e
      let (s3, len1) ←
        if fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC
        then
          if w != 0#u64
          then
            do
            let i ← syscall.DEBUG_MESSAGE_START + 1#u64
            let w1 ← msg.buf_get st s2 w i
            let i1 ← lift (~~~255#u64)
            let i2 ← lift (w1 &&& i1)
            let s3 ← msg.buf_set st s2 w i i2
            let len1 ← lift (core.num.U64.wrapping_add len 1#u64)
            ok (s3, len1)
          else ok (s2, len)
        else ok (s2, len)
      let i ← error.SysError.code e
      let mi ← msginfo.MessageInfo.new i 0#u64 0#u64 len1
      msg.set_msg_info st s3 ct mi) ⦃ s2 =>
        JAt (L := L) arI AR s2 a (replyErrState σ ct.bv x (Fl4Spec.msgFromSyscallError e').1
          (Fl4Spec.msgFromSyscallError e').2) ⦄ by
    refine WP.spec_mono hsuf ?_
    rintro s2 ⟨Z2, H2, Cs2, Ac2, Lst2, D2, J2⟩
    refine ⟨((), replyErrState σ ct.bv x (Fl4Spec.msgFromSyscallError e').1 (Fl4Spec.msgFromSyscallError e').2),
      ?_, J2.xtop.relTop, Z2, H2, Cs2, Ac2, Lst2, D2, J2⟩
    rw [hspec]; exact Set.mem_singleton _
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
  rintro s1 rfl
  -- the badge
  have hXb := badge_wr_irel J.ip (J.xtop.irelK J.ks J.buf) hct hk 0#u64
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V1, J1⟩ := J.regWrJ hct hk Fl4Spec.badge_register 0#u64 hXb
  rw [Endp.regIdx_badge] at J1
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  rw [e0] at J1
  set xA := Notif.setReg x Fl4Spec.badge_register 0 with hxA
  set σA := Notif.updK σ ct.bv (.tcb xA) with hσA
  have hkA : σA.kheap ct.bv = some (.tcb xA) := by simp [σA, Notif.updK]
  set s1 := L.wr s (Endp.regA ct layout.reg.BADGE) 0#u64 with hs1
  have hks1 : L.ksb s1 = L.ksb s := L.ksb_wr _ _ _
  have hBPA : ∀ s', L.ksb s' = L.ksb s → Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s' σA := fun s' h =>
    hBP0.mono h (fun q y n hq => by
      by_cases e : q = ct.bv
      · subst e; rw [hkA] at hq; cases hq
      · simpa [σA, Notif.updK, e] using hq)
  have hOK1 := J1.xferH.1
  have hWOK : ∀ q, Endp.ipcBufOf true x = some q → ∀ i : U64, i.val < 128 →
      BufWordOK H σA (fl4BufA w i) := fun q hq i hi =>
    J1.bufWord hOK1 htcb hkA hq i.val hi (by rw [fl4BufA_bv, hwp hwx q hq])
  set buf := Endp.ipcBufOf true x with hbuf
  -- the words
  let I : S → List Fl4Spec.Word → Prop := fun s' ms => L.ksb s' = L.ksb s ∧
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a (MrS σA ct.bv xA buf ms)
  have hI0 : I s1 [] := ⟨hks1, V1, by rw [MrS_nil hkA]; exact J1⟩
  have step : ∀ (s' : S) (ms1 : List Fl4Spec.Word), I s' ms1 → ∀ (i : U64), i.val = ms1.length →
      ms1.length < 120 → ∀ v : U64, msg.set_mr st s' ct w i v ⦃ r => r.1.val = mrLen buf (ms1.length + 1) ∧
        I r.2 (ms1 ++ [v.bv]) ⦄ := by
    rintro s' ms1 ⟨hk', V, J'⟩ i hi hi' v
    refine WP.spec_mono (J'.setmrJ hct hkA w hw0 hbm (hBPA s' hk') hWOK i hi hi' v) ?_
    rintro r ⟨h1, h2, V', J''⟩
    exact ⟨h1, h2.trans hk', V', J''⟩
  refine WP.spec_bind (error_mrs_gen ct buf w I step s1 hI0 e e' he) ?_
  rintro ⟨len, s3⟩ ⟨hlen, hk3, V3, J3⟩
  simp only at hlen hk3 J3
  have hkM := MrS_kheap_t σA ct.bv xA buf (Fl4Spec.msgFromSyscallError e').2
  cases hb : Endp.ipcBufOf true x with
  | none =>
    have hbn : buf = none := hb
    rw [hbn] at J3 hlen hkM
    have hw : w = 0#u64 := hw0.2 hb
    simp only [hflag, hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine WP.spec_bind (code_label he) ?_
    rintro cd hcd
    unfold msginfo.MessageInfo.new
    simp only [bind_ok]
    have hl128 : len.val < 128 := by rw [hlen]; simp only [mrLen]; omega
    refine WP.spec_mono (Endp.set_msg_info_spec _ ct cd len hl128) ?_
    rintro s4 ⟨v, rfl, hv⟩
    rw [← Endp.regIdx_msgInfo]
    have hX4 := reg_wr_irel J3.ip (J3.xtop.irelK J3.ks J3.buf) hct hkM Fl4Spec.msg_info_register (by decide) v
    obtain ⟨V4, J4⟩ := J3.regWrJ hct hkM Fl4Spec.msg_info_register v hX4
    have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen none (Fl4Spec.msgFromSyscallError e').2.length),
        0, 0, (Fl4Spec.msgFromSyscallError e').1⟩ := by
      rw [hv, hcd]; congr 2
      apply BitVec.eq_of_toNat_eq; simp only [Fl4Spec.natToLen, BitVec.toNat_ofNat, UScalar.bv_toNat, hlen, mrLen]; omega
    unfold replyErrState
    simp only [hb]
    rw [← hvd]; exact ⟨_, _, _, _, _, _, J4⟩
  | some p =>
    have hbs : buf = some p := hb
    rw [hbs] at J3 hlen hkM
    have hw : w ≠ 0#u64 := fun h => by rw [hbs] at hw0; cases hw0.1 h
    have hbw : (w != 0#u64) = true := by simp [hw]
    simp only [hflag, hbw, ↓reduceIte, hdm, bind_ok]
    have hdbg : (do
        let w_1 ← msg.buf_get st s3 w 7#u64
        let i1 ← lift (~~~255#u64)
        let i2 ← lift (w_1 &&& i1)
        let s4 ← msg.buf_set st s3 w 7#u64 i2
        let len2 ← lift (core.num.U64.wrapping_add len 1#u64)
        ok (s4, len2)) ⦃ r => r = (L.wr s3 (Endp.fl4BufA w 7#u64) (L.mem s3 (Endp.fl4BufA w 7#u64) &&& ~~~255#u64),
          core.num.U64.wrapping_add len 1#u64) ⦄ := by
      refine WP.spec_bind (Endp.msg.buf_get.spec s3 w 7#u64) ?_
      rintro dv rfl
      simp only [lift, bind_ok]
      refine WP.spec_bind (Endp.msg.buf_set.spec s3 w 7#u64 _) ?_
      rintro s4 rfl
      simp only [bind_ok, WP.spec_ok]
    refine WP.spec_bind hdbg ?_
    rintro r rfl
    have hpair := hbm p hb 7#u64 (by decide)
    set σM := MrS σA ct.bv xA (some p) (Fl4Spec.msgFromSyscallError e').2 with hσM
    have hdv : (L.mem s3 (Endp.fl4BufA w 7#u64)).bv = Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) :=
      J3.xtop.fin.1.1.2.1.buf _ hpair
    have hval : (L.mem s3 (Endp.fl4BufA w 7#u64) &&& ~~~255#u64).bv =
        Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) &&& ~~~(255 : Fl4Spec.Word) := by
      rw [UScalar.bv_and]; exact congrArg₂ (· &&& ·) hdv rfl
    obtain ⟨hAp, o, ko, hko, g1, g2⟩ := hWOK p hb 7#u64 (by decide)
    have hObj : ∃ o ko, σM.kheap o = some ko ∧ o.toNat ≤ (Endp.fl4BufA w 7#u64).val ∧
        (Endp.fl4BufA w 7#u64).val < o.toNat + 2 ^ Fl4Spec.objBits ko := by
      by_cases e : o = ct.bv
      · subst e; rw [hkA] at hko; cases hko
        exact ⟨_, _, MrS_kheap_t _ _ _ _ _, g1, g2⟩
      · exact ⟨o, ko, by rw [hσM, MrS_kheap_ne _ _ _ _ _ e]; exact hko, g1, g2⟩
    have hBP3 : Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s3 σM := (hBPA s3 hk3).mono rfl (MrS_sc hkA _ _)
    have J4 := J3.userWrJ hBP3 hpair hAp hObj (L.mem s3 (Endp.fl4BufA w 7#u64) &&& ~~~255#u64)
    simp only [hval] at J4
    refine WP.spec_bind (code_label he) ?_
    rintro cd hcd
    unfold msginfo.MessageInfo.new
    simp only [bind_ok]
    have hl128 : (core.num.U64.wrapping_add len 1#u64).val < 128 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hlen, mrLen]; omega
    refine WP.spec_mono (Endp.set_msg_info_spec _ ct cd _ hl128) ?_
    rintro s5 ⟨v, rfl, hv⟩
    rw [← Endp.regIdx_msgInfo]
    have hkD : (Endp.setUm σM (Endp.storeMem σM.machineState.underlyingMemory (Endp.bufAddr p 7)
        (Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) &&& ~~~(255 : Fl4Spec.Word)))).kheap ct.bv =
        some (.tcb (Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs (Fl4Spec.msgFromSyscallError e').2))) :=
      hkM
    have hX5 := reg_wr_irel J4.ip (J4.xtop.irelK J4.ks J4.buf) hct hkD Fl4Spec.msg_info_register (by decide) v
    obtain ⟨V5, J5⟩ := J4.regWrJ hct hkD Fl4Spec.msg_info_register v hX5
    have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen (some p)
        (Fl4Spec.msgFromSyscallError e').2.length) + 1, 0, 0, (Fl4Spec.msgFromSyscallError e').1⟩ := by
      rw [hv, hcd]; congr 2
      apply BitVec.eq_of_toNat_eq
      simp [Fl4Spec.natToLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hlen, mrLen]
    unfold replyErrState
    simp only [hb]
    rw [← hvd]; exact ⟨_, _, _, _, _, _, J5⟩

set_option maxHeartbeats 4000000 in
/-- **The error reply at `J`** (`ReplyHypMX.fail`'s program, module
docstring). -/
theorem JAtZ.replyFailJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (hcur : σ.curThread = ct.bv) (is_call : Bool) (e : error.SysError) (e' : Fl4Spec.SyscallError)
    (he : ErrRel (.Sys e) e') :
    ((if is_call then do
        let s2 ← syscall.reply_error st s ct e
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a)
      else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a)) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ res =>
      res.1 = .Ok () ∧ ∃ z ∈ ((Fl4Spec.NonDet.when is_call <|
        Fl4Spec.fl4ReplyFromKernelError true ct.bv (Fl4Spec.msgFromSyscallError e')) σ).1,
        RelTopM (L := L) res.2.1 z.2 ∧ JAt (L := L) arI AR res.2.1 res.2.2 z.2 ⦄ := by
  cases is_call
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨trivial, ((), σ), ?_, J.xtop.relTop, Z, H, Cs, Ac, Lst, D, J⟩
    rw [Endp.nd_when_false (by simp)]; exact Set.mem_singleton _
  simp only [↓reduceIte]
  refine WP.spec_bind (J.replyErrJ hcur e e' he) ?_
  rintro s2 ⟨z, hz, hRT, hJ⟩
  refine (WP.spec_ok _).2 ⟨rfl, z, ?_, hRT, hJ⟩
  unfold Fl4Spec.NonDet.when
  simp only [↓reduceIte]
  exact hz

end

end

end Fl4Proofs.P3
