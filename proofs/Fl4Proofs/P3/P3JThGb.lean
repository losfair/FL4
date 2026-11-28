/-
P3 (p3J gen 42): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at GetBreakpoint (17),
for both classes**, by the buffer-is-0 route (gen 41 Finding 2); the rest set {CNode at Revoke / Delete, Thread at
2, 5, 8–11, 22, or SetEPTRoot}.

* `SInvCk.cki_sts`: the cap-kind invariant `CKI` survives a thread-state change of a TCB (only `tcbState` changes;
  `capOpt` of a TCB reads its cap fields).
* `JAtZ.setMr0ProjW`: FL4's `msg::set_mr` with buffer word `0` writes at most a message register of a thread of `Z.T`
  (`regProjW`); for an index ≥ 4 it writes nothing (FL4 `msg.rs` `set_mr`: the buffer write is guarded by
  `buf != 0`).
* `JAtZ.replyTailJStW`: StPostIoLeaf's `JAtZ.replyTailJSt` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)`
  (proof text unchanged but the posts: the badge and message-info registers by `regProjW`, `Running` by
  `stsProjW`).
* **`tcb_get_bpJSt`**: XTopJointTcb's `tcb_get_bpJ` (a replying label, `TcbOKRX`) with the post
  `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)` and one more hypothesis, `SInvCk.CKI σ` (the dispatch state's
  cap-kind invariant, an intro hypothesis of `MidDecStWL` / `InvDecStWL`): after the caller's restart (`cki_sts`)
  P3JMcBuf's `lookup_ipc_buffer_cki` gives the caller's buffer `0`, so the five `set_mr` steps write registers only
  (`setMr0ProjW`; MR4 writes nothing), the tail by `replyTailJStW`. `GetBpHyp` [P] of the non-stable leaf is
  TcbHypsX's theorem `getBpHyp_of` (no premise).
* **`decThGbSt`** (any flags): the dispatch leaf (the `DecOKRMX` disjunct of `XCap`; `ArgRel … 1` from
  `JAtZ.argsJ`).
* `ThHard15 l`: `ThHard14 l ∧ l ≠ TCBGetBreakpoint`. `IsRestCap23`. `restCap22_of23`, `restCap23_of`.
  **`midDecRest22_of_gb`** / **`invDecRest22_of_gb`**, `midDecStWL_of_22` / `invDecStWL_of_22`.
* **`DispStabFootLzp` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap23`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzo_of_Lzp`** (under the tops' platform facts), **`dispStabFootLzp_of_Lzo`**; top
  **`kernel_entry_runMcWKR_sysLzp`** (globals verbatim as `_sysLzo`).

Premise honesty: `DispStabFootLzp`'s decode fields are `DispStabFootLzo`'s at the smaller antecedent
(`IsRestCap23 → IsRestCap22`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzp` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThCp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvCk
open Fl4Spec

/-- (p3J gen 42) **`CKI` survives a thread-state change** (module docstring). -/
theorem cki_sts {σ : State Unit} (hC : CKI σ) {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (ts : ThreadState) :
    CKI (Fl4Proofs.P3.Notif.stsAct (Fl4Proofs.P3.Notif.updK σ t (.tcb { x with tcbState := ts })) t) := by
  intro p cref c hc
  rw [Fl4Proofs.P3.Notif.stsAct_kheap, Fl4Proofs.P3.Notif.updK_kheap, Function.update_apply] at hc
  by_cases e : p = t
  · rw [if_pos e] at hc
    subst e
    exact hC p cref c (by rw [hk]; exact hc)
  · rw [if_neg e] at hc
    exact hC p cref c hc

end Fl4Proofs.P3.SInvCk

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **`set_mr` with buffer word `0` writes only `ProjW`** (module docstring). -/
theorem JAtZ.setMr0ProjW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (s1 : S) (i v : U64) :
    msg.set_mr st s1 t 0#u64 i v ⦃ r => P1.WritesIn st s1 r.2 (Mc.ProjW (L := L) H Cs s1) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  unfold msg.set_mr
  by_cases h4 : i < msg.N_MSG_REGISTERS
  · have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h4; omega
    simp only [h4, ↓reduceIte]
    refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
    rintro r rfl
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s1 t _ v) ?_
    rintro s2 rfl
    simp only [lift, bind_ok, WP.spec_ok]
    exact J.regProjW ht (Endp.mrIdx i.val) s1 v
  · rw [if_neg h4]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact P1.WritesIn.refl _ _

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **The reply tail at stable ghosts, with its `ProjW` footprint** (StPostIoLeaf's
`JAtZ.replyTailJSt`; module docstring). -/
theorem JAtZ.replyTailJStW {s : S} {a : A} {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb}
    {ms : List Fl4Spec.Word}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (MrS σ0 ct.bv x0 (Endp.ipcBufOf true x0) ms)) [VxE Z]
    (hct : ct ∈ Z.T) (hk0 : σ0.kheap ct.bv = some (.tcb x0)) (hrs : x0.tcbState = .restart)
    (hlen : ms.length ≤ Fl4Spec.msgMaxLength)
    (hfr : ∀ p, Endp.ipcBufOf true x0 = some p → ∀ z ∈ Endp.mrPairs ms,
      (Endp.bufAddr p z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p z.1) σ0)
    (n : U64) (hn : n.val = mrLen (Endp.ipcBufOf true x0) ms.length) (hn128 : n.val < 128) :
    (do
      let s4 ← tcb.reply_words st s ct n
      sched.set_thread_state st s4 ct sched.TS_RUNNING) ⦃ s5 =>
        ∀ z ∈ (specTail true ct.bv ms σ0).1, JStab (L := L) arI AR Z H Cs s5 a z.2 ∧
          P1.WritesIn st s s5 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  set buf := Endp.ipcBufOf true x0
  have hkx := MrS_kheap_t σ0 ct.bv x0 buf ms
  refine WP.spec_bind (Pₘ := fun s4 => (∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s4 a
    (replyStateB σ0 ct.bv x0 buf ms)) ∧ P1.WritesIn st s s4 (Mc.ProjW (L := L) H Cs s)) ?_ ?_
  swap
  · rintro s4 ⟨⟨V2, J2⟩, W4⟩
    refine WP.spec_mono (WP.spec_and (J2.runJ hct (replyStateB_kheap_t _ _ _ _ _) (by rw [replyTcbB_state, hrs]))
      (stsProjW J2 hct sched.TS_RUNNING)) ?_
    rintro s5 ⟨⟨Lst', D', J5⟩, W5⟩ z hz
    rw [specTail_data hk0 hrs ms hlen hfr] at hz
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨J5.stab.mv, W4.projW_trans W5⟩
  unfold tcb.reply_words
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
  rintro s1 rfl
  have W1 := J.regProjW hct Fl4Spec.badge_register s 0#u64
  rw [Endp.regIdx_badge] at W1
  -- the badge
  have hXb := badge_wr_irel J.ip (J.xtop.irelK J.ks J.buf) hct hkx 0#u64
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V1, J1⟩ := J.regWrJ hct hkx Fl4Spec.badge_register 0#u64 hXb
  rw [Endp.regIdx_badge] at J1
  rw [mrS_setReg σ0 ct.bv x0 buf ms badge_not_mr] at J1
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  rw [e0] at J1
  set xA := Notif.setReg x0 Fl4Spec.badge_register 0
  unfold msginfo.MessageInfo.new
  simp only [bind_ok]
  refine WP.spec_mono (Endp.set_msg_info_spec _ ct 0#u64 n hn128) ?_
  rintro s2 ⟨v, rfl, hv⟩
  rw [← Endp.regIdx_msgInfo]
  have W2 := J.regProjW hct Fl4Spec.msg_info_register (L.wr s (Endp.regA ct layout.reg.BADGE) 0#u64) v
  have hkA := MrS_kheap_t (Notif.updK σ0 ct.bv (.tcb xA)) ct.bv xA buf ms
  have hX2 := reg_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hct hkA Fl4Spec.msg_info_register (by decide) v
  obtain ⟨V2, J2⟩ := J1.regWrJ hct hkA Fl4Spec.msg_info_register v hX2
  have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen buf ms.length), 0, 0, 0⟩ := by
    rw [hv]; congr 2
    apply BitVec.eq_of_toNat_eq; simp only [Fl4Spec.natToLen, BitVec.toNat_ofNat, UScalar.bv_toNat, ← hn]; omega
  have eR : Notif.updK (MrS (Notif.updK σ0 ct.bv (.tcb xA)) ct.bv xA buf ms) ct.bv
      (.tcb (Notif.setReg (Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs ms))
        Fl4Spec.msg_info_register v.bv)) = replyStateB σ0 ct.bv x0 buf ms := by
    unfold replyStateB; rw [hvd]
  rw [eR] at J2
  exact ⟨⟨V2, J2⟩, W1.projW_trans W2⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **GetBreakpoint at stable ghosts, with its `ProjW` footprint, at a `CKI` state** (XTopJointTcb's
`tcb_get_bpJ`; module docstring). -/
theorem tcb_get_bpJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    [VxE Z] (hni : Entered σ) (hC : SInvCk.CKI σ)
    (p : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .getBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 1)
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKRX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBGetBreakpoint p
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
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, ⟨_, ?_, bp_err⟩, ⟨J.stab, P1.WritesIn.refl _ _⟩⟩)
    apply run_liftME_err
    rw [hsp]
    exact run_bind_error (by rw [checkBp_run, if_pos hb]) _
  simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨s1, σ1, x0, hrc1, hst1, hk0, -, hσ1, -, -, hcu1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
    have h := stsProjW J hctT sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h; exact h
  rw [hkc] at hk0; cases hk0
  set xr : Fl4Spec.Tcb := { xc with tcbState := .restart }
  have hkc1 : σ1.kheap ct.bv = some (.tcb xr) := by
    rw [hσ1, Notif.stsAct_kheap]; simp [Notif.updK, xr]
  have hC1 : SInvCk.CKI σ1 := by rw [hσ1]; exact SInvCk.cki_sts hC hkc .restart
  have hcurY : ct.bv = σ1.curThread := by rw [hcu1, hcur]
  have hX1 := J1.xtop
  have hact1 : OutsideObjects Z.th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) := J1.kern.act
  rw [hrc1]; simp only [bind_ok]
  obtain ⟨r1, hr1⟩ := getBpHyp_of (st := st) s ct p s1 bp hs1
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
    TopPostRMX (L := L) (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) σ blk call don (Fl4Spec.NonDetE.liftME
      Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)) ct s
      (x.1, x.2, ar)) ?_ fun x hx => (WP.spec_ok _).2 hx
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (WP.spec_and (nodata_tail_core hX1 hcurY hkc1 rfl hact1 [0, 0, 0, 0, 0])
      (WP.spec_and (J1.runJ hctT hkc1 rfl) (stsProjW J1 hctT sched.TS_RUNNING))) ?_
    rintro s2 ⟨⟨hne, z, hz, hRT, -⟩, ⟨Lst', D', J5⟩, W5⟩
    refine (WP.spec_ok _).2 (Or.inr ⟨rfl, hne, _, DecOut.of_eq hdec, σ1, hst1, _, σ1, hy _ rfl, z, hz, hRT, ?_⟩)
    have hrs1 : xr.tcbState = .restart := rfl
    unfold specTail at hz
    rw [nd_bind_one (Notif.getThreadState_eq hkc1)] at hz
    simp only [hrs1] at hz
    rw [Endp.nd_when_false (by simp), Notif.nd_pure_bind', Notif.setThreadState_eq .running hkc1] at hz
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨J5.stab, W1.projW_trans W5⟩
  · simp only [↓reduceIte]
    have hOK1 := J1.xferH.1
    obtain ⟨x', hk', hwx⟩ := J1.buf ct hctT
    rw [hkc1] at hk'; cases hk'
    have hb0 : msg.lookup_ipc_buffer st s1 true ct = ok 0#u64 := Mc.lookup_ipc_buffer_cki J1 hC1 htcb true
    refine WP.spec_bind (WP.spec_and (lookup_buf_full s1 σ1 hX1.rel.2.1.1 hX1.rel.2.1.2.1 htcb hkc1 hOK1 true)
      (show msg.lookup_ipc_buffer st s1 true ct ⦃ b => b = 0#u64 ⦄ by rw [hb0]; exact (WP.spec_ok _).2 rfl)) ?_
    rintro bf ⟨⟨hw0, hwp⟩, rfl⟩
    have hbm : ∀ q, Endp.ipcBufOf true xr = some q → Endp.BufMap Z.B 0#u64 q := fun q hq =>
      J1.xferH.2.1 ct hctT xr true q hkc1 hq 0#u64 (hwp hwx q hq)
    have hBP1 := J1.xferH.2.2
    have hWOK : ∀ q, Endp.ipcBufOf true xr = some q → ∀ i : U64, i.val < 128 →
        BufWordOK H σ1 (Endp.fl4BufA 0#u64 i) := fun q hq i hi =>
      J1.bufWord hOK1 htcb hkc1 hq i.val hi (by rw [fl4BufA_bv, hwp hwx q hq])
    have hI0 : Vs.RInv (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR Z.G s1 ar
        (MrS σ1 ct.bv xr (Endp.ipcBufOf true xr) []) := by
      rw [MrS_nil hkc1]; exact hX1.toRInv
    have J0 : JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 s1 ar (MrS σ1 ct.bv xr (Endp.ipcBufOf true xr) []) := by
      rw [MrS_nil hkc1]; exact J1
    refine WP.spec_bind (WP.spec_and (WP.spec_and (setmr_reg_inv σ1 ct htcb hcurY xr _ 0#u64 s1 ar [] hI0 0#u64 rfl
      (by decide) r1.vaddr) (J0.setmrJ hctT hkc1 0#u64 hw0 hbm hBP1 hWOK 0#u64 rfl (by decide) r1.vaddr))
      (J.setMr0ProjW hctT s1 0#u64 r1.vaddr)) ?_
    rintro ⟨l2, s2⟩ ⟨⟨⟨-, hI2, hk2, hc2⟩, -, -, V2, J2⟩, W2⟩
    simp only at hI2 hk2 hc2 J2 W2
    refine WP.spec_bind (WP.spec_and (WP.spec_and (setmr_reg_inv σ1 ct htcb hcurY xr _ 0#u64 s2 ar _ hI2 1#u64 rfl
      (by simp) r1.ty) (J2.setmrJ hctT hkc1 0#u64 hw0 hbm (hBP1.mono hk2 fun _ _ _ h => h) hWOK 1#u64 rfl (by simp)
        r1.ty)) (J.setMr0ProjW hctT s2 1#u64 r1.ty)) ?_
    rintro ⟨l3, s3⟩ ⟨⟨⟨-, hI3, hk3, hc3⟩, -, -, V3, J3⟩, W3⟩
    simp only at hI3 hk3 hc3 J3 W3
    refine WP.spec_bind (WP.spec_and (WP.spec_and (setmr_reg_inv σ1 ct htcb hcurY xr _ 0#u64 s3 ar _ hI3 2#u64 rfl
      (by simp) r1.size) (J3.setmrJ hctT hkc1 0#u64 hw0 hbm (hBP1.mono (hk3.trans hk2) fun _ _ _ h => h) hWOK
        2#u64 rfl (by simp) r1.size)) (J.setMr0ProjW hctT s3 2#u64 r1.size)) ?_
    rintro ⟨l4, s4⟩ ⟨⟨⟨-, hI4, hk4, hc4⟩, -, -, V4, J4⟩, W4⟩
    simp only at hI4 hk4 hc4 J4 W4
    refine WP.spec_bind (WP.spec_and (WP.spec_and (setmr_reg_inv σ1 ct htcb hcurY xr _ 0#u64 s4 ar _ hI4 3#u64 rfl
      (by simp) r1.rw) (J4.setmrJ hctT hkc1 0#u64 hw0 hbm (hBP1.mono (hk4.trans (hk3.trans hk2)) fun _ _ _ h => h)
        hWOK 3#u64 rfl (by simp) r1.rw)) (J.setMr0ProjW hctT s4 3#u64 r1.rw)) ?_
    rintro ⟨l5, s5⟩ ⟨⟨⟨-, hI5, hk5, hc5⟩, -, -, V5, J5⟩, W5⟩
    simp only at hI5 hk5 hc5 J5 W5
    have W15 : P1.WritesIn st s s5 (Mc.ProjW (L := L) H Cs s) :=
      (((W1.projW_trans W2).projW_trans W3).projW_trans W4).projW_trans W5
    have hks5 : L.ksb s5 = L.ksb s1 := hk5.trans (hk4.trans (hk3.trans hk2))
    have hcp5 : L.cpu s5 = L.cpu s1 := hc5.trans (hc4.trans (hc3.trans hc2))
    have hBP5 : Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s5 σ1 := hBP1.mono hks5 (fun _ _ _ h => h)
    have tail : ∀ v : U64, (do
        let (len, s6) ← msg.set_mr st s5 ct 0#u64 4#u64 v
        let s7 ← tcb.reply_words st s6 ct len
        let s8 ← sched.set_thread_state st s7 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s8)) ⦃ res =>
          TopPostRMX (L := L) (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
            P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) σ blk true don (Fl4Spec.NonDetE.liftME
            Fl4Spec.Fl4Invocation.invokeFl4TCB (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)) ct s
            (res.1, res.2, ar) ⦄ := by
      intro v
      refine WP.spec_bind (WP.spec_and (WP.spec_and (Vs.setmr_inv σ1 ct htcb hcurY hkc1 _ 0#u64 hw0 hbm s5 ar _ hI5
        hBP5 4#u64 rfl (by simp) v) (J5.setmrJ hctT hkc1 0#u64 hw0 hbm hBP5 hWOK 4#u64 rfl (by simp) v))
        (J.setMr0ProjW hctT s5 4#u64 v)) ?_
      rintro ⟨len, s6⟩ ⟨⟨⟨hlen, hI6, hk6, hc6⟩, -, -, V6, J6⟩, W6⟩
      simp only at hlen hI6 hk6 hc6 J6 W6
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
        (J6.replyTailJStW hctT hkc1 rfl (by rw [hl5]; decide) hfr len (by rw [hlen]; simp) hn128)) ?_
      rintro s8 ⟨⟨hne, z, hz, hRT, -⟩, hJ8⟩
      obtain ⟨hS8, W8⟩ := hJ8 z hz
      refine (WP.spec_ok _).2 (Or.inr ⟨rfl, hne, _, DecOut.of_eq hdec, σ1, hst1, _, σ1, hy _ hl5, z, hz, hRT,
        ?_, (W15.projW_trans W6).projW_trans W8⟩)
      exact hS8.mv.mv.mv.mv.mv
    split
    · exact tail 1#u64
    · exact tail 0#u64

end

/-- (p3J gen 42) The Thread labels left after GetBreakpoint. -/
def ThHard15 (l : U64) : Prop := ThHard14 l ∧ l ≠ fl4_abi.label.TCBGetBreakpoint

/-- (p3J gen 42) The caps left after the GetBreakpoint leaf, with the message label. -/
def IsRestCap23 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard15 l
  | _, _ => False

theorem restCap22_of23 {cp : capability.Cap} {l : U64} (h : IsRestCap23 cp l) : IsRestCap22 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap23_of {cp : capability.Cap} {l : U64} (h : IsRestCap22 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBGetBreakpoint) : IsRestCap23 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem gb_nonIns : TcbNonIns fl4_abi.label.TCBGetBreakpoint := by
  unfold TcbNonIns fl4_abi.label.TCBGetBreakpoint fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **The Thread cap's decode at a dispatch state at GetBreakpoint, any flags** (module docstring). -/
theorem decThGbSt (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb) (hCb : SInvCk.CKI σb)
    (hMb : MR a' σb.machineState) {ct : U64} (hct : sched.cur_thread st s' = ok ct)
    {info : msginfo.MessageInfo} {mi : Fl4Spec.MessageInfo} {buf : U64} {buffer : Option Fl4Spec.ObjRef}
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))} {argsU : List U64}
    (hinfo : msg.msg_info st s' ct = ok info)
    (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σb = ({(mi, σb)}, False))
    (hbuf : msg.lookup_ipc_buffer st s' false ct = ok buf)
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σb = ({(buffer, σb)}, False))
    (hr2 : ipc.lookup_extra_caps st s' ct buf info = ok r2)
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σb = ({(er, σb)}, False))
    (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σb = ({(argsU.map UScalar.bv, σb)}, False))
    (sl : Fl4Spec.CslotPtr) (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p : U64}
    (hc : capAt (L.mem s') (cslotAddr sl) = ok (.Thread p))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs)
    (hl : info.label = fl4_abi.label.TCBGetBreakpoint) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
    XCapP (L := L) arI (MidX (L := L) arI AR MR Z H Cs s') (MidXP (L := L) arI AR MR Z H Cs s') s' a' σb
      info.label (msgLen info buf) (cslotAddr sl) (.Thread p) bl call don fp buf e mi.miLabel
      (argsU.map UScalar.bv) ci sl exs buffer ct := by
  have hX0 : JStab (L := L) arI AR (Z.mv Z.G V') H Cs s' a' σb ∧
      P1.WritesIn st s' s' (Mc.ProjW (L := L) H Cs s') := ⟨J.stab, P1.WritesIn.refl _ _⟩
  refine XCapP.monoX (X := fun s1 a1 σ1 => (JStab (L := L) arI AR (Z.mv Z.G V') H Cs s1 a1 σ1 ∧
      P1.WritesIn st s' s1 (Mc.ProjW (L := L) H Cs s')) ∧ MR a1 σ1.machineState) ?_
    fun _ _ _ ⟨⟨hJ, hw⟩, hm⟩ => ⟨JStab.mv hJ, hm, hw⟩
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  obtain ⟨hLb, -⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
  obtain ⟨-, -, hA5⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  rw [hl]
  obtain ⟨sl', hlbl, hext, hd⟩ := tcb_canon fl4_abi.label.TCBGetBreakpoint
  have hl5 : fl4_abi.label.TCBGetBreakpoint.val ≠ 5 ∧ fl4_abi.label.TCBGetBreakpoint.val ≠ 8 ∧
      fl4_abi.label.TCBGetBreakpoint.val ≠ 9 ∧ fl4_abi.label.TCBGetBreakpoint.val ≠ 10 ∧
      fl4_abi.label.TCBGetBreakpoint.val ≠ 11 := by simp [fl4_abi.label.TCBGetBreakpoint]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine XCapP.mrGT (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD gb_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  right
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hg, he⟩ := ext_lbl hlbl hext (by simp [tcbLabelOf])
      (show tcbExtOf _ = some .getBreakpoint by simp [tcbExtOf])
    exact tcb_get_bpJSt s' a' σb J hnib hCb p sl' hg he _ buf ct hct (J.stallT p hpT) buffer
      (fun i hi => hA5 i (by omega)) call _ e bl don _ ci sl exs
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **`MidDecStWL` at `KW ∧ IsRestCap22` from the GetBreakpoint leaf** (module docstring). -/
theorem midDecRest22_of_gb (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap23 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap22 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBGetBreakpoint
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThGbSt hA hT hMT hKD J hnib hCb hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap23_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **`InvDecStWL` at `KW ∧ IsRestCap22` from the GetBreakpoint leaf** (module docstring). -/
theorem invDecRest22_of_gb (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap23 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap22 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBGetBreakpoint
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, -⟩ := dispEnteredSg hnd hX hni hBA
    exact decThGbSt hA hT hMT hKD J hnib hCb hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap23_of hW.2 hS⟩

/-- (p3J gen 42) `MidDecStWL` at `KW ∧ IsRestCap22` gives it at `KW ∧ IsRestCap23` (antitone). -/
theorem midDecStWL_of_22 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap22 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap23 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap22_of23 hW.2⟩

/-- (p3J gen 42) `InvDecStWL` at `KW ∧ IsRestCap22` gives it at `KW ∧ IsRestCap23` (antitone). -/
theorem invDecStWL_of_22 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap22 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap23 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap22_of23 hW.2⟩

end

end

end Fl4Proofs.P3


namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 42) **`DispStabFootLzp` [J]**: `DispStabFootLzo` with `invDecRest` / `midDecRest` restricted to
`IsRestCap23` (`IsRestCap22` minus the Thread caps at GetBreakpoint; module docstring). -/
structure DispStabFootLzp (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzo.invDecRest` at `KW ∧ IsRestCap23`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap23 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzo.midDecRest` at `KW ∧ IsRestCap23`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap23 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzo.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzo.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 42) **`DispStabFootLzp → DispStabFootLzo`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzo_of_Lzp (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzp (L := L) arI AR MR s a σ) :
    DispStabFootLzo (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest22_of_gb hA hT hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest22_of_gb hA hT hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 42) **`DispStabFootLzo → DispStabFootLzp`** (the honesty claim: `DispStabFootLzp` is implied). -/
theorem dispStabFootLzp_of_Lzo {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzo (L := L) arI AR MR s a σ) : DispStabFootLzp (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_22 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_22 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzp` only** (`hLzp` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzp [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzp : DispStabFootLzp (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzo hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzo_of_Lzp hA hT hnd hM hIp hKD hLzp)

end

end Fl4Proofs.P3.Mc
