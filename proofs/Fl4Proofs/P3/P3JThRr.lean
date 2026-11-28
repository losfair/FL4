/-
P3 (p3J gen 42): **the Thread cap's decode leaf at stable ghosts, with its `ProjW` footprint, at ReadRegisters (2),
for both classes**, by the buffer-is-0 route; the rest set {CNode at Revoke / Delete, Thread at 5, 8–11, 22, or
SetEPTRoot}.

* XTopJointReadRegs' pieces with the footprint threaded (proof text unchanged but the posts; at 4M heartbeats, the
  sources have 8M / 16M / 64M): **`rrJ_loop0W`** (`rrJ_loop0` with `WritesIn` in the loop invariant, each word by
  P3JThSs's `JAtZ.regProjW`), **`JAtZ.rrTailJW`** (`rrTailJ` at stable ghosts: the message info by `regProjW`,
  `Running` by `stsProjW`), **`JAtZ.readRegsJW`** (`readRegsJ` with one more hypothesis `SInvCk.CKI σ1`: the source's
  `suspend` by P3JThSus's `JAtZ.suspendProjW`, the badge by `regProjW`; the caller's buffer after the suspend is `0`
  (P3JMcBuf's `lookup_ipc_buffer_cki` at the spec state after the suspend, which is `CKI` by P3JCkS's
  `ck_fl4Perform` on the ReadRegisters perform outcome), so the source's buffer branch (FL4 `tcb.rs`
  `read_registers`, `if buf != 0`) is never taken and only `MR0`..`MR3` are written).
* **`tcb_read_regsJSt`**: XTopJointTcb's `tcb_read_regsJ` with the post `JStab Z H Cs ∧ WritesIn s · (ProjW H Cs s)`
  and the hypothesis `SInvCk.CKI σ` (carried across the caller's restart by P3JThGb's `cki_sts`).
* **`decThRrSt`** (any flags): the dispatch leaf (the `DecOKRMX` disjunct; the arguments by `JAtZ.argsJ`; the
  non-stable chain's `hpI` by P3JThSus's `JAtZ.capNotIdle` from `SpecGlob σb`; `CKI σb` an intro hypothesis).
* `ThHard16 l`: `ThHard15 l ∧ l ≠ TCBReadRegisters`. `IsRestCap24`. `restCap23_of24`, `restCap24_of`.
  **`midDecRest23_of_rr`** / **`invDecRest23_of_rr`**, `midDecStWL_of_23` / `invDecStWL_of_23`.
* **`DispStabFootLzq` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap24`, midSpec, midRecvSw verbatim};
  **`dispStabFootLzp_of_Lzq`** (under the tops' platform facts), **`dispStabFootLzq_of_Lzp`**; top
  **`kernel_entry_runMcWKR_sysLzq`** (globals verbatim as `_sysLzp`).

Premise honesty: `DispStabFootLzq`'s decode fields are `DispStabFootLzp`'s at the smaller antecedent
(`IsRestCap24 → IsRestCap23`), midSpec / midRecvSw verbatim; both directions proved.

Named premise: `DispStabFootLzq` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThGb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **XTopJointReadRegs' `rrJ_loop0` with its `ProjW` footprint** (module docstring). -/
theorem rrJ_loop0W {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb} {buf : Option Fl4Spec.ObjRef}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (MrS σ0 ct.bv x0 buf []))
    (hct : ct ∈ Z.T) {src : U64} (hne : src.bv ≠ ct.bv) (hsT : src ∈ Z.T) {xs : Fl4Spec.Tcb}
    (hks : σ0.kheap src.bv = some (.tcb xs)) (n : U64) :
    tcb.read_registers_loop0 st s src n ct 0#u64 ⦃ r => r.2.val = min n.val 4 ∧
      (∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D r.1 a (MrS σ0 ct.bv x0 buf ((rrOf xs n).take r.2.val))) ∧
      L.ksb r.1 = L.ksb s ∧ L.cpu r.1 = L.cpu s ∧ P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  have hfl : Fl4Spec.frameRegisters.length = 18 := rfl
  have hwl : wrRegs.length = 20 := rfl
  unfold tcb.read_registers_loop0
  apply loop.spec_decr_nat (measure := fun x => 4 - x.2.val)
    (inv := fun x => x.2.val ≤ min n.val 4 ∧
      (∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D x.1 a
        (MrS σ0 ct.bv x0 buf ((rrOf xs n).take x.2.val))) ∧
      L.ksb x.1 = L.ksb s ∧ L.cpu x.1 = L.cpu s ∧ P1.WritesIn st s x.1 (Mc.ProjW (L := L) H Cs s))
  · rintro ⟨s', i⟩ ⟨hi, ⟨V', J'⟩, hk', hc', W'⟩
    unfold tcb.read_registers_loop0.body
    simp only at hi J' hk' hc' W' ⊢
    by_cases h1 : i < n
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : i.val = min n.val 4 := by have := (P1.gt_iff_val).not.1 h1; omega
      exact ⟨this, ⟨V', J'⟩, hk', hc', W'⟩
    rw [if_pos h1]
    have hin : i.val < n.val := (P1.gt_iff_val).1 h1
    have h2 : i < tcb.N_FRAME := (P1.gt_iff_val).2 (by rw [hf]; omega)
    rw [if_pos h2]
    by_cases h3 : i < msg.N_MSG_REGISTERS
    swap
    · rw [if_neg h3, WP.spec_ok]
      have : i.val = min n.val 4 := by have := (P1.gt_iff_val).not.1 h3; rw [hN] at this; omega
      exact ⟨this, ⟨V', J'⟩, hk', hc', W'⟩
    rw [if_pos h3]
    have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h3; rwa [hN] at this
    simp only [lift, bind_ok]
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ (by rw [cast_to_us' i (by omega)]; simp; omega)) ?_
    rintro rr hrr
    have hrv : rr = regIdx (wrRegs[i.val]'(by omega)) := by
      rw [hrr, List.getElem_of_eq frame_regs_val, List.getElem_map]
      congr 1
      simp [cast_to_us' i (by omega), wrRegs, List.getElem_append_left (show i.val < Fl4Spec.frameRegisters.length by omega)]
    subst hrv
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' src _) ?_
    rintro v rfl
    refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
    rintro r3 rfl
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s' ct _ _) ?_
    rintro s2 rfl
    obtain ⟨i4, h4e, h4v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h4e, bind_ok, WP.spec_ok]
    have hi4' : i4.val = i.val + 1 := by simpa using h4v
    have hlen : ((rrOf xs n).take i.val).length = i.val := by simp [List.length_take, rrOf_length]; omega
    obtain ⟨V2, J2⟩ := J'.mrRegJ hct i.val hlen.symm (by omega)
      (L.mem s' (regA src (regIdx (wrRegs[i.val]'(by omega)))))
    rw [rr_src_reg hne hsT hks J'.xtop.toRInv, ← rrOf_take_succ xs n i.val (by omega)] at J2
    refine ⟨⟨by show i4.val ≤ min n.val 4; omega, ⟨V2, by rw [hi4']; exact J2⟩,
      by show L.ksb (L.wr s' _ _) = L.ksb s; rw [L.ksb_wr]; exact hk',
      by show L.cpu (L.wr s' _ _) = L.cpu s; rw [L.cpu_wr]; exact hc',
      W'.projW_trans (J.regProjW hct (Endp.mrIdx i.val) s' _)⟩,
      by show 4 - i4.val < 4 - i.val; omega⟩
  · exact ⟨by simp, ⟨Z.vs, by simpa using J⟩, rfl, rfl, P1.WritesIn.refl _ _⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **XTopJointReadRegs' `JAtZ.rrTailJ` at stable ghosts, with its `ProjW` footprint** (module
docstring). -/
theorem JAtZ.rrTailJW {σy : Fl4Spec.State Unit} {ct : U64} {x : Fl4Spec.Tcb} {ms : List Fl4Spec.Word}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a
      (MrS (Notif.updK σy ct.bv (.tcb (Notif.setReg x Fl4Spec.badge_register 0))) ct.bv
        (Notif.setReg x Fl4Spec.badge_register 0) (Endp.ipcBufOf true x) ms)) [VxE Z]
    (hct : ct ∈ Z.T) (hcur : ct.bv = σy.curThread) (hk : σy.kheap ct.bv = some (.tcb x))
    (hrs : x.tcbState = .restart) (hlen : ms.length ≤ Fl4Spec.msgMaxLength)
    (hfr : ∀ p, Endp.ipcBufOf true x = some p → ∀ z ∈ Endp.mrPairs ms,
      (Endp.bufAddr p z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p z.1) σy)
    (n : U64) (hn : n.val = mrLen (Endp.ipcBufOf true x) ms.length) (hn128 : n.val < 128) :
    (do
      let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
      let s6 ← msg.set_msg_info st s ct mi
      let s7 ← sched.set_thread_state st s6 ct sched.TS_RUNNING
      ok (s7, a)) ⦃ res =>
      L.mem res.1 (stA ct) ≠ sched.TS_RESTART ∧
      ∃ z ∈ (specTail true ct.bv ms σy).1, RelTopM (L := L) res.1 z.2 ∧ JStab (L := L) arI AR Z H Cs res.1 res.2 z.2 ∧
        P1.WritesIn st s res.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  set xA := Notif.setReg x Fl4Spec.badge_register 0 with hxA
  set buf := Endp.ipcBufOf true x
  unfold msginfo.MessageInfo.new
  simp only [bind_ok]
  refine WP.spec_bind (Endp.set_msg_info_spec _ ct 0#u64 n hn128) ?_
  rintro s3 ⟨v, rfl, hv⟩
  rw [← Endp.regIdx_msgInfo]
  have W2 := J.regProjW hct Fl4Spec.msg_info_register s v
  have hkA := MrS_kheap_t (Notif.updK σy ct.bv (.tcb xA)) ct.bv xA buf ms
  have hX2 := reg_wr_irel J.ip (J.xtop.irelK J.ks J.buf) hct hkA Fl4Spec.msg_info_register (by decide) v
  obtain ⟨V2, J2⟩ := J.regWrJ hct hkA Fl4Spec.msg_info_register v hX2
  have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen buf ms.length), 0, 0, 0⟩ := by
    rw [hv]; congr 2
    apply BitVec.eq_of_toNat_eq; simp only [Fl4Spec.natToLen, BitVec.toNat_ofNat, UScalar.bv_toNat, ← hn]; omega
  have eR : Notif.updK (MrS (Notif.updK σy ct.bv (.tcb xA)) ct.bv xA buf ms) ct.bv
      (.tcb (Notif.setReg (Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs ms))
        Fl4Spec.msg_info_register v.bv)) = replyStateB σy ct.bv x buf ms := by
    unfold replyStateB; rw [hvd]
  rw [eR] at J2
  have htcb : (Z.mv Z.G V2).th ct = some .tcb := (J2.xtop.curTcb (by rw [replyStateB_cur]; exact hcur.symm)).1
  have hcode : sched.TS_RUNNING.val = Notif.tsCode .running := by unfold sched.TS_RUNNING; rfl
  refine WP.spec_bind (WP.spec_and (sts_inv _ a _ J2.xtop.toRInv ct htcb (by rw [replyStateB_cur]; exact hcur)
    (replyStateB_kheap_t _ _ _ _ _) (by rw [replyTcbB_state, hrs]; rfl) J2.kern.act .running (by decide) _ hcode)
    (WP.spec_and (J2.runJ hct (replyStateB_kheap_t _ _ _ _ _) (by rw [replyTcbB_state, hrs]))
      (stsProjW J2 hct sched.TS_RUNNING))) ?_
  rintro s5 ⟨⟨hI5, hst5, -⟩, ⟨Lst', D', J5⟩, W5⟩
  rw [WP.spec_ok]
  exact ⟨by rw [hst5]; exact run_ne_rst, _, by rw [specTail_data hk hrs ms hlen hfr]; exact Set.mem_singleton _,
    J5.xtop.relTop, J5.stab.mv, W2.projW_trans W5⟩

set_option maxHeartbeats 4000000 in
/-- **ReadRegisters' leaf at `J`** (IpcReadRegsJ's `readRegsXHypJ` with
`JAtZ` carried): after the caller's restart, the source's suspend
(`JAtZ.suspendJ` with the four cancel steps, `recvReplyHyp_holds` for
`jCancel_recv`), then, called, the badge (`JAtZ.regWrJ`), the copy loops
(`rrJ_loop0`, `rrJ_loop1`, `rrJ_loopGB`; the buffer words by
`JAtZ.bufWord`) and the message info and `Running` (`JAtZ.rrTailJ`); not
called, `Running` (`JAtZ.runJ`, `XTop`'s facts by `nodata_tail_core`). -/
theorem JAtZ.readRegsJW {s1 : S} {σ1 : Fl4Spec.State Unit} {ct p : U64} {blk call don : Bool}
    (J1 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a σ1) [VxE Z] (hC1 : SInvCk.CKI σ1)
    (hns : ∀ u, σ1.schedulerAction = .switchThread u → False) (hidp : p.bv ≠ σ1.idleThread)
    (hcur1 : σ1.curThread = ct.bv) {x1 : Fl4Spec.Tcb} (hkc1 : σ1.kheap ct.bv = some (.tcb x1))
    (hrs1 : x1.tcbState = .restart) (hpne : p ≠ ct) (hpT : p ∈ Z.T) (flags n : U64) :
    tcb.read_registers st arI s1 a p ((flags &&& 1#u64) != 0#u64) n call ⦃ r =>
      L.mem r.1 (stA ct) ≠ sched.TS_RESTART ∧ ∃ rr σy,
        (.ok rr, σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.readRegisters p.bv
          (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 ∧
        ∃ z ∈ (specTail call ct.bv rr σy).1, RelTopM (L := L) r.1 z.2 ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 z.2 ∧
          P1.WritesIn st s1 r.1 (Mc.ProjW (L := L) H Cs s1) ⦄ := by
  have hI1 := J1.xtop.irelK J1.ks J1.buf
  have hctT : ct ∈ Z.T := TopSR.cur_mem J1.xtop.fin.1 hcur1.symm
  have hne : p.bv ≠ ct.bv := fun e => hpne (P1.eq_of_bv e)
  unfold tcb.read_registers
  refine WP.spec_bind (cur_thread_bv hI1.2.2.1) ?_
  rintro ct' hct'
  obtain rfl : ct = ct' := (P1.eq_of_bv (hct'.trans hcur1)).symm
  rw [and1_ne0]
  -- the source's suspend
  have hsus : (if Fl4Spec.testBit flags.bv 0 = true then sched.suspend st arI s1 a p else ok (s1, a)) ⦃ r =>
      (r.2 = a ∧ ∃ σy, Fl4Spec.NonDet.when (Fl4Spec.testBit flags.bv 0 = true) (Fl4Spec.suspend (Z := Unit) p.bv) σ1 =
        ({((), σy)}, False) ∧ StK.OSK p.bv σ1 σy ∧
        ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σy) ∧
        P1.WritesIn st s1 r.1 (Mc.ProjW (L := L) H Cs s1) ⦄ := by
    cases Fl4Spec.testBit flags.bv 0
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨⟨trivial, σ1, rfl, StK.OSK.refl _, Z.vs, Ac, Lst, D, J1⟩, P1.WritesIn.refl _ _⟩
    · simp only [↓reduceIte]
      refine WP.spec_mono (WP.spec_and (J1.suspendJ (jCancel_send arI) (jCancel_ntfn arI) (jCancel_recv arI)
        (jCancel_reply arI) hpT (fun u h => (hns u h).elim) hidp) (J1.suspendProjW hpT)) ?_
      rintro ⟨s2, a2⟩ ⟨⟨h1, σy, h2, V, Ac', Lst', D', J2⟩, Ws⟩
      refine ⟨⟨h1, σy, by simpa [Fl4Spec.NonDet.when] using h2, StK.st_suspend σ1 ((), σy) ?_, V, Ac', Lst', D', J2⟩, Ws⟩
      rw [h2]; exact Set.mem_singleton _
  refine WP.spec_bind hsus ?_
  rintro ⟨s2, a2⟩ ⟨⟨ha2, σy, hsy, hosk, V2, Ac2, Lst2, D2, J2⟩, W2⟩
  obtain rfl : a = a2 := ha2.symm
  simp only at J2 W2
  -- the caller and the source after it
  have hXy := J2.xtop.irelK J2.ks J2.buf
  obtain ⟨xy, hky, -⟩ := hXy.1.tcb ct hctT
  obtain ⟨y0, hy0, hys⟩ := hosk.1 ct.bv xy (Ne.symm hne) hky
  rw [hkc1] at hy0; cases hy0
  have hrs : xy.tcbState = .restart := hys.trans hrs1
  have hcury : ct.bv = σy.curThread := (hosk.2.trans hcur1).symm
  obtain ⟨xs, hks, -⟩ := hXy.1.tcb p hpT
  have hXZ := J2.xtop
  have hOKb := J2.xferH.1
  have hBCy := J2.xferH.2.1
  have hBPy := J2.xferH.2.2
  have hact := J2.kern.act
  have htcb : (Z.mv Z.G V2).th ct = some .tcb := (hXZ.curTcb hcury.symm).1
  -- the spec's ReadRegisters
  have hmem : ((.ok (rrOf xs n) : Except Unit (List Fl4Spec.Data)), σy) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB (.readRegisters p.bv
        (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 := by
    show _ ∈ ((Fl4Spec.invokeTcb (Z := Unit) _).run σ1).1
    unfold Fl4Spec.invokeTcb
    refine mem_liftE (x := (rrOf xs n, σy)) (mem_bind_nd (x := ((), σy)) (by rw [hsy]; rfl)
      (mem_bind_nd (x := (σy.curThread, σy)) rfl (mem_bind_nd rfl ?_)))
    rw [asUser_mapM_get hks]
    exact Set.mem_singleton _
  cases call
  · -- not called: `Running`
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (WP.spec_and (nodata_tail_core hXZ hcury hky hrs hact (rrOf xs n))
      (WP.spec_and (J2.runJ hctT hky hrs) (stsProjW J2 hctT sched.TS_RUNNING))) ?_
    rintro s3 ⟨⟨hne3, z, hz, hRT, -⟩, ⟨Lst', D', J5⟩, W5⟩
    refine (WP.spec_ok _).2 ⟨hne3, rrOf xs n, σy, hmem, z, hz, hRT, ?_⟩
    unfold specTail at hz
    rw [nd_bind_one (Notif.getThreadState_eq hky)] at hz
    simp only [hrs] at hz
    rw [Endp.nd_when_false (by simp), Notif.nd_pure_bind', Notif.setThreadState_eq .running hky] at hz
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨J5.stab.mv, W2.projW_trans W5⟩
  -- called: the caller's buffer, the badge, the words, the message info and `Running`
  simp only [↓reduceIte]
  obtain ⟨x', hk', hwx⟩ := J2.buf ct hctT
  rw [hky] at hk'; cases hk'
  have hCy : SInvCk.CKI σy := SInvCk.ck_fl4Perform blk true don (.invokeTCB (.readRegisters p.bv
    (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters)) trivial σ1 hC1 _ hmem
  have hb0 : msg.lookup_ipc_buffer st s2 true ct = ok 0#u64 := Mc.lookup_ipc_buffer_cki J2 hCy htcb true
  refine WP.spec_bind (WP.spec_and (lookup_buf_full s2 σy hXZ.rel.2.1.1 hXZ.rel.2.1.2.1 htcb hky hOKb true)
    (show msg.lookup_ipc_buffer st s2 true ct ⦃ b => b = 0#u64 ⦄ by rw [hb0]; exact (WP.spec_ok _).2 rfl)) ?_
  rintro bf ⟨⟨hw0, hwp⟩, rfl⟩
  have hbm : ∀ q, Endp.ipcBufOf true xy = some q → Endp.BufMap Z.B 0#u64 q := fun q hq =>
    hBCy ct hctT xy true q hky hq 0#u64 (hwp hwx q hq)
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s2 ct _ 0#u64) ?_
  rintro s3 rfl
  rw [← Endp.regIdx_badge]
  have W3 : P1.WritesIn st s1 (L.wr s2 (regA ct (regIdx Fl4Spec.badge_register)) 0#u64) (Mc.ProjW (L := L) H Cs s1) :=
    W2.projW_trans (J1.regProjW hctT Fl4Spec.badge_register s2 0#u64)
  set xb := Notif.setReg xy Fl4Spec.badge_register 0 with hxb
  set σb := Notif.updK σy ct.bv (.tcb xb) with hσb
  have hkb : σb.kheap ct.bv = some (.tcb xb) := by simp [hσb, Notif.updK]
  have hksb : σb.kheap p.bv = some (.tcb xs) := by simp [hσb, Notif.updK, hne, hks]
  have hXb := badge_wr_irel J2.ip hXy hctT hky 0#u64
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V3, J3⟩ := J2.regWrJ hctT hky Fl4Spec.badge_register 0#u64 hXb
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  rw [e0] at J3
  have J0 : JAtZ (L := L) arI AR (Z.mv Z.G V3) H Cs Ac2 Lst2 D2
      (L.wr s2 (regA ct (regIdx Fl4Spec.badge_register)) 0#u64) a (MrS σb ct.bv xb (Endp.ipcBufOf true xy) []) := by
    rw [MrS_nil hkb]; exact J3
  have hOK3 := J3.xferH.1
  have hWOK : ∀ q, Endp.ipcBufOf true xy = some q → ∀ i : U64, i.val < 128 →
      BufWordOK H σb (fl4BufA 0#u64 i) := fun q hq i hi =>
    J3.bufWord hOK3 htcb hkb hq i.val hi (by rw [fl4BufA_bv, hwp hwx q hq])
  have hks3 : L.ksb (L.wr s2 (regA ct (regIdx Fl4Spec.badge_register)) 0#u64) = L.ksb s2 := L.ksb_wr _ _ _
  have hlenR := rrOf_length xs n
  have hfr : ∀ q, Endp.ipcBufOf true xy = some q → ∀ z ∈ Endp.mrPairs (rrOf xs n),
      (Endp.bufAddr q z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q z.1) σy :=
    fun q hq z hz => ⟨Endp.bufAddr_aligned hXZ.fin.1.2.ep (hbm q hq) z.1,
      buf_frame_of_ok hOKb hky hq z.1 (mrPairs_lt hz)⟩
  refine WP.spec_bind (rrJ_loop0W J0 hctT hne hpT hksb n) ?_
  rintro ⟨s4, i⟩ ⟨hiv, ⟨V4, J4⟩, hk4, hc4, W4⟩
  simp only at hiv J4 hk4 hc4 W4
  try simp only [uncurry_apply_pair]
  have fin : ∀ (s5 : S) (len : U64),
      JAtZ (L := L) arI AR (Z.mv Z.G V4) H Cs Ac2 Lst2 D2 s5 a
        (MrS σb ct.bv xb (Endp.ipcBufOf true xy) (rrOf xs n)) →
      P1.WritesIn st s1 s5 (Mc.ProjW (L := L) H Cs s1) →
      len.val = mrLen (Endp.ipcBufOf true xy) (rrOf xs n).length →
      (do
        let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 len
        let s6 ← msg.set_msg_info st s5 ct mi
        let s7 ← sched.set_thread_state st s6 ct sched.TS_RUNNING
        ok (s7, a)) ⦃ r => L.mem r.1 (stA ct) ≠ sched.TS_RESTART ∧ ∃ rr σy',
        (.ok rr, σy') ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk true don (.invokeTCB (.readRegisters p.bv
          (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters))).run σ1).1 ∧
        ∃ z ∈ (specTail true ct.bv rr σy').1, RelTopM (L := L) r.1 z.2 ∧
          JStab (L := L) arI AR Z H Cs r.1 r.2 z.2 ∧ P1.WritesIn st s1 r.1 (Mc.ProjW (L := L) H Cs s1) ⦄ := by
    intro s5 len J5 W5 hl
    refine WP.spec_mono (J5.rrTailJW hctT hcury hky hrs
      (by rw [hlenR]; unfold Fl4Spec.msgMaxLength; omega) hfr len hl
      (by rw [hl]; cases Endp.ipcBufOf true xy <;> simp [mrLen, hlenR] <;> omega)) ?_
    rintro r ⟨hne5, z, hz, hRT, hJT, Wr⟩
    exact ⟨hne5, rrOf xs n, σy, hmem, z, hz, hRT, hJT.mv, W5.projW_trans Wr⟩
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hg : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
  -- no buffer (`CKI`): the message registers only
  have hbn : Endp.ipcBufOf true xy = none := hw0.1 rfl
  have hbb : ((0#u64 : U64) != 0#u64) = false := by simp
  simp only [hbb, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (rr_loopGR n s4 _ (fun _ _ => rfl)) ?_
  rintro ⟨s5, k⟩ hk5
  obtain ⟨rfl, rfl⟩ : s4 = s5 ∧ k = 0#u64 := ⟨(Prod.mk.inj hk5).1.symm, (Prod.mk.inj hk5).2⟩
  try simp only [uncurry_apply_pair]
  simp only [lift, bind_ok]
  refine fin s4 _ ?_ (W3.projW_trans W4) ?_
  · rw [hbn] at J4 ⊢
    by_cases hn4 : n.val ≤ 4
    · rw [hiv, show min n.val 4 = (rrOf xs n).length by rw [hlenR]; omega, List.take_length] at J4; exact J4
    · rw [hiv, show min n.val 4 = 4 by omega] at J4
      simp only [MrS] at J4 ⊢
      rw [← List.take_append_drop 4 (rrOf xs n), Endp.mrStateN_append_ge _ _ _ _ _ (by simp [hlenR]; omega)]
      exact J4
  · rw [hbn, hlenR]
    simp [mrLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **ReadRegisters at stable ghosts, with its `ProjW` footprint, at a `CKI` state** (XTopJointTcb's
`tcb_read_regsJ`; module docstring). -/
theorem tcb_read_regsJSt (s : S) (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ) (hC : SInvCk.CKI σ) (p : U64) (hpT : p ∈ Z.T) (hpI : p ≠ L.idleW s) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .tcbReadRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (call : Bool) (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKRX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBReadRegisters p ⟨length, buf, call, slot, extra⟩
      blk call don slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
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
      obtain ⟨s1, σ1, x1, hrc1, hst1, hk1, -, hσ1, hns, hid1, hcu1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
      have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
        have h := stsProjW J (J.thT ct htcb) sched.TS_RESTART
        rw [hs1, WP.spec_ok] at h; exact h
      have hC1 : SInvCk.CKI σ1 := by rw [hσ1]; exact SInvCk.cki_sts hC hk1 .restart
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
      refine WP.spec_bind (J1.readRegsJW (blk := blk) (don := don) hC1 hns
        (by rw [hid1]; exact J.ne_idle hpI) (by rw [hcu1]; exact hcur) hkc1 rfl hpc hpT y0 y1) ?_
      rintro ⟨s2, a2⟩ ⟨hne, rr, σy, hm, z, hz, hRz, hXz, Wz⟩
      exact (WP.spec_ok _).2 (Or.inr ⟨rfl, hne, _, DecOut.of_eq hdec, σ1, hst1, rr, σy, hm, z, hz, hRz, hXz,
        W1.projW_trans Wz⟩)
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

end

/-- (p3J gen 42) The Thread labels left after ReadRegisters. -/
def ThHard16 (l : U64) : Prop := ThHard15 l ∧ l ≠ fl4_abi.label.TCBReadRegisters

/-- (p3J gen 42) The caps left after the ReadRegisters leaf, with the message label. -/
def IsRestCap24 : capability.Cap → U64 → Prop
  | .CNode .., l => CnDel l
  | .Thread _, l => ThHard16 l
  | _, _ => False

theorem restCap23_of24 {cp : capability.Cap} {l : U64} (h : IsRestCap24 cp l) : IsRestCap23 cp l := by
  cases cp
  case CNode => exact h
  case Thread => exact h.1
  all_goals exact False.elim h

theorem restCap24_of {cp : capability.Cap} {l : U64} (h : IsRestCap23 cp l)
    (hS : ¬ ∃ p, cp = .Thread p ∧ l = fl4_abi.label.TCBReadRegisters) : IsRestCap24 cp l := by
  cases cp
  case CNode => exact h
  case Thread p => exact ⟨h, fun hc => hS ⟨p, rfl, hc⟩⟩
  all_goals exact False.elim h

theorem rr_nonIns : TcbNonIns fl4_abi.label.TCBReadRegisters := by
  unfold TcbNonIns fl4_abi.label.TCBReadRegisters fl4_abi.label.TCBSetEPTRoot fl4_abi.label.TCBConfigure
    fl4_abi.label.TCBSetSchedParams fl4_abi.label.TCBSetIPCBuffer fl4_abi.label.TCBSetSpace
    fl4_abi.label.TCBSetTimeoutEndpoint
  decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **The Thread cap's decode at a dispatch state at ReadRegisters, any flags** (module docstring). -/
theorem decThRrSt (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR)
    [VxE Z] {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb) (hnib : Entered σb) (hsgb : SpecGlob σb) (hCb : SInvCk.CKI σb)
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
    (hget : Fl4Spec.getCap (Z := Unit) sl σb = ({(absCap (.Thread p), σb)}, False))
    {e : Aeneas.Std.Array obj.Slot 3#usize} {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (he : r2 = .Ok e) (hexs : er = .ok exs)
    (hl : info.label = fl4_abi.label.TCBReadRegisters) (bl call don fp : Bool) (ci : Fl4Spec.CapRef) :
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
  obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
  rw [← hLb]
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨q, hq, hth⟩ := hsl; exact ⟨q, hq, Or.inl hth⟩
  have hsc : capV (L.mem s') (cslotAddr sl) = .Thread p := capV_of_capAt hc
  have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop hAs hsc).2
  have hpT : p ∈ (Z.mv Z.G V').T := J.thT p hp
  have hpI : p ≠ L.idleW s' := J.capNotIdle hsgb hget
  rw [hl]
  obtain ⟨sl', hlbl, -, hd⟩ := tcb_canon fl4_abi.label.TCBReadRegisters
  have hl5 : fl4_abi.label.TCBReadRegisters.val ≠ 5 ∧ fl4_abi.label.TCBReadRegisters.val ≠ 8 ∧
      fl4_abi.label.TCBReadRegisters.val ≠ 9 ∧ fl4_abi.label.TCBReadRegisters.val ≠ 10 ∧
      fl4_abi.label.TCBReadRegisters.val ≠ 11 := by simp [fl4_abi.label.TCBReadRegisters]
  refine XCapP.lbl_congr arI (specDec_thread p hd) ?_
  refine XCapP.mrGT (f := id) hMT ?_
    (WP.spec_mono (MKD.decode_thread_nonins L.total hA hKD rr_nonIns hMb) fun r h => by split <;> exact h)
    (perfF_tcbN hlbl hl5 σb bl call don fp _ ci sl exs buffer p)
  refine XCap.toPN arI ?_ (thread_noPre_of hlbl hl5)
  right
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact tcb_read_regsJSt s' a' σb J hnib hCb p hpT hpI sl' (by rw [hlbl]; simp [tcbLabelOf]) _ buf ct hct argsU
      hLen hArgs (J.stallT p hpT) call _ e bl don ci sl exs buffer
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hX0⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **`MidDecStWL` at `KW ∧ IsRestCap23` from the ReadRegisters leaf** (module docstring). -/
theorem midDecRest23_of_rr (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap24 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap23 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBReadRegisters
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsgb⟩ := dispEnteredSg hnd hX hni hBA
    exact decThRrSt hA hT hMT hKD J hnib hsgb hCb hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc hget he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap24_of hW.2 hS⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **`InvDecStWL` at `KW ∧ IsRestCap23` from the ReadRegisters leaf** (module docstring). -/
theorem invDecRest23_of_rr (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hMT : MachPlat arI MR)
    (hKD : MRKeepD arI MR) [VxE Z] {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap24 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap23 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hS : ∃ p, cp = .Thread p ∧ info.label = fl4_abi.label.TCBReadRegisters
  · obtain ⟨p, rfl, hl⟩ := hS
    obtain ⟨hnib, hsgb⟩ := dispEnteredSg hnd hX hni hBA
    exact decThRrSt hA hT hMT hKD J hnib hsgb hCb hMb hct a1 a2 a3 a4 a5 a6 a7 sl hsl hc hget he hexs hl _ _ _ _ _
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap24_of hW.2 hS⟩

/-- (p3J gen 42) `MidDecStWL` at `KW ∧ IsRestCap23` gives it at `KW ∧ IsRestCap24` (antitone). -/
theorem midDecStWL_of_23 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap23 cp l) Z H Cs s a σ n c) :
    MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap24 cp l) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap23_of24 hW.2⟩

/-- (p3J gen 42) `InvDecStWL` at `KW ∧ IsRestCap23` gives it at `KW ∧ IsRestCap24` (antitone). -/
theorem invDecStWL_of_23 {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool}
    (h : InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap23 cp l) Z H Cs s a σ n
      call bl don) :
    InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap24 cp l) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap23_of24 hW.2⟩

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

/-- (p3J gen 42) **`DispStabFootLzq` [J]**: `DispStabFootLzp` with `invDecRest` / `midDecRest` restricted to
`IsRestCap24` (`IsRestCap23` minus the Thread caps at ReadRegisters; module docstring). -/
structure DispStabFootLzq (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzp.invDecRest` at `KW ∧ IsRestCap24`. -/
  invDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (call bl don : Bool),
        σ.curThread ≠ σ.idleThread → InvSys n call bl don → SysFlag (L := L) s →
        SysK6 (L := L) arI AR Z H Cs s a σ n (invSysOf call bl) →
        InvDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap24 cp l) Z H Cs s a σ n
          call bl don
  /-- `DispStabFootLzp.midDecRest` at `KW ∧ IsRestCap24`. -/
  midDecRest : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidDecStWL (L := L) arI AR MR (fun cp l => SInvCk.KW (absCap cp) ∧ IsRestCap24 cp l) Z H Cs s a σ n c
  /-- `DispStabFootLzp.midSpec`, verbatim. -/
  midSpec : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidSpecAt σ
  /-- `DispStabFootLzp.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 42) **`DispStabFootLzq → DispStabFootLzp`** under the tops' platform facts (module docstring). -/
theorem dispStabFootLzp_of_Lzq (hA : P0.ArchTotal arI) (hT : TimeAgree arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFootLzq (L := L) arI AR MR s a σ) :
    DispStabFootLzp (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact invDecRest23_of_rr hA hT hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    haveI := hV
    exact midDecRest23_of_rr hA hT hnd (MachPlatF.toT hM hIp) hKD hX hct
      (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

/-- (p3J gen 42) **`DispStabFootLzp → DispStabFootLzq`** (the honesty claim: `DispStabFootLzq` is implied). -/
theorem dispStabFootLzq_of_Lzp {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzp (L := L) arI AR MR s a σ) : DispStabFootLzq (L := L) arI AR MR s a σ where
  invDecRest := fun hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6 =>
    invDecStWL_of_23 (h.invDecRest hR Z H Cs Ac Lst D J hV n call bl don hct hi hfl hk6)
  midDecRest := fun hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6 =>
    midDecStWL_of_23 (h.midDecRest hR Z H Cs Ac Lst D J hV n c hct hm hfl hk6)
  midSpec := h.midSpec
  midRecvSw := h.midRecvSw

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootLzq` only** (`hLzq` [J];
module docstring). -/
theorem kernel_entry_runMcWKR_sysLzq [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hLzq : DispStabFootLzq (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzp hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFootLzp_of_Lzq hA hT hnd hM hIp hKD hLzq)

end

end Fl4Proofs.P3.Mc
