/-
P3 (DESIGN.md §9), IPC: **the timeout fault of a thread with a scheduling
context sent to a waiting receiver** (toward XTopJointIpcJ's reply tail:
`handle_timeout` of the replied-to thread when receivers wait on its timeout
handler's endpoint).

FL4's `set_mrs_fault` of a timeout fault runs `update_consumed` on the
sender's SC (the SC's `CONSUMED` word to 0) before the two message words
(the badge and the consumed time, both message registers: no receive-buffer
word is written).

* `set_mr_rgR`: `set_mr` of a register word, its footprint and result.
* `do_ipc_transfer_tmo_rg`: FL4's footprint of the transfer from the state
  after the SC word (`tmoS`): the receiver's registers only.
* `set_mrs_fault_tmoSC_E`, `set_mrs_fault_tmoSCN_E`, `do_ipc_transfer_tmoE`:
  IpcTmo's `set_mrs_fault_tmoSC(N)` / `tmoXfer_top` with the endpoint
  hypotheses (`EpHyps`) instead of `IpcSchedHyps`, with or without a receive
  buffer, the base of the frame the state after the SC step.
* `xferTmoStepJ`: the transfer step of `send_ipc` to a waiting receiver for
  a sender with a timeout fault and an SC (as XTopJointFaultRecv's
  `xferFaultStepJ`): the spec's outcome `updK (tmoSt σ sc y n) rcv x'`, the
  FL4 footprint the SC word and the receiver's registers, P1 by
  `XS.consumed` then `xfer_all`.
-/
import Fl4Proofs.P3.XTopJointFaultRecv
import Fl4Proofs.P3.XTopJointSendBlockG
import Fl4Proofs.P3.IpcTmo
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- `set_mr` of a word `i < 4` (a message register): the receiver's
registers, and the next index. -/
theorem set_mr_rgR {T : Set U64} (hT : P1.TcbPlaced T) {s0 s : S} {rcv rw i v : U64} (hr : rcv ∈ T)
    (hi : i.val < 4) (h : P1.WritesIn st s0 s (XferRegW T ∅)) :
    msg.set_mr st s rcv rw i v ⦃ r => r.1 = core.num.U64.wrapping_add i 1#u64 ∧
      P1.WritesIn st s0 r.2 (XferRegW T ∅) ⦄ := by
  have hc : i < msg.N_MSG_REGISTERS := by
    unfold msg.N_MSG_REGISTERS; scalar_tac
  unfold msg.set_mr
  rw [if_pos hc]
  refine WP.spec_bind (msg.msg_register.lt i) fun rg hrg => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.rg (v := v) (s := s) hT hr hrg) fun s2 w2 => ?_
  simp only [lift, bind_ok, WP.spec_ok]
  exact ⟨by trivial, rg_trans h w2⟩

theorem scW8_eq (sc : U64) : scW sc 8#u64 = core.num.U64.wrapping_add sc layout.sc.CONSUMED := by
  unfold scW layout.sc.CONSUMED; rfl

/-- **`do_ipc_transfer`'s footprint, a sender with a timeout fault and an
SC** (`hU`: `update_consumed` writes the SC word, `tmoS`): from the state
after it, the receiver's registers only. -/
theorem do_ipc_transfer_tmo_rg {T : Set U64} (hT : P1.TcbPlaced T) {snd rcv : U64} (hr : rcv ∈ T) (s : S) (a : A)
    (ep badge : U64) (grant : Bool) {sc : U64}
    (hty : L.mem s (tFaultA snd) = 5#u64) (hsc : L.mem s (P1.scA snd) = sc)
    (hsc0 : sc ≠ 0#u64)
    (hU : schedcontext.update_consumed st arI s a sc ⦃ r => r.2 = tmoS st s sc ⦄) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' =>
      P1.WritesIn st (tmoS st s sc) s' (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s true rcv hS) fun rb _ => ?_
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_
  rintro ft rfl
  rw [hty, if_neg (by unfold fl4_abi.consts.fault.NullFault; decide)]
  unfold ipc.do_fault_transfer
  refine WP.spec_bind (Pₘ := fun r : U64 × S => P1.WritesIn st (tmoS st s sc) r.2 (XferRegW T ∅)) ?_ ?_
  · unfold faults.set_mrs_fault
    refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_; rintro _ rfl
    refine WP.spec_bind (Endp.obj.Tcb.fault_w0.spec s snd) ?_; rintro _ rfl
    refine WP.spec_bind (Endp.obj.Tcb.fault_w1.spec s snd) ?_; rintro _ rfl
    refine WP.spec_bind (Endp.obj.Tcb.fault_w2.spec s snd) ?_; rintro _ rfl
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s snd _) ?_; rintro _ rfl
    rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
      ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
      ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
      ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.Timeout; rfl))]
    refine WP.spec_bind (Fl4Proofs.P1.obj.Tcb.sc.spec s snd) ?_
    rintro i rfl
    unfold obj.Sc.is_null
    apply ok_bind_spec
    simp only [hsc, hsc0, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind hU ?_
    rintro ⟨cv, s1⟩ hs1
    simp only at hs1
    subst hs1
    refine WP.spec_bind (set_mr_rgR (rw := rb) (i := 0#u64) (v := L.mem s (tFw0A snd)) hT hr (by decide)
      (P1.WritesIn.refl _ _)) ?_
    rintro ⟨k, s2⟩ ⟨hk, h2⟩
    simp only at hk h2
    subst hk
    exact WP.spec_mono (set_mr_rgR hT hr (by decide) h2) fun r hr' => hr'.2
  rintro ⟨sent, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s1 hS) fun ft _ => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  refine WP.spec_bind (Pₘ := fun s3 => P1.WritesIn st (tmoS st s sc) s3 (XferRegW T ∅)) ?_
    fun s3 h3 => WP.spec_mono (obj.Tcb.set_reg.rg (s := s3) (v := badge) hT hr
      (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s4 w4 => rg_trans h3 w4
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    WP.spec_mono (obj.Tcb.set_reg.rg (v := w) (s := s1) hT hr (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => rg_trans h1 w4

end

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 2000000 in
/-- IpcTmo's `set_mrs_fault_tmoSC` from `EpHyps`. -/
theorem set_mrs_fault_tmoSC_E (hE : EpHyps st T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))))
    (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {b : Fl4Spec.Word} (hf : xs.tcbFault = some (.timeout b)) {sc : U64} (hsc : L.mem s (scA snd) = sc)
    (hsc0 : sc ≠ 0#u64) (hscC : sc ∈ C) {y : Fl4Spec.SchedContext} {n : Nat}
    (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p) :
    faults.set_mrs_fault st ar s a snd rcv rw ⦃ r => r.1.val = [b, consumedUs y.scConsumed].length ∧
      MrInv (L := L) T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (tmoS st s sc)
        (tmoSt σ sc y n) rcv xr p r.2 [b, consumedUs y.scConsumed] ⦄ := by
  have hP := hP0.e
  have hxs := hX.1.toE.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  have hrsc : rcv.bv ≠ sc.bv := kheap_ne hkr hky (fun _ h1 h2 => by subst h1; cases h2)
  unfold faults.set_mrs_fault
  step with obj.Tcb.fault_type.spec as ⟨ty, hty'⟩
  step with obj.Tcb.fault_w0.spec as ⟨w0, hw0'⟩
  step with obj.Tcb.fault_w1.spec as ⟨w1, hw1'⟩
  step with obj.Tcb.fault_w2.spec as ⟨w2, hw2'⟩
  step with Endp.obj.Tcb.reg.spec as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.Timeout; rfl))]
  step with obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  unfold obj.Sc.is_null
  apply ok_bind_spec
  simp only [hsc, hsc0, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (update_consumed_irel hP0 s a σ hX hscC hky hmax htu) ?_
  rintro ⟨cv, s1⟩ ⟨hs1, hcv, -, hI1⟩
  simp only at hs1 hcv hI1
  subst hs1
  have hkr1 : (tmoSt σ sc y n).kheap rcv.bv = some (.tcb xr) := by simp [updK, hrsc, hkr]
  have hM0 := mrInv_init (L := L) (SR := SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    hI1.1.toE ⟨hI1.2, ScRelM.of hI1.1⟩ hkr1 p
  refine WP.spec_bind (set_mr_inv (L := L) hE hP hr hkr1 hrw0 hmr hM0 0#u64 rfl (by decide)
    (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s2⟩ ⟨hk, hM1⟩
  simp only at hk hM1
  refine WP.spec_mono (set_mr_inv (L := L) hE hP hr hkr1 hrw0 hmr hM1 k (by simpa using hk) (by simp at hk; omega)
    cv) ?_
  rintro ⟨k2, s3⟩ ⟨hk2, hM2⟩
  simp only at hk2 hM2 ⊢
  rw [hw0, hcv] at hM2
  exact ⟨by simp at hk hk2 ⊢; omega, hM2⟩

set_option maxHeartbeats 2000000 in
/-- IpcTmo's `set_mrs_fault_tmoSCN` from `EpHyps`. -/
theorem set_mrs_fault_tmoSCN_E (hE : EpHyps st T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))))
    (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {b : Fl4Spec.Word} (hf : xs.tcbFault = some (.timeout b)) {sc : U64} (hsc : L.mem s (scA snd) = sc)
    (hsc0 : sc ≠ 0#u64) (hscC : sc ∈ C) {y : Fl4Spec.SchedContext} {n : Nat}
    (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    faults.set_mrs_fault st ar s a snd rcv 0#u64 ⦃ r => r.1.val = min [b, consumedUs y.scConsumed].length 4 ∧
      MrInvN (L := L) T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) (tmoS st s sc)
        (tmoSt σ sc y n) rcv xr r.2 [b, consumedUs y.scConsumed] ⦄ := by
  have hP := hP0.e
  have hxs := hX.1.toE.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  have hrsc : rcv.bv ≠ sc.bv := kheap_ne hkr hky (fun _ h1 h2 => by subst h1; cases h2)
  unfold faults.set_mrs_fault
  step with obj.Tcb.fault_type.spec as ⟨ty, hty'⟩
  step with obj.Tcb.fault_w0.spec as ⟨w0, hw0'⟩
  step with obj.Tcb.fault_w1.spec as ⟨w1, hw1'⟩
  step with obj.Tcb.fault_w2.spec as ⟨w2, hw2'⟩
  step with Endp.obj.Tcb.reg.spec as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.Timeout; rfl))]
  step with obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  unfold obj.Sc.is_null
  apply ok_bind_spec
  simp only [hsc, hsc0, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (update_consumed_irel hP0 s a σ hX hscC hky hmax htu) ?_
  rintro ⟨cv, s1⟩ ⟨hs1, hcv, -, hI1⟩
  simp only at hs1 hcv hI1
  subst hs1
  have hkr1 : (tmoSt σ sc y n).kheap rcv.bv = some (.tcb xr) := by simp [updK, hrsc, hkr]
  have hM0 := mrInvN_init (L := L) (SR := SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    hI1.1.toE ⟨hI1.2, ScRelM.of hI1.1⟩ hkr1
  refine WP.spec_bind (set_mr_invN (L := L) hE hP hr hkr1 hM0 0#u64 rfl (by decide)
    (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s2⟩ ⟨hk, hM1⟩
  simp only at hk hM1
  refine WP.spec_mono (set_mr_invN (L := L) hE hP hr hkr1 hM1 k (by simpa using hk) (by simp at hk; omega)
    cv) ?_
  rintro ⟨k2, s3⟩ ⟨hk2, hM2⟩
  simp only at hk2 hM2 ⊢
  rw [hw0, hcv] at hM2
  exact ⟨by simp at hk hk2 ⊢; omega, hM2⟩

set_option maxHeartbeats 4000000 in
/-- **`do_ipc_transfer` of a timeout fault from a thread with an SC on
`IRel`** (IpcTmo's `tmoXfer_top` from `EpHyps`, the receive buffer by
`lookup_buf_full` with `IpcBufCapOK` and `BufCover`): the frame's base is the
state after the SC step (`tmoS`, `tmoSt`). -/
theorem do_ipc_transfer_tmoE (hE : EpHyps st T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))))
    (hP0 : IPlaced N T E R B) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hX : IRel st th cr N T C E R B c s σ) (hOK : Endp.IpcBufCapOK σ) (hBC : Endp.BufCover T B σ)
    {t d : U64} (ht : t ∈ T) (hd : d ∈ T) (htd : t ≠ d) {xt xd : Fl4Spec.Tcb}
    (hks : σ.kheap t.bv = some (.tcb xt)) (hkd : σ.kheap d.bv = some (.tcb xd))
    {bb : Fl4Spec.Word} (hf : xt.tcbFault = some (.timeout bb)) {sc : U64} (hscx : xt.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (e bdg : U64) (g : Bool) :
    ipc.do_ipc_transfer st ar s a t e bdg g d ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) t.bv (some e.bv) bdg.bv g d.bv σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧
      SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s' σ' ∧
      Agree (L.mem (tmoS st s sc)) (L.mem s') (fun b => ¬ RcvReg d b ∧ ¬ BufW B b) ∧
      (∀ q, q ≠ d.bv → σ'.kheap q = (tmoSt σ sc y n).kheap q) ∧
      ∃ x', σ'.kheap d.bv = some (.tcb x') ∧ x'.tcbState = xd.tcbState ⦄ := by
  have hP := hP0.e
  have hR := hX.1.toE
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hsp⟩ := hS.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb t ht
  rw [hks] at hk0; cases hk0
  have hsc0 : L.mem s (scA t) ≠ 0#u64 := (Notif.optRef_some (hscw.symm.trans hscx)).1
  have hsce : L.mem s (scA t) = sc := P1.eq_of_bv (Notif.optRef_some (hscw.symm.trans hscx)).2
  have hscC : sc ∈ C := by rw [← hsce]; exact hsp.scMem t ht hsc0
  rw [hsce] at hsc0
  have hdsc : d.bv ≠ sc.bv := kheap_ne hkd hky (fun _ h1 h2 => by subst h1; cases h2)
  have hkd' : (tmoSt σ sc y n).kheap d.bv = some (.tcb xd) := by simp [updK, hdsc, hkd]
  have hupd := schedContextUpdateConsumed_eq hky hmax
  have hmsg := makeFaultMsg_timeoutSC hks hscx hupd bb
  have hxs := hR.at_tcb ht hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  have hta := hP.tcb t ht
  have hscw8 : ScW st C c s σ (scW sc 8#u64) := Or.inl (sw_hdr hS hscC (K := 8#u64) (by simp) (by simp) (by decide))
  have hnot : ∀ b, IFoot N T E R B b → b ≠ scW sc 8#u64 := fun b hb e => scw_not_ifoot hP0 hS hX.2.2.2 (e ▸ hscw8) hb
  obtain ⟨y', n', hky', hy⟩ := hsp.scs sc hscC
  rw [hky] at hky'; cases hky'
  have hal8 : Aligned (scW sc 8#u64) := (hy.hdr (K := 8#u64) (by simp) (by simp)).1
  have hty0 : L.mem (tmoS st s sc) (tFaultA t) = 5#u64 := by
    rw [rd_wr_ne hal8 (a_fault hta).1 (fun e => hnot _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl
      (a_fault hta).2⟩)))) e.symm)]
    exact hfr.1
  obtain ⟨⟨⟨G, hBt⟩, hBw⟩, -⟩ := (IpcRel.toSRN hX.1 hX.2).1.1
  have hspec : Fl4Spec.doIpcTransfer (Z := Unit) t.bv (some e.bv) bdg.bv g d.bv σ =
      Fl4Spec.doFaultTransfer (Z := Unit) bdg.bv t.bv d.bv (ipcBufOf true xd) σ := by
    unfold Fl4Spec.doIpcTransfer
    rw [nd_bind_one (lookupIpcBuffer_eq hkd true), nd_bind_one (threadGet_eq _ hks), hf]
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (lookup_buf_full s σ hBt.2.1.1 hBt.2.1.2.1 (Ipc.RelTopB.tcbT hBt hkd) hkd hOK true) ?_
  rintro rw ⟨hrw0, hrwp⟩
  step with obj.Tcb.fault_type.spec as ⟨ft, hft⟩
  have hft0 : ¬ ft = fl4_abi.consts.fault.NullFault := by
    intro h
    have : L.mem s (tFaultA t) = 0#u64 := by rw [← hft, h]; unfold fl4_abi.consts.fault.NullFault; rfl
    rw [hxs.fault0.1 this] at hf; cases hf
  simp only [hft0, ↓reduceIte]
  rw [hspec]
  cases hrb : ipcBufOf true xd with
  | none =>
    obtain rfl : rw = 0#u64 := hrw0.2 hrb
    exact do_fault_transfer_fullN hE hP s a σ ht hd htd hks hkd' hf hmsg hty0 (by rw [mask52]; decide)
      bdg (set_mrs_fault_tmoSCN_E hE hP0 s a σ hX ht hd hks hkd hf hsce hsc0 hscC hky hmax htu)
  | some rp =>
    obtain ⟨x1, hk1, hbw⟩ := hBw.bw d hd
    rw [hkd] at hk1; cases hk1
    have hrwv : rw.bv = rp := hrwp hbw rp hrb
    have hrw0' : rw ≠ 0#u64 := fun e' => by have := hrw0.1 e'; rw [hrb] at this; cases this
    have hmr : BufMap B rw rp := hBC d hd xd true rp hkd hrb rw hrwv
    have hu' : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rp k) (tmoSt σ sc y n) := by
      intro k hk
      obtain ⟨sz, hz⟩ := buf_frame_of_ok hOK hkd hrb k hk
      refine ⟨sz, ?_⟩
      have hne : bufAddr rp k &&& ~~~(Fl4Spec.mask (Fl4Spec.pageBitsForSize sz)) ≠ sc.bv := by
        intro e'; rw [e', hky] at hz; cases hz
      simp [updK, hne, hz]
    exact do_fault_transfer_full hE hP s a σ hR ht hd htd hks hkd' hf hmsg (by simp) hty0
      (by rw [mask52]; decide) hmr hu' bdg
      (set_mrs_fault_tmoSC_E hE hP0 s a σ hX ht hd hks hkd hf hsce hsc0 hscC hky hmax htu hrw0' hmr)

end

section SpecT
open Fl4Spec

/-- **The spec's `do_ipc_transfer` of a timeout fault from a thread with an
SC**: the SC's consumed time cleared (`tmoSt`), the receiver's TCB changed in
its user context (two message registers: no receive-buffer word). -/
theorem doIpcTransfer_tmo_eq {σ : State Unit} {snd rcv : ObjRef} {xs xr : Tcb}
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) {bb : Word}
    (hf : xs.tcbFault = some (.timeout bb)) {sc : U64} (hscx : xs.tcbSchedContext = some sc.bv)
    {y : SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hmax : maxTicksToUs = core.num.U64.MAX.bv) (ep : Option ObjRef) (badge : Word) (grant : Bool) :
    ∃ x', doIpcTransfer (Z := Unit) snd ep badge grant rcv σ =
      ({((), updK (Ipc.tmoSt σ sc y n) rcv (.tcb x'))}, False) ∧ x' = { xr with tcbArch := x'.tcbArch } := by
  have hrsc : rcv ≠ sc.bv := fun e => by rw [e, hky] at hkr; cases hkr
  have hkrm : (Ipc.tmoSt σ sc y n).kheap rcv = some (.tcb xr) := by simp [updK, hrsc, hkr]
  have hmsg := makeFaultMsg_timeoutSC hks hscx (schedContextUpdateConsumed_eq hky hmax) bb
  have hspec : doIpcTransfer (Z := Unit) snd ep badge grant rcv σ =
      doFaultTransfer (Z := Unit) badge snd rcv (Endp.ipcBufOf true xr) σ := by
    unfold doIpcTransfer
    rw [nd_bind_one (Endp.lookupIpcBuffer_eq hkr true), nd_bind_one (threadGet_eq _ hks), hf]
  have hal : ∀ p, Endp.ipcBufOf true xr = some p → ∀ q ∈ Endp.mrPairs [bb, consumedUs y.scConsumed],
      (Endp.bufAddr p q.1).toNat % 8 = 0 ∧ inUserFrame (Endp.bufAddr p q.1) (Ipc.tmoSt σ sc y n) := by
    intro p _ q hq
    simp [Endp.mrPairs] at hq
  rw [hspec, doFaultTransfer_j hks hkrm hf hmsg _ hal badge]
  have key : ∀ o : KernelObject, updK (jMrSt (Ipc.tmoSt σ sc y n) rcv xr (Endp.ipcBufOf true xr)
      [bb, consumedUs y.scConsumed]) rcv o = updK (Ipc.tmoSt σ sc y n) rcv o := by
    intro o
    cases Endp.ipcBufOf true xr with
    | none => simp only [jMrSt, Endp.mrStateN, updK, Function.update_idem]
    | some p =>
      simp only [jMrSt, Endp.mrState]
      rw [updK_setUm_updK]
      rfl
  exact ⟨_, by rw [key], rfl⟩

end SpecT

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 16000000 in
/-- **The transfer step of `send_ipc` to a waiting receiver for a sender
with a timeout fault and an SC** (module docstring; XTopJointFaultRecv's
`xferFaultStepJ` for the timeout fault): on `IRel` by `do_ipc_transfer_tmoE`
(the base of the frame the state after the SC step, where `IRel` holds by
`sc_step_lift`), the spec's outcome `doIpcTransfer_tmo_eq`; FL4's footprint
the SC word, then the receiver's registers (`do_ipc_transfer_tmo_rg`); P1's
hole by `XS.consumed` and `xfer_all`. -/
theorem xferTmoStepJ {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64}
    {B : Set (U64 × Fl4Spec.Word)} {c : U64} (hP0 : Ipc.IPlaced N T E R B)
    (hHE : EpHyps st T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))))
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s σ)
    (hOK : Endp.IpcBufCapOK σ) (hBC : Endp.BufCover T B σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) {bb : Fl4Spec.Word}
    (hf : xs.tcbFault = some (.timeout bb)) {sc : U64} (hscx : xs.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (ep badge : U64) (grant : Bool)
    {T1 Cs1 Ω Sg Rp Scs Nt Ac1 X : Set U64} {H1 : P1.Heap} {Zb : U64 → Nat} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} (hT1 : P1.TcbPlaced T1) (hr1 : rcv ∈ T1)
    (h : P1.SchedQueuesInvX st T1 Cs1 Ω H1 X s Q Rq) (hB : P1.BoundInv st T1 Ac1 s)
    (hX : P1.XInv st T1 Cs1 Ω Sg Rp Scs Nt Zb s) (hS : P1.SCsOK st T1 Ω Sg Scs Zb Ac1 s) (hSg : P1.SgOK st Ω Sg s)
    (hsc1 : sc ∈ Scs) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => ∃ x' : Fl4Spec.Tcb,
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        ({((), Notif.updK (Ipc.tmoSt σ sc y n) rcv.bv (.tcb x'))}, False) ∧ x' = { xr with tcbArch := x'.tcbArch } ∧
      EpStateRel T E R B (L.mem s') (Notif.updK (Ipc.tmoSt σ sc y n) rcv.bv (.tcb x')) ∧
      SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s'
        (Notif.updK (Ipc.tmoSt σ sc y n) rcv.bv (.tcb x')) ∧
      Agree (L.mem (tmoS st s sc)) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      P1.WritesIn st s s' (fun b => (b = scW sc 8#u64 ∧ ∃ c ∈ Scs, P1.InSC c (Zb c) b) ∨ XferRegW T1 ∅ b) ∧
      L.actionW s' = L.actionW s ∧
      P1.SchedQueuesInvX st T1 Cs1 Ω H1 X s' Q Rq ∧ P1.BoundInv st T1 Ac1 s' ∧ P1.XInv st T1 Cs1 Ω Sg Rp Scs Nt Zb s' ∧
      P1.SCsOK st T1 Ω Sg Scs Zb Ac1 s' ∧ P1.SgOK st Ω Sg s' ∧
      (∀ y ∈ T1, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ⦄ := by
  have hP := hP0.e
  have hXr : IRel st th cr N T C E R B c s σ := IpcRel.ofSRN hR hSR
  have hSs := hXr.2.2.1
  obtain ⟨Q0, R0, hc, hsp⟩ := hSs.lists
  obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb snd hs
  rw [hks] at hk0; cases hk0
  have hsc0 : L.mem s (scA snd) ≠ 0#u64 := (Notif.optRef_some (hscw.symm.trans hscx)).1
  have hsce : L.mem s (scA snd) = sc := P1.eq_of_bv (Notif.optRef_some (hscw.symm.trans hscx)).2
  have hscC : sc ∈ C := by rw [← hsce]; exact hsp.scMem snd hs hsc0
  rw [hsce] at hsc0
  obtain ⟨y', n', hky', hy⟩ := hsp.scs sc hscC
  rw [hky] at hky'; cases hky'
  have hal8 : P1.Aligned (scW sc 8#u64) := (hy.hdr (K := 8#u64) (by simp) (by simp)).1
  have hscw8 : ScW st C c s σ (scW sc 8#u64) := Or.inl (sw_hdr hSs hscC (K := 8#u64) (by simp) (by simp) (by decide))
  have hupd := schedContextUpdateConsumed_eq hky hmax
  have hI0 : IRel st th cr N T C E R B c (tmoS st s sc) (Ipc.tmoSt σ sc y n) := by
    obtain ⟨hS1, -, -⟩ := hSs.set_sc_consumed hscC hky 0#u64
    have hW : P1.WritesIn st s (tmoS st s sc) (fun b => ScW st C c s σ b ∨ SFootI st T c s b) :=
      (P1.writesIn_wr hal8).mono fun b hb => Or.inl (hb ▸ hscw8)
    exact sc_step_lift hP0 hXr hW (nks_schedContextUpdateConsumed sc.bv σ (_, _) (by rw [hupd]; rfl)) hS1
  have hxs := hR.at_tcb hs hks
  have hty : L.mem s (tFaultA snd) = 5#u64 := by
    have hfr := hxs.faultR
    unfold FaultRel at hfr; rw [hf] at hfr; exact hfr.1
  have hU : schedcontext.update_consumed st arI s a sc ⦃ r => r.2 = tmoS st s sc ⦄ :=
    WP.spec_mono (update_consumed_irel hP0 s a σ hXr hscC hky hmax htu) fun r hr' => hr'.1
  have hrsc : rcv.bv ≠ sc.bv := kheap_ne hkr hky (fun _ h1 h2 => by subst h1; cases h2)
  have hkr0 : (Ipc.tmoSt σ sc y n).kheap rcv.bv = some (.tcb xr) := by simp [updK, hrsc, hkr]
  obtain ⟨x', hspec, hx'⟩ := doIpcTransfer_tmo_eq hks hkr hf hscx hky hmax (some ep.bv) badge.bv grant
    (rcv := rcv.bv)
  -- P1 across the SC word
  have hXS : P1.XS st T1 Cs1 Ω H1 Sg Rp Scs Nt Zb ∅ Ac1 X Q Rq s s :=
    ⟨⟨h, hB, hX, hS, hSg, fun b hb => absurd hb (Set.notMem_empty b)⟩, P1.XferFr.refl s, P1.WritesIn.refl s _⟩
  have hXS1 := P1.XS.consumed (v := 0#u64) hXS hsc1
  rw [← scW8_eq] at hXS1
  obtain ⟨⟨h1, hB1, hX1, hS1, hSg1, hU1⟩, fr1, -⟩ := hXS1
  refine WP.spec_mono (WP.spec_and (do_ipc_transfer_tmoE (ar := arI) hHE hP0 hmax s a σ htu hXr hOK hBC hs hr hne hks hkr
    hf hscx hky ep badge grant) (do_ipc_transfer_tmo_rg (arI := arI) hT1 hr1 s a ep badge grant hty hsce hsc0 hU)) ?_
  rintro s' ⟨⟨σ', h1', h2', h3', h4', h5', x'', h6', h7'⟩, w⟩
  have eσ : σ' = Notif.updK (Ipc.tmoSt σ sc y n) rcv.bv (.tcb x') :=
    congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (h1'.symm.trans hspec)))
  subst eσ
  obtain ⟨h2, hB2, hX2, hS2, hSg2, ea2, -, -, -, f2, -⟩ :=
    P1.xfer_all h1 hB1 hX1 hS1 hSg1 hU1 (w.mono fun b hb => P1.XferRegW.foot hb)
  have hN := ntfn_lift_rcv hP0.toC hI0.1.toN h2' hr h4' h5' hkr0 h6' h7'
  have hin : P1.InSC sc (Zb sc) (scW sc 8#u64) := by
    obtain ⟨hPs, hz⟩ := hX.1.sc sc hsc1
    obtain ⟨h8, h128, -⟩ := P1.sc_lo hPs hz
    have hv := P1.sc_word_val hPs hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    rw [scW8_eq]
    exact ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  refine ⟨x', hspec, hx', h2', ⟨h3', hN⟩, h4', ((P1.writesIn_wr hal8).trans w).mono fun b hb =>
      hb.imp_left fun e => ⟨e, sc, hsc1, e ▸ hin⟩, ea2.trans fr1.1, h2, hB2, hX2, hS2, hSg2,
    fun y0 hy0 K k1 k2 k3 => (f2 y0 hy0 K k1 k2 k3).trans (fr1.2.2.2.2.1 y0 hy0 K k1 k2 k3)⟩

end

/-! ## The base `J` state: the thread's timeout fault and its SC's consumed time -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

variable (st) in
/-- The FL4 state after `set_fault` of a timeout fault with badge `b`
(XTopJointSendBlockG's `set_fault_timeout_eq`). -/
abbrev fltS (s : S) (t b : U64) : S :=
  L.wr (L.wr (L.wr (L.wr s (tFaultA t) fl4_abi.consts.fault.Timeout) (tFw0A t) b) (tFw1A t) 0#u64) (tFw2A t) 0#u64

/-- A fault word written keeps P1's `BlkOK` (QueueRecv's `faultW_step`
without the `CanBlock` it carries). -/
theorem blk_faultW {T Cs Ω : Set U64} {H : P1.Heap} {Sg Rp Scs Nt : Set U64} {Zb : U64 → Nat} {Ac : Set U64}
    {s : S} {t K v : U64} (h : P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Zb Ac s) (ht : t ∈ T)
    (hK : 3376 ≤ K.val) (hK' : K.val < 3432) (hK8 : K.val % 8 = 0) :
    P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Zb Ac (L.wr s (core.num.U64.wrapping_add t K) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  obtain ⟨b1, b2⟩ := P1.bx_field (K := K) (v := v) h0 hB hX hSg.sub ht (by omega) hK8 (by omega) (by omega)
  exact ⟨⟨Q, R, P1.inv_wr_field h0 ht (by omega) hK8 (by omega)⟩, b1, b2,
    P1.SCsOK.field h0 hS hX ht (by omega) hK8 (by omega),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩

/-- A footprint rebased onto a state that differs from the start inside it. -/
theorem writesIn_rebase {s0 s1 s2 : S} {A A0 : U64 → Prop} (h : P1.WritesIn st s0 s2 A) (h0 : P1.WritesIn st s0 s1 A0)
    (hsub : ∀ b, A0 b → A b) : P1.WritesIn st s1 s2 A :=
  ⟨h.1.trans h0.1.symm, h.2.1.trans h0.2.1.symm, fun b hb hn =>
    (h.2.2 b hb hn).trans (h0.2.2 b hb (fun h' => hn (hsub b h'))).symm⟩

end

section SpecR
open Fl4Spec

/-- **The shadow of a state**: the thread `t`'s TCB and the SC `sc` set to
the base's (`xT`, `yS`). -/
def rhoT (σ : State Unit) (t sc : ObjRef) (xT : Tcb) (yS : SchedContext) (n : Nat) : State Unit :=
  updK (updK σ t (.tcb xT)) sc (.schedContext yS n)

variable {t sc : ObjRef} {xT : Tcb} {yS : SchedContext} {n : Nat}

theorem rhoT_eq (σ : State Unit) : rhoT σ t sc xT yS n =
    { σ with kheap := Function.update (Function.update σ.kheap t (some (.tcb xT))) sc (some (.schedContext yS n)) } :=
  rfl

theorem rhoT_updK {σ : State Unit} {p : ObjRef} (o : KernelObject) (hpt : p ≠ t) (hps : p ≠ sc) :
    rhoT (updK σ p o) t sc xT yS n = updK (rhoT σ t sc xT yS n) p o := by
  rw [rhoT_eq, rhoT_eq]
  show ({ σ with kheap := Function.update (Function.update (Function.update σ.kheap p (some o)) t (some (.tcb xT))) sc (some (.schedContext yS n)) } : State Unit) = { σ with kheap := Function.update (Function.update (Function.update σ.kheap t (some (.tcb xT))) sc (some (.schedContext yS n))) p (some o) }
  rw [Function.update_comm hpt, Function.update_comm hps]

theorem rhoT_updKt {σ : State Unit} (o : KernelObject) : rhoT (updK σ t o) t sc xT yS n = rhoT σ t sc xT yS n := by
  rw [rhoT_eq, rhoT_eq]
  show ({ σ with kheap := Function.update (Function.update (Function.update σ.kheap t (some o)) t (some (.tcb xT))) sc (some (.schedContext yS n)) } : State Unit) = _
  rw [Function.update_idem]

theorem rhoT_updKsc {σ : State Unit} (o : KernelObject) (hts : t ≠ sc) :
    rhoT (updK σ sc o) t sc xT yS n = rhoT σ t sc xT yS n := by
  rw [rhoT_eq, rhoT_eq]
  show ({ σ with kheap := Function.update (Function.update (Function.update σ.kheap sc (some o)) t (some (.tcb xT))) sc (some (.schedContext yS n)) } : State Unit) = _
  rw [Function.update_comm (Ne.symm hts), Function.update_idem]

theorem rhoT_kh {σ : State Unit} {q : ObjRef} (hqt : q ≠ t) (hqs : q ≠ sc) :
    (rhoT σ t sc xT yS n).kheap q = σ.kheap q := by
  unfold rhoT; simp [updK, hqt, hqs]

theorem rhoT_kt {σ : State Unit} (hts : t ≠ sc) : (rhoT σ t sc xT yS n).kheap t = some (.tcb xT) := by
  unfold rhoT; simp [updK, hts]

theorem rhoT_ksc {σ : State Unit} : (rhoT σ t sc xT yS n).kheap sc = some (.schedContext yS n) := by
  unfold rhoT; simp [updK]

theorem rhoT_self {σ : State Unit} (h1 : σ.kheap t = some (.tcb xT)) (h2 : σ.kheap sc = some (.schedContext yS n)) :
    rhoT σ t sc xT yS n = σ := by
  rw [rhoT_eq]
  have e1 : Function.update σ.kheap t (some (.tcb xT)) = σ.kheap := by
    rw [← h1]; exact Function.update_eq_self _ _
  rw [e1]
  have e2 : Function.update σ.kheap sc (some (.schedContext yS n)) = σ.kheap := by
    rw [← h2]; exact Function.update_eq_self _ _
  rw [e2]

theorem rhoT_setUm {σ : State Unit} (um : Word → Word8) :
    rhoT (Endp.setUm σ um) t sc xT yS n = Endp.setUm (rhoT σ t sc xT yS n) um := rfl

end SpecR

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

theorem bufCover_updT {T : Set U64} {B : Set (U64 × Fl4Spec.Word)} {σ : Fl4Spec.State Unit} (h : Endp.BufCover T B σ)
    {t : Fl4Spec.ObjRef} {x y : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb x)) (hf : y.tcbIpcframe = x.tcbIpcframe)
    (hb : y.tcbIpcBuffer = x.tcbIpcBuffer) : Endp.BufCover T B (Notif.updK σ t (.tcb y)) := by
  intro u hu x' bb p hx' hp w hw
  by_cases e : u.bv = t
  · rw [e] at hx'
    simp only [Notif.updK, Function.update_self, Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hx'
    subst hx'
    have hp' : Endp.ipcBufOf bb x = some p := by unfold Endp.ipcBufOf at hp ⊢; rw [hf, hb] at hp; exact hp
    exact h u hu x bb p (by rw [e]; exact hk) hp' w hw
  · exact h u hu x' bb p (by simpa [Notif.updK, e] using hx') hp w hw

set_option maxHeartbeats 16000000 in
/-- **The base `J` state of the timeout-fault send** (module docstring):
from `JAtZ`, the thread `t` (not blocked on send) given the timeout fault
(`set_fault`'s four words, `JAtZ.fin_frameF` as XTopJointFaultRecv's
`JAtZ.setFaultCapJ`, P1 by `blk_faultW`) and its SC's consumed time cleared
(`JAtZ.updConsumedJ`, the state by `update_consumed_irel`). -/
theorem JAtZ.tmoBaseJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {t : U64} (ht : t ∈ Z.T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hns : ∀ e d, x.tcbState ≠ .blockedOnSend e d) (b : U64) {sc : U64} (hsc : sc ∈ Z.C)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n)) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (tmoS st (fltS st s t b) sc) a
      (Ipc.tmoSt (updK σ t.bv (.tcb { x with tcbFault := some (.timeout b.bv) })) sc y n) := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hta := hP0.e.tcb t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP0.e.tcb
  obtain ⟨s1, -, ⟨⟨-, hI1⟩, hs1⟩, hfoot1⟩ := spec_exists (WP.spec_and (WP.spec_and
    (set_fault_timeout_top hP0 hI ht hk b) (set_fault_timeout_eq s t b))
    (P1.faults.set_fault.kw (Cs := Cs) (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
      (Es := ∅) s t (error.Fault.Timeout b) hTH htH))
  subst hs1
  have hblk1 := blk_faultW (v := 0#u64) (K := 3400#u64) (blk_faultW (v := 0#u64) (K := 3392#u64)
    (blk_faultW (v := b) (K := 3384#u64) (blk_faultW (v := fl4_abi.consts.fault.Timeout) (K := 3376#u64) J.blk htH
      (by simp) (by simp) (by simp)) htH (by simp) (by simp) (by simp)) htH (by simp) (by simp) (by simp))
    htH (by simp) (by simp) (by simp)
  have hwF : P1.WritesIn st s (fltS st s t b) (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := by
    have w := (((writesIn_wr (st := st) (s := s) (v := fl4_abi.consts.fault.Timeout) (a_fault hta).1).trans
      (writesIn_wr (v := b) (a_fw0 hta).1)).trans (writesIn_wr (v := 0#u64) (a_fw1 hta).1)).trans
      (writesIn_wr (v := 0#u64) (a_fw2 hta).1)
    refine w.mono fun w0 hw0 => ?_
    have k : ∃ K : Nat, 256 ≤ K ∧ K < 4096 ∧ K ≠ 3440 ∧ K ≠ 3472 ∧ (K ≠ 3512 ∧ K ≠ 3664) ∧ w0.val = t.val + K := by
      rcases hw0 with ((h | h) | h) | h <;> subst h
      · exact ⟨3376, by omega, by omega, by omega, by omega, by omega, val_fault hta⟩
      · exact ⟨3384, by omega, by omega, by omega, by omega, by omega, val_fw0 hta⟩
      · exact ⟨3392, by omega, by omega, by omega, by omega, by omega, val_fw1 hta⟩
      · exact ⟨3400, by omega, by omega, by omega, by omega, by omega, val_fw2 hta⟩
    obtain ⟨K, k1, k2, k3, k4, k5, k6⟩ := k
    exact Or.inr ⟨t, ht, K, k1, k2, k3, k4, k5, k6⟩
  set y1 : Fl4Spec.Tcb := { x with tcbFault := some (.timeout b.bv) } with hy1
  have hA : QKY σ (updK σ t.bv (.tcb y1)) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun p => ?_⟩
    by_cases hp : p = t.bv
    · subst hp; exact Or.inr (Or.inl ⟨x, y1, hk, by simp [updK], rfl⟩)
    · exact Or.inl (by simp [updK, hp])
  obtain ⟨V1, J1⟩ := J.fin_frameF hI1 hwF hA (YK.YKS.updTcb (y := y1) hk rfl).ykeep
    (J.inv.updSame (y := y1) hk rfl rfl (Or.inr hns)) hblk1 hfoot1
  have hst : sc.bv ≠ t.bv := fun e => by rw [e, hk] at hky; cases hky
  have hky1 : (updK σ t.bv (.tcb y1)).kheap sc.bv = some (.schedContext y n) := by simp [updK, hst, hky]
  have hI1' := J1.xtop.irelK J1.ks J1.buf
  obtain ⟨r, -, ⟨σ2, c2, he2, V2, J2⟩, hs2, -, he2', -⟩ := spec_exists (WP.spec_and
    (J1.updConsumedJ hAT hmax htu hsc ht) (update_consumed_irel (ar := arI) J1.ip _ a _ hI1' hsc hky1 hmax htu))
  have eσ : σ2 = Ipc.tmoSt (updK σ t.bv (.tcb y1)) sc y n := by
    have e := (Prod.mk.inj (he2.symm.trans he2')).1
    exact congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e)
  rw [eσ, hs2] at J2
  exact ⟨V2, J2⟩

end

/-! ## The timeout-fault send to a waiting receiver -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- An SC's `CONSUMED` word is one of its words (P1's `InSC`). -/
theorem scW8_inSC {T Cs1 Ω : Set U64} {H1 : P1.Heap} {Sg Rp Scs Nt : Set U64} {Zb : U64 → Nat} {Ac1 : Set U64}
    {s1 : S} (h : P1.BlkOK st T Cs1 Ω H1 Sg Rp Scs Nt Zb Ac1 s1) {sc : U64} (hsc : sc ∈ Scs) :
    P1.InSC sc (Zb sc) (scW sc 8#u64) := by
  obtain ⟨-, -, hX, -, -⟩ := h
  obtain ⟨hPs, hz⟩ := hX.1.sc sc hsc
  obtain ⟨h8, h128, -⟩ := P1.sc_lo hPs hz
  have hv := P1.sc_word_val hPs hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  rw [scW8_eq]
  exact ⟨by rw [hv]; omega, by rw [hv]; omega⟩

set_option maxHeartbeats 64000000 in
/-- **The timeout-fault `send_ipc` of a thread other than the current one to
a waiting receiver, the sender left `Inactive`** (module docstring): at the
send (`s7`, `σf`: `t` made `Running`/`Restart` and given the timeout fault,
from the `J` state `s`, `σ` where it is `Inactive`), FL4's dequeue, transfer
(`xferTmoStepJ`), reply unlink, `t` `Inactive` and the receiver `Running` on
`IRel` as XTopJointFaultRecv's `JAtZ.sendFaultIJ` (P1's queue bits of `t`
from its `CanBlock` at the send); `JAtZ` by `JAtZ.wake_postD` from the base
`JAtZ.tmoBaseJ` (`t` `Inactive` with the fault, its SC's consumed time
cleared), whose frame to the end is the receiver's wake (`CFr`, read on the
shadows `rhoT` of the states between: `t` and its SC as at the base). -/
theorem JAtZ.sendTmoRecvIJ (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hcr : ∃ xc, σ.kheap σ.curThread = some (.tcb xc) ∧ Fl4Spec.runnable xc.tcbState = true)
    {t : U64} (ht : t ∈ Z.T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (htc : t.bv ≠ σ.curThread) {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (b : U64) {ts : Fl4Spec.ThreadState} (hrun : Fl4Spec.runnable ts = true) {s7 : S}
    (hI7 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s7
      (updK σ t.bv (.tcb { x with tcbState := ts, tcbFault := some (.timeout b.bv) })))
    (hblk7 : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s7)
    (hW7 : P1.WritesIn st s s7 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hfoot7 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s7)
    (hcb7 : P1.CanBlock st (P1.Heap.tcbs H) Ac s7 t)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hke : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (badge : U64) (g gr : Bool)
    (hno : (g = false ∧ gr = false) ∨
      ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none) :
    endpoint.send_ipc st arI s7 a true false badge g gr false t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) true false badge.bv g gr false t.bv e.bv
        (updK σ t.bv (.tcb { x with tcbState := ts, tcbFault := some (.timeout b.bv) }))).1,
        JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  set xt : Fl4Spec.Tcb := { x with tcbState := ts, tcbFault := some (.timeout b.bv) } with hxt
  set σf := updK σ t.bv (.tcb xt) with hσf
  set xT : Fl4Spec.Tcb := { x with tcbFault := some (.timeout b.bv) } with hxT
  set yS : Fl4Spec.SchedContext := { y with scConsumed := (0#u64 : U64).bv } with hyS
  have hns : ∀ e d, x.tcbState ≠ .blockedOnSend e d := by rw [hrs]; intro _ _ h; cases h
  have hst : t.bv ≠ sc.bv := fun e0 => by rw [e0, hky] at hk; cases hk
  -- the base `J` state
  obtain ⟨V0, J0⟩ := J.tmoBaseJ hAT hmax htu ht hk hns b hsc hky
  set s0 := tmoS st (fltS st s t b) sc with hs0
  set σ0 := Ipc.tmoSt (updK σ t.bv (.tcb xT)) sc y n with hσ0
  have hσ0r : σ0 = rhoT σ t.bv sc.bv xT yS n := rfl
  have hfr : rhoT σf t.bv sc.bv xT yS n = σ0 := by rw [hσf, rhoT_updKt, hσ0r]
  have hk0 : ∀ q, q ≠ t.bv → q ≠ sc.bv → σ0.kheap q = σ.kheap q := fun q h1 h2 => by
    rw [hσ0r]; exact rhoT_kh h1 h2
  have hkf : ∀ q, q ≠ t.bv → σf.kheap q = σ.kheap q := fun q h1 => by simp [hσf, updK, h1]
  have hP0 := J.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hI := hI7
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hRe : Z.R = P1.Heap.replies H := J.tcbs_eq.2
  have hte0 : t.bv ≠ e.bv := kheap_ne hk hke (fun _ h1 h2 => by subst h1; cases h2)
  have hse0 : sc.bv ≠ e.bv := kheap_ne hky hke (fun _ h1 h2 => by subst h1; cases h2)
  have hkx := hk
  have hk : σf.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))) := by rw [hkf _ (Ne.symm hte0)]; exact hke
  have hkt : σf.kheap t.bv = some (.tcb xt) := by simp [hσf, updK]
  have hrn : Fl4Spec.runnable xt.tcbState = true := hrun
  have hft : xt.tcbFault = some (.timeout b.bv) := rfl
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ Z.T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  obtain ⟨xd, hkd, -⟩ := hI.1.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s7 (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s7 (tBlockA d') = e := (hB d' (by simp)).2
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by have := runnable_code hrn; omega
  have htd : t ≠ d' := by intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := hte0
  have htd' : t.bv ≠ d'.bv := bv_ne htd
  have hdsc : d'.bv ≠ sc.bv := fun e0 => by
    have h1 : σf.kheap sc.bv = some (.schedContext y n) := by rw [hkf _ (Ne.symm hst)]; exact hky
    rw [e0, h1] at hkd; cases hkd
  have hkdσ : σ.kheap d'.bv = some (.tcb xd) := by rw [← hkf _ (Ne.symm htd')]; exact hkd
  have hkd0 : σ0.kheap d'.bv = some (.tcb xd) := by rw [hk0 _ (Ne.symm htd') hdsc]; exact hkdσ
  have hke0 : σ0.kheap e.bv = some (.endpoint (.recvEP (d'.bv :: q))) := by
    rw [hk0 _ (Ne.symm hte0) (Ne.symm hse0)]; exact hke
  have hdc : d'.bv ≠ σf.curThread := by
    intro h
    obtain ⟨xc, hkc, hrc⟩ := hcr
    have h' : d'.bv = σ.curThread := h
    rw [← h', hkdσ] at hkc; cases hkc; rw [hstd] at hrc; cases hrc
  -- P1's facts at the send
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := hblk7
  have hdH : d' ∈ P1.Heap.tcbs H := J.zH.1 d' hdT
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hdta := hTP d' hdH
  have hsub := hSg0.sub
  have hds : L.mem s7 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := by
    rw [stA_tStA, tsVals.2.2.1]; exact UScalar.eq_of_val_eq hd3
  have hbe : L.mem s7 (P1.blockA d') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hdb
  have hdq := P1.endpoint.ep_dequeue.inv s7 d' Q0 R0 h0 hdH (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : d' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 d' hdH (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s7 e d' (EQ0 e) hTP hE0 hq0' hdm
  -- FL4: the endpoint's state and queue
  unfold endpoint.send_ipc
  refine WP.spec_bind (Fl4Proofs.P1.obj.Ep.state.spec s7 e) ?_
  rintro _ rfl
  rw [epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s7 e) ?_
  rintro _ rfl
  have hhead : (L.epQ s7 e).head = d' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s7 σf hR hS0 he hk (d := d')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s7 he d' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  set σ1 := Notif.updK σf e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1
  have hW1a : P1.WritesIn st s7 s1 (fun b => EW e b ∨ ∃ w ∈ (d' :: xs'), TL w b) :=
    ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩⟩
  have hW1 : P1.WritesIn st s7 s1 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) := hW1a.mono fun b hb => by
    rcases hb with h | ⟨w, hw, h | h⟩
    · exact Or.inr (Or.inl ⟨e, he, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
  have F1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s7 s1 :=
    P1.Foot.of w1 fun b hb => hb.kw hq0'.mem (Or.inl hHe)
  obtain ⟨hB1, hX1, hS1', hSg1, ea1, -, -⟩ := P1.frame_bx h0 hB0 hX0 hSc0 hSg0 f1 o1 n1 k1
    (P1.TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg0.sub _ (hX0.1.ntB n' hn').2)⟩)
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hky1 : σ1.kheap sc.bv = some (.schedContext y n) := by
    simp [σ1, hse0, hσf, updK, Ne.symm hst, hky]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  -- the shadow frame from the base
  have eρ1 : rhoT σ1 t.bv sc.bv xT yS n = updK σ0 e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    rw [hσ1, rhoT_updK _ (Ne.symm hte) (Ne.symm hse0), hfr]
  have Fr1 : CFr e.bv d'.bv σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    exact CFr.upd hke0 (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
      by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
      by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1 : IK d'.bv σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    exact IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hke0 (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : SKeep σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    exact SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h)
      (fun _ _ h => by cases h)
  have hOKσ := (J.xferH).1
  have hBCσ := (J.xferH).2.1
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (ipcBufCapOK_updT (y := xt) hOKσ hkx rfl rfl) (EpStep.ep hk)
  have hBC1 : Endp.BufCover Z.T Z.B σ1 := bufCover_epStep (bufCover_updT (y := xt) hBCσ hkx rfl rfl) (EpStep.ep hk)
  have hsc1 : sc ∈ P1.Heap.scs H := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨_, (hJ.sc sc y n (J.c0 sc hsc) hky).2⟩
  -- the transfer
  refine WP.spec_bind (xferTmoStepJ hP0 (hH.epHyps hP0) hmax s1 a σ1 htu hR1 hS1 hOK1 hBC1 ht hdT htd hkt1 hkd1 hft
    hxsc hky1 e badge g hTP hdH h1 hB1 hX1 hS1' hSg1 hsc1) ?_
  rintro s2 ⟨x2, e2, hx2, hR2, hS2, hA2, w2, ea2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Ipc.tmoSt σ1 sc y n) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by
    rw [hσ2]
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne htd', Function.update_of_ne hst]
    exact hkt1
  have hksc2 : σ2.kheap sc.bv = some (.schedContext yS n) := by
    rw [hσ2, updK_kheap, Function.update_of_ne (Ne.symm hdsc)]
    show Function.update σ1.kheap sc.bv _ sc.bv = _
    rw [Function.update_self]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc2 : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    rw [hσ2]
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne (Ne.symm hde), Function.update_of_ne (Ne.symm hse0)]
    exact hk1e
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    have hns' : sc.bv ≠ e''.bv := by intro h; rw [← h, hksc2] at hz; cases hz
    rw [hσ2] at hz
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne (Ne.symm hne),
      Function.update_of_ne (Ne.symm hns')] at hz
    exact hq1 e'' he'' z hz
  have hrw : L.mem s2 (tReplyA d') = L.mem s7 (tReplyA d') := by
    rw [show tReplyA d' = core.num.U64.wrapping_add d' 3360#u64 from rfl, f2 d' hdH _ (by simp) (by simp) (by simp),
      ← show tReplyA d' = core.num.U64.wrapping_add d' 3360#u64 from rfl,
      hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
  have hscw8 : SW Z.C σf (scW sc 8#u64) := sw_hdr hI.2.2.1 hsc (K := 8#u64) (by simp) (by simp) (by decide)
  have hW2 : P1.WritesIn st s7 s2 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW1.trans1 (w2.mono fun b hb => by
    rcases hb with ⟨eb, -⟩ | (⟨y0, hy, K, h1', h2', -, eb⟩ | hb)
    · subst eb; exact Or.inl (Or.inl (Or.inr (Or.inr hscw8)))
    · have hyT : y0 ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inr ⟨y0, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩)
      rw [eb]; exact tfield_val (hP.tcb y0 hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _))
  have F2 : P1.WritesIn st s1 s2 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1) :=
    w2.mono fun b hb => by
      rcases hb with ⟨-, c0, hc0, hin⟩ | (⟨y0, hy, K, h1', h2', h3', eb⟩ | hb)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c0, hc0, hin⟩)))
      · exact Or.inl ⟨y0, hy, K, by omega, by omega, by omega, by omega, eb⟩
      · exact absurd hb (Set.notMem_empty _)
  have eρ2 : rhoT σ2 t.bv sc.bv xT yS n = updK (rhoT σ1 t.bv sc.bv xT yS n) d'.bv (.tcb x2) := by
    rw [hσ2, rhoT_updK _ (Ne.symm htd') hdsc, rhoT_updKsc _ hst]
  have hkd1ρ : (rhoT σ1 t.bv sc.bv xT yS n).kheap d'.bv = some (.tcb xd) := by
    rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd1
  have Fr2 : CFr e.bv d'.bv σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]
    exact Fr1.trans (CFr.upd hkd1ρ (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl,
      by rw [hx2], Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]; exact IK1.trans (IK.updSelf hkd1ρ hxsc2)
  have SK2 : SKeep σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]
    exact SK1.trans (SKeep.updK (p := d'.bv) (o := .tcb x2) (fun y h => ⟨xd, hkd1ρ, by cases h; exact hxsc2.symm⟩)
      (fun _ _ h => by cases h))
  have hks2 : L.ksb s2 = L.ksb s7 := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s7 (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true]
  refine WP.spec_bind (Pₘ := fun s3 => ∃ σ3 x3 X3,
      Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) rep σ2 = ({((), σ3)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem s3) σ3 ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s3 σ3 ∧
      σ3.kheap t.bv = some (.tcb xt) ∧ σ3.kheap d'.bv = some (.tcb x3) ∧ RbIn x3.tcbState ∧
      tsCode x3.tcbState ≠ 6 ∧ x3.tcbSchedContext = xd.tcbSchedContext ∧
      σ3.kheap sc.bv = some (.schedContext yS n) ∧
      (∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue) ∧
      P1.WritesIn st s7 s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) ∧
      P1.WritesIn st s7 s3 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
        (P1.Heap.scBits H) (P1.EH H) s7 b ∨ False) ∧
      CFr e.bv d'.bv σ0 (rhoT σ3 t.bv sc.bv xT yS n) ∧ IK d'.bv σ0 (rhoT σ3 t.bv sc.bv xT yS n) ∧
      SKeep σ0 (rhoT σ3 t.bv sc.bv xT yS n) ∧ σ3.curThread = σ.curThread ∧
      σ3.schedulerAction = σ.schedulerAction ∧
      P1.SchedQueuesInvX st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H X3 s3 Q0 R0 ∧
      P1.BoundInv st (P1.Heap.tcbs H) Ac s3 ∧
      P1.XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) s3 ∧
      P1.SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s3 ∧
      P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 ∧ P1.ExcT X3 d' ∧
      (d' ∈ X3 ∨ ¬ P1.Blocked (L.mem s3 (P1.stA d'))) ∧
      (∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d')) ?_ ?_
  · cases hrp : rep with
    | none =>
      rw [hrp] at hrep
      have h00 := optRef_none hrep
      simp only [h00, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      have hrA : L.mem s2 (P1.replyA d') = 0#u64 := by
        show L.mem s2 (tReplyA d') = 0#u64; rw [hrw]; exact h00
      exact ⟨σ2, x2, _, rfl, hR2, hS2, hkt2, hkd2, Or.inl ⟨_, _, _, hst2'⟩,
        by rw [hst2']; simp [tsCode], hxsc2, hksc2, hq2, hW2, footW_trans (footW_of F1) (F2.mono fun b hb => Or.inl hb),
        Fr2, IK2, SK2, rfl, rfl, h2, hB2, hX2, hS2'',
        hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl), hX2.noref0 hdta hrA⟩
    | some r =>
      rw [hrp] at hrep hrepR hst2'
      obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
      have hwR := hrepR (by simp)
      have hne0 : (L.mem s7 (tReplyA d') != 0#u64) = true := by simp [hw0]
      simp only [hne0, ↓reduceIte]
      set w := L.mem s7 (tReplyA d') with hwdef
      subst hwr
      obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
      have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
      have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
      have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
      have hws : w.bv ≠ sc.bv := fun e0 => by
        have h1 : σf.kheap sc.bv = some (.schedContext y n) := by rw [hkf _ (Ne.symm hst)]; exact hky
        rw [e0, h1] at hkr; cases hkr
      have hkr2 : σ2.kheap w.bv = some (.reply xr) := by
        rw [hσ2]
        simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne hwd, Function.update_of_ne hws]
        simp [σ1, hwe, hkr]
      have hkrσ : σ.kheap w.bv = some (.reply xr) := by rw [← hkf _ hwt]; exact hkr
      have hb' : xr.replyTcb = some d'.bv := hback_of J.sv hkdσ e.bv w.bv dd xr (by rw [hstd, hrp]) hkrσ
      have hX2' := IpcRel.ofSRN hR2 hS2
      have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
      rw [hrA] at hiR hit
      refine WP.spec_mono (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2 hdT hkd2 hst2' hwR hkr2
          hb' hq2) (reply_unlink_cn hP0 hX2' hdT hwR hkr2))
        (WP.spec_and (P1.ipc.reply_unlink.inv s2 w d' Q0 R0 h2 hdH hX2.1 hsub hiR hit
            (by rw [hds2]; exact P1.blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
          (P1.ipc.reply_unlink.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
            (Es := P1.EH H) s2 w d' h2 hX2 hsub hiR hdH))) ?_
      rintro s3 ⟨⟨⟨e3, hR3, hS3⟩, hW3⟩, ⟨h3, e3', k3, z3⟩, fu3⟩
      have hclr : ∀ r ∈ P1.Heap.replies H, L.mem s2 (P1.rTcbA r) = d' → L.mem s3 (P1.rTcbA r) = 0#u64 := by
        intro r hr er
        obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
        rw [er, hrA] at b2; rw [← b2]; exact z3
      set x3 : Fl4Spec.Tcb := { x2 with tcbState := .inactive } with hx3
      have hkd3a : (Notif.updK σ2 w.bv (.reply { xr with replyTcb := none })).kheap d'.bv = some (.tcb (x2)) := by
        simp [Ne.symm hwd, hkd2]
      have hct3a : d'.bv ≠ (Notif.updK (Notif.updK σ2 w.bv (.reply { xr with replyTcb := none })) d'.bv
          (.tcb x3)).curThread := hdc
      have e3s : Notif.stsAct (Notif.updK (Notif.updK σ2 w.bv (.reply { xr with replyTcb := none })) d'.bv (.tcb x3))
          d'.bv = Notif.updK (Notif.updK σ2 w.bv (.reply { xr with replyTcb := none })) d'.bv (.tcb x3) :=
        stsAct_ne hct3a
      have hW3' : P1.WritesIn st s7 s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
        hW2.trans1 (hW3.mono fun b hb => cnW_back hks2 (SzKeepC.of (by
          intro p y0 m hp
          by_cases hps : p = sc.bv
          · subst hps; rw [hksc2] at hp; cases hp; exact ⟨y, by rw [hkf _ (Ne.symm hst)]; exact hky⟩
          · refine ⟨y0, ?_⟩
            rw [hσ2] at hp
            have hpd : p ≠ d'.bv := fun e0 => by rw [e0] at hp; simp at hp
            simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne hpd, Function.update_of_ne hps] at hp
            have hpe : p ≠ e.bv := fun e0 => by rw [e0] at hp; simp [σ1] at hp
            simpa [σ1, hpe] using hp)) hb)
      -- the shadows
      have hkr2ρ : (rhoT σ2 t.bv sc.bv xT yS n).kheap w.bv = some (.reply xr) := by
        rw [rhoT_kh hwt hws]; exact hkr2
      have hkd3aρ : (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv (.reply { xr with replyTcb := none })).kheap d'.bv =
          some (.tcb x2) := by
        simp only [updK_kheap, Function.update_of_ne (Ne.symm hwd)]
        rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd2
      have eρ3 : rhoT (Notif.stsAct (Notif.updK (Notif.updK σ2 w.bv (.reply { xr with replyTcb := none })) d'.bv
          (.tcb x3)) d'.bv) t.bv sc.bv xT yS n = Notif.stsAct (Notif.updK (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv
          (.reply { xr with replyTcb := none })) d'.bv (.tcb x3)) d'.bv := by
        rw [e3s, stsAct_ne (show d'.bv ≠ (Notif.updK (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv
          (.reply { xr with replyTcb := none })) d'.bv (.tcb x3)).curThread from hdc),
          rhoT_updK _ (Ne.symm htd') hdsc, rhoT_updK _ hwt hws]
      refine ⟨_, x3, _, e3, hR3, hS3, ?_, ?_, Or.inr rfl, by simp [x3, tsCode], by simp [x3, hxsc2], ?_, ?_, hW3',
        footW_trans (footW_trans (footW_of F1) (F2.mono fun b hb => Or.inl hb)) (footW_of fu3), ?_, ?_, ?_, ?_, ?_, h3,
        hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1),
        hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr, hS2''.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3']; exact P1.not_blocked_inactive),
        (hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr).noref hdta (by rw [e3']; exact P1.inactive_ne.1)
          (by rw [e3']; exact P1.inactive_ne.2)⟩
      · rw [stsAct_kheap]; simp [htd', hwt.symm, hkt2]
      · rw [stsAct_kheap]; simp
      · rw [stsAct_kheap]; simp [Ne.symm hdsc, hws.symm, hksc2]
      · intro e'' he'' z hz
        rw [stsAct_kheap] at hz
        have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
        have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [hwd] at hz
        exact hq2 e'' he'' z (by simpa [Ne.symm hne, Ne.symm hne'] using hz)
      · rw [eρ3]
        exact (Fr2.trans (CFr.upd hkr2ρ (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
          (CFr.stsIn hkd3aρ (Or.inl ⟨_, _, _, hst2'⟩))
      · rw [eρ3]
        have IK3a : IK d'.bv σ0 (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv (.reply { xr with replyTcb := none })) :=
          IK2.trans (IK.updOther (o' := .reply { xr with replyTcb := none }) hkr2ρ (fun o0 h => by
            rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
        exact (IK3a.trans (IK.updSelf (y := x3) hkd3aρ rfl)).trans (IK.sts _ _ _)
      · rw [eρ3]
        exact ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply { xr with replyTcb := none }) (fun y h => by cases h)
          (fun _ _ h => by cases h))).trans (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3aρ, by cases h; rfl⟩)
          (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
      · rw [e3s]; rfl
      · rw [e3s]; rfl
      · obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
  rintro s3 ⟨σ3, x3, X3, hU, hR3, hS3, hkt3, hkd3, hrb3, hns3, hsc3, hksc3, hq3, hW3, F3, Fr3, IK3, SK3, hct3, hact3,
    h3, hB3, hX3, hS3', hSg3, hXc3, hx3, hnr3⟩
  have hxt3 := hR3.at_tcb ht hkt3
  have hty3 : L.mem s3 (tFaultA t) = 5#u64 := by
    have hfr := hxt3.faultR
    unfold FaultRel at hfr; rw [hft] at hfr; exact hfr.1
  have hks3 : L.ksb s3 = L.ksb s7 := hW3.1
  -- the sender's `Inactive`
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = tsCode xt.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st]
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (w := L.mem s3 (P1.stA t)) (by rw [hw3]; exact runnable_code hrn)
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := (IpcRel.ofSRN hR3 hS3).2.2.1
  have hna3 : L.actionW s3 ≠ t := actionW_ne_of hSR3 ht (by
    rw [hact3]; intro e0
    obtain ⟨x', -, -, -, h1', -, h3', -⟩ := schedulable_inv (J.act.1 _ e0)
    rw [hkx] at h1'; cases h1'; rw [hrs] at h3'; cases h3')
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  have hstsT := WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s3 σ3 hR3 hS3 ht hkt3 hqt3
      (by have := runnable_code hrn; omega) .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl))
      (set_thread_state_sfoot hSR3 ht sched.TS_INACTIVE))
    (WP.spec_and (P1.sts_all s3 t _ Q0 R0 h3 hB3 hX3 hS3' hSg3 htH P1.not_blocked_inactive P1.inactive_ne
        (Or.inr hnbt3) (hX3.noref (hTP t htH) hnrp3 (fun e0 => hnbt3 (Or.inr (Or.inl e0))))
        ⟨fun c hc' p hp hm => absurd hm (h0.notQ htH hcb7.nq hc' hp), fun c hc' hm => absurd hm (h0.notR htH hcb7.nr hc'),
          fun e0 => absurd e0 hna3⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s3 t sched.TS_INACTIVE h3 htH))
  -- FL4: no reply pushed, the sender `Inactive`
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧ sched.set_thread_state st s3 t sched.TS_INACTIVE = ok r.1)
    ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 rfl
    rw [hty3, if_pos (by unfold fl4_abi.consts.fault.NullFault; decide)]
    by_cases hi : (L.mem s7 (tReplyA d') != 0#u64) = true
    · rw [if_pos hi]
      have hgg : g = false ∧ gr = false := by
        rcases hno with h | hn
        · exact h
        · exfalso
          have hr0 := hn xd hkdσ _ _ _ hstd
          rw [hr0] at hrep
          have h00 := optRef_none hrep
          rw [h00] at hi
          simp at hi
      obtain ⟨rfl, rfl⟩ := hgg
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_bind (spec_self hstsT) fun s4 h4 => (WP.spec_ok _).2 ⟨rfl, h4⟩
    · rw [if_neg hi]
      exact WP.spec_bind (spec_self hstsT) fun s4 h4 => (WP.spec_ok _).2 ⟨rfl, h4⟩
  rintro ⟨s4, a4⟩ ⟨ha4, hs4⟩
  simp only at ha4 hs4
  subst ha4
  try dsimp only
  have hpost := hstsT
  rw [hs4] at hpost
  obtain ⟨⟨⟨hR4, hS4⟩, hW4⟩, ⟨h4, hB4, hX4, hS4', hSg4, -, k4⟩, fu4⟩ := (WP.spec_ok _).1 hpost
  have hkd4 : (ciSt σ3 t.bv xt).kheap d'.bv = some (.tcb x3) := by rw [ciSt_kh (Ne.symm htd')]; exact hkd3
  have hq4 : ∀ e'' ∈ Z.E, ∀ z, (ciSt σ3 t.bv xt).kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue :=
    fun e'' he'' z hz => hq3 e'' he'' z (by rw [← ciSt_kh (ciSt_ne hz (fun _ h => by cases h))]; exact hz)
  have hx4 : d' ∈ {y | y ∈ X3 ∧ y ≠ t} ∨ ¬ P1.Blocked (L.mem s4 (P1.stA d')) := by
    rcases hx3 with h | h
    · exact Or.inl ⟨h, Ne.symm htd⟩
    · right
      have e0 : L.mem s4 (P1.stA d') = L.mem s3 (P1.stA d') := by
        rw [P1.stA_eq]
        exact k4.fld d' hdH _ (by simp) (by simp) (by simp) (by simp) (fun e1 => absurd e1 (Ne.symm htd))
      rw [e0]; exact h
  have hnr4 : ∀ r ∈ P1.Heap.replies H, L.mem s4 (P1.rTcbA r) ≠ d' := fun r hr => by
    rcases k4.rtcb r hr with e0 | ⟨-, e0⟩
    · rw [e0]; exact hnr3 r hr
    · rw [e0]; intro h0'; exact hdta.ne0 (by rw [← h0']; rfl)
  have hks4 : L.ksb s4 = L.ksb s7 := hW4.1.trans hks3
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s4 _ hR4 hS4 hdT hkd4 hq4 hns3
      .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR4 hS4).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s4 d' _ Q0 R0 h4 hB4 hX4 hS4' hSg4 hdH P1.not_blocked_running P1.running_ne hx4 hnr4
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s4 d' sched.TS_RUNNING h4 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σ5 := Notif.stsAct (Notif.updK (ciSt σ3 t.bv xt) d'.bv (.tcb x5)) d'.bv with hσ5
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 σ5 := IpcRel.ofSRN hR5 hS5
  have hW4' : P1.WritesIn st s7 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW3.trans1 (hW4.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3).1 hb))))
  have hW5' : P1.WritesIn st s7 s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW4'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks4).1 hb))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q0, R0, h5.congrX (P1.excT_congr (X := {y | y ∈ X3 ∧ y ≠ t}) (fun y hy => hXc3 y hy.1))⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans (footW_trans F3 (footW_of fu4)) (footW_of fu5)
  -- the shadows to the end, and the end its own shadow
  have hc3 : t.bv ≠ (Notif.updK σ3 t.bv (.tcb { xt with tcbState := .inactive })).curThread := by
    show t.bv ≠ σ3.curThread; rw [hct3]; exact htc
  have eρ4 : rhoT (ciSt σ3 t.bv xt) t.bv sc.bv xT yS n = rhoT σ3 t.bv sc.bv xT yS n := by
    unfold ciSt; rw [stsAct_ne hc3, rhoT_updKt]
  have hdc4 : d'.bv ≠ (Notif.updK (ciSt σ3 t.bv xt) d'.bv (.tcb x5)).curThread := by
    show d'.bv ≠ (ciSt σ3 t.bv xt).curThread
    rw [(ciSt_skD (σ := σ3) (c := t.bv) (x := xt)).ct, hct3]; exact hdc
  have hdc4ρ : d'.bv ≠ (Notif.updK (rhoT σ3 t.bv sc.bv xT yS n) d'.bv (.tcb x5)).curThread := by
    show d'.bv ≠ σ3.curThread; rw [hct3]; exact hdc
  have eρ5 : rhoT σ5 t.bv sc.bv xT yS n =
      Notif.stsAct (Notif.updK (rhoT σ3 t.bv sc.bv xT yS n) d'.bv (.tcb x5)) d'.bv := by
    rw [hσ5, stsAct_ne hdc4, rhoT_updK _ (Ne.symm htd') hdsc, eρ4, stsAct_ne hdc4ρ]
  have hkd3ρ : (rhoT σ3 t.bv sc.bv xT yS n).kheap d'.bv = some (.tcb x3) := by
    rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd3
  have exT : ({ xt with tcbState := .inactive } : Fl4Spec.Tcb) = xT := by
    simp only [hxt, hxT]; cases x; cases hrs; rfl
  have hk5t : σ5.kheap t.bv = some (.tcb xT) := by
    rw [hσ5, stsAct_kheap]; simp only [updK_kheap, Function.update_of_ne htd']; rw [ciSt_kc, exT]
  have hk5sc : σ5.kheap sc.bv = some (.schedContext yS n) := by
    rw [hσ5, stsAct_kheap]; simp only [updK_kheap, Function.update_of_ne (Ne.symm hdsc)]
    rw [ciSt_kh (Ne.symm hst)]; exact hksc3
  have eσ5 : rhoT σ5 t.bv sc.bv xT yS n = σ5 := rhoT_self hk5t hk5sc
  have Fr5 : CFr e.bv d'.bv σ0 σ5 := by
    rw [← eσ5, eρ5]; exact Fr3.trans (CFr.stsRun hkd3ρ hrb3)
  have IK5 : IK d'.bv σ0 σ5 := by
    rw [← eσ5, eρ5]; exact (IK3.trans (IK.updSelf (y := x5) hkd3ρ rfl)).trans (IK.sts _ _ _)
  have SK5 : SKeep σ0 σ5 := by
    rw [← eσ5, eρ5]
    exact (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3ρ, by cases h; rfl⟩)
      (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hnqD : NotQueued σ0 d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x0, -, -, -, hkx0, -, hrx, -, -⟩ := J0.inv.rq dm p _ hm
      rw [hkd0] at hkx0; cases hkx0; rw [hstd] at hrx; cases hrx
    · obtain ⟨x0, -, -, -, hkx0, -, hrx, -, -⟩ := J0.inv.rel _ hm
      rw [hkd0] at hkx0; cases hkx0; rw [hstd] at hrx; cases hrx
  have hrib : RelIfBound σ5 d'.bv :=
    Ipc.RelIfBound.of_keep (J0.inv.rd d'.bv xd hkd0 (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σ5 := ((J0.inv.toBut d'.bv).ik hnqD IK5).1.inv fun _ _ _ => hrib
  have act5 : σ5.schedulerAction = σ0.schedulerAction := by
    rw [hσ5, stsAct_ne hdc4]
    show (ciSt σ3 t.bv xt).schedulerAction = σ.schedulerAction
    unfold ciSt; rw [stsAct_ne hc3]; exact hact3
  have hAI5 : ActIdle σ5 := ⟨fun u hu => Fr5.sched (J0.act.1 u (by rw [← act5]; exact hu)), Fr5.idleOK J0.act.2⟩
  have hcur5 : σ5.schedulerAction = .chooseNewThread ∨ CurInv σ5 :=
    J0.cur.imp (fun e0 => by rw [act5]; exact e0) Fr5.curInv
  have hrun5 : CurRunM σ5 := J0.curRun.of_cn Fr5.curRunW (Or.inr act5)
  -- the footprints from the base
  have hSσ := J.xtop.fin.1.1.1
  obtain ⟨Qs, Rs, hcs, hsps⟩ := hSσ.lists
  obtain ⟨ys, ns, hkys, hys⟩ := hsps.scs sc hsc
  rw [hky] at hkys; cases hkys
  have hal8 : P1.Aligned (scW sc 8#u64) := (hys.hdr (K := 8#u64) (by simp) (by simp)).1
  have hta := hP.tcb t ht
  have hw0 : P1.WritesIn st s s0 (fun b => (((b = tFaultA t ∨ b = tFw0A t) ∨ b = tFw1A t) ∨ b = tFw2A t) ∨
      b = scW sc 8#u64) :=
    ((((writesIn_wr (st := st) (s := s) (v := fl4_abi.consts.fault.Timeout) (a_fault hta).1).trans
      (writesIn_wr (v := b) (a_fw0 hta).1)).trans (writesIn_wr (v := 0#u64) (a_fw1 hta).1)).trans
      (writesIn_wr (v := 0#u64) (a_fw2 hta).1)).trans (writesIn_wr (v := 0#u64) hal8)
  have hz7 : SzKeepC Z.C σ σf := SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := xt) (fun q hq => hkf q hq) hkt)
  have hWs5 : P1.WritesIn st s s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hW7.trans1 (hW5'.mono fun b hb => cnW_back hW7.1 hz7 hb)
  have hsw : SW Z.C σ (scW sc 8#u64) := sw_hdr hSσ hsc (K := 8#u64) (by simp) (by simp) (by decide)
  have hsub0 : ∀ b0, ((((b0 = tFaultA t ∨ b0 = tFw0A t) ∨ b0 = tFw1A t) ∨ b0 = tFw2A t) ∨ b0 = scW sc 8#u64) →
      CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b0 := by
    intro b0 hb0
    rcases hb0 with (((h | h) | h) | h) | h <;> subst h
    · exact Or.inl (Or.inr ⟨t, ht, 3376, by omega, by omega, by omega, by omega, by omega, val_fault hta⟩)
    · exact Or.inl (Or.inr ⟨t, ht, 3384, by omega, by omega, by omega, by omega, by omega, val_fw0 hta⟩)
    · exact Or.inl (Or.inr ⟨t, ht, 3392, by omega, by omega, by omega, by omega, by omega, val_fw1 hta⟩)
    · exact Or.inl (Or.inr ⟨t, ht, 3400, by omega, by omega, by omega, by omega, by omega, val_fw2 hta⟩)
    · exact Or.inl (Or.inl (Or.inr (Or.inr hsw)))
  have hz0 : SzKeepC Z.C σ0 σ := by
    intro p _ y0 m hp
    by_cases hps : p = sc
    · subst hps; rw [hky] at hp; cases hp; exact ⟨yS, by rw [hσ0r]; exact rhoT_ksc⟩
    · have hps' : p.bv ≠ sc.bv := fun e0 => hps (P1.eq_of_bv e0)
      have hpt : p.bv ≠ t.bv := fun e0 => by rw [e0, hkx] at hp; cases hp
      exact ⟨y0, by rw [hk0 _ hpt hps']; exact hp⟩
  have hW05 : P1.WritesIn st s0 s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s0 σ0) :=
    (writesIn_rebase hWs5 hw0 hsub0).mono fun b0 hb0 => CnW.back (s := s0) (s' := s) hw0.1.symm hz0 hb0
  have hfs5 := footW_trans (footW_of (W := fun _ => False) hfoot7) hfoot
  have hsubK : ∀ b0, ((((b0 = tFaultA t ∨ b0 = tFw0A t) ∨ b0 = tFw1A t) ∨ b0 = tFw2A t) ∨ b0 = scW sc 8#u64) →
      P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s b0 ∨ False := by
    intro b0 hb0
    rcases hb0 with (((h | h) | h) | h) | h <;> subst h
    · exact Or.inl (Or.inl ⟨t, htH, 3376#u64, by simp, by simp, by simp, by simp, rfl⟩)
    · exact Or.inl (Or.inl ⟨t, htH, 3384#u64, by simp, by simp, by simp, by simp, rfl⟩)
    · exact Or.inl (Or.inl ⟨t, htH, 3392#u64, by simp, by simp, by simp, by simp, rfl⟩)
    · exact Or.inl (Or.inl ⟨t, htH, 3400#u64, by simp, by simp, by simp, by simp, rfl⟩)
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc1, scW8_inSC J.blk hsc1⟩))))
  have hfoot05 : P1.WritesIn st s0 s5 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s0) :=
    (writesIn_rebase hfs5 hw0 hsubK).mono fun b0 hb0 => hb0.elim (P1.KW.ksb hw0.1.symm) False.elim
  have hI0 := J0.xtop.irelK J0.ks J0.buf
  have hF : IFrame (L := L) Z.th s0 s5 := IRel.iframe_of hI0 hW05 fun b0 hb0 => CnW.oobj hI0.2.2.1 hb0
  have htD := J0.not_dead_of_st hdT hkd0 (by rw [hstd]; simp [tsCode])
  have hRR : ∀ q' ∈ Z.R, ∀ xr, σ0.kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem s0 (rNextA q') = 0#u64 ∧ L.mem s0 (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds _ Ac Lst D s0 _ σ0 J0 q' hq'' xr d'.bv xd hx'
      hxt' hkd0 (by rw [hstd]; rfl)
  obtain ⟨V', J5⟩ := J0.wake_postD hIR hF hW05 hblk hfoot05 (DWFr.ofCFr Fr5) I5 (Fr5.bsa J0.bsa) hAI5
    hcur5 hrun5 hRR htD ⟨d', hdT, rfl⟩
  -- the tail
  have hk5 : σ5.kheap d'.bv = some (.tcb x5) := by rw [hσ5, stsAct_kheap]; simp
  have hnr5 : d'.bv ∉ σ5.releaseQueue := by rw [SK5.1]; exact hnqD.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → σ5.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hy0 := SK5.2.2.2 p y n hy
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := J0.inv.back _ _ _ hkd0 hp'
    rw [hy0] at hky'; cases hky'
    exact J0.bsa.tcb p y n d'.bv xd hy0 hyt hkd0 (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ σ5.idleThread := by
    rw [Fr5.sk.idle]
    intro h
    obtain ⟨x0, hkx0, -, hxs, -⟩ := J0.act.2
    rw [← h, hkd0] at hkx0; cases hkx0; rw [hstd] at hxs; cases hxs
  have htc5 : d'.bv ≠ σ5.curThread := by rw [Fr5.sk.ct]; exact hdc
  have hcond : ¬ ((g = true ∨ gr = true) ∧ rep ≠ none) := by
    rintro ⟨hg, hr⟩
    rcases hno with ⟨rfl, rfl⟩ | hn
    · rcases hg with h | h <;> cases h
    · exact hr (hn xd hkdσ _ _ _ hstd)
  have hspec := sendIpc_faultInactive_eq (don := false) hk hkd hde htd' hstd true badge.bv g gr hcond e2 hU hkt3 hkd3
    (by rw [hft]; simp) (t := t.bv)
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7', a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  refine ⟨((), σ7), ?_, ⟨_, _, _, _, _, _, J7⟩⟩
  rw [hspec]
  show ((), σ7) ∈ (Endp.specWakeTailE d'.bv σ5).1
  rw [h7]; exact Set.mem_singleton _

set_option maxHeartbeats 64000000 in
/-- **The timeout-fault `send_ipc` of a thread other than the current one to
a waiting receiver with a reply object, the sender with the grant or
grant-reply right: the reply pushed without a donation** (`can_donate` is
false for `handle_timeout`; as `JAtZ.sendTmoRecvIJ` up to the reply unlink,
then `reply_push` as XTopJointFaultRecv's `JAtZ.sendFaultPJ` (P1's queue bits
of the sender from `NotQueued`, its SC's activity from its `CanBlock` at the
send, the action not the sender nor the receiver by `actionW_ne_of`);
`JAtZ` by `JAtZ.wake_postGR` from the base `JAtZ.tmoBaseJ` at the push from
the receiver's woken shadow (`pushSt`, the scheduler action kept: the sender
is not the current thread). -/
theorem JAtZ.sendTmoRecvPJ (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hcr : ∃ xc, σ.kheap σ.curThread = some (.tcb xc) ∧ Fl4Spec.runnable xc.tcbState = true)
    {t : U64} (ht : t ∈ Z.T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (htc : t.bv ≠ σ.curThread) {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (b : U64) {ts : Fl4Spec.ThreadState} (hrun : Fl4Spec.runnable ts = true) {s7 : S}
    (hI7 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s7
      (updK σ t.bv (.tcb { x with tcbState := ts, tcbFault := some (.timeout b.bv) })))
    (hblk7 : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s7)
    (hW7 : P1.WritesIn st s s7 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hfoot7 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s7)
    (hcb7 : P1.CanBlock st (P1.Heap.tcbs H) Ac s7 t)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hke : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (badge : U64) (g gr : Bool)
    (hg : g = true ∨ gr = true) (htD : t ∉ D) (hya : Fl4Spec.scActive y = true)
    (hrepn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none) :
    endpoint.send_ipc st arI s7 a true false badge g gr false t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) true false badge.bv g gr false t.bv e.bv
        (updK σ t.bv (.tcb { x with tcbState := ts, tcbFault := some (.timeout b.bv) }))).1,
        JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  set xt : Fl4Spec.Tcb := { x with tcbState := ts, tcbFault := some (.timeout b.bv) } with hxt
  set σf := updK σ t.bv (.tcb xt) with hσf
  set xT : Fl4Spec.Tcb := { x with tcbFault := some (.timeout b.bv) } with hxT
  set yS : Fl4Spec.SchedContext := { y with scConsumed := (0#u64 : U64).bv } with hyS
  have hns : ∀ e d, x.tcbState ≠ .blockedOnSend e d := by rw [hrs]; intro _ _ h; cases h
  have hst : t.bv ≠ sc.bv := fun e0 => by rw [e0, hky] at hk; cases hk
  -- the base `J` state
  obtain ⟨V0, J0⟩ := J.tmoBaseJ hAT hmax htu ht hk hns b hsc hky
  set s0 := tmoS st (fltS st s t b) sc with hs0
  set σ0 := Ipc.tmoSt (updK σ t.bv (.tcb xT)) sc y n with hσ0
  have hσ0r : σ0 = rhoT σ t.bv sc.bv xT yS n := rfl
  have hfr : rhoT σf t.bv sc.bv xT yS n = σ0 := by rw [hσf, rhoT_updKt, hσ0r]
  have hk0 : ∀ q, q ≠ t.bv → q ≠ sc.bv → σ0.kheap q = σ.kheap q := fun q h1 h2 => by
    rw [hσ0r]; exact rhoT_kh h1 h2
  have hkf : ∀ q, q ≠ t.bv → σf.kheap q = σ.kheap q := fun q h1 => by simp [hσf, updK, h1]
  have hP0 := J.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hI := hI7
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hRe : Z.R = P1.Heap.replies H := J.tcbs_eq.2
  have hte0 : t.bv ≠ e.bv := kheap_ne hk hke (fun _ h1 h2 => by subst h1; cases h2)
  have hse0 : sc.bv ≠ e.bv := kheap_ne hky hke (fun _ h1 h2 => by subst h1; cases h2)
  have hkx := hk
  have hk : σf.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))) := by rw [hkf _ (Ne.symm hte0)]; exact hke
  have hkt : σf.kheap t.bv = some (.tcb xt) := by simp [hσf, updK]
  have hrn : Fl4Spec.runnable xt.tcbState = true := hrun
  have hft : xt.tcbFault = some (.timeout b.bv) := rfl
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ Z.T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  obtain ⟨xd, hkd, -⟩ := hI.1.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s7 (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s7 (tBlockA d') = e := (hB d' (by simp)).2
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by have := runnable_code hrn; omega
  have htd : t ≠ d' := by intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := hte0
  have htd' : t.bv ≠ d'.bv := bv_ne htd
  have hdsc : d'.bv ≠ sc.bv := fun e0 => by
    have h1 : σf.kheap sc.bv = some (.schedContext y n) := by rw [hkf _ (Ne.symm hst)]; exact hky
    rw [e0, h1] at hkd; cases hkd
  have hkdσ : σ.kheap d'.bv = some (.tcb xd) := by rw [← hkf _ (Ne.symm htd')]; exact hkd
  have hkd0 : σ0.kheap d'.bv = some (.tcb xd) := by rw [hk0 _ (Ne.symm htd') hdsc]; exact hkdσ
  have hke0 : σ0.kheap e.bv = some (.endpoint (.recvEP (d'.bv :: q))) := by
    rw [hk0 _ (Ne.symm hte0) (Ne.symm hse0)]; exact hke
  have hdc : d'.bv ≠ σf.curThread := by
    intro h
    obtain ⟨xc, hkc, hrc⟩ := hcr
    have h' : d'.bv = σ.curThread := h
    rw [← h', hkdσ] at hkc; cases hkc; rw [hstd] at hrc; cases hrc
  -- P1's facts at the send
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := hblk7
  have hdH : d' ∈ P1.Heap.tcbs H := J.zH.1 d' hdT
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hdta := hTP d' hdH
  have hsub := hSg0.sub
  have hds : L.mem s7 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := by
    rw [stA_tStA, tsVals.2.2.1]; exact UScalar.eq_of_val_eq hd3
  have hbe : L.mem s7 (P1.blockA d') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hdb
  have hdq := P1.endpoint.ep_dequeue.inv s7 d' Q0 R0 h0 hdH (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : d' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 d' hdH (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s7 e d' (EQ0 e) hTP hE0 hq0' hdm
  -- FL4: the endpoint's state and queue
  unfold endpoint.send_ipc
  refine WP.spec_bind (Fl4Proofs.P1.obj.Ep.state.spec s7 e) ?_
  rintro _ rfl
  rw [epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s7 e) ?_
  rintro _ rfl
  have hhead : (L.epQ s7 e).head = d' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s7 σf hR hS0 he hk (d := d')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s7 he d' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  set σ1 := Notif.updK σf e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1
  have hW1a : P1.WritesIn st s7 s1 (fun b => EW e b ∨ ∃ w ∈ (d' :: xs'), TL w b) :=
    ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩⟩
  have hW1 : P1.WritesIn st s7 s1 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) := hW1a.mono fun b hb => by
    rcases hb with h | ⟨w, hw, h | h⟩
    · exact Or.inr (Or.inl ⟨e, he, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
  have F1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s7 s1 :=
    P1.Foot.of w1 fun b hb => hb.kw hq0'.mem (Or.inl hHe)
  obtain ⟨hB1, hX1, hS1', hSg1, ea1, -, -⟩ := P1.frame_bx h0 hB0 hX0 hSc0 hSg0 f1 o1 n1 k1
    (P1.TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg0.sub _ (hX0.1.ntB n' hn').2)⟩)
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hky1 : σ1.kheap sc.bv = some (.schedContext y n) := by
    simp [σ1, hse0, hσf, updK, Ne.symm hst, hky]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  -- the shadow frame from the base
  have eρ1 : rhoT σ1 t.bv sc.bv xT yS n = updK σ0 e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    rw [hσ1, rhoT_updK _ (Ne.symm hte) (Ne.symm hse0), hfr]
  have Fr1 : CFr e.bv d'.bv σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    exact CFr.upd hke0 (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
      by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
      by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1 : IK d'.bv σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    exact IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hke0 (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : SKeep σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    exact SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h)
      (fun _ _ h => by cases h)
  have hOKσ := (J.xferH).1
  have hBCσ := (J.xferH).2.1
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (ipcBufCapOK_updT (y := xt) hOKσ hkx rfl rfl) (EpStep.ep hk)
  have hBC1 : Endp.BufCover Z.T Z.B σ1 := bufCover_epStep (bufCover_updT (y := xt) hBCσ hkx rfl rfl) (EpStep.ep hk)
  have hsc1 : sc ∈ P1.Heap.scs H := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨_, (hJ.sc sc y n (J.c0 sc hsc) hky).2⟩
  -- the transfer
  refine WP.spec_bind (xferTmoStepJ hP0 (hH.epHyps hP0) hmax s1 a σ1 htu hR1 hS1 hOK1 hBC1 ht hdT htd hkt1 hkd1 hft
    hxsc hky1 e badge g hTP hdH h1 hB1 hX1 hS1' hSg1 hsc1) ?_
  rintro s2 ⟨x2, e2, hx2, hR2, hS2, hA2, w2, ea2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Ipc.tmoSt σ1 sc y n) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by
    rw [hσ2]
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne htd', Function.update_of_ne hst]
    exact hkt1
  have hksc2 : σ2.kheap sc.bv = some (.schedContext yS n) := by
    rw [hσ2, updK_kheap, Function.update_of_ne (Ne.symm hdsc)]
    show Function.update σ1.kheap sc.bv _ sc.bv = _
    rw [Function.update_self]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc2 : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    rw [hσ2]
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne (Ne.symm hde), Function.update_of_ne (Ne.symm hse0)]
    exact hk1e
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    have hns' : sc.bv ≠ e''.bv := by intro h; rw [← h, hksc2] at hz; cases hz
    rw [hσ2] at hz
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne (Ne.symm hne),
      Function.update_of_ne (Ne.symm hns')] at hz
    exact hq1 e'' he'' z hz
  have hrw : L.mem s2 (tReplyA d') = L.mem s7 (tReplyA d') := by
    rw [show tReplyA d' = core.num.U64.wrapping_add d' 3360#u64 from rfl, f2 d' hdH _ (by simp) (by simp) (by simp),
      ← show tReplyA d' = core.num.U64.wrapping_add d' 3360#u64 from rfl,
      hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
  have hscw8 : SW Z.C σf (scW sc 8#u64) := sw_hdr hI.2.2.1 hsc (K := 8#u64) (by simp) (by simp) (by decide)
  have hW2 : P1.WritesIn st s7 s2 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW1.trans1 (w2.mono fun b hb => by
    rcases hb with ⟨eb, -⟩ | (⟨y0, hy, K, h1', h2', -, eb⟩ | hb)
    · subst eb; exact Or.inl (Or.inl (Or.inr (Or.inr hscw8)))
    · have hyT : y0 ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inr ⟨y0, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩)
      rw [eb]; exact tfield_val (hP.tcb y0 hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _))
  have F2 : P1.WritesIn st s1 s2 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1) :=
    w2.mono fun b hb => by
      rcases hb with ⟨-, c0, hc0, hin⟩ | (⟨y0, hy, K, h1', h2', h3', eb⟩ | hb)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c0, hc0, hin⟩)))
      · exact Or.inl ⟨y0, hy, K, by omega, by omega, by omega, by omega, eb⟩
      · exact absurd hb (Set.notMem_empty _)
  have eρ2 : rhoT σ2 t.bv sc.bv xT yS n = updK (rhoT σ1 t.bv sc.bv xT yS n) d'.bv (.tcb x2) := by
    rw [hσ2, rhoT_updK _ (Ne.symm htd') hdsc, rhoT_updKsc _ hst]
  have hkd1ρ : (rhoT σ1 t.bv sc.bv xT yS n).kheap d'.bv = some (.tcb xd) := by
    rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd1
  have Fr2 : CFr e.bv d'.bv σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]
    exact Fr1.trans (CFr.upd hkd1ρ (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl,
      by rw [hx2], Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]; exact IK1.trans (IK.updSelf hkd1ρ hxsc2)
  have SK2 : SKeep σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]
    exact SK1.trans (SKeep.updK (p := d'.bv) (o := .tcb x2) (fun y h => ⟨xd, hkd1ρ, by cases h; exact hxsc2.symm⟩)
      (fun _ _ h => by cases h))
  have hks2 : L.ksb s2 = L.ksb s7 := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s7 (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  obtain ⟨r, hrp⟩ := Option.ne_none_iff_exists'.1 (hrepn xd hkdσ _ _ _ hstd)
  subst hrp
  obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
  have hwR := hrepR (by simp)
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  have hne0 : (L.mem s7 (tReplyA d') != 0#u64) = true := by simp [hw0]
  simp only [hne0, ↓reduceIte, Bool.false_eq_true, eq_self_iff_true, if_true]
  set w := L.mem s7 (tReplyA d') with hwdef
  subst hwr
  obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
  have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hws : w.bv ≠ sc.bv := fun e0 => by
    have h1 : σf.kheap sc.bv = some (.schedContext y n) := by rw [hkf _ (Ne.symm hst)]; exact hky
    rw [e0, h1] at hkr; cases hkr
  have hkr2 : σ2.kheap w.bv = some (.reply xr) := by
    rw [hσ2]
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne hwd, Function.update_of_ne hws]
    simp [σ1, hwe, hkr]
  have hkrσ : σ.kheap w.bv = some (.reply xr) := by rw [← hkf _ hwt]; exact hkr
  have hb' : xr.replyTcb = some d'.bv := hback_of J.sv hkdσ e.bv w.bv dd xr (by rw [hstd]) hkrσ
  have hX2' := IpcRel.ofSRN hR2 hS2
  have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
  obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
  rw [hrA] at hiR hit
  refine WP.spec_bind (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2 hdT hkd2 hst2' hwR hkr2
      hb' hq2) (reply_unlink_cn hP0 hX2' hdT hwR hkr2))
    (WP.spec_and (P1.ipc.reply_unlink.inv s2 w d' Q0 R0 h2 hdH hX2.1 hsub hiR hit
        (by rw [hds2]; exact P1.blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
      (P1.ipc.reply_unlink.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s2 w d' h2 hX2 hsub hiR hdH))) ?_
  rintro s3 ⟨⟨⟨e3, hR3, hS3⟩, hW3⟩, ⟨h3, e3', k3, z3⟩, fu3⟩
  have hclr : ∀ r ∈ P1.Heap.replies H, L.mem s2 (P1.rTcbA r) = d' → L.mem s3 (P1.rTcbA r) = 0#u64 := by
    intro r hr er
    obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
    rw [er, hrA] at b2; rw [← b2]; exact z3
  set x3 : Fl4Spec.Tcb := { x2 with tcbState := .inactive } with hx3
  set xr3 : Fl4Spec.Reply := { xr with replyTcb := none } with hxr3
  set σ3a := Notif.updK σ2 w.bv (.reply xr3) with hσ3a
  have hkd3a : σ3a.kheap d'.bv = some (.tcb (x2)) := by simp [σ3a, Ne.symm hwd, hkd2]
  have hct3a : d'.bv ≠ (Notif.updK σ3a d'.bv (.tcb x3)).curThread := hdc
  have e3s : Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv = Notif.updK σ3a d'.bv (.tcb x3) :=
    stsAct_ne hct3a
  set σ3 := Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv with hσ3
  have hU : Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) (some w.bv) σ2 =
      ({((), σ3)}, False) := e3
  have hW3' : P1.WritesIn st s7 s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW2.trans1 (hW3.mono fun b hb => cnW_back hks2 (SzKeepC.of (by
      intro p y0 m hp
      by_cases hps : p = sc.bv
      · subst hps; rw [hksc2] at hp; cases hp; exact ⟨y, by rw [hkf _ (Ne.symm hst)]; exact hky⟩
      · refine ⟨y0, ?_⟩
        rw [hσ2] at hp
        have hpd : p ≠ d'.bv := fun e0 => by rw [e0] at hp; simp at hp
        simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne hpd, Function.update_of_ne hps] at hp
        have hpe : p ≠ e.bv := fun e0 => by rw [e0] at hp; simp [σ1] at hp
        simpa [σ1, hpe] using hp)) hb)
  have hkt3 : σ3.kheap t.bv = some (.tcb xt) := by rw [stsAct_kheap]; simp [σ3a, htd', hwt.symm, hkt2]
  have hkd3 : σ3.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp
  have hkr3 : σ3.kheap w.bv = some (.reply xr3) := by rw [stsAct_kheap]; simp [σ3a, hwd]
  have hksc3 : σ3.kheap sc.bv = some (.schedContext yS n) := by
    rw [stsAct_kheap]; simp [σ3a, Ne.symm hdsc, hws.symm, hksc2]
  have hq3 : ∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    rw [stsAct_kheap] at hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
    have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [σ3a, hwd] at hz
    exact hq2 e'' he'' z (by simpa [σ3a, Ne.symm hne, Ne.symm hne'] using hz)
  -- the shadows
  have hkr2ρ : (rhoT σ2 t.bv sc.bv xT yS n).kheap w.bv = some (.reply xr) := by
    rw [rhoT_kh hwt hws]; exact hkr2
  have hkd3aρ : (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv (.reply xr3)).kheap d'.bv = some (.tcb x2) := by
    simp only [updK_kheap, Function.update_of_ne (Ne.symm hwd)]
    rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd2
  have eρ3 : rhoT σ3 t.bv sc.bv xT yS n =
      Notif.stsAct (Notif.updK (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv (.reply xr3)) d'.bv (.tcb x3)) d'.bv := by
    rw [e3s, stsAct_ne (show d'.bv ≠ (Notif.updK (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv
      (.reply xr3)) d'.bv (.tcb x3)).curThread from hdc), hσ3a, rhoT_updK _ (Ne.symm htd') hdsc, rhoT_updK _ hwt hws]
  have Fr3 : CFr e.bv d'.bv σ0 (rhoT σ3 t.bv sc.bv xT yS n) := by
    rw [eρ3]
    exact (Fr2.trans (CFr.upd hkr2ρ (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
      (CFr.stsIn hkd3aρ (Or.inl ⟨_, _, _, hst2'⟩))
  have IK3 : IK d'.bv σ0 (rhoT σ3 t.bv sc.bv xT yS n) := by
    rw [eρ3]
    have IK3a : IK d'.bv σ0 (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv (.reply xr3)) :=
      IK2.trans (IK.updOther (o' := .reply xr3) hkr2ρ (fun o0 h => by
        rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
    exact (IK3a.trans (IK.updSelf (y := x3) hkd3aρ rfl)).trans (IK.sts _ _ _)
  have SK3 : SKeep σ0 (rhoT σ3 t.bv sc.bv xT yS n) := by
    rw [eρ3]
    exact ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply xr3) (fun y h => by cases h)
      (fun _ _ h => by cases h))).trans (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3aρ, by cases h; rfl⟩)
      (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hct3 : σ3.curThread = σ.curThread := by rw [e3s]; rfl
  have hact3 : σ3.schedulerAction = σ.schedulerAction := by rw [e3s]; rfl
  have hsc3 : x3.tcbSchedContext = xd.tcbSchedContext := by simp [x3, hxsc2]
  have hB3 := hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1)
  have hX3 := hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr
  have hS3' := hS2''.keepT hX2 k3
  have hSg3 : P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 :=
    ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩
  have F3 := footW_trans (footW_trans (footW_of (W := fun _ => False) F1) (F2.mono fun b hb => Or.inl hb))
    (footW_of fu3)
  have hxt3 := hR3.at_tcb ht hkt3
  have hty3 : L.mem s3 (tFaultA t) = 5#u64 := by
    have hfr := hxt3.faultR
    unfold FaultRel at hfr; rw [hft] at hfr; exact hfr.1
  have hks3 : L.ksb s3 = L.ksb s7 := hW3'.1
  -- the sender's and the receiver's words at `s3`
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = tsCode xt.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st]
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (w := L.mem s3 (P1.stA t)) (by rw [hw3]; exact runnable_code hrn)
  have hX3' := IpcRel.ofSRN hR3 hS3
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hX3'.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have hSM := ScRelM.of hX3'.1
  have hnqD : NotQueued σ d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x0, -, -, -, hkx0, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
      rw [hkdσ] at hkx0; cases hkx0; rw [hstd] at hrx; cases hrx
    · obtain ⟨x0, -, -, -, hkx0, -, hrx, -, -⟩ := J.inv.rel _ hm
      rw [hkdσ] at hkx0; cases hkx0; rw [hstd] at hrx; cases hrx
  have hnqT : NotQueued σ t.bv := J.inv.notQueued hkx (by rw [hrs]; rfl)
  have hqq3 : σ3.readyQueues = σ.readyQueues := IK3.2.1
  have hrq3 : σ3.releaseQueue = σ.releaseQueue := IK3.2.2.1
  have hnqT3 : NotQueued σ3 t.bv := ⟨by rw [hqq3]; exact hnqT.1, by rw [hrq3]; exact hnqT.2⟩
  have hnqD3 : NotQueued σ3 d'.bv := ⟨by rw [hqq3]; exact hnqD.1, by rw [hrq3]; exact hnqD.2⟩
  have bits3 : ∀ u ∈ Z.T, NotQueued σ3 u.bv →
      (L.mem s3 (P1.inqA u) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s3 (P1.inqA u) &&& sched.Q_RELEASE) = 0#u64 := by
    intro u hu hnu
    refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
    · have hm := (hcq3.queued u hu).1 h
      apply hnu.1 0 (specPrio (L.mem s3 (P1.prioA u)))
      rw [hs3.rq _ (hcq3.prio u hu)]
      exact List.mem_map_of_mem hm
    · have hm := (hcq3.released u hu).1 h
      apply hnu.2
      rw [hs3.rel]
      exact List.mem_map_of_mem hm
  obtain ⟨hqbT, hrbT⟩ := bits3 t ht hnqT3
  obtain ⟨hqbD, hrbD⟩ := bits3 d' hdT hnqD3
  have hna3t : L.actionW s3 ≠ t := actionW_ne_of hSR3 ht (by
    rw [hact3]; intro e0
    obtain ⟨x', -, -, -, h1', -, h3', -⟩ := schedulable_inv (J.act.1 _ e0)
    rw [hkx] at h1'; cases h1'; rw [hrs] at h3'; cases h3')
  have hna3d : L.actionW s3 ≠ d' := actionW_ne_of hSR3 hdT (by
    rw [hact3]; intro e0
    obtain ⟨x', -, -, -, h1', -, h3', -⟩ := schedulable_inv (J.act.1 _ e0)
    rw [hkdσ] at h1'; cases h1'; rw [hstd] at h3'; cases h3')
  have hidl3 : σ3.idleThread = σ.idleThread := by rw [e3s]; rfl
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σ.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σ.idleThread := by
    intro h
    obtain ⟨x0, hkx0, -, hxs, -⟩ := J.act.2
    rw [← h, hkx] at hkx0; cases hkx0; rw [hrs] at hxs; cases hxs
  have hid : d'.bv ≠ σ.idleThread := by
    intro h
    obtain ⟨x0, hkx0, -, hxs, -⟩ := J.act.2
    rw [← h, hkdσ] at hkx0; cases hkx0; rw [hstd] at hxs; cases hxs
  have hsA3 : L.mem s3 (P1.scA t) = L.mem s7 (P1.scA t) := by
    rw [P1.scA_eq, k3.fld t htH _ (by simp) (by simp) (by simp) (by simp) (fun e0 => absurd e0 htd),
      f2 t htH _ (by simp) (by simp) (by simp), f1 t htH _ (by simp) (by simp) (by simp) (by simp)]
  have hcA : L.mem s3 (P1.scA t) ≠ 0#u64 → L.mem s3 (P1.scA t) ∈ Ac := fun h0' => by
    rw [hsA3] at h0' ⊢; exact hcb7.ac h0'
  have hwH : w ∈ P1.Heap.replies H := hRe ▸ hwR
  have hw00 : w ≠ 0#u64 := (J.rp.align w hwR).2.1
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  -- the push on `IRel`, at P1
  have hw1 : P1.WritesIn st s3 (L.wr s3 (P1.rTcbA w) t) (fun b => b.val = w.val) := by
    obtain ⟨-, -, -, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s3 σ3 hR3 hS3.1 hwR hkr3 t
    exact ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
  have hns3 : tsCode xt.tcbState ≠ 6 := by have := runnable_code hrn; omega
  have hPush : ipc.reply_push st arI s3 a t d' w false ⦃ r => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv false σ3 = ({((), pushSt σ3 t.bv w.bv xr3 xt)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) (pushSt σ3 t.bv w.bv xr3 xt) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 (pushSt σ3 t.bv w.bv xr3 xt) ∧
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      (∀ y ∈ P1.Heap.tcbs H, y ≠ t → L.mem r.1 (P1.stA y) = L.mem s3 (P1.stA y)) ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1 ∧
      sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA w) t) t w = ok r.1 ⦄ := by
    refine WP.spec_mono (WP.spec_and (WP.spec_and
      (reply_push_iC (don := false) (P := fun s' σ' => σ' = pushSt σ3 t.bv w.bv xr3 xt ∧
          EpStateRel Z.T Z.E Z.R Z.B (L.mem s') σ' ∧
          SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
            (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s' σ')
        hH hP0 hP s3 a σ3 hR3 hS3 ht hkt3 hkd3 hqt3 hns3 hwR hkr3 (fun _ => hdT)
        (fun s' h1 h2 => ⟨rfl, h1, h2⟩) (fun hdon => by cases hdon))
      (P1.ipc.reply_push.ipc hAT s3 a t d' w false Q0 R0 h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        hna3t (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 (J.zH.1 d' hdT)
        (Ne.symm htd) hqbD hrbD hna3d (hiw3 d' hdT hid) hcA))
      (P1.ipc.reply_push.nd (Es := P1.EH H) s3 a t d' w false h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        hna3t (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 (J.zH.1 d' hdT)
        (Ne.symm htd) hcA (Or.inl rfl))) ?_
    rintro ⟨s4, a4⟩ ⟨⟨⟨ha, σ', hm, e4, hR4, hS4⟩, hb1, hb2, -⟩, -, hf, hsb⟩
    subst e4
    exact ⟨ha, hm, hR4, hS4, hb1, hb2, hf, hsb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv false σ3 = ({((), pushSt σ3 t.bv w.bv xr3 xt)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) (pushSt σ3 t.bv w.bv xr3 xt) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 (pushSt σ3 t.bv w.bv xr3 xt) ∧
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      (∀ y ∈ P1.Heap.tcbs H, y ≠ t → L.mem r.1 (P1.stA y) = L.mem s3 (P1.stA y)) ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1 ∧
      sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA w) t) t w = ok r.1) ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 rfl
    rw [hty3, if_pos (by unfold fl4_abi.consts.fault.NullFault; decide)]
    rcases hg with rfl | rfl
    · simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true]; exact hPush
    · cases g <;> simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true] <;> exact hPush
  rintro ⟨s4, a4⟩ ⟨ha4, hpush, hR4, hS4, ⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4', hSg4⟩, hst4, fu4, hsb4⟩
  simp only at ha4 hpush hR4 hS4 h4 hB4 hX4 hS4' hSg4 hst4 fu4 hsb4 ⊢
  subst ha4
  try dsimp only
  have hW4 : P1.WritesIn st s3 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s3 σ3) := by
    have h := set_blocked_on_reply_cn (N := Z.N) (C := Z.C) (E := Z.E) hP hSR3 ht hwR hw1
    rw [hsb4, WP.spec_ok] at h; exact h
  have hz3 : SzKeepC Z.C σf σ3 := by
    intro p _ y0 m hp
    by_cases hps : p = sc
    · subst hps; rw [hksc3] at hp; cases hp; exact ⟨y, by rw [hkf _ (Ne.symm hst)]; exact hky⟩
    · have hps' : p.bv ≠ sc.bv := fun e0 => hps (P1.eq_of_bv e0)
      have hpt : p.bv ≠ t.bv := fun e0 => by rw [e0, hkt3] at hp; cases hp
      have hpd : p.bv ≠ d'.bv := fun e0 => by rw [e0, hkd3] at hp; cases hp
      have hpw : p.bv ≠ w.bv := fun e0 => by rw [e0, hkr3] at hp; cases hp
      have hpe : p.bv ≠ e.bv := fun e0 => by
        have h1 : σ3.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
          rw [stsAct_kheap]; simp [σ3a, updK, Ne.symm hde, Ne.symm hwe, hk1e2]
        rw [e0, h1] at hp; cases hp
      refine ⟨y0, ?_⟩
      rw [stsAct_kheap] at hp
      simp [σ3a, hσ2, updK, hpd, hpw, hps', σ1, hpe] at hp
      exact hp
  have hW4' : P1.WritesIn st s7 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW3'.trans1 (hW4.mono fun b hb => cnW_back hks3 hz3 hb)
  have hks4 : L.ksb s4 = L.ksb s7 := hW4'.1
  set σ4 := pushSt σ3 t.bv w.bv xr3 xt with hσ4
  have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := by rw [ps_ko (Ne.symm htd') (Ne.symm hwd)]; exact hkd3
  have hq4 : ∀ e'' ∈ Z.E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue :=
    fun e'' he'' z hz => hq3 e'' he'' z ((ps_oth hkt3 hkr3 hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hz)
  have hst4d : L.mem s4 (P1.stA d') = sched.TS_INACTIVE := by rw [hst4 d' hdH (Ne.symm htd)]; exact e3'
  have hx4 : d' ∈ (∅ : Set U64) ∨ ¬ P1.Blocked (L.mem s4 (P1.stA d')) := Or.inr (by rw [hst4d]; exact P1.not_blocked_inactive)
  have hnr4 : ∀ r ∈ P1.Heap.replies H, L.mem s4 (P1.rTcbA r) ≠ d' :=
    hX4.noref hdta (by rw [hst4d]; exact P1.inactive_ne.1) (by rw [hst4d]; exact P1.inactive_ne.2)
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s4 _ hR4 hS4 hdT hkd4 hq4
      (by simp [x3, tsCode]) .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR4 hS4).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s4 d' _ Q4 R4 h4 hB4 hX4 hS4' hSg4 hdH P1.not_blocked_running P1.running_ne hx4 hnr4
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s4 d' sched.TS_RUNNING h4 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σa := Notif.stsAct (Notif.updK σ3 d'.bv (.tcb x5)) d'.bv with hσa
  have hdc3 : d'.bv ≠ σ3.curThread := by rw [hct3]; exact hdc
  have heq5 : Notif.stsAct (Notif.updK σ4 d'.bv (.tcb x5)) d'.bv = pushSt σa t.bv w.bv xr3 xt :=
    ps_swap htd' hwd hdc3
  have hW5' : P1.WritesIn st s7 s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW4'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks4).1 hb))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q4, R4, h5.congrX P1.empty_congr⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans (footW_trans F3 (footW_of fu4)) (footW_of fu5)
  have hrb3 : RbIn x3.tcbState := Or.inr rfl
  -- the shadow of the state before the push
  have hdcρ : d'.bv ≠ (Notif.updK (rhoT σ3 t.bv sc.bv xT yS n) d'.bv (.tcb x5)).curThread := by
    show d'.bv ≠ σ3.curThread; exact hdc3
  set σb := rhoT σa t.bv sc.bv xT yS n with hσb
  have eρa : σb = Notif.stsAct (Notif.updK (rhoT σ3 t.bv sc.bv xT yS n) d'.bv (.tcb x5)) d'.bv := by
    rw [hσb, hσa, stsAct_ne (show d'.bv ≠ (Notif.updK σ3 d'.bv (.tcb x5)).curThread from hdc3),
      rhoT_updK _ (Ne.symm htd') hdsc, stsAct_ne hdcρ]
  have hkd3ρ : (rhoT σ3 t.bv sc.bv xT yS n).kheap d'.bv = some (.tcb x3) := by
    rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd3
  have Fr5 : CFr e.bv d'.bv σ0 σb := by rw [eρa]; exact Fr3.trans (CFr.stsRun hkd3ρ hrb3)
  have IK5 : IK d'.bv σ0 σb := by
    rw [eρa]; exact (IK3.trans (IK.updSelf (y := x5) hkd3ρ rfl)).trans (IK.sts _ _ _)
  have SK5 : SKeep σ0 σb := by
    rw [eρa]
    exact (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3ρ, by cases h; rfl⟩)
      (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hkda : σa.kheap d'.bv = some (.tcb x5) := by rw [hσa, stsAct_kheap]; simp
  have hksca : σa.kheap sc.bv = some (.schedContext yS n) := by
    rw [hσa, stsAct_kheap]; simp only [updK_kheap, Function.update_of_ne (Ne.symm hdsc)]; exact hksc3
  have hkta : σb.kheap t.bv = some (.tcb xT) := rhoT_kt hst
  have hkwa : σb.kheap w.bv = some (.reply xr3) := by
    rw [hσb, rhoT_kh hwt hws, hσa, stsAct_kheap]; simp only [updK_kheap, Function.update_of_ne hwd]; exact hkr3
  -- the push from the shadow is the push from the state
  have hpb : pushSt σa t.bv w.bv xr3 xt = pushSt σb t.bv w.bv xr3 xT := by
    have e1 : σb = Notif.updK σa t.bv (.tcb xT) := by
      rw [hσb, rhoT_eq]
      show ({ σa with kheap := Function.update (Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT))) sc.bv (some (Fl4Spec.KernelObject.schedContext yS n)) } : Fl4Spec.State Unit) = { σa with kheap := Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT)) }
      have e2 : Function.update (Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT))) sc.bv
          (some (Fl4Spec.KernelObject.schedContext yS n)) = Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT)) := by
        have e3 : (some (Fl4Spec.KernelObject.schedContext yS n) : Option Fl4Spec.KernelObject) =
            Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT)) sc.bv := by
          rw [Function.update_of_ne (Ne.symm hst)]; exact hksca.symm
        rw [e3, Function.update_eq_self]
      rw [e2]
    rw [e1]
    unfold pushSt
    show Notif.stsAct ({ σa with kheap := Function.update (Function.update σa.kheap w.bv (some (Fl4Spec.KernelObject.reply { xr3 with replyTcb := some t.bv }))) t.bv (some (Fl4Spec.KernelObject.tcb { xt with tcbState := .blockedOnReply w.bv })) } : Fl4Spec.State Unit) t.bv = Notif.stsAct ({ σa with kheap := Function.update (Function.update (Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT))) w.bv (some (Fl4Spec.KernelObject.reply { xr3 with replyTcb := some t.bv }))) t.bv (some (Fl4Spec.KernelObject.tcb { xT with tcbState := .blockedOnReply w.bv })) } : Fl4Spec.State Unit) t.bv
    rw [Function.update_comm (f := σa.kheap) (Ne.symm hwt), Function.update_idem]
    all_goals rfl
  have hIR0 := IpcRel.ofSRN hR5 hS5
  set σ' := pushSt σb t.bv w.bv xr3 xT with hσ'
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 σ' := by
    rw [← hpb, ← heq5]; exact hIR0
  -- the scheduler facts
  have hrib : RelIfBound σb d'.bv :=
    Ipc.RelIfBound.of_keep (J0.inv.rd d'.bv xd hkd0 (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have hnqD0 : NotQueued σ0 d'.bv := ⟨hnqD.1, hnqD.2⟩
  have I5 : Inv σb := ((J0.inv.toBut d'.bv).ik hnqD0 IK5).1.inv fun _ _ _ => hrib
  have hnqTb : ∀ dm p, t.bv ∉ σb.readyQueues dm p := by rw [IK5.2.1]; exact hnqT.1
  have hnrTb : t.bv ∉ σb.releaseQueue := by rw [IK5.2.2.1]; exact hnqT.2
  have I5' : Inv σ' := ps_inv hkta hkwa hwt I5 hnqTb hnrTb
  have hscA : ∀ p y0 n0, σb.kheap p = some (.schedContext y0 n0) → y0.scTcb = some t.bv →
      Fl4Spec.scActive y0 = true := by
    intro p y0 n0 hp hyt
    by_cases hps : p = sc.bv
    · subst hps; rw [hσb, rhoT_ksc] at hp; cases hp; exact hya
    · have hp0 : σ0.kheap p = some (.schedContext y0 n0) := SK5.2.2.2 _ _ _ hp
      obtain ⟨q0, hqC, eq⟩ := J0.obj.sc p y0 n0 hp0
      subst eq
      obtain ⟨Tr, Cq, hJ⟩ := J0.jpl
      have hq0 := J0.c0 q0 hqC
      have hqS : q0 ∈ P1.Heap.scs H := ⟨_, (hJ.sc q0 y0 n0 hq0 hp0).2⟩
      have hS0' := J0.xtop.fin.1.1.1
      obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS0' J0.blk.2.2.1 J0.tcbs_eq.1.symm hqC hqS hq0 hp0 hyt
      have hkt0 : σ0.kheap t.bv = some (.tcb xT) := by rw [hσ0r]; exact rhoT_kt hst
      rw [hkt0] at hku; cases hku
      exact absurd (Option.some.inj (hxs.symm.trans hxsc)) hps
  have B5' : BlockedScActive σ' := ps_bsa hkta hkwa hwt hscA (Fr5.bsa J0.bsa)
  have htcb : t.bv ≠ σb.curThread := by rw [Fr5.sk.ct]; exact htc
  have act5 : σ'.schedulerAction = σ.schedulerAction := by
    show (pushSt σb t.bv w.bv xr3 xT).schedulerAction = _
    unfold pushSt
    rw [stsAct_ne (σ := Notif.updK (Notif.updK σb w.bv (.reply { xr3 with replyTcb := some t.bv })) t.bv
      (.tcb { xT with tcbState := .blockedOnReply w.bv })) htcb]
    show σb.schedulerAction = σ.schedulerAction
    rw [eρa, stsAct_ne hdcρ]; exact hact3
  have hidT : σb.idleThread ≠ t.bv := by rw [Fr5.sk.idle]; exact fun e0 => hit e0.symm
  have hsched : ∀ u, Fl4Spec.schedulable u σ0 = true → Fl4Spec.schedulable u σ' = true := by
    intro u hu
    have hub := Fr5.sched hu
    obtain ⟨xu, scp, yu, nu, hku, hscu, hrunu, hkyu, hacu, hnru⟩ := schedulable_inv hub
    have hut : u ≠ t.bv := by rintro rfl; rw [hkta] at hku; cases hku; rw [hrs] at hrunu; cases hrunu
    have huw : u ≠ w.bv := by rintro rfl; rw [hkwa] at hku; cases hku
    exact schedulable_of (by rw [ps_ko hut huw]; exact hku) hscu hrunu
      ((ps_oth hkta hkwa hwt (fun _ h => by cases h) (fun _ h => by cases h)).2 hkyu) hacu (by rw [ps_rel]; exact hnru)
  have hAI5 : ActIdle σ' :=
    ⟨fun u hu => hsched u (J0.act.1 u (by rw [act5] at hu; exact hu)), ps_idleOK hkta hkwa hwt hidT (Fr5.idleOK J0.act.2)⟩
  have hcur5 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases J0.cur with e0 | hC
    · left; rw [act5]; exact e0
    · right
      have hCb := Fr5.curInv hC
      obtain ⟨xc, hkc, hcs, hnb'⟩ := hCb.tcb
      have hcw : σb.curThread ≠ w.bv := fun e0 => by rw [e0, hkwa] at hkc; cases hkc
      have F := (ps_skD (σ := σb) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xT))
      obtain ⟨yc, nc, hkyc⟩ := hCb.sc
      refine ⟨⟨xc, by rw [F.ct, ps_ko (Ne.symm htcb) hcw]; exact hkc, by rw [F.csc]; exact hcs, hnb'⟩,
        ⟨yc, nc, by rw [F.csc]; exact (ps_oth hkta hkwa hwt (fun _ h => by cases h) (fun _ h => by cases h)).2 hkyc⟩,
        fun hne y2 n2 hy => ?_, fun hm => ?_⟩
      · rw [F.csc, F.isc] at hne; rw [F.csc] at hy
        exact hCb.active hne y2 n2 ((ps_oth hkta hkwa hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hy)
      · rw [F.ct, ps_rel] at hm; exact hCb.notRel hm
  have hrun5 : CurRunM σ' := by
    have hRb : CurRunM σb := J0.curRun.of_cn Fr5.curRunW (Or.inr (by rw [eρa, stsAct_ne hdcρ]; exact hact3))
    refine hRb.of_cn (fun hW => ?_) (Or.inr ?_)
    · have F := (ps_skD (σ := σb) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xT))
      rcases hW with hW | e0
      · left
        intro y1 hy1
        rw [F.ct] at hy1
        have hcw : σb.curThread ≠ w.bv := fun e0 => by rw [e0, ps_kw hwt] at hy1; cases hy1
        rw [ps_ko (Ne.symm htcb) hcw] at hy1
        exact hW y1 hy1
      · right; rw [F.ct, F.idle]; exact e0
    · rw [act5, eρa, stsAct_ne hdcρ]; exact hact3.symm
  -- the footprints from the base
  have hSσ := J.xtop.fin.1.1.1
  obtain ⟨Qs, Rs, hcs, hsps⟩ := hSσ.lists
  obtain ⟨ys, ns, hkys, hys⟩ := hsps.scs sc hsc
  rw [hky] at hkys; cases hkys
  have hal8 : P1.Aligned (scW sc 8#u64) := (hys.hdr (K := 8#u64) (by simp) (by simp)).1
  have hta := hP.tcb t ht
  have hw0 : P1.WritesIn st s s0 (fun b => (((b = tFaultA t ∨ b = tFw0A t) ∨ b = tFw1A t) ∨ b = tFw2A t) ∨
      b = scW sc 8#u64) :=
    ((((writesIn_wr (st := st) (s := s) (v := fl4_abi.consts.fault.Timeout) (a_fault hta).1).trans
      (writesIn_wr (v := b) (a_fw0 hta).1)).trans (writesIn_wr (v := 0#u64) (a_fw1 hta).1)).trans
      (writesIn_wr (v := 0#u64) (a_fw2 hta).1)).trans (writesIn_wr (v := 0#u64) hal8)
  have hz7 : SzKeepC Z.C σ σf := SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := xt) (fun q hq => hkf q hq) hkt)
  have hWs5 : P1.WritesIn st s s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hW7.trans1 (hW5'.mono fun b hb => cnW_back hW7.1 hz7 hb)
  have hsw : SW Z.C σ (scW sc 8#u64) := sw_hdr hSσ hsc (K := 8#u64) (by simp) (by simp) (by decide)
  have hsub0 : ∀ b0, ((((b0 = tFaultA t ∨ b0 = tFw0A t) ∨ b0 = tFw1A t) ∨ b0 = tFw2A t) ∨ b0 = scW sc 8#u64) →
      CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b0 := by
    intro b0 hb0
    rcases hb0 with (((h | h) | h) | h) | h <;> subst h
    · exact Or.inl (Or.inr ⟨t, ht, 3376, by omega, by omega, by omega, by omega, by omega, val_fault hta⟩)
    · exact Or.inl (Or.inr ⟨t, ht, 3384, by omega, by omega, by omega, by omega, by omega, val_fw0 hta⟩)
    · exact Or.inl (Or.inr ⟨t, ht, 3392, by omega, by omega, by omega, by omega, by omega, val_fw1 hta⟩)
    · exact Or.inl (Or.inr ⟨t, ht, 3400, by omega, by omega, by omega, by omega, by omega, val_fw2 hta⟩)
    · exact Or.inl (Or.inl (Or.inr (Or.inr hsw)))
  have hz0 : SzKeepC Z.C σ0 σ := by
    intro p _ y0 m hp
    by_cases hps : p = sc
    · subst hps; rw [hky] at hp; cases hp; exact ⟨yS, by rw [hσ0r]; exact rhoT_ksc⟩
    · have hps' : p.bv ≠ sc.bv := fun e0 => hps (P1.eq_of_bv e0)
      have hpt : p.bv ≠ t.bv := fun e0 => by rw [e0, hkx] at hp; cases hp
      exact ⟨y0, by rw [hk0 _ hpt hps']; exact hp⟩
  have hW05 : P1.WritesIn st s0 s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s0 σ0) :=
    (writesIn_rebase hWs5 hw0 hsub0).mono fun b0 hb0 => CnW.back (s := s0) (s' := s) hw0.1.symm hz0 hb0
  have hfs5 := footW_trans (footW_of (W := fun _ => False) hfoot7) hfoot
  have hsubK : ∀ b0, ((((b0 = tFaultA t ∨ b0 = tFw0A t) ∨ b0 = tFw1A t) ∨ b0 = tFw2A t) ∨ b0 = scW sc 8#u64) →
      P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s b0 ∨ False := by
    intro b0 hb0
    rcases hb0 with (((h | h) | h) | h) | h <;> subst h
    · exact Or.inl (Or.inl ⟨t, htH, 3376#u64, by simp, by simp, by simp, by simp, rfl⟩)
    · exact Or.inl (Or.inl ⟨t, htH, 3384#u64, by simp, by simp, by simp, by simp, rfl⟩)
    · exact Or.inl (Or.inl ⟨t, htH, 3392#u64, by simp, by simp, by simp, by simp, rfl⟩)
    · exact Or.inl (Or.inl ⟨t, htH, 3400#u64, by simp, by simp, by simp, by simp, rfl⟩)
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc1, scW8_inSC J.blk hsc1⟩))))
  have hfoot05 : P1.WritesIn st s0 s5 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s0) :=
    (writesIn_rebase hfs5 hw0 hsubK).mono fun b0 hb0 => hb0.elim (P1.KW.ksb hw0.1.symm) False.elim
  have hI0 := J0.xtop.irelK J0.ks J0.buf
  have hF : IFrame (L := L) Z.th s0 s5 := IRel.iframe_of hI0 hW05 fun b0 hb0 => CnW.oobj hI0.2.2.1 hb0
  have htDd := J0.not_dead_of_st hdT hkd0 (by rw [hstd]; simp [tsCode])
  have hRR : ∀ q' ∈ Z.R, ∀ xr, σ0.kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem s0 (rNextA q') = 0#u64 ∧ L.mem s0 (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds _ Ac Lst D s0 _ σ0 J0 q' hq'' xr d'.bv xd hx'
      hxt' hkd0 (by rw [hstd]; rfl)
  have hcD : ∀ q0 ∈ D, q0.bv ≠ t.bv := fun q0 hq0 e0 => htD (by rw [← P1.eq_of_bv e0]; exact hq0)
  have hwD : ∀ q0 ∈ D, q0.bv ≠ w.bv := fun q0 hq0 e0 => by
    have hqw : q0 = w := P1.eq_of_bv e0
    rw [hqw] at hq0
    have d1 : L.mem s (Endp.rTcbA w) = 0#u64 := (J.jcov.dead w hq0).2.2.2.1 hwH
    obtain ⟨xr', hkr', hxr'⟩ := J.xtop.irelK J.ks J.buf |>.1.toE.reply w hwR
    rw [hkrσ] at hkr'; cases hkr'
    rw [hb', d1, optRef_zero] at hxr'
    cases hxr'
  have hkq : ∀ q0 ∈ D, σ'.kheap q0.bv = σb.kheap q0.bv := fun q0 hq0 => ps_ko (hcD q0 hq0) (hwD q0 hq0)
  have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
      (σ'.kheap q = some o ↔ σb.kheap q = some o) := fun h1 h2 => ps_oth hkta hkwa hwt h1 h2
  obtain ⟨V', J5⟩ := J0.wake_postGR hIR hF hW05 hblk hfoot05 (DWFr.ofCFr Fr5) ps_skD
    (ps_ksub hkta hkwa hwt) (ps_szKeep hkta hkwa hwt) (ps_ykeep hkta hkwa hwt) (ps_mcpKeep hkta hkwa hwt)
    (ps_bufKeep hkta hkwa hwt) (fun d _ h => ps_recvB hkta hkwa hwt h) (ps_ksz hkta hkwa hwt)
    (ps_kback hkta hkwa hwt) (ps_ipcFr hkta hkwa hwt) (ps_ck hkta hkwa hwt) (fun d _ h => ps_free hkta hkwa hwt h)
    (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
    I5' B5' hAI5 hcur5 hrun5 (ps_own hkta hkwa hwt ((DWFr.ofCFr Fr5).own ⟨d', hdT, rfl⟩ J0.own))
    (ps_off hkta hkwa hwt ((DWFr.ofCFr Fr5).off J0.off)) (ps_nsc hkta hkwa hwt ((DWFr.ofCFr Fr5).nsc J0.nsc))
    (ps_isorted hkta hkwa hwt ((DWFr.ofCFr Fr5).isorted J0.isorted)) hRR htDd
  -- the tail
  have hk5 : σ'.kheap d'.bv = some (.tcb x5) := by
    rw [ps_ko (Ne.symm htd') (Ne.symm hwd), hσb, rhoT_kh (Ne.symm htd') hdsc]; exact hkda
  have hnr5 : d'.bv ∉ σ'.releaseQueue := by rw [ps_rel, SK5.1]; exact hnqD.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → σ'.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hya' : σb.kheap p = some (.schedContext y n) :=
      (ho (fun _ h => by cases h) (fun _ h => by cases h)).1 hy
    have hy0 := SK5.2.2.2 p y n hya'
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := J0.inv.back _ _ _ hkd0 hp'
    rw [hy0] at hky'; cases hky'
    exact J0.bsa.tcb p y n d'.bv xd hy0 hyt hkd0 (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ σ'.idleThread := by
    rw [(ps_skD (σ := σb) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xT)).idle, Fr5.sk.idle]
    exact hid
  have htc5 : d'.bv ≠ σ'.curThread := by
    rw [(ps_skD (σ := σb) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xT)).ct, Fr5.sk.ct]; exact hdc
  have hspec := sendIpc_faultPush_eq (don := false) hk hkd hde hstd true badge.bv g gr hg e2 hU hkt3 hkd3 hpush hkd4
    (by rw [hft]; simp) (t := t.bv)
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7', a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  refine ⟨((), σ7), ?_, ⟨_, _, _, _, _, _, J7⟩⟩
  rw [hspec, heq5, hpb]
  show ((), σ7) ∈ (Endp.specWakeTailE d'.bv σ').1
  rw [h7]; exact Set.mem_singleton _


set_option maxHeartbeats 64000000 in
/-- **`Running` or `Restart` of an `Inactive` thread other than the current
one, then `handle_timeout` sending its timeout fault to a receiver waiting on
its timeout handler's endpoint, at `J`** (XTopJointSendBlockG's
`JAtZ.runTmoJ` for an endpoint with receivers: `set_thread_state`, the
handler cap, `set_fault`, then `JAtZ.sendTmoRecvIJ` (the sender left
`Inactive`) or `JAtZ.sendTmoRecvPJ` (the reply pushed); `hcr`: the current
thread runnable, so not the receiver). -/
theorem JAtZ.runTmoRecvJ (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hcr : ∃ xc, σ.kheap σ.curThread = some (.tcb xc) ∧ Fl4Spec.runnable xc.tcbState = true)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (htD : t ∉ D)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrs : x.tcbState = .inactive)
    (htc : t.bv ≠ σ.curThread) {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : x.tcbTimeoutHandler = .endpointCap p bd r)
    (hcb : ∀ xe, σ.kheap p = some (.endpoint xe) → ¬ Endp.CanBlock false xe)
    (ts : Fl4Spec.ThreadState) (hrun : Fl4Spec.runnable ts = true) (hts : tsCode ts < 3) (v : U64)
    (hv : v.val = tsCode ts)
    (hB : sched.set_thread_state st s t v ⦃ s' => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H
      (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s' ⦄) :
    sched.set_thread_state st s t v ⦃ s6 =>
      XTopAt (L := L) AR Z s6 a (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ∧
      IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s6
        (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv) ∧
      ∀ b : U64, faults.handle_timeout st arI s6 a t (error.Fault.Timeout b) ⦃ res => ∃ z ∈
        (Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout b.bv)
          (stsAct (updK σ t.bv (.tcb { x with tcbState := ts })) t.bv)).1,
        JAt (L := L) arI AR res.1 res.2 z.2 ⦄ ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have hta := hP0.e.tcb t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP0.e.tcb
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb t ht
  rw [hk] at hk0; cases hk0
  have hst : (L.mem s (tStA t)).val = tsCode x.tcbState := hTR.st
  have hq := IpcRel.not_ep_queued hI.1 (t := t) ⟨by rw [hst, hrs]; decide, by rw [hst, hrs]; decide⟩
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hSR := IpcRel.toSRN hI.1 hI.2
  have hnq : NotQueued σ t.bv := J.inv.notQueued hk (by rw [hrs]; rfl)
  obtain ⟨y0, n0, hky0, hyt⟩ := J.inv.back t.bv x sc.bv hk hxsc
  rw [hky] at hky0; cases hky0
  have hidt : σ.idleThread ≠ t.bv := by
    intro e
    obtain ⟨y1, h1, -, h3, -⟩ := J.act.2
    rw [e, hk] at h1; cases h1; rw [hrs] at h3; cases h3
  -- the handler cap at the start, its endpoint
  obtain ⟨⟨G0, hB0⟩, -⟩ := hI.2.1
  have hth0 : Z.th t = some .tcb := hB0.tcbT hk
  obtain ⟨xh, cv, hkh, hcv, hca⟩ := hB0.2.1.1.timeoutCap hth0
  rw [hk] at hkh; cases hkh
  have habs := hca.2
  rw [hth] at habs
  obtain ⟨ptr, bdg, sd, rv, g, gr, rfl⟩ : ∃ ptr bdg sd rv g gr, cv = .Endpoint ptr bdg sd rv g gr := by
    cases cv <;> simp [absCap] at habs; exact ⟨_, _, _, _, _, _, rfl⟩
  simp only [absCap, Fl4Spec.Cap.endpointCap.injEq] at habs
  obtain ⟨hp, hbd, hr⟩ := habs
  subst hp hbd hr
  have hAS : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex 4) := ⟨t, rfl, Or.inr ⟨hth0, 4, by decide, rfl⟩⟩
  have hcv' : capAt (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 4)) = ok (.Endpoint ptr bdg sd rv g gr) := by
    rw [tcbSlot4_eq]; exact hcv
  have hpE : ptr ∈ Z.E := J.slotE hAS hcv'
  obtain ⟨xe, hke, -⟩ := hI.1.ep ptr hpE
  have hcbe : ¬ Endp.CanBlock false xe := hcb xe hke
  have hpt : ptr.bv ≠ t.bv := fun e => by rw [e, hk] at hke; cases hke
  have hps : ptr.bv ≠ sc.bv := fun e => by rw [e, hky] at hke; cases hke
  -- the endpoint covered by the handler cap
  have hHe : H ptr = some .ep := J.zH.2.1 ptr hpE
  have hfit := J.kern.heap.fits ptr _ hHe
  simp only [P1.HKind.bits] at hfit
  have hcov := J.cover_cap (P1.WritesIn.refl s _) hAS.isSlot hcv' (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
    (range_ep ptr bdg sd rv g gr hfit) fun k hk' => by
      rw [hHe] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  -- `set_thread_state`
  refine WP.spec_mono (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP0.e s σ hI.1.toE hSR ht
    hk hq (by rw [hrs]; decide) ts hts v hv) (set_thread_state_sfoot hS ht _)) hB) ?_
  rintro s6 ⟨⟨⟨hR6, hS6r⟩, hw6⟩, hblk6, hfoot6⟩
  have hX6 := IpcRel.ofSRN hR6 hS6r
  set x6 : Fl4Spec.Tcb := { x with tcbState := ts } with hx6
  set σ1 := updK σ t.bv (.tcb x6) with hσ1
  set σ6 := stsAct σ1 t.bv with hσ6
  have hrec : σ6 = { σ1 with schedulerAction := σ6.schedulerAction } := stsAct_rec σ1 t.bv
  have hk1 : σ1.kheap t.bv = some (.tcb x6) := by simp [hσ1, updK]
  have hk6 : σ6.kheap t.bv = some (.tcb x6) := by rw [hσ6, stsAct_kheap]; exact hk1
  have hkp : ∀ q, q ≠ t.bv → σ6.kheap q = σ.kheap q := by
    intro q hq'; rw [hσ6, stsAct_kheap, hσ1]; simp [updK, hq']
  have e61 : σ6 = σ1 := by
    rw [hσ6]; unfold Notif.stsAct; rw [if_neg]; rintro ⟨h, -⟩; exact htc h
  have e_ct : σ6.curThread = σ.curThread := by rw [hrec]; rfl
  have e_isc : σ6.idleSc = σ.idleSc := by rw [hrec]; rfl
  have hW : P1.WritesIn st s s6 (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_sfoot (P1.WritesIn.refl _ _) hw6
  have hfx : IpcFree x.tcbState := by
    rw [hrs]; exact ⟨rfl, rfl, fun _ e => by cases e⟩
  have hK : ScTKw (fun q => q = t.bv) σ σ6 := by
    refine ⟨fun q => ?_, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl,
      by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, by rw [hrec]; rfl, e_ct, e_isc⟩
    by_cases hq' : q = t.bv
    · subst hq'; rw [hk, hk6]
      show TKObj _ _ _
      exact Or.inr (Or.inl ⟨x, x6, rfl, rfl, rfl, Or.inr ⟨rfl, hfx, tsLow_free hts⟩⟩)
    · rw [hkp q hq']; exact OTK.refl _ _
  have hX' : XTopAt (L := L) AR Z s6 a σ6 := xtop_sc_step J.xtop hP0 J.nk hW hK hX6.2.2.1 hX6.1.toN id
  have hks6 : L.ksb s6 = L.ksb s := hW.1
  have hbuf6 : BufWordRel Z.T (L.mem s6) σ6 := J.sc_buf hW hK
  have hI6 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s6 σ6 := by
    have h := hX'.irelK (by rw [hks6]; exact J.ks) hbuf6
    have e : σ6.archState = σ.archState := hK.arch
    rw [e] at h; exact h
  refine ⟨hX', hI6, fun b => ?_⟩
  -- the FL4 step from the start to `s6` (`CnStep`)
  have hC1 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ s6 σ6 :=
    ⟨hw6.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot hb)), SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := x6)
      hkp hk6)⟩
  -- `handle_timeout`: the handler cap at `s6`
  obtain ⟨⟨G6, hB6⟩, -⟩ := hI6.2.1
  obtain ⟨xh6, cv6, hkh6, hcv6, hca6⟩ := hB6.2.1.1.timeoutCap (hB6.tcbT hk6)
  rw [hk6] at hkh6; cases hkh6
  have habs6 := hca6.2
  rw [show x6.tcbTimeoutHandler = x.tcbTimeoutHandler from rfl, hth] at habs6
  unfold faults.handle_timeout
  rw [tcb_slot_timeout]
  apply ok_bind_spec
  rw [slot_cap_eq, hcv6]
  apply ok_bind_spec
  cases cv6
  case Endpoint ptr' bdg' sd' rv' g' gr' =>
    simp only [absCap, Fl4Spec.Cap.endpointCap.injEq] at habs6
    obtain ⟨hp', hbd', hr'⟩ := habs6
    obtain rfl : ptr = ptr' := (P1.eq_of_bv hp').symm
    obtain rfl : bdg = bdg' := (P1.eq_of_bv hbd').symm
    have hg : g' = g := by have := congrArg (fun R => decide (Fl4Spec.Rights.allowGrant ∈ R)) hr'; simpa [rights_grant] using this
    have hgr : gr' = gr := by
      have := congrArg (fun R => decide (Fl4Spec.Rights.allowGrantReply ∈ R)) hr'; simpa [rights_grantReply] using this
    obtain rfl : g = g' := hg.symm
    obtain rfl : gr = gr' := hgr.symm
    refine WP.spec_bind (Pₘ := fun r : Bool × S × A => ∃ z ∈ (Fl4Spec.handleTimeout (Z := Unit) t.bv (.timeout b.bv) σ6).1,
      JAt (L := L) arI AR r.2.1 r.2.2 z.2) ?_ ?_
    swap
    · rintro ⟨b0, s2, a2⟩ hr0
      exact (WP.spec_ok _).2 hr0
    unfold faults.send_fault_ipc
    dsimp only
    -- `set_fault`
    set x2 : Fl4Spec.Tcb := { x6 with tcbFault := some (.timeout b.bv) } with hx2
    set σf := updK σ6 t.bv (.tcb x2) with hσf
    refine WP.spec_bind (WP.spec_and (WP.spec_and (set_fault_timeout_top hP0 hI6 ht hk6 b)
      (set_fault_timeout_eq s6 t b)) (WP.spec_and (P1.faults.set_fault.blk (U := ∅) s6 t (error.Fault.Timeout b)
        (t0 := t) hblk6 htH (fun _ h => by simp at h) ?hcb6)
        (P1.faults.set_fault.kw (Cs := Cs) (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
          (Es := P1.EH H) s6 t (error.Fault.Timeout b) hTH htH))) ?_
    case hcb6 =>
      have hS6 : SchedRel st Z.N Z.T Z.C Z.c s6 σ6 := hX6.2.2.1
      obtain ⟨Q, R0, hcq, hs⟩ := hS6.lists
      obtain ⟨x7, hk7, hTR7⟩ := hI6.1.tcb t ht
      rw [hk6] at hk7; cases hk7
      have hv7 : (L.mem s6 (tStA t)).val = tsCode ts := hTR7.st
      have hrr : L.mem s6 (P1.stA t) = sched.TS_RUNNING ∨ L.mem s6 (P1.stA t) = sched.TS_RESTART := by
        have hrr' : ts = .running ∨ ts = .restart := by
          cases ts with
          | running => exact Or.inl rfl
          | restart => exact Or.inr rfl
          | _ => simp [tsCode, Fl4Spec.runnable] at hts hrun
        rcases hrr' with e | e
        · left; apply UScalar.eq_of_val_eq; rw [P1.stA_eq, ← tStA_eq, hv7, e]; unfold sched.TS_RUNNING; rfl
        · right; apply UScalar.eq_of_val_eq; rw [P1.stA_eq, ← tStA_eq, hv7, e]; unfold sched.TS_RESTART; rfl
      have hrq6 : σ6.readyQueues = σ.readyQueues := by rw [hrec]; rfl
      have hrl6 : σ6.releaseQueue = σ.releaseQueue := by rw [hrec]; rfl
      have hac6 : σ6.schedulerAction = σ.schedulerAction := by rw [e61]; rfl
      have hid6 : σ6.idleThread = σ.idleThread := by rw [hrec]; rfl
      obtain ⟨xt6, hkt6, -, -, hsct6, -⟩ := hs.tcb t ht
      rw [hk6] at hkt6; cases hkt6
      have hst6 : L.mem s6 (scA t) = sc := P1.eq_of_bv (Notif.optRef_some (hsct6.symm.trans hxsc)).2
      have h06 : L.mem s6 (scA t) ≠ 0#u64 := (Notif.optRef_some (hsct6.symm.trans hxsc)).1
      have hky6 : σ6.kheap sc.bv = some (.schedContext y n) := by
        rw [hkp _ (fun e => by rw [e, hk] at hky; cases hky)]; exact hky
      obtain ⟨y', n', hky', hy'⟩ := hs.scs sc hsc
      rw [hky6] at hky'; cases hky'
      have hmx : (L.rmax s6 (L.mem s6 (scA t))).val ≠ 0 := by rw [hst6]; exact hy'.rmax_ne hya
      refine ⟨htH, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rcases hrr with h | h <;> rw [h]
        · exact P1.not_blocked_running
        · exact P1.not_blocked_restart
      · rcases hrr with h | h <;> rw [h]
        · exact P1.running_ne.1
        · exact P1.restart_ne.1
      · by_contra hq'
        have hm := (hcq.queued t ht).1 hq'
        exact hnq.1 0 _ (by rw [← hrq6, hs.rq _ (hcq.prio t ht), mem_map_bv]; exact hm)
      · by_contra hq'
        have hm := (hcq.released t ht).1 hq'
        exact hnq.2 (by rw [← hrl6, hs.rel, mem_map_bv]; exact hm)
      · refine actionW_ne_of hS6 ht ?_
        rw [hac6]; intro e
        obtain ⟨x', -, -, -, h1, -, h3, -⟩ := schedulable_inv (J.act.1 _ e)
        rw [hk] at h1; cases h1; rw [hrs] at h3; cases h3
      · intro h
        have ei : L.idleW s6 = nodeW st s6 Z.c layout.node.IDLE_THREAD := by
          unfold P1.LawfulStore.idleW nodeW; rw [hcq.cur]
        exact hidt (by rw [← hid6, hs.idleTh, ← ei, h])
      · intro hbd
        obtain ⟨⟨Q', R', h0⟩, hBd, hXi, hSc, hSg⟩ := hblk6
        obtain ⟨hiS, -, -⟩ := hXi.2.2.bound _ htH hbd
        exact (hSc.act _ hiS).2 (fun e => hmx (by rw [e]; rfl))
    rintro s7 ⟨⟨⟨hsp7, hI7⟩, hs7⟩, ⟨hblk7, -, hcb7⟩, hfoot7⟩
    have hC2 : Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s6 σ6 s7 σf := by
      refine ⟨?_, SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := x2) (fun q hq' => by simp [hσf, updK, hq']) (by simp [hσf, updK]))⟩
      subst hs7
      have w := (((writesIn_wr (st := st) (s := s6) (v := fl4_abi.consts.fault.Timeout) (a_fault hta).1).trans
        (writesIn_wr (v := b) (a_fw0 hta).1)).trans (writesIn_wr (v := 0#u64) (a_fw1 hta).1)).trans
        (writesIn_wr (v := 0#u64) (a_fw2 hta).1)
      refine w.mono fun w0 hw0 => ?_
      have k : ∃ K : Nat, 256 ≤ K ∧ K < 4096 ∧ K ≠ 3440 ∧ K ≠ 3472 ∧ (K ≠ 3512 ∧ K ≠ 3664) ∧ w0.val = t.val + K := by
        rcases hw0 with ((h | h) | h) | h <;> subst h
        · exact ⟨3376, by omega, by omega, by omega, by omega, by omega, val_fault hta⟩
        · exact ⟨3384, by omega, by omega, by omega, by omega, by omega, val_fw0 hta⟩
        · exact ⟨3392, by omega, by omega, by omega, by omega, by omega, val_fw1 hta⟩
        · exact ⟨3400, by omega, by omega, by omega, by omega, by omega, val_fw2 hta⟩
      obtain ⟨K, k1, k2, k3, k4, k5, k6⟩ := k
      exact Or.inl (Or.inr ⟨t, ht, K, k1, k2, k3, k4, k5, k6⟩)
    have hW7 : P1.WritesIn st s s7 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := (hC1.trans hC2).1
    have hfoot7' := P1.Foot.trans hfoot6 hfoot7
    have eσf : σf = updK σ t.bv (.tcb { x with tcbState := ts, tcbFault := some (.timeout b.bv) }) := by
      rw [hσf, e61, hσ1]
      show ({ σ with kheap := Function.update (Function.update σ.kheap t.bv (some (.tcb x6))) t.bv (some (.tcb x2)) } :
        Fl4Spec.State Unit) = _
      rw [Function.update_idem]
      rfl
    have hI7' : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s7
        (updK σ t.bv (.tcb { x with tcbState := ts, tcbFault := some (.timeout b.bv) })) := by
      rw [← eσf]; exact hI7
    -- the receivers waiting on the endpoint
    cases xe with
    | idleEP => exact absurd trivial hcbe
    | sendEP l => exact absurd rfl hcbe
    | recvEP l =>
      obtain ⟨-, xs, hxs0, hq, hQ, -⟩ := hI.1.toE.at_ep hpE hke
      obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
      simp only [List.map_cons] at hq
      subst hq
      have hdT : d' ∈ Z.T := hQ.mem d' (by simp)
      have hth6 : x6.tcbTimeoutHandler = .endpointCap ptr.bv bdg.bv (rightsOf sd rv g gr) := hth
      have fin : ∀ z : Unit × Fl4Spec.State Unit, z ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv g gr false t.bv ptr.bv
          (updK σ t.bv (.tcb { x with tcbState := ts, tcbFault := some (.timeout b.bv) }))).1 →
          z ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv
            (decide (Fl4Spec.Rights.allowGrant ∈ rightsOf sd rv g gr))
            (decide (Fl4Spec.Rights.allowGrantReply ∈ rightsOf sd rv g gr)) false t.bv ptr.bv
            (updK σ6 t.bv (.tcb { x6 with tcbFault := some (.timeout b.bv) }))).1 := by
        intro z hz
        rw [rights_grant, rights_grantReply]
        show z ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv g gr false t.bv ptr.bv σf).1
        rw [eσf]; exact hz
      by_cases hpush : (g = true ∨ gr = true) ∧ ∀ xd, σ.kheap d'.bv = some (.tcb xd) →
          ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none
      · refine WP.spec_bind (J.sendTmoRecvPJ hAT hmax htu hcr ht hk hrs htc hsc hxsc hky b hrun hI7' hblk7 hW7
          hfoot7' hcb7 hpE hke bdg g gr hpush.1 htD hya hpush.2) ?_
        rintro ⟨s', a'⟩ ⟨z, hz, hJ⟩
        exact (WP.spec_ok _).2 ⟨((), z.2), handleTimeout_mem hk6 hth6 _ (fin z hz), hJ⟩
      · have hno : (g = false ∧ gr = false) ∨ ∀ xd, σ.kheap d'.bv = some (.tcb xd) →
            ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none := by
          by_cases hgg : g = true ∨ gr = true
          · right
            intro xd hkd e' rep dd hst
            by_contra hr
            apply hpush
            refine ⟨hgg, fun xd' hkd' e'' rep' dd' hst' => ?_⟩
            rw [hkd] at hkd'; cases hkd'
            rw [hst] at hst'; cases hst'; exact hr
          · left
            have h1 : g ≠ true := fun h => hgg (Or.inl h)
            have h2 : gr ≠ true := fun h => hgg (Or.inr h)
            exact ⟨by simpa using h1, by simpa using h2⟩
        refine WP.spec_bind (J.sendTmoRecvIJ hAT hmax htu hcr ht hk hrs htc hsc hxsc hky b hrun hI7' hblk7 hW7
          hfoot7' hcb7 hpE hke bdg g gr hno) ?_
        rintro ⟨s', a'⟩ ⟨z, hz, hJ⟩
        exact (WP.spec_ok _).2 ⟨((), z.2), handleTimeout_mem hk6 hth6 _ (fin z hz), hJ⟩
  all_goals simp [absCap] at habs6


/-- **`RunTmoP` for a timeout handler endpoint with receivers waiting**
(`JAtZ.runTmoRecvJ`): what XTopJointIpcJ's `replyXferJ` / `replyLeafJ` take
for that case (formerly the named premise `JReplyRestHyp`). -/
theorem runTmoP_recv (Z0 : XSets) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    RunTmoP (L := L) arI AR Z0 (fun xe => ¬ Endp.CanBlock false xe) :=
  fun _ _ _ _ _ _ _ a _ hth J hcr _ ht htD _ hk hrs htc _ hsc hxsc _ _ hky hya _ _ _ hthd hcb ts hrun hts v hv hB =>
    JAtZ.runTmoRecvJ hAT hmax (htu a) hcr J ht htD hk hrs htc
      hsc hxsc hky hya hthd hcb ts hrun hts v hv hB
end

end

end Fl4Proofs.P3
