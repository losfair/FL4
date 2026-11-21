/-
P3 (DESIGN.md §9), IPC: **the fault transfer of any fault but a timeout with
an SC** (toward XTopJointRecvIpcLink's `JRecvSendHyp`, KENTRY-PLAN.md item 6
(d4'); l4v `do_fault_transfer`): XTopJointFaultRecv's `xferFaultStepJ` for
every fault EpFaultNone/EpFaultMore relate (`FaultOK`).

* `FW`, `set_mr_rgW`, `set_mrs_lookup_failure_rgW`, `copy_mrs_fault_rgW`,
  `set_mrs_fault_rgW`, `do_ipc_transfer_fault_rgW`: FL4's footprint of the
  fault transfer, uniform in the fault type and in the receive buffer
  (`FW T rw W`: `W` holds the receiver's registers and, for a buffer
  `rw ≠ 0`, its buffer words), a timeout only without an SC.
* `makeFaultMsg_pure`: the spec's fault message leaves the state unchanged
  (a timeout without an SC); `doIpcTransfer_faultN_eq`,
  `doIpcTransfer_faultB_eq`: the spec's outcome `updK (setUm σ um) rcv x'`.
* `xferFaultStepGJ`: `xferFaultStepJ` for a fault `f` with `FaultOK`.
-/
import Fl4Proofs.P3.XTopJointFaultRecv
import Fl4Proofs.P3.EpFaultUs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

/-- A footprint `W` holding the receiver's registers and, for a receive
buffer `rw ≠ 0`, its (aligned) buffer words. -/
def FW (T : Set U64) (rw : U64) (W : U64 → Prop) : Prop :=
  (∀ b, XferRegW T ∅ b → W b) ∧
    (rw ≠ 0#u64 → (∀ i : U64, i.val < 128 → P1.Aligned (Endp.fl4BufA rw i)) ∧ ∀ b, RBufW rw b → W b)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

theorem set_mr_rgW {T : Set U64} (hT : P1.TcbPlaced T) {s0 s : S} {rcv rw i v : U64} (hr : rcv ∈ T)
    {W : U64 → Prop} (hW : FW T rw W) (hi : i.val < 127) (h : P1.WritesIn st s0 s W) :
    msg.set_mr st s rcv rw i v ⦃ r => P1.WritesIn st s0 r.2 W ⦄ := by
  unfold msg.set_mr
  split
  · refine WP.spec_bind (msg.msg_register.lt i) fun rg hrg => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.rg (v := v) (s := s) hT hr hrg) fun s2 w2 => ?_
    simp only [lift, bind_ok, WP.spec_ok]
    exact (h.trans w2).mono fun b hb => hb.elim id (hW.1 b)
  · by_cases hb : (rw != 0#u64) = true
    · have hrw0 : rw ≠ 0#u64 := by simpa using hb
      obtain ⟨hal, hWb⟩ := hW.2 hrw0
      simp only [hb, ↓reduceIte, lift, bind_ok]
      have hv : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := wadd_val i 1 (by omega) _ rfl
      refine WP.spec_bind (Endp.msg.buf_set.spec s rw _ v) ?_
      rintro s1 rfl
      simp only [WP.spec_ok]
      exact (h.trans ((P1.writesIn_wr (hal _ (by omega))).mono fun b hb' => hWb b ⟨_, by omega, hb'⟩)).mono
        fun b hb' => hb'.elim id id
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact h

theorem set_mrs_lookup_failure_rgW {T : Set U64} (hT : P1.TcbPlaced T) {s0 s : S} {rcv rw off : U64}
    {lf : error.LookupFault} (hr : rcv ∈ T) {W : U64 → Prop} (hW : FW T rw W) (hoff : off.val ≤ 3)
    (h : P1.WritesIn st s0 s W) :
    faults.set_mrs_lookup_failure st s rcv rw lf off ⦃ r => P1.WritesIn st s0 r.2 W ⦄ := by
  unfold faults.set_mrs_lookup_failure
  refine WP.spec_bind (P0.error.LookupFault.type_code.p0 lf) fun i _ => ?_
  refine WP.spec_bind (set_mr_rgW (v := i) (i := off) hT hr hW (by omega) h) ?_
  rintro ⟨i1, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · exact (WP.spec_ok _).2 h1
  · try simp only [lift, bind_ok]
    exact set_mr_rgW hT hr hW (by rw [wadd_val off 1 (by omega) _ rfl]; omega) h1
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (set_mr_rgW hT hr hW (by rw [wadd_val off 1 (by omega) _ rfl]; omega) h1) ?_
    rintro ⟨_, s2⟩ h2
    simp only at h2
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    exact set_mr_rgW hT hr hW (by rw [wadd_val off 2 (by omega) _ rfl]; omega) h2
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (set_mr_rgW hT hr hW (by rw [wadd_val off 1 (by omega) _ rfl]; omega) h1) ?_
    rintro ⟨_, s2⟩ h2
    simp only at h2
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    refine WP.spec_bind (set_mr_rgW hT hr hW (by rw [wadd_val off 2 (by omega) _ rfl]; omega) h2) ?_
    rintro ⟨_, s3⟩ h3
    simp only at h3
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    exact set_mr_rgW hT hr hW (by rw [wadd_val off 3 (by omega) _ rfl]; omega) h3

theorem copy_mrs_fault_loop0_rgW {T : Set U64} (hT : P1.TcbPlaced T) {s0 s : S} {snd rcv : U64}
    {sl : Slice U64} {i : Usize} (hr : rcv ∈ T) {W : U64 → Prop} (hW : ∀ b, XferRegW T ∅ b → W b)
    (h : P1.WritesIn st s0 s W) :
    faults.copy_mrs_fault_loop0 st s snd rcv sl i ⦃ r => P1.WritesIn st s0 r.1 W ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_loop0
  apply loop.spec_decr_nat (measure := fun y => sl.val.length - y.2.val)
    (inv := fun y => P1.WritesIn st s0 y.1 W)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold faults.copy_mrs_fault_loop0.body
    dsimp only
    split
    · rename_i hj
      have hj' : j.val < sl.val.length := by simpa using hj
      simp only [lift, bind_ok]
      split
      · refine WP.spec_bind (Slice.index_usize_spec sl j hj') fun rg _ => ?_
        refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 rg hS) fun v _ => ?_
        refine WP.spec_bind (msg.msg_register.lt _) fun i5 hi5 => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.rg (v := v) (s := s1) hT hr hi5) fun s2 w2 => ?_
        step as ⟨j2, hj2⟩
        refine ⟨(h1.trans w2).mono fun b hb => hb.elim id (hW b), ?_⟩
        omega
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem copy_mrs_fault_loop1_rgW {rw : U64} {W : U64 → Prop}
    (hal : ∀ i : U64, i.val < 128 → P1.Aligned (Endp.fl4BufA rw i)) (hWb : ∀ b, RBufW rw b → W b)
    {s0 : S} {snd : U64} {sl : Slice U64} (hn : sl.val.length ≤ 120) (s : S) (i : Usize)
    (h : P1.WritesIn st s0 s W) :
    faults.copy_mrs_fault_loop1 st s snd sl rw i ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_loop1
  apply loop.spec_decr_nat (measure := fun y => sl.val.length - y.2.val)
    (inv := fun y => P1.WritesIn st s0 y.1 W)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold faults.copy_mrs_fault_loop1.body
    dsimp only
    split
    · rename_i hj
      have hj' : j.val < sl.val.length := by simpa using hj
      refine WP.spec_bind (Slice.index_usize_spec sl j hj') fun rg _ => ?_
      refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 rg hS) fun v _ => ?_
      simp only [lift, bind_ok]
      have h3v : (UScalar.cast .U64 j : U64).val = j.val := cast_us j (by omega)
      have hi4 : (core.num.U64.wrapping_add (UScalar.cast .U64 j) 1#u64).val = j.val + 1 := by
        rw [wadd_val _ 1 (by omega) _ rfl, h3v]
      refine WP.spec_bind (Endp.msg.buf_set.spec s1 rw _ v) ?_
      rintro s2 rfl
      step as ⟨j2, hj2⟩
      refine ⟨(h1.trans ((P1.writesIn_wr (hal _ (by omega))).mono fun b hb' => hWb b ⟨_, by omega, hb'⟩)).mono
        fun b hb' => hb'.elim id id, ?_⟩
      omega
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem copy_mrs_fault_rgW {T : Set U64} (hT : P1.TcbPlaced T) {s0 s : S} {snd rcv rw : U64}
    {sl : Slice U64} (hn : sl.val.length ≤ 120) (hr : rcv ∈ T) {W : U64 → Prop} (hW : FW T rw W)
    (h : P1.WritesIn st s0 s W) :
    faults.copy_mrs_fault st s snd rcv sl rw ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  unfold faults.copy_mrs_fault
  refine WP.spec_bind (copy_mrs_fault_loop0_rgW (snd := snd) (sl := sl) (i := 0#usize) hT hr hW.1 h) ?_
  rintro ⟨s1, i⟩ h1
  simp only at h1
  by_cases hb : (rw != 0#u64) = true
  · have hrw0 : rw ≠ 0#u64 := by simpa using hb
    obtain ⟨hal, hWb⟩ := hW.2 hrw0
    simp only [hb, ↓reduceIte]
    exact copy_mrs_fault_loop1_rgW hal hWb hn s1 i h1
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    show (ok s1) ⦃ _ ⦄
    exact (WP.spec_ok _).2 h1

/-- **`set_mrs_fault`'s footprint** (any fault type; a timeout only without
an SC): the receiver's registers and buffer words (`FW`). -/
theorem set_mrs_fault_rgW {T : Set U64} (hT : P1.TcbPlaced T) {snd rcv rw : U64} (hr : rcv ∈ T) (s : S) (a : A)
    {W : U64 → Prop} (hW : FW T rw W)
    (hto : L.mem s (tFaultA snd) = fl4_abi.consts.fault.Timeout → L.mem s (P1.scA snd) = 0#u64) :
    faults.set_mrs_fault st arI s a snd rcv rw ⦃ r => P1.WritesIn st s r.2 W ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h0 : P1.WritesIn st s s W := P1.WritesIn.refl s _
  unfold faults.set_mrs_fault
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_
  rintro ty rfl
  refine WP.spec_bind (P0.obj.Tcb.fault_w0.p0 st snd s hS) fun w0 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w1.p0 st snd s hS) fun w1 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w2.p0 st snd s hS) fun w2 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s _ hS) fun pc _ => ?_
  by_cases h1 : L.mem s (tFaultA snd) = fl4_abi.consts.fault.CapFault
  · rw [if_pos h1]
    refine WP.spec_bind (set_mr_rgW hT hr hW (by decide) h0) ?_
    rintro ⟨_, s1⟩ h1'
    simp only at h1'
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (set_mr_rgW hT hr hW (by decide) h1') ?_
    rintro ⟨_, s2⟩ h2
    simp only at h2
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (set_mr_rgW hT hr hW (by decide) h2) ?_
    rintro ⟨_, s3⟩ h3
    simp only at h3
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (P0.faults.lookup_failure.p0 st s3 snd hS) fun lf _ => ?_
    exact set_mrs_lookup_failure_rgW hT hr hW (by decide) h3
  rw [if_neg h1]
  by_cases h2 : L.mem s (tFaultA snd) = fl4_abi.consts.fault.UnknownSyscall
  · rw [if_pos h2]
    unfold lift
    apply ok_bind_spec
    refine WP.spec_bind (copy_mrs_fault_rgW (snd := snd) hT (by rw [syscall_slice_length]; omega) hr hW h0) ?_
    rintro s2 h2'
    exact set_mr_rgW hT hr hW (by decide) h2'
  rw [if_neg h2]
  by_cases h3 : L.mem s (tFaultA snd) = fl4_abi.consts.fault.UserException
  · rw [if_pos h3]
    unfold lift
    apply ok_bind_spec
    have hel : (Array.to_slice faults.EXCEPTION_MESSAGE).val.length ≤ 120 := by
      rw [exc_slice_val]; simp [Fl4Spec.exceptionMessage]
    refine WP.spec_bind (copy_mrs_fault_rgW (snd := snd) hT hel hr hW h0) ?_
    rintro s2 h2'
    refine WP.spec_bind (set_mr_rgW hT hr hW (by decide) h2') ?_
    rintro ⟨_, s3⟩ h3'
    simp only at h3'
    try simp only [WP.uncurry'_pair]
    exact set_mr_rgW hT hr hW (by decide) h3'
  rw [if_neg h3]
  by_cases h4 : L.mem s (tFaultA snd) = fl4_abi.consts.fault.Timeout
  · rw [if_pos h4]
    refine WP.spec_bind (Fl4Proofs.P1.obj.Tcb.sc.spec s snd) ?_
    rintro i rfl
    unfold obj.Sc.is_null
    apply ok_bind_spec
    simp only [hto h4, decide_true, ↓reduceIte]
    exact set_mr_rgW hT hr hW (by decide) h0
  rw [if_neg h4]
  by_cases h5 : L.mem s (tFaultA snd) = fl4_abi.consts.fault.DebugException
  · rw [if_pos h5]
    refine WP.spec_bind (set_mr_rgW hT hr hW (by decide) h0) ?_
    rintro ⟨_, s1⟩ h1'
    simp only at h1'
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (set_mr_rgW hT hr hW (by decide) h1') ?_
    rintro ⟨ret, s2⟩ h2'
    simp only at h2'
    try simp only [WP.uncurry'_pair]
    split
    · split
      · refine WP.spec_bind (set_mr_rgW hT hr hW (by decide) h2') ?_
        rintro ⟨_, s3⟩ h3'
        simp only at h3'
        try simp only [WP.uncurry'_pair]
        exact set_mr_rgW hT hr hW (by decide) h3'
      · exact (WP.spec_ok _).2 h2'
    · exact (WP.spec_ok _).2 h2'
  rw [if_neg h5]
  by_cases h6 : L.mem s (tFaultA snd) = fl4_abi.consts.fault.VMFault
  · rw [if_pos h6]
    refine WP.spec_bind (set_mr_rgW hT hr hW (by decide) h0) ?_
    rintro ⟨_, s1⟩ h1'
    simp only at h1'
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (set_mr_rgW hT hr hW (by decide) h1') ?_
    rintro ⟨_, s2⟩ h2'
    simp only at h2'
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (set_mr_rgW hT hr hW (by decide) h2') ?_
    rintro ⟨_, s3⟩ h3'
    simp only at h3'
    try simp only [WP.uncurry'_pair]
    exact set_mr_rgW hT hr hW (by decide) h3'
  rw [if_neg h6]
  exact (WP.spec_ok _).2 h0

/-- **`do_ipc_transfer`'s footprint, a faulted sender** (any fault, a
timeout only without an SC), for the receive buffer `rw` the lookup
returns: `FW T rw W`. -/
theorem do_ipc_transfer_fault_rgW {T : Set U64} (hT : P1.TcbPlaced T) {snd rcv : U64} (hr : rcv ∈ T) (s : S)
    (a : A) (ep badge : U64) (grant : Bool) {rw : U64} {W : U64 → Prop} (hW : FW T rw W)
    (hb : msg.lookup_ipc_buffer st s true rcv ⦃ w => w = rw ⦄)
    (hty : L.mem s (tFaultA snd) ≠ fl4_abi.consts.fault.NullFault)
    (hto : L.mem s (tFaultA snd) = fl4_abi.consts.fault.Timeout → L.mem s (P1.scA snd) = 0#u64) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => P1.WritesIn st s s' W ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind hb ?_
  rintro rb rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_
  rintro ft rfl
  rw [if_neg hty]
  unfold ipc.do_fault_transfer
  refine WP.spec_bind (set_mrs_fault_rgW (arI := arI) hT hr s a hW hto) ?_
  rintro ⟨sent, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s1 hS) fun ft _ => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  refine WP.spec_bind (Pₘ := fun s3 => P1.WritesIn st s s3 W) ?_
    fun s3 h3 => WP.spec_mono (obj.Tcb.set_reg.rg (s := s3) (v := badge) hT hr
      (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s4 w4 => (h3.trans w4).mono fun b hb => hb.elim id (hW.1 b)
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    WP.spec_mono (obj.Tcb.set_reg.rg (v := w) (s := s1) hT hr (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => (h1.trans w4).mono fun b hb => hb.elim id (hW.1 b)

end

section SpecF
open Fl4Spec

/-- The spec's fault message of any fault but a timeout with an SC leaves
the state unchanged. -/
theorem makeFaultMsg_pure {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (f : Fault)
    (hto : ∀ b, f = .timeout b → x.tcbSchedContext = none) :
    ∃ label ms, makeFaultMsg (Z := Unit) f t σ = ({((label, ms), σ)}, False) := by
  cases f with
  | capFault c rp lf => exact ⟨_, _, makeFaultMsg_cap hk c rp lf⟩
  | unknownSyscallException n => exact ⟨_, _, makeFaultMsg_unknown hk n⟩
  | userException e c => exact ⟨_, _, makeFaultMsg_user hk e c⟩
  | timeout b => exact ⟨_, _, makeFaultMsg_timeout hk (hto b rfl) b⟩
  | archFault af =>
    cases af with
    | vmFault va d => exact ⟨_, _, makeFaultMsg_vm hk va d⟩

end SpecF

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 16000000 in
/-- **The transfer step of a faulted sender to a receiver, with or without a
receive buffer** (XTopJointFaultRecv's `xferFaultStepJ` for any fault with
`FaultOK`): on `IRel` by EpFaultNone's `do_ipc_transfer_faultN` (no buffer)
or EpFaultMore's `do_ipc_transfer_fault` (a buffer), the spec's outcome by
`makeFaultMsg_pure` and `doFaultTransfer_eqN`/`doFaultTransfer_eq`, the
footprint by `do_ipc_transfer_fault_rgW`, P1's hole by `xfer_all` or
`blkX_bufw`. -/
theorem xferFaultStepGJ {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64}
    {B : Set (U64 × Fl4Spec.Word)} {c : U64} (hP0 : Ipc.IPlaced N T E R B) (hP : EPlaced T E R B)
    (hHE : EpHyps st T E R B (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))))
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    (hSR : SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s σ)
    (hOK : Endp.IpcBufCapOK σ) (hBC : Endp.BufCover T B σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) {f : Fl4Spec.Fault}
    (hf : xs.tcbFault = some f) (hok : FaultOK (L := L) s snd xs f)
    (ep badge : U64) (grant : Bool)
    {T1 Cs1 Ω Sg Rp Scs Nt Ac1 X : Set U64} {H1 : P1.Heap} {Zb : U64 → Nat} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} (hT1 : P1.TcbPlaced T1) (hr1 : rcv ∈ T1)
    (h : P1.SchedQueuesInvX st T1 Cs1 Ω H1 X s Q Rq) (hB : P1.BoundInv st T1 Ac1 s)
    (hX : P1.XInv st T1 Cs1 Ω Sg Rp Scs Nt Zb s) (hS : P1.SCsOK st T1 Ω Sg Scs Zb Ac1 s) (hSg : P1.SgOK st Ω Sg s)
    (hU : ∀ b, RcvBufW xr b → P1.OutsideObjs st T1 Cs1 s b ∧
      (∀ e, (H1 e = some .ep ∨ H1 e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val) ∧ b ∉ Sg) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => ∃ (x' : Fl4Spec.Tcb)
      (um : Fl4Spec.Word → Fl4Spec.Word8),
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        ({((), Notif.updK (Endp.setUm σ um) rcv.bv (.tcb x'))}, False) ∧ x' = { xr with tcbArch := x'.tcbArch } ∧
      EpStateRel T E R B (L.mem s') (Notif.updK (Endp.setUm σ um) rcv.bv (.tcb x')) ∧
      (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)) s'
          (Notif.updK (Endp.setUm σ um) rcv.bv (.tcb x')) ∧
        Endp.IpcBufCapOK (Notif.updK (Endp.setUm σ um) rcv.bv (.tcb x'))) ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      P1.WritesIn st s s' (fun b => XferRegW T1 ∅ b ∨ RcvBufW xr b) ∧
      P1.SchedQueuesInvX st T1 Cs1 Ω H1 X s' Q Rq ∧ P1.BoundInv st T1 Ac1 s' ∧ P1.XInv st T1 Cs1 Ω Sg Rp Scs Nt Zb s' ∧
      P1.SCsOK st T1 Ω Sg Scs Zb Ac1 s' ∧ P1.SgOK st Ω Sg s' ∧
      (∀ y ∈ T1, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ⦄ := by
  have hxs := hR.at_tcb hs hks
  have hty : L.mem s (tFaultA snd) ≠ fl4_abi.consts.fault.NullFault := by
    intro e
    have := hxs.fault0.1 (by rw [e]; unfold fl4_abi.consts.fault.NullFault; rfl)
    rw [hf] at this; cases this
  have hto : L.mem s (tFaultA snd) = fl4_abi.consts.fault.Timeout → L.mem s (P1.scA snd) = 0#u64 := by
    intro e
    obtain ⟨b, hb⟩ := hxs.faultT.1 (by rw [e]; unfold fl4_abi.consts.fault.Timeout; rfl)
    rw [hf] at hb; cases hb
    exact hok.2
  have htoS : ∀ b, f = .timeout b → xs.tcbSchedContext = none := by
    intro b hb; subst hb; exact hok.1
  obtain ⟨label, ms, hmsg⟩ := makeFaultMsg_pure hks f htoS
  obtain ⟨⟨⟨G, hBt⟩, hBw⟩, -⟩ := hSR.1.1
  have hlb := lookup_buf_full s σ hBt.2.1.1 hBt.2.1.2.1 (Ipc.RelTopB.tcbT hBt hkr) hkr hOK true
  cases hrb : Endp.ipcBufOf true xr with
  | none =>
    have hlk : msg.lookup_ipc_buffer st s true rcv ⦃ w => w = 0#u64 ⦄ := WP.spec_mono hlb fun w hw => hw.1.2 hrb
    have hspec0 : Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv none σ := by
      unfold Fl4Spec.doIpcTransfer
      rw [nd_bind_one (lookupIpcBuffer_eq hkr true), hrb, nd_bind_one (threadGet_eq _ hks), hf]
    have hspec := hspec0.trans (doFaultTransfer_eqN hks hkr hf hmsg badge.bv)
    have uu : ∀ (σ0 : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (o o' : Fl4Spec.KernelObject),
        Notif.updK (Notif.updK σ0 p o) p o' = Notif.updK σ0 p o' := fun _ _ _ _ => by
      simp only [Notif.updK, Function.update_idem]
    simp only [mrStateN, uu] at hspec
    have hW : FW T1 0#u64 (XferRegW T1 ∅) := ⟨fun _ h => h, fun h => absurd rfl h⟩
    refine WP.spec_mono (WP.spec_and (do_ipc_transfer_faultN (ar := arI) (epHyps_buf hHE)
      (epBufHyps_buf (st := st) (th := th) (cr := cr) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c))
      hP s a σ hR ⟨hSR.1, hOK⟩ hs hr hne hks hkr hf hok hrb ep badge grant)
      (do_ipc_transfer_fault_rgW (arI := arI) hT1 hr1 s a ep badge grant hW hlk hty hto)) ?_
    rintro s2 ⟨⟨σ', e2, hR2, hS2, hA2, -⟩, w2⟩
    have eσ := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (e2.symm.trans hspec)))
    subst eσ
    obtain ⟨h2, hB2, hX2, hS2', hSg2, -, -, -, -, f2, -⟩ :=
      P1.xfer_all h hB hX hS hSg (U := ∅) (fun b hb => absurd hb (Set.notMem_empty _))
        (w2.mono fun b hb => P1.XferRegW.foot hb)
    exact ⟨_, σ.machineState.underlyingMemory, e2, rfl, hR2, hS2, hA2, w2.mono fun b hb => Or.inl hb,
      h2, hB2, hX2, hS2', hSg2, f2⟩
  | some p =>
    obtain ⟨x0, hk0, hbw⟩ := hBw.bw rcv hr
    rw [hkr] at hk0; cases hk0
    have hlk : msg.lookup_ipc_buffer st s true rcv ⦃ w => w = ⟨p⟩ ⦄ := WP.spec_mono hlb fun w hw => by
      have hwb : w.bv = p := hw.2 hbw p hrb
      rw [← hwb]
    have hrw0 : (⟨p⟩ : U64) ≠ 0#u64 := by
      obtain ⟨w0, -, hw0⟩ := spec_exists hlb
      have hwb : w0.bv = p := hw0.2 hbw p hrb
      intro e
      have : w0 = 0#u64 := by rw [← e, ← hwb]
      rw [hw0.1.1 this] at hrb; cases hrb
    have hal : ∀ i : U64, i.val < 128 → P1.Aligned (Endp.fl4BufA ⟨p⟩ i) := fun i hi =>
      (hP.balign _ (hBC rcv hr xr true p hkr hrb ⟨p⟩ rfl i hi)).1
    have hBm := epBufMapHyps_bufC (st := st) (th := th) (cr := cr) (C := C) (c := c) hP0
    obtain ⟨rw1, -, hrw1, hmr⟩ := spec_exists (hBm.lookupMap s σ rcv xr true p hR ⟨⟨hSR.1, hOK⟩, hBC⟩ hr hkr hrb)
    have hu := hBm.frame s σ rcv xr p hR ⟨⟨hSR.1, hOK⟩, hBC⟩ hr hkr hrb
    have hal' : ∀ q ∈ mrPairs ms, (bufAddr p q.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (bufAddr p q.1) σ := by
      intro q hq
      have := (List.of_mem_zip hq).1
      simp at this
      exact ⟨bufAddr_aligned hP hmr _, hu _ (by omega)⟩
    have hspec0 : Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv (some p) σ := by
      unfold Fl4Spec.doIpcTransfer
      rw [nd_bind_one (lookupIpcBuffer_eq hkr true), hrb, nd_bind_one (threadGet_eq _ hks), hf]
    have hspec := hspec0.trans (doFaultTransfer_eq hks hkr hf hmsg p hal' badge.bv)
    have hW : FW T1 ⟨p⟩ (XferBW T1 ⟨p⟩) := ⟨fun _ h => Or.inl h, fun _ => ⟨hal, fun _ h => Or.inr h⟩⟩
    refine WP.spec_mono (WP.spec_and (Endp.do_ipc_transfer_fault (ar := arI) (epHyps_bufC hHE T) hBm hP s a σ hR
      ⟨⟨hSR.1, hOK⟩, hBC⟩ hs hr hne hks hkr hf hok hrb ep badge grant)
      (do_ipc_transfer_fault_rgW (arI := arI) hT1 hr1 s a ep badge grant hW hlk hty hto)) ?_
    rintro s2 ⟨⟨σ', e2, hR2, hS2, hA2, -⟩, w2⟩
    have eσ := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst (e2.symm.trans hspec)))
    simp only [mrState, updK_setUm_updK] at eσ
    subst eσ
    have hW' : P1.WritesIn st s s2 (fun b => XferRegW T1 ∅ b ∨ RcvBufW xr b) :=
      w2.mono fun b hb => hb.imp_right fun h' => ⟨p, hrb, h'⟩
    obtain ⟨h2, hB2, hX2, hS2', hSg2, -, -, -, -, f2⟩ := blkX_bufw (l := rbList ⟨p⟩) h hB hX hS hSg
      (fun b hb => hU b ⟨p, hrb, mem_rbList.1 hb⟩) (w2.mono fun b hb => hb.imp_right mem_rbList.2)
    exact ⟨_, _, e2, rfl, hR2, hS2.1, hA2, hW', h2, hB2, hX2, hS2', hSg2, f2⟩

end

end

end Fl4Proofs.P3
