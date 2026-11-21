/-
P3 (DESIGN.md §9), IPC: **`do_ipc_transfer` of a faulted sender at `J`**
(toward XTopJointIpcJ's `JReplyRestHyp` and `JSendRestHyp`): FL4's
`do_fault_transfer` (`faults::set_mrs_fault` per fault type, the message
info, the badge) from `JAtZ` before to `JAtZ` after, against the spec's
`do_fault_transfer`, one J step per word written (as XTopJointXfer, and the
`IRel` proofs EpFault / EpFaultUs / EpFaultMore / EpFaultNone / IpcTmo).

* `jMrSt σ0 rcv x0 pb ms`: the spec's state after `set_mrs rcv pb ms`
  (`mrState` into a buffer, `mrStateN` without one); `MrJ`: `JAtZ` at it.
* `MrJ.reg` (a message register, `JAtZ.regWrJ` with `reg_wr_irel`),
  `MrJ.buf` (a buffer word, `JAtZ.userWrJ` with `JAtZ.bufWord`;
  `IpcBufCapOK`, `BufPlaced` by BufJ's `JAtZ.xferH`), `MrJ.appendN`
  (past the registers without a buffer nothing is written); `setMrJ`: FL4's
  `set_mr` of the next word, either way.
* `setMrsLfJ`, `copyMrsFaultJ`: the lookup-failure words, and
  `copy_mrs_fault` of a register list (the sender's registers read through
  the endpoint relation at the current `J` state).
* `setMrsFault*J`: `set_mrs_fault` of a cap fault, an unknown syscall, a user
  exception, a timeout without an SC, a VM fault, and a timeout with an SC
  (`schedcontext::update_consumed` first: `JAtZ.updConsumedJ` with
  `update_consumed_irel`; [P] `hAT`, `hmax`, `htu` as ScJointConsumed's).
* `doFaultXferJ`: `do_fault_transfer` given its `set_mrs_fault`;
  `JAtZ.xferFaultJ`: `do_ipc_transfer` of a faulted sender, the spec's
  outcome changing only the receiver's TCB (in its user context) and, for a
  timeout with an SC, that SC.
-/
import Fl4Proofs.P3.XTopJointXfer
import Fl4Proofs.P3.ScJointConsumed
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- The spec's state after `set_mrs rcv pb ms`. -/
def jMrSt (σ0 : Fl4Spec.State Unit) (rcv : Fl4Spec.ObjRef) (x0 : Fl4Spec.Tcb) :
    Option Fl4Spec.ObjRef → List Fl4Spec.Word → Fl4Spec.State Unit
  | some p, ms => Endp.mrState σ0 rcv x0 p ms
  | none, ms => Endp.mrStateN σ0 rcv x0 ms

/-- What FL4's `set_mr` returns after `n` words. -/
def jMrRet : Option Fl4Spec.ObjRef → Nat → Nat
  | some _, n => n
  | none, n => min n 4

/-- The spec's message length after `n` words. -/
def jLen : Option Fl4Spec.ObjRef → Nat → Nat
  | some _, n => min n Fl4Spec.msgMaxLength
  | none, n => min 4 n

/-- FL4's receive buffer word `rw` for the spec's `pb`. -/
def JBufR (B : Set (U64 × Fl4Spec.Word)) (rw : U64) : Option Fl4Spec.ObjRef → Prop
  | none => rw = 0#u64
  | some p => rw ≠ 0#u64 ∧ Endp.BufMap B rw p ∧ rw.bv = p

theorem jMrSt_nil {σ0 : Fl4Spec.State Unit} {rcv : Fl4Spec.ObjRef} {x0 : Fl4Spec.Tcb}
    (hk : σ0.kheap rcv = some (.tcb x0)) (pb : Option Fl4Spec.ObjRef) : jMrSt σ0 rcv x0 pb [] = σ0 := by
  cases pb with
  | none => exact Endp.mrStateN_nil hk
  | some p => exact Endp.mrState_nil hk p

theorem jMrSt_rcv (σ0 : Fl4Spec.State Unit) (rcv : Fl4Spec.ObjRef) (x0 : Fl4Spec.Tcb) (pb : Option Fl4Spec.ObjRef)
    (ms : List Fl4Spec.Word) : (jMrSt σ0 rcv x0 pb ms).kheap rcv =
      some (.tcb (Endp.withRegs x0 (Endp.mrRegs x0.tcbArch.tcbContext.userRegs ms))) := by
  cases pb <;> simp [jMrSt, Endp.mrState, Endp.mrStateN, Endp.setUm, Notif.updK]

theorem jMrSt_other (σ0 : Fl4Spec.State Unit) (rcv : Fl4Spec.ObjRef) (x0 : Fl4Spec.Tcb) (pb : Option Fl4Spec.ObjRef)
    (ms : List Fl4Spec.Word) {q : Fl4Spec.ObjRef} (hq : q ≠ rcv) : (jMrSt σ0 rcv x0 pb ms).kheap q = σ0.kheap q := by
  cases pb <;> simp [jMrSt, Endp.mrState, Endp.mrStateN, Endp.setUm, Notif.updK, hq]

theorem jMrSt_appendN (σ0 : Fl4Spec.State Unit) (rcv : Fl4Spec.ObjRef) (x0 : Fl4Spec.Tcb) (ms ys : List Fl4Spec.Word)
    (h : 4 ≤ ms.length) : jMrSt σ0 rcv x0 none (ms ++ ys) = jMrSt σ0 rcv x0 none ms :=
  Endp.mrStateN_append_ge _ _ _ _ _ h

/-- `JAtZ` at the state after the words `ms` of a message. -/
def MrJ {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
    (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64)
    (D : Set U64) (a : A) (σ0 : Fl4Spec.State Unit) (rcv : U64) (x0 : Fl4Spec.Tcb) (pb : Option Fl4Spec.ObjRef)
    (s : S) (ms : List Fl4Spec.Word) : Prop :=
  ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s a (jMrSt σ0 rcv.bv x0 pb ms)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
  {σ0 : Fl4Spec.State Unit} {rcv : U64} {x0 : Fl4Spec.Tcb} {pb : Option Fl4Spec.ObjRef}

theorem MrJ.init {V : XVs} (J : JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s a σ0)
    (hk0 : σ0.kheap rcv.bv = some (.tcb x0)) (pb : Option Fl4Spec.ObjRef) :
    MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb s [] :=
  ⟨V, by rw [jMrSt_nil hk0]; exact J⟩

theorem MrJ.appendN {ms : List Fl4Spec.Word} (h : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 none s ms)
    (h4 : 4 ≤ ms.length) (ys : List Fl4Spec.Word) :
    MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 none s (ms ++ ys) := by
  obtain ⟨V, J⟩ := h
  exact ⟨V, by rw [jMrSt_appendN _ _ _ _ _ h4]; exact J⟩

/-- A sender's register at a message state (its TCB unchanged). -/
theorem MrJ.sndReg {ms : List Fl4Spec.Word} (h : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb s ms)
    {snd : U64} (hs : snd ∈ Z.T) (hne : snd.bv ≠ rcv.bv) {xs : Fl4Spec.Tcb}
    (hks : σ0.kheap snd.bv = some (.tcb xs)) (r : Fl4Spec.Register) :
    (L.mem s (regA snd (regIdx r))).bv = xs.tcbArch.tcbContext.userRegs r := by
  obtain ⟨V, J⟩ := h
  exact J.regRead hs (by rw [jMrSt_other _ _ _ _ _ hne]; exact hks) r

/-- A sender's fault words at a message state. -/
theorem MrJ.sndFault {ms : List Fl4Spec.Word} (h : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb s ms)
    {snd : U64} (hs : snd ∈ Z.T) (hne : snd.bv ≠ rcv.bv) {xs : Fl4Spec.Tcb}
    (hks : σ0.kheap snd.bv = some (.tcb xs)) : FaultRel (L.mem s) snd xs.tcbFault := by
  obtain ⟨V, J⟩ := h
  exact ((J.xtop.irelK J.ks J.buf).1.toE.at_tcb hs (by rw [jMrSt_other _ _ _ _ _ hne]; exact hks)).faultR

set_option maxHeartbeats 8000000 in
/-- **A message register written at `J`** (word `k < 4`). -/
theorem MrJ.reg {ms : List Fl4Spec.Word} (h : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb s ms)
    (hr : rcv ∈ Z.T) (k : Nat) (hk : k = ms.length) (hk4 : k < 4) (v : U64) :
    MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb (L.wr s (regA rcv (regIdx (Endp.mrIdx k))) v)
      (ms ++ [v.bv]) := by
  obtain ⟨V, J⟩ := h
  have hkr := jMrSt_rcv σ0 rcv.bv x0 pb ms
  have hX := reg_wr_irel J.ip (J.xtop.irelK J.ks J.buf) hr hkr (Endp.mrIdx k) (mrIdx_ne_badge _) v
  obtain ⟨V2, J2⟩ := J.regWrJ hr hkr (Endp.mrIdx k) v hX
  refine ⟨V2, ?_⟩
  have e : Notif.updK (jMrSt σ0 rcv.bv x0 pb ms) rcv.bv (.tcb (Notif.setReg (Endp.withRegs x0
      (Endp.mrRegs x0.tcbArch.tcbContext.userRegs ms)) (Endp.mrIdx k) v.bv)) =
      jMrSt σ0 rcv.bv x0 pb (ms ++ [v.bv]) := by
    cases pb with
    | none => exact Endp.mrStateN_snoc_lt _ _ _ _ _ k hk (by omega)
    | some p => exact Endp.mrState_snoc_lt _ _ _ _ _ _ k hk (by omega)
  rw [← e]; exact J2

set_option maxHeartbeats 8000000 in
/-- **A buffer word of the message written at `J`** (word `i1 = |ms| + 1`
of the receive buffer, `4 ≤ |ms| < 120`). -/
theorem MrJ.buf {ms : List Fl4Spec.Word} {p : Fl4Spec.ObjRef}
    (h : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 (some p) s ms)
    (hr : rcv ∈ Z.T) (hq : Endp.ipcBufOf true x0 = some p) {rw : U64} (hmr : Endp.BufMap Z.B rw p)
    (hrw : rw.bv = p) (i1 : U64) (hi1 : i1.val = ms.length + 1) (h4 : 4 ≤ ms.length) (h120 : ms.length < 120)
    (v : U64) :
    MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 (some p) (L.wr s (Endp.fl4BufA rw i1) v) (ms ++ [v.bv]) := by
  obtain ⟨V, J⟩ := h
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hrT : Z.th rcv = some .tcb := (hJ.tcb rcv).2 (J.zH.1 rcv hr)
  obtain ⟨hOK, -, hBP⟩ := J.xferH
  have hwB := hmr i1 (by omega)
  have hk := jMrSt_rcv σ0 rcv.bv x0 (some p) ms
  obtain ⟨hAp, hObj⟩ := J.bufWord hOK hrT hk (q := p) hq i1.val (by omega) (b := Endp.fl4BufA rw i1)
    (by rw [fl4BufA_bv, hrw])
  have J2 := J.userWrJ hBP hwB hAp hObj v
  refine ⟨V, ?_⟩
  show JAtZ (L := L) arI AR _ H Cs Ac Lst D _ a (Endp.mrState σ0 rcv.bv x0 p (ms ++ [v.bv]))
  rw [← Endp.mrState_snoc_ge _ _ _ _ _ _ h4 h120, ← hi1]
  exact J2

set_option maxHeartbeats 8000000 in
/-- **FL4's `set_mr` of the next message word at `J`**, into a receive
buffer or without one. -/
theorem setMrJ
    (hr : rcv ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p) {rw : U64} (hb : JBufR Z.B rw pb)
    {ms : List Fl4Spec.Word} (h : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb s ms)
    (i : U64) (hi : i.val = ms.length) (hi' : i.val < 120) (v : U64) :
    msg.set_mr st s rcv rw i v ⦃ r => r.1.val = jMrRet pb (i.val + 1) ∧
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb r.2 (ms ++ [v.bv]) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  unfold msg.set_mr
  by_cases h4 : i < msg.N_MSG_REGISTERS
  · have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h4; omega
    simp only [h4, ↓reduceIte]
    refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
    rintro r rfl
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s rcv _ v) ?_
    rintro s1 rfl
    unfold lift
    apply ok_bind_spec
    simp only [WP.spec_ok]
    refine ⟨?_, h.reg hr i.val hi hi4 v⟩
    have e : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [e]; cases pb <;> simp only [jMrRet] <;> omega
  · have hi4 : 4 ≤ i.val := by
      have : ¬ i.val < 4 := fun h' => h4 ((P1.gt_iff_val).2 (by rw [hN]; exact h')); omega
    rw [if_neg h4]
    cases pb with
    | none =>
      have hb' : rw = 0#u64 := hb
      subst hb'
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨by rw [hN]; simp only [jMrRet]; omega, h.appendN (by omega) _⟩
    | some p =>
      obtain ⟨hrw0, hmr, hrw⟩ := hb
      have hb1 : (rw != 0#u64) = true := by simp [hrw0]
      simp only [hb1, ↓reduceIte]
      unfold lift
      apply ok_bind_spec
      refine WP.spec_bind (Endp.msg.buf_set.spec s rw _ v) ?_
      rintro s1 rfl
      apply ok_bind_spec
      simp only [WP.spec_ok]
      have hiv : (core.num.U64.wrapping_add i 1#u64).val = ms.length + 1 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      refine ⟨by rw [hiv]; simp only [jMrRet]; omega,
        h.buf hr (hq p rfl) hmr hrw _ hiv (by omega) (by omega) v⟩

set_option maxHeartbeats 8000000 in
/-- **`set_mrs_lookup_failure` at `J`**: the lookup-failure words, appended. -/
theorem setMrsLfJ
    (hr : rcv ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p) {rw : U64} (hb : JBufR Z.B rw pb)
    {ms : List Fl4Spec.Word} (h : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb s ms)
    (off : U64) (hoff : off.val = ms.length) (hlen : ms.length + 4 ≤ 120) (lfv : error.LookupFault) :
    faults.set_mrs_lookup_failure st s rcv rw lfv off ⦃ r =>
      r.1.val = jMrRet pb (ms.length + (Endp.fl4LfMsg lfv).length) ∧
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb r.2 (ms ++ ((Endp.fl4LfMsg lfv).map UScalar.bv : List Fl4Spec.Word)) ⦄ := by
  have hset := fun {s' : S} {ms' : List Fl4Spec.Word}
      (h' : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb s' ms') => setMrJ hr hq hb h'
  unfold faults.set_mrs_lookup_failure error.LookupFault.type_code
  cases lfv with
  | InvalidRoot =>
    dsimp only
    apply ok_bind_spec
    refine WP.spec_bind (hset h off hoff (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨h1, h2⟩
    show (ok (i1, s1)) ⦃ _ ⦄
    simp only [WP.spec_ok]
    refine ⟨by simp only at h1; rw [h1, hoff]; rfl, ?_⟩
    simpa [Endp.fl4LfMsg, fl4_abi.consts.lookup.InvalidRoot] using h2
  | MissingCapability bl =>
    dsimp only
    apply ok_bind_spec
    refine WP.spec_bind (hset h off hoff (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨h1, h2⟩
    unfold lift
    apply ok_bind_spec
    refine WP.spec_mono (hset h2 (core.num.U64.wrapping_add off 1#u64)
      (by rw [Endp.wadd_val off 1 (by omega) _ rfl]; simp; omega)
      (by rw [Endp.wadd_val off 1 (by omega) _ rfl]; omega) bl) ?_
    rintro ⟨i2, s2⟩ ⟨g1, g2⟩
    refine ⟨by simp only at g1 ⊢; rw [g1, Endp.wadd_val off 1 (by omega) _ rfl, hoff]; rfl, ?_⟩
    simpa [Endp.fl4LfMsg, fl4_abi.consts.lookup.MissingCapability] using g2
  | DepthMismatch bf bl =>
    dsimp only
    apply ok_bind_spec
    refine WP.spec_bind (hset h off hoff (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨h1, h2⟩
    unfold lift
    apply ok_bind_spec
    refine WP.spec_bind (hset h2 (core.num.U64.wrapping_add off 1#u64)
      (by rw [Endp.wadd_val off 1 (by omega) _ rfl]; simp; omega)
      (by rw [Endp.wadd_val off 1 (by omega) _ rfl]; omega) bl) ?_
    rintro ⟨i2, s2⟩ ⟨g1, g2⟩
    apply ok_bind_spec
    refine WP.spec_mono (hset g2 (core.num.U64.wrapping_add off 2#u64)
      (by rw [Endp.wadd_val off 2 (by omega) _ rfl]; simp; omega)
      (by rw [Endp.wadd_val off 2 (by omega) _ rfl]; omega) bf) ?_
    rintro ⟨i3, s3⟩ ⟨k1, k2⟩
    refine ⟨by simp only at k1 ⊢; rw [k1, Endp.wadd_val off 2 (by omega) _ rfl, hoff]; rfl, ?_⟩
    simpa [Endp.fl4LfMsg, fl4_abi.consts.lookup.DepthMismatch] using k2
  | GuardMismatch g bl gs =>
    dsimp only
    apply ok_bind_spec
    refine WP.spec_bind (hset h off hoff (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨h1, h2⟩
    unfold lift
    apply ok_bind_spec
    refine WP.spec_bind (hset h2 (core.num.U64.wrapping_add off 1#u64)
      (by rw [Endp.wadd_val off 1 (by omega) _ rfl]; simp; omega)
      (by rw [Endp.wadd_val off 1 (by omega) _ rfl]; omega) bl) ?_
    rintro ⟨i2, s2⟩ ⟨g1, g2⟩
    apply ok_bind_spec
    refine WP.spec_bind (hset g2 (core.num.U64.wrapping_add off 2#u64)
      (by rw [Endp.wadd_val off 2 (by omega) _ rfl]; simp; omega)
      (by rw [Endp.wadd_val off 2 (by omega) _ rfl]; omega) g) ?_
    rintro ⟨i3, s3⟩ ⟨k1, k2⟩
    apply ok_bind_spec
    refine WP.spec_mono (hset k2 (core.num.U64.wrapping_add off 3#u64)
      (by rw [Endp.wadd_val off 3 (by omega) _ rfl]; simp; omega)
      (by rw [Endp.wadd_val off 3 (by omega) _ rfl]; omega) gs) ?_
    rintro ⟨i4, s4⟩ ⟨l1, l2⟩
    refine ⟨by simp only at l1 ⊢; rw [l1, Endp.wadd_val off 3 (by omega) _ rfl, hoff]; rfl, ?_⟩
    simpa [Endp.fl4LfMsg, fl4_abi.consts.lookup.GuardMismatch] using l2

set_option maxHeartbeats 8000000 in
/-- **`copy_mrs_fault`'s first loop at `J`**: message registers
`0 .. min |rl| 4`. -/
theorem copyMrsFaultJ_loop0 {s0 : S} (hr : rcv ∈ Z.T) {snd : U64} (hs : snd ∈ Z.T) (hne : snd.bv ≠ rcv.bv)
    {xs : Fl4Spec.Tcb} (hks : σ0.kheap snd.bv = some (.tcb xs))
    (h0 : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb s0 [])
    {sl : Slice U64} {rl : List Fl4Spec.Register} (hsl : sl.val = rl.map regIdx) (hn : rl.length ≤ 120) :
    faults.copy_mrs_fault_loop0 st s0 snd rcv sl 0#usize ⦃ r => r.2.val = min rl.length 4 ∧
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb r.1
        ((rl.take r.2.val).map xs.tcbArch.tcbContext.userRegs) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  have hlen := Endp.slice_len_val hsl
  unfold faults.copy_mrs_fault_loop0
  apply loop.spec_decr_nat (measure := fun x => 4 - x.2.val)
    (inv := fun x => x.2.val ≤ min rl.length 4 ∧
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb x.1 ((rl.take x.2.val).map xs.tcbArch.tcbContext.userRegs))
  · rintro ⟨s', i⟩ ⟨hi4, hI⟩
    unfold faults.copy_mrs_fault_loop0.body
    simp only at hi4 hI ⊢
    by_cases h1 : i < Slice.len sl
    · have hin : i.val < rl.length := by have := Endp.us_lt_iff.1 h1; omega
      simp only [h1, ↓reduceIte]
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = i.val := by rw [hi2]; exact Endp.cast_us i (by omega)
      by_cases h2 : i2 < msg.N_MSG_REGISTERS
      · have hi : i.val < 4 := by have := (P1.gt_iff_val).1 h2; omega
        simp only [h2, ↓reduceIte]
        step as ⟨r, hr'⟩
        refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' snd r) ?_
        rintro v rfl
        step as ⟨i4, hi4'⟩
        have hi4v : i4.val = i.val := by rw [hi4']; exact Endp.cast_us i (by omega)
        refine WP.spec_bind (Endp.msg_register_spec i4 (by omega)) ?_
        rintro r5 rfl
        refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s' rcv _ _) ?_
        rintro s1 rfl
        have hlen' : ((rl.take i.val).map xs.tcbArch.tcbContext.userRegs).length = i.val := by simp; omega
        have hI1 := hI.reg hr i4.val (by omega) (by omega) (L.mem s' (regA snd r))
        step as ⟨i6, hi6⟩
        have hi6v : i6.val = i.val + 1 := by simpa using hi6
        have hvb : (L.mem s' (regA snd r)).bv = xs.tcbArch.tcbContext.userRegs rl[i.val] := by
          rw [hr', Endp.getElem_regs hsl]; exact hI.sndReg hs hne hks _
        refine ⟨by omega, ?_, by omega⟩
        rw [hi6v, Endp.take_succ_map _ rl i.val hin, ← hvb]
        exact hI1
      · simp only [h2, ↓reduceIte, WP.spec_ok]
        have hi : i.val = 4 := by
          have h2' : ¬ i.val < 4 := fun h => h2 ((P1.gt_iff_val).2 (by rw [hN]; omega))
          omega
        exact ⟨by omega, hI⟩
    · simp only [h1, ↓reduceIte, WP.spec_ok]
      have : ¬ i.val < rl.length := fun h => h1 (Endp.us_lt_iff.2 (by omega))
      exact ⟨by omega, hI⟩
  · exact ⟨by simp, by simpa using h0⟩

set_option maxHeartbeats 8000000 in
/-- **`copy_mrs_fault`'s second loop at `J`**: message words `4 .. |rl|`,
in the receive buffer. -/
theorem copyMrsFaultJ_loop1
    (hr : rcv ∈ Z.T) {snd : U64} (hs : snd ∈ Z.T) (hne : snd.bv ≠ rcv.bv)
    {xs : Fl4Spec.Tcb} (hks : σ0.kheap snd.bv = some (.tcb xs)) {p : Fl4Spec.ObjRef}
    (hq : Endp.ipcBufOf true x0 = some p) {rw : U64} (hmr : Endp.BufMap Z.B rw p) (hrw : rw.bv = p)
    {sl : Slice U64} {rl : List Fl4Spec.Register} (hsl : sl.val = rl.map regIdx) (hn : rl.length ≤ 120)
    (s1 : S) (i0 : Usize) (hi0 : i0.val = min rl.length 4)
    (hI : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 (some p) s1
      ((rl.take i0.val).map xs.tcbArch.tcbContext.userRegs)) :
    faults.copy_mrs_fault_loop1 st s1 snd sl rw i0 ⦃ s2 =>
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 (some p) s2 (rl.map xs.tcbArch.tcbContext.userRegs) ⦄ := by
  have hlen := Endp.slice_len_val hsl
  unfold faults.copy_mrs_fault_loop1
  apply loop.spec_decr_nat (measure := fun x => rl.length - x.2.val)
    (inv := fun x => min rl.length 4 ≤ x.2.val ∧ x.2.val ≤ rl.length ∧
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 (some p) x.1
        ((rl.take x.2.val).map xs.tcbArch.tcbContext.userRegs))
  · rintro ⟨s', i⟩ ⟨h4, hle, hI'⟩
    unfold faults.copy_mrs_fault_loop1.body
    simp only at h4 hle hI' ⊢
    by_cases h1 : i < Slice.len sl
    · have hi : i.val < rl.length := by have := Endp.us_lt_iff.1 h1; omega
      simp only [h1, ↓reduceIte]
      step as ⟨r, hr'⟩
      refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' snd r) ?_
      rintro v rfl
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = i.val + 1 := by
        have h3v : i3.val = i.val := by rw [hi3]; exact Endp.cast_us i (by omega)
        rw [hi4]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, h3v]; omega
      have hlen' : ((rl.take i.val).map xs.tcbArch.tcbContext.userRegs).length = i.val := by simp; omega
      refine WP.spec_bind (Endp.msg.buf_set.spec s' rw i4 _) ?_
      rintro s3 rfl
      have hI3 := hI'.buf hr hq hmr hrw i4 (by omega) (by omega) (by omega) (L.mem s' (regA snd r))
      step as ⟨i5, hi5⟩
      have hi5v : i5.val = i.val + 1 := by simpa using hi5
      have hvb : (L.mem s' (regA snd r)).bv = xs.tcbArch.tcbContext.userRegs rl[i.val] := by
        rw [hr', Endp.getElem_regs hsl]; exact hI'.sndReg hs hne hks _
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hi5v, Endp.take_succ_map _ rl i.val hi, ← hvb]
      exact hI3
    · simp only [h1, ↓reduceIte, WP.spec_ok]
      have hi : i.val = rl.length := by
        have : ¬ i.val < rl.length := fun h => h1 (Endp.us_lt_iff.2 (by omega))
        omega
      rw [hi, List.take_of_length_le (le_refl _)] at hI'
      exact hI'
  · simp only [hi0]
    exact ⟨le_refl _, by omega, hi0 ▸ hI⟩

set_option maxHeartbeats 8000000 in
/-- **`copy_mrs_fault` at `J`** of the sender's registers `rl`: the words
`0 .. |rl|` (into a buffer), or the first four (without one). -/
theorem copyMrsFaultJ
    (hr : rcv ∈ Z.T) {snd : U64} (hs : snd ∈ Z.T) (hne : snd.bv ≠ rcv.bv)
    {xs : Fl4Spec.Tcb} (hks : σ0.kheap snd.bv = some (.tcb xs))
    (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p) {rw : U64} (hb : JBufR Z.B rw pb)
    (h0 : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb s [])
    {sl : Slice U64} {rl : List Fl4Spec.Register} (hsl : sl.val = rl.map regIdx) (hn : rl.length ≤ 120) :
    faults.copy_mrs_fault st s snd rcv sl rw ⦃ s2 =>
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σ0 rcv x0 pb s2 (rl.map xs.tcbArch.tcbContext.userRegs) ⦄ := by
  unfold faults.copy_mrs_fault
  refine WP.spec_bind (copyMrsFaultJ_loop0 hr hs hne hks h0 hsl hn) ?_
  rintro ⟨s1, i⟩ ⟨hi, hI⟩
  simp only at hi hI
  cases pb with
  | none =>
    have hb' : rw = 0#u64 := hb
    subst hb'
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    show (ok s1) ⦃ _ ⦄
    simp only [WP.spec_ok]
    by_cases hn4 : rl.length ≤ 4
    · rw [hi, Nat.min_eq_left hn4, List.take_of_length_le (le_refl _)] at hI; exact hI
    · rw [hi, Nat.min_eq_right (by omega)] at hI
      have e : rl.map xs.tcbArch.tcbContext.userRegs = (rl.take 4).map xs.tcbArch.tcbContext.userRegs ++
          (rl.drop 4).map xs.tcbArch.tcbContext.userRegs := by
        rw [← List.map_append, List.take_append_drop]
      rw [e]
      exact hI.appendN (by simp; omega) _
  | some p =>
    obtain ⟨hrw0, hmr, hrw⟩ := hb
    have hb1 : (rw != 0#u64) = true := by simp [hrw0]
    simp only [hb1, ↓reduceIte]
    exact copyMrsFaultJ_loop1 hr hs hne hks (hq p rfl) hmr hrw hsl hn s1 i hi hI


theorem fault_ip_idx : layout.reg.FAULT_IP = regIdx .faultIP := by unfold layout.reg.FAULT_IP; rfl

set_option maxHeartbeats 16000000 in
/-- **`set_mrs_fault` of a cap fault at `J`**. -/
theorem setMrsFaultCapJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {snd : U64} (hr : rcv ∈ Z.T) (hs : snd ∈ Z.T) (hne : snd.bv ≠ rcv.bv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    (hq : ∀ p, pb = some p → Endp.ipcBufOf true xr = some p) {rw : U64} (hb : JBufR Z.B rw pb)
    {c : Fl4Spec.ObjRef} {rp : Bool} {lf : Fl4Spec.LookupFailure} (hf : xs.tcbFault = some (.capFault c rp lf)) :
    faults.set_mrs_fault st arI s a snd rcv rw ⦃ r =>
      r.1.val = jMrRet pb (Endp.capFaultMsg (xs.tcbArch.tcbContext.userRegs .faultIP) c rp lf).length ∧
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σ rcv xr pb r.2
        (Endp.capFaultMsg (xs.tcbArch.tcbContext.userRegs .faultIP) c rp lf) ⦄ := by
  have hfr := ((J.xtop.irelK J.ks J.buf).1.toE.at_tcb hs hks).faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0, hw1, -⟩ := hfr
  have hset := fun {s' : S} {ms' : List Fl4Spec.Word}
      (h' : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ rcv xr pb s' ms') => setMrJ hr hq hb h'
  have hpc : (L.mem s (regA snd layout.reg.FAULT_IP)).bv = xs.tcbArch.tcbContext.userRegs .faultIP := by
    rw [fault_ip_idx]; exact J.regRead hs hks _
  unfold faults.set_mrs_fault
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w0.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w1.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w2.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s snd _) ?_; rintro _ rfl
  rw [hty, if_pos (by unfold fl4_abi.consts.fault.CapFault; rfl)]
  refine WP.spec_bind (hset (MrJ.init (V := Z.vs) J hkr pb) 0#u64 rfl (by decide) _) ?_
  rintro ⟨_, s1⟩ ⟨-, hI1⟩
  refine WP.spec_bind (hset hI1 1#u64 rfl (by decide) _) ?_
  rintro ⟨_, s2⟩ ⟨-, hI2⟩
  refine WP.spec_bind (hset hI2 2#u64 rfl (by decide) _) ?_
  rintro ⟨_, s3⟩ ⟨-, hI3⟩
  have hf3 := hI3.sndFault hs hne hks
  unfold FaultRel at hf3
  rw [hf] at hf3
  refine WP.spec_bind (Pₘ := fun lfv =>
    ((Endp.fl4LfMsg lfv).map UScalar.bv : List Fl4Spec.Word) = Fl4Spec.msgFromLookupFailure lf) ?_ ?_
  · unfold faults.lookup_failure
    refine WP.spec_bind (Endp.obj.Tcb.lf_type.spec s3 snd) ?_; rintro _ rfl
    refine WP.spec_bind (Endp.obj.Tcb.lf_w0.spec s3 snd) ?_; rintro _ rfl
    refine WP.spec_bind (Endp.obj.Tcb.lf_w1.spec s3 snd) ?_; rintro _ rfl
    exact Endp.decode_rel hf3.2.2.2
  rintro lfv hlfv
  refine WP.spec_mono (setMrsLfJ hr hq hb hI3 3#u64 rfl (by simp) lfv) ?_
  rintro ⟨n, s4⟩ ⟨hn, hI4⟩
  have hlist : [(L.mem s (regA snd layout.reg.FAULT_IP)).bv, (L.mem s (tFw0A snd)).bv, (L.mem s (tFw1A snd)).bv] ++
      ((Endp.fl4LfMsg lfv).map UScalar.bv : List Fl4Spec.Word) =
      Endp.capFaultMsg (xs.tcbArch.tcbContext.userRegs .faultIP) c rp lf := by
    rw [hlfv, hpc, hw0, hw1]
    unfold Endp.capFaultMsg
    cases rp <;> rfl
  rw [List.nil_append, List.singleton_append, List.cons_append, List.singleton_append] at hI4
  refine ⟨?_, ?_⟩
  · simp only at hn
    rw [hn, ← hlist]
    apply congrArg (jMrRet pb)
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.nil_append] <;> omega
  · rw [← hlist]
    simpa using hI4

set_option maxHeartbeats 16000000 in
/-- **`set_mrs_fault` of an unknown-syscall fault at `J`**. -/
theorem setMrsFaultUnknownJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {snd : U64} (hr : rcv ∈ Z.T) (hs : snd ∈ Z.T) (hne : snd.bv ≠ rcv.bv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    (hq : ∀ p, pb = some p → Endp.ipcBufOf true xr = some p) {rw : U64} (hb : JBufR Z.B rw pb)
    {n : Fl4Spec.Word} (hf : xs.tcbFault = some (.unknownSyscallException n)) :
    faults.set_mrs_fault st arI s a snd rcv rw ⦃ r =>
      r.1.val = jMrRet pb (Endp.usMsg xs.tcbArch.tcbContext.userRegs n).length ∧
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σ rcv xr pb r.2 (Endp.usMsg xs.tcbArch.tcbContext.userRegs n) ⦄ := by
  have hfr := ((J.xtop.irelK J.ks J.buf).1.toE.at_tcb hs hks).faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  unfold faults.set_mrs_fault
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w0.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w1.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w2.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s snd _) ?_; rintro _ rfl
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.UnknownSyscall; rfl))]
  unfold lift
  apply ok_bind_spec
  refine WP.spec_bind (copyMrsFaultJ hr hs hne hks hq hb (MrJ.init (V := Z.vs) J hkr pb)
    Endp.syscall_slice_val (by decide)) ?_
  rintro s2 hI2
  refine WP.spec_mono (setMrJ hr hq hb hI2 18#u64 (by simp [Endp.syscall_len]) (by decide)
    (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s3⟩ ⟨hk, hI3⟩
  rw [hw0] at hI3
  exact ⟨by rw [Endp.usMsg_length]; simpa using hk, hI3⟩

set_option maxHeartbeats 16000000 in
/-- **`set_mrs_fault` of a user exception at `J`**. -/
theorem setMrsFaultUserJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {snd : U64} (hr : rcv ∈ Z.T) (hs : snd ∈ Z.T) (hne : snd.bv ≠ rcv.bv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    (hq : ∀ p, pb = some p → Endp.ipcBufOf true xr = some p) {rw : U64} (hb : JBufR Z.B rw pb)
    {e c : Fl4Spec.Word} (hf : xs.tcbFault = some (.userException e c)) :
    faults.set_mrs_fault st arI s a snd rcv rw ⦃ r =>
      r.1.val = jMrRet pb (Endp.ueMsg xs.tcbArch.tcbContext.userRegs e c).length ∧
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σ rcv xr pb r.2 (Endp.ueMsg xs.tcbArch.tcbContext.userRegs e c) ⦄ := by
  have hfr := ((J.xtop.irelK J.ks J.buf).1.toE.at_tcb hs hks).faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0, hw1⟩ := hfr
  unfold faults.set_mrs_fault
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w0.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w1.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w2.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s snd _) ?_; rintro _ rfl
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.UserException; rfl))]
  unfold lift
  apply ok_bind_spec
  refine WP.spec_bind (copyMrsFaultJ hr hs hne hks hq hb (MrJ.init (V := Z.vs) J hkr pb)
    Endp.exc_slice_val (by decide)) ?_
  rintro s2 hI2
  refine WP.spec_bind (setMrJ hr hq hb hI2 3#u64 (by simp [Fl4Spec.exceptionMessage]) (by decide)
    (L.mem s (tFw0A snd))) ?_
  rintro ⟨k3, s3⟩ ⟨-, hI3⟩
  refine WP.spec_mono (setMrJ hr hq hb hI3 4#u64 (by simp [Fl4Spec.exceptionMessage]) (by decide)
    (L.mem s (tFw1A snd))) ?_
  rintro ⟨k4, s4⟩ ⟨hk4, hI4⟩
  rw [hw0, hw1, List.append_assoc] at hI4
  exact ⟨by rw [Endp.ueMsg_length]; simpa using hk4, hI4⟩

set_option maxHeartbeats 16000000 in
/-- **`set_mrs_fault` of a timeout fault of a sender without an SC at
`J`**. -/
theorem setMrsFaultTmoJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {snd : U64} (hr : rcv ∈ Z.T) (hs : snd ∈ Z.T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    (hq : ∀ p, pb = some p → Endp.ipcBufOf true xr = some p) {rw : U64} (hb : JBufR Z.B rw pb)
    {b : Fl4Spec.Word} (hf : xs.tcbFault = some (.timeout b)) (hsc0 : L.mem s (P1.scA snd) = 0#u64) :
    faults.set_mrs_fault st arI s a snd rcv rw ⦃ r =>
      r.1.val = jMrRet pb [b].length ∧ MrJ (L := L) arI AR Z H Cs Ac Lst D a σ rcv xr pb r.2 [b] ⦄ := by
  have hfr := ((J.xtop.irelK J.ks J.buf).1.toE.at_tcb hs hks).faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  unfold faults.set_mrs_fault
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
  simp only [hsc0, decide_true, ↓reduceIte]
  refine WP.spec_mono (setMrJ hr hq hb (MrJ.init (V := Z.vs) J hkr pb) 0#u64 rfl (by decide)
    (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s1⟩ ⟨hk, hI⟩
  rw [hw0, List.nil_append] at hI
  exact ⟨by simpa using hk, hI⟩

set_option maxHeartbeats 16000000 in
/-- **`set_mrs_fault` of a VM fault at `J`**. -/
theorem setMrsFaultVmJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {snd : U64} (hr : rcv ∈ Z.T) (hs : snd ∈ Z.T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    (hq : ∀ p, pb = some p → Endp.ipcBufOf true xr = some p) {rw : U64} (hb : JBufR Z.B rw pb)
    {va : Fl4Spec.VSpaceRef} {d : List Fl4Spec.Word} (hf : xs.tcbFault = some (.archFault (.vmFault va d))) :
    faults.set_mrs_fault st arI s a snd rcv rw ⦃ r =>
      r.1.val = jMrRet pb (Endp.vmMsg (xs.tcbArch.tcbContext.userRegs .faultIP) va d).length ∧
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σ rcv xr pb r.2 (Endp.vmMsg (xs.tcbArch.tcbContext.userRegs .faultIP) va d) ⦄ := by
  have hfr := ((J.xtop.irelK J.ks J.buf).1.toE.at_tcb hs hks).faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0, hd⟩ := hfr
  have hset := fun {s' : S} {ms' : List Fl4Spec.Word}
      (h' : MrJ (L := L) arI AR Z H Cs Ac Lst D a σ rcv xr pb s' ms') => setMrJ hr hq hb h'
  have hpc : (L.mem s (regA snd layout.reg.FAULT_IP)).bv = xs.tcbArch.tcbContext.userRegs .faultIP := by
    rw [fault_ip_idx]; exact J.regRead hs hks _
  unfold faults.set_mrs_fault
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w0.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w1.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.fault_w2.spec s snd) ?_; rintro _ rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s snd _) ?_; rintro _ rfl
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.Timeout; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.DebugException; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.VMFault; rfl))]
  refine WP.spec_bind (hset (MrJ.init (V := Z.vs) J hkr pb) 0#u64 rfl (by decide) _) ?_
  rintro ⟨_, s1⟩ ⟨-, hI1⟩
  refine WP.spec_bind (hset hI1 1#u64 rfl (by decide) _) ?_
  rintro ⟨_, s2⟩ ⟨-, hI2⟩
  refine WP.spec_bind (hset hI2 2#u64 rfl (by decide) _) ?_
  rintro ⟨_, s3⟩ ⟨-, hI3⟩
  refine WP.spec_mono (hset hI3 3#u64 rfl (by decide) _) ?_
  rintro ⟨k, s4⟩ ⟨hk, hI4⟩
  have hl : [(L.mem s (regA snd layout.reg.FAULT_IP)).bv] ++ [(L.mem s (tFw0A snd)).bv] ++
      [(L.mem s (tFw2A snd)).bv] ++ [(L.mem s (tFw1A snd)).bv] =
      Endp.vmMsg (xs.tcbArch.tcbContext.userRegs .faultIP) va d := by
    rw [hpc, hw0, hd]; rfl
  rw [List.nil_append, hl] at hI4
  exact ⟨by rw [← hl]; simpa using hk, hI4⟩

set_option maxHeartbeats 16000000 in
/-- **`set_mrs_fault` of a timeout fault of a sender with an SC at `J`**:
`update_consumed` (`JAtZ.updConsumedJ`, with `update_consumed_irel` for the
word written and the time returned), then the badge and the consumed time.
[P] `hAT`, `hmax`, `htu` (as ScJointConsumed). -/
theorem setMrsFaultTmoScJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {snd : U64} (hr : rcv ∈ Z.T) (hs : snd ∈ Z.T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    (hq : ∀ p, pb = some p → Endp.ipcBufOf true xr = some p) {rw : U64} (hb : JBufR Z.B rw pb)
    {b : Fl4Spec.Word} (hf : xs.tcbFault = some (.timeout b)) {sc : U64} (hsc : L.mem s (P1.scA snd) = sc)
    (hsc0 : sc ≠ 0#u64) (hscC : sc ∈ Z.C) {y : Fl4Spec.SchedContext} {n : Nat}
    (hky : σ.kheap sc.bv = some (.schedContext y n)) :
    faults.set_mrs_fault st arI s a snd rcv rw ⦃ r => r.1.val = jMrRet pb [b, Sched.consumedUs y.scConsumed].length ∧
      MrJ (L := L) arI AR Z H Cs Ac Lst D a (Ipc.tmoSt σ sc y n) rcv xr pb r.2 [b, Sched.consumedUs y.scConsumed] ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hfr := (hI.1.toE.at_tcb hs hks).faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  have hrsc : rcv.bv ≠ sc.bv := fun e => by rw [e, hky] at hkr; cases hkr
  have hkr1 : (Ipc.tmoSt σ sc y n).kheap rcv.bv = some (.tcb xr) := by
    simp [Sched.updSc, Notif.updK, hrsc, hkr]
  unfold faults.set_mrs_fault
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
  refine WP.spec_bind (WP.spec_and (J.updConsumedJ hAT hmax htu hscC hs)
    (Ipc.update_consumed_irel (ar := arI) J.ip s a σ hI hscC hky hmax htu)) ?_
  rintro ⟨cv, s1⟩ ⟨⟨σ1, c1, he1, V1, J1⟩, -, hcv, he2, -⟩
  simp only at he1 J1 hcv he2
  have eσ : σ1 = Ipc.tmoSt σ sc y n := by
    have e := (Prod.mk.inj (he1.symm.trans he2)).1
    exact congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e)
  subst eσ
  have hM0 := MrJ.init (L := L) (arI := arI) (AR := AR) (Z := Z) (V := V1) J1 hkr1 pb
  refine WP.spec_bind (setMrJ hr hq hb hM0 0#u64 rfl (by decide) (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s2⟩ ⟨hk, hM1⟩
  simp only at hk hM1
  have hk1 : k.val = 1 := by rw [hk]; cases pb <;> rfl
  refine WP.spec_mono (setMrJ hr hq hb hM1 k (by rw [hk1]; rfl) (by omega) cv) ?_
  rintro ⟨k2, s3⟩ ⟨hk2, hM2⟩
  simp only at hk2 hM2 ⊢
  rw [hw0, hcv, List.nil_append, List.singleton_append] at hM2
  exact ⟨by rw [hk2, hk1]; rfl, hM2⟩

theorem jMrRet_eq_jLen (pb : Option Fl4Spec.ObjRef) {n : Nat} (h : n < 120) : jMrRet pb n = jLen pb n := by
  cases pb <;> simp only [jMrRet, jLen, Fl4Spec.msgMaxLength] <;> omega

/-- The spec's `do_fault_transfer`, into a buffer or not. -/
theorem doFaultTransfer_j {σ σm : Fl4Spec.State Unit} {snd rcv : Fl4Spec.ObjRef} {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σm.kheap rcv = some (.tcb xr)) {f : Fl4Spec.Fault}
    (hf : xs.tcbFault = some f) {label : Fl4Spec.Data} {ms : List Fl4Spec.Word}
    (hmsg : Fl4Spec.makeFaultMsg (Z := Unit) f snd σ = ({((label, ms), σm)}, False)) (pb : Option Fl4Spec.ObjRef)
    (hal : ∀ p, pb = some p → ∀ q ∈ Endp.mrPairs ms, (Endp.bufAddr p q.1).toNat % 8 = 0 ∧
      Fl4Spec.inUserFrame (Endp.bufAddr p q.1) σm) (badge : Fl4Spec.Data) :
    Fl4Spec.doFaultTransfer (Z := Unit) badge snd rcv pb σ =
      ({((), Notif.updK (jMrSt σm rcv xr pb ms) rcv (.tcb (Notif.setReg (Notif.setReg
        (Endp.withRegs xr (Endp.mrRegs xr.tcbArch.tcbContext.userRegs ms)) Fl4Spec.msg_info_register
        (Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (jLen pb ms.length), 0, 0, label⟩))
        Fl4Spec.badge_register badge)))}, False) := by
  cases pb with
  | none => exact Endp.doFaultTransfer_eqN hks hkr hf hmsg badge
  | some p => exact Endp.doFaultTransfer_eq hks hkr hf hmsg p (hal p rfl) badge

set_option maxHeartbeats 16000000 in
/-- **`do_fault_transfer` at `J`**, given that `set_mrs_fault` writes the
spec's fault message `ms` (from the state `σm` after `make_fault_msg`). -/
theorem doFaultXferJ {snd : U64} (hr : rcv ∈ Z.T) (hs : snd ∈ Z.T)
    (hne : snd.bv ≠ rcv.bv) {xs xr : Fl4Spec.Tcb} (hks : σ.kheap snd.bv = some (.tcb xs)) {f : Fl4Spec.Fault}
    (hf : xs.tcbFault = some f) {σm : Fl4Spec.State Unit} (hksm : σm.kheap snd.bv = some (.tcb xs))
    (hkrm : σm.kheap rcv.bv = some (.tcb xr))
    (hu : ∀ p, pb = some p → ∀ k, k < 128 → Fl4Spec.inUserFrame (Endp.bufAddr p k) σm)
    {label : Fl4Spec.Data} {ms : List Fl4Spec.Word}
    (hmsg : Fl4Spec.makeFaultMsg (Z := Unit) f snd.bv σ = ({((label, ms), σm)}, False)) (hlen : ms.length < 120)
    {lab : U64} (hlab0 : ∀ m : U64 → U64, FaultRel m snd xs.tcbFault → m (tFaultA snd) = lab)
    (hlab : lab.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits = label)
    {rw : U64} (hb : JBufR Z.B rw pb) (badge : U64)
    (hset : faults.set_mrs_fault st arI s a snd rcv rw ⦃ r => r.1.val = jMrRet pb ms.length ∧
      MrJ (L := L) arI AR Z H Cs Ac Lst D a σm rcv xr pb r.2 ms ⦄) :
    ipc.do_fault_transfer st arI s a badge snd rcv rw ⦃ s' => ∃ σ',
      Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv pb σ = ({((), σ')}, False) ∧
      (∀ q, q ≠ rcv.bv → σ'.kheap q = σm.kheap q) ∧
      (∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x' = { xr with tcbArch := x'.tcbArch }) ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ' ⦄ := by
  unfold ipc.do_fault_transfer
  refine WP.spec_bind hset ?_
  rintro ⟨sent, s1⟩ ⟨hn, hI1⟩
  simp only at hn hI1
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s1 snd) ?_
  rintro ft rfl
  rw [hlab0 _ (hI1.sndFault hs hne hksm)]
  unfold msginfo.MessageInfo.new
  apply ok_bind_spec
  have hsent : sent.val < 128 := by rw [hn]; cases pb <;> simp only [jMrRet] <;> omega
  refine WP.spec_bind (Endp.set_msg_info_spec (L := L) s1 rcv lab sent hsent) ?_
  rintro s2 ⟨v, rfl, hv⟩
  refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec _ rcv _ badge) ?_
  rintro s3 rfl
  obtain ⟨V1, J1⟩ := hI1
  have hEP := J1.xtop.fin.1.2.ep
  have hk1 := jMrSt_rcv σm rcv.bv xr pb ms
  set x1 := Endp.withRegs xr (Endp.mrRegs xr.tcbArch.tcbContext.userRegs ms) with hx1
  have hX2 := reg_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hr hk1 Fl4Spec.msg_info_register (by decide) v
  obtain ⟨V2, J2⟩ := J1.regWrJ hr hk1 Fl4Spec.msg_info_register v hX2
  rw [regIdx_msgInfo] at J2
  have hk2 : (Notif.updK (jMrSt σm rcv.bv xr pb ms) rcv.bv
      (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv))).kheap rcv.bv =
      some (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv)) := by simp [Notif.updK]
  have hX3 := badge_wr_irel J2.ip (J2.xtop.irelK J2.ks J2.buf) hr hk2 badge
  rw [badgeRegA_eq_regA] at hX3
  obtain ⟨V3, J3⟩ := J2.regWrJ hr hk2 Fl4Spec.badge_register badge hX3
  rw [regIdx_badge] at J3
  have hal : ∀ p, pb = some p → ∀ q ∈ Endp.mrPairs ms, (Endp.bufAddr p q.1).toNat % 8 = 0 ∧
      Fl4Spec.inUserFrame (Endp.bufAddr p q.1) σm := by
    intro p hp q hq
    have := (List.of_mem_zip hq).1
    simp at this
    rw [hp] at hb
    exact ⟨Endp.bufAddr_aligned hEP hb.2.1 _, hu p hp _ (by omega)⟩
  have hspec := doFaultTransfer_j hks hkrm hf hmsg pb hal badge.bv
  have hvx : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (jLen pb ms.length), 0, 0, label⟩ := by
    rw [hv, hlab, Endp.bv_ofNat_val sent (hn.trans (jMrRet_eq_jLen pb hlen))]; rfl
  have hfin : Notif.updK (Notif.updK (jMrSt σm rcv.bv xr pb ms) rcv.bv
      (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register v.bv) Fl4Spec.badge_register badge.bv)) =
      Notif.updK (jMrSt σm rcv.bv xr pb ms) rcv.bv (.tcb (Notif.setReg (Notif.setReg x1
        Fl4Spec.msg_info_register (Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (jLen pb ms.length), 0, 0, label⟩))
        Fl4Spec.badge_register badge.bv)) := by
    rw [hvx]; simp only [Notif.updK, Function.update_idem]
  refine ⟨_, hspec, fun q hq => ?_, ⟨Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register
      (Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (jLen pb ms.length), 0, 0, label⟩)) Fl4Spec.badge_register badge.bv,
    (by simp only [Notif.updK_kheap, Function.update_self]; try rfl), rfl⟩, V3, by rw [← hfin]; exact J3⟩
  simp only [Notif.updK_kheap, Function.update_of_ne hq]
  exact jMrSt_other _ _ _ _ _ hq

set_option maxHeartbeats 16000000 in
/-- **`do_ipc_transfer` of a faulted sender at `J`** (module docstring):
the receive buffer by `lookup_buf_full` (`BufWordRel`, `BufCover` [J]), the
fault branch, then `doFaultXferJ` with the fault type's `set_mrs_fault`.
The spec's outcome changes only the receiver's TCB (in its user context) and,
for a timeout with an SC, that SC. [P] `hAT`, `hmax`, `htu` (only for a
timeout with an SC). -/
theorem JAtZ.xferFaultJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) 
    {snd : U64} (hs : snd ∈ Z.T) (hr : rcv ∈ Z.T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) {f : Fl4Spec.Fault}
    (hf : xs.tcbFault = some f)
    (htmo : ∀ b sc, xs.tcbFault = some (.timeout b) → xs.tcbSchedContext = some sc →
      P0.ArchTotal arI ∧ Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (epo : Option Fl4Spec.ObjRef) (ep badge : U64) (grant : Bool) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv epo badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      (∀ q, q ≠ rcv.bv → (∀ b sc, xs.tcbFault = some (.timeout b) → xs.tcbSchedContext = some sc → q ≠ sc) →
        σ'.kheap q = σ.kheap q) ∧
      (∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x' = { xr with tcbArch := x'.tcbArch }) ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ' ⦄ := by
  have hne' : snd.bv ≠ rcv.bv := fun e => hne (P1.eq_of_bv e)
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hs hks
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have thT : ∀ t ∈ Z.T, Z.th t = some .tcb := fun t ht => (hJ.tcb t).2 (J.zH.1 t ht)
  obtain ⟨hOK, hBC, -⟩ := J.xferH
  obtain ⟨xr', hkr', hwr⟩ := J.buf rcv hr
  rw [hkr] at hkr'; cases hkr'
  have hspec : Fl4Spec.doIpcTransfer (Z := Unit) snd.bv epo badge.bv grant rcv.bv σ =
      Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv (Endp.ipcBufOf true xr) σ := by
    unfold Fl4Spec.doIpcTransfer
    rw [nd_bind_one (Endp.lookupIpcBuffer_eq hkr true), nd_bind_one (threadGet_eq _ hks), hf]
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 (thT rcv hr) hkr hOK true) ?_
  rintro rw ⟨hrw0, hrwp⟩
  have hb : JBufR Z.B rw (Endp.ipcBufOf true xr) := by
    cases hrb : Endp.ipcBufOf true xr with
    | none => exact hrw0.2 hrb
    | some rp =>
      have hrwv : rw.bv = rp := hrwp hwr rp hrb
      exact ⟨(fun e => by have := hrw0.1 e; rw [hrb] at this; cases this), hBC rcv hr xr true rp hkr hrb rw hrwv, hrwv⟩
  have hq : ∀ p, Endp.ipcBufOf true xr = some p → Endp.ipcBufOf true xr = some p := fun _ h => h
  have hu : ∀ p, Endp.ipcBufOf true xr = some p → ∀ k, k < 128 → Fl4Spec.inUserFrame (Endp.bufAddr p k) σ :=
    fun p h k hk => buf_frame_of_ok hOK hkr h k hk
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_
  rintro ft rfl
  have hft0 : ¬ L.mem s (tFaultA snd) = fl4_abi.consts.fault.NullFault := by
    intro h
    have : L.mem s (tFaultA snd) = 0#u64 := by rw [h]; unfold fl4_abi.consts.fault.NullFault; rfl
    rw [hxs.fault0.1 this] at hf; cases hf
  simp only [hft0, ↓reduceIte]
  rw [hspec]
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  -- the faults whose message reads no SC
  have hgen : ∀ {label : Fl4Spec.Data} {ms : List Fl4Spec.Word},
      Fl4Spec.makeFaultMsg (Z := Unit) f snd.bv σ = ({((label, ms), σ)}, False) → ms.length < 120 →
      ∀ (lab : U64), (∀ m : U64 → U64, FaultRel m snd xs.tcbFault → m (tFaultA snd) = lab) →
      lab.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits = label →
      faults.set_mrs_fault st arI s a snd rcv rw ⦃ r => r.1.val = jMrRet (Endp.ipcBufOf true xr) ms.length ∧
        MrJ (L := L) arI AR Z H Cs Ac Lst D a σ rcv xr (Endp.ipcBufOf true xr) r.2 ms ⦄ →
      ipc.do_fault_transfer st arI s a badge snd rcv rw ⦃ s' => ∃ σ',
        Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv (Endp.ipcBufOf true xr) σ = ({((), σ')}, False) ∧
        (∀ q, q ≠ rcv.bv → (∀ b sc, xs.tcbFault = some (.timeout b) → xs.tcbSchedContext = some sc → q ≠ sc) →
          σ'.kheap q = σ.kheap q) ∧
        (∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x' = { xr with tcbArch := x'.tcbArch }) ∧
        ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ' ⦄ :=
    fun hmsg hlen _ hlab0 hlab hset =>
      WP.spec_mono (doFaultXferJ hr hs hne' hks hf hks hkr hu hmsg hlen hlab0 hlab hb badge hset)
        fun _ ⟨σ', h1, h2, h3, h4⟩ => ⟨σ', h1, fun q hq _ => h2 q hq, h3, h4⟩
  cases f with
  | capFault c rp lf =>
    exact hgen (Endp.makeFaultMsg_cap hks c rp lf)
      (by have := Endp.msgFromLookupFailure_len lf; simp [Endp.capFaultMsg]; omega)
      1#u64 (fun m h => by unfold FaultRel at h; rw [hf] at h; exact h.1) (by rw [Endp.mask52]; decide)
      (setMrsFaultCapJ J hr hs hne' hks hkr hq hb hf)
  | unknownSyscallException n =>
    exact hgen (Endp.makeFaultMsg_unknown hks n) (by rw [Endp.usMsg_length]; omega)
      2#u64 (fun m h => by unfold FaultRel at h; rw [hf] at h; exact h.1) (by rw [Endp.mask52]; decide)
      (setMrsFaultUnknownJ J hr hs hne' hks hkr hq hb hf)
  | userException e c =>
    exact hgen (Endp.makeFaultMsg_user hks e c) (by rw [Endp.ueMsg_length]; omega)
      3#u64 (fun m h => by unfold FaultRel at h; rw [hf] at h; exact h.1) (by rw [Endp.mask52]; decide)
      (setMrsFaultUserJ J hr hs hne' hks hkr hq hb hf)
  | archFault af =>
    cases af with
    | vmFault va d =>
      have hd := hfr.2.2
      exact hgen (Endp.makeFaultMsg_vm hks va d) (by rw [hd]; simp [Endp.vmMsg])
        6#u64 (fun m h => by unfold FaultRel at h; rw [hf] at h; exact h.1) (by rw [Endp.mask52]; decide)
        (setMrsFaultVmJ J hr hs hks hkr hq hb hf)
  | timeout bb =>
    obtain ⟨Q, R0, hc, hsp⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨x0, hk0, -, -, hscw, -⟩ := hsp.tcb snd hs
    rw [hks] at hk0; cases hk0
    by_cases hscb : xs.tcbSchedContext = none
    · have hsc0 : L.mem s (P1.scA snd) = 0#u64 := by
        by_contra h
        have e := hscw
        rw [Notif.optRef_ne h, hscb] at e
        cases e
      exact hgen (Endp.makeFaultMsg_timeout hks hscb bb) (by simp)
        5#u64 (fun m h => by unfold FaultRel at h; rw [hf] at h; exact h.1) (by rw [Endp.mask52]; decide)
        (setMrsFaultTmoJ J hr hs hks hkr hq hb hf hsc0)
    · obtain ⟨scb, hscb⟩ := Option.ne_none_iff_exists'.1 hscb
      set sc := L.mem s (P1.scA snd) with hscdef
      obtain ⟨hsc0, hscbv⟩ := Notif.optRef_some (hscw.symm.trans hscb)
      have hscC := hsp.scMem snd hs hsc0
      obtain ⟨y, n, hky, -⟩ := hsp.scs sc hscC
      have hscx : xs.tcbSchedContext = some sc.bv := by rw [hscb, hscbv]
      obtain ⟨hAT, hmax, htu⟩ := htmo bb sc.bv hf hscx
      have hrsc : rcv.bv ≠ sc.bv := fun e => by rw [e, hky] at hkr; cases hkr
      have hssc : snd.bv ≠ sc.bv := fun e => by rw [e, hky] at hks; cases hks
      have hkm : ∀ q, q ≠ sc.bv → (Ipc.tmoSt σ sc y n).kheap q = σ.kheap q := fun q hq => by
        simp [Notif.updK, hq]
      have hksm : (Ipc.tmoSt σ sc y n).kheap snd.bv = some (.tcb xs) := by rw [hkm _ hssc]; exact hks
      have hkrm : (Ipc.tmoSt σ sc y n).kheap rcv.bv = some (.tcb xr) := by rw [hkm _ hrsc]; exact hkr
      have hu' : ∀ p, Endp.ipcBufOf true xr = some p → ∀ k, k < 128 →
          Fl4Spec.inUserFrame (Endp.bufAddr p k) (Ipc.tmoSt σ sc y n) := by
        intro p hp k hk
        obtain ⟨sz, hz⟩ := hu p hp k hk
        refine ⟨sz, ?_⟩
        have hne2 : Endp.bufAddr p k &&& ~~~(Fl4Spec.mask (Fl4Spec.pageBitsForSize sz)) ≠ sc.bv := by
          intro e'; rw [e', hky] at hz; cases hz
        simp [Sched.updSc, Notif.updK, hne2, hz]
      have hmsg := Ipc.makeFaultMsg_timeoutSC hks hscx (Ipc.schedContextUpdateConsumed_eq hky hmax) bb
      refine WP.spec_mono (doFaultXferJ hr hs hne' hks hf hksm hkrm hu' hmsg (by simp)
        (lab := 5#u64) (fun m h => by unfold FaultRel at h; rw [hf] at h; exact h.1) (by rw [Endp.mask52]; decide)
        hb badge (setMrsFaultTmoScJ J hAT hmax htu hr hs hks hkr hq hb hf rfl hsc0 hscC hky)) ?_
      rintro s' ⟨σ', h1, h2, h3, h4⟩
      refine ⟨σ', h1, fun q hq hqs => ?_, h3, h4⟩
      rw [h2 q hq, hkm q (hqs bb _ hf hscx)]

end

end

end Fl4Proofs.P3
