/-
P3 (DESIGN.md §9), IPC: **`do_ipc_transfer` at `J`** (toward XTopJointIpcJ's
`JSendRestHyp` and `JReplyRestHyp`): FL4's message transfer from `JAtZ`
before to `JAtZ` after, against the spec's `do_ipc_transfer`, one J step per
word written (as XTopJointReadRegs' copy loops).

* `copyMrsJ_loop0`: `copy_mrs`' first loop (the sender's message registers
  into the receiver's, `MR0`..`MR3`), each word by `JAtZ.regWrJ` with
  `reg_wr_irel`; the spec's receiver grows by `copyRegsTcb` over the
  registers copied so far (`copyRegs_take_succ`). The sender's registers are
  read through the endpoint relation at the current `J` state.
* `JAtZ.xferRegsJ`: the register-only transfer (the receiver without an IPC
  buffer, the sender without a fault, no extra caps looked up; IpcBuf's
  `lookup_buf_full` at `J` with `IpcBufCapOK` [J, l4v
  `valid_ipc_buffer_cap`]), then the message info (`JAtZ.regWrJ`) and the
  badge (`badge_wr_irel`); the spec's outcome is EpXferSpec's
  `doIpcTransfer_regs` (`updK … (xferTcb xr xs badge)`), for any endpoint
  argument of the spec (the reply transfer passes none).
* `copyMrsJ_loop1`: `copy_mrs`' second loop (the sender's buffer words
  `5 .. n` into the receiver's buffer), each word by `JAtZ.userWrJ` with
  `JAtZ.bufWord`, the spec's memory growing by `copyBufMem`.
* `JAtZ.xferBufJ`: the transfer into a receive buffer (the sender without a
  fault, no extra caps): the buffers by `lookup_buf_full` with `BufWordRel`
  and `BufCover` [J], the two loops, the message info and the badge; the
  spec's outcome is EpBufSpec's `doIpcTransfer_recvBuf` (its receive slots by
  `get_receive_slot_top` at the `J` state after the copy).
* `JAtZ.xferJ`: the two by the receiver's buffer, the spec's outcome
  changing only the receiver's TCB, in its user context (for the callers:
  the send to a receiver, the reply transfer).

Not covered here (the rest of `do_ipc_transfer` at `J`): a faulted sender
(`do_fault_transfer`, IpcEpXfer's `do_ipc_transfer_faultI`/`_faultNI` at
`IRel`), and a granted transfer with extra caps (`transfer_caps` inserting
into the receiver's CNode slot, IpcGrantX's `do_ipc_transfer_grant`).
-/
import Fl4Proofs.P3.XTopJointReadRegs
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- One more message register copied. -/
theorem copyRegs_take_succ (x : Fl4Spec.Tcb) (vals : Fl4Spec.Register → Fl4Spec.Word) (i : Nat) (hi : i < 4) :
    Endp.copyRegsTcb x vals (Fl4Spec.msgRegisters.take (i + 1)) =
      Notif.setReg (Endp.copyRegsTcb x vals (Fl4Spec.msgRegisters.take i)) (Endp.mrIdx i) (vals (Endp.mrIdx i)) := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem msgRegs_take_min (n : Nat) : Fl4Spec.msgRegisters.take (min n 4) = Fl4Spec.msgRegisters.take n := by
  by_cases h : n ≤ 4
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), Endp.take_four 4 (le_refl _), Endp.take_four n (by omega)]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- The sender's register read at a `J` state where its TCB is `xs`. -/
theorem JAtZ.regRead (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (r : Fl4Spec.Register) :
    (L.mem s (regA t (regIdx r))).bv = x.tcbArch.tcbContext.userRegs r :=
  ((J.xtop.irelK J.ks J.buf).1.toE.at_tcb ht hk).regs r

set_option maxHeartbeats 8000000 in
/-- **`copy_mrs`' first loop at `J`** (module docstring). -/
theorem copyMrsJ_loop0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {snd rcv : U64} (hs : snd ∈ Z.T)
    (hr : rcv ∈ Z.T) (hne : snd.bv ≠ rcv.bv) {xs xr : Fl4Spec.Tcb} (hks : σ.kheap snd.bv = some (.tcb xs))
    (hkr : σ.kheap rcv.bv = some (.tcb xr)) (n : U64) :
    msg.copy_mrs_loop0 st s snd rcv n 0#u64 ⦃ r => r.2.val = min n.val 4 ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D r.1 a
        (Notif.updK σ rcv.bv (.tcb (Endp.copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
          (Fl4Spec.msgRegisters.take n.val)))) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  unfold msg.copy_mrs_loop0
  apply loop.spec_decr_nat (measure := fun x => 4 - x.2.val)
    (inv := fun x => x.2.val ≤ 4 ∧ x.2.val ≤ n.val ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D x.1 a
        (Notif.updK σ rcv.bv (.tcb (Endp.copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
          (Fl4Spec.msgRegisters.take x.2.val)))))
  · rintro ⟨s', i⟩ ⟨hi4, hin, V', J'⟩
    unfold msg.copy_mrs_loop0.body
    simp only at hi4 hin J' ⊢
    have hks' : (Notif.updK σ rcv.bv (.tcb (Endp.copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
        (Fl4Spec.msgRegisters.take i.val)))).kheap snd.bv = some (.tcb xs) := by
      simp [Notif.updK, hne, hks]
    have hkr' : (Notif.updK σ rcv.bv (.tcb (Endp.copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
        (Fl4Spec.msgRegisters.take i.val)))).kheap rcv.bv = some (.tcb (Endp.copyRegsTcb xr
          xs.tcbArch.tcbContext.userRegs (Fl4Spec.msgRegisters.take i.val))) := by
      simp [Notif.updK]
    by_cases h1 : i < n
    · simp only [h1, ↓reduceIte]
      by_cases h2 : i < msg.N_MSG_REGISTERS
      · have hi : i.val < 4 := by have := (P1.gt_iff_val).1 h2; omega
        simp only [h2, ↓reduceIte]
        refine WP.spec_bind (Endp.msg_register_spec i hi) ?_
        rintro r rfl
        refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' snd _) ?_
        rintro v rfl
        refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s' rcv _ _) ?_
        rintro s2 rfl
        obtain ⟨i2, h2e, h2v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
        rw [h2e, bind_ok, WP.spec_ok]
        have hi2 : i2.val = i.val + 1 := by simpa using h2v
        have hX := reg_wr_irel J'.ip (J'.xtop.irelK J'.ks J'.buf) hr hkr' (Endp.mrIdx i.val)
          (mrIdx_ne_badge _) (L.mem s' (regA snd (regIdx (Endp.mrIdx i.val))))
        obtain ⟨V2, J2⟩ := J'.regWrJ hr hkr' (Endp.mrIdx i.val) _ hX
        have hv := J'.regRead hs hks' (Endp.mrIdx i.val)
        refine ⟨⟨show i2.val ≤ 4 by omega, show i2.val ≤ n.val by have := (P1.gt_iff_val).1 h1; omega, V2, ?_⟩, by show 4 - i2.val < 4 - i.val; omega⟩
        simp only
        rw [hi2, copyRegs_take_succ _ _ _ hi]
        have e : Notif.updK (Notif.updK σ rcv.bv (.tcb (Endp.copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
            (Fl4Spec.msgRegisters.take i.val)))) rcv.bv (.tcb (Notif.setReg (Endp.copyRegsTcb xr
              xs.tcbArch.tcbContext.userRegs (Fl4Spec.msgRegisters.take i.val)) (Endp.mrIdx i.val)
              (L.mem s' (regA snd (regIdx (Endp.mrIdx i.val)))).bv)) =
            Notif.updK σ rcv.bv (.tcb (Notif.setReg (Endp.copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
              (Fl4Spec.msgRegisters.take i.val)) (Endp.mrIdx i.val)
              (xs.tcbArch.tcbContext.userRegs (Endp.mrIdx i.val)))) := by
          rw [hv]; simp only [Notif.updK, Function.update_idem]
        rw [← e]; exact J2
      · simp only [h2, ↓reduceIte, WP.spec_ok]
        have hi : i.val = 4 := by
          have h2' : ¬ i.val < 4 := fun h => h2 ((P1.gt_iff_val).2 (by rw [hN]; exact h))
          omega
        have hn4 : 4 ≤ n.val := by have := (P1.gt_iff_val).1 h1; omega
        refine ⟨by omega, V', ?_⟩
        have e : Fl4Spec.msgRegisters.take n.val = Fl4Spec.msgRegisters.take i.val := by
          rw [Endp.take_four n.val hn4, Endp.take_four i.val (by omega)]
        rw [e]; exact J'
    · simp only [h1, ↓reduceIte, WP.spec_ok]
      have hni : i.val = n.val := by
        have : ¬ i.val < n.val := fun h => h1 ((P1.gt_iff_val).2 h)
        omega
      refine ⟨by omega, V', ?_⟩
      rw [← hni]; exact J'
  · refine ⟨by simp, by simp, Z.vs, ?_⟩
    show JAtZ (L := L) arI AR (Z.mv Z.G Z.vs) H Cs Ac Lst D s a (Notif.updK σ rcv.bv (.tcb xr))
    rw [Endp.updK_self hkr]; simpa using J

set_option maxHeartbeats 8000000 in
/-- **`copy_mrs` without a receive buffer at `J`**: only the first loop. -/
theorem copyMrsJ_norecv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {snd rcv : U64} (hs : snd ∈ Z.T)
    (hr : rcv ∈ Z.T) (hne : snd.bv ≠ rcv.bv) {xs xr : Fl4Spec.Tcb} (hks : σ.kheap snd.bv = some (.tcb xs))
    (hkr : σ.kheap rcv.bv = some (.tcb xr)) (sb n : U64) :
    msg.copy_mrs st s snd sb rcv 0#u64 n ⦃ r => r.1.val = min n.val 4 ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D r.2 a
        (Notif.updK σ rcv.bv (.tcb (Endp.copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
          (Fl4Spec.msgRegisters.take n.val)))) ⦄ := by
  unfold msg.copy_mrs
  refine WP.spec_bind (copyMrsJ_loop0 J hs hr hne hks hkr n) ?_
  rintro ⟨s1, i⟩ h
  simp only [↓reduceIte]
  show (ok (i, s1)) ⦃ _ ⦄
  simp only [WP.spec_ok]
  exact h

set_option maxHeartbeats 16000000 in
/-- **The register-only `do_ipc_transfer` at `J`** (module docstring). -/
theorem JAtZ.xferRegsJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hOK : Endp.IpcBufCapOK σ)
    {snd rcv : U64} (hs : snd ∈ Z.T) (hr : rcv ∈ Z.T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (hrb : Endp.ipcBufOf true xr = none) (epo : Option Fl4Spec.ObjRef) (ep badge : U64) (grant : Bool)
    (hcaps : grant = false ∨ Endp.ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' =>
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv epo badge.bv grant rcv.bv σ =
        ({((), Notif.updK σ rcv.bv (.tcb (Endp.xferTcb xr xs badge.bv)))}, False) ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a
        (Notif.updK σ rcv.bv (.tcb (Endp.xferTcb xr xs badge.bv))) ⦄ := by
  have hne' : snd.bv ≠ rcv.bv := fun e => hne (P1.eq_of_bv e)
  have hspec := Endp.doIpcTransfer_regs hne' hks hkr hf hrb epo badge.bv grant hcaps
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hs hks
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have thT : ∀ t ∈ Z.T, Z.th t = some .tcb := fun t ht => (hJ.tcb t).2 (J.zH.1 t ht)
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv =
      xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 (thT rcv hr) hkr hOK true) ?_
  rintro rb ⟨hrb0, -⟩
  have hrb' : rb = 0#u64 := hrb0.2 hrb
  subst hrb'
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_
  rintro ft rfl
  have hft0 : L.mem s (tFaultA snd) = fl4_abi.consts.fault.NullFault := by
    rw [hxs.fault0.2 hf]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hft0, ↓reduceIte]
  refine WP.spec_bind (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 (thT snd hs) hks hOK false) ?_
  rintro sb ⟨hsb, -⟩
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (Endp.msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, hext, hle⟩
  have hex : (if grant = true then (do
        let r ← ipc.lookup_extra_caps st s snd sb tag
        match r with
        | core.result.Result.Ok e => ok e
        | core.result.Result.Err _ => ok ipc.NO_EXTRA_CAPS)
      else ok ipc.NO_EXTRA_CAPS) ⦃ _ => True ⦄ := by
    cases grant with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      have hc : sb = 0#u64 ∨ tag.extra_caps = 0#u64 := by
        rcases hcaps with h | h | h
        · cases h
        · exact Or.inl (hsb.2 h)
        · right; apply P1.eq_of_bv; rw [hext, hwmi]; apply BitVec.eq_of_toNat_eq; exact h
      refine WP.spec_bind (Endp.lookup_extra_caps_nil s snd sb tag hc) ?_
      rintro r -
      split <;> simp
  refine WP.spec_bind hex ?_
  rintro extra -
  refine WP.spec_bind (copyMrsJ_norecv J hs hr hne' hks hkr sb tag.length) ?_
  rintro ⟨i, s1⟩ ⟨hi, V1, J1⟩
  refine WP.spec_bind (Endp.transfer_caps_norecv (L := L) s1 tag extra ep rcv) ?_
  rintro ⟨out, s2⟩ hout
  simp only [Prod.mk.injEq] at hout
  obtain ⟨rfl, h2⟩ := hout
  subst s2
  show (do
    let s3 ← msg.set_msg_info st s1 rcv
      { label := tag.label, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := i }
    obj.Tcb.set_reg st rcv s3 layout.reg.BADGE badge) ⦃ _ ⦄
  have hi4 : i.val ≤ 4 := by rw [hi]; omega
  refine WP.spec_bind (Endp.set_msg_info_spec (L := L) s1 rcv tag.label i (by omega)) ?_
  rintro s3 ⟨v, rfl, hv⟩
  refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec _ rcv _ badge) ?_
  rintro s4 rfl
  -- the spec's message info
  set w := xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register with hwdef
  have hLv : Fl4Spec.unat (Fl4Spec.dataToMessageInfo w).miLength = tag.length.val := by
    show _ = tag.length.bv.toNat
    rw [hlen, hwmi]
  have hvx : v.bv = Fl4Spec.messageInfoToData (Endp.xferInfo w) := by
    rw [hv]
    unfold Endp.xferInfo
    congr 1
    congr 1
    · exact Endp.xfer_len (by rw [hi]; show _ = min (Fl4Spec.unat _) 4; rw [hLv])
    · rw [hlab, hwmi]; rfl
  set x1 := Endp.copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take
    (Fl4Spec.unat (Fl4Spec.dataToMessageInfo w).miLength)) with hx1
  rw [← hLv] at J1
  change JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac Lst D s1 a (Notif.updK σ rcv.bv (.tcb x1)) at J1
  have hkr1 : (Notif.updK σ rcv.bv (.tcb x1)).kheap rcv.bv = some (.tcb x1) := by simp [Notif.updK]
  -- the message info
  have hX2 := reg_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hr hkr1 Fl4Spec.msg_info_register (by decide) v
  obtain ⟨V2, J2⟩ := J1.regWrJ hr hkr1 Fl4Spec.msg_info_register v hX2
  rw [regIdx_msgInfo] at J2
  have hkr2 : (Notif.updK (Notif.updK σ rcv.bv (.tcb x1)) rcv.bv
      (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv))).kheap rcv.bv =
      some (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv)) := by simp [Notif.updK]
  -- the badge
  have hX3 := badge_wr_irel J2.ip (J2.xtop.irelK J2.ks J2.buf) hr hkr2 badge
  rw [badgeRegA_eq_regA] at hX3
  obtain ⟨V3, J3⟩ := J2.regWrJ hr hkr2 Fl4Spec.badge_register badge hX3
  rw [regIdx_badge] at J3
  have hfin : Notif.updK (Notif.updK (Notif.updK σ rcv.bv (.tcb x1)) rcv.bv
      (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register v.bv) Fl4Spec.badge_register badge.bv)) =
      Notif.updK σ rcv.bv (.tcb (Endp.xferTcb xr xs badge.bv)) := by
    simp only [Notif.updK, Function.update_idem]
    rw [hvx]; rfl
  refine ⟨hspec, V3, ?_⟩
  rw [← hfin]; exact J3

set_option maxHeartbeats 8000000 in
/-- **`copy_mrs`' second loop at `J`**: the sender's buffer words `5 .. n`
into the receiver's buffer, each by `JAtZ.userWrJ` (the word apart from `H`'s
objects and inside the receiver's frame, `JAtZ.bufWord`; `BufPlaced` [J]);
the sender's word read through the endpoint relation's buffer words. -/
theorem copyMrsJ_loop1 {σ1 : Fl4Spec.State Unit}
    {rcv : U64} (hrT : Z.th rcv = some .tcb) {x1 : Fl4Spec.Tcb} (hk1 : σ1.kheap rcv.bv = some (.tcb x1))
    {rp sp : Fl4Spec.Word} (hq : Endp.ipcBufOf true x1 = some rp) {sw rw : U64} (hmr : Endp.BufMap Z.B rw rp)
    (hrw : rw.bv = rp) (hms : Endp.BufMap Z.B sw sp) (n i0 : U64) (hn : n.val ≤ 120)
    (hi0 : i0.val = min n.val 4) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ1) :
    msg.copy_mrs_loop1 st s sw rw n i0 ⦃ r => r.1.val = n.val ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D r.2 a
        (Endp.setUm σ1 (Endp.copyBufMem σ1.machineState.underlyingMemory sp rp (List.range' 5 (n.val - 4)))) ⦄ := by
  unfold msg.copy_mrs_loop1
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.val)
    (inv := fun x => i0.val ≤ x.2.val ∧ x.2.val ≤ n.val ∧ ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D x.1 a
      (Endp.setUm σ1 (Endp.copyBufMem σ1.machineState.underlyingMemory sp rp (List.range' 5 (x.2.val - 4)))))
  · rintro ⟨s', i⟩ ⟨h1, h2, V', J'⟩
    unfold msg.copy_mrs_loop1.body
    simp only at h1 h2 J' ⊢
    by_cases hc1 : i < n
    · have hlt : i.val < n.val := (P1.gt_iff_val).1 hc1
      have h4 : 4 ≤ i.val := by omega
      have hmax : msg.MSG_MAX_LENGTH.val = 120 := by unfold msg.MSG_MAX_LENGTH; rfl
      have hc2 : i < msg.MSG_MAX_LENGTH := (P1.gt_iff_val).2 (by rw [hmax]; omega)
      simp only [hc1, hc2, ↓reduceIte]
      obtain ⟨i1, h1e, h1v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
      rw [h1e, bind_ok]
      have hi1v : i1.val = i.val + 1 := by simpa using h1v
      refine WP.spec_bind (Endp.msg.buf_get.spec s' sw i1) ?_
      rintro v rfl
      refine WP.spec_bind (Endp.msg.buf_set.spec s' rw i1 _) ?_
      rintro s1 rfl
      rw [WP.spec_ok]
      set um' := Endp.copyBufMem σ1.machineState.underlyingMemory sp rp (List.range' 5 (i.val - 4)) with hum'
      have hwr := hmr i1 (by omega)
      have hws := hms i1 (by omega)
      obtain ⟨hOK', -, hBP'⟩ := J'.xferH
      have hvb : (L.mem s' (Endp.fl4BufA sw i1)).bv = Endp.loadWordAt um' (Endp.bufAddr sp i1.val) :=
        (J'.xtop.irelK J'.ks J'.buf).1.toE.buf _ hws
      obtain ⟨hAp, hObj⟩ := J'.bufWord hOK' hrT hk1 hq i1.val (by omega) (b := Endp.fl4BufA rw i1)
        (by rw [fl4BufA_bv, hrw])
      have J2 := J'.userWrJ hBP' hwr hAp hObj (L.mem s' (Endp.fl4BufA sw i1))
      have hlist : List.range' 5 (i1.val - 4) = List.range' 5 (i.val - 4) ++ [i1.val] := by
        rw [show i1.val - 4 = (i.val - 4) + 1 by omega, Endp.range'_snoc5]; congr 2; omega
      refine ⟨⟨show i0.val ≤ i1.val by omega, show i1.val ≤ n.val by omega, V', ?_⟩,
        by show n.val - i1.val < n.val - i.val; omega⟩
      dsimp only
      rw [hlist, Endp.copyBufMem_snoc, ← hum', ← hvb]
      exact J2
    · simp only [hc1, ↓reduceIte, WP.spec_ok]
      have : i.val = n.val := by have : ¬ i.val < n.val := fun h => hc1 ((P1.gt_iff_val).2 h); omega
      refine ⟨this, V', ?_⟩
      rw [← this]; exact J'
  · dsimp only
    refine ⟨le_refl _, by omega, Z.vs, ?_⟩
    rw [show i0.val - 4 = 0 by omega]
    have e : Endp.setUm σ1 (Endp.copyBufMem σ1.machineState.underlyingMemory sp rp (List.range' 5 0)) = σ1 := rfl
    rw [e]; simpa using J

set_option maxHeartbeats 16000000 in
/-- **`do_ipc_transfer` into a receive buffer at `J`** (the sender without a
fault, no extra caps looked up): the receiver's buffer by `lookup_buf_full`
with `BufWordRel` and `BufCover` [J], the sender's buffer likewise (none, or
mapped), `copy_mrs` (`copyMrsJ_loop0`, then `copyMrsJ_loop1` when the sender
has a buffer), no cap transferred (`transfer_caps_noextra`), the message info
and the badge (`JAtZ.regWrJ`). The spec's outcome is EpBufSpec's
`doIpcTransfer_recvBuf`, its receive slots by `get_receive_slot_top` at the
`J` state after the copy. -/
theorem JAtZ.xferBufJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {snd rcv : U64} (hs : snd ∈ Z.T) (hr : rcv ∈ Z.T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rp : Fl4Spec.ObjRef} (hrb : Endp.ipcBufOf true xr = some rp) (epo : Option Fl4Spec.ObjRef) (ep badge : U64)
    (grant : Bool)
    (hcaps : grant = false ∨ Endp.ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv epo badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      (∀ p, p ≠ rcv.bv → σ'.kheap p = σ.kheap p) ∧
      (∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x' = { xr with tcbArch := x'.tcbArch }) ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ' ⦄ := by
  have hne' : snd.bv ≠ rcv.bv := fun e => hne (P1.eq_of_bv e)
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hs hks
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have thT : ∀ t ∈ Z.T, Z.th t = some .tcb := fun t ht => (hJ.tcb t).2 (J.zH.1 t ht)
  obtain ⟨hOK, hBC, -⟩ := J.xferH
  have hEP := J.xtop.fin.1.2.ep
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv =
      xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  obtain ⟨xr', hkr', hwr⟩ := J.buf rcv hr
  rw [hkr] at hkr'; cases hkr'
  obtain ⟨xs', hks', hws⟩ := J.buf snd hs
  rw [hks] at hks'; cases hks'
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 (thT rcv hr) hkr hOK true) ?_
  rintro rw ⟨hrw0, hrwp⟩
  have hrwv : rw.bv = rp := hrwp hwr rp hrb
  have hmr : Endp.BufMap Z.B rw rp := hBC rcv hr xr true rp hkr hrb rw hrwv
  have hrwn : rw ≠ 0#u64 := fun e => by have := hrw0.1 e; rw [hrb] at this; cases this
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s snd) ?_
  rintro ft rfl
  have hft0 : L.mem s (tFaultA snd) = fl4_abi.consts.fault.NullFault := by
    rw [hxs.fault0.2 hf]; unfold fl4_abi.consts.fault.NullFault; rfl
  simp only [hft0, ↓reduceIte]
  refine WP.spec_bind (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 (thT snd hs) hks hOK false) ?_
  rintro sw ⟨hsw0, hswp⟩
  have hsw : (Endp.ipcBufOf false xs = none ∧ sw = 0#u64) ∨
      (∃ sp, Endp.ipcBufOf false xs = some sp ∧ sw ≠ 0#u64 ∧ Endp.BufMap Z.B sw sp) := by
    cases h : Endp.ipcBufOf false xs with
    | none => exact Or.inl ⟨rfl, hsw0.2 h⟩
    | some sp =>
      exact Or.inr ⟨sp, rfl, (fun e => by have := hsw0.1 e; rw [h] at this; cases this),
        hBC snd hs xs false sp hks h sw (hswp hws sp h)⟩
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (Endp.msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, hext, hle⟩
  have hex : (if grant = true then (do
        let r ← ipc.lookup_extra_caps st s snd sw tag
        match r with
        | core.result.Result.Ok e => ok e
        | core.result.Result.Err _ => ok ipc.NO_EXTRA_CAPS)
      else ok ipc.NO_EXTRA_CAPS) ⦃ e => e = ipc.NO_EXTRA_CAPS ⦄ := by
    cases grant with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      have hc : sw = 0#u64 ∨ tag.extra_caps = 0#u64 := by
        rcases hcaps with h | h | h
        · cases h
        · rcases hsw with ⟨-, h'⟩ | ⟨sp, h', -⟩
          · exact Or.inl h'
          · rw [h] at h'; cases h'
        · right; apply P1.eq_of_bv; rw [hext, hwmi]; apply BitVec.eq_of_toNat_eq; exact h
      refine WP.spec_bind (Endp.lookup_extra_caps_none s snd sw tag hc) ?_
      rintro r rfl
      simp
  refine WP.spec_bind hex ?_
  rintro extra rfl
  -- `copy_mrs`
  have hun : Fl4Spec.unat tag.length.bv = tag.length.val := rfl
  set x1 := Endp.copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take tag.length.val)
    with hx1
  have hcm : msg.copy_mrs st s snd sw rcv rw tag.length ⦃ r => ∃ σc,
      Fl4Spec.copyMrs (Z := Unit) snd.bv (Endp.ipcBufOf false xs) rcv.bv (some rp) tag.length.bv σ =
        ({(r.1.bv, σc)}, False) ∧
      σc.kheap = Function.update σ.kheap rcv.bv (some (.tcb x1)) ∧ r.1.val ≤ 120 ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D r.2 a σc ⦄ := by
    unfold msg.copy_mrs
    refine WP.spec_bind (copyMrsJ_loop0 J hs hr hne' hks hkr tag.length) ?_
    rintro ⟨s1, i⟩ ⟨hi, V1, J1⟩
    simp only [hrwn, ↓reduceIte]
    rcases hsw with ⟨hsn, rfl⟩ | ⟨sp, hsp, hsw0', hms⟩
    · simp only [↓reduceIte]
      show (ok (i, s1)) ⦃ _ ⦄
      simp only [WP.spec_ok]
      refine ⟨Notif.updK σ rcv.bv (.tcb x1), ?_, rfl, by rw [hi]; omega, V1, J1⟩
      rw [hsn, Endp.copyMrs_noSendBuf hne' hks hkr _ _, hun]
      congr
      exact (Endp.xfer_len (by rw [hi]; rfl)).symm
    · simp only [hsw0', ↓reduceIte]
      have hk1 : (Notif.updK σ rcv.bv (.tcb x1)).kheap rcv.bv = some (.tcb x1) := by simp [Notif.updK]
      have hq1 : Endp.ipcBufOf true x1 = some rp := by rw [hx1, Endp.ipcBufOf_copyRegs]; exact hrb
      refine WP.spec_mono (copyMrsJ_loop1 (Z := Z.mv Z.G V1) (thT rcv hr)
        hk1 hq1 hmr hrwv hms tag.length i hle hi J1) ?_
      rintro ⟨n2, s2⟩ ⟨hn2, V2, J2⟩
      refine ⟨Endp.setUm (Notif.updK σ rcv.bv (.tcb x1)) (Endp.copyBufMem σ.machineState.underlyingMemory sp rp
        (List.range' 5 (tag.length.val - 4))), ?_, rfl, by show n2.val ≤ 120; rw [hn2]; exact hle, V2, J2⟩
      rw [hsp, Endp.copyMrs_bufs hne' hks hkr sp rp tag.length.bv ?_]
      · have e : n2 = tag.length := UScalar.eq_of_val_eq hn2
        subst e
        rw [← Endp.xfer_len_buf hle, Endp.bufIdx_eq, hun]
      · intro x hx
        rw [Endp.bufIdx_eq] at hx
        have hx' : x < 128 := by simp at hx; omega
        exact ⟨Endp.bufAddr_aligned hEP hms x, Endp.bufAddr_aligned hEP hmr x, buf_frame_of_ok hOK hkr hrb x hx'⟩
  refine WP.spec_bind hcm ?_
  rintro ⟨n, s1⟩ ⟨σc, hcopy, hkcf, hn, V1, J1⟩
  simp only at hcopy hkcf hn J1
  have hkc : σc.kheap rcv.bv = some (.tcb x1) := by rw [hkcf]; simp
  refine WP.spec_bind (Endp.transfer_caps_noextra (L := L) s1 tag ep rcv rw) ?_
  rintro ⟨out, s2⟩ hout
  simp only [Prod.mk.injEq] at hout
  obtain ⟨rfl, h2⟩ := hout
  subst s2
  show (do
    let s3 ← msg.set_msg_info st s1 rcv
      { label := tag.label, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := n }
    obj.Tcb.set_reg st rcv s3 layout.reg.BADGE badge) ⦃ _ ⦄
  refine WP.spec_bind (Endp.set_msg_info_spec (L := L) s1 rcv tag.label n (by omega)) ?_
  rintro s3 ⟨v, rfl, hv⟩
  refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec _ rcv _ badge) ?_
  rintro s4 rfl
  set w := xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register with hwdef
  have hlenw : tag.length.bv = (Fl4Spec.dataToMessageInfo w).miLength := by rw [hlen, hwmi]
  -- the receive slots
  have hI1 := J1.xtop.irelK J1.ks J1.buf
  obtain ⟨⟨G1, hB1⟩, -⟩ := hI1.2.1
  obtain ⟨dest, sl, hsl, -⟩ := WP.spec_exists (Ipc.get_receive_slot_top J1.ip hB1 hI1.1.toE (thT rcv hr) hmr hrwn []
    (Aeneas.Std.Array.repeat 3#usize 0#u64))
  rw [hlenw] at hcopy
  have hspec := Endp.doIpcTransfer_recvBuf hks hkr hf hrb epo badge.bv grant hcaps hcopy hkc hsl
  -- the message info
  have hX2 := reg_wr_irel J1.ip hI1 hr hkc Fl4Spec.msg_info_register (by decide) v
  obtain ⟨V2, J2⟩ := J1.regWrJ hr hkc Fl4Spec.msg_info_register v hX2
  rw [regIdx_msgInfo] at J2
  have hkc2 : (Notif.updK σc rcv.bv (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv))).kheap rcv.bv =
      some (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv)) := by simp [Notif.updK]
  -- the badge
  have hX3 := badge_wr_irel J2.ip (J2.xtop.irelK J2.ks J2.buf) hr hkc2 badge
  rw [badgeRegA_eq_regA] at hX3
  obtain ⟨V3, J3⟩ := J2.regWrJ hr hkc2 Fl4Spec.badge_register badge hX3
  rw [regIdx_badge] at J3
  have hvx : v.bv = Fl4Spec.messageInfoToData ⟨n.bv, 0, 0, (Fl4Spec.dataToMessageInfo w).miLabel⟩ := by
    rw [hv]; congr 2; rw [hlab, hwmi]; rfl
  have hfin : Notif.updK (Notif.updK σc rcv.bv (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register v.bv) Fl4Spec.badge_register badge.bv)) =
      Notif.updK σc rcv.bv (.tcb (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register
        (Fl4Spec.messageInfoToData ⟨n.bv, 0, 0, (Fl4Spec.dataToMessageInfo w).miLabel⟩))
        Fl4Spec.badge_register badge.bv)) := by
    simp only [Notif.updK, Function.update_idem]; rw [hvx]
  refine ⟨_, hspec, ?_, ⟨Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register
    (Fl4Spec.messageInfoToData ⟨n.bv, 0, 0, (Fl4Spec.dataToMessageInfo w).miLabel⟩)) Fl4Spec.badge_register badge.bv,
    (by simp only [Notif.updK_kheap, Function.update_self]; try rfl), ?_⟩, V3, by rw [← hfin]; exact J3⟩
  · intro p hp
    simp [Notif.updK, Function.update_of_ne hp, hkcf]
  · rw [hx1, Endp.copyRegsTcb_other]; rfl

set_option maxHeartbeats 8000000 in
/-- **`do_ipc_transfer` at `J`, the sender without a fault and no extra caps
looked up**: `JAtZ.xferRegsJ` or `JAtZ.xferBufJ` by the receiver's buffer;
the spec's outcome changes only the receiver's TCB, in its user context. -/
theorem JAtZ.xferJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {snd rcv : U64} (hs : snd ∈ Z.T) (hr : rcv ∈ Z.T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (epo : Option Fl4Spec.ObjRef) (ep badge : U64) (grant : Bool)
    (hcaps : grant = false ∨ Endp.ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) :
    ipc.do_ipc_transfer st arI s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv epo badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      (∀ p, p ≠ rcv.bv → σ'.kheap p = σ.kheap p) ∧
      (∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x' = { xr with tcbArch := x'.tcbArch }) ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s' a σ' ⦄ := by
  cases hrb : Endp.ipcBufOf true xr with
  | none =>
    refine WP.spec_mono (J.xferRegsJ (J.xferH).1 hs hr hne hks hkr hf hrb epo ep badge grant hcaps) ?_
    rintro s' ⟨h1, V, J'⟩
    refine ⟨_, h1, fun p hp => by simp [Notif.updK, hp], ⟨Endp.xferTcb xr xs badge.bv,
      (by simp only [Notif.updK_kheap, Function.update_self]), ?_⟩, V, J'⟩
    simp only [Endp.xferTcb]
    rw [Endp.copyRegsTcb_other]
    rfl
  | some rp => exact J.xferBufJ hs hr hne hks hkr hf hrb epo ep badge grant hcaps

end

end

end Fl4Proofs.P3

