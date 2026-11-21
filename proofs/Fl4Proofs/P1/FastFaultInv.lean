/-
# The fault fast path's reads from the entry state (FL4 #56, m61 (d))

m58–m60 proved an accepted `fastpath.fault` run ends where `handle_fault` +
`finish` ends, given the general path's reads at the states it reaches
(`FaultOK`: m58 `FaultReads`, m59 `UsOff`, m60 `FinReads`). This module
derives those reads from facts at the entry state through frame lemmas:

* the footprint of the fault message (`set_mrs_fault_rg`: an UnknownSyscall
  fault writes only the receiver's user context and IPC-buffer words,
  `XferRegW T U`), with the transfer's register writes (`set_msg_info`,
  `BADGE`);
* a read is kept by every write of the run whose address differs
  (`mem_wr_ne'`), the addresses being words of distinct objects (TCBs at
  4K-aligned bases, the node, endpoints, replies, user words) or distinct
  offsets of one TCB.
-/
import Fl4Proofs.P1.FastEntry
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T U : Set U64}

/-! ## The fault message's footprint -/

theorem set_reg_rgU {s0 s : S} {t r v : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hr : r.val < 384)
    (h : WritesIn st s0 s (XferRegW T U)) :
    obj.Tcb.set_reg st t s r v ⦃ s' => WritesIn st s0 s' (XferRegW T U) ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (hT t ht) hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    exact (h.trans (writesIn_wr (field_aligned (hT t ht) (by omega) (by omega)))).mono fun b hb =>
      hb.elim id fun e => Or.inl ⟨t, ht, K, by omega, by omega, by omega, e⟩

theorem buf_set_rgU {s0 s : S} {buf i v : U64} (hUa : ∀ b ∈ U, Aligned b) (hb : BufOK U buf)
    (h0 : buf ≠ 0#u64) (hi : i.val < 512) (h : WritesIn st s0 s (XferRegW T U)) :
    msg.buf_set st s buf i v ⦃ s' => WritesIn st s0 s' (XferRegW T U) ⦄ := by
  unfold msg.buf_set
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
  subst e
  have hu := hb h0 i hi
  exact (h.trans (writesIn_wr (hUa _ hu))).mono fun b hb => hb.elim id fun e => Or.inr (e ▸ hu)

theorem set_mr_rgU {s0 s : S} {y buf i v : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hUa : ∀ b ∈ U, Aligned b)
    (hb : BufOK U buf) (hi : i.val < 511) (h : WritesIn st s0 s (XferRegW T U)) :
    msg.set_mr st s y buf i v ⦃ r => WritesIn st s0 r.2 (XferRegW T U) ∧ r.1.val ≤ i.val + 4 ⦄ := by
  unfold msg.set_mr
  split
  · refine WP.spec_bind (msg.msg_register.lt i) fun r hr => ?_
    refine WP.spec_bind (set_reg_rgU (v := v) hT hy hr h) fun s1 h1 => ?_
    try simp only [lift, bind_ok]
    refine (WP.spec_ok _).2 ⟨h1, ?_⟩
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  · split
    · rename_i hne
      have h0 : buf ≠ 0#u64 := by simpa using hne
      simp only [lift, bind_ok]
      have hi1 : (core.num.U64.wrapping_add i 1#u64).val < 512 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      refine WP.spec_bind (buf_set_rgU (v := v) hUa hb h0 hi1 h) fun s1 h1 => ?_
      refine (WP.spec_ok _).2 ⟨h1, ?_⟩
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · exact (WP.spec_ok _).2 ⟨h, by simp [msg.N_MSG_REGISTERS]⟩

theorem copy_mrs_fault_loop0_rgU {s0 s : S} {snd rcv : U64} {regs : Slice U64} {i : Usize}
    (hT : TcbPlaced T) (hr : rcv ∈ T) (h : WritesIn st s0 s (XferRegW T U)) (hi : i.val ≤ (Slice.len regs).val) :
    faults.copy_mrs_fault_loop0 st s snd rcv regs i ⦃ r => WritesIn st s0 r.1 (XferRegW T U) ∧
      r.2.val ≤ (Slice.len regs).val ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_loop0
  apply loop.spec_decr_nat (measure := fun y => (Slice.len regs).val - y.2.val)
    (inv := fun y => WritesIn st s0 y.1 (XferRegW T U) ∧ y.2.val ≤ (Slice.len regs).val)
  · rintro ⟨s1, j⟩ ⟨h1, hj1⟩
    simp only at h1 hj1
    dsimp only
    unfold faults.copy_mrs_fault_loop0.body
    dsimp only
    split
    · rename_i hj
      have hj' : j.val < (Slice.len regs).val := by simpa using hj
      simp only [lift, bind_ok]
      split
      · step with Aeneas.Std.Slice.index_usize_spec as ⟨r0, _⟩
        refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 r0 hS) fun v _ => ?_
        refine WP.spec_bind (msg.msg_register.lt _) fun rg hrg => ?_
        refine WP.spec_bind (set_reg_rgU (v := v) hT hr hrg h1) fun s2 h2 => ?_
        step as ⟨j2, hj2⟩
        exact ⟨h2, by omega, by omega⟩
      · exact (WP.spec_ok _).2 ⟨h1, hj1⟩
    · exact (WP.spec_ok _).2 ⟨h1, hj1⟩
  · exact ⟨h, hi⟩

theorem copy_mrs_fault_loop1_rgU {s0 s : S} {snd buf : U64} {regs : Slice U64} {i : Usize}
    (hUa : ∀ b ∈ U, Aligned b) (hb : BufOK U buf) (h0 : buf ≠ 0#u64)
    (hl : (Slice.len regs).val < 511) (h : WritesIn st s0 s (XferRegW T U)) :
    faults.copy_mrs_fault_loop1 st s snd regs buf i ⦃ s' => WritesIn st s0 s' (XferRegW T U) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_loop1
  apply loop.spec_decr_nat (measure := fun y => (Slice.len regs).val - y.2.val)
    (inv := fun y => WritesIn st s0 y.1 (XferRegW T U))
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold faults.copy_mrs_fault_loop1.body
    dsimp only
    split
    · rename_i hj
      have hj' : j.val < (Slice.len regs).val := by simpa using hj
      step with Aeneas.Std.Slice.index_usize_spec as ⟨r0, _⟩
      refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 r0 hS) fun v _ => ?_
      simp only [lift, bind_ok]
      have hc : (UScalar.cast .U64 j).val = j.val := by
        have : 2 ^ System.Platform.numBits ≤ 2 ^ 64 := by
          rcases System.Platform.numBits_eq with e | e <;> simp [e]
        have := j.hBounds
        simp only [UScalar.cast_val_eq, UScalarTy.numBits]
        exact Nat.mod_eq_of_lt (by simp [Usize.size] at *; omega)
      have hix : (core.num.U64.wrapping_add (UScalar.cast .U64 j) 1#u64).val < 512 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hc]; omega
      refine WP.spec_bind (buf_set_rgU (v := v) hUa hb h0 hix h1) fun s2 h2 => ?_
      step as ⟨j2, hj2⟩
      exact ⟨h2, by omega⟩
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem copy_mrs_fault_rgU {s : S} {snd rcv buf : U64} {regs : Slice U64}
    (hT : TcbPlaced T) (hr : rcv ∈ T) (hUa : ∀ b ∈ U, Aligned b) (hb : BufOK U buf)
    (hl : (Slice.len regs).val < 511) :
    faults.copy_mrs_fault st s snd rcv regs buf ⦃ s' => WritesIn st s s' (XferRegW T U) ⦄ := by
  unfold faults.copy_mrs_fault
  refine WP.spec_bind (copy_mrs_fault_loop0_rgU (snd := snd) (regs := regs) (i := 0#usize) hT hr
    (WritesIn.refl s (XferRegW T U)) (by simp)) ?_
  rintro ⟨s1, i⟩ ⟨h1, -⟩
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · rename_i hne
    exact copy_mrs_fault_loop1_rgU hUa hb (by simpa using hne) hl h1
  · exact (WP.spec_ok _).2 h1

theorem us_ne_cap : fl4_abi.consts.fault.UnknownSyscall ≠ fl4_abi.consts.fault.CapFault := by
  unfold fl4_abi.consts.fault.UnknownSyscall fl4_abi.consts.fault.CapFault; decide

variable {A : Type _} (ar : machine.Arch A)

/-- **The fault message of an UnknownSyscall fault writes only the
receiver's registers and IPC-buffer words.** -/
theorem set_mrs_fault_rgU {s : S} {a : A} {snd rcv buf : U64} (hT : TcbPlaced T) (hr : rcv ∈ T)
    (hUa : ∀ b ∈ U, Aligned b) (hb : BufOK U buf)
    (hty : L.mem s (faultA snd) = fl4_abi.consts.fault.UnknownSyscall) :
    faults.set_mrs_fault st ar s a snd rcv buf ⦃ r => WritesIn st s r.2 (XferRegW T U) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.set_mrs_fault
  rw [fault_type_ok, hty]; simp only [bind_ok]
  refine WP.spec_bind (P0.obj.Tcb.fault_w0.p0 st snd s hS) fun w0 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w1.p0 st snd s hS) fun w1 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w2.p0 st snd s hS) fun w2 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s _ hS) fun pc _ => ?_
  simp only [us_ne_cap, if_false, if_true, ↓reduceIte, lift, bind_ok]
  refine WP.spec_bind (copy_mrs_fault_rgU (snd := snd) hT hr hUa hb (by simp [faults.SYSCALL_MESSAGE])) fun s2 h2 => ?_
  exact WP.spec_mono (set_mr_rgU hT hr hUa hb (by simp) h2) fun r hr' => hr'.1

/-- The transfer's register writes after the message (`set_msg_info`, `BADGE`). -/
theorem set_msg_info_rgU {s0 s : S} {y : U64} {mi : msginfo.MessageInfo} (hT : TcbPlaced T) (hy : y ∈ T)
    (h : WritesIn st s0 s (XferRegW T U)) :
    msg.set_msg_info st s y mi ⦃ s' => WritesIn st s0 s' (XferRegW T U) ⦄ := by
  unfold msg.set_msg_info
  refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 mi) fun w _ => ?_
  exact set_reg_rgU hT hy (by simp [layout.reg.MSG_INFO, layout.reg.RSI]) h

/-- **The footprint from the dequeued state `S5` to `S8`** (the message, its
info word, the badge). -/
theorem xfer_foot_S8 {S5 S6 S7 S8 : S} {a : A} {t dest rb sent badge : U64} {mi : msginfo.MessageInfo}
    (hT : TcbPlaced T) (hd : dest ∈ T) (hUa : ∀ b ∈ U, Aligned b) (hb : BufOK U rb)
    (hty : L.mem S5 (faultA t) = fl4_abi.consts.fault.UnknownSyscall)
    (hmrs : faults.set_mrs_fault st ar S5 a t dest rb = ok (sent, S6))
    (hS7 : msg.set_msg_info st S6 dest mi = ok S7)
    (hS8 : obj.Tcb.set_reg st dest S7 layout.reg.BADGE badge = ok S8) :
    WritesIn st S5 S6 (XferRegW T U) ∧ WritesIn st S5 S8 (XferRegW T U) := by
  have w6 : WritesIn st S5 S6 (XferRegW T U) := by
    have := set_mrs_fault_rgU (T := T) ar (a := a) (snd := t) hT hd hUa hb hty
    rw [hmrs, WP.spec_ok] at this; exact this
  have w7 : WritesIn st S5 S7 (XferRegW T U) := by
    have := set_msg_info_rgU (mi := mi) hT hd w6
    rw [hS7, WP.spec_ok] at this; exact this
  refine ⟨w6, ?_⟩
  have := set_reg_rgU (r := layout.reg.BADGE) (v := badge) hT hd (by simp [layout.reg.BADGE, layout.reg.RDI]) w7
  rw [hS8, WP.spec_ok] at this; exact this

end

/-! ## Addresses and frames of the run's explicit writes -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T U : Set U64}

theorem rTcbA_val0 (r : U64) : (rTcbA r).val = r.val := by
  unfold rTcbA layout.reply.TCB
  have := r.hBounds
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at this ⊢
  all_goals omega

/-- Two TCB words differ when their objects or their offsets differ. -/
theorem tcbw_ne {y y' K K' : U64} (hy : TcbAddr y) (hy' : TcbAddr y') (hK : K.val < 4096) (hK' : K'.val < 4096)
    (h : y ≠ y' ∨ K.val ≠ K'.val) : core.num.U64.wrapping_add y K ≠ core.num.U64.wrapping_add y' K' := by
  intro e
  have e' := congrArg UScalar.val e
  rw [tcb_wadd_val hy hK, tcb_wadd_val hy' hK'] at e'
  have a1 := hy.align; have a2 := hy'.align
  rcases h with h | h
  · exact h (UScalar.eq_of_val_eq (by omega))
  · omega

/-- A TCB word above the user context is no transfer word. -/
theorem tcbw_notRegW {Cs : Set U64} {s : S} {y K : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK : 3328 ≤ K.val)
    (hK4 : K.val < 4096) (hU : ∀ b ∈ U, OutsideObjs st T Cs s b) :
    ¬ XferRegW T U (core.num.U64.wrapping_add y K) := by
  rintro (⟨y', hy', K', h1, h2, h3, e⟩ | hb)
  · exact tcbw_ne (hT y hy) (hT y' hy') hK4 (by omega) (Or.inr (by omega)) e
  · obtain ⟨-, h2, -⟩ := hU _ hb
    have := h2 y hy; rw [tcb_wadd_val (hT y hy) hK4] at this; omega

/-- A node word is no transfer word. -/
theorem node_notRegW {Cs : Set U64} {s : S} {c off : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c)
    (hc : c ∈ Cs) (ho : off.val < 4288) (hU : ∀ b ∈ U, OutsideObjs st T Cs s b) :
    ¬ XferRegW T U (L.nodeAt s c off) := by
  rintro (⟨y', hy', K', h1, h2, h3, e⟩ | hb)
  · have := hN.disj y' hy'
    have e' := congrArg UScalar.val e
    rw [nodeAt_val hN ho, tcb_wadd_val (hT y' hy') (by omega)] at e'; omega
  · have := (hU _ hb).2.2 c hc; rw [nodeAt_val hN ho] at this; omega

theorem ksb_sfW (s : S) (t n : U64) : L.ksb (sfW (L := L) s t n) = L.ksb s := by unfold sfW; simp
theorem cpu_sfW (s : S) (t n : U64) : L.cpu (sfW (L := L) s t n) = L.cpu s := by unfold sfW; simp

theorem ksb_epFast (s : S) (ep d : U64) : L.ksb (epFast (L := L) s ep d) = L.ksb s := by
  unfold epFast epW; dsimp only; split <;> simp
theorem cpu_epFast (s : S) (ep d : U64) : L.cpu (epFast (L := L) s ep d) = L.cpu s := by
  unfold epFast epW; dsimp only; split <;> simp

/-- A word `set_fault` does not write. -/
theorem sfW_mem {s : S} {t n b : U64} (hb : Aligned b)
    (h0 : Aligned (faultA t) ∧ faultA t ≠ b)
    (h1 : Aligned (core.num.U64.wrapping_add t 3384#u64) ∧ core.num.U64.wrapping_add t 3384#u64 ≠ b)
    (h2 : Aligned (core.num.U64.wrapping_add t 3392#u64) ∧ core.num.U64.wrapping_add t 3392#u64 ≠ b)
    (h3 : Aligned (core.num.U64.wrapping_add t 3400#u64) ∧ core.num.U64.wrapping_add t 3400#u64 ≠ b) :
    L.mem (sfW (L := L) s t n) b = L.mem s b := by
  unfold sfW
  rw [mem_wr_ne' h3.1 hb h3.2, mem_wr_ne' h2.1 hb h2.2, mem_wr_ne' h1.1 hb h1.2, mem_wr_ne' h0.1 hb h0.2]

/-- A word the fast dequeue does not write. -/
theorem epFast_mem {s : S} {ptr dest b : U64} (hb : Aligned b)
    (hh : Aligned (epHeadA ptr) ∧ epHeadA ptr ≠ b) (htl : Aligned (epTSA ptr) ∧ epTSA ptr ≠ b)
    (hn : Aligned (nextA .Ep dest) ∧ nextA .Ep dest ≠ b) (hp : Aligned (prevA .Ep dest) ∧ prevA .Ep dest ≠ b)
    (haf : (L.epQ s ptr).end ≠ dest →
      Aligned (prevA .Ep (L.mem s (nextA .Ep dest))) ∧ prevA .Ep (L.mem s (nextA .Ep dest)) ≠ b) :
    L.mem (epFast (L := L) s ptr dest) b = L.mem s b := by
  unfold epFast epW
  dsimp only
  rw [mem_wr_ne' hp.1 hb hp.2, mem_wr_ne' hn.1 hb hn.2]
  by_cases h : (L.epQ s ptr).end = dest
  · rw [if_pos h, mem_wr_ne' htl.1 hb htl.2, mem_wr_ne' hh.1 hb hh.2]
  · rw [if_neg h, mem_wr_ne' htl.1 hb htl.2, mem_wr_ne' hh.1 hb hh.2, mem_wr_ne' (haf h).1 hb (haf h).2]

theorem curA_of {X Y : S} (hk : L.ksb X = L.ksb Y) (hc : L.cpu X = L.cpu Y) : curA (L := L) X = curA (L := L) Y := by
  unfold curA; rw [hc, nodeAt_of_ksb hk]
theorem actA_of {X Y : S} (hk : L.ksb X = L.ksb Y) (hc : L.cpu X = L.cpu Y) : actA (L := L) X = actA (L := L) Y := by
  unfold actA; rw [hc, nodeAt_of_ksb hk]

end

/-! ## The receive buffer's lookup -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- The IPC-buffer word of a TCB. -/
def ibA (t : U64) : U64 := core.num.U64.wrapping_add t 3512#u64
/-- The IPC-buffer cap slot of a TCB. -/
def sbA (t : U64) : U64 := core.num.U64.wrapping_add t (core.num.U64.wrapping_mul layout.tcb.SLOT_BUFFER layout.cte.SIZE)

theorem ipc_buffer_ok (s : S) (t : obj.Tcb) : obj.Tcb.ipc_buffer st t s = ok (L.mem s (ibA t)) := by
  apply eq_of_spec_fd; unfold obj.Tcb.ipc_buffer; step*; simp_all [ibA]

theorem sbA_val {t : U64} (h : TcbAddr t) : (sbA t).val = t.val + 64 := by
  have := h.fits
  unfold sbA layout.tcb.SLOT_BUFFER layout.cte.SIZE
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  all_goals omega

/-- **`lookup_ipc_buffer` reads three words**: the IPC-buffer word and the
buffer cap slot's two words. -/
theorem lookup_buf_agree {s s' : S} {t : U64} (h1 : L.mem s' (ibA t) = L.mem s (ibA t))
    (h2 : L.mem s' (sbA t) = L.mem s (sbA t))
    (h3 : L.mem s' (core.num.U64.wrapping_add (sbA t) 8#u64) = L.mem s (core.num.U64.wrapping_add (sbA t) 8#u64)) :
    msg.lookup_ipc_buffer st s' true t = msg.lookup_ipc_buffer st s true t := by
  unfold msg.lookup_ipc_buffer
  rw [ipc_buffer_ok, ipc_buffer_ok, h1]
  have hs : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok (sbA t) := by simp [obj.Tcb.slot, lift, sbA]
  rw [hs]; simp only [bind_ok]
  have hc : obj.Slot.cap st (sbA t) s' = obj.Slot.cap st (sbA t) s := by
    unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, h2, h3]
  rw [hc]

end

/-! ## `FaultReads` from the entry state -/

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- **The entry-state facts the general fault path's reads (m58
`FaultReads`) come from**, for an accepted fault run (`FaultChecks`): the
TCBs and the node placed, the endpoint placed outside the TCBs and nodes with
its queue headed by the handler (l4v `valid_ep`, `sym_refs`), the handler not
the faulting thread (F1: l4v `ct_in_state active`, queued threads blocked),
the user words outside the kernel objects (`UserOK`), the reply word among
the other kernel objects `Ω` (l4v `pspace_distinct`), the current thread, the
receive buffer user memory (`XferHyps.buf`), the handler's SC nonzero (what
`schedulable_here` checked). -/
structure FaultEnt (T Cs Ω U : Set U64) (s : S) (t : obj.Tcb) (ptr dest r : U64) (rest : List U64) : Prop where
  hT : TcbPlaced T
  ht : t ∈ T
  hE : EpPlaced T ptr
  hEN : EpOutNodes st Cs s ptr
  hq : QueueRel (L.mem s) T .Ep (L.epQ s ptr) (dest :: rest)
  hst : L.epState s ptr = obj.EP_RECV
  hdt : dest ≠ t
  hcC : L.cpu s ∈ Cs
  hN : NodePlaced st T s (L.cpu s)
  hU : ∀ b ∈ U, OutsideObjs st T Cs s b ∧ b ∉ Ω
  hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a
  hEΩ : ∀ a ∈ Ω, a.val + 8 ≤ ptr.val ∨ ptr.val + 16 ≤ a.val
  hrΩ : rTcbA r ∈ Ω
  hcur : L.mem s (curA (L := L) s) = t
  hact : L.actionW s = sched.ACTION_RESUME_CURRENT
  hbuf : msg.lookup_ipc_buffer st s true dest ⦃ b => BufOK U b ⦄
  hrep : L.mem s (replyA dest) = r
  hsc : L.mem s (scA dest) ≠ 0#u64

/-- The words the general fault path writes from the entry state to the
meeting state `fS14` (m58): `set_fault`'s four words of `t`, the endpoint's
two words, Ep links, the transfer's words (`XferRegW`), the reply's TCB word,
the two threads' state words and `t`'s reply word. -/
def FaultW (T U : Set U64) (t ptr dest r : U64) (b : U64) : Prop :=
  b = faultA t ∨ b = core.num.U64.wrapping_add t 3384#u64 ∨ b = core.num.U64.wrapping_add t 3392#u64 ∨
  b = core.num.U64.wrapping_add t 3400#u64 ∨ b = epHeadA ptr ∨ b = epTSA ptr ∨
  (∃ y ∈ T, b = nextA .Ep y ∨ b = prevA .Ep y) ∨ XferRegW T U b ∨ b = rTcbA r ∨ b = stA dest ∨ b = stA t ∨
  b = replyA t

/-- **What the fault run keeps up to `fS14`**: the core's node words, the
TCB words above the user context other than the state, reply, fault and Ep
link words, and the other kernel objects' words except the reply's TCB word
(for the reads of `UsOff` / `FinReads`). -/
structure FaultKeep (T Ω : Set U64) (s X : S) (r : U64) : Prop where
  ksb : L.ksb X = L.ksb s
  cpu : L.cpu X = L.cpu s
  node : ∀ off : U64, off.val < 4288 → off.val % 8 = 0 →
    L.mem X (L.nodeAt s (L.cpu s) off) = L.mem s (L.nodeAt s (L.cpu s) off)
  tcb : ∀ y ∈ T, ∀ K : U64, 3328 < K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3360 → K.val ≠ 3376 →
    K.val ≠ 3384 → K.val ≠ 3392 → K.val ≠ 3400 → K.val ≠ 3496 → K.val ≠ 3504 →
    L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)
  omg : ∀ b ∈ Ω, b ≠ rTcbA r → L.mem X b = L.mem s b

/-- A fact kept out of `omega`'s sight (a placement disjunction, unfolded
only where it is needed, so `omega` does not split on all of them). -/
def HidF (p : Prop) : Prop := p

set_option hygiene false in
/-- `omega`, then with one placement disjunction at a time. -/
local macro "omh" : tactic => `(tactic| first
  | omega
  | (have h := pt; unfold HidF at h; rcases h with h | h <;> omega)
  | (have h := pd; unfold HidF at h; rcases h with h | h <;> omega)
  | (have h := nt; unfold HidF at h; rcases h with h | h <;> omega)
  | (have h := nd; unfold HidF at h; rcases h with h | h <;> omega)
  | (have h := pn; unfold HidF at h; rcases h with h | h <;> omega)
  | (have h := rt; unfold HidF at h; rcases h with h | h <;> omega)
  | (have h := rd; unfold HidF at h; rcases h with h | h <;> omega)
  | (have h := rn; unfold HidF at h; rcases h with h | h <;> omega)
  | (have h := rE; unfold HidF at h; rcases h with h | h <;> omega))

set_option hygiene false in
/-- Address inequalities by their values. -/
local macro "ane" : tactic => `(tactic| (
  intro e
  have e' := congrArg UScalar.val e
  try simp only [vF, v84, v92, v00, vEh, vEt, vdn, vdp, vrd, vst, vsd, vrt, vsc, vC, vA, vR, vib, vsb, vsb8] at e'
  all_goals omh))

set_option hygiene false in
local macro "al" : tactic => `(tactic| (
  show _ % 8 = 0
  try simp only [vF, v84, v92, v00, vEh, vEt, vdn, vdp, vrd, vst, vsd, vrt, vsc, vC, vA, vR, vib, vsb, vsb8]
  all_goals omega))

set_option maxHeartbeats 1600000 in
/-- **m58's `FaultReads` from the entry state**, with the run's footprint up
to the meeting state `fS14` (for the later reads: `UsOff`, `FinReads`). -/
theorem faultReads_of {T Cs Ω U : Set U64} {s : S} {a : A} {t : obj.Tcb} {n ptr dest r : U64} {rest : List U64}
    (E : FaultEnt (L := L) T Cs Ω U s t ptr dest r rest) {rb sent : U64} {S6 S7 S8 : S} {mi : msginfo.MessageInfo}
    {badge : U64}
    (hbuf : msg.lookup_ipc_buffer st (epFast (L := L) (sfW (L := L) s t n) ptr dest) true dest = ok rb)
    (hmrs : faults.set_mrs_fault st ar (epFast (L := L) (sfW (L := L) s t n) ptr dest) a t dest rb = ok (sent, S6))
    (hS7 : msg.set_msg_info st S6 dest mi = ok S7)
    (hS8 : obj.Tcb.set_reg st dest S7 layout.reg.BADGE badge = ok S8) :
    FaultReads (L := L) T s t n ptr dest r rest S6 S8 ∧
      WritesIn st s (fS14 (L := L) S8 t dest r) (FaultW T U t ptr dest r) ∧
      FaultKeep (L := L) T Ω s (fS14 (L := L) S8 t dest r) r := by
  have hT := E.hT
  have ht' := hT t E.ht
  have hdT : dest ∈ T := E.hq.mem dest (by simp)
  have hd' := hT dest hdT
  have hUa : ∀ b ∈ U, Aligned b := fun b hb => (E.hU b hb).1.1
  have hUo : ∀ b ∈ U, OutsideObjs st T Cs s b := fun b hb => (E.hU b hb).1
  -- values
  have vF : (faultA t).val = t.val + 3376 := by
    have := tcb_wadd_val ht' (o := 3376#u64) (by simp); simpa [faultA] using this
  have v84 : (core.num.U64.wrapping_add t 3384#u64).val = t.val + 3384 := by
    have := tcb_wadd_val ht' (o := 3384#u64) (by simp); simpa using this
  have v92 : (core.num.U64.wrapping_add t 3392#u64).val = t.val + 3392 := by
    have := tcb_wadd_val ht' (o := 3392#u64) (by simp); simpa using this
  have v00 : (core.num.U64.wrapping_add t 3400#u64).val = t.val + 3400 := by
    have := tcb_wadd_val ht' (o := 3400#u64) (by simp); simpa using this
  have vEh : (epHeadA ptr).val = ptr.val := epHeadA_val
  have vEt : (epTSA ptr).val = ptr.val + 8 := epTSA_val E.hE
  have vdn : (nextA .Ep dest).val = dest.val + 3496 := by rw [nextA_val hd']; rfl
  have vdp : (prevA .Ep dest).val = dest.val + 3504 := by rw [prevA_val hd']; rfl
  have vrd : (replyA dest).val = dest.val + 3360 := by
    have := tcb_wadd_val hd' (o := 3360#u64) (by simp); simpa [replyA] using this
  have vst : (stA t).val = t.val + 3328 := by
    rw [stA_eq]; have := tcb_wadd_val ht' (o := 3328#u64) (by simp); simpa using this
  have vsd : (stA dest).val = dest.val + 3328 := by
    rw [stA_eq]; have := tcb_wadd_val hd' (o := 3328#u64) (by simp); simpa using this
  have vrt : (replyA t).val = t.val + 3360 := by
    have := tcb_wadd_val ht' (o := 3360#u64) (by simp); simpa [replyA] using this
  have vsc : (scA dest).val = dest.val + 3464 := by
    have := tcb_wadd_val hd' (o := 3464#u64) (by simp); simpa [scA] using this
  have vC : (curA (L := L) s).val = L.nodeBase s (L.cpu s) := by
    have := nodeAt_val E.hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD])
    rw [curth0] at this; simpa [curA] using this
  have vA : (actA (L := L) s).val = L.nodeBase s (L.cpu s) + 16 := by
    have := nodeAt_val E.hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
    rw [act_val] at this; simpa [actA] using this
  have vR : (rTcbA r).val = r.val := rTcbA_val0 r
  have vib : (ibA dest).val = dest.val + 3512 := by
    have := tcb_wadd_val hd' (o := 3512#u64) (by simp); simpa [ibA] using this
  have vsb : (sbA dest).val = dest.val + 64 := sbA_val hd'
  have vsb8 : (core.num.U64.wrapping_add (sbA dest) 8#u64).val = dest.val + 72 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vsb]
    have := hd'.fits; omega
  -- placement as numbers
  have ta := ht'.align; have tf := ht'.fits; have da := hd'.align; have df := hd'.fits
  have pt : HidF _ := E.hE.disj t E.ht; have pd : HidF _ := E.hE.disj dest hdT; have pal := E.hE.align
  have nt : HidF _ := E.hN.disj t E.ht; have nd : HidF _ := E.hN.disj dest hdT
  have pn : HidF _ := E.hEN.1 _ E.hcC
  obtain ⟨rA, rT, rN⟩ := E.hΩ _ E.hrΩ
  have rt : HidF _ := rT t E.ht; have rd : HidF _ := rT dest hdT; have rn : HidF _ := rN _ E.hcC
  have rE : HidF _ := E.hEΩ _ E.hrΩ
  clear rT rN
  have hdt' : dest.val ≠ t.val := fun e => E.hdt (UScalar.eq_of_val_eq e)
  have nal := E.hN.align
  have rA' : (rTcbA r).val % 8 = 0 := rA
  -- the states
  have k1 : L.ksb (sfW (L := L) s t n) = L.ksb s := ksb_sfW s t n
  have c1 : L.cpu (sfW (L := L) s t n) = L.cpu s := cpu_sfW s t n
  -- a word `set_fault` leaves
  have m1 : ∀ b, Aligned b → faultA t ≠ b → core.num.U64.wrapping_add t 3384#u64 ≠ b →
      core.num.U64.wrapping_add t 3392#u64 ≠ b → core.num.U64.wrapping_add t 3400#u64 ≠ b →
      L.mem (sfW (L := L) s t n) b = L.mem s b := fun b hb h0 h1 h2 h3 =>
    sfW_mem hb ⟨by al, h0⟩ ⟨by al, h1⟩ ⟨by al, h2⟩ ⟨by al, h3⟩
  -- F2 at set_fault's state
  have eQ : L.epQ (sfW (L := L) s t n) ptr = L.epQ s ptr := by
    unfold LawfulStore.epQ
    rw [m1 (epHeadA ptr) (by al) (by ane) (by ane) (by ane) (by ane),
      m1 (epTSA ptr) (by al) (by ane) (by ane) (by ane) (by ane)]
  have hq1 : QueueRel (L.mem (sfW (L := L) s t n)) T .Ep (L.epQ (sfW (L := L) s t n) ptr) (dest :: rest) := by
    rw [eQ]
    refine ⟨E.hq.nodup, E.hq.mem, E.hq.head, E.hq.last, E.hq.seg.congr fun y hy => ?_⟩
    have hy' := hT y (E.hq.mem y hy)
    have ya := hy'.align; have yf := hy'.fits
    have vyn : (nextA .Ep y).val = y.val + 3496 := by rw [nextA_val hy']; rfl
    have vyp : (prevA .Ep y).val = y.val + 3504 := by rw [prevA_val hy']; rfl
    constructor
    · refine m1 (prevA .Ep y) (by show _ % 8 = 0; rw [vyp]; omega) ?_ ?_ ?_ ?_ <;>
        (intro e; have e' := congrArg UScalar.val e; rw [vyp] at e'; simp only [vF, v84, v92, v00] at e'; omega)
    · refine m1 (nextA .Ep y) (by show _ % 8 = 0; rw [vyn]; omega) ?_ ?_ ?_ ?_ <;>
        (intro e; have e' := congrArg UScalar.val e; rw [vyn] at e'; simp only [vF, v84, v92, v00] at e'; omega)
  have hst1 : L.epState (sfW (L := L) s t n) ptr = obj.EP_RECV := by
    unfold LawfulStore.epState; rw [m1 (epTSA ptr) (by al) (by ane) (by ane) (by ane) (by ane)]; exact E.hst
  -- the successor in the queue
  have haf : (L.epQ (sfW (L := L) s t n) ptr).end ≠ dest → L.mem (sfW (L := L) s t n) (nextA .Ep dest) ∈ T := by
    intro hne
    obtain ⟨-, hn, -⟩ := (Seg_cons _ _ _ _ _ _).1 hq1.seg
    cases rest with
    | nil => exact absurd (by simpa using hq1.last) hne
    | cons y ys =>
      have : L.mem (sfW (L := L) s t n) (nextA .Ep dest) = y := by simpa using hn
      rw [this]; exact hq1.mem y (by simp)
  -- a word the dequeue leaves
  have m2 : ∀ b, Aligned b → epHeadA ptr ≠ b → epTSA ptr ≠ b → nextA .Ep dest ≠ b → prevA .Ep dest ≠ b →
      (∀ y ∈ T, (prevA .Ep y).val ≠ b.val) →
      L.mem (epFast (L := L) (sfW (L := L) s t n) ptr dest) b = L.mem (sfW (L := L) s t n) b :=
    fun b hb h0 h1 h2 h3 h4 => epFast_mem hb ⟨by al, h0⟩ ⟨by al, h1⟩ ⟨by al, h2⟩ ⟨by al, h3⟩ fun hne => by
      have hy := haf hne
      have hy' := hT _ hy
      refine ⟨?_, fun e => h4 _ hy (congrArg UScalar.val e)⟩
      show _ % 8 = 0; rw [prevA_val hy']; have := hy'.align; simp [prevOff]; omega
  have pv : ∀ (b : U64) (k : Nat), b.val = dest.val + k → k ≠ 3504 → k < 4096 → ∀ y ∈ T, (prevA .Ep y).val ≠ b.val :=
    fun b k hb hk hk4 y hy => by
      have hy' := hT y hy; rw [prevA_val hy', hb]; have := hy'.align; simp [prevOff]; omega
  have pvt : ∀ (b : U64) (k : Nat), b.val = t.val + k → k ≠ 3504 → k < 4096 → ∀ y ∈ T, (prevA .Ep y).val ≠ b.val :=
    fun b k hb hk hk4 y hy => by
      have hy' := hT y hy; rw [prevA_val hy', hb]; have := hy'.align; simp [prevOff]; omega
  -- the transfer's footprint
  have hb0 : BufOK U rb := by
    have hl := E.hbuf
    have e0 : msg.lookup_ipc_buffer st (epFast (L := L) (sfW (L := L) s t n) ptr dest) true dest =
        msg.lookup_ipc_buffer st s true dest := by
      refine lookup_buf_agree ?_ ?_ ?_
      · rw [m2 (ibA dest) (by al) (by ane) (by ane) (by ane) (by ane) (pv _ 3512 vib (by decide) (by decide)),
          m1 (ibA dest) (by al) (by ane) (by ane) (by ane) (by ane)]
      · rw [m2 (sbA dest) (by al) (by ane) (by ane) (by ane) (by ane) (pv _ 64 vsb (by decide) (by decide)),
          m1 (sbA dest) (by al) (by ane) (by ane) (by ane) (by ane)]
      · rw [m2 (core.num.U64.wrapping_add (sbA dest) 8#u64) (by al) (by ane) (by ane) (by ane) (by ane)
          (pv _ 72 vsb8 (by decide) (by decide)),
          m1 (core.num.U64.wrapping_add (sbA dest) 8#u64) (by al) (by ane) (by ane) (by ane) (by ane)]
    rw [e0] at hbuf; rw [hbuf, WP.spec_ok] at hl; exact hl
  have hR5 : L.mem (epFast (L := L) (sfW (L := L) s t n) ptr dest) (faultA t) = fl4_abi.consts.fault.UnknownSyscall := by
    rw [m2 (faultA t) (by al) (by ane) (by ane) (by ane) (by ane) (pvt _ 3376 vF (by decide) (by decide))]
    unfold sfW
    rw [mem_wr_ne' (a := core.num.U64.wrapping_add t 3400#u64) (b := faultA t) (by al) (by al) (by ane),
      mem_wr_ne' (a := core.num.U64.wrapping_add t 3392#u64) (b := faultA t) (by al) (by al) (by ane),
      mem_wr_ne' (a := core.num.U64.wrapping_add t 3384#u64) (b := faultA t) (by al) (by al) (by ane),
      LawfulStore.mem_wr_same (a := faultA t) (by al)]
  obtain ⟨w6, w8⟩ := xfer_foot_S8 ar hT hdT hUa hb0 hR5 hmrs hS7 hS8
  have k2 : L.ksb (epFast (L := L) (sfW (L := L) s t n) ptr dest) = L.ksb s := by rw [ksb_epFast, k1]
  have c2 : L.cpu (epFast (L := L) (sfW (L := L) s t n) ptr dest) = L.cpu s := by rw [cpu_epFast, c1]
  have k8 : L.ksb S8 = L.ksb s := by rw [w8.1, k2]
  have c8 : L.cpu S8 = L.cpu s := by rw [w8.2.1, c2]
  have hC8 : curA (L := L) S8 = curA (L := L) s := curA_of k8 c8
  have hA8 : actA (L := L) S8 = actA (L := L) s := actA_of k8 c8
  have nC : ¬ XferRegW T U (curA (L := L) s) :=
    node_notRegW hT E.hN E.hcC (by simp [layout.node.CUR_THREAD]) hUo
  have nA : ¬ XferRegW T U (actA (L := L) s) :=
    node_notRegW hT E.hN E.hcC (by simp [layout.node.SCHED_ACTION]) hUo
  -- a node word is kept by every write up to `S8`
  have node8 : ∀ b, (b = curA (L := L) s ∨ b = actA (L := L) s) → L.mem S8 b = L.mem s b := by
    intro b hb
    have hbv : b.val = L.nodeBase s (L.cpu s) ∨ b.val = L.nodeBase s (L.cpu s) + 16 := by
      rcases hb with rfl | rfl
      · exact Or.inl vC
      · exact Or.inr vA
    have hba : Aligned b := by show _ % 8 = 0; have := E.hN.align; omega
    rw [w8.2.2 b hba (by rcases hb with rfl | rfl <;> assumption)]
    rw [m2 b hba (fun e => by have := congrArg UScalar.val e; rw [vEh] at this; omh)
      (fun e => by have := congrArg UScalar.val e; rw [vEt] at this; omh)
      (fun e => by have := congrArg UScalar.val e; rw [vdn] at this; omh)
      (fun e => by have := congrArg UScalar.val e; rw [vdp] at this; omh)
      (fun y hy e => by have hy' := hT y hy; have := E.hN.disj y hy; rw [prevA_val hy'] at e; simp [prevOff] at e; omega)]
    exact m1 b hba (fun e => by have := congrArg UScalar.val e; rw [vF] at this; omh)
      (fun e => by have := congrArg UScalar.val e; rw [v84] at this; omh)
      (fun e => by have := congrArg UScalar.val e; rw [v92] at this; omh)
      (fun e => by have := congrArg UScalar.val e; rw [v00] at this; omh)
  have hR6 : L.mem S6 (faultA t) = fl4_abi.consts.fault.UnknownSyscall := by
    rw [w6.2.2 (faultA t) (by al) (tcbw_notRegW hT E.ht (K := 3376#u64) (by simp) (by simp) hUo)]; exact hR5
  have hF8 : L.mem S8 (faultA t) = fl4_abi.consts.fault.UnknownSyscall := by
    rw [w8.2.2 (faultA t) (by al) (tcbw_notRegW hT E.ht (K := 3376#u64) (by simp) (by simp) hUo)]; exact hR5
  have hR8 : L.mem S8 (replyA dest) = r := by
    rw [w8.2.2 (replyA dest) (by al) (tcbw_notRegW hT hdT (K := 3360#u64) (by simp) (by simp) hUo)]
    rw [m2 (replyA dest) (by al) (by ane) (by ane) (by ane) (by ane) (pv _ 3360 vrd (by decide) (by decide)),
      m1 (replyA dest) (by al) (by ane) (by ane) (by ane) (by ane)]
    exact E.hrep
  -- the reply writes
  have R10 : ∀ b, Aligned b → rTcbA r ≠ b → stA dest ≠ b → L.mem (fS10 (L := L) S8 dest r) b = L.mem S8 b :=
    fun b hb h1 h2 => by unfold fS10; rw [mem_wr_ne' (by al) hb h2, mem_wr_ne' (by al) hb h1]
  have R13 : ∀ b, Aligned b → rTcbA r ≠ b → stA t ≠ b → replyA t ≠ b →
      L.mem (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) b = L.mem (fS10 (L := L) S8 dest r) b :=
    fun b hb h1 h2 h3 => by
      unfold fS13; rw [mem_wr_ne' (by al) hb h3, mem_wr_ne' (by al) hb h2, mem_wr_ne' (by al) hb h1]
  have eC0 : L.mem (fS10 (L := L) S8 dest r) (curA (L := L) s) = t := by
    rw [R10 (curA (L := L) s) (by al) (by ane) (by ane), node8 _ (Or.inl rfl)]; exact E.hcur
  have eA0 : L.mem (fS10 (L := L) S8 dest r) (actA (L := L) s) = sched.ACTION_RESUME_CURRENT := by
    rw [R10 (actA (L := L) s) (by al) (by ane) (by ane), node8 _ (Or.inr rfl)]; exact E.hact
  have eC : L.mem (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (curA (L := L) S8) = t := by
    rw [hC8, R13 (curA (L := L) s) (by al) (by ane) (by ane) (by ane)]; exact eC0
  have eA : L.mem (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) (actA (L := L) s) = sched.ACTION_RESUME_CURRENT := by
    rw [R13 (actA (L := L) s) (by al) (by ane) (by ane) (by ane)]; exact eA0
  have k10 : L.ksb (fS10 (L := L) S8 dest r) = L.ksb s := by unfold fS10; simp [k8]
  have c10 : L.cpu (fS10 (L := L) S8 dest r) = L.cpu s := by unfold fS10; simp [c8]
  have k13 : L.ksb (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) = L.ksb s := by unfold fS13; simp [k10]
  have c13 : L.cpu (fS13 (L := L) (fS10 (L := L) S8 dest r) t r) = L.cpu s := by unfold fS13; simp [c10]
  have hsA : Aligned (stA dest) := by al
  have haA : Aligned (actA (L := L) s) := by al
  have hcA : Aligned (curA (L := L) s) := by al
  -- the footprint
  have w1 : WritesIn st s (sfW (L := L) s t n) (fun b => b = faultA t ∨ b = core.num.U64.wrapping_add t 3384#u64 ∨
      b = core.num.U64.wrapping_add t 3392#u64 ∨ b = core.num.U64.wrapping_add t 3400#u64) :=
    ⟨k1, c1, fun b hb hn => m1 b hb (fun e => hn (Or.inl e.symm)) (fun e => hn (Or.inr (Or.inl e.symm)))
      (fun e => hn (Or.inr (Or.inr (Or.inl e.symm)))) (fun e => hn (Or.inr (Or.inr (Or.inr e.symm))))⟩
  have w2 : WritesIn st (sfW (L := L) s t n) (epFast (L := L) (sfW (L := L) s t n) ptr dest)
      (fun b => b = epHeadA ptr ∨ b = epTSA ptr ∨ ∃ y ∈ T, b = nextA .Ep y ∨ b = prevA .Ep y) :=
    ⟨by rw [ksb_epFast], by rw [cpu_epFast], fun b hb hn => m2 b hb (fun e => hn (Or.inl e.symm))
      (fun e => hn (Or.inr (Or.inl e.symm))) (fun e => hn (Or.inr (Or.inr ⟨dest, hdT, Or.inl e.symm⟩)))
      (fun e => hn (Or.inr (Or.inr ⟨dest, hdT, Or.inr e.symm⟩)))
      (fun y hy e => hn (Or.inr (Or.inr ⟨y, hy, Or.inr (UScalar.eq_of_val_eq e).symm⟩)))⟩
  have w14 : WritesIn st S8 (fS14 (L := L) S8 t dest r)
      (fun b => b = rTcbA r ∨ b = stA dest ∨ b = stA t ∨ b = replyA t) := by
    unfold fS14 fS13 fS10
    refine ⟨by simp, by simp, fun b hb hn => ?_⟩
    rw [mem_wr_ne' hsA hb (fun e => hn (Or.inr (Or.inl e.symm))),
      mem_wr_ne' (by al) hb (fun e => hn (Or.inr (Or.inr (Or.inr e.symm)))),
      mem_wr_ne' (by al) hb (fun e => hn (Or.inr (Or.inr (Or.inl e.symm)))),
      mem_wr_ne' (by al) hb (fun e => hn (Or.inl e.symm)),
      mem_wr_ne' hsA hb (fun e => hn (Or.inr (Or.inl e.symm))),
      mem_wr_ne' (by al) hb (fun e => hn (Or.inl e.symm))]
  have wF : WritesIn st s (fS14 (L := L) S8 t dest r) (FaultW T U t ptr dest r) :=
    (((w1.trans w2).trans w8).trans w14).mono fun b hb => by
      unfold FaultW
      rcases hb with ((h1 | h2) | h3) | h4
      · rcases h1 with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases h2 with h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3)))))))
      · rcases h4 with h | h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))
  have keepN : ∀ off : U64, off.val < 4288 → off.val % 8 = 0 →
      L.mem (fS14 (L := L) S8 t dest r) (L.nodeAt s (L.cpu s) off) = L.mem s (L.nodeAt s (L.cpu s) off) := by
    intro off ho h8
    have vb := nodeAt_val E.hN ho
    refine wF.2.2 _ (nodeAt_aligned E.hN ho h8) ?_
    unfold FaultW
    rintro (h | h | h | h | h | h | ⟨y, hy, h | h⟩ | h | h | h | h | h)
    all_goals first
      | exact node_notRegW hT E.hN E.hcC ho hUo h
      | (have e' := congrArg UScalar.val h
         try simp only [vb, vF, v84, v92, v00, vEh, vEt, vR, vsd, vst, vrt] at e'
         all_goals omh)
      | (have hy' := hT y hy
         have := E.hN.disj y hy
         have e' := congrArg UScalar.val h
         first | rw [nextA_val hy'] at e' | rw [prevA_val hy'] at e'
         rw [vb] at e'; simp [nextOff, prevOff] at e'; omega)
  have keepT : ∀ y ∈ T, ∀ K : U64, 3328 < K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3360 → K.val ≠ 3376 →
      K.val ≠ 3384 → K.val ≠ 3392 → K.val ≠ 3400 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem (fS14 (L := L) S8 t dest r) (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K h1 h2 h3 k1 k2 k3 k4 k5 k6 k7
    have hy' := hT y hy
    have vb := tcb_wadd_val hy' h2
    have ya := hy'.align; have yf := hy'.fits
    have p1 := E.hE.disj y hy
    have p2 := (E.hΩ _ E.hrΩ).2.1 y hy
    refine wF.2.2 _ (by show _ % 8 = 0; rw [vb]; omega) ?_
    unfold FaultW
    rintro (h | h | h | h | h | h | ⟨z, hz, h | h⟩ | h | h | h | h | h)
    all_goals first
      | exact tcbw_notRegW hT hy (by omega) h2 hUo h
      | (have e' := congrArg UScalar.val h
         try simp only [vb, vF, v84, v92, v00, vEh, vEt, vR, vsd, vst, vrt] at e'
         all_goals omega)
      | (have hz' := hT z hz
         have za := hz'.align
         have e' := congrArg UScalar.val h
         first | rw [nextA_val hz'] at e' | rw [prevA_val hz'] at e'
         rw [vb] at e'; simp [nextOff, prevOff] at e'; omega)
  have keepO : ∀ b ∈ Ω, b ≠ rTcbA r → L.mem (fS14 (L := L) S8 t dest r) b = L.mem s b := by
    intro b hb hbr
    obtain ⟨ba, bT, bN⟩ := E.hΩ b hb
    have bE := E.hEΩ b hb
    have bt := bT t E.ht; have bd := bT dest hdT
    refine wF.2.2 b ba ?_
    unfold FaultW
    rintro (h | h | h | h | h | h | ⟨z, hz, h | h⟩ | (⟨z, hz, K, -, hK, -, h⟩ | h) | h | h | h | h)
    all_goals first
      | (have e' := congrArg UScalar.val h
         try simp only [vF, v84, v92, v00, vEh, vEt, vR, vsd, vst, vrt] at e'
         all_goals omega)
      | (have hz' := hT z hz
         have bz := bT z hz
         have e' := congrArg UScalar.val h
         first | rw [nextA_val hz'] at e' | rw [prevA_val hz'] at e' | rw [tcb_wadd_val hz' (by omega)] at e'
         try simp [nextOff, prevOff] at e'
         all_goals omega)
      | exact hbr h
      | exact absurd hb (E.hU b h).2
  have hk14 : L.ksb (fS14 (L := L) S8 t dest r) = L.ksb s := wF.1
  have hc14 : L.cpu (fS14 (L := L) S8 t dest r) = L.cpu s := wF.2.1
  refine ⟨⟨hT, E.hE, hq1, hst1, hR5, hR6, hR8, E.hdt, ?_, ?_, ?_, ?_, eC, ?_, ?_, ?_, by rw [hA8]; exact haA, hsA,
    by rw [hA8]; ane⟩, wF, ⟨hk14, hc14, keepN, keepT, keepO⟩⟩
  · rw [hC8]; exact eC0
  · rw [R10 (faultA t) (by al) (by ane) (by ane)]; exact hF8
  · show L.mem _ (actA (L := L) (fS10 (L := L) S8 dest r)) = _
    rw [actA_of k10 c10]; exact eA0
  · unfold fS13
    rw [mem_wr_ne' (a := replyA t) (b := stA t) (by al) (by al) (by ane),
      LawfulStore.mem_wr_same (a := stA t) (by al)]
  · show L.mem _ (actA (L := L) (fS13 (L := L) (fS10 (L := L) S8 dest r) t r)) = _
    rw [actA_of k13 c13]; exact eA
  · rw [hA8, mem_wr_ne' (a := actA (L := L) s) (b := scA dest) haA (by al) (by ane),
      R13 (scA dest) (by al) (by ane) (by ane) (by ane), R10 (scA dest) (by al) (by ane) (by ane)]
    rw [w8.2.2 (scA dest) (by al) (tcbw_notRegW hT hdT (K := 3464#u64) (by simp) (by simp) hUo)]
    rw [m2 (scA dest) (by al) (by ane) (by ane) (by ane) (by ane) (pv _ 3464 vsc (by decide) (by decide)),
      m1 (scA dest) (by al) (by ane) (by ane) (by ane) (by ane)]
    exact E.hsc
  · rw [hA8, hC8, mem_wr_ne' (a := stA dest) (b := curA (L := L) s) hsA hcA (by ane),
      mem_wr_ne' (a := actA (L := L) s) (b := curA (L := L) s) haA hcA (by ane)]
    rw [← hC8]; exact eC

end

/-! ## What `schedulable_here` checked -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem cur_time_ok (s : S) :
    sched.cur_time st s = ok (L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_TIME)) := by
  unfold sched.cur_time; rw [L.cur_cpu_eq]; simp only [bind_ok]
  exact eq_of_spec_fd (obj.node_get.spec (L := L) s _ _)

theorem cur_domain_ok (s : S) :
    sched.cur_domain st s = ok (L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)) := by
  unfold sched.cur_domain obj.ks_get; simp only [L.ks_base_eq, bind_ok, lift, L.read_eq]

theorem cde_one (s : S) : sched.is_cur_domain_expired st s = ok false := by
  unfold sched.is_cur_domain_expired; rw [if_neg num_domains_one]

theorem node_get_ok (s : S) (c o : U64) : obj.node_get st s c o = ok (L.mem s (L.nodeAt s c o)) :=
  eq_of_spec_fd (obj.node_get.spec s c o)
theorem is_null_ok (t : U64) : obj.Tcb.is_null t = ok (decide (t = 0#u64)) := eq_of_spec_fd (obj.Tcb.is_null.spec t)
theorem tcb_sc_ok (s : S) (t : U64) : obj.Tcb.sc st t s = ok (L.mem s (scA t)) := eq_of_spec_fd (obj.Tcb.sc.spec s t)
theorem ready_ok (s : S) (c : U64) :
    sporadic.ready st s c = ok (decide ((L.refill s c (L.rhead s c)).time ≤ L.curTime s)) :=
  eq_of_spec_fd (sporadic.ready.spec s c)
theorem td_ok (s : S) (t : U64) : obj.Tcb.timer_deadline st t s = ok (L.mem s (tdA t)) :=
  eq_of_spec_fd (obj.Tcb.timer_deadline.val s t)
theorem aff_ok (s : S) (t : U64) : obj.Tcb.affinity st t s = ok (L.mem s (affA t)) :=
  eq_of_spec_fd (obj.Tcb.affinity.spec s t)
theorem dom_ok (s : S) (t : U64) : obj.Tcb.domain st t s = ok (L.mem s (domA t)) :=
  eq_of_spec_fd (obj.Tcb.domain.spec s t)
theorem inrel_ok (s : S) (t : U64) :
    sched.in_release_queue st s t = ok (decide ((L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64)) :=
  eq_of_spec_fd (sched.in_release_queue.spec s t)
theorem queued_ok (s : S) (t : U64) :
    sched.queued st s t = ok (decide ((L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64)) :=
  eq_of_spec_fd (sched.queued.spec s t)

/-- **What an accepted `schedulable_here s d` checked.** -/
structure HereF (s : S) (d : U64) : Prop where
  nd : NoDue (L := L) s
  dt : L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME) ≠ 0#u64
  aff : L.mem s (affA d) = L.cpu s
  dom : L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) = L.mem s (domA d)
  sc : L.mem s (scA d) ≠ 0#u64
  nr : (L.mem s (inqA d) &&& sched.Q_RELEASE) = 0#u64
  nq : (L.mem s (inqA d) &&& sched.Q_QUEUED) = 0#u64

theorem here_facts {s : S} {d : U64} (h : fastpath.schedulable_here st s d = ok true) : HereF (L := L) s d := by
  unfold fastpath.schedulable_here at h
  simp only [L.cur_cpu_eq, cur_time_ok, cde_one, domain_time_eq, cur_domain_ok, node_get_ok, is_null_ok,
    tcb_sc_ok, ready_ok, td_ok, aff_ok, dom_ok, inrel_ok, queued_ok, bind_ok, decide_eq_true_eq,
    Bool.false_eq_true, ↓reduceIte] at h
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    by_contra h0
    try push_neg at h0
    first
      | (simp [h0, ite_self] at h <;> exact absurd (ok_inj_ff h) (by decide))
      | (have h1 := Ne.symm h0
         simp [h1, ite_self] at h <;> exact absurd (ok_inj_ff h) (by decide))
end

/-! ## (d1) `UsOff` at a state that keeps the entry state's words -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- A node word is outside every SC whose words are `Ω` words. -/
theorem node_outside_sc {T Cs Ω : Set U64} {s : S} {sc : U64} {sb : Nat} {off : U64}
    (hN : NodePlaced st T s (L.cpu s)) (hcC : L.cpu s ∈ Cs) (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a)
    (scW : ∀ b, Aligned b → InSC sc sb b → b ∈ Ω) (ho : off.val < 4288) (h8 : off.val % 8 = 0) :
    Outside (L.nodeAt s (L.cpu s) off) sc sb := by
  by_contra hc
  unfold Outside at hc
  have hm := scW _ (nodeAt_aligned hN ho h8) ⟨by omega, by omega⟩
  have := (hΩ _ hm).2.2 _ hcC
  rw [nodeAt_val hN ho] at this hc
  omega

/-- **(d1) `UsOff` from the entry state** at any state `X` that keeps the
entry state's node, TCB and `Ω` words (`FaultKeep`; `fS14` by
`faultReads_of`), given the handler's SC placed at the entry state: its words
`Ω` words (`ObjsOK.scW`), its `SPORADIC` word in `Ω` (`SCsOK.spSg`, `sub`),
well formed if sporadic (`SCsOK.spor` ⇒ active ⇒ `SCA`), apart from the reply
object (`ObjsOK.rpSc`), at least 128 bytes (`ObjsOK.sc`). -/
theorem usOff_of {T Cs Ω U : Set U64} {s X : S} {t : obj.Tcb} {ptr dest r : U64} {rest : List U64} {sb : Nat}
    (E : FaultEnt (L := L) T Cs Ω U s t ptr dest r rest) (K : FaultKeep (L := L) T Ω s X r)
    (scW : ∀ b, Aligned b → InSC (L.mem s (scA dest)) sb b → b ∈ Ω)
    (spΩ : sporA (L.mem s (scA dest)) ∈ Ω)
    (spWF : L.mem s (sporA (L.mem s (scA dest))) ≠ 0#u64 → RefillsWF st s (L.mem s (scA dest)) sb)
    (rpSc : r.val + 32 ≤ (L.mem s (scA dest)).val ∨ (L.mem s (scA dest)).val + 2 ^ sb ≤ r.val)
    (sb7 : 7 ≤ sb) (fits : (L.mem s (scA dest)).val + 2 ^ sb ≤ 2 ^ 64) :
    UsOff (L := L) X dest (actA (L := L) X) sb := by
  have hdT : dest ∈ T := E.hq.mem dest (by simp)
  have hd' := E.hT dest hdT
  have eA : actA (L := L) X = actA (L := L) s := actA_of K.ksb K.cpu
  have eN : ∀ off, L.nodeA X off = L.nodeAt s (L.cpu s) off := fun off => by
    unfold LawfulStore.nodeA; rw [K.cpu, nodeAt_of_ksb K.ksb]
  have esc : L.mem X (scA dest) = L.mem s (scA dest) :=
    K.tcb dest hdT 3464#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have vsc : (scA dest).val = dest.val + 3464 := by
    have := tcb_wadd_val hd' (o := 3464#u64) (by simp); simpa [scA] using this
  have da := hd'.align
  have nd := E.hN.disj dest hdT
  have nal := E.hN.align
  have vA : (actA (L := L) s).val = L.nodeBase s (L.cpu s) + 16 := by
    have := nodeAt_val E.hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
    rw [act_val] at this; simpa [actA] using this
  have vN : ∀ off : U64, off.val < 4288 → (L.nodeAt s (L.cpu s) off).val = L.nodeBase s (L.cpu s) + off.val :=
    fun off ho => nodeAt_val E.hN ho
  have hsp := E.hΩ _ spΩ
  have hspN := hsp.2.2 _ E.hcC
  have p7 : 128 ≤ 2 ^ sb := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) sb7)
  have vsp : (sporA (L.mem s (scA dest))).val = (L.mem s (scA dest)).val + 64 := by
    unfold sporA layout.sc.SPORADIC
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have haA : Aligned (actA (L := L) s) := by show _ % 8 = 0; rw [vA]; omega
  rw [eA]
  refine ⟨haA, by show _ % 8 = 0; rw [vsc]; omega, fun e => by
      have := congrArg UScalar.val e; rw [vA, vsc] at this; omega,
    by rw [eN]; exact nodeAt_aligned E.hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]),
    fun e => by
      rw [eN] at e; have := congrArg UScalar.val e
      rw [vA, vN _ (by simp [layout.node.CUR_SC])] at this; simp [layout.node.CUR_SC] at this,
    ?_, ?_, ?_,
    by rw [eN]; exact nodeAt_aligned E.hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]),
    fun e => by
      rw [eN] at e; have := congrArg UScalar.val e
      rw [vA, vN _ (by simp [layout.node.CUR_TIME])] at this; simp [layout.node.CUR_TIME] at this,
    ?_,
    fun e => by
      rw [eN] at e; have := congrArg UScalar.val e
      rw [vA, vN _ (by simp [layout.node.REPROGRAM])] at this; simp [layout.node.REPROGRAM] at this⟩
  · rw [esc]
    refine ⟨hsp.1, fun e => ?_⟩
    have := congrArg UScalar.val e; rw [vA] at this; rw [← this] at hspN; omega
  · rw [esc]; intro _ h1
    have espX : L.mem X (sporA (L.mem s (scA dest))) = L.mem s (sporA (L.mem s (scA dest))) := by
      refine K.omg _ spΩ fun e => ?_
      have := congrArg UScalar.val e; rw [vsp, rTcbA_val0] at this; omega
    rw [espX] at h1
    refine (spWF h1).agree fun b hb hin => K.omg b (scW b hb hin) fun e => ?_
    subst e; unfold InSC at hin; rw [rTcbA_val0] at hin; obtain ⟨h1, h2⟩ := hin; omega
  · rw [esc]
    have := node_outside_sc (sb := sb) (off := layout.node.SCHED_ACTION) E.hN E.hcC E.hΩ scW
      (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    exact this
  · rw [esc, eN]
    exact ⟨nodeAt_aligned E.hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]),
      node_outside_sc E.hN E.hcC E.hΩ scW (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])⟩

end

end Fl4Proofs.P1
