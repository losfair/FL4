/-
P3 (DESIGN.md §9), IPC: **the fault reply's `handle_fault_reply` at `J`**
(toward `JReplyRestHyp`'s faulted receiver: IpcFaultReply's
`handle_fault_reply_rel` with `JAtZ` carried).

* `cmfrJ_loop0`, `cmfrJ_loop1`, `cmfrJ_top`: `copy_mrs_fault_reply` (as
  `cmfr_loop0`, `cmfr_loop1`, `cmfr_top`) with `JAtZ` beside IpcFaultReply's
  `RgInv`, each sanitised register by XTopJointWriteRegs' `JAtZ.sanWrJ`; the
  replier's buffer by `lookup_buf_full` at the `J` state after the first
  loop (`IpcBufCapOK`, `BufWordRel`, `BufCover` [J], JEntryGlob's, as
  XTopJointXfer), no IRel-level buffer bundle.
* `JAtZ.hfrJ`: `handle_fault_reply` at `J`, by the fault's kind; the spec's
  outcome changes only the receiver's user context, and with it the whole
  fault reply's spec prefix (`specFaultReply` up to the fault clear) is
  identified (`getMrs_eq`, the replier's buffer words aligned by `BufCover`
  and `EPlaced.balign`).
-/
import Fl4Proofs.P3.IpcFaultReply
import Fl4Proofs.P3.XTopJointWriteRegs
import Fl4Proofs.P3.XTopJointCancelReply
import Fl4Proofs.P3.XTopJointStsI
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

section Loops
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {a : A} {SR : S → Fl4Spec.State Unit → Prop}

set_option maxHeartbeats 8000000 in
/-- **The first loop of `copy_mrs_fault_reply` at `J`** (as `cmfr_loop0`). -/
theorem cmfrJ_loop0 (hH : EpHyps st Z.T Z.E Z.R Z.B SR) (hP : EPlaced Z.T Z.E Z.R Z.B) {s0 : S}
    {σ0 : Fl4Spec.State Unit}
    {snd rcv : U64} (hs : snd ∈ Z.T) (hr : rcv ∈ Z.T) (hne : snd ≠ rcv) {x0 : Fl4Spec.Tcb}
    (hk0 : σ0.kheap rcv.bv = some (.tcb x0))
    {regs : Fl4Spec.Register → Fl4Spec.Word} (hreg : ∀ r, (L.mem s0 (regA snd (regIdx r))).bv = regs r)
    {sl : Slice U64} {Lr : List Fl4Spec.Register} (hsl : sl.val = Lr.map regIdx) (hLr : Lr.length < 32)
    (n : Usize) (hn : n.val ≤ Lr.length) {V : List Fl4Spec.Word}
    (hV : ∀ i (h : i < min n.val 4), i < V.length ∧ V[i]! = regs (mrIdx i))
    (hI : RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 rcv x0 s0 [] [])
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a σ0) :
    faults.copy_mrs_fault_reply_loop0 st s0 snd rcv sl n 0#usize ⦃ r => r.2.val = min n.val 4 ∧
      RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 rcv x0 r.1 (Lr.take r.2.val) (V.take r.2.val) ∧
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D r.1 a
        (updK σ0 rcv.bv (.tcb (sanRegs x0 (Lr.take r.2.val) (V.take r.2.val)))) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  have hlen : (Slice.len sl).val = Lr.length := by simp [Slice.len, hsl]
  unfold faults.copy_mrs_fault_reply_loop0
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.val)
    (inv := fun x => x.2.val ≤ min n.val 4 ∧
      RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 rcv x0 x.1 (Lr.take x.2.val) (V.take x.2.val) ∧
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D x.1 a
        (updK σ0 rcv.bv (.tcb (sanRegs x0 (Lr.take x.2.val) (V.take x.2.val)))))
  · rintro ⟨s', i⟩ ⟨hi4, hI', V', J'⟩
    unfold faults.copy_mrs_fault_reply_loop0.body
    simp only at hi4 hI' J' ⊢
    by_cases hcn : i < n
    swap
    · rw [if_neg hcn, WP.spec_ok]
      have : i.val = min n.val 4 := by have := us_lt_iff.not.1 hcn; omega
      exact ⟨this, this ▸ hI', V', this ▸ J'⟩
    rw [if_pos hcn]
    have hin : i.val < n.val := us_lt_iff.1 hcn
    have h1 : i < Slice.len sl := us_lt_iff.2 (by omega)
    rw [if_pos h1]
    simp only [lift, bind_ok]
    by_cases h2 : (UScalar.cast .U64 i : U64) < msg.N_MSG_REGISTERS
    swap
    · rw [if_neg h2, WP.spec_ok]
      have : i.val = min n.val 4 := by
        have h2' : ¬ i.val < 4 := fun h => h2 ((gt_iff_val).2 (by rw [hN, cast_us i (by omega)]; omega))
        omega
      exact ⟨this, this ▸ hI', V', this ▸ J'⟩
    rw [if_pos h2]
    have hi4' : i.val < 4 := by have := (gt_iff_val).1 h2; rw [hN, cast_us i (by omega)] at this; omega
    have hiL : i.val < Lr.length := by omega
    have hidx : Slice.index_usize sl i = ok (regIdx Lr[i.val]) := by
      unfold Slice.index_usize
      have : sl[i]? = some (regIdx Lr[i.val]) := by
        simp [Slice.getElem?_Usize_eq, hsl, List.getElem?_map, List.getElem?_eq_getElem hiL]
      rw [this]
    rw [hidx]
    simp only [bind_ok]
    refine WP.spec_bind (msg_register_spec (UScalar.cast .U64 i) (by rw [cast_us i (by omega)]; exact hi4')) ?_
    rintro r5 rfl
    rw [cast_us i (by omega)]
    refine WP.spec_bind (obj.Tcb.reg.spec s' snd _) ?_
    rintro v rfl
    obtain ⟨w, hw, hwv⟩ := sanitise_eq Lr[i.val] (L.mem s' (regA snd (regIdx (mrIdx i.val))))
    rw [hw]
    simp only [bind_ok]
    have hvv : (L.mem s' (regA snd (regIdx (mrIdx i.val)))).bv = V[i.val]! := by
      rw [snd_reg_keep hP hs hr hne hI'.2.2.1, hreg, (hV i.val (by omega)).2]
    rw [hvv] at hwv
    have hl : (Lr.take i.val).length = (V.take i.val).length := by
      simp [List.length_take]; have := (hV i.val (by omega)).1; omega
    refine WP.spec_bind (WP.spec_and (set_reg_rg_inv hH hP hr hI' hl Lr[i.val] V[i.val]! w hwv)
      (obj.Tcb.set_reg.spec s' rcv _ w)) ?_
    rintro s2 ⟨hI2, rfl⟩
    obtain ⟨V2, J2⟩ := J'.sanWrJ hr hl Lr[i.val] V[i.val]! w hwv
    obtain ⟨i6, h6e, h6v⟩ := spec_exists (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [h6e, bind_ok, WP.spec_ok]
    have hi6 : i6.val = i.val + 1 := by simpa using h6v
    refine ⟨⟨by show i6.val ≤ min n.val 4; rw [hi6]; exact Nat.le_min.2 ⟨by omega, by omega⟩, ?_⟩,
      by show n.val - i6.val < n.val - i.val; omega⟩
    show RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 rcv x0 _ (Lr.take i6.val) (V.take i6.val) ∧
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D _ a
        (updK σ0 rcv.bv (.tcb (sanRegs x0 (Lr.take i6.val) (V.take i6.val))))
    have hVl := (hV i.val (by omega)).1
    rw [hi6, List.take_succ, List.take_succ, List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hVl]
    simp only [Option.toList_some]
    rw [← getElem!_pos V i.val hVl]
    exact ⟨hI2, V2, J2⟩
  · refine ⟨by simp, by simpa using hI, Z.vs, ?_⟩
    show JAtZ (L := L) arI AR (Z.mv Z.G Z.vs) H Cs Ac Lst D s0 a (updK σ0 rcv.bv (.tcb (sanRegs x0 [] [])))
    rw [show sanRegs x0 [] [] = x0 from rfl, Endp.updK_self hk0]
    simpa using J

set_option maxHeartbeats 8000000 in
/-- **The second loop of `copy_mrs_fault_reply` at `J`** (as `cmfr_loop1`). -/
theorem cmfrJ_loop1 (hH : EpHyps st Z.T Z.E Z.R Z.B SR) (hP : EPlaced Z.T Z.E Z.R Z.B) {s0 : S}
    {σ0 : Fl4Spec.State Unit}
    (hR0 : EpStateRel Z.T Z.E Z.R Z.B (L.mem s0) σ0) {rcv : U64} (hr : rcv ∈ Z.T) {x0 : Fl4Spec.Tcb}
    {sw : U64} {sp : Fl4Spec.Word} (hms : BufMap Z.B sw sp)
    {sl : Slice U64} {Lr : List Fl4Spec.Register} (hsl : sl.val = Lr.map regIdx) (hLr : Lr.length < 32)
    (n : Usize) (hn : n.val ≤ Lr.length) (hn120 : n.val ≤ 120) {V : List Fl4Spec.Word}
    (hV : ∀ i, 4 ≤ i → i < n.val → i < V.length ∧
      V[i]! = loadWordAt σ0.machineState.underlyingMemory (bufAddr sp (i + 1)))
    (s1 : S) (i0 : Usize) (hi0 : 4 ≤ i0.val) (hi0n : i0.val ≤ n.val)
    (hI : RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 rcv x0 s1 (Lr.take i0.val) (V.take i0.val))
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a
      (updK σ0 rcv.bv (.tcb (sanRegs x0 (Lr.take i0.val) (V.take i0.val))))) :
    faults.copy_mrs_fault_reply_loop1 st s1 rcv sl n i0 sw ⦃ s2 =>
      RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 rcv x0 s2 (Lr.take n.val) (V.take n.val) ∧
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s2 a
        (updK σ0 rcv.bv (.tcb (sanRegs x0 (Lr.take n.val) (V.take n.val)))) ⦄ := by
  have hlen : (Slice.len sl).val = Lr.length := by simp [Slice.len, hsl]
  unfold faults.copy_mrs_fault_reply_loop1
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.val)
    (inv := fun x => 4 ≤ x.2.val ∧ x.2.val ≤ n.val ∧
      RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 rcv x0 x.1 (Lr.take x.2.val) (V.take x.2.val) ∧
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D x.1 a
        (updK σ0 rcv.bv (.tcb (sanRegs x0 (Lr.take x.2.val) (V.take x.2.val)))))
  · rintro ⟨s', i⟩ ⟨hi4, hin', hI', V', J'⟩
    unfold faults.copy_mrs_fault_reply_loop1.body
    simp only at hi4 hin' hI' J' ⊢
    by_cases hcn : i < n
    swap
    · rw [if_neg hcn, WP.spec_ok]
      have : i.val = n.val := by have := us_lt_iff.not.1 hcn; omega
      exact ⟨this ▸ hI', V', this ▸ J'⟩
    rw [if_pos hcn]
    have hin : i.val < n.val := us_lt_iff.1 hcn
    have h1 : i < Slice.len sl := us_lt_iff.2 (by omega)
    rw [if_pos h1]
    have hiL : i.val < Lr.length := by omega
    have hidx : Slice.index_usize sl i = ok (regIdx Lr[i.val]) := by
      unfold Slice.index_usize
      have : sl[i]? = some (regIdx Lr[i.val]) := by
        simp [Slice.getElem?_Usize_eq, hsl, List.getElem?_map, List.getElem?_eq_getElem hiL]
      rw [this]
    rw [hidx]
    simp only [lift, bind_ok]
    set k := core.num.U64.wrapping_add (UScalar.cast .U64 i) 1#u64 with hk
    have hkv : k.val = i.val + 1 := by
      rw [hk]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, cast_us i (by omega)]; omega
    refine WP.spec_bind (msg.buf_get.spec s' sw k) ?_
    rintro v rfl
    have hw := hms k (by omega)
    have hvv : (L.mem s' (fl4BufA sw k)).bv = V[i.val]! := by
      rw [buf_keep hP hr hI'.2.2.1 hw, hR0.buf _ hw, (hV i.val hi4 hin).2, hkv]
    obtain ⟨w, hw', hwv⟩ := sanitise_eq Lr[i.val] (L.mem s' (fl4BufA sw k))
    rw [hw']
    simp only [bind_ok]
    rw [hvv] at hwv
    have hl : (Lr.take i.val).length = (V.take i.val).length := by
      simp [List.length_take]; have := (hV i.val hi4 hin).1; omega
    refine WP.spec_bind (WP.spec_and (set_reg_rg_inv hH hP hr hI' hl Lr[i.val] V[i.val]! w hwv)
      (obj.Tcb.set_reg.spec s' rcv _ w)) ?_
    rintro s2 ⟨hI2, rfl⟩
    obtain ⟨V2, J2⟩ := J'.sanWrJ hr hl Lr[i.val] V[i.val]! w hwv
    obtain ⟨i5, h5e, h5v⟩ := spec_exists (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [h5e, bind_ok, WP.spec_ok]
    have hi5 : i5.val = i.val + 1 := by simpa using h5v
    refine ⟨⟨by show 4 ≤ i5.val; omega, by show i5.val ≤ n.val; omega, ?_⟩,
      by show n.val - i5.val < n.val - i.val; omega⟩
    show RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 rcv x0 _ (Lr.take i5.val) (V.take i5.val) ∧
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D _ a
        (updK σ0 rcv.bv (.tcb (sanRegs x0 (Lr.take i5.val) (V.take i5.val))))
    have hVl := (hV i.val hi4 hin).1
    rw [hi5, List.take_succ, List.take_succ, List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hVl]
    simp only [Option.toList_some]
    rw [← getElem!_pos V i.val hVl]
    exact ⟨hI2, V2, J2⟩
  · exact ⟨hi0, hi0n, hI, Z.vs, by simpa using J⟩

end Loops

section Top
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {a : A}

set_option maxHeartbeats 8000000 in
/-- **`copy_mrs_fault_reply` at `J`** over a register list `Lr` (as
`cmfr_top`): the receiver's registers `Lr` set to the sanitised `get_mrs`
words of the replier; its buffer looked up at the `J` state after the first
loop. -/
theorem cmfrJ_top
    (s : S) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {snd rcv : U64} (hs : snd ∈ Z.T) (hr : rcv ∈ Z.T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {sl : Slice U64} {Lr : List Fl4Spec.Register} (hsl : sl.val = Lr.map regIdx) (hLr : Lr.length < 32)
    (len : U64) (hlen : len.val ≤ 120) :
    faults.copy_mrs_fault_reply st s snd rcv sl len ⦃ s' => ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a
      (updK σ rcv.bv (.tcb (sanRegs xr Lr
        (specMrs xs.tcbArch.tcbContext.userRegs (ipcBufOf false xs) σ.machineState.underlyingMemory len.val)))) ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hR : EpStateRel Z.T Z.E Z.R Z.B (L.mem s) σ := hI.1.toE
  have hHc := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hH := hHc.epHyps hP0
  have hSR := IpcRel.toSRN hI.1 hI.2
  have hP := hP0.e
  set V := specMrs xs.tcbArch.tcbContext.userRegs (ipcBufOf false xs) σ.machineState.underlyingMemory len.val
    with hVdef
  have hxs := hR.at_tcb hs hks
  have hreg : ∀ r, (L.mem s (regA snd (regIdx r))).bv = xs.tcbArch.tcbContext.userRegs r := fun r => hxs.regs r
  have hslen : (Slice.len sl).val = Lr.length := by simp [Slice.len, hsl]
  unfold faults.copy_mrs_fault_reply
  simp only [lift, bind_ok]
  obtain ⟨n, hn, hnv⟩ : ∃ n : Usize, (if len < UScalar.cast .U64 (Slice.len sl) then ok (UScalar.cast .Usize len)
      else ok (Slice.len sl) : Result Usize) = ok n ∧ n.val = min len.val Lr.length := by
    have hc : (UScalar.cast .U64 (Slice.len sl) : U64).val = Lr.length := by
      rw [cast_us _ (by omega), hslen]
    by_cases h : len < UScalar.cast .U64 (Slice.len sl)
    · refine ⟨_, if_pos h, ?_⟩
      have := (gt_iff_val).1 h; rw [hc] at this
      rw [UScalar.cast_val_eq]
      rw [Nat.mod_eq_of_lt (by rw [UScalarTy.Usize_numBits_eq]; rcases System.Platform.numBits_eq with e | e <;>
        rw [e] <;> omega)]
      omega
    · refine ⟨_, if_neg h, ?_⟩
      have : ¬ len.val < Lr.length := fun h' => h ((gt_iff_val).2 (by rw [hc]; exact h'))
      rw [hslen]; omega
  rw [hn]
  simp only [bind_ok]
  refine WP.spec_bind (cmfrJ_loop0 (L := L) hH hP hs hr hne hkr hreg hsl hLr n (by omega)
    (fun i hi => specMrs_lo xs.tcbArch.tcbContext.userRegs (ipcBufOf false xs) σ.machineState.underlyingMemory
      len.val i (by omega) (by omega)) (rgInv_init hR hSR.1 hkr) J) ?_
  rintro ⟨s1, i2⟩ ⟨hi2, hI1, V1, J1⟩
  show (if i2 < n then _ else _) ⦃ _ ⦄
  have h2a : i2.val ≤ 4 := by rw [hi2]; exact Nat.min_le_right _ _
  have h2b : i2.val ≤ n.val := by rw [hi2]; exact Nat.min_le_left _ _
  have h2c : i2.val = n.val ∨ i2.val = 4 := by rw [hi2]; exact min_choice _ _
  have hna : n.val ≤ len.val := by rw [hnv]; exact Nat.min_le_left _ _
  have hnb : n.val ≤ Lr.length := by rw [hnv]; exact Nat.min_le_right _ _
  have hnc : n.val = len.val ∨ n.val = Lr.length := by rw [hnv]; exact min_choice _ _
  have hVl : V.length ≤ len.val := specMrs_len_le _ _ _ _
  have mle : ∀ k, (Lr.length ≤ k ∨ V.length ≤ k) → min Lr.length V.length ≤ k := fun k h => by
    rcases h with h | h
    · exact (Nat.min_le_left _ _).trans h
    · exact (Nat.min_le_right _ _).trans h
  have fin : ∀ s' k, min Lr.length V.length ≤ k →
      (∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a
        (updK σ rcv.bv (.tcb (sanRegs xr (Lr.take k) (V.take k))))) →
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a
        (updK σ rcv.bv (.tcb (sanRegs xr Lr V))) := by
    intro s' k hk h
    rw [sanRegs_take xr Lr V k hk] at h; exact h
  by_cases hlt : i2 < n
  swap
  · rw [if_neg hlt, WP.spec_ok]
    refine fin s1 i2.val (mle _ ?_) ⟨V1, J1⟩
    have := us_lt_iff.not.1 hlt
    omega
  rw [if_pos hlt]
  have hi2n : i2.val < n.val := us_lt_iff.1 hlt
  have hi24 : i2.val = 4 := by omega
  -- the replier's buffer, looked up at the `J` state after the first loop
  set σ1 := updK σ rcv.bv (.tcb (sanRegs xr (Lr.take i2.val) (V.take i2.val))) with hσ1
  have hk1 : σ1.kheap snd.bv = some (.tcb xs) := by
    simp [hσ1, updK, show snd.bv ≠ rcv.bv from fun e => hne (eq_of_bv e), hks]
  obtain ⟨Tr, Cq, hJ⟩ := J1.jpl
  have thT : Z.th snd = some .tcb := (hJ.tcb snd).2 (J1.zH.1 snd hs)
  obtain ⟨hOK1, hBC1, -⟩ := J1.xferH
  obtain ⟨xs', hks', hws⟩ := J1.buf snd hs
  rw [hk1] at hks'; cases hks'
  refine WP.spec_bind (lookup_buf_full s1 σ1 J1.xtop.rel.2.1.1 J1.xtop.rel.2.1.2.1 thT hk1 hOK1 false) ?_
  rintro sw ⟨hsw0, hswp⟩
  cases hsb : ipcBufOf false xs with
  | none =>
    have hswz : sw = 0#u64 := hsw0.2 hsb
    rw [if_neg (by simp [hswz]), WP.spec_ok]
    refine fin s1 i2.val (mle _ ?_) ⟨V1, J1⟩
    have : V.length ≤ 4 := by rw [hVdef, hsb]; exact specMrs_len_none _ _ _
    omega
  | some sp =>
    have hsw0' : sw ≠ 0#u64 := fun e => by have := hsw0.1 e; rw [hsb] at this; cases this
    have hms : BufMap Z.B sw sp := hBC1 snd hs xs false sp hk1 hsb sw (hswp hws sp hsb)
    rw [if_pos (by simp [hsw0'])]
    refine WP.spec_mono (cmfrJ_loop1 (L := L) (Z := Z.mv Z.G V1) hH hP hR hr hms hsl hLr n (by omega) (by omega) (V := V)
      (fun i h4 hin => by
        rw [hVdef, hsb]; exact specMrs_hi xs.tcbArch.tcbContext.userRegs sp σ.machineState.underlyingMemory len.val i h4
          (by omega) (by omega)) s1 i2
      (by omega) (by omega) hI1 J1) ?_
    rintro s2 ⟨-, V2, J2⟩
    exact fin s2 n.val (mle _ (by omega)) ⟨V2, J2⟩

set_option maxHeartbeats 8000000 in
/-- **`handle_fault_reply` at `J`** (module docstring), as
`handle_fault_reply_rel`: the spec's outcome `σ'` is the receiver's TCB
updated in its user context (`x'`), and the whole spec prefix of the fault
reply up to the fault clear is identified. -/
theorem _root_.Fl4Proofs.P3.JAtZ.hfrJ
    {s : S} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {rcv snd : U64} (hr : rcv ∈ Z.T) (hs : snd ∈ Z.T) (hne : snd ≠ rcv) {xr xs : Fl4Spec.Tcb}
    (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hks : σ.kheap snd.bv = some (.tcb xs))
    {f : Fl4Spec.Fault} (hf : xr.tcbFault = some f) :
    faults.handle_fault_reply st arI s a rcv snd ⦃ res => res.2.2 = a ∧ ∃ x',
      Fl4Spec.handleFaultReply (Z := Unit) f rcv.bv
        (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miLabel
        (specMrs xs.tcbArch.tcbContext.userRegs (ipcBufOf false xs) σ.machineState.underlyingMemory
          (Fl4Spec.unat (Fl4Spec.dataToMessageInfo
            (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miLength)) σ =
        ({(res.1, updK σ rcv.bv (.tcb x'))}, False) ∧
      (∀ z, z ∈ ((Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) rcv.bv >>= fun _ =>
        Fl4Spec.setThreadState (Z := Unit) rcv.bv (if res.1 then .restart else .inactive))
          (updK σ rcv.bv (.tcb x'))).1 → z ∈ (specFaultReply snd.bv rcv.bv f σ).1) ∧
      x' = { xr with tcbArch := x'.tcbArch } ∧
      ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D res.2.1 a (updK σ rcv.bv (.tcb x')) ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hR : EpStateRel Z.T Z.E Z.R Z.B (L.mem s) σ := hI.1.toE
  have hxs := hR.at_tcb hs hks
  have hxr := hR.at_tcb hr hkr
  obtain ⟨-, hBC, -⟩ := J.xferH
  -- the replier's buffer words are aligned
  have hal : ∀ sb, ipcBufOf false xs = some sb → ∀ k, k < 128 → (bufAddr sb k).toNat % 8 = 0 := by
    intro sb hsb k hk
    have hmb := hBC snd hs xs false sb hks hsb ⟨sb⟩ rfl
    have hv : (⟨BitVec.ofNat 64 k⟩ : U64).val = k := by
      show (BitVec.ofNat 64 k).toNat = k; simp; omega
    have h := (hP0.e.balign _ (hmb ⟨BitVec.ofNat 64 k⟩ (by rw [hv]; omega))).2
    rw [hv] at h; exact h
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  set w := xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register with hwdef
  set V := specMrs xs.tcbArch.tcbContext.userRegs (ipcBufOf false xs) σ.machineState.underlyingMemory
    (Fl4Spec.unat (Fl4Spec.dataToMessageInfo w).miLength) with hVdef
  -- the spec's prefix from its `handle_fault_reply`
  have hpre : ∀ (rst : Bool) (σ1 : Fl4Spec.State Unit),
      Fl4Spec.handleFaultReply (Z := Unit) f rcv.bv (Fl4Spec.dataToMessageInfo w).miLabel V σ = ({(rst, σ1)}, False) →
      ∀ z, z ∈ ((Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) rcv.bv >>= fun _ =>
        Fl4Spec.setThreadState (Z := Unit) rcv.bv (if rst then .restart else .inactive)) σ1).1 →
      z ∈ (specFaultReply snd.bv rcv.bv f σ).1 := by
    intro rst σ1 h1 z hz
    unfold specFaultReply
    rw [nd_bind_one (getMessageInfo_eq hks), nd_bind_one (lookupIpcBuffer_eq hks false),
      nd_bind_one (getMrs_eq hks _ hal _), nd_bind_one h1]
    exact hz
  have hfr := hxr.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  unfold faults.handle_fault_reply
  refine WP.spec_bind (msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, -, hle⟩
  rw [hwmi] at hlab hlen
  have hlab0 : decide (tag.label = 0#u64) = decide ((Fl4Spec.dataToMessageInfo w).miLabel = 0) := by
    refine decide_eq_decide.2 ⟨fun h => ?_, fun h => ?_⟩
    · show (w >>> 12) &&& Fl4Spec.mask Fl4Spec.msgLabelBits = 0
      rw [label_mask, ← hlab, h]; rfl
    · apply UScalar.eq_of_val_eq
      have : tag.label.bv = 0 := by rw [hlab]; rw [← label_mask w]; exact h
      show tag.label.bv.toNat = _; rw [this]; rfl
  have hlv : tag.length.val = Fl4Spec.unat (Fl4Spec.dataToMessageInfo w).miLength := by
    show tag.length.bv.toNat = _; rw [hlen]
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ty, hty⟩
  have same : ∀ rst, Fl4Spec.handleFaultReply (Z := Unit) f rcv.bv (Fl4Spec.dataToMessageInfo w).miLabel V σ =
      ({(rst, σ)}, False) →
      (ok (rst, s, a) : Result (Bool × S × A)) ⦃ res => res.2.2 = a ∧ ∃ x',
        Fl4Spec.handleFaultReply (Z := Unit) f rcv.bv (Fl4Spec.dataToMessageInfo w).miLabel V σ =
          ({(res.1, updK σ rcv.bv (.tcb x'))}, False) ∧
        (∀ z, z ∈ ((Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) rcv.bv >>= fun _ =>
          Fl4Spec.setThreadState (Z := Unit) rcv.bv (if res.1 then .restart else .inactive))
            (updK σ rcv.bv (.tcb x'))).1 → z ∈ (specFaultReply snd.bv rcv.bv f σ).1) ∧
        x' = { xr with tcbArch := x'.tcbArch } ∧
        ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D res.2.1 a (updK σ rcv.bv (.tcb x')) ⦄ := by
    intro rst h1
    rw [WP.spec_ok]
    refine ⟨rfl, xr, by rw [Endp.updK_self hkr]; exact h1,
      fun z hz => hpre rst σ h1 z (by rw [Endp.updK_self hkr] at hz; exact hz), rfl, Z.vs, ?_⟩
    rw [Endp.updK_self hkr]; simpa using J
  have regs_case : ∀ (sl : Slice U64) (lst : List Fl4Spec.Register), sl.val = lst.map regIdx → lst.length < 32 →
      (Fl4Spec.handleFaultReply (Z := Unit) f rcv.bv (Fl4Spec.dataToMessageInfo w).miLabel V σ =
        ({(decide ((Fl4Spec.dataToMessageInfo w).miLabel = 0), updK σ rcv.bv (.tcb (sanRegs xr lst V)))}, False)) →
      (do
        let s2 ← faults.copy_mrs_fault_reply st s snd rcv sl tag.length
        ok (decide (tag.label = 0#u64), s2, a)) ⦃ res => res.2.2 = a ∧ ∃ x',
        Fl4Spec.handleFaultReply (Z := Unit) f rcv.bv (Fl4Spec.dataToMessageInfo w).miLabel V σ =
          ({(res.1, updK σ rcv.bv (.tcb x'))}, False) ∧
        (∀ z, z ∈ ((Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) rcv.bv >>= fun _ =>
          Fl4Spec.setThreadState (Z := Unit) rcv.bv (if res.1 then .restart else .inactive))
            (updK σ rcv.bv (.tcb x'))).1 → z ∈ (specFaultReply snd.bv rcv.bv f σ).1) ∧
        x' = { xr with tcbArch := x'.tcbArch } ∧
        ∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D res.2.1 a (updK σ rcv.bv (.tcb x')) ⦄ := by
    intro sl lst hsl hl hspec
    refine WP.spec_bind (cmfrJ_top (L := L) s σ J hs hr hne hks hkr hsl hl tag.length hle) ?_
    intro s2 hJ2
    rw [hlv] at hJ2
    refine (WP.spec_ok _).2 ⟨rfl, sanRegs xr lst V, by rw [hspec, hlab0],
      fun z hz => hpre _ _ (by rw [hspec, hlab0]) z hz, ?_, hJ2⟩
    rw [← sanRegs_eq]
  cases f with
  | capFault c rp lf =>
    obtain ⟨h1, -⟩ := hfr
    rw [hty, h1, if_pos (by unfold fl4_abi.consts.fault.CapFault; rfl)]
    exact same true rfl
  | unknownSyscallException n =>
    obtain ⟨h1, -⟩ := hfr
    rw [hty, h1, if_neg (by unfold fl4_abi.consts.fault.CapFault; decide),
      if_pos (by unfold fl4_abi.consts.fault.UnknownSyscall; rfl)]
    simp only [lift, bind_ok]
    exact regs_case _ _ Fl4Proofs.P3.Endp.syscall_slice_val (by decide) (hfr_regs_eq hkr _ _ _)
  | userException e c =>
    obtain ⟨h1, -⟩ := hfr
    rw [hty, h1, if_neg (by unfold fl4_abi.consts.fault.CapFault; decide),
      if_neg (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
      if_pos (by unfold fl4_abi.consts.fault.UserException; rfl)]
    simp only [lift, bind_ok]
    exact regs_case _ _ Fl4Proofs.P3.Endp.exc_slice_val (by decide) (hfr_regs_eq hkr _ _ _)
  | timeout b =>
    obtain ⟨h1, -⟩ := hfr
    rw [hty, h1, if_neg (by unfold fl4_abi.consts.fault.CapFault; decide),
      if_neg (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
      if_neg (by unfold fl4_abi.consts.fault.UserException; decide),
      if_pos (by unfold fl4_abi.consts.fault.Timeout; rfl)]
    simp only [lift, bind_ok]
    exact regs_case _ _ timeout_slice_val (by decide) (hfr_regs_eq hkr _ _ _)
  | archFault af =>
    cases af with
    | vmFault ad d =>
      obtain ⟨h1, -⟩ := hfr
      rw [hty, h1, if_neg (by unfold fl4_abi.consts.fault.CapFault; decide),
        if_neg (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
        if_neg (by unfold fl4_abi.consts.fault.UserException; decide),
        if_neg (by unfold fl4_abi.consts.fault.Timeout; decide),
        if_neg (by unfold fl4_abi.consts.fault.DebugException; decide)]
      exact same true rfl

end Top

end

end Fl4Proofs.P3.Endp
