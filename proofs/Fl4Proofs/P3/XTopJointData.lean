/-
P3 (DESIGN.md §9), TCB: **the data reply tail at `J`** (the reply of the
TCB labels whose spec result is data: GetBreakpoint, ReadRegisters): the
message words by `set_mr` (registers, past `MR3` the caller's IPC buffer),
then `tcb::reply_words` (the badge and the message info), then `Running`,
from `JAtZ` before to `JAt` after, against the spec's `specTail true`.

* `JAtZ.userWrJ`: one IPC-buffer word written at `J` (FL4 writes a word of
  `Z.B`, the spec stores the matching user word: an `ArFr` step changing
  only the machine state, as XTopJointFinVs's `finVsJb`), given the word
  apart from every non-`other` object of `H` and inside a spec object (so
  outside the untyped caps' free parts, `SpecFree`). `XTopAt` after by
  VSpace's `bufw_inv` (`XTopAt.ofRInv`), the slots kept
  (`BufPlaced.slot`), P1's `BlkOK` by `blk_of_untracked` (the word
  untracked: P1's `UserOK` does not fit, its user words lie outside `H`'s
  `other` objects, which hold the frames).
* `JAtZ.bufWord`: those two facts for a word of a TCB's IPC buffer, from
  `JAtZ` alone with `IpcBufCapOK`: the TCB's IPC-frame slot holds a frame
  cap (`StateRel.bufCap`) whose range meets no non-`other` object of `H`
  (`JPlaced.cobj`, `FrApartH`), and the frame's data page is a spec object
  (`buf_frame_rng`, the buffer word's range in the frame by value).
* `JAtZ.setmrJ`: `set_mr` of the next word (a register by `JAtZ.regWrJ`, a
  buffer word by `JAtZ.userWrJ`), the spec's `set_mrs` state growing by the
  word (VSpace's `setmr_inv` at `JAtZ`), for any word list.
* `JAtZ.replyTailJ`: `reply_words` (badge, message info; `mrS_setReg`) and
  `Running` (`JAtZ.runJ`), `JAt` at the spec's success tail with data
  (`specTail_data`). With XTopReply's `data_tail_core` by `WP.spec_and`.
-/
import Fl4Proofs.P3.XTopJointDelR
import Fl4Proofs.P3.XTopJointReply
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- A machine-state-only spec step is an `ArFr` step. -/
theorem arFr_setUm (σ : Fl4Spec.State Unit) (um : Fl4Spec.Word → Fl4Spec.Word8) : ArFr σ (Endp.setUm σ um) :=
  ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

open Fl4Proofs.P1 in
set_option maxHeartbeats 16000000 in
/-- **One IPC-buffer word written at `J`** (module docstring). -/
theorem JAtZ.userWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hBP : BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ) {wp : U64 × Fl4Spec.Word} (hwB : wp ∈ Z.B)
    (hAp : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → wp.1.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ wp.1.val)
    (hObj : ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ wp.1.val ∧ wp.1.val < o.toNat + 2 ^ Fl4Spec.objBits ko)
    (v : U64) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.wr s wp.1 v) a
      (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv)) := by
  set s1 := L.wr s wp.1 v with hs1
  set σ1 := Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv) with hσ1
  have F : ArFr σ σ1 := arFr_setUm σ _
  have hP := J.xtop.fin.1.2
  have hal : P1.Aligned wp.1 := (hP.ep.balign wp hwB).1
  have hW : P1.WritesIn st s s1 (· = wp.1) := P1.writesIn_wr hal
  have hkb : L.ksb s1 = L.ksb s := hW.1
  have hcpu : L.cpu s1 = L.cpu s := hW.2.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_wr hP.pl s v hal fun x hx => BufPlaced.slot hP hwB hx
  have hX1 : XTopAt (L := L) AR Z s1 a σ1 :=
    J.xtop.ofRInv (bufw_inv s a σ J.xtop.toRInv hBP hwB v) hkb F.szKeep
  -- the frame words
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHk := J.kern.heap
  have objK : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → ∀ w : U64, P1.Aligned w → p.val ≤ w.val →
      w.val < p.val + 2 ^ k.bits → L.mem s1 w = L.mem s w := fun p k hp hk w hal' g1 g2 =>
    hW.mem_eq hal' fun hb => by subst hb; rcases hAp p k hp hk with e | e <;> omega
  have tcbK : ∀ t ∈ Z.T, ∀ w : U64, P1.Aligned w → t.val ≤ w.val → w.val < t.val + 4096 →
      L.mem s1 w = L.mem s w := fun t ht w hal' g1 g2 =>
    objK t .tcb (J.zH.1 t ht) (fun _ e => by cases e) w hal' g1 (by simpa [P1.HKind.bits] using g2)
  have k1 : ∀ t ∈ Z.T, L.mem s1 (mcpA t) = L.mem s (mcpA t) := fun t ht =>
    tcbK t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega)
  have k2 : ∀ t ∈ Z.T, L.mem s1 (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    tcbK t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega)
  have kb : ∀ t ∈ Z.T, L.mem s1 (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    tcbK t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega)
  have scw : ∀ q z, H q = some (.sc z) → ∀ w : U64, P1.Aligned w → q.val ≤ w.val → w.val < q.val + 2 ^ z →
      L.mem s1 w = L.mem s w := fun q z hq w hal' g1 g2 =>
    objK q _ hq (fun _ e => by cases e) w hal' g1 (by simpa only [P1.HKind.bits] using g2)
  have k3 : ∀ q ∈ Z.C, L.mem s1 (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun q hq => by
    obtain ⟨xq, nq, hkq, hin⟩ := screply_obj J.xtop.fin.1.1.1 hq
    have hHq := (hJ.sc q xq nq (J.c0 q hq) hkq).2
    exact scw q _ hHq _ (sc_reply_word J.xtop.fin.1.1.1 hq).1 hin.1 hin.2
  have k4 : ∀ r ∈ Z.R, L.mem s1 (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧
      L.mem s1 (P1.rNextA r) = L.mem s (P1.rNextA r) := by
    intro r hr
    have hal' := J.rp.align r hr
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s1 a' = L.mem s a' := fun a' ha =>
      objK r _ hHr (fun _ e => by cases e) a' (J.rp.aligned hr ha) (by omega)
        (by simp only [P1.HKind.bits]; omega)
    exact ⟨k _ (Or.inl (rPrevA_val hal')), k _ (Or.inr (rNextA_val hal'))⟩
  have hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s1 (scW q K) = L.mem s (scW q K) := by
    intro q z hq K hK8 hK
    have hal' := hHk.align q _ hq
    have hfit := hHk.fits q _ hq
    have hz := hHk.scmin q z hq
    simp only [P1.HKind.bits] at hal' hfit
    have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have hq8 : q.val % 8 = 0 := by
      have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
      rw [← Nat.mod_mod_of_dvd q.val hd, hal']
    have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
    exact scw q z hq _ (by show (scW q K).val % 8 = 0; rw [hv]; omega) (by omega) (by omega)
  -- the debug word and the IRQ node
  have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
  have hDbg : L.mem s1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hdv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have hdo : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
    exact hW.mem_eq J.kern.dwAl fun hb => by
      have := J.nodeB wp hwB 0#u64 (by simp)
      rw [hb] at hdv; omega
  have hnbc : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hirq : ∀ i : U64, i.val < 128 → capV (L.mem s1) (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hW J.kern.ksbFit J.kern.ksbAl fun b hb => by
      subst hb; have := hBP.far wp hwB; omega
  -- the dead stay dead
  have hAI : ActIdle σ1 := J.act.ar F
  have yk : YKeep σ σ1 := ⟨fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩,
    fun p x n hp => ⟨x, F.sc.2 hp, rfl⟩, fun p y n hp => ⟨y, F.sc.1 hp, rfl⟩⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s1 q := fun q hq =>
    J.deadP_keep hX1.fin.1.1.1 hX1.ipc
      (fun x hx _ => ⟨x, (F.look (fun _ e => by cases e)).2 hx, rfl, rfl, Or.inl rfl⟩)
      (fun x hx => (F.look (fun _ e => by cases e)).2 hx)
      (fun x hx => ⟨x, F.ntfn.2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, (F.look (fun _ e => by cases e)).2 hx, rfl⟩)
      (fun x n hx => ⟨x, F.sc.2 hx, Or.inl rfl, Or.inl rfl⟩) (k3 q) (fun z hz _ => hOut q z hz) F.idle hAI.1
      (J.yld.frame k2 yk) (yk.dk q.bv) (J.jcov.dead q hq)
  -- P1's `BlkOK`
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s1 := by
    refine (P1.blk_of_untracked J.blk hW fun b hb => ⟨⟨by rw [hb]; exact hal, fun t ht => ?_, fun c hc => ?_⟩,
      fun e he => ?_, fun hf => ?_⟩).1
    · subst hb
      rcases hAp t .tcb ht (fun _ e => by cases e) with e | e
      · left; omega
      · right; simpa [P1.HKind.bits] using e
    · subst hb
      rcases J.nodeB wp hwB c (J.kern.csLt c hc) with e | e <;> omega
    · subst hb
      rcases he with he | he
      · rcases hAp e _ he (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
      · rcases hAp e _ he (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
    · subst hb
      obtain ⟨-, p, k, hp, hk, hin⟩ := hf
      have hko : ∀ z, k ≠ .other z := by
        rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z e <;> cases e
      obtain ⟨g1, g2⟩ := hin
      rcases hAp p k hp hko with e | e <;> omega
  -- the untyped caps' facts
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s1) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s1 σ1 Z.G sl p sb fi := by
    intro sl p sb fi dev hsl hcap hdv
    have hna : ∀ c o, L.nodeAt s1 c o = L.nodeAt s c o := P1.nodeAt_of_ksb hkb
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
      rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
    have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
    have U := J.utc sl p sb fi dev hsl hcap0 hdv
    have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
      (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
    have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
    refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_,
      U.sb4, U.nostr, U.nsFree,
      fun h0 => U.ns (by rw [F.cdt] at h0; exact h0),
      ?_, fun g => by rw [hna]; exact U.dwReg (B g),
      fun g => by rw [F.gpml4]; exact U.gReg (B g)⟩
    · intro g w hal' h1 h2
      rw [hW.mem_eq hal' fun hb => ?_]
      · exact U.zero (B g) w hal' h1 h2
      subst hb
      obtain ⟨o, ko, hko, g1, g2⟩ := hObj
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) o ko hko
      omega
    · intro g h0 hf0
      rw [F.cdt] at h0
      obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
      exact ⟨fun sl' h => r1 sl' (by rw [← F.orig]; exact h), by rw [hna, hDbg]; exact r3⟩
  -- the spec's frames
  have ck : Sched.CKeep σ σ1 := ⟨fun q y n hq => ⟨y, F.sc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (F.look (fun _ e => by cases e)).2 hq, rfl, rfl⟩, fun p x n hp => ⟨x, F.sc.1 hp⟩⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hkb ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s1 σ1 :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) hkb hirq (J.idleW_keep hX1.fin.1.1.1 F.idle F.isc).2⟩
  have hkern := J.kern_keepA hkb hcpu hX1.fin.1.1.1 F hDbg
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s1 σ1 :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩),
      J.buf.frame kb (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩), hRP',
      J.apart.sc_frame hkb F.szKeep, hjpl, J.jcov_keep hkb hSS hdead (J.idleW_keep hX1.fin.1.1.1 F.idle F.isc), hkern,
      hutc, J.nsc.ar F, J.inv.ar F, CurInvW.ar J.cur F, J.own.ar F,
      J.off.ar F, hAI, J.bsa.ar F, J.isorted.ar F, J.curRun.ar F, hblk⟩
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1 := dbgKeep_of_writes J.blk hW fun b hb => by
    subst hb
    refine J.notDbg (fun t ht => ?_) (fun c hc => ?_)
    · rcases hAp t .tcb ht (fun _ e => by cases e) with e | e
      · left; omega
      · right; simpa [P1.HKind.bits] using e
    · rcases J.nodeB wp hwB c (J.kern.csLt c hc) with e | e <;> omega
  exact J.cs_frameK hkb hX1 F.kback F.ipcFr (JCs.same J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (fun t ht => tcbK t (J.thT t ht) _ (Sched.tVcpuA_aligned J.ip.e.tcb (J.thT t ht)) (by rw [Sched.tVcpuA_val J.ip.e.tcb (J.thT t ht)]; omega) (by rw [Sched.tVcpuA_val J.ip.e.tcb (J.thT t ht)]; omega))
    hSS hKd F.idle

/-- **The IPC-buffer word `k` lies in the buffer's frame** (as IpcBuf's
`buf_frame_base`, by value): at least the frame's base, its last byte below
the frame's end, the frame not wrapping. -/
theorem buf_frame_rng (vms : Fl4Spec.VMPageSize) (pb tb : BitVec 64) (k : Nat) (hk : k < 128)
    (hpb : pb.toNat % 2 ^ Fl4Spec.pageBitsForSize vms = 0) (htb : tb.toNat % 1024 = 0) :
    pb.toNat ≤ (Endp.bufAddr (pb + (tb &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k).toNat ∧
      (Endp.bufAddr (pb + (tb &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k).toNat + 8 ≤
        pb.toNat + 2 ^ Fl4Spec.pageBitsForSize vms ∧
      pb.toNat + 2 ^ Fl4Spec.pageBitsForSize vms ≤ 2 ^ 64 := by
  have hm := Endp.pageBits_mem vms
  set b := Fl4Spec.pageBitsForSize vms with hbdef
  have hb : 12 ≤ b ∧ b ≤ 30 := by simp at hm; omega
  have h2b : 1024 ∣ 2 ^ b := by
    have : 2 ^ 10 ∣ 2 ^ b := Nat.pow_dvd_pow 2 (by omega)
    simpa using this
  have hpos : 0 < 2 ^ b := by positivity
  have hpbL := pb.isLt
  have htbL := tb.isLt
  have hoff := Endp.mask_toNat' b hm tb
  have hoff1 : tb.toNat % 2 ^ b % 1024 = 0 := by
    rw [Nat.mod_mod_of_dvd _ h2b]; exact htb
  have hoff2 : tb.toNat % 2 ^ b < 2 ^ b := Nat.mod_lt _ hpos
  have hb64 : 2 ^ b ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
  have hpbm : pb.toNat + 2 ^ b ≤ 2 ^ 64 := by
    obtain ⟨a, ha⟩ := Nat.dvd_of_mod_eq_zero hpb
    obtain ⟨c, hc⟩ := hb64
    have : a < c := by
      by_contra h; push_neg at h
      have := Nat.mul_le_mul_left (2 ^ b) h; omega
    have := Nat.mul_le_mul_left (2 ^ b) (Nat.succ_le_of_lt this)
    rw [Nat.mul_succ] at this; omega
  unfold Endp.bufAddr
  rw [BitVec.toNat_add, BitVec.toNat_add, hoff, BitVec.toNat_ofNat]
  have hk8 : k * Fl4Spec.wordSize % 2 ^ 64 = k * 8 := by
    simp only [Fl4Spec.wordSize]; omega
  rw [hk8]
  have h1 : (pb.toNat + tb.toNat % 2 ^ b) % 2 ^ 64 = pb.toNat + tb.toNat % 2 ^ b := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have h3 : tb.toNat % 2 ^ b + k * 8 + 8 ≤ 2 ^ b := by
    have : tb.toNat % 2 ^ b ≤ 2 ^ b - 1024 := by
      obtain ⟨q, hq⟩ := h2b
      omega
    omega
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxHeartbeats 8000000 in
/-- **A word of a TCB's IPC buffer at `J`** (for `JAtZ.userWrJ`): apart from
every non-`other` object of `H` (the TCB's IPC-frame slot holds a frame cap,
`StateRel.bufCap`, whose range meets no such object, `JPlaced.cobj`'s
`FrApartH`) and inside a spec object (the frame's data page, `IpcBufCapOK`). -/
theorem JAtZ.bufWord (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hOK : Endp.IpcBufCapOK σ) {t : U64}
    (ht : Z.th t = some .tcb) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {q : Fl4Spec.ObjRef}
    (hq : Endp.ipcBufOf true x = some q) (k : Nat) (hk128 : k < 128) {b : U64} (hb : b.bv = Endp.bufAddr q k) :
    (∀ p k', H p = some k' → (∀ z, k' ≠ .other z) → b.val + 8 ≤ p.val ∨ p.val + 2 ^ k'.bits ≤ b.val) ∧
      ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ b.val ∧ b.val < o.toNat + 2 ^ Fl4Spec.objBits ko := by
  have hbv : b.val = (Endp.bufAddr q k).toNat := by rw [← hb]; rfl
  unfold Endp.ipcBufOf at hq
  split at hq
  · rename_i dev pb R mt vms md he
    split_ifs at hq with hc
    cases hq
    have hro : Fl4Spec.vmReadOnly ⊆ R := by
      rcases hc with h | ⟨h, -⟩
      · exact fun z hz => h (by unfold Fl4Spec.vmReadOnly Fl4Spec.vmReadWrite at *; simp at hz ⊢; simp [hz])
      · exact h
    obtain ⟨-, -, hd, ha, hpa⟩ := hOK t.bv x hk dev pb R mt vms md he hro
    obtain ⟨r1, r2, r3⟩ := buf_frame_rng vms pb x.tcbIpcBuffer k hk128 hpa ha
    rw [← hbv] at r1 r2
    refine ⟨?_, ?_⟩
    swap
    · obtain ⟨sz', hsz'⟩ := hd k hk128
      have hn := Endp.and_not_mask_toNat (Endp.bufAddr (pb + (x.tcbIpcBuffer &&&
        Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k) _ (Endp.pageBits_mem sz')
      have hpos : 0 < 2 ^ Fl4Spec.pageBitsForSize sz' := by positivity
      have hlo := Nat.div_mul_le_self (Endp.bufAddr (pb + (x.tcbIpcBuffer &&&
        Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k).toNat (2 ^ Fl4Spec.pageBitsForSize sz')
      have hhi := Nat.lt_div_mul_add (a := (Endp.bufAddr (pb + (x.tcbIpcBuffer &&&
        Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k).toNat) hpos
      refine ⟨_, _, hsz', ?_, ?_⟩
      · rw [hn, hbv]; exact hlo
      · show b.val < _ + 2 ^ Fl4Spec.pageBitsForSize sz'
        rw [hn, hbv]; exact hhi
    intro p k' hp hk'
    obtain ⟨x', c, hkx, hcap, hcr⟩ := J.xtop.rel.2.1.1.bufCap ht
    rw [hk] at hkx; cases hkx
    rw [he] at hcr
    obtain ⟨-, h2⟩ := hcr
    cases c <;> try (simp [absCap] at h2; done)
    case Frame p0 sz r0 d0 m0 ep0 as0 va0 =>
      simp only [absCap] at h2
      injection h2 with h2
      injection h2 with _ hp0 _ _ hsz _
      have hsl : IsSlot Z.th (slotOf t 2) := ⟨t, 2, Or.inr ⟨ht, by simp [tcbSlots]⟩, rfl⟩
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hcv : capV (L.mem s) (slotOf t 2) = .Frame p0 sz r0 d0 m0 ep0 as0 va0 := capV_of_capAt hcap
      have hFA : Sched.FrApartH H (.Frame p0 sz r0 d0 m0 ep0 as0 va0) := by
        have := hJ.cobj _ hsl; rw [hcv] at this; exact this
      obtain ⟨bs, ts⟩ := frame_range p0 sz r0 d0 m0 as0 va0 ep0
      have hm := Endp.pageBits_mem vms
      have hbits : (fbitsF sz).val = Fl4Spec.pageBitsForSize vms := by rw [fbitsF_val, hsz]
      have hmk : (maskF (fbitsF sz)).val = 2 ^ Fl4Spec.pageBitsForSize vms - 1 := by
        rw [maskF_val (by rw [hbits]; simp at hm; omega), hbits]
      have hpv : p0.val = pb.toNat := by rw [← hp0]; rfl
      have hpos : 0 < 2 ^ Fl4Spec.pageBitsForSize vms := by positivity
      have htop : topF (.Frame p0 sz r0 d0 m0 ep0 as0 va0) = p0.val + 2 ^ Fl4Spec.pageBitsForSize vms - 1 := by
        rw [ts]
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hmk]
        omega
      rcases hFA p k' hp hk' with e | e
      · rw [bs] at e; right; omega
      · rw [htop] at e; left; omega
  · cases hq

/-- FL4's buffer word `i` at the spec's buffer address (both wrapping). -/
theorem fl4BufA_bv (w i : U64) : (Endp.fl4BufA w i).bv = Endp.bufAddr w.bv i.val := by
  apply BitVec.eq_of_toNat_eq
  simp only [Endp.fl4BufA, Endp.bufAddr, UScalar.bv_toNat, core.num.U64.wrapping_add_val_eq,
    core.num.U64.wrapping_mul_val_eq, BitVec.toNat_add, BitVec.toNat_ofNat, Fl4Spec.wordSize]
  simp [U64.size_def, U64.numBits]

theorem mrIdx_ne_badge (k : Nat) : Endp.mrIdx k ≠ Fl4Spec.badge_register := fun e =>
  badge_not_mr (e ▸ Endp.mrIdx_mem k)

/-- **What `JAtZ.setmrJ` reads of a buffer word**: apart from every
non-`other` object of `H`, inside a spec object of `σ0` (`JAtZ.bufWord`). -/
def BufWordOK (H : P1.Heap) (σ0 : Fl4Spec.State Unit) (b : U64) : Prop :=
  (∀ p k', H p = some k' → (∀ z, k' ≠ .other z) → b.val + 8 ≤ p.val ∨ p.val + 2 ^ k'.bits ≤ b.val) ∧
    ∃ o ko, σ0.kheap o = some ko ∧ o.toNat ≤ b.val ∧ b.val < o.toNat + 2 ^ Fl4Spec.objBits ko

set_option maxHeartbeats 16000000 in
/-- **`set_mr` of the next message word at `J`** (VSpace's `setmr_inv` at
`JAtZ`): a register (`JAtZ.regWrJ`) or a buffer word (`JAtZ.userWrJ`), the
spec's `set_mrs` state growing by the word. -/
theorem JAtZ.setmrJ {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb} {buf : Option Fl4Spec.ObjRef}
    {ms : List Fl4Spec.Word} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (MrS σ0 ct.bv x0 buf ms))
    (hct : ct ∈ Z.T) (hk0 : σ0.kheap ct.bv = some (.tcb x0)) (w : U64) (hw0 : w = 0#u64 ↔ buf = none)
    (hbm : ∀ p, buf = some p → Endp.BufMap Z.B w p) (hBP : BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ0)
    (hOK : ∀ p, buf = some p → ∀ i : U64, i.val < 128 → BufWordOK H σ0 (Endp.fl4BufA w i))
    (i : U64) (hi : i.val = ms.length) (hi' : ms.length < 120) (v : U64) :
    msg.set_mr st s ct w i v ⦃ r => r.1.val = mrLen buf (ms.length + 1) ∧ L.ksb r.2 = L.ksb s ∧
      ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D r.2 a (MrS σ0 ct.bv x0 buf (ms ++ [v.bv])) ⦄ := by
  have hkx := MrS_kheap_t σ0 ct.bv x0 buf ms
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  unfold msg.set_mr
  by_cases h4 : i < msg.N_MSG_REGISTERS
  · have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h4; omega
    simp only [h4, ↓reduceIte]
    refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
    rintro r rfl
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct _ v) ?_
    rintro s1 rfl
    simp only [lift, bind_ok, WP.spec_ok]
    have hX := reg_wr_irel J.ip (J.xtop.irelK J.ks J.buf) hct hkx (Endp.mrIdx i.val) (mrIdx_ne_badge _) v
    obtain ⟨V, J1⟩ := J.regWrJ hct hkx (Endp.mrIdx i.val) v hX
    refine ⟨?_, L.ksb_wr _ _ _, V, ?_⟩
    · have : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      rw [this, hi]; cases buf <;> simp [mrLen] <;> omega
    · cases buf with
      | none =>
        have e := Endp.mrStateN_snoc_lt σ0 ct.bv x0 ms v.bv i.val hi (by omega)
        simp only [MrS] at J1 ⊢; rw [← e]; exact J1
      | some p =>
        have e := Endp.mrState_snoc_lt σ0 ct.bv x0 p ms v.bv i.val hi (by omega)
        simp only [MrS] at J1 ⊢; rw [← e]; exact J1
  · have hi4 : 4 ≤ i.val := by
      have : ¬ i.val < 4 := fun h => h4 ((P1.gt_iff_val).2 (by rw [hN]; exact h)); omega
    rw [if_neg h4]
    cases buf with
    | none =>
      have hw : w = 0#u64 := hw0.2 rfl
      simp only [hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨by rw [hN]; simp [mrLen]; omega, by first | rfl | trivial, Z.vs, ?_⟩
      simp only [MrS] at J ⊢
      rw [Endp.mrStateN_append_ge _ _ _ _ _ (by omega)]; exact J
    | some p =>
      have hw : w ≠ 0#u64 := fun h => by cases hw0.1 h
      have hb : (w != 0#u64) = true := by simp [hw]
      simp only [hb, ↓reduceIte]
      unfold lift
      apply Endp.ok_bind_spec
      refine WP.spec_bind (Endp.msg.buf_set.spec s w _ v) ?_
      rintro s1 rfl
      have hiv : (core.num.U64.wrapping_add i 1#u64).val = ms.length + 1 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have hwB := hbm p rfl (core.num.U64.wrapping_add i 1#u64) (by omega)
      have hBP' : BufPlaced (L := L) Z.N Z.C Z.B Z.c s (MrS σ0 ct.bv x0 (some p) ms) :=
        hBP.mono rfl (MrS_sc hk0 _ _)
      obtain ⟨hAp, o, ko, hko, g1, g2⟩ := hOK p rfl (core.num.U64.wrapping_add i 1#u64) (by omega)
      have hObj : ∃ o ko, (MrS σ0 ct.bv x0 (some p) ms).kheap o = some ko ∧
          o.toNat ≤ (Endp.fl4BufA w (core.num.U64.wrapping_add i 1#u64)).val ∧
          (Endp.fl4BufA w (core.num.U64.wrapping_add i 1#u64)).val < o.toNat + 2 ^ Fl4Spec.objBits ko := by
        by_cases e : o = ct.bv
        · subst e; rw [hk0] at hko; cases hko
          exact ⟨_, _, MrS_kheap_t _ _ _ _ _, g1, g2⟩
        · exact ⟨o, ko, by rw [MrS_kheap_ne _ _ _ _ _ e]; exact hko, g1, g2⟩
      have J1 := J.userWrJ hBP' hwB hAp hObj v
      simp only [lift, bind_ok, WP.spec_ok]
      refine ⟨by rw [hiv]; simp [mrLen], L.ksb_wr _ _ _, Z.vs, ?_⟩
      simp only [hiv] at J1
      simp only [MrS] at J1 ⊢
      rw [← Endp.mrState_snoc_ge _ _ _ _ _ _ (by omega) hi']
      exact J1

set_option maxHeartbeats 16000000 in
/-- **The reply tail at `J`** (`reply_words` then `Running`, as XTopReply's
`reply_tail_inv`): from `JAtZ` at the spec's `set_mrs` state of the words
`ms` (the caller `Restart`), `JAt` at the spec's success tail with data
(`specTail_data`). -/
theorem JAtZ.replyTailJ {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb} {ms : List Fl4Spec.Word}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (MrS σ0 ct.bv x0 (Endp.ipcBufOf true x0) ms))
    (hct : ct ∈ Z.T) (hk0 : σ0.kheap ct.bv = some (.tcb x0)) (hrs : x0.tcbState = .restart)
    (hlen : ms.length ≤ Fl4Spec.msgMaxLength)
    (hfr : ∀ p, Endp.ipcBufOf true x0 = some p → ∀ z ∈ Endp.mrPairs ms,
      (Endp.bufAddr p z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p z.1) σ0)
    (n : U64) (hn : n.val = mrLen (Endp.ipcBufOf true x0) ms.length) (hn128 : n.val < 128) :
    (do
      let s4 ← tcb.reply_words st s ct n
      sched.set_thread_state st s4 ct sched.TS_RUNNING) ⦃ s5 =>
        ∀ z ∈ (specTail true ct.bv ms σ0).1, JAt (L := L) arI AR s5 a z.2 ⦄ := by
  set buf := Endp.ipcBufOf true x0
  have hkx := MrS_kheap_t σ0 ct.bv x0 buf ms
  refine WP.spec_bind (Pₘ := fun s4 => ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s4 a
    (replyStateB σ0 ct.bv x0 buf ms)) ?_ ?_
  swap
  · rintro s4 ⟨V2, J2⟩
    refine WP.spec_mono (J2.runJ hct (replyStateB_kheap_t _ _ _ _ _) (by rw [replyTcbB_state, hrs])) ?_
    rintro s5 ⟨Lst', D', J5⟩ z hz
    rw [specTail_data hk0 hrs ms hlen hfr] at hz
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨_, _, _, _, _, _, J5⟩
  unfold tcb.reply_words
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
  rintro s1 rfl
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
  exact ⟨V2, J2⟩

end

end

end Fl4Proofs.P3
