/-
P3 (DESIGN.md §9), TCB: **ReadFPU's frame writes at `J`** (for XTopJointTcb's
`tcb_read_fpuJ`: FL4's `copy_words` of a TCB's FPU image into a user frame).

* `FpuFrameJHyp` [J]: the destination frame cap's facts at the invocation's
  start that `JAtZ` does not carry (the cap's range meeting no non-`other`
  object of `H` is `JPlaced.cobj`'s `FrApartH`, which also keeps it off the
  TCBs; module docstring below).
* `JAtZ.frameWrJ`: a word that is not an IPC-buffer word written at `J`, the
  spec state kept: `XTopAt.userWr` (a `UserW` word), the slots kept (the word
  misses the VSpace objects, hence the slots, `vobj_of_slot`), the nodes and
  the IRQ node kept (the word misses the kernel's global data), the untyped
  caps' free parts untouched (the word lies in a spec object, `SpecFree`),
  P1's `BlkOK` by `blk_of_untracked` (as XTopJointData's `JAtZ.userWrJ`).
* `JAtZ.frameWordJ`: any frame word at `J`: an IPC-buffer word by
  `JAtZ.userWrJ` (the spec's user memory updated), another by
  `JAtZ.frameWrJ`.
* `JAtZ.copyFrameJ`: the 337-word copy into the frame at `J`
  (`copy_words_inv`): every word of the frame is a word of a spec data page,
  hence the IPC-buffer word `(w, w)` of `B` (JointAt's `FrameCover`), written
  by `JAtZ.userWrJ`; the spec's user memory then agrees with the old one
  outside the frame's 2696 bytes (the spec's `Fl4Spec.fl4FpuToFrame`).
  (`frameWrJ`/`frameWordJ` are no longer used by it.)

## `FpuFrameJHyp` [J]

For the frame cap in the first extra slot (non-device): its range lies in a
spec user data page (l4v `valid_cap`: `typ_at (AArch (AUserData sz)) p` for
a non-device `PageCap`; a DeriveSubframe alias lies inside the large frame's
page). Only the entry state is asked; the fact is carried across the
caller's restart (the data page is not the caller's TCB) and the arch's
`fpu_flush`. Until fpu1 (KENTRY-PLAN) it also asked the range to miss the
CNodes, FL4's VSpace tables and ASID pools and the kernel-global data; those
were needed only for frame words outside `B`, which `FrameCover` rules out.
-/
import Fl4Proofs.P3.XTopJointData
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **ReadFPU's destination frame at the invocation's start** [J] (module
docstring): every byte of the non-device frame cap at `x` lies in a spec
user frame (`UFr`: a non-device data page holds it; l4v `valid_cap` of a
non-device `PageCap`). This is exactly what `JAtZ.fcap` says of the slot, so
`JAtZ.fpuFrameJ` (XTopJointKEntry35E) proves it from `JAtZ` alone (g5b: the
former "one data page contains the whole range" form needed the spec-only
`SpecFrPg`; the copy needs only a page per written word, `ufr_word`). Asked
only when `x` is a slot of the typed heap (KENTRY-PLAN g5a: the extra-cap
array pads with slot 0, whose word nothing constrains; the consumer
`tcb_read_fpuJ` has the slot from `XcRel`). -/
def FpuFrameJHyp (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) (x : U64) : Prop :=
  ∀ sl0 : Fl4Spec.CslotPtr, AbsSlot Z.th sl0 → x = cslotAddr sl0 → ∀ (p : U64) (sz : capability.FrameSize) (r : U64) (m ep : Bool) (asid va : U64),
    capV (L.mem s) x = .Frame p sz r false m ep asid va →
    ∀ a : Nat, p.val ≤ a → a < p.val + 2 ^ frameBitsN sz → _root_.Fl4Proofs.P3.UFr σ a

end

/-- An aligned frame fits below `2^64`, at least a page, 8-byte aligned. -/
theorem frame_fit {p : U64} {sz : capability.FrameSize} (h : p.val % 2 ^ frameBitsN sz = 0) :
    4096 ≤ 2 ^ frameBitsN sz ∧ p.val % 8 = 0 ∧ p.val + 2 ^ frameBitsN sz ≤ 2 ^ 64 := by
  have hp : p.val < 2 ^ 64 := p.bv.isLt
  cases sz <;> simp only [frameBitsN, Nat.reducePow] at h ⊢ <;> omega

/-- The last byte of an aligned frame cap. -/
theorem frame_topF {p : U64} {sz : capability.FrameSize} (r : U64) (d m ep : Bool) (a va : U64)
    (h : p.val % 2 ^ frameBitsN sz = 0) :
    baseF (.Frame p sz r d m ep a va) = p.val ∧
      topF (.Frame p sz r d m ep a va) = p.val + 2 ^ frameBitsN sz - 1 := by
  obtain ⟨bs, ts⟩ := frame_range p sz r d m a va ep
  obtain ⟨h4, -, hfit⟩ := frame_fit h
  have hb : (fbitsF sz).val = frameBitsN sz := by rw [fbitsF_val]; cases sz <;> rfl
  have hb64 : (fbitsF sz).val < 64 := by rw [hb]; cases sz <;> simp [frameBitsN]
  have hmk : (maskF (fbitsF sz)).val = 2 ^ frameBitsN sz - 1 := by rw [maskF_val hb64, hb]
  refine ⟨bs, ?_⟩
  rw [ts]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hmk]
  omega

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

open Fl4Proofs.P1 in
set_option maxHeartbeats 16000000 in
/-- **A frame word that is not an IPC-buffer word, written at `J`** (module
docstring; the spec state kept). -/
theorem JAtZ.frameWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {w : U64}
    (hu : UserW (L := L) Z s σ w) (hnB : ∀ wp ∈ Z.B, wp.1 ≠ w)
    (hAp : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ w.val)
    (hObj : ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ w.val ∧ w.val < o.toNat + 2 ^ Fl4Spec.objBits ko)
    (hks : w.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ w.val) (v : U64) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.wr s w v) a σ := by
  set s1 := L.wr s w v with hs1
  have F : ArFr σ σ := ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hP := J.xtop.fin.1.2
  have hal : P1.Aligned w := hu.al
  have hW : P1.WritesIn st s s1 (· = w) := P1.writesIn_wr hal
  have hkb : L.ksb s1 = L.ksb s := hW.1
  have hcpu : L.cpu s1 = L.cpu s := hW.2.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_wr hP.pl s v hal fun x hx ⟨h1, h2⟩ =>
      hu.vobj (vobj_of_slot hP.pl Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) hx h1 h2)
  have hX1 : XTopAt (L := L) AR Z s1 a σ := J.xtop.userWr hu hnB v
  -- the frame words
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHk := J.kern.heap
  have objK : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → ∀ w' : U64, P1.Aligned w' → p.val ≤ w'.val →
      w'.val < p.val + 2 ^ k.bits → L.mem s1 w' = L.mem s w' := fun p k hp hk w' hal' g1 g2 =>
    hW.mem_eq hal' fun hb => by rw [hb] at g1 g2; rcases hAp p k hp hk with e | e <;> omega
  have tcbK : ∀ t ∈ Z.T, ∀ w' : U64, P1.Aligned w' → t.val ≤ w'.val → w'.val < t.val + 4096 →
      L.mem s1 w' = L.mem s w' := fun t ht w' hal' g1 g2 =>
    objK t .tcb (J.zH.1 t ht) (fun _ e => by cases e) w' hal' g1 (by simpa [P1.HKind.bits] using g2)
  have k1 : ∀ t ∈ Z.T, L.mem s1 (mcpA t) = L.mem s (mcpA t) := fun t ht =>
    tcbK t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega)
  have k2 : ∀ t ∈ Z.T, L.mem s1 (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    tcbK t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega)
  have kb : ∀ t ∈ Z.T, L.mem s1 (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    tcbK t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega)
  have scw : ∀ q z, H q = some (.sc z) → ∀ w' : U64, P1.Aligned w' → q.val ≤ w'.val → w'.val < q.val + 2 ^ z →
      L.mem s1 w' = L.mem s w' := fun q z hq w' hal' g1 g2 =>
    objK q _ hq (fun _ e => by cases e) w' hal' g1 (by simpa only [P1.HKind.bits] using g2)
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
  -- the debug word and the IRQ node: in the kernel-global data, which the word misses
  have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
  have hnb0 : L.nodeBase s 0#u64 = (L.ksb s).val + 13568 := by
    show (L.ksb s).val + 13568 + (0#u64 : U64).val * 4288 = _; simp
  have hDbg : L.mem s1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hdv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have hdo : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
    exact hW.mem_eq J.kern.dwAl fun hb => by
      rw [hb, hnb0] at hdv; omega
  have hirq : ∀ i : U64, i.val < 128 → capV (L.mem s1) (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hW J.kern.ksbFit J.kern.ksbAl fun b hb => by
      rw [hb]; omega
  -- the dead stay dead
  have hAI : ActIdle σ := J.act.ar F
  have yk : YKeep σ σ := ⟨fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩,
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
      have hcl := J.kern.csLt c hc
      have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
      omega
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
      Sched.UtCapP3 (L := L) arI Z.th s1 σ Z.G sl p sb fi := by
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
    · intro g w' hal' h1 h2
      rw [hW.mem_eq hal' fun hb => ?_]
      · exact U.zero (B g) w' hal' h1 h2
      rw [hb] at h1 h2
      obtain ⟨o, ko, hko, g1, g2⟩ := hObj
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) o ko hko
      omega
    · intro g h0 hf0
      rw [F.cdt] at h0
      obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
      exact ⟨fun sl' h => r1 sl' (by rw [← F.orig]; exact h), by rw [hna, hDbg]; exact r3⟩
  -- the spec's frames
  have ck : Sched.CKeep σ σ := ⟨fun q y n hq => ⟨y, F.sc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (F.look (fun _ e => by cases e)).2 hq, rfl, rfl⟩, fun p x n hp => ⟨x, F.sc.1 hp⟩⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hkb ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s1 σ :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) hkb hirq (J.idleW_keep hX1.fin.1.1.1 F.idle F.isc).2⟩
  have hkern := J.kern_keepA hkb hcpu hX1.fin.1.1.1 F hDbg
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s1 σ :=
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
    · have hcl := J.kern.csLt c hc
      have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
      omega
  exact J.cs_frameK hkb hX1 F.kback F.ipcFr (JCs.same J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (fun t ht => tcbK t (J.thT t ht) _ (Sched.tVcpuA_aligned J.ip.e.tcb (J.thT t ht)) (by rw [Sched.tVcpuA_val J.ip.e.tcb (J.thT t ht)]; omega) (by rw [Sched.tVcpuA_val J.ip.e.tcb (J.thT t ht)]; omega))
    hSS hKd F.idle

/-- **A frame word written at `J`** (`JAtZ.userWrJ` for an IPC-buffer word,
`JAtZ.frameWrJ` for another), the spec's machine state some `ms`. -/
theorem JAtZ.frameWordJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hBP : BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ) {w : U64}
    (hu : UserW (L := L) Z s σ w)
    (hAp : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ w.val)
    (hObj : ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ w.val ∧ w.val < o.toNat + 2 ^ Fl4Spec.objBits ko)
    (hks : w.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ w.val) (v : U64) :
    ∃ ms, JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.wr s w v) a { σ with machineState := ms } := by
  by_cases hB : ∃ wp ∈ Z.B, wp.1 = w
  · obtain ⟨wp, hwp, rfl⟩ := hB
    exact ⟨_, J.userWrJ hBP hwp hAp hObj v⟩
  · push_neg at hB
    exact ⟨σ.machineState, J.frameWrJ hu hB hAp hObj hks v⟩

/-- **An 8-aligned user-frame word lies with its 8 bytes in one data page**
(the page `inUserFrame` names: its base is the word rounded down to the page
size, a multiple of 8). -/
theorem ufr_word {σ : Fl4Spec.State Unit} {w : U64} (h8 : w.val % 8 = 0)
    (hU : _root_.Fl4Proofs.P3.UFr σ w.val) :
    ∃ o vms, σ.kheap o = some (.archObj (.dataPage false vms)) ∧ o.toNat ≤ w.val ∧
      w.val + 8 ≤ o.toNat + 2 ^ Fl4Spec.pageBitsForSize vms := by
  obtain ⟨sz, hk⟩ := hU
  refine ⟨_, sz, hk, ?_⟩
  rw [Endp.and_not_mask_toNat _ _ (Endp.pageBits_mem sz)]
  have hw : (BitVec.ofNat 64 w.val).toNat = w.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt w.bv.isLt
  rw [hw]
  have hm := Endp.pageBits_mem sz
  generalize Fl4Spec.pageBitsForSize sz = b at hm ⊢
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl <;> norm_num <;> omega

set_option maxHeartbeats 8000000 in
/-- **ReadFPU's copy into the frame at `J`** (`copy_words_inv` with
`JAtZ.userWrJ`): the 2696 bytes at `f` miss every non-`other` object of `H`
and lie in spec user frames (`ufr_word`: a data page per word), so each word `w` written is the IPC-buffer word
`(w, w)` of `B` (`FrameCover`); the spec's user memory is stored as FL4's
there, and so agrees with the old one outside the 2696 bytes at `f`
(`fpu_store_other`: the outcomes of `Fl4Spec.fl4FpuToFrame`). -/
theorem JAtZ.copyFrameJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (src f : U64) (hf8 : f.val % 8 = 0) (hfit : f.val + 2696 ≤ 2 ^ 64)
    (hApR : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → f.val + 2696 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ f.val)
    (hDP : ∀ a : Nat, f.val ≤ a → a < f.val + 2696 → _root_.Fl4Proofs.P3.UFr σ a) :
    tcb.copy_words st s src f 337#u64 ⦃ s' =>
      ∃ um : Fl4Spec.Word → Fl4Spec.Word8,
        (∀ a : Fl4Spec.Word, 2696 ≤ (a - f.bv).toNat → um a = σ.machineState.underlyingMemory a) ∧
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a (Endp.setUm σ um) ⦄ := by
  refine WP.spec_mono (copy_words_inv (fun s' => L.ksb s' = L.ksb s ∧
    ∃ um : Fl4Spec.Word → Fl4Spec.Word8,
      (∀ a : Fl4Spec.Word, 2696 ≤ (a - f.bv).toNat → um a = σ.machineState.underlyingMemory a) ∧
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a (Endp.setUm σ um)) s src f 337#u64
    ⟨rfl, σ.machineState.underlyingMemory, fun _ _ => rfl, J⟩ ?_) (fun _ h => h.2)
  rintro s2 i ⟨hk2, um, hag, J2⟩ hi v
  have hi' : i.val < 337 := hi
  set w := core.num.U64.wrapping_add f (core.num.U64.wrapping_mul i 8#u64) with hw
  have hwv : w.val = f.val + 8 * i.val := by
    rw [hw]
    simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
    simp [U64.size, U64.numBits]
    omega
  have hAp : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ w.val :=
    fun q k hq hk => by rcases hApR q k hq hk with e | e <;> omega
  obtain ⟨o, vms, hko, g1, g2⟩ := ufr_word (σ := σ) (w := w) (by omega) (hDP w.val (by omega) (by omega))
  have hwB : (w, w.bv) ∈ Z.B := J2.fcov o vms hko w (by omega) (by omega) (by omega)
  have hObj : ∃ o ko, (Endp.setUm σ um).kheap o = some ko ∧ o.toNat ≤ (w, w.bv).1.val ∧
      (w, w.bv).1.val < o.toNat + 2 ^ Fl4Spec.objBits ko :=
    ⟨o, _, hko, by show o.toNat ≤ w.val; omega,
      by show w.val < o.toNat + 2 ^ Fl4Spec.pageBitsForSize vms; omega⟩
  have J3 := J2.userWrJ J2.xferH.2.2 hwB hAp hObj v
  refine ⟨by rw [L.ksb_wr, hk2], Endp.storeMem um w.bv v.bv, fun b hb => ?_, J3⟩
  have hwv' : w.val = (f.bv.toNat + 8 * i.val) % 2 ^ 64 := by
    rw [hwv]; exact (Nat.mod_eq_of_lt (by show f.val + 8 * i.val < 2 ^ 64; omega)).symm
  rw [fpu_store_other um f.bv w (8 * i.val) (by omega) hwv' v.bv b hb]
  exact hag b hb

end

end

end Fl4Proofs.P3
