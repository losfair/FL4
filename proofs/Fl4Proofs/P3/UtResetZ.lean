/-
P3 (DESIGN.md §9), untyped: **the reset's memory clears at `J`** (handoff
utj.md Round 11, item 3a).

FL4's `reset_untyped` clears the region of a childless RAM untyped cap chunk
by chunk (`clear_free` = `L.zr`). After the drop step (UtDropJ2's
`JAtZ.drop`) no relation reads a word of the region, so `JAtZ` survives the
clears with the spec state kept (the spec's own clears, `deleteObjects`'
`freeMemory` and the chunks' `clearMemory`, store zeros over zeros).

* `Sched.SchedRel.ws_far`: `SchedRel.wr_far` for writes in a set `W` of
  `Far` words.
* `XTopAt.userWs`: `XTopAt.userWr` for writes in a set `W` of user words
  (`UserW`) none an IPC-buffer word.
* `JAtZ.zeroJ`: `JAtZ` across `L.zr s q n`, the cleared range's words user
  words, not IPC-buffer words, apart from every non-`other` object of `H`,
  from the kernel-state block and from every core's node (XTopJointReadFpu's
  `JAtZ.frameWrJ` for a range of zeros: the untyped caps' zero parts stay
  zero, so no word needs to lie in a spec object).
-/
import Fl4Proofs.P3.XTopJointReadFpu
import Fl4Proofs.P3.XTopJointCnDel
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
open Fl4Proofs.P1

/-- **Writes far from what the scheduler relation reads keep it**
(`SchedRel.wr_far` for a set of words). -/
theorem Sched.SchedRel.ws_far {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {W : U64 → Prop} (hW : P1.WritesIn st s s' W)
    (hf : ∀ b, W b → Far st T C c s σ b) :
    SchedRel st N T C c s' σ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hnode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun o ho h8 => hW.mem_eq (nodeAt_aligned hN ho h8) (fun hb => by
      have hk := (hf _ hb).1
      rw [nodeAt_val hN ho] at hk; simp only [LawfulStore.nodeBase] at hk ⊢; omega)
  have hksb : ∀ K : U64, 8 ≤ K.val → K.val < 13568 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add (L.ksb s) K) = L.mem s (core.num.U64.wrapping_add (L.ksb s) K) := by
    intro K h1 h2 h3
    have hfi := hN.fits; have hal := hN.align
    simp only [LawfulStore.nodeBase] at hfi hal
    have hv : (core.num.U64.wrapping_add (L.ksb s) K).val = (L.ksb s).val + K.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine hW.mem_eq ?_ (fun hb => by
      have hk := (hf _ hb).1
      rw [hv] at hk; simp only [LawfulStore.nodeBase] at hk; omega)
    unfold Aligned; rw [hv]; omega
  have ha' : SAgree st T C c s s' := by
    refine ⟨hW.1, hW.2.1, fun o ho h8 _ _ _ _ _ => hnode o ho h8, fun y hy K hK => ?_,
      by unfold curDomA; exact hksb 8#u64 (by simp) (by simp) (by simp),
      by unfold dtA; exact hksb 16#u64 (by simp) (by simp) (by simp), fun sc' hsc' b hb hin => ?_⟩
    · obtain ⟨h1, h2, -⟩ := schedField_ok hK
      have hya := hc.tcbs y hy
      refine hW.mem_eq (field_aligned hya h1 h2) (fun hb => ?_)
      have := (hf _ hb).2.1 y hy
      rw [tfield_val hya h1] at this; omega
    · obtain ⟨x, n, hkx, hx⟩ := hs.scs sc' hsc'
      have hin' := hx.in_obj hin
      refine hW.mem_eq hb (fun hb' => ?_)
      have := (hf _ hb').2.2 sc' hsc' x n hkx; unfold ScObj at hin'; omega
  refine hS.of_sagree ha' ?_ ?_ ⟨rfl, rfl, fun _ => Or.inl rfl⟩
  · unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hW.1]
    exact hnode _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  · unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hW.1]
    exact hnode _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

set_option maxHeartbeats 4000000 in
/-- **Writes in a set of user words, none an IPC-buffer word**, keep
`XTopAt` (`XTopAt.userWr` for a set of words; the spec's state kept). -/
theorem XTopAt.userWs {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hu : ∀ b, W b → UserW (L := L) Z s σ b) (hnB : ∀ wp ∈ Z.B, ¬ W wp.1) :
    XTopAt (L := L) AR Z s' a σ := by
  have hSch := hX.fin.1.1.1
  have hP := hX.fin.1.2
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  have hT := hc.tcbs
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  -- a written word is off the kernel-state block below the core's node
  have hfar : ∀ b, W b → b.val + 8 ≤ (L.ksb s).val ∨ L.nodeBase s Z.c + 4288 ≤ b.val := fun b hb =>
    (hu b hb).far.1
  have hne : ∀ x : U64, P1.Aligned x → (L.ksb s).val ≤ x.val → x.val < (L.ksb s).val + 13568 →
      L.mem s' x = L.mem s x := fun x hx h1 h2 => hw.mem_eq hx fun hb => by
    have := hfar x hb; have := (hu x hb).al; unfold P1.Aligned at *; omega
  refine hX.frameStepV hw (fun x hx => (hu x hx).vobj) (fun x hx hf => ?_) (fun x hx hf => ?_)
    (fun hx => ?_) rfl rfl rfl rfl rfl rfl rfl (hSch.ws_far hw fun b hb => (hu b hb).far) ?_ ?_ ?_
    hX.fin.1.1.2.2.2.2.2.2
  · have hu' := hu x hx
    have hbal : x.val % 8 = 0 := hu'.al
    obtain ⟨-, hf2, -⟩ := hu'.far
    rcases hf with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hwp, h⟩
    · have := hu'.ep e he; have := (hP.ep.ep e he).1; omega
    · have := hu'.rep r hr; have := (hP.ep.rep r hr).1; omega
    · have := hf2 t ht; have := h.range; have := (hT t ht).align; omega
    · have := hf2 t ht; unfold Endp.TL at h; have := (hT t ht).align; omega
    · exact hnB wp hwp (h ▸ hx)
  · have hu' := hu x hx
    obtain ⟨-, hf2, -⟩ := hu'.far
    rcases hf with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩
    · have := hu'.ntfn n hn; omega
    · have hv := nfootT_val (hT t ht) h
      have := hf2 t ht; have := (hT t ht).align; omega
  · have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have := hfar _ hx
    rw [hkv] at this; omega
  · have hI := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, fun i hi => hI.node i hi⟩
    have hv := irqStA_val hkf hi
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega) (by omega)]
    exact hI.st i hi
  · have hI := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hwi : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have hv := ioA_val hkf hwi
    unfold bitOf
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega) (by omega)]
    exact hI p hp
  · refine hX.rel.2.2.2.1.frame (fun o ho => ?_) rfl rfl
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    exact hne _ (by unfold P1.Aligned; rw [hv]; omega) (by omega) (by omega)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

open Fl4Proofs.P1 in
set_option maxHeartbeats 16000000 in
/-- **A range of words cleared at `J`** (module docstring; the spec state
kept): `[q, q+n)` holds user words only, no IPC-buffer word, meets no
non-`other` object of `H`, and misses the kernel-state block and every
core's node. -/
theorem JAtZ.zeroJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {q n : U64} (hal : P1.Aligned q)
    (hn8 : n.val % 8 = 0) (hfit : q.val + n.val ≤ 2 ^ 64)
    (hu : ∀ b : U64, P1.Aligned b → q.val ≤ b.val → b.val < q.val + n.val → UserW (L := L) Z s σ b)
    (hnB : ∀ wp ∈ Z.B, ¬ (q.val ≤ wp.1.val ∧ wp.1.val < q.val + n.val))
    (hAp : ∀ r k, H r = some k → (∀ z, k ≠ .other z) → q.val + n.val ≤ r.val ∨ r.val + 2 ^ k.bits ≤ q.val)
    (hks : q.val + n.val ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ q.val)
    (hnd : ∀ c ∈ Cs, q.val + n.val ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ q.val) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.zr s q n) a σ := by
  set s1 := L.zr s q n with hs1
  have F : ArFr σ σ := ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hP := J.xtop.fin.1.2
  have hq8 : q.val % 8 = 0 := hal
  let W : U64 → Prop := fun b => P1.Aligned b ∧ q.val ≤ b.val ∧ b.val < q.val + n.val
  have hW : P1.WritesIn st s s1 W := by
    have h := P1.writesIn_zr (st := st) (s := s) hal hn8 hfit
    exact ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun hr => hn ⟨hb, hr⟩⟩
  have hkb : L.ksb s1 = L.ksb s := hW.1
  have hcpu : L.cpu s1 = L.cpu s := hW.2.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_of_vobj hP.pl fun b hb hv => hW.mem_eq hb fun hw => (hu b hw.1 hw.2.1 hw.2.2).vobj hv
  have hX1 : XTopAt (L := L) AR Z s1 a σ :=
    J.xtop.userWs hW (fun b hb => hu b hb.1 hb.2.1 hb.2.2) (fun wp hwp hw => hnB wp hwp hw.2)
  -- the frame words
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHk := J.kern.heap
  have objK : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → ∀ w' : U64, P1.Aligned w' → p.val ≤ w'.val →
      w'.val < p.val + 2 ^ k.bits → L.mem s1 w' = L.mem s w' := fun p k hp hk w' hal' g1 g2 =>
    hW.mem_eq hal' fun hb => by obtain ⟨-, h1, h2⟩ := hb; rcases hAp p k hp hk with e | e <;> omega
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
  -- the debug word and the IRQ node: in the kernel-global data, which the range misses
  have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
  have hnb0 : L.nodeBase s 0#u64 = (L.ksb s).val + 13568 := by
    show (L.ksb s).val + 13568 + (0#u64 : U64).val * 4288 = _; simp
  have hDbg : L.mem s1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hdv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have hdo : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
    have h0 := hnd 0#u64 J.kern.cs0
    exact hW.mem_eq J.kern.dwAl fun hb => by
      obtain ⟨-, h1, h2⟩ := hb
      rw [hdv] at h1 h2; omega
  have hirq : ∀ i : U64, i.val < 128 → capV (L.mem s1) (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hW J.kern.ksbFit J.kern.ksbAl fun b hb => by
      obtain ⟨-, h1, h2⟩ := hb; omega
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
    refine (P1.blk_of_untracked J.blk hW fun b hb => ⟨⟨hb.1, fun t ht => ?_, fun c hc => ?_⟩,
      fun e he => ?_, fun hf => ?_⟩).1
    · obtain ⟨hb8, h1, h2⟩ := hb
      have hb8' : b.val % 8 = 0 := hb8
      rcases hAp t .tcb ht (fun _ e => by cases e) with e | e <;>
        (try simp only [P1.HKind.bits, Nat.reducePow] at e ⊢) <;> omega
    · obtain ⟨-, h1, h2⟩ := hb
      have := hnd c hc
      omega
    · obtain ⟨hb8, h1, h2⟩ := hb
      have hb8' : b.val % 8 = 0 := hb8
      rcases he with he | he
      · rcases hAp e _ he (fun _ e => by cases e) with e | e <;>
          (try simp only [P1.HKind.bits, Nat.reducePow] at e) <;> omega
      · rcases hAp e _ he (fun _ e => by cases e) with e | e <;>
          (try simp only [P1.HKind.bits, Nat.reducePow] at e) <;> omega
    · obtain ⟨-, h1, h2⟩ := hb
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
    have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
    refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_,
      U.sb4, U.nostr, U.nsFree,
      fun h0 => U.ns (by rw [F.cdt] at h0; exact h0),
      ?_, fun g => by rw [hna]; exact U.dwReg (B g),
      fun g => by rw [F.gpml4]; exact U.gReg (B g)⟩
    · intro g w' hal' h1 h2
      show L.mem (L.zr s q n) w' = _
      rw [L.mem_zr _ _ _ _ hal hn8 hfit hal']
      split_ifs
      · rfl
      · exact U.zero (B g) w' hal' h1 h2
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
    obtain ⟨-, h1, h2⟩ := hb
    refine J.notDbg' (fun p hp => ?_) (fun c hc => ?_)
    · rcases hAp p .tcb hp (fun z h => by cases h) with e | e <;> simp only [P1.HKind.bits] at e ⊢ <;> omega
    · rcases hnd c hc with e | e <;> omega
  exact J.cs_frameK hkb hX1 F.kback F.ipcFr (JCs.same J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (J.vkeep_of hW fun b hb u hu' e => by
    obtain ⟨-, h1, h2⟩ := hb
    have hv := Sched.tVcpuA_val J.ip.e.tcb hu'
    have := hAp u .tcb (J.zH.1 u hu') (fun z h => by cases h)
    rw [e] at h1 h2
    simp only [P1.HKind.bits] at this
    omega)
    hSS hKd F.idle

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The caller's restart keeps `resumeCurThread`** (handoff utj.md Round 9):
at an entry state the current thread, set to `Restart`, stays schedulable
(its SC is the current SC, `CurInv`; not the idle SC, else `Inv.back` makes
it the idle thread; active by `CurInv.active`; off the release queue), so
`set_thread_state_act` asks no reschedule. -/
theorem JAtZ.restart_keeps_resume (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    {ct : U64} {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hc : σ.curThread = ct.bv) :
    (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv).schedulerAction =
      .resumeCurThread := by
  have hC : CurInv σ := J.cur.resolve_left fun h => by rw [hni.2] at h; cases h
  obtain ⟨xc, hkc, hcs, -⟩ := hC.tcb
  rw [hc, hk] at hkc; cases hkc
  have hne : σ.curSc ≠ σ.idleSc := by
    intro hci
    obtain ⟨xi, hki, hxi, -, -⟩ := J.act.2
    have hkc' : σ.kheap σ.curThread = some (.tcb x) := by rw [hc]; exact hk
    obtain ⟨y1, n1, hk1, hy1⟩ := J.inv.back _ _ _ hkc' hcs
    obtain ⟨y2, n2, hk2, hy2⟩ := J.inv.back _ _ _ hki hxi
    rw [hci, hk2] at hk1; cases hk1
    rw [hy1] at hy2
    exact hni.1 (Option.some.inj hy2)
  obtain ⟨y, n, hky⟩ := hC.sc
  have ha := hC.active hne y n hky
  have hscne : σ.curSc ≠ ct.bv := fun e => by rw [e, hk] at hky; cases hky
  have hs : Fl4Spec.schedulable ct.bv (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) = true :=
    schedulable_of (x := { x with tcbState := .restart }) (by simp [Notif.updK]) hcs rfl (by rw [Notif.updK_kheap, Function.update_of_ne hscne]; exact hky) ha
      (by show ct.bv ∉ σ.releaseQueue; rw [← hc]; exact hC.notRel)
  unfold Notif.stsAct
  rw [if_neg fun h => h.2.2 hs]
  exact hni.2

/-- **The preempted outcome of a preemption point at `JAtZ`** is `JAtPre`
(XTopJointCnDel; `PPR0` gives the base its no-switch and non-idle facts). -/
theorem JAtZ.jAtPre_pp (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (hpp : sched.preemption_point st arI s a = ok (.Err .Preempted, s', a'))
    (hsp : (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) (hR0 : PPR0 σ) :
    JAtPre (L := L) arI AR s' a' σ' :=
  ⟨s, a, σ, ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hR0.1.2.1, hR0⟩, hpp, hsp⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **A range cleared at `J` that no ghost reads** (`JAtZ.zeroJ` with its
word facts from the ghosts): `[q, q+n)` meets no object of `H` (hence, by
`zH`/`JPlaced`, no TCB, endpoint, reply, notification, SC or CNode of the
sets and the typed heap), no VSpace table of the sets, no IPC-buffer word,
neither the kernel-state block, nor any core's node, nor the ASID-table area;
one core (`Z.c = 0`). After the drop step (`JAtZ.drop`) this holds of every
part of the dropped region. -/
theorem JAtZ.zeroJR (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {q n : U64} (hal : P1.Aligned q)
    (hn8 : n.val % 8 = 0) (hfit : q.val + n.val ≤ 2 ^ 64) (hc0 : Z.c = 0#u64)
    (hH : ∀ r k, H r = some k → q.val + n.val ≤ r.val ∨ r.val + 2 ^ k.bits ≤ q.val)
    (hV : ∀ x : U64, (x ∈ Z.P ∨ x ∈ Z.L4 ∨ x ∈ Z.L3 ∨ x ∈ Z.L2 ∨ x ∈ Z.L1) →
      q.val + n.val ≤ x.val ∨ x.val + 4096 ≤ q.val)
    (hnB : ∀ wp ∈ Z.B, wp.1.val + 8 ≤ q.val ∨ q.val + n.val ≤ wp.1.val)
    (hks : q.val + n.val ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ q.val)
    (hnd : ∀ c ∈ Cs, q.val + n.val ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ q.val)
    (hasid : q.val + n.val ≤ (L.ksb s).val + 288000 ∨ (L.ksb s).val + 288000 + 16384 ≤ q.val) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.zr s q n) a σ := by
  have hq8 : q.val % 8 = 0 := hal
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hn0 : L.nodeBase s 0#u64 = (L.ksb s).val + 13568 := by
    show (L.ksb s).val + 13568 + (0#u64 : U64).val * 4288 = _; simp
  have hnd0 := hnd 0#u64 J.kern.cs0
  refine J.zeroJ hal hn8 hfit (fun b hb h1 h2 => ?_) (fun wp hwp h => ?_) (fun r k hr _ => hH r k hr) hks hnd
  · have hb8 : b.val % 8 = 0 := hb
    have hb' : b.val + 8 ≤ q.val + n.val := by omega
    refine ⟨hb, ⟨?_, fun t ht => ?_, fun sc hsc x m hkx => ?_⟩, ?_, fun e he => ?_, fun r hr => ?_, fun m hm => ?_⟩
    · show b.val + 8 ≤ (L.ksb s).val ∨ L.nodeBase s Z.c + 4288 ≤ b.val
      rw [hc0, hn0]; rw [hn0] at hnd0; omega
    · have e := hH t _ (J.zH.1 t ht)
      simp only [P1.HKind.bits, Nat.reducePow] at e; omega
    · have e := hH sc _ (hJ.sc sc x m (J.c0 sc hsc) hkx).2
      simp only [P1.HKind.bits] at e; omega
    · rintro (⟨x, r, hx, g1, g2⟩ | ⟨t, ht, g1, g2⟩ | ⟨x, hx, g1, g2⟩ | ⟨g1, g2⟩)
      · have e := hH x _ (hJ.cnode x r hx)
        have h32 : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
        simp only [P1.HKind.bits, h32] at e; omega
      · have e := hH t _ ((hJ.tcb t).1 ht)
        simp only [P1.HKind.bits, Nat.reducePow] at e; omega
      · have := hV x hx; omega
      · omega
    · have e := hH e _ (J.zH.2.1 e he)
      simp only [P1.HKind.bits, Nat.reducePow] at e; omega
    · have e := hH r _ (J.zH.2.2.1 r hr)
      simp only [P1.HKind.bits, Nat.reducePow] at e; omega
    · have e := hH m _ (J.zH.2.2.2 m hm)
      simp only [P1.HKind.bits, Nat.reducePow] at e; omega
  · have := hnB wp hwp; omega

end

end

end Fl4Proofs.P3
