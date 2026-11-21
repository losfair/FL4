/-
P3 (DESIGN.md §9), VT-x: **`JAtZ` across a step writing only VT-x words**
(toward the VT-x side of a cap's finalisation: `revoke_ports`, `ept::unmap`;
as XTopJointFinVs for the native VSpace finalisation).

The spec does not model the VT-x objects' contents (VCPU state, IO bitmaps,
EPT tables: DESIGN §5); their finalisation work leaves the spec state as it
is. FL4's writes then land in words no relation of `JAtZ` reads:

* `VtOut Z H Cs s σ b`: an aligned word outside the other subsystems'
  objects (`OObj`: the core's node, the low kernel-state block, the TCB
  fields, endpoints, replies, notifications, SCs, IPC-buffer words), the
  VSpace code's objects (`VObj`: CNodes, TCB cap slots, tables, pools, the
  ASID table), every object of P1's heap `H` but the `other` ones, every
  core's node and the free part of every untyped cap.
* `XTopAt.vtStep`: `XTopAt` across writes outside `OObj` and `VObj`, the
  spec state kept, the arch relation at the new arch state (`TopSR.step`
  with the region `Rw` the written words).
* `JAtZ.vtJ`: `JAtZ` across writes of `VtOut` words, the spec state kept and
  the arch relation at the new arch state; the slots and the kernel-state
  base kept (finVsJb's frame argument, at `ArFr σ σ`).
* `JAtZ.vheadJ`: `JAtZ` across a write of the VCPU list's head word
  (`VCPU_HEAD`, a `KsW` word of the low kernel-state block read by no
  relation; as XTopJointPP's `workUnitsJ`, `jowes_ks`).
* `JAtZ.vtHJ`: `JAtZ` across writes of `VtOut` words and the head word
  (`vtJ` then `vheadJ`, the head word split off by writing back its old
  value): `vcpu::finalise`'s footprint.
-/
import Fl4Proofs.P3.XTopJointFinVs
import Fl4Proofs.P1.QueueFinIo
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **A VT-x word** at a `JAtZ` state (module docstring): a word no
relation of `JAtZ` reads. -/
structure VtOut (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (σ : Fl4Spec.State Unit) (b : U64) : Prop where
  al : P1.Aligned b
  oobj : ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b
  vobj : ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b
  obj : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → b.val < p.val ∨ p.val + 2 ^ k.bits ≤ b.val
  node : ∀ c ∈ Cs, b.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ b.val
  ut : ∀ x ∈ Z.G.chains.flatten, ∀ p sb fi d, capV (L.mem s) x = .Untyped p sb fi d →
    b.val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ b.val

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 8000000 in
/-- **`XTopAt` across writes outside `OObj` and `VObj`** (module docstring),
the spec state kept. -/
theorem XTopAt.vtStep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hWO : ∀ b, W b → ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b)
    (hWV : ∀ b, W b → ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b)
    (hAR : AR a' σ.archState.x64CurrentCr3) :
    XTopAt (L := L) AR Z s' a' σ ∧ SlotsSame Z.th (L.mem s) (L.mem s') := by
  obtain ⟨⟨hS, hR, hPt, hPI, hCO⟩, ⟨hPl, hCR, hFI, hD, hMO, hIA, hSA⟩, -, hE⟩ := hX
  have hP := hS.2
  have hk : L.ksb s' = L.ksb s := hw.1
  have hvobj : ∀ b, VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b → ¬ W b := fun b hv hb => hWV b hb hv
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    slotsSame_of_vobj hPl fun b hb hv => hw.mem_eq hb (hvobj b hv)
  have hS' : TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR s' a' σ :=
    TopSR.step (Rw := W) hS hw.1 hw.2.1 (fun b hb _ hr => hw.2.2 b hb hr) hWO (OStep.refl' σ)
      (fun _ h => h.elim) (fun _ _ => rfl) (fun _ => hAR)
  have hvw : ∀ b, VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hw.mem_eq (VsWrite.aligned hP.vs hb) (hvobj b (vsWrite_vobj hP.vs hb))
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hD' : DomRel (L.mem s') (L.ksb s) σ := by
    refine DomRel.frame hD (fun o ho => ?_) rfl rfl
    have hlt := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    exact hw.mem_eq (ksW_al hkf hka hlt.1 hlt.2) fun hb =>
      hWO _ hb (Or.inr (Or.inl ⟨by rw [hv]; omega, by rw [hv]; omega⟩))
  have hSz : Sched.SzKeep σ σ := Sched.SzKeep.of_kheap rfl
  refine ⟨⟨⟨hS', by rw [hk]; exact hR.frame hvw rfl (fun _ _ => rfl), ?_, fun q hq lo hl => ?_,
    hCO.of_same hSS rfl⟩,
    ⟨hPl, crel_same hCR hSS rfl rfl rfl, hFI.of_same hCR.2.2.1 hSS (KSub.of_kheap rfl),
      by rw [hk]; exact hD', by rw [hk]; exact MdbOKV.of_same hCR.2.2.1 hSS hMO, by rw [hk]; exact hIA,
      hSA.mono hSz⟩, IpcRel.of hS'.1.2.2.1 hS'.1.2.1 (sched_sc hS'.1.1), hE.mono hk hSz⟩, hSS⟩
  · refine hPt.frame (fun b ⟨q, hq, i, hi, e⟩ => ?_) fun q hq => rfl
    subst e
    have hv := table_vobj (th := Z.th) (P := Z.P) hP.pt hq hi (L.ksb s)
    exact hw.mem_eq (hP.po _ ⟨q, hq, i, hi, rfl⟩).1 (hvobj _ hv)
  · have hwv : VsWrite Z.P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hwv]; exact hPI q hq lo hl

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The untyped caps' facts across `VtOut` writes** (as `JAtZ.vs_utc`). -/
theorem JAtZ.vt_utc {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hw : P1.WritesIn st s s' (VtOut (L := L) Z H Cs s σ))
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdv
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns h0, ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases hb.ut _ hxm p sb fi dev hcv with e | e <;> omega
  · intro g h0 hf0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨r1, by rw [hna, hDbg]; exact r3⟩

set_option maxHeartbeats 16000000 in
/-- **`JAtZ` across `VtOut` writes** (module docstring): the spec state
kept, the arch relation at the new arch state; at the same sets, the dead
set and P1's sets kept. -/
theorem JAtZ.vtJ {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s1 : S} {a1 : A} (hW : P1.WritesIn st s s1 (VtOut (L := L) Z H Cs s σ))
    (hAR : AR a1 σ.archState.x64CurrentCr3) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 σ ∧ SlotsSame Z.th (L.mem s) (L.mem s1) ∧ L.ksb s1 = L.ksb s := by
  have F : ArFr σ σ := ArFr.of_eq rfl
  have hkb : L.ksb s1 = L.ksb s := hW.1
  have hcpu : L.cpu s1 = L.cpu s := hW.2.1
  obtain ⟨hX1, hSS⟩ := J.xtop.vtStep hW (fun b hb => hb.oobj) (fun b hb => hb.vobj) hAR
  -- the frame words
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHk := J.kern.heap
  have objK : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → ∀ w : U64, P1.Aligned w → p.val ≤ w.val →
      w.val < p.val + 2 ^ k.bits → L.mem s1 w = L.mem s w := fun p k hp hk w hal g1 g2 =>
    hW.mem_eq hal fun hb => by rcases hb.obj p k hp hk with e | e <;> omega
  have tcbK : ∀ t ∈ Z.T, ∀ w : U64, P1.Aligned w → t.val ≤ w.val → w.val < t.val + 4096 →
      L.mem s1 w = L.mem s w := fun t ht w hal g1 g2 =>
    objK t .tcb (J.zH.1 t ht) (fun _ e => by cases e) w hal g1 (by simpa [P1.HKind.bits] using g2)
  have k1 : ∀ t ∈ Z.T, L.mem s1 (mcpA t) = L.mem s (mcpA t) := fun t ht =>
    tcbK t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega)
  have k2 : ∀ t ∈ Z.T, L.mem s1 (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    tcbK t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega)
  have kb : ∀ t ∈ Z.T, L.mem s1 (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    tcbK t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega)
  have scw : ∀ q z, H q = some (.sc z) → ∀ w : U64, P1.Aligned w → q.val ≤ w.val → w.val < q.val + 2 ^ z →
      L.mem s1 w = L.mem s w := fun q z hq w hal g1 g2 =>
    objK q _ hq (fun _ e => by cases e) w hal g1 (by simpa only [P1.HKind.bits] using g2)
  have k3 : ∀ q ∈ Z.C, L.mem s1 (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun q hq => by
    obtain ⟨xq, nq, hkq, hin⟩ := screply_obj J.xtop.fin.1.1.1 hq
    have hHq := (hJ.sc q xq nq (J.c0 q hq) hkq).2
    exact scw q _ hHq _ (sc_reply_word J.xtop.fin.1.1.1 hq).1 hin.1 hin.2
  have k4 : ∀ r ∈ Z.R, L.mem s1 (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧
      L.mem s1 (P1.rNextA r) = L.mem s (P1.rNextA r) := by
    intro r hr
    have hal := J.rp.align r hr
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s1 a' = L.mem s a' := fun a' ha =>
      objK r _ hHr (fun _ e => by cases e) a' (J.rp.aligned hr ha) (by omega)
        (by simp only [P1.HKind.bits]; omega)
    exact ⟨k _ (Or.inl (rPrevA_val hal)), k _ (Or.inr (rNextA_val hal))⟩
  have hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s1 (scW q K) = L.mem s (scW q K) := by
    intro q z hq K hK8 hK
    have hal := hHk.align q _ hq
    have hfit := hHk.fits q _ hq
    have hz := hHk.scmin q z hq
    simp only [P1.HKind.bits] at hal hfit
    have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have hq8 : q.val % 8 = 0 := by
      have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
      rw [← Nat.mod_mod_of_dvd q.val hd, hal]
    have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
    exact scw q z hq _ (by show (scW q K).val % 8 = 0; rw [hv]; omega) (by omega) (by omega)
  -- the debug word and the IRQ node
  have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
  have hDbg : L.mem s1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hdv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have hdo : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
    exact hW.mem_eq J.kern.dwAl fun hb => by rcases hb.node _ J.kern.cs0 with e | e <;> omega
  have hirq : ∀ i : U64, i.val < 128 → capV (L.mem s1) (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hW J.kern.ksbFit J.kern.ksbAl fun b hb => by
      by_contra hn
      by_cases hI : (L.ksb s).val + 1248 ≤ b.val ∧ b.val < (L.ksb s).val + 5344
      · obtain ⟨i, -, hn', g1, g2⟩ := J.intL.in_node hI.1 hI.2
        exact hb.vobj (Or.inl ⟨_, 0, hn', g1, by simpa using g2⟩)
      · exact hb.oobj (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
  -- the dead stay dead
  have hAI : ActIdle σ := J.act
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
    refine (P1.blk_of_untracked J.blk hW fun b hb => ⟨⟨hb.al, fun t ht => ?_, fun c hc => ?_⟩,
      fun e he => ?_, fun hf => ?_⟩).1
    · rcases hb.obj t .tcb ht (fun _ e => by cases e) with e | e
      · left; omega
      · right; simpa [P1.HKind.bits] using e
    · rcases hb.node c hc with e | e <;> omega
    · have hb8 : b.val % 8 = 0 := hb.al
      rcases he with he | he
      · have ha := hHk.align e _ he
        simp only [P1.HKind.bits] at ha
        rcases hb.obj _ _ he (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
      · have ha := hHk.align e _ he
        simp only [P1.HKind.bits] at ha
        rcases hb.obj _ _ he (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
    · obtain ⟨-, p, k, hp, hk, hin⟩ := hf
      have hko : ∀ z, k ≠ .other z := by
        rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z e <;> cases e
      obtain ⟨g1, g2⟩ := hin
      rcases hb.obj p k hp hko with e | e <;> omega
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
      J.vt_utc hW hSS hDbg, J.nsc, J.inv, J.cur, J.own, J.off, hAI, J.bsa, J.isorted, J.curRun, hblk⟩
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1 := dbgKeep_of_writes J.blk hW fun b hb =>
    J.notDbg (fun p hp => hb.obj p .tcb hp (fun z h => by cases h)) hb.node
  exact ⟨J.cs_frameK hkb hX1 F.kback F.ipcFr (JCs.same J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (fun t ht => tcbK t (J.thT t ht) _ (Sched.tVcpuA_aligned J.ip.e.tcb (J.thT t ht)) (by rw [Sched.tVcpuA_val J.ip.e.tcb (J.thT t ht)]; omega) (by rw [Sched.tVcpuA_val J.ip.e.tcb (J.thT t ht)]; omega))
    hSS hKd F.idle, hSS, hkb⟩


/-- The value of the VCPU list's head word (`VCPU_HEAD`, offset 80 of the
kernel-state block). -/
theorem vHead_val {kb : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) :
    (core.num.U64.wrapping_add kb layout.ks.VCPU_HEAD).val = kb.val + 80 := by
  simp [core.num.U64.wrapping_add_val_eq, layout.ks.VCPU_HEAD, U64.size_def, U64.numBits]; omega

set_option maxHeartbeats 4000000 in
/-- **A write of the VCPU list's head word keeps `JAtZ`** (as XTopJointPP's
`workUnitsJ`: a `KsW` word, read by no relation; `jowes_ks`), the spec
state, the sets and the arch state kept. -/
theorem JAtZ.vheadJD {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw0 : P1.WritesIn st s s' (· = P1.vHeadA st s)) :
    (∃ (Ac' : Set U64) (Lst' : U64 → List U64),
      JAtZ (L := L) arI AR Z H Cs Ac' Lst' D s' a σ) ∧
      SlotsSame Z.th (L.mem s) (L.mem s') ∧ L.ksb s' = L.ksb s := by
  have hX := J.xtop
  have hf := J.kern.ksbFit
  have hal := J.kern.ksbAl
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val hf
  have hw : P1.WritesIn st s s' (KsW (L.ksb s)) :=
    hw0.mono fun b hb => ⟨80#u64, by decide, by decide, by decide, by rw [hb, hv]; rfl, Or.inl (by decide)⟩
  have hne : ∀ b : U64, P1.Aligned b → b.val ≠ (L.ksb s).val + 80 → L.mem s' b = L.mem s b := fun b hb hb' =>
    hw0.mem_eq hb fun e => hb' (by rw [e, hv])
  have hirq : IrqRel (L.mem s') (L.ksb s) σ := by
    have hR := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, hR.node⟩
    have e := irqStA_val hf hi
    rw [hne _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega)]
    exact hR.st i hi
  have hio : IoRel (L.mem s') (L.ksb s) σ := by
    have hR := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hw' : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have e := ioA_val hf hw'
    unfold bitOf
    rw [hne _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega)]
    exact hR p hp
  have hD' : DomRel (L.mem s') (L.ksb s) σ := by
    refine hX.rel.2.2.2.1.frame (fun o ho => ?_) rfl rfl
    have hlt := domOffs_lt' ho
    have h80 : o.val ≠ 80 := by
      simp only [domOffs, List.mem_cons, List.mem_nil_iff, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
    have e := ksW_val (kb := L.ksb s) (o := o) (by omega)
    exact hne _ (ksW_al hf hal hlt.1 hlt.2) (by rw [e]; omega)
  have hAR := hX.fin.1.1.2.2.2.2.2.2
  have hX1 : XTopAt (L := L) AR Z s' a σ := XTopAt.ksStep hX J.ks hw (KsStep.refl σ) hirq hio hD' hAR
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    hX.slotsSame_of hw fun b hb => by obtain ⟨K, h1, h2, -, e⟩ := hb; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨Ac', Lst', R⟩ := jowes_ksD arI s s' a a σ σ hw (KsStep.refl σ) Z H Cs Ac Lst D rfl J hX1
  exact ⟨⟨Ac', Lst', J.cs_frameK hw.1 hX1 (KBack.of_kheap rfl) (IpcFrKeep.of_kheap rfl) (JCs.same J hSS (KSz.of_kheap rfl)) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (J.vkeep_of hw fun _ hb => J.ksW_nv hb)
    hSS (dbgKeep_of_writes J.blk hw fun _ hb => J.ksW_notDbg hb) rfl⟩, hSS, hw.1⟩

/-- **`JAtZ` across writes of `VtOut` words and the VCPU list's head word**
(`vtJ`, then `vheadJ` for the head word, split off by a write back of its old
value), the spec state kept, the arch relation at the new arch state. -/
theorem JAtZ.vtHJD {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s1 : S} {a1 : A} (hW : P1.WritesIn st s s1 (fun b => VtOut (L := L) Z H Cs s σ b ∨ b = P1.vHeadA st s))
    (hAR : AR a1 σ.archState.x64CurrentCr3) :
    (∃ (Ac' : Set U64) (Lst' : U64 → List U64),
      JAtZ (L := L) arI AR Z H Cs Ac' Lst' D s1 a1 σ) ∧
      SlotsSame Z.th (L.mem s) (L.mem s1) ∧ L.ksb s1 = L.ksb s := by
  have hf := J.kern.ksbFit
  have hal := J.kern.ksbAl
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val hf
  have ha : P1.Aligned (P1.vHeadA st s) := by unfold P1.Aligned; rw [hv]; omega
  have hA : P1.WritesIn st s (L.wr s1 (P1.vHeadA st s) (L.mem s (P1.vHeadA st s))) (VtOut (L := L) Z H Cs s σ) := by
    refine ⟨by rw [P1.LawfulStore.ksb_wr]; exact hW.1, by rw [P1.LawfulStore.cpu_wr]; exact hW.2.1,
      fun b hb hn => ?_⟩
    rw [L.mem_wr _ _ _ _ ha hb]
    by_cases e : P1.vHeadA st s = b
    · rw [if_pos e, e]
    · rw [if_neg e]
      exact hW.mem_eq hb fun h' => Or.elim h' hn fun e' => e e'.symm
  obtain ⟨JA, hSA, hkA⟩ := J.vtJ hA hAR
  have hhd : P1.vHeadA st (L.wr s1 (P1.vHeadA st s) (L.mem s (P1.vHeadA st s))) = P1.vHeadA st s := by
    unfold P1.vHeadA; rw [P1.LawfulStore.ksb_wr, hW.1]
  have hB : P1.WritesIn st (L.wr s1 (P1.vHeadA st s) (L.mem s (P1.vHeadA st s))) s1
      (· = P1.vHeadA st (L.wr s1 (P1.vHeadA st s) (L.mem s (P1.vHeadA st s)))) := by
    refine ⟨by rw [P1.LawfulStore.ksb_wr], by rw [P1.LawfulStore.cpu_wr], fun b hb hn => ?_⟩
    rw [L.mem_wr _ _ _ _ ha hb, if_neg fun e => hn (by rw [hhd]; exact e.symm)]
  obtain ⟨J1, hS1, hk1⟩ := JA.vheadJD hB
  exact ⟨J1, hSA.trans hS1, hk1.trans hkA⟩

/-- `vheadJD` with the dead set existential. -/
theorem JAtZ.vheadJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw0 : P1.WritesIn st s s' (· = P1.vHeadA st s)) :
    (∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' a σ) ∧
      SlotsSame Z.th (L.mem s) (L.mem s') ∧ L.ksb s' = L.ksb s :=
  let ⟨⟨Ac', Lst', J'⟩, h1, h2⟩ := J.vheadJD hw0
  ⟨⟨Ac', Lst', D, J'⟩, h1, h2⟩

/-- `vtHJD` with the dead set existential. -/
theorem JAtZ.vtHJ {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s1 : S} {a1 : A} (hW : P1.WritesIn st s s1 (fun b => VtOut (L := L) Z H Cs s σ b ∨ b = P1.vHeadA st s))
    (hAR : AR a1 σ.archState.x64CurrentCr3) :
    (∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 a1 σ) ∧
      SlotsSame Z.th (L.mem s) (L.mem s1) ∧ L.ksb s1 = L.ksb s :=
  let ⟨⟨Ac', Lst', J'⟩, h1, h2⟩ := J.vtHJD hW hAR
  ⟨⟨Ac', Lst', D, J'⟩, h1, h2⟩

end

end

end Fl4Proofs.P3
