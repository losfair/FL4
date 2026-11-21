/-
P3 (DESIGN.md §9), VSpace: **the frame's `DeriveSubframe` at `J`**
(XTopJointVsCap's `JFramePath.post`, the last frame label with `JPostHyp`).

* `TypedKeptH`: XTopJointRest's `TypedKept` with a third case, a cap whose
  `CapTyped` and `CapObjH` facts hold outright (a fresh 4 KiB alias names no
  object of its own: its range lies inside the large frame's, which misses
  every object of `H` but the `other` ones, `CapObjH`).
* `JPlaced.slotTFH`, `jowes_slotDFH`: `JPlaced.slotTF` and XTopJointDel's
  `jowes_slotDF` with `TypedKeptH` for `TypedKept`.
* `JAtZ.subInsJ`: one alias insert (VsSubRel's `sub_step`, at `SR := TopSR`)
  at `J`: the trace (`insert_trace`), `DelInv` (`insert_delinv_imp`),
  `XTopAt.slotStep`, the cover and untyped regions kept (only the empty
  destination changes, to a frame cap), the untyped caps' facts by
  `JAtZ.ins_utc` (the destination's CNode live, `DestLive`), then
  `jowes_slotDFH` and `JAtZ.cs_frameV`.
-/
import Fl4Proofs.P3.XTopJointVsReply
import Fl4Proofs.P3.VsSubTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- A TCB's slot is no CNode slot. -/
theorem slotOf_ne_cnV {th : TypedHeap} (hP : Placed th) {t : U64} {n : Nat} (hn : IsSlotAt th t n)
    (ht : th t = some .tcb) {q : U64} {r : Nat} {idx : List Bool} (hq : th q = some (.cnode r))
    (hl : idx.length = r) : slotOf t n ≠ cslotAddr (q.bv, idx) := by
  intro e
  obtain ⟨p, i, hi, hp1, hp2⟩ := AbsSlot.at (th := th) (sl := (q.bv, idx)) ⟨q, rfl, Or.inl (by rw [hl]; exact hq)⟩
  have hpp : p = q := P1.eq_of_bv hp1.symm
  subst hpp
  have := IsSlotAt.apart hP hn hi (fun hh => by obtain ⟨h, -⟩ := hh; subst h; rw [hq] at ht; cases ht)
  rw [e, hp2] at this; omega

/-- **The slots' caps keep their objects, or have their objects' facts**
(module docstring). -/
def TypedKeptH (th : TypedHeap) (H : P1.Heap) (isc : U64) (m m' : U64 → U64) : Prop :=
  ∀ a, IsSlot th a → tyObj (capV m' a) = false ∨ (∃ b, IsSlot th b ∧ shape (capV m' a) = shape (capV m b)) ∨
    (CapTyped H (P1.Heap.replies H) (P1.Heap.ntfns H) (capV m' a) ∧ CapObjH H isc (capV m' a))

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`JPlaced` after a slot step** with `TypedKeptH` (`JPlaced.slotTF`). -/
theorem Sched.JPlaced.slotTFH {th : TypedHeap} {H : P1.Heap} {Tr C : Set U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : JPlaced (L := L) th H Tr C s σ) (hkc : KeepCT σ σ') (hk : L.ksb s' = L.ksb s) (hL : IntLayout th (L.ksb s))
    (hT : TypedKeptH th H (Sched.idleScW (L := L) s) (L.mem s) (L.mem s'))
    (hfh : ∀ t, th t = some .tcb → capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Endpoint ep b0 b1 b2 b3 b4)
    (hbf : ∀ t, th t = some .tcb → Sched.BufSlotOK (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2))))
    (hiw : Sched.idleScW (L := L) s' = Sched.idleScW (L := L) s) :
    JPlaced (L := L) th H Tr C s' σ' := by
  have hirqS : ∀ i : U64, i.val < 128 → IsSlot th (nodeA (L.ksb s) i) := fun i hi => by
    have hA : AbsSlot th ((nodeA (L.ksb s) i).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node i hi)⟩
    have := hA.isSlot; rwa [cslotAddr_nil] at this
  have hty' : ∀ a, IsSlot th a → CapTyped H (P1.Heap.replies H) (P1.Heap.ntfns H) (capV (L.mem s') a) := by
    intro a ha
    rcases hT a ha with hn | ⟨b, hb, hs⟩ | ⟨h1, -⟩
    · exact capTyped_of_tyObj hn
    · exact capTyped_of_shape hs (h.typed b hb)
    · exact h1
  refine ⟨h.heap, h.pl, h.tcb, h.cnode, h.tr, fun c y n hc hk' => ?_, by rw [hk]; exact h.ks, by rw [hk]; exact h.ksIn,
    fun a ha => hty' a ha, fun i hi => by rw [hk]; exact hty' _ (hirqS i hi), hfh, hbf, fun a ha => ?_⟩
  · rcases hkc c.bv with e | ⟨r, cs, cs', -, h2⟩ | ⟨x, y', -, h2, -⟩
    · rw [e] at hk'; exact h.sc c y n hc hk'
    · rw [h2] at hk'; cases hk'
    · rw [h2] at hk'; cases hk'
  · rcases hT a ha with hn | ⟨b, hb, hs⟩ | ⟨-, h2⟩
    · exact capObjH_of_tyObj hn
    · rw [hiw]; exact capObjH_of_shape hs (h.cobj b hb)
    · rw [hiw]; exact h2

set_option maxHeartbeats 4000000 in
/-- **XTopJointDel's `jowes_slotDF` with `TypedKeptH`.** -/
theorem jowes_slotDFH {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {G' : MdbGhost} {V' : XVs} (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a' σ')
    (hcn : Ipc.CnK σ σ') (hkc : KeepCT σ σ') (hw : P1.WritesIn st s s' (InSlot Z.th))
    {kb : U64} (hFI : FinInv Z.th (L.mem s') σ' G') (hMO : MdbOKV kb (L.mem s') G') (hkz : KSz σ σ')
    (hTK : TypedKeptH Z.th H (Sched.idleScW (L := L) s) (L.mem s) (L.mem s'))
    (hfh : ∀ t, Z.th t = some .tcb → capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Endpoint ep b0 b1 b2 b3 b4)
    (hbf : ∀ t, Z.th t = some .tcb → Sched.BufSlotOK (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2))))
    (hDl : DelInv Z.th (L.mem s')) (hUK : UtKept Z.th (L.mem s) (L.mem s'))
    {D' : Set U64} (hjc : JCovD (L := L) Z.th H G' D' Cs s')
    (horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl)
    (hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' G' sl p sb fi) :
    JCs (L := L) (Z.mv G' V') s' σ' ∧ JRest (L := L) arI (Z.mv G' V') H Cs Ac Lst D' s' σ' := by
  have hC := CnStep.of_cnK hcn
  obtain ⟨k1, k2, kb', k3, k4⟩ := inSlot_keeps arI J hw
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, hC.sc.2 hq, rfl⟩, fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hq,
    rfl, rfl⟩, fun p x n hp => ⟨x, hC.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.yld⟩, fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩,
    fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩
  have mk : McpKeep σ σ' := fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.mcp⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hC.toHStep.khrb
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := by
    have hPl := J.xtop.rel.1
    have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
      ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hPl hb h)⟩
    exact (P1.blk_of_capw J.blk hw' (J.slotCapW P1.tlow_slots)).1
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' :=
    let ⟨Tr, Cq, hJ⟩ := J.jpl
    ⟨Tr, Cq, hJ.slotTFH hkc hw.1 J.intL hTK hfh hbf (J.idleW_keep hX'.fin.1.1.1 hC.idle hC.isc).2⟩
  obtain ⟨-, ⟨-, -, hM', -, -⟩, -⟩ := hX'.rel
  have hJC0 := J.jcs_slot hM' hMO hFI hUK hkz hDl
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn.1; exact e
  have hkern := J.kern_keep hw.1 hw.2.1 hX'.fin.1.1.1 hC.ct hC.csc horig hgp
    (fun p ao h => (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 h) hDbg (D' := D')
  exact ⟨⟨hJC0.del, hJC0.ut, hJC0.finM, hJC0.sfree⟩, ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 mk,
    J.buf.frame kb' (fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.buf⟩), hRP', J.apart.sc_frame hw.1 (SzKeep.of_keepCT hkc), hjpl,
    hjc, hkern, hutc, J.nsc.cn hC.toHStep, J.inv.cn hC, CurInvW.cn J.cur hC, J.own.cn hC.toHStep, J.off.cn hC.toHStep,
    J.act.cn hC,
    J.bsa.cn hC.toHStep, J.isorted.cn hC.toHStep, J.curRun.cn hC.toHStep (Or.inr hC.act), hblk⟩⟩

end

/-! ## One alias insert at `J` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- `TopSR` at `Z`'s sets (the `SR` of the alias loop at `J`). -/
abbrev subSRJ (st : machine.Store S) [L : P1.LawfulStore st] (Z : XSets) (AR : A → Fl4Spec.Cr3 → Prop) :
    S → A → Fl4Spec.State Unit → Prop :=
  TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR

set_option maxHeartbeats 16000000 in
/-- **One alias insert at `J`** (module docstring). -/
theorem JAtZ.subInsJ {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pp : U64} {rs : Nat} (hpp : Z.th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {ptr rt fa fv : U64} {mm rv : Bool}
    (hS : SubRel st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (subSRJ st Z AR) (cslotAddr (pp.bv, idx))
      (.Frame ptr .Large rt false mm false fa fv) rv s a σ Z.G)
    (hal : ptr.val % 2 ^ 21 = 0)
    {dp : U64} {r : Nat} (hdp : Z.th dp = some (.cnode r)) (hr : r < 64) {k : Nat} (hk : k < 2 ^ r)
    (hdst : capAt (L.mem s) (slotAddr dp.bv (BitVec.ofNat 64 k)) = ok .Null)
    {q vm : U64} (hq1 : ptr.val ≤ q.val) (hq2 : q.val + 4096 ≤ ptr.val + 2 ^ 21) (hvm : 1 ≤ vm.val ∧ vm.val ≤ 3)
    (hqal : q.val % 4096 = 0) (hDLc : DestCap Z.th (L.mem s) dp) :
    cdt.insert st s (.Frame q .Small vm false false false 0#u64 0#u64) (cslotAddr (pp.bv, idx))
      (slotAddr dp.bv (BitVec.ofNat 64 k)) ⦃ s' => ∃ σ',
        Fl4Spec.capInsert (Z := Unit) (absCap (.Frame q .Small vm false false false 0#u64 0#u64)) (pp.bv, idx)
          (dp.bv, Fl4Spec.natToCref r k) σ = ({((), σ')}, False) ∧
        SubRel st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (subSRJ st Z AR) (cslotAddr (pp.bv, idx))
          (.Frame ptr .Large rt false mm false fa fv) rv s' a σ'
          (insG Z.G (cslotAddr (pp.bv, idx)) (slotAddr dp.bv (BitVec.ofNat 64 k)) rv) ∧
        L.ksb s' = L.ksb s ∧
        MdbStep (L.mem s) Z.G (L.mem s') (insG Z.G (cslotAddr (pp.bv, idx)) (slotAddr dp.bv (BitVec.ofNat 64 k)) rv) ∧
        (∀ y, IsSlot Z.th y → y ≠ slotAddr dp.bv (BitVec.ofNat 64 k) → capAt (L.mem s') y = capAt (L.mem s) y) ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv (insG Z.G (cslotAddr (pp.bv, idx)) (slotAddr dp.bv (BitVec.ofNat 64 k)) rv) Z.vs)
            H Cs Ac' Lst' D' s' a σ' ⦄ := by
  have hDL : DestLive Z.th (L.mem s) (L.ksb s) dp := Or.inl hDLc
  have hX := J.xtop
  obtain ⟨hPl, ⟨hSt, hV, hM, hC, hI⟩, hFI, -, hMO, -, -⟩ := hX.rel
  have hTP := hS.sr.2
  set src := cslotAddr (pp.bv, idx) with hsrcdef
  set dest := slotAddr dp.bv (BitVec.ofNat 64 k) with hdestdef
  set c : capability.Cap := .Frame q .Small vm false false false 0#u64 0#u64 with hcdef
  set srcC : capability.Cap := .Frame ptr .Large rt false mm false fa fv with hsrcCdef
  have hcap := hS.cap
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hs : IsSlot Z.th src := hAs.isSlot
  have hd : IsSlot Z.th dest := ⟨dp, k, Or.inl ⟨r, hdp, hk⟩, rfl⟩
  have hdest' : cslotAddr (dp.bv, Fl4Spec.natToCref r k) = dest := cslotAddr_natToCref dp.bv r k (by omega) hk
  have hlen : (Fl4Spec.natToCref r k).length = r := natToCref_length r k (by omega)
  have hsd : src ≠ dest := by
    intro e; rw [e, hdst] at hcap; have := eq_of_ok_eq hcap; rw [hsrcCdef] at this; cases this
  have hes : EncWf srcC := by rw [capAt_words] at hcap; exact decode_encWf hcap
  have hcp : Canonical ptr := by have h := hes; rw [hsrcCdef] at h; exact h.1
  have he : EncWf c := ⟨canonical_window hcp hal hq1 (by omega), by omega, by decide, by decide⟩
  have hsm : src ∈ Z.G.chains.flatten := (hM.members src).2 ⟨hs, _, hcap, by simp⟩
  have hdnm : dest ∉ Z.G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members dest).1 h
    rw [hdst] at h0; exact hn (eq_of_ok_eq h0).symm
  refine WP.spec_mono (WP.spec_and (Vs.sub_step (L := L) (Vs.vsSubHyps_top (st := st) (L := L)) hTP.pl hTP.pt hpp
      hidx s a σ Z.G hTP.vs hTP.vo hTP.po hS hal hdp hr hk hdst hq1 hq2 hvm hqal)
    (WP.spec_and (Vs.insert_trace hPl s Z.G hM hsm hd hdnm hcap c he)
      (insert_delinv_imp hPl s Z.G hM hsm hd hdnm hcap c he (by simp [hcdef]) rfl))) ?_
  rintro s' ⟨⟨σ', hci, hS', hks, hMS, hoth⟩, ⟨hF, -, hdc, -⟩, hdi⟩
  set G' := insG Z.G src dest rv with hG'
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) (absCap c) (pp.bv, idx) (dp.bv, Fl4Spec.natToCref r k) σ).1 := by
    rw [hci]; rfl
  have hcn := capInsert_nkn (absCap c) _ _ σ _ hmem
  have hkc : KeepC σ σ' := keepC_of hcn (capInsert_nko (absCap c) _ _ σ _ hmem) (by
    rintro p (rfl | hp)
    · obtain ⟨cs, h, -⟩ := hSt.cnode pp rs hpp; exact ⟨rs, cs, h⟩
    · rw [Set.mem_singleton_iff.1 hp]; obtain ⟨cs, h, -⟩ := hSt.cnode dp r hdp; exact ⟨r, cs, h⟩)
  have hkcT : KeepCT σ σ' := KeepCT.of_cnK hcn
  have hMO' : MdbOKV (L.ksb s) (L.mem s') G' := hMS.okv hMO
  have hw : P1.WritesIn st s s' (InSlot Z.th) := by
    refine ⟨hF.1, hF.2.1, fun b hb hn => hF.2.2 b hb fun ⟨y, k, hy, hk', e⟩ => hn ⟨y, hy, ?_⟩⟩
    have hf := hy.fit hPl
    have := hk'.lt
    have hv := wordOf_val (a := y) (k := k) (by omega)
    rw [e, hv]; omega
  have hw' : P1.WritesIn st s s' (Sched.SlotWd Z.th) :=
    ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn (Sched.slotSpan_wd hPl hb h)⟩
  have hcapV : ∀ y, IsSlot Z.th y → y ≠ dest → capV (L.mem s') y = capV (L.mem s) y := fun y hy hne => by
    have e := hoth y hy hne
    rw [capAt_capV, capAt_capV] at e; exact eq_of_ok_eq e
  have hTS : ∀ n, n < tcbSlots → ∀ t, Z.th t = some .tcb →
      capAt (L.mem s') (slotOf t n) = capAt (L.mem s) (slotOf t n) := by
    intro n hn t ht
    have hi : IsSlotAt Z.th t n := Or.inr ⟨ht, hn⟩
    exact hoth _ ⟨t, n, hi, rfl⟩ (fun e => slotOf_ne_cnV hPl hi ht hdp hlen (e.trans hdest'.symm))
  have hX1 := XTopAt.slotStep hX hw' hcn hkc ⟨hS'.R, hS'.V, hS'.M, hS'.C, hS'.I⟩ hS'.F hMO' (hTS 1 (by decide))
  have hX1' : XTopAt (L := L) AR (Z.mv G' Z.vs) s' a σ' := hX1
  have hn0 : capV (L.mem s) dest = .Null := capV_of_capAt hdst
  have hnu : ∀ p sb fi d, capV (L.mem s') dest ≠ .Untyped p sb fi d := fun p sb fi d e => by
    rw [hdc, hcdef] at e; cases e
  have hCK : CoverKept Z.th (L.mem s) (L.mem s') := fun y hy hp hu => by
    have hyd : y ≠ dest := fun e => by rw [e, hn0, physF_null] at hp; cases hp
    have e := hcapV y hy hyd
    exact ⟨y, hy, by rw [e]; exact hp, by rw [e]; exact hu, by rw [e], by rw [e]⟩
  have hUK : UtKept Z.th (L.mem s) (L.mem s') := fun x hx p sb fi d hc => by
    have hxd : x ≠ dest := fun e => hnu p sb fi d (e ▸ hc)
    exact ⟨x, hx, fi, by rw [← hcapV x hx hxd]; exact hc, Or.inl le_rfl⟩
  have horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl := by
    intro sl h
    by_cases e : sl = (dp.bv, Fl4Spec.natToCref r k)
    · right; rw [e]; exact ⟨dp, rfl, Or.inl (by rw [hlen]; exact hdp)⟩
    · left; rw [← capInsert_orig (absCap c) _ _ σ ((), σ') hmem sl e]; exact h
  have hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn.1; exact e
  have hutc := J.ins_utc arI (G' := G') hdp hlen (by rw [hdest']; exact hcapV) (by rw [hdest']; exact hdst)
    (by rw [hdest']; exact hnu) hw (capInsert_cdt (absCap c) _ _ σ _ hmem)
    (fun sl e => capInsert_orig (absCap c) _ _ σ ((), σ') hmem sl e) hgp hS'.M hDL
  have hjc := J.jcov_cover hw.1 hS'.M hCK hUK
    (fun q hq => J.deadP_slot hX1' hcn hkcT hw (J.jcov.dead q hq))
    (J.idleW_keep hX1'.fin.1.1.1 (CnStep.of_cnK hcn).idle (CnStep.of_cnK hcn).isc)
  have hfh' : ∀ t, Z.th t = some .tcb → capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) =
        .Endpoint ep b0 b1 b2 b3 b4 := by
    intro t ht
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have e := hTS 3 (by decide) t ht
    rw [capAt_capV, capAt_capV] at e
    rw [cslot_tcb3, eq_of_ok_eq e, ← cslot_tcb3]; exact hJ.fh t ht
  -- the alias's objects: inside the large frame's range
  obtain ⟨bs, ts⟩ := frame_range ptr .Large rt false mm fa fv false
  obtain ⟨bc, tc⟩ := frame_range q .Small vm false false 0#u64 0#u64 false
  have hmL : (maskF (fbitsF .Large)).val = 2 ^ 21 - 1 := by
    rw [maskF_val (by rw [fbitsF_val]; decide), fbitsF_val]; rfl
  have hmS : (maskF (fbitsF .Small)).val = 2 ^ 12 - 1 := by
    rw [maskF_val (by rw [fbitsF_val]; decide), fbitsF_val]; rfl
  have hfit : ptr.val + 2 ^ 21 ≤ 2 ^ 64 := by have : ptr.val < 2 ^ 64 := ptr.hBounds; omega
  have tsv : topF srcC = ptr.val + 2 ^ 21 - 1 := by
    rw [ts]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hmL]
    omega
  have tcv : topF c = q.val + 4095 := by
    rw [tc]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hmS]
    omega
  have tsv' : topF (.Frame ptr .Large rt false mm false fa fv) = ptr.val + 2 ^ 21 - 1 := tsv
  have tcv' : topF (.Frame q .Small vm false false false 0#u64 0#u64) = q.val + 4095 := tcv
  have hTKH : TypedKeptH Z.th H (Sched.idleScW (L := L) s) (L.mem s) (L.mem s') := by
    intro y hy
    by_cases e : y = dest
    · right; right
      rw [e, hdc]
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hob : FrApartH H (.Frame ptr .Large rt false mm false fa fv) := by
        have h := hJ.cobj src hs; rw [capV_of_capAt hcap] at h; exact h
      refine ⟨⟨fun _ _ _ _ _ _ e => (by rw [hcdef] at e; cases e), fun _ _ _ _ e => (by rw [hcdef] at e; cases e),
        fun _ _ e => (by rw [hcdef] at e; cases e)⟩, ?_⟩
      show FrApartH H (.Frame q .Small vm false false false 0#u64 0#u64)
      intro q0 k0 hq0 hk0
      rcases hob q0 k0 hq0 hk0 with h | h
      · left; rw [bc]; rw [bs] at h; omega
      · right; rw [tcv']; rw [tsv'] at h; omega
    · right; left; exact ⟨y, hy, by rw [hcapV y hy e]⟩
  obtain ⟨hJC, R⟩ := jowes_slotDFH J hX1' hcn hkcT hw hS'.F hMO' (capInsert_nkz (absCap c) _ _ σ _ hmem) hTKH hfh'
    (let ⟨_, _, hJ⟩ := J.jpl; hJ.bfsT fun t ht => Or.inl (hTS 2 (by decide) t ht)) (hdi J.del) hUK hjc horig hutc
  have hvT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s') :=
    Vs.VsSlotsT.of_some (· = dest) (fun y hy hn => hcapV y hy hn) (fun y _ e P L4 L3 L2 L1 h => by
      subst e
      have h0 := h src hs
      rw [capV_of_capAt hcap] at h0
      rw [hdc]
      exact (vcap_alias (h0.ok_of fun _ _ _ => ⟨by simp [hsrcCdef], by simp [hsrcCdef], by simp [hsrcCdef]⟩) hq1 hq2 hqal).toW)
      (fun y _ e U h => by
        subst e
        have h0 := h src hs
        rw [capV_of_capAt hcap, hsrcCdef] at h0
        rw [hdc, hcdef]
        have hL : (fbitsF .Large).val = 21 := by rw [fbitsF_val]; rfl
        have hS : (fbitsF .Small).val = 12 := by rw [fbitsF_val]; rfl
        intro _ x hx1 hx2
        rw [hS] at hx2
        exact h0 rfl x (by omega) (by rw [hL]; omega))
      fun y _ e _ => by subst e; rw [hdc, hcdef]; simp [Vs.NativeCap]
  have hZf : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s') y = .Zombie p zt n →
      ∃ y0, IsSlot Z.th y0 ∧ capV (L.mem s) y0 = .Zombie p zt n := fun y hy p zt n h => by
    by_cases e : y = dest
    · subst e; rw [hdc, hcdef] at h; cases h
    · exact ⟨y, hy, by rw [← hcapV y hy e]; exact h⟩
  have hLv' := LiveDN.wstepC J J.live hX1' (fun p hp => R.jcov.dead p (J.zD p hp)) hcn.idle hw
    [(dp.bv, Fl4Spec.natToCref r k)]
    (fun sl hsl => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hsl
      subst hsl; exact ⟨dp, r, rfl, hdp, hlen, hDLc⟩)
    (fun y hy hne => hcapV y hy (by rw [← hdest']; exact hne _ (List.mem_singleton_self _)))
    (fun sl h => by
      by_cases e : sl = (dp.bv, Fl4Spec.natToCref r k)
      · exact Or.inr (by simp [e])
      · exact Or.inl (by rw [← capInsert_orig (absCap c) _ _ σ ((), σ') hmem sl e]; exact h))
    (fun sl hsl h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hsl
      subst hsl; rw [hdest', hdc, hcdef] at h; cases h)
    hZf
    (fun y0 hy0 hn => by
      have e : y0 ≠ dest := fun e => hn (by rw [e]; exact hn0)
      exact ⟨y0, hy0, by rw [hcapV y0 hy0 e]; exact hn, by rw [hcapV y0 hy0 e]⟩)
  exact ⟨σ', hci, hS', hks, hMS, hoth, Ac, Lst, D,
    J.cs_frameV hw.1 hX1' (KBack.of_keepCT hkcT)
      (J.bfK (J.slot2Fr hkcT hX1'.rel.2.1.1 fun q hq => Or.inl (hTS 2 (by decide) q hq)) hvT) hJC R (J.vsc.step hvT) (J.ext.step hvT (J.vkeep_slot hw))
      hLv' (fun p hp => J.zD p (ZTcb.of_zombies hZf hp))⟩

end

/-! ## The destination CNode live, and the alias loop at `J` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **`subframe_dest`'s CNode is live** (`DestLive`: named by the node cap,
held in its slot, or by the CNode cap the lookup reaches, held in the slot
it returns). -/
theorem subframe_dest_live {th : TypedHeap} (s : S) (σ : Fl4Spec.State Unit) (hSt : StateRel th (L.mem s) σ)
    (hSV : SlotsValid th (L.mem s)) {y : U64} (hy : IsSlot th y) {nc : capability.Cap} {nc' : Fl4Spec.Cap}
    (hcy : capAt (L.mem s) y = ok nc) (hnr : CapRel nc nc') (hnv : CapValid th nc) (a0 a1 a2 a4 : U64) :
    vspace.subframe_dest st s y a0 a1 a2 a4 ⦃ res => ∀ d, res = .Ok d → DestCap th (L.mem s) d ⦄ := by
  unfold vspace.subframe_dest
  rw [slot_cap_eq, hcy]; simp only [bind_ok]
  by_cases hd : a1 = 0#u64
  · subst hd
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have hcv := capV_of_capAt hcy
    obtain ⟨HWF, -⟩ := hnr
    clear hcy hnv
    cases nc
    case CNode q rad gs g =>
      obtain ⟨hr64, -, -⟩ := HWF
      simp only [vspace.cnode_of, bind_ok, lift, uncurry_apply_pair]
      obtain ⟨z, hz, -⟩ := shl_radix hr64
      rw [hz]; simp only [bind_ok]
      split_ifs <;> simp only [error.range, bind_ok, WP.spec_ok] <;> intro d h <;> cases h
      exact ⟨y, rad, gs, g, hy, hcv⟩
    all_goals
      simp only [vspace.cnode_of, bind_ok, vspace.failed_lookup, WP.spec_ok]
      intro d h; cases h
  have hd' : (a1 != 0#u64) = true := by simpa using hd
  simp only [hd', ↓reduceIte]
  unfold cspace.lookup_target_slot
  obtain ⟨r1, hr1, e1, -, hrel1⟩ := spec_exists
    (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hSt hSV false nc nc' hnr hnv a0 a1)
  rw [hr1]; simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  cases r1 with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    intro d h; cases h
  | Ok val =>
    cases e1 with
    | error _ => exact hrel1.elim
    | ok dsl =>
      obtain ⟨rfl, pd, hpd1, hpd, -⟩ := hrel1
      obtain ⟨c2, a2', hc2, hca2, -⟩ := hSt.slot_cap (Z := Unit) hpd1 hpd
      have hsl : IsSlot th (cslotAddr dsl) := AbsSlot.isSlot ⟨pd, hpd1, Or.inl hpd⟩
      simp only [bind_ok]
      rw [slot_cap_eq, hc2]; simp only [bind_ok]
      have hcv := capV_of_capAt hc2
      obtain ⟨HWF, -⟩ := hca2
      clear hc2
      cases c2
      case CNode q rad gs g =>
        obtain ⟨hr64, -, -⟩ := HWF
        simp only [vspace.cnode_of, bind_ok, lift, uncurry_apply_pair]
        obtain ⟨z, hz, -⟩ := shl_radix hr64
        rw [hz]; simp only [bind_ok]
        split_ifs <;> simp only [error.range, bind_ok, WP.spec_ok] <;> intro d h <;> cases h
        exact ⟨cslotAddr dsl, rad, gs, g, hsl, hcv⟩
      all_goals
        simp only [vspace.cnode_of, bind_ok, vspace.failed_lookup, WP.spec_ok]
        intro d h; cases h

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **The alias loop at `J`** (VsSubRel's `insert_subframes_rel`, each
insert by `JAtZ.subInsJ`; the destination's CNode stays live: its naming
cap is in no destination slot, those held nothing). -/
theorem insert_subframesJ {s : S} {a : A} {σ : Fl4Spec.State Unit} {Ac : Set U64} {Lst : U64 → List U64}
    {D : Set U64} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pp : U64} {rs : Nat} (hpp : Z.th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {ptr rt fa fv : U64} {mm rv : Bool}
    (hS : SubRel st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (subSRJ st Z AR) (cslotAddr (pp.bv, idx))
      (.Frame ptr .Large rt false mm false fa fv) rv s a σ Z.G)
    (hal : ptr.val % 2 ^ 21 = 0)
    {dp : U64} {r : Nat} (hdp : Z.th dp = some (.cnode r)) (hr : r < 64) {first count base vm : U64}
    (hfc : first.val + count.val ≤ 2 ^ r) (hb1 : ptr.val ≤ base.val) (hb2 : base.val + count.val * 4096 ≤ ptr.val + 2 ^ 21)
    (hvm : 1 ≤ vm.val ∧ vm.val ≤ 3) (hbal : base.val % 4096 = 0)
    (hempty : ∀ j : Nat, first.val ≤ j → j < first.val + count.val →
      capAt (L.mem s) (slotAddr dp.bv (BitVec.ofNat 64 j)) = ok .Null)
    (hDL : DestCap Z.th (L.mem s) dp) :
    vspace.insert_subframes st s (cslotAddr (pp.bv, idx)) dp first base count vm ⦃ s' => ∃ σ' G',
      Fl4Spec.NonDet.mapMx (subIns (pp.bv, idx) base.bv (vmRightsOf vm)) (subList dp r first.val count.val) σ =
        ({((), σ')}, False) ∧
      SubRel st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (subSRJ st Z AR) (cslotAddr (pp.bv, idx))
        (.Frame ptr .Large rt false mm false fa fv) rv s' a σ' G' ∧
      L.ksb s' = L.ksb s ∧ MdbStep (L.mem s) Z.G (L.mem s') G' ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' s' a σ' ⦄ := by
  have hfit : ptr.val + 2 ^ 21 ≤ 2 ^ 64 := by have : ptr.val < 2 ^ 64 := ptr.hBounds; omega
  have hPl : Placed Z.th := hS.sr.2.pl
  set Lst0 := subList dp r first.val count.val with hLst
  set g := subIns (pp.bv, idx) base.bv (vmRightsOf vm) with hg
  unfold vspace.insert_subframes vspace.insert_subframes_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 => count.val - x.2.val)
    (inv := fun x : S × U64 => x.2.val ≤ count.val ∧ ∃ σi Gi,
      SubRel st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (subSRJ st Z AR) (cslotAddr (pp.bv, idx))
        (.Frame ptr .Large rt false mm false fa fv) rv x.1 a σi Gi ∧
      MdbStep (L.mem s) Z.G (L.mem x.1) Gi ∧ L.ksb x.1 = L.ksb s ∧
      (∀ j : Nat, first.val + x.2.val ≤ j → j < first.val + count.val →
        capAt (L.mem x.1) (slotAddr dp.bv (BitVec.ofNat 64 j)) = ok .Null) ∧
      (∀ σf, Fl4Spec.NonDet.mapMx g (Lst0.drop x.2.val) σi = ({((), σf)}, False) →
        Fl4Spec.NonDet.mapMx g Lst0 σ = ({((), σf)}, False)) ∧
      (∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Gi Z.vs) H Cs Ac' Lst' D' x.1 a σi) ∧
      DestCap Z.th (L.mem x.1) dp)
  · rintro ⟨si, i⟩ ⟨hic, σi, Gi, hSi, hMSi, hksi, hemp, hcont, ⟨Aci, Lsti, Di, Ji⟩, hDLi⟩
    unfold vspace.insert_subframes_loop.body
    simp only at hic hksi hemp hcont hDLi ⊢
    by_cases hlt : i < count
    · have hlt' : i.val < count.val := hlt
      rw [if_pos hlt]
      step as ⟨i1, hi1⟩
      simp only [lift, bind_ok]
      rw [show obj.Slot.index dp (core.num.U64.wrapping_add first i) =
        ok (slotAddr dp.bv (core.num.U64.wrapping_add first i).bv) from spec_eq_ok (slot_index_spec _ _)]
      simp only [bind_ok]
      have hk2 : first.val + i.val < 2 ^ r := by omega
      have hfiv : (core.num.U64.wrapping_add first i).bv = BitVec.ofNat 64 (first.val + i.val) := by
        apply BitVec.eq_of_toNat_eq
        have : 2 ^ r < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hr
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        try (rw [Nat.mod_eq_of_lt (by omega)])
      have hi1v : i1.val = i.val * 4096 := by
        rw [hi1]; simp [Nat.shiftLeft_eq, U64.size_def, U64.numBits]
        try (rw [Nat.mod_eq_of_lt (by omega)])
        try omega
      have hqv : (core.num.U64.wrapping_add base i1).val = base.val + i.val * 4096 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hi1v]; omega
      rw [hfiv]
      have hnull := hemp (first.val + i.val) (by omega) (by omega)
      refine WP.spec_bind (JAtZ.subInsJ (Z := Z.mv Gi Z.vs) Ji hpp hidx hSi hal hdp hr hk2 hnull
        (q := core.num.U64.wrapping_add base i1) (by rw [hqv]; omega) (by
          rw [hqv]; have := Nat.mul_le_mul_right 4096 (show i.val + 1 ≤ count.val by omega)
          rw [Nat.add_mul] at this; omega) hvm (by rw [hqv]; omega) hDLi) ?_
      rintro s2 ⟨σ2, hci, hS2, hks2, hMS2, hoth, Ac2, Lst2, D2, J2⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = i.val + 1 := by simpa using hi4
      refine ⟨by omega, ⟨σ2, _, hS2, hMSi.trans hMS2, hks2.trans hksi, fun j h1 h2 => ?_, fun σf hf => hcont σf ?_,
        ⟨Ac2, Lst2, D2, J2⟩, ?_⟩, by omega⟩
      · have hne : slotAddr dp.bv (BitVec.ofNat 64 j) ≠ slotAddr dp.bv (BitVec.ofNat 64 (first.val + i.val)) := by
          intro e
          have hj : IsSlotAt Z.th dp j := Or.inl ⟨r, hdp, by omega⟩
          have hk' : IsSlotAt Z.th dp (first.val + i.val) := Or.inl ⟨r, hdp, hk2⟩
          rcases hj.apart hPl hk' (fun ⟨_, h3⟩ => by omega) with h | h <;>
            (change slotOf dp j = slotOf dp (first.val + i.val) at e; rw [e] at h; omega)
        rw [hoth _ ⟨dp, j, Or.inl ⟨r, hdp, by omega⟩, rfl⟩ hne]
        exact hemp j (by omega) h2
      · rw [subList_drop dp r first.val count.val i.val hlt']
        rw [hi4v] at hf
        have hgi : g (i.val, (dp.bv, Fl4Spec.natToCref r (first.val + i.val))) σi = ({((), σ2)}, False) := by
          rw [hg]; unfold subIns
          have e : (base.bv + BitVec.ofNat 64 (i.val * 4096)) = (core.num.U64.wrapping_add base i1).bv := by
            apply BitVec.eq_of_toNat_eq
            rw [show (core.num.U64.wrapping_add base i1).bv.toNat = (core.num.U64.wrapping_add base i1).val from rfl, hqv]
            simp [BitVec.toNat_add]; omega
          rw [e]; exact hci
        rw [mapMx_cons_one hgi]; exact hf
      · obtain ⟨y, r', gs, g', hy, hc⟩ := hDLi
        have hyd : y ≠ slotAddr dp.bv (BitVec.ofNat 64 (first.val + i.val)) := fun e => by
          rw [e, capV_of_capAt hnull] at hc; cases hc
        have e := hoth y hy hyd
        rw [capAt_capV, capAt_capV] at e
        exact ⟨y, r', gs, g', hy, by rw [eq_of_ok_eq e]; exact hc⟩
    · rw [if_neg hlt]
      have hic' : i.val = count.val := by
        have : ¬ i.val < count.val := hlt
        omega
      refine (WP.spec_ok _).2 ⟨σi, Gi, hcont σi ?_, hSi, hksi, hMSi, Aci, Lsti, Di, Ji⟩
      rw [hic', subList_drop_all]; rfl
  · refine ⟨by simp, σ, Z.G, hS, MdbStep.refl hS.M, rfl, fun j h1 h2 => hempty j (by simpa using h1) h2,
      fun σf hf => ?_, ⟨Ac, Lst, D, ?_⟩, hDL⟩
    · simpa using hf
    · exact J

end


/-! ## `DeriveSubframe`'s decode and invocation at `J` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`DeriveSubframe` at `J`** (VsSubRel's `derive_subframe_rel` from
`JAtZ`: the caller's restart by `JAtZ.restartJ`, the loop by
`insert_subframesJ`, the destination's CNode live by `subframe_dest_live`):
an error with the states unchanged, or the spec's single invocation after
the restart, its single outcome at `JAtZ`. -/
theorem derive_subframeJ {s : S} {a : A} {σ : Fl4Spec.State Unit} {Ac : Set U64} {Lst : U64 → List U64}
    {D : Set U64} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    {pp : U64} {rs : Nat} (hpp : Z.th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {ptr rt fa fv : U64} {sz : capability.FrameSize} {dev mm : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Frame ptr sz rt dev mm false fa fv))
    (hno : sz = .Large → dev = false → ∀ x ∈ Z.G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame ptr sz rt dev mm false fa fv) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame ptr sz rt dev mm false fa fv) (capV (L.mem s) x))
    (hVC : VsCapsW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ex : Array obj.Slot 3#usize) {y : obj.Slot} (hex0 : vspace.extra ex 0#usize = ok (some y)) (hy : IsSlot Z.th y)
    {nc : capability.Cap} (hcy : capAt (L.mem s) y = ok nc) {nc' : Fl4Spec.Cap} (hnr : CapRel nc nc')
    (hnv : CapValid Z.th nc) (nsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    vspace.derive_subframe st arI s a length (cslotAddr (pp.bv, idx)) (.Frame ptr sz rt dev mm false fa fv) buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ SysErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodeDeriveSubframe (Z := Unit) (args.map UScalar.bv) (pp.bv, idx)
          (.pageCap dev ptr.bv (vmRightsOf rt) (if mm then .vmVSpaceMap else .vmNoMap) (frameSizeOf sz)
            (if mm then some (fa.bv, fv.bv) else none)) ((nc', nsl) :: rest)) σ = ({(.error e', σ)}, False) ∧
        res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ res.2.2 = a ∧ ∃ iv,
        ExceptT.run (Fl4Spec.decodeDeriveSubframe (Z := Unit) (args.map UScalar.bv) (pp.bv, idx)
          (.pageCap dev ptr.bv (vmRightsOf rt) (if mm then .vmVSpaceMap else .vmNoMap) (frameSizeOf sz)
            (if mm then some (fa.bv, fv.bv) else none)) ((nc', nsl) :: rest)) σ = ({(.ok iv, σ)}, False) ∧
        ∃ σ', (Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
          Fl4Spec.performDeriveSubframe iv) σ = ({((), σ')}, False) ∧
        ∃ (G' : MdbGhost) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' res.2.1 a σ') ⦄ := by
  have hX := J.xtop
  obtain ⟨hPl, ⟨hSt, hSV, hM, hC, hI⟩, hFI, -, hMO, -, -⟩ := hX.rel
  have hU : UtInv (L.mem s) Z.G := J.ut
  have hFR : Vs.FrameInv (L.mem s) Z.G := hMO.1.1
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  have hact := J.kern.act
  obtain ⟨s1, σ1, x1, -, hst1, -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  generalize hD : ExceptT.run (Fl4Spec.decodeDeriveSubframe (Z := Unit) (args.map UScalar.bv) (pp.bv, idx)
    (.pageCap dev ptr.bv (vmRightsOf rt) (if mm then .vmVSpaceMap else .vmNoMap) (frameSizeOf sz)
      (if mm then some (fa.bv, fv.bv) else none)) ((nc', nsl) :: rest)) σ = DD
  obtain ⟨cS, aS, hcS, hcaS, -⟩ := hSt.slot_cap (Z := Unit) (sl := (pp.bv, idx)) (p := pp) rfl
    (by simpa [hidx] using hpp)
  rw [hcap] at hcS; cases eq_of_ok_eq hcS
  have hrt : 1 ≤ rt.val ∧ rt.val ≤ 3 := hcaS.1
  unfold vspace.derive_subframe
  rw [hct]; apply ok_bind_spec
  rw [hex0]; simp only [bind_ok]
  by_cases hl6 : length >= 6#u64
  swap
  · rw [if_neg hl6]
    simp only [error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .truncatedMessage, rfl, trivial, ?_, rfl, rfl⟩)
    rw [← hD]
    exact decodeSub_trunc (Or.inr (by rw [List.length_map, ← hlen]; scalar_tac)) _ _ σ
  rw [if_pos hl6]
  have hill : (∀ p r mt mp, (Fl4Spec.ArchCap.pageCap dev ptr.bv (vmRightsOf rt)
      (if mm then .vmVSpaceMap else .vmNoMap) (frameSizeOf sz) (if mm then some (fa.bv, fv.bv) else none)) ≠
      .pageCap false p r mt .x64LargePage mp) → DD = ({(.error .illegalOperation, σ)}, False) := fun h => by
    rw [← hD]; exact decodeSub_illegal (by simp) (by rw [List.length_map, ← hlen]; scalar_tac) _ h σ
  cases sz <;> cases dev
  all_goals try
    simp only [vspace.large_ram_frame, error.illegal, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, .illegalOperation, rfl, trivial,
      hill (fun p r mt mp h => by simp [frameSizeOf] at h), rfl, rfl⟩)
  simp only [vspace.large_ram_frame, Bool.false_eq_true, ↓reduceIte, bind_ok]
  have hal' : ptr.val % 2 ^ 21 = 0 := by
    have h := hSV.cnode pp rs hpp (blVal 0 idx) (hidx ▸ blVal_lt idx) _
      (by rw [show slotAddr pp.bv (BitVec.ofNat 64 (blVal 0 idx)) = cslotAddr (pp.bv, idx) from
        (slotAddr_ofBl pp idx).symm]; exact hcap)
    exact h
  have hfit : ptr.val + 2 ^ 21 ≤ 2 ^ 64 := by have : ptr.val < 2 ^ 64 := ptr.hBounds; omega
  have hno' := hno rfl rfl
  have hfr0' := hFR.alias_ov ((hM.members _).2 ⟨AbsSlot.isSlot (th := Z.th) (sl := (pp.bv, idx)) ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩, _, hcap, by simp⟩) (capV_of_capAt hcap)
  clear hill hno
  obtain ⟨a0, a1, a2, a3, a4, a5, rs', rfl⟩ :
      ∃ a0 a1 a2 a3 a4 a5 r, args = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: r := by
    have : 6 ≤ args.length := by rw [← hlen]; scalar_tac
    match args, this with
    | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: r, _ => exact ⟨a0, a1, a2, a3, a4, a5, r, rfl⟩
  rw [hargs 0#u64 a0 rfl, hargs 1#u64 a1 rfl, hargs 2#u64 a2 rfl, hargs 3#u64 a3 rfl, hargs 4#u64 a4 rfl]
  simp only [bind_ok]
  simp only [List.map_cons, frameSizeOf] at hD
  rw [decodeSub_main] at hD
  simp only [uncurry_apply_pair]
  step as ⟨i, hi⟩
  have hiv : i.val = 2097152 := by
    rw [hi]; simp [Nat.shiftLeft_eq, U64.size_def, U64.numBits]
  have hu3 : Fl4Spec.unat a3.bv = a3.val := rfl
  have hu4 : Fl4Spec.unat a4.bv = a4.val := rfl
  by_cases ho1 : a3 >= i
  · rw [if_pos ho1]; simp only [error.invalid_arg, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 3, rfl, rfl, ?_, rfl, rfl⟩)
    rw [← hD]; exact sfAfter_inv3 (Or.inl (by rw [hu3]; have : i.val ≤ a3.val := ho1; omega))
  rw [if_neg ho1]
  have ho1' : a3.val < 2097152 := by have : ¬ i.val ≤ a3.val := ho1; omega
  simp only [lift, bind_ok]
  have hand : (a3 &&& 4095#u64).val = a3.val % 4096 := by
    rw [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod a3.val 12
  by_cases ho2 : (a3 &&& 4095#u64) != 0#u64
  · rw [if_pos ho2]; simp only [error.invalid_arg, bind_ok]
    have hne : (a3 &&& 4095#u64).val ≠ 0 := fun h => (bne_iff_ne.1 ho2) (UScalar.eq_of_val_eq (by rw [h]; rfl))
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 3, rfl, rfl, ?_, rfl, rfl⟩)
    rw [← hD]; exact sfAfter_inv3 (Or.inr (by rw [hu3, ← hand]; exact hne))
  rw [if_neg ho2]
  have ho2' : a3.val % 4096 = 0 := by
    have : ¬ (a3 &&& 4095#u64).val ≠ 0 := fun hne => ho2 (bne_iff_ne.2 (fun e => hne (by rw [e]; rfl)))
    omega
  have hinv : ¬ (2 ^ 21 ≤ Fl4Spec.unat a3.bv ∨ Fl4Spec.unat a3.bv % 4096 ≠ 0) := by rw [hu3]; omega
  step as ⟨i2, hi2⟩
  step as ⟨mx, hmx⟩
  have hmxv : mx.val = (2 ^ 21 - a3.val) / 4096 := by
    rw [hmx, hi2, hiv, Nat.shiftRight_eq_div_pow]; rfl
  have hmxe : BitVec.ofNat 64 ((2 ^ 21 - Fl4Spec.unat a3.bv) / 4096) = mx.bv := ofNat_bv (by rw [hu3, hmxv])
  by_cases hc1 : a4 < 1#u64
  · rw [if_pos hc1]; simp only [error.range, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .rangeError 1 (BitVec.ofNat 64 ((2 ^ 21 - Fl4Spec.unat a3.bv) / 4096)),
      rfl, ⟨rfl, hmxe⟩, ?_, rfl, rfl⟩)
    rw [← hD]; exact sfAfter_range hinv (Or.inl (by rw [hu4]; scalar_tac))
  rw [if_neg hc1]
  by_cases hc2 : a4 > mx
  · rw [if_pos hc2]; simp only [error.range, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .rangeError 1 (BitVec.ofNat 64 ((2 ^ 21 - Fl4Spec.unat a3.bv) / 4096)),
      rfl, ⟨rfl, hmxe⟩, ?_, rfl, rfl⟩)
    rw [← hD]; exact sfAfter_range hinv (Or.inr (by rw [hu4, hu3, ← hmxv]; exact hc2))
  rw [if_neg hc2]
  have hc1' : 1 ≤ a4.val := by scalar_tac
  have hc2' : a4.val ≤ mx.val := by scalar_tac
  have hrng : ¬ (Fl4Spec.unat a4.bv < 1 ∨ (2 ^ 21 - Fl4Spec.unat a3.bv) / 4096 < Fl4Spec.unat a4.bv) := by
    rw [hu3, hu4, ← hmxv]; omega
  rw [sfAfter_go hinv hrng] at hD
  -- the node
  refine WP.spec_bind (WP.spec_and (subframe_dest_rel (L := L) s σ hSt hSV hcy hnr hnv (pp.bv, idx) ptr.bv
    (vmRightsOf rt) a0 a1 a2 a3 a4 a5) (subframe_dest_live (L := L) s σ hSt hSV hy hcy hnr hnv a0 a1 a2 a4)) ?_
  rintro r ⟨hr, hlive⟩
  rw [hD] at hr
  cases r with
  | Err e =>
    obtain ⟨e', he, hE⟩ := hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨e, e', rfl, he, hE, rfl, rfl⟩)
  | Ok dest =>
    obtain ⟨rr, hdp, hr64, hfc, hE⟩ := hr
    have hDL := hlive dest rfl
    have hrr : 2 ^ rr < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hr64
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [ensure_empty_run_eq (L := L) s dest a2 a4 (by omega)]
    have hdr := sfDests_run (L := L) s σ hSt hdp hr64 a2.val a4.val hfc
    by_cases hemp : ∀ j : Nat, a2.val ≤ j → j < a2.val + a4.val →
        capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 j)) = ok .Null
    swap
    · rw [if_neg hemp]
      rw [if_neg hemp] at hdr
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .deleteFirst, rfl, trivial, by rw [hE]; exact runE_bind_err hdr, rfl, rfl⟩)
    rw [if_pos hemp]
    rw [if_pos hemp] at hdr
    rw [runE_bind_ok hdr, runE_ret] at hE
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [hargs 5#u64 a5 rfl, bind_ok, from_word_eq, bind_ok]
    obtain ⟨m, hm, hm1, hm3, hmv⟩ := vm_mask rt hrt (rightsW a5)
    rw [hm, bind_ok]
    -- the Restart, at `J`
    rw [hs1, bind_ok]
    have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := by
      have h := set_thread_state_slots (L := L) Z.th hPl s ct sched.TS_RESTART htcb hact
      rw [hs1, WP.spec_ok] at h; exact h
    have hksb1 : L.ksb s1 = L.ksb s := by
      have h := set_thread_state_cases (L := L) s ct sched.TS_RESTART
      rw [hs1, WP.spec_ok] at h
      rcases h with rfl | rfl <;> simp
    obtain ⟨-, ⟨hSt1, hSV1, hM1, hC1, hI1⟩, hFI1, -, -, -, -⟩ := J1.xtop.rel
    have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
    have hs : IsSlot Z.th (cslotAddr (pp.bv, idx)) := hAs.isSlot
    have hSub1 : SubRel st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (subSRJ st Z AR) (cslotAddr (pp.bv, idx))
        (.Frame ptr .Large rt false mm false fa fv) (revOf (L.mem s) (cslotAddr (pp.bv, idx))) s1 a σ1 Z.G :=
      { R := hSt1, V := hSV1, M := hM1, C := hC1, I := hI1, U := UtInv.of_same hM hU hSS
        vs := J1.xtop.fin.2.1, pt := J1.xtop.fin.2.2.1, sr := J1.xtop.fin.1
        cap := by rw [hSS.capAt hs]; exact hcap, rev := hSS.revOf hs
        no := fun x hx => by
          have hxs := ((hM.members x).1 hx).1
          rw [hSS.capV hxs, hSS.revOf hxs]; exact hno' x hx
        F := hFI1
        fr := fun w hw q vm h1 h2 hov => by
          have hws := ((hM.members w).1 hw).1
          rw [hSS.capV hws] at hov ⊢
          rw [(frame_range ptr .Large rt false mm fa fv false).1] at h1 h2
          exact hfr0' w hw q vm h1 h2 hov
        FR := hFR.of_caps (fun z hz => hSS.capV ((hM.members z).1 hz).1)
        VC := hVC.of_caps (fun z hz => hSS.capV ((hM.members z).1 hz).1) }
    have hbv : (core.num.U64.wrapping_add ptr a3).val = ptr.val + a3.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have hdiv : a4.val * 4096 ≤ 2 ^ 21 - a3.val := by
      calc a4.val * 4096 ≤ (2 ^ 21 - a3.val) / 4096 * 4096 :=
            Nat.mul_le_mul_right 4096 (by rw [← hmxv]; exact hc2')
        _ ≤ 2 ^ 21 - a3.val := Nat.div_mul_le_self _ _
    refine WP.spec_bind (insert_subframesJ (L := L) J1 hpp hidx hSub1 hal' hdp hr64 hfc (by rw [hbv]; omega)
      (by rw [hbv]; omega) ⟨hm1, hm3⟩ (by rw [hbv]; omega) (fun j h1 h2 => by
        rw [hSS.capAt ⟨dest, j, Or.inl ⟨rr, hdp, by omega⟩, rfl⟩]; exact hemp j h1 h2)
      (hDL.same hSS)) ?_
    rintro s2 ⟨σ', G', hmap, -, -, -, Ac2, Lst2, D2, J2⟩
    have hbase : (core.num.U64.wrapping_add ptr a3).bv = ptr.bv + a3.bv := core.num.U64.wrapping_add_bv_eq _ _
    have hrights : vmRightsOf m = Fl4Spec.maskVmRights (vmRightsOf rt) (Fl4Spec.dataToRights a5.bv) := by
      rw [hmv, rightsW_spec]; rfl
    have hperf : Fl4Spec.performDeriveSubframe (Z := Unit)
        ⟨(pp.bv, idx), ptr.bv + a3.bv, Fl4Spec.maskVmRights (vmRightsOf rt) (Fl4Spec.dataToRights a5.bv),
          (List.range' a2.val a4.val).map fun i => (dest.bv, Fl4Spec.natToCref rr i)⟩ =
        Fl4Spec.NonDet.mapMx (subIns (pp.bv, idx) (core.num.U64.wrapping_add ptr a3).bv (vmRightsOf m))
          (subList dest rr a2.val a4.val) := by
      unfold Fl4Spec.performDeriveSubframe subIns subList
      simp only [List.length_map, List.length_range', hbase, hrights]
    have hrun2 : (Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
        Fl4Spec.performDeriveSubframe (Z := Unit)
          ⟨(pp.bv, idx), ptr.bv + a3.bv, Fl4Spec.maskVmRights (vmRightsOf rt) (Fl4Spec.dataToRights a5.bv),
            (List.range' a2.val a4.val).map fun i => (dest.bv, Fl4Spec.natToCref rr i)⟩) σ =
        ({((), σ')}, False) := by
      rw [Fl4Proofs.P3.nd_bind_one hst1, hperf]; exact hmap
    exact (WP.spec_ok _).2 (Or.inr ⟨rfl, rfl, _, hE, σ', hrun2, G', Ac2, Lst2, D2, J2⟩)

end


/-! ## The frame's `DeriveSubframe` at `JAt` -/

/-- A decode with a single error outcome has no `DecOut`. -/
theorem not_decOut_errV {α : Type} {m : Fl4Spec.SEMonad Unit α} {σ : Fl4Spec.State Unit} {e : Fl4Spec.SyscallError}
    (h : m.run σ = ({(.error e, σ)}, False)) (inv : α) : ¬ DecOut m σ inv := by
  rintro ⟨h1, -⟩
  rw [h] at h1
  have := Set.mem_singleton_iff.1 h1
  simp at this

/-- A decode with a single outcome has it as its only `DecOut`. -/
theorem decOut_eqV {α : Type} {m : Fl4Spec.SEMonad Unit α} {σ : Fl4Spec.State Unit} {i inv : α}
    (h : m.run σ = ({(.ok i, σ)}, False)) (hd : DecOut m σ inv) : inv = i := by
  obtain ⟨h1, -⟩ := hd
  rw [h] at h1
  have := Set.mem_singleton_iff.1 h1
  simp only [Prod.mk.injEq, Except.ok.injEq] at this
  exact this.1

/-- **`DeriveSubframe`'s perform from the restart's state ends in the
spec's single outcome.** -/
theorem dsPerf_state {blk call don : Bool} {iv : Fl4Spec.Fl4SubframeInvocation} {σ1 σf : Fl4Spec.State Unit}
    (h : Fl4Spec.performDeriveSubframe (Z := Unit) iv σ1 = ({((), σf)}, False)) {y : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit}
    (hy : y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
      (.invokeArchObject (.deriveSubframe iv))).run σ1).1) : y.2 = σf := by
  obtain ⟨x, hx, e⟩ := mem_liftE_inv (m := Fl4Spec.archNoReturn (Fl4Spec.performDeriveSubframe (Z := Unit) iv)) hy
  unfold Fl4Spec.archNoReturn at hx
  rw [Fl4Proofs.P3.nd_bind_one h] at hx
  have hx' : x = ([], σf) := hx
  rw [e, hx']

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **What `DeriveSubframe`'s decode gives at `J`**: every spec outcome
after the restart and the invocation at `JAt`, the states unchanged on an
error. -/
def DsJPost (AR : A → Fl4Spec.Cr3 → Prop) (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation) (blk call don : Bool)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∀ inv, DecOut m σ inv → ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    ∀ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1,
      JAt (L := L) arI AR res.2.1 res.2.2 y.2) ∧
  ((∃ e, res.1 = .Err e) → res.2.1 = s ∧ res.2.2 = ar)

set_option maxHeartbeats 8000000 in
/-- **`DeriveSubframe` on a frame cap at `J`** (VsDecFrame's
`decode_invocation_frame_dsX` with `derive_subframeJ`). -/
theorem decode_invocation_frame_dsJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hVC : VsCapsW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl) (hl : lbl = fl4_abi.label.X86PageDeriveSubframe)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hno : sz = .Large → d = false → ∀ x ∈ Z.G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    syscall.decode_invocation st arI s ar lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk
      call don fp buf extra ⦃ res => DsJPost (L := L) arI AR (specDec fp slbl (args.map UScalar.bv) ci (pc.bv, idx)
        (.Frame p sz rt d m false asid va) excaps buffer) blk call don s ar σ res ⦄ := by
  subst hl
  have hSV := J.xtop.rel.2.1.2.1
  have hspec : specDec fp slbl (args.map UScalar.bv) ci (pc.bv, idx) (.Frame p sz rt d m false asid va) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.deriveSubframe
          (Fl4Spec.decodeDeriveSubframe (Z := Unit) (args.map UScalar.bv) (pc.bv, idx)
            (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps)) := by
    show Fl4Spec.NonDetE.liftME _ (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
      (frameACapG ⟨p, sz, rt, d, m, false, asid, va⟩) excaps) = _
    unfold Fl4Spec.fl4ArchDecodeInvocation frameACapG; dsimp only
    rw [if_pos (hlbl.dsr rfl)]
  rw [hspec]
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode_frame
  have n1 : ¬ fl4_abi.label.X86PageDeriveSubframe = fl4_abi.label.X86PageMap := by
    unfold fl4_abi.label.X86PageDeriveSubframe fl4_abi.label.X86PageMap; decide
  have n2 : ¬ fl4_abi.label.X86PageDeriveSubframe = fl4_abi.label.X86PageUnmap := by
    unfold fl4_abi.label.X86PageDeriveSubframe fl4_abi.label.X86PageUnmap; decide
  have n3 : ¬ fl4_abi.label.X86PageDeriveSubframe = fl4_abi.label.X86PageGetAddress := by
    unfold fl4_abi.label.X86PageDeriveSubframe fl4_abi.label.X86PageGetAddress; decide
  have n4 : ¬ fl4_abi.label.X86PageDeriveSubframe = fl4_abi.label.X86PageTestAndClearAccessed := by
    unfold fl4_abi.label.X86PageDeriveSubframe fl4_abi.label.X86PageTestAndClearAccessed; decide
  have n5 : ¬ fl4_abi.label.X86PageDeriveSubframe = fl4_abi.label.X86PageMapEPT := by
    unfold fl4_abi.label.X86PageDeriveSubframe fl4_abi.label.X86PageMapEPT; decide
  simp only [vspace.as_frame, bind_ok, n1, n2, n3, n4, n5, ↓reduceIte]
  rcases hex.hext with ⟨hex0, rfl⟩ | ⟨y, nc, nc', nsl, rest, hex0, hcy, hnr, rfl⟩
  · unfold vspace.derive_subframe
    rw [hct, hex0]
    simp only [bind_ok, error.truncated, WP.spec_ok]
    exact ⟨fun inv hd => absurd hd (not_decOut_errV (run_liftME_err (run_liftME_err
      (decodeSub_trunc (Or.inl rfl) _ _ σ))) inv), fun _ => ⟨rfl, rfl⟩⟩
  have hy := hex.hxs y hex0
  have hnv : CapValid Z.th nc := by
    have h := Vs.capValid_slot hSV hy; rwa [capV_of_capAt hcy] at h
  refine WP.spec_mono (derive_subframeJ arI J hni hpc hidx hcap hno hVC ct hct length buf args hlen hargs extra hex0
    hy hcy hnr hnv nsl rest) ?_
  rintro res (⟨e, e', h1, -, hD, h2, h2a⟩ | ⟨h1, h1a, iv, hD, σ', hrun, G', Ac', Lst', D', J'⟩)
  · exact ⟨fun inv hd => absurd hd (not_decOut_errV (run_liftME_err (run_liftME_err hD)) inv), fun _ => ⟨h2, h2a⟩⟩
  · refine ⟨fun inv hd σ1 hst y hy => ?_, fun ⟨e, he⟩ => by rw [h1] at he; cases he⟩
    have hinv := decOut_eqV (run_liftME_ok (run_liftME_ok hD)) hd
    subst hinv
    rw [Fl4Proofs.P3.nd_bind_one hst] at hrun
    rw [dsPerf_state hrun hy, h1a]
    exact ⟨_, H, Cs, Ac', Lst', D', J'⟩

set_option maxHeartbeats 4000000 in
/-- **A native frame cap at `JAt`, no per-op premise** (XTopJointVsReply's
`decode_invocation_frameJR` with `DeriveSubframe` by
`decode_invocation_frame_dsJ`: VsTopX's `decode_invocation_frame_capXR`'s
outcome at `JAt` from `DsJPost`, then VsThX's `DecOKMX.toXD`). -/
theorem decode_invocation_frameJS [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hVC : VsCapsW Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (hlGA : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageGetAddress →
      lbl = fl4_abi.label.X86PageGetAddress)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hno : sz = .Large → d = false → ∀ x ∈ Z.G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame p sz rt d m false asid va) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame p sz rt d m false asid va) (capV (L.mem s) x))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : JVsExtra (L := L) Z s extra excaps)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx))
      (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps
      buffer ct := by
  by_cases hga : lbl = fl4_abi.label.X86PageGetAddress
  · exact decode_invocation_frame_gaJ arI s ar σ J hni lbl slbl hlbl hga length buf ct hct _ blk call don fp extra
      _ ci _ excaps buffer
  by_cases htac : lbl = fl4_abi.label.X86PageTestAndClearAccessed
  · exact decode_invocation_frame_tacJ arI s ar σ J hni lbl slbl hlbl htac length buf ct hct hpc hidx hcap blk call
      don fp extra _ ci _ excaps buffer
  by_cases hds : lbl = fl4_abi.label.X86PageDeriveSubframe
  · have hX := J.xtop
    obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
    obtain ⟨-, hCR, hFI, hDR, hMO, -, -⟩ := hX.rel
    rcases decode_invocation_frame_capXR arI Z.th s ar σ Z.G hCR hFI J.ut hMO hA hX.fin.1 hX.fin.2.2.2.1
        hX.fin.2.2.2.2 hX.fin.2.1 hX.fin.2.2.1 hVC lbl slbl hlbl length buf ct hct hcur htcb J.kern.act
        (J.curRun.run hni) args hlen hargs hpc hidx hcap (Or.inl trivial) hno extra excaps hex.hext hex.hxs blk call
        don fp ci buffer hDR with ⟨-, -, h⟩ | ⟨hl, -⟩
    · have hJ : DecOKMX (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr (pc.bv, idx))
          (.Frame p sz rt d m false asid va) blk call don fp buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx)
          excaps buffer := by
        refine WP.spec_mono (WP.spec_and h (decode_invocation_frame_dsJ arI s ar σ J hni hVC lbl slbl hlbl hds
          length buf ct hct args hlen hargs hpc hidx hcap hno extra excaps hex blk call don fp ci buffer)) ?_
        rintro res ⟨hq, hP1, hP2⟩
        rcases hq with ⟨e, h1, h2, h3, -⟩ | ⟨inv, h1, σ1, h2, y, hy, h3, -⟩
        · refine Or.inl ⟨e, h1, h2, h3, ?_⟩
          obtain ⟨e1, e2⟩ := hP2 ⟨e, h1⟩
          rw [e1, e2]; exact ⟨Z, H, Cs, Ac, Lst, D, J⟩
        · exact Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, hP1 inv h1 σ1 h2 y hy⟩
      exact Or.inl (DecOKMX.toXD arI hJ
        (domFrame_frame arI Z.th s ar σ Z.G hCR hFI J.ut hMO hA hX.fin.1 hX.fin.2.2.2.1 hX.fin.2.1 hX.fin.2.2.1 hVC
          lbl slbl hlbl length buf ct hct hcur htcb J.kern.act (J.curRun.run hni) args hlen hargs hpc hidx hcap
          (Or.inl trivial) hno extra excaps hex.hext hex.hxs blk call don fp ci buffer hga htac)
        (okAll_specDec_frameCap fp slbl (args.map UScalar.bv) ci (pc.bv, idx) p sz rt d m false asid va excaps buffer
          (fun e => htac (hlbl.tac e)) (fun e => hga (hlGA e))) hDR (fun _ _ _ hx _ => hx))
    · exact hl.elim (fun e => absurd e hga) (fun e => absurd e htac)
  exact decode_invocation_frameJV arI s ar σ J hni hA hVC lbl slbl hlbl hlGA length buf ct hct args hlen hargs hpc
    hidx hcap hno extra excaps hex blk call don fp ci buffer
    (fun h => h.elim (fun e => absurd e hds) (fun h => h.elim (fun e => absurd e hga) (fun e => absurd e htac)))

end

end

end Fl4Proofs.P3
