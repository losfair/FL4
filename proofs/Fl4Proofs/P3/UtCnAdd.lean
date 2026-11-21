/-
P3 (DESIGN.md §9), untyped: **`XTopAt` across a retype that grows the typed
heap** (the no-reset retype of CNodes at `J`, handoff/utj.md "uttypes (line
ut29-)").

* `thk_grow`, `thT_grow`, `IntLayout.grow`, `AbsSlot.thMono`/`restrictMono`,
  `RegionFree.grow`, `NoStraddle.grow`, `Sched.SlotsApart.grow`,
  `JKern.grow`, `Sched.UtCapP3.grow`: `JAtZ`'s typed-heap fields at `th'`
  from `th`'s and facts about the window.
* `JAtZ.add_frameT`: `JAtZ.add_frame` with `thk`, `bound`, `intL` given at
  the grown heap.
* `XTopAt.addStepT`: `XTopAt.addStepW` with the typed heap grown to `th'`
  (`ThX`: the window's new CNodes or TCBs) and FL4 writing the window's words
  (the new objects' zeroed slots); the window's words are none the relations
  read (`¬ OObj`), none of the VSpace's or `th`'s objects (`¬ VObj`) and miss
  the kernel-state block, so the placement facts move to `th'`
  (`TopPlaced.grow`, `IpcApart.grow`, `ScApart.grow`, `CurOK.grow`).
-/
import Fl4Proofs.P3.UtCnGrow
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P1

noncomputable section

section GrowJ
variable {th th' : TypedHeap} {A k w n us : Nat}

/-- **`JAtZ.thk` at the grown heap**: the new objects are CNodes or TCBs. -/
theorem thk_grow (hT : ThX th th' A k w n us) (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k)
    (h : ∀ q kd, th q = some kd → kd = .tcb ∨ ∃ r, kd = .cnode r) :
    ∀ q kd, th' q = some kd → kd = .tcb ∨ ∃ r, kd = .cnode r := by
  intro q kd hq
  rcases hT.cases hks hq with h1 | ⟨-, -, h2⟩
  · exact h q kd h1
  · unfold thKindN at h2
    split_ifs at h2
    · cases h2; exact Or.inl rfl
    · cases h2; exact Or.inr ⟨_, rfl⟩

/-- **No new TCB** when the retype makes no TCBs (`n ≠ 1`). -/
theorem thT_grow (hT : ThX th th' A k w n us) (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k) (hn : n ≠ 1)
    {t : U64} (h : th' t = some .tcb) : th t = some .tcb := by
  rcases hT.cases hks h with h1 | ⟨-, -, h2⟩
  · exact h1
  · unfold thKindN at h2; split_ifs at h2 <;> simp_all

/-- **`IntLayout` at the grown heap**: the IRQ state words lie in the
kernel-state block, which the window misses; the IRQ node's CNodes stay. -/
theorem IntLayout.grow {kb : U64} (h : IntLayout th kb) (hT : ThX th th' A k w n us)
    (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k) (hk0 : 0 < k)
    (hpos : ∀ q kd, th q = some kd → 0 < objSize kd)
    (hWk : A + w * k ≤ kb.val ∨ kb.val + 13568 ≤ A) : IntLayout th' kb := by
  refine ⟨h.fit, h.align, fun i hi => OutsideObjects.grow hT hks (h.st_out i hi) ?_,
    fun i hi => hT.mono hk0 hpos (h.node i hi)⟩
  rw [irqStA_val h.fit hi]; omega

/-- `th`'s abstract slots stay. -/
theorem AbsSlot.thMono (hT : ThX th th' A k w n us) (hk0 : 0 < k) (hpos : ∀ q kd, th q = some kd → 0 < objSize kd)
    {sl : Fl4Spec.CslotPtr} (h : AbsSlot th sl) : AbsSlot th' sl := by
  obtain ⟨p, hp, h1 | ⟨h1, h2⟩⟩ := h
  · exact ⟨p, hp, Or.inl (hT.mono hk0 hpos h1)⟩
  · exact ⟨p, hp, Or.inr ⟨hT.mono hk0 hpos h1, h2⟩⟩

/-- `RegionFree` at the grown heap, the window's objects off the region. -/
theorem RegionFree.grow {lo hi : Nat} (h : RegionFree th lo hi) (hT : ThX th th' A k w n us)
    (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k)
    (hW : ∀ (q : U64) kd, A ≤ q.val → q.val + objSize kd ≤ A + w * k → q.val + objSize kd ≤ lo ∨ hi ≤ q.val) :
    RegionFree th' lo hi := by
  intro q kd hq
  rcases hT.cases hks hq with h1 | ⟨g1, g2, -⟩
  · exact h q kd h1
  · exact hW q kd g1 g2

/-- `NoStraddle` at the grown heap, no window object straddling the region. -/
theorem NoStraddle.grow {lo hi : Nat} (h : NoStraddle th lo hi) (hT : ThX th th' A k w n us)
    (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k)
    (hW : ∀ (q : U64) kd, A ≤ q.val → q.val + objSize kd ≤ A + w * k →
      (lo ≤ q.val ∧ q.val + objSize kd ≤ hi) ∨ q.val + objSize kd ≤ lo ∨ hi ≤ q.val) :
    NoStraddle th' lo hi := by
  intro q kd hq
  rcases hT.cases hks hq with h1 | ⟨g1, g2, -⟩
  · exact h q kd h1
  · exact hW q kd g1 g2

/-- The restricted heap's abstract slots stay. -/
theorem AbsSlot.restrictMono (hT : ThX th th' A k w n us) (hk0 : 0 < k)
    (hpos : ∀ q kd, th q = some kd → 0 < objSize kd) {lo hi : Nat} {sl : Fl4Spec.CslotPtr}
    (h : AbsSlot (restrictTh th lo hi) sl) : AbsSlot (restrictTh th' lo hi) sl := by
  have hm : ∀ {q : U64} {kd : ObjKind}, restrictTh th lo hi q = some kd → restrictTh th' lo hi q = some kd := by
    intro q kd hq
    unfold restrictTh at hq ⊢
    by_cases hc : lo ≤ q.val ∧ q.val < hi
    · rw [if_pos hc] at hq; cases hq
    · rw [if_neg hc] at hq; rw [if_neg hc]; exact hT.mono hk0 hpos hq
  obtain ⟨p, hp, h1 | ⟨h1, h2⟩⟩ := h
  · exact ⟨p, hp, Or.inl (hm h1)⟩
  · exact ⟨p, hp, Or.inr ⟨hm h1, h2⟩⟩

end GrowJ

section GrowS
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th th' : TypedHeap} {A k w n us : Nat}

/-- **`SlotsApart` at the grown heap**: `th`'s slots as before, the window's
slots apart by the window's facts. -/
theorem Sched.SlotsApart.grow {T N C R : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (h : Sched.SlotsApart (st := st) th T N C R c s σ) (hT : ThX th th' A k w n us)
    (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k) (hP' : Placed th')
    (hW : ∀ a : U64, A ≤ a.val → a.val + 32 ≤ A + w * k →
      (∀ t ∈ T, a.val + 32 ≤ t.val + 256 ∨ t.val + 4096 ≤ a.val) ∧
      (a.val + 32 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ a.val) ∧
      (∀ n ∈ N, a.val + 32 ≤ n.val ∨ n.val + 40 ≤ a.val) ∧
      (∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) →
        a.val + 32 ≤ sc.val ∨ sc.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ a.val) ∧
      (∀ r ∈ R, a.val + 32 ≤ r.val ∨ r.val + 32 ≤ a.val)) :
    Sched.SlotsApart (st := st) th' T N C R c s σ := fun a ha =>
  (IsSlot.thX hT hks hP' ha).elim (h a) (fun g => hW a g.1 g.2)

/-- **`JKern` at the grown heap**: `th`'s objects stay; the scheduler-action
word and core 0's debug-list head word lie outside the window. -/
theorem JKern.grow {H : P1.Heap} {Cs D : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (h : JKern (L := L) H Cs D th s σ) (hT : ThX th th' A k w n us)
    (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k) (hk0 : 0 < k)
    (hpos : ∀ q kd, th q = some kd → 0 < objSize kd) (hP' : Placed th')
    (hact : ¬ (A ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < A + w * k))
    (hdw : ¬ (A ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < A + w * k)) :
    JKern (L := L) H Cs D th' s σ := by
  refine { h with
    orig := fun sl hs => AbsSlot.thMono hT hk0 hpos (h.orig sl hs)
    curT := hT.mono hk0 hpos h.curT
    act := OutsideObjects.grow hT hks h.act hact
    dwObj := fun a ha hin => ?_
    head := h.head.imp id fun g => ⟨hT.mono hk0 hpos g.1, g.2⟩ }
  rcases IsSlot.thX hT hks hP' ha with ho | ⟨g1, g2⟩
  · exact h.dwObj a ho hin
  · exact hdw ⟨by omega, by omega⟩

/-- **An untyped cap's facts at the grown heap**: the window's objects off the
cap's free part and not straddling its region; the reset's slots by
monotonicity. -/
theorem Sched.UtCapP3.grow {A' : Type} {arI : machine.Arch A'} {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} {p sb fi : U64} (U : Sched.UtCapP3 (L := L) arI th s σ G sl p sb fi)
    (hT : ThX th th' A k w n us) (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k) (hk0 : 0 < k)
    (hpos : ∀ q kd, th q = some kd → 0 < objSize kd)
    (hWf : ∀ (q : U64) kd, A ≤ q.val → q.val + objSize kd ≤ A + w * k →
      q.val + objSize kd ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ q.val)
    (hWs : ∀ (q : U64) kd, A ≤ q.val → q.val + objSize kd ≤ A + w * k →
      (p.val ≤ q.val ∧ q.val + objSize kd ≤ p.val + 2 ^ sb.val) ∨ q.val + objSize kd ≤ p.val ∨
        p.val + 2 ^ sb.val ≤ q.val) :
    Sched.UtCapP3 (L := L) arI th' s σ G sl p sb fi :=
  { U with
    free := RegionFree.grow U.free hT hks hWf
    nostr := NoStraddle.grow U.nostr hT hks hWs
    rst := fun h1 h2 h3 => ⟨fun sl' ho => AbsSlot.restrictMono hT hk0 hpos ((U.rst h1 h2 h3).1 sl' ho),
      (U.rst h1 h2 h3).2⟩ }

end GrowS

section Add
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {σ σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}

set_option maxHeartbeats 4000000 in
/-- **`XTopAt` across fresh objects, a CNode-only step, writes to a window
and the typed heap grown over it** (`XTopAt.addStepW` at `th'`). -/
theorem XTopAt.addStepT {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a : A}
    {σB : Fl4Spec.State Unit} {th' : TypedHeap} {Aw k w n us : Nat}
    (hX : XTopAt (L := L) AR Z s a σ) (hT : ThX Z.th th' Aw k w n us)
    (hks : ∀ kd, thKindN n us = some kd → objSize kd ≤ k) (hk0 : 0 < k) (hP' : Placed th')
    (hpos : ∀ q kd, Z.th q = some kd → 0 < objSize kd)
    (hw : P1.WritesIn st s s' (fun b => Sched.SlotWd Z.th b ∨ (Aw ≤ b.val ∧ b.val < Aw + w * k)))
    (hWin : ∀ b : U64, Aw ≤ b.val → b.val < Aw + w * k → ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧
      ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b)
    (hWk : Aw + w * k ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ Aw)
    (hA : Sched.SpecAdd σ σB W o) (ho : ∀ p, W p → ∀ x n, o p ≠ .schedContext x n)
    (hcn : CnK σB σ') (hkc : KeepC σB σ') {G' : MdbGhost} (hCR : CRel th' (L.mem s') σ' G')
    (hFI : FinInv th' (L.mem s') σ' G') (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hTS : ∀ t, Z.th t = some .tcb → ∀ p asid, capAt (L.mem s') (slotOf t 1) = ok (.Pml4 p true asid) →
      capAt (L.mem s) (slotOf t 1) = ok (.Pml4 p true asid)) :
    XTopAt (L := L) AR { Z with th := th', G := G' } s' a σ' := by
  obtain ⟨⟨hS, hR, hPt, hPI, hCO⟩, ⟨hPl, -, -, hD, -, hIA, hSA⟩, -, hE⟩ := hX
  obtain ⟨hO, hms, har⟩ := ostep_of_cnk hcn hkc
  have hP := hS.2
  have hk : L.ksb s' = L.ksb s := hw.1
  have hSB := TopSR.specAdd hS hA ho
  have hz := hA.szKeep ho
  have hkW : ∀ b, P1.Aligned b → ¬ Sched.SlotWd Z.th b → ¬ (Aw ≤ b.val ∧ b.val < Aw + w * k) →
      L.mem s' b = L.mem s b :=
    fun b hb h1 h2 => hw.2.2 b hb (fun h => h.elim h1 h2)
  have hS' := TopSR.step (Rw := fun b => Aw ≤ b.val ∧ b.val < Aw + w * k) (Rg := fun _ => False) hSB hw.1 hw.2.1
    (fun b hb hv hr => hkW b hb (fun h => hv (slotWd_vobj hPl h)) hr)
    (fun b hb ho' => (hWin b hb.1 hb.2).1 (OObj.of_szKeep hz ho')) hO (fun _ h => h.elim)
    (fun wp _ => by rw [hms]) (fun h => by rw [har]; exact h)
  have hSz : Sched.SzKeep σ σ' := fun p x n hp => by
    obtain ⟨x1, h1⟩ := SzKeep.of_keepC hkc p x n hp
    exact hz p x1 n h1
  have har' : σ'.archState = σ.archState := har.trans hA.arch
  have hvw : ∀ b, VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hkW b (hP.vo b hb).1 (fun h => slotWd_inObj hPl h (hP.vo b hb))
      (fun h => (hWin b h.1 h.2).2 (vsWrite_vobj hP.vs hb))
  have hcur : σ'.curThread = σ.curThread := hO.ct.trans hA.f.2.2.1
  have hkeep : ∀ q k, σ.kheap q = some k → (∀ r cs, k ≠ .cnode r cs) → σ'.kheap q = σ.kheap q := by
    intro q k hq hnc
    rcases hkc q with e | ⟨r, cs, cs', h1, -⟩
    · rw [e, hA.kold hq, hq]
    · rw [hA.kold hq] at h1; cases h1; exact absurd rfl (hnc r cs)
  have hab : Fl4Spec.AbstractState.domainList σ'.toAbstractState = σ.domainList ∧
      Fl4Spec.AbstractState.domainStartIndex σ'.toAbstractState = σ.domainStartIndex := by
    refine ⟨?_, ?_⟩
    · have e1 := congrArg Fl4Spec.AbstractState.domainList hcn.1
      have e2 := congrArg Fl4Spec.AbstractState.domainList hA.abs
      exact e1.trans e2
    · have e1 := congrArg Fl4Spec.AbstractState.domainStartIndex hcn.1
      have e2 := congrArg Fl4Spec.AbstractState.domainStartIndex hA.abs
      exact e1.trans e2
  -- the window's words at the state after (the base kept, SC sizes kept)
  have hWo' : ∀ b : U64, Aw ≤ b.val → b.val < Aw + w * k → ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' b := by
    intro b h1 h2 hob
    refine (hWin b h1 h2).1 (OObj.of_szKeep hSz ?_)
    exact OObj.of_same (σ := σ') (σ' := σ') hk rfl hob
  have hWv' : ∀ b : U64, Aw ≤ b.val → b.val < Aw + w * k → ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s') b := by
    intro b h1 h2; rw [hk]; exact (hWin b h1 h2).2
  have hWk' : Aw + w * k ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ Aw := by rw [hk]; exact hWk
  refine ⟨⟨⟨hS'.1, TopPlaced.grow hS'.2 hT hks hP' hWo' hWv' hWk'⟩, ?_, ?_, fun q hq lo hl => ?_, ?_⟩,
    ⟨hP', hCR, hFI, ?_, by rw [hk]; exact hMO,
    IpcApart.grow (σ := σ') (by rw [hk]; exact hIA) hT hks hP' hWo' hWk', ScApart.grow (s := s') (hSA.mono hSz) hT hks hP' hWo'⟩,
    IpcRel.of hS'.1.2.2.1 hS'.1.2.1 (sched_sc hS'.1.1), hE.mono hk hSz⟩
  · rw [hk]
    refine hR.frame hvw (by rw [har']) fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    exact hkeep _ _ hf (fun r cs e => by cases e)
  · refine hPt.frame (fun b hb => hkW b (hP.po b hb).1 (fun h => slotWd_inObj hPl h (hP.po b hb)) (fun h => ?_))
      fun q hq => ?_
    · obtain ⟨q, hq, i, hi, e⟩ := hb
      exact (hWin b h.1 h.2).2 (e ▸ table_vobj hP.pt hq hi _)
    rcases hq with hq | hq | hq | hq
    · obtain ⟨g, hg, -⟩ := hPt.l4 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l3 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l2 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
    · obtain ⟨g, hg, -⟩ := hPt.l1 q hq; exact hkeep _ _ hg (fun r cs e => by cases e)
  · have hwv : VsWrite Z.P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hwv]; exact hPI q hq lo hl
  · obtain ⟨t, h1, h2, h3⟩ := hCO
    exact CurOK.grow ⟨t, h1.trans hcur.symm, h2, fun p asid hc => h3 p asid (hTS t h2 p asid hc)⟩ hT hk0 hpos
  · rw [hk]
    refine hD.frame (fun o ho => ?_) hab.1 hab.2
    have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    refine hkW _ (by unfold P1.Aligned; rw [hv]; have := hP.vs.ksb_al; omega) (fun h => ?_) (fun h => ?_)
    · obtain ⟨y, hy, g1, g2⟩ := slotWd_range hPl h
      exact hIA.ks _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) y hy ⟨g1, g2⟩
    · rcases hWk with h' | h' <;> rw [hv] at h <;> omega

end Add


/-! ## `JAtZ` at a grown typed heap -/

section Frame
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 1000000 in
/-- **`JAtZ` at enlarged sets, a grown heap `H'` and a grown typed heap**
(XTopJointUtEp's `JAtZ.add_frame` without `Z'.th = Z.th`: the fields that
read the typed heap and are not re-established by `JCs`/`JRest` (`thk`,
`bound`, `intL`) given at `Z'.th`). -/
theorem JAtZ.add_frameT {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {Z' : XSets} {H' : P1.Heap} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64}
    (hC : Z'.C = Z.C) (hB : Z'.B = Z.B) (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR Z' s' a' σ') (hCs : JCs (L := L) Z' s' σ') (R : JRest (L := L) arI Z' H' Cs Ac' Lst' D' s' σ')
    (hKs : KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s')) (hthT : ∀ t, Z'.th t = some .tcb → t ∈ Z'.T)
    (hthk : ∀ q k, Z'.th q = some k → k = .tcb ∨ ∃ r, k = .cnode r) (hbound : DelBound Z'.th)
    (hintL : IntLayout Z'.th (L.ksb s'))
    (hIp : IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B)
    (hnk : ∀ n ∈ Z'.N, n.val + 40 ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ n.val)
    (hcov : Sched.SpecCover H' σ') (hobj : Sched.ObjCover Z'.N Z'.T Z'.E Z'.R Z'.C σ')
    (hzH : (∀ t ∈ Z'.T, H' t = some .tcb) ∧ (∀ e ∈ Z'.E, H' e = some .ep) ∧ (∀ r ∈ Z'.R, H' r = some .reply) ∧
      (∀ n ∈ Z'.N, H' n = some .ntfn))
    (hset : (∀ e, H' e = some .ep → e ∈ Z'.E) ∧ (∀ n, H' n = some .ntfn → n ∈ Z'.N) ∧
      (∀ r, H' r = some .reply → r ∈ Z'.R))
    (hscC : ∀ c z, H' c = some (.sc z) → c ∈ Z'.C)
    (hvc : Vs.VsSlotsW Z'.th Z'.P Z'.L4 Z'.L3 Z'.L2 Z'.L1 (L.mem s'))
    (hbf : JBuf (L := L) Z' s' σ') (hext : JExt (L := L) Z'.th s')
    (hlv : LiveDN (L := L) Z'.th H' Cs Z'.G s' σ') (hzD : ∀ p ∈ ZTcb (L := L) Z'.th s', p ∈ D') :
    JAtZ (L := L) arI AR Z' H' Cs Ac' Lst' D' s' a' σ' := by
  have hTe : Z'.T = P1.Heap.tcbs H' := by
    obtain ⟨Tr, Cq, hJ⟩ := R.jpl
    exact Set.ext fun t => ⟨fun h => hzH.1 t h, fun h => hthT t ((hJ.tcb t).2 h)⟩
  have hRe : Z'.R = P1.Heap.replies H' := Set.ext fun r => ⟨fun h => hzH.2.2.1 r h, fun h => hset.2.2 r h⟩
  have hc0 : ∀ q ∈ Z'.C, q ≠ 0#u64 := by rw [hC]; exact J.c0
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX hTe hobj R.blk hset.2.1 R.jpl hc0
  exact ⟨hX, R.call, R.rfree, R.rrecv, R.yld, R.mcp, R.buf, hKs, hthT, hthk, hIp, R.rp, R.apart,
    hnk, fun wp hw c hc => by
      simp only [P1.LawfulStore.nodeBase, hks]; rw [hB] at hw; exact J.nodeB wp hw c hc,
    R.jpl, hcov, hobj, hzH, hCs.sfree, hset, hscC, R.jcov,
    R.kern, hCs.del, hCs.ut, hbound, hCs.finM, R.utc, R.nsc, R.inv, R.cur, R.own, R.off, R.act,
    hc0, R.bsa, schedValid_rebuild hX hTe hRe hobj R.blk hset.1 hset.2.1 R.call R.yld hc0 R.inv hsl, R.isorted, hsl,
    R.curRun, R.blk, hintL, hvc, hbf.1, hbf.2.1, hbf.2.2, hext, hlv, hzD⟩

end Frame

end

end Fl4Proofs.P3
