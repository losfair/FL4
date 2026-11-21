/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr6): **the deletion loop at
`MachPlat`**: the loop invariant `WJL` with `MR ∧ ValidMachineTime ∧
ValidIrqMasks` beside it (`WMR MR W`), each step of the loop re-proved with
it, the preemption point by mr3's `ppJDMV` (no `PPPlat`).

* `MRV MR a σ` := `MR a σ.ms ∧ ValidMachineTime σ ∧ ValidIrqMasks σ` [J]
  (l4v shared machine_state, valid_machine_time, valid_irq_masks), carried;
  `WMR MR W` := `W ∧ MRV`. `mrv_keep`: a spec step keeping MachFieldFamT's
  `msFT` (the four machine fields `MR` reads, the interrupt table and the
  current time) keeps `MRV` at the same arch state.
* Generic lifts (any `W`): the zombie write (`mtk_setCap`), the swap
  (`mtk_capSwapForDelete'`), the empty (`mtk_emptySlotNull`), the trivial
  readiness, the finalisation (`FinObjHypWRcZ.mrv`: FL4 by MachKeepD's
  `MKD.objects_finalise_cap` under `MRKeepD` [P], spec by `mtk_finaliseCap`),
  and `post_cap_deletion` (`PostDelHypW.mrv` from `post_mrv`).
* `post_mrv`: a cleanup cap's `post_cap_deletion` keeps `MRV`: an IRQ
  handler by `MachPlat.mask` (FL4's `mask_irq irq true` is the spec's
  `maskInterrupt true`, the masks of both sides updated at the same line,
  `BitVec.ofNat_toNat`) and `MRKeepD.irq_free`; the spec's `setIrqState
  irqInactive` (`setIrqInactive_out`: its only outcome is `setIrqSt`) sets
  the line inactive AND masked, so `ValidIrqMasks` holds after (l4v
  deleting_irq_handler_valid_irq_masks / set_irq_state_valid_irq_masks); an
  IO port by `mtk_archPostCapDeletion'` (FL4's arch state kept).
* `jPreemptHypLM`: XTopJointWJLPP's `jPreemptHypL` with `ppJDMV` for `ppJD`
  (`MachPlat` + `PPPlatA` for `PPPlat`); after a preemption `WJPM` := `WJP ∧
  JAtPreMV` (what mr3's `hPre_ofZQIM` eats).
* `delHypsJLM`: `DelHypsWRZ` at `WMR MR WJL` / `WJPM` (delHypsJL without
  `PPPlat`); `JDelHypLM`, `JDelParts.jDelHypLM`: the whole deletion of one cap
  (DelFull's `delHyp_fullWRZ`) at `MachPlat`.
* `modelArch_mrKeepD`: non-vacuity of `MRKeepD`.
-/
import Fl4Proofs.P3.XTopJointWJLDel
import Fl4Proofs.P3.XTopJointMRHole2
import Fl4Proofs.P3.MachFieldFamT
import Fl4Proofs.P3.MachKeepD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- **The model platform satisfies `MRKeepD`** for every predicate. -/
theorem modelArch_mrKeepD {C : Type} (AR : Fl4Spec.MachineState → C → Prop) : MRKeepD modelArch AR where
  set_deadline _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  send_reschedule _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  remote_stall _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_flush _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_release _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_sanitise _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_reload _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  vcpu_barrier _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  invalidate_ept _ _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  invalidate_page _ _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  invalidate_asid _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  invalidate_page_structures _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  set_vspace _ _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  dma_frame _ _ _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  irq_free _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h

/-- **The spec's `setIrqState irqInactive` has the one outcome `setIrqSt`.** -/
theorem setIrqInactive_out {irq : Fl4Spec.Irq} {σ : Fl4Spec.State Unit} {x : Unit × Fl4Spec.State Unit}
    (hx : x ∈ (Fl4Spec.setIrqState (Z := Unit) .irqInactive irq σ).1) : x.2 = setIrqSt .irqInactive irq σ := by
  unfold Fl4Spec.setIrqState at hx
  obtain ⟨⟨u0, σ1⟩, h0, hx⟩ := hx
  have e0 := Set.mem_singleton_iff.1 h0
  simp only [Prod.mk.injEq] at e0
  obtain ⟨-, rfl⟩ := e0
  unfold Fl4Spec.doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 h1] at h2
  obtain ⟨hm2, e2⟩ := h2
  simp only [Prod.mk.injEq] at e2 h3
  obtain ⟨-, rfl⟩ := e2
  rw [Set.mem_singleton_iff.1 h3] at hx
  rw [Set.mem_singleton_iff.1 hx]
  unfold Fl4Spec.maskInterrupt at hm2
  have e2 := Set.mem_singleton_iff.1 hm2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨-, rfl⟩ := e2
  rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {th : TypedHeap}

/-- **`MR`, `ValidMachineTime` and `ValidIrqMasks`** [J] (module docstring). -/
def MRV (MR : A → Fl4Spec.MachineState → Prop) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  MR a σ.machineState ∧ ValidMachineTime σ ∧ ValidIrqMasks σ

/-- **A loop invariant with `MRV` beside it.** -/
abbrev WMR (MR : A → Fl4Spec.MachineState → Prop) (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) :
    S → A → Fl4Spec.State Unit → MdbGhost → Prop :=
  fun s a σ G => W s a σ G ∧ MRV MR a σ

/-- **A spec step keeping `msFT` keeps `MRV`.** -/
theorem mrv_keep {arI : machine.Arch A} (hM : MachPlat arI MR) {a : A} {σ σ' : Fl4Spec.State Unit}
    (h : MRV MR a σ) (e : MachT.msFT σ' = MachT.msFT σ) : MRV MR a σ' := by
  unfold MRV ValidMachineTime ValidIrqMasks at *
  obtain ⟨hR, ⟨hV1, hV2⟩, hI⟩ := h
  simp only [MachT.msFT, MachF.msF, Prod.mk.injEq] at e
  obtain ⟨⟨e1, e2, e3, e4, e5⟩, e6⟩ := e
  refine ⟨hM.frame a _ _ hR e1 e2 e3 e4, ⟨?_, ?_⟩, fun i hi => ?_⟩
  · rw [e6, e4]; exact hV1
  · rw [e4]; exact hV2
  · rw [e1]; exact hI i (by rw [← e5]; exact hi)

variable {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}
  {Rd Rz : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop}

theorem ZombieHypWZ.mrv {arI : machine.Arch A} (hM : MachPlat arI MR) (h : ZombieHypWZ (L := L) (A := A) W Rz th) :
    ZombieHypWZ (L := L) (A := A) (WMR MR W) Rz th := by
  intro s s' a σ σ' G sl p zt n hW hRz hcd hZF hD1 hD2 hF hsc hA hxn hz hal hoth hmS
  exact ⟨h s s' a σ σ' G sl p zt n hW.1 hRz hcd hZF hD1 hD2 hF hsc hA hxn hz hal hoth hmS,
    mrv_keep hM hW.2 (MachT.mtk_setCap _ _ σ ((), σ') (mem_of_single hsc))⟩

theorem SwapHypWZ.mrv {arI : machine.Arch A} (hM : MachPlat arI MR) (h : SwapHypWZ (L := L) (A := A) W th) :
    SwapHypWZ (L := L) (A := A) (WMR MR W) th := by
  intro s s' a σ σ' G G' sl p zt n hW hn1 hD1 hD2 hF hsw hA hz hpx hG' hcap hmS
  exact ⟨h s s' a σ σ' G G' sl p zt n hW.1 hn1 hD1 hD2 hF hsw hA hz hpx hG' hcap hmS,
    mrv_keep hM hW.2 (MachT.mtk_capSwapForDelete' _ _ σ ((), σ') (mem_of_single hsw))⟩

theorem EmptyHypWR.mrv {arI : machine.Arch A} (hM : MachPlat arI MR) (h : EmptyHypWR (L := L) W Rd th) :
    EmptyHypWR (L := L) (WMR MR W) Rd th := by
  intro s s' a σ σ' G G' sl hW hRd hD1 hD2 hF hes hA hxn hx0 hoth hmS
  exact ⟨h s s' a σ σ' G G' sl hW.1 hRd hD1 hD2 hF hes hA hxn hx0 hoth hmS,
    mrv_keep hM hW.2 (MachT.mtk_emptySlotNull _ σ ((), σ') hes)⟩

theorem RdTrivHyp.mrv (h : RdTrivHyp (L := L) W Rd th) : RdTrivHyp (L := L) (WMR MR W) Rd th :=
  fun s a σ G sl c hDS hW => h s a σ G sl c hDS hW.1

theorem FinObjHypWRcZ.mrv (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hT : P0.ArchTotal arI)
    (h : FinObjHypWRcZ (L := L) arI W Rd Rz th) : FinObjHypWRcZ (L := L) arI (WMR MR W) Rd Rz th := by
  intro s a σ G sl c hDS hW hA hc hk ht
  refine WP.spec_mono (WP.spec_and (h s a σ G sl c hDS hW.1 hA hc hk ht)
    (MKD.objects_finalise_cap L.total hT hKD hW.2.1)) ?_
  rintro r ⟨⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, h9, h10, h11⟩, hR⟩
  exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8,
    ⟨h9, mrv_keep hM ⟨hR, hW.2.2⟩ (MachT.mtk_finaliseCap _ _ σ _ h4)⟩, h10, h11⟩

/-- **A cleanup cap's `post_cap_deletion` keeps `MRV`** (module docstring). -/
theorem post_mrv (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {cl : capability.Cap} (h : MRV MR a σ) (hcl : CleanCap cl) (hn : cl ≠ .Null) (hw : CapWf cl) :
    objects.post_cap_deletion st arI s a cl ⦃ r => ∀ σ',
      ((), σ') ∈ (Fl4Spec.postCapDeletion (Z := Unit) (absCap cl) σ).1 → MRV MR r.2 σ' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  cases cl <;> simp only [CleanCap] at hcl
  · exact absurd rfl hn
  · rename_i irq
    have hirq : irq.val < 128 := hw
    obtain ⟨a1, hm, hR1⟩ := spec_exists (hM.mask a irq (decide (interrupt.IRQ_INACTIVE = interrupt.IRQ_INACTIVE))
      σ.machineState h.1 (by omega))
    obtain ⟨a2, hf, hR2⟩ := spec_exists (hKD.irq_free a1 irq _ hR1)
    unfold objects.post_cap_deletion
    simp only
    rw [deleted_irq_handler_eq arI s a irq hm hf, WP.spec_ok]
    intro σ' hσ'
    have e : σ' = setIrqSt .irqInactive (BitVec.ofNat 8 irq.val) σ :=
      setIrqInactive_out (irq := BitVec.ofNat 8 irq.val) (x := ((), σ')) hσ'
    subst e
    have hd : decide (interrupt.IRQ_INACTIVE = interrupt.IRQ_INACTIVE) = true := by simp
    rw [hd] at hR2
    have e8 : BitVec.ofNat 8 irq.val = irq.bv.setWidth 8 := BitVec.ofNat_toNat 8 irq.bv
    unfold MRV at h ⊢
    obtain ⟨hR, hV, hI⟩ := h
    refine ⟨hM.frame a2 _ _ hR2 ?_ rfl rfl rfl, hV, ?_⟩
    · show Function.update σ.machineState.irqMasks (BitVec.ofNat 8 irq.val)
          (decide (Fl4Spec.IrqState.irqInactive = .irqInactive)) =
        Function.update σ.machineState.irqMasks (irq.bv.setWidth 8) true
      rw [e8]; simp
    · unfold ValidIrqMasks at hI ⊢
      intro i hi
      show Function.update σ.machineState.irqMasks (BitVec.ofNat 8 irq.val)
          (decide (Fl4Spec.IrqState.irqInactive = .irqInactive)) i = true
      have hi' : Function.update σ.interruptStates (BitVec.ofNat 8 irq.val) Fl4Spec.IrqState.irqInactive i =
          .irqInactive := hi
      by_cases ei : i = BitVec.ofNat 8 irq.val
      · subst ei; simp
      · rw [Function.update_of_ne ei] at hi' ⊢
        exact hI i hi'
  · rename_i f l o
    unfold objects.post_cap_deletion
    simp only
    refine WP.spec_bind (P0.ioport.free_ioports.p0 st s f l hS) fun s1 _ => ?_
    rw [WP.spec_ok]
    intro σ' hσ'
    exact mrv_keep hM h (MachT.mtk_archPostCapDeletion'
      (.ioPortCap (BitVec.ofNat 16 f.val) (BitVec.ofNat 16 l.val)) σ _ hσ')

theorem PostDelHypW.mrv (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (h : PostDelHypW (L := L) arI W th) :
    PostDelHypW (L := L) arI (WMR MR W) th := by
  intro s a σ G cl hDS hW h1 h2 h3
  refine WP.spec_mono (WP.spec_and (h s a σ G cl hDS hW.1 h1 h2 h3) (post_mrv arI hM hKD hW.2 h1 h2 h3)) ?_
  rintro r ⟨⟨hSS, σ', hm, hCR, hW'⟩, hmv⟩
  exact ⟨hSS, σ', hm, hCR, hW', hmv σ' hm⟩

/-- **The deletion's state after a preemption at `MachPlat`**: `WJP` and
`JAtPreMV`. -/
def WJPM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (kb : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop :=
  WJP (L := L) arI AR Z H Cs kb s a σ G ∧ JAtPreMV (L := L) arI AR MR s a σ

set_option maxHeartbeats 4000000 in
/-- **The preemption point keeps `WMR MR WJL`** (module docstring). -/
theorem jPreemptHypLM (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlat arI MR) (hPA : PPPlatA arI AR) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    PPHypDW (L := L) arI (WMR MR (WJL (L := L) arI AR Z H Cs kb)) (WJPM (L := L) arI AR MR Z H Cs kb) th := by
  intro s a σ G hDS ⟨⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩, hR, hV, hVI⟩
  subst hth
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  obtain ⟨r0, hr0, hP0⟩ := J0.ppJDMV hAK hA hnd hM hPA hR hV hVI hns hp0
  have hPS : sched.preemption_point st arI s a ⦃ r => ∃ σ',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 ∧
          (∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac' Lst'
            (D ∪ ZTcb (L := L) Z.th s) r.2.1 r.2.2 σ') ∧ PPR0 σ' ∧ Vs.NoSwitch σ') ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 ∧
          JAtPreMV (L := L) arI AR MR r.2.1 r.2.2 σ')) ∧
      XTopAt (L := L) AR (Z.mv G V) r.2.1 r.2.2 σ' ∧
      MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ∧ ValidIrqMasks σ' ⦄ := by
    rw [hr0, WP.spec_ok]; exact hP0
  obtain ⟨⟨r1, s', a'⟩, hr, ⟨⟨σ', hcase2, hX', hR', hV', hVI'⟩, -, hw⟩, hK⟩ :=
    spec_exists (WP.spec_and (WP.spec_and hPS
      (P1.sched.preemption_point.pp hA s a J.blk)) (J.ppDbg hA))
  have hcase : ((r1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
      (r1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) :=
    hcase2.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)
  rw [hr, WP.spec_ok]
  simp only at hcase hcase2 hX' hw hK hR' hV' hVI' ⊢
  have hX := J.xtop
  obtain ⟨Q, R0, hc, -⟩ := hX.fin.1.1.1.lists
  have hN' : P1.NodePlaced st (Z.mv G V).T s (L.cpu s) := by
    rw [hc.cur, J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ (hc.cur ▸ J.kern.cpuCs)
  have hSS : SlotsSame (Z.mv G V).th (L.mem s) (L.mem s') := hX.slotsSame_of hw fun b hb => by
    have hf := J.kern.ksbFit
    rcases hb with rfl | rfl | rfl
    · have := workUnits_val hf; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have e := P1.nodeAt_val hN' (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
      have e48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
      refine Or.inl ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
    · have e := P1.nodeAt_val hN' (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
      have e40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
      refine Or.inl ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
  have hks : L.ksb s' = L.ksb s := hw.1
  refine ⟨hSS, σ', hcase, hX'.rel.2.1, ?_⟩
  rcases hcase2 with ⟨rfl, hm0, ⟨Ac', Lst', J'⟩, hp', -⟩ | ⟨rfl, hm, hPre⟩
  · have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hDS.1.2.2.1.members y).1 hy).1
    have horig : σ'.isOriginalCap = σ.isOriginalCap :=
      orig_eq_of_slots hDS.1.2.2.2.1 hX'.rel.2.1.2.2.2.1 J.kern.orig J'.kern.orig hSS
    have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s :=
      ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
    have hL' : LiveJ (L := L) Z.th H G s' σ' :=
      hL.of_sameZ hSS hmem horig (congrArg Prod.snd (Vs.gke_preemptionPoint' σ _ hm0)) hK J.kern.cs0 hTz fun p hp => J'.jcov.dead p (Or.inr hp)
    exact ⟨⟨⟨V, Ac', Lst', _, J', by rw [hks]; exact hkb, Vs.ake_preemptionPoint'.noSwitch hm0 hns,
      SpecGlob.pp hm0 hsg, hp'⟩, hL', ⟨lst, J.dbgWF_keep J' rfl rfl hDW hK⟩,
      hN.of_same (fun y hy => hSS.capV hy) horig⟩, hR', hV', hVI'⟩
  · exact ⟨⟨s, a, σ, ⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hr, hm, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩, hPre⟩

/-- **The deletion loop's named steps at `MachPlat`** (module docstring). -/
theorem delHypsJLM [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hAR : ArchRefines arI AR)
    (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR th) (hF : JThreadFinHypsU (L := L) arI AR th)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    DelHypsWRZ (L := L) arI (WMR MR (WJL (L := L) arI AR Z H Cs kb)) (WJPM (L := L) arI AR MR Z H Cs kb)
      (RdLO (L := L) (A := A) th H) (RzJ (L := L) (A := A) H) th := by
  have hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a' := fun a i m => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.mask_irq a i m); exact ⟨a', h⟩
  have hfree : ∀ (a : A) (irq : U64), ∃ a', arI.irq_free a irq = ok a' := fun a i => by
    obtain ⟨a', h, -⟩ := spec_exists (hT.irq_free a i); exact ⟨a', h⟩
  exact ⟨(finJLZ arI hT hAR hK hV hF Z H Cs kb hth).mrv arI hM hKD hT, (rdTrivJLO arI Z H Cs kb hth).mrv,
    jPreemptHypLM arI hK hT hnd hM hPA Z H Cs kb hth,
    (jPostDelHypL arI hAM hmask hfree Z H Cs kb hth).mrv arI hM hKD,
    (jZombieHypL arI Z H Cs kb hth).mrv hM, (jSwapHypL arI Z H Cs kb hth).mrv hM,
    (emptyHypJL arI Z H Cs kb hth).mrv hM⟩

/-- **The deletion at `MachPlat`**: XTopJointWJLDel's `JDelHypL` with `MRV`
beside `WJL`, `WJPM` after a preemption. -/
def JDelHypLM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (K : Nat), Z.th = th →
    (∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) → 6 ≤ K →
    DelHypW (L := L) arI psiD th
      (fun s a σ G => DelE (L := L) Z.th K s σ ∧ WMR MR (WJL (L := L) arI AR Z H Cs kb) s a σ G)
      (fun s a σ G => DelE (L := L) Z.th K s σ ∧ WJPM (L := L) arI AR MR Z H Cs kb s a σ G)

/-- **`JDelHypLM` from `JDelParts`' platform and scope facts and `MachPlat`**
(no `PPPlat`). -/
theorem JDelParts.jDelHypLM [Fl4Proofs.P1.PlainStore st] (h : JDelParts (L := L) arI AR th)
    (hT : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (hPA : PPPlatA arI AR) (hAM : ARMask arI AR) :
    JDelHypLM (L := L) arI AR MR th := by
  intro Z H Cs kb K hth hK hK6 s a σ G c hCR hE hA hxm
  obtain ⟨⟨⟨V, Ac, Lst, D, J, -⟩, -⟩, -⟩ := hE.2
  have hP : Placed th := hth ▸ J.xtop.rel.1
  have hH := delHypsJLM arI hT h.archRef h.arKeep h.vt h.thr hnd hM hKD hPA hAM Z H Cs kb hth
  subst hth
  exact delHyp_fullWRZ arI _ _ _ _ Z.th hP (finalHyp_full Z.th hP) hH K hK hK6 s a σ G c hCR hE hA hxm

end

end

end Fl4Proofs.P3
