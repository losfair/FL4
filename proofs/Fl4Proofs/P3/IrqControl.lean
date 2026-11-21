/-
P3 (DESIGN.md §9), interrupts: **the IRQControl invocations** (FL4
`interrupt::decode_irq_control`: `IRQIssueIRQHandler` (label 33), the x86
`X86IRQIssueIRQHandlerIOAPIC` (67) and `MSI` (68), and l4h's
`X86IRQIssueIRQHandlerIOAPICRemapped` (69)) against FL4's spec
(`Fl4Spec/Ext/IrqControl.lean`: l4v's `decode_irq_control_invocation` with
the legacy-PIC `arch_check_irq`, and the remapped label), then `set_thread_state
Restart` and `invoke_irq_control`.

This file: the shared steps. The IRQ handler cap is inserted as a child of
the IRQ control cap (`insert_ctl_full`); it is fresh because IRQ handler
caps exist only for active IRQs (`HandlersActive`, l4v `valid_irq_handlers`)
and the decode checked that the IRQ is inactive. The IRQ's state word
becomes `IRQ_SIGNAL`; `IrqRel` is kept (`invoke_ctl_rel`, `restart_irq`).
-/
import Fl4Proofs.P3.IrqHandler
import Fl4Proofs.P3.IntFrame
import Fl4Spec.Ext.IrqControl
import Fl4Proofs.P3.MdbStepVs
import Fl4Proofs.P3.DomKeep
import Fl4Proofs.P3.StepSem
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- IRQ handler caps exist only for active IRQs (l4v `valid_irq_handlers`). -/
def HandlersActive (mem : U64 → U64) (kb : U64) (G : MdbGhost) : Prop :=
  ∀ y ∈ G.chains.flatten, ∀ i, capV mem y = .IrqHandler i → i.val < 128 ∧ mem (irqStA kb i) ≠ 0#u64

theorem srB_irqH_left (i : U64) (b : capability.Cap) : srB (.IrqHandler i) b = decide (b = .IrqHandler i) := by
  apply srB_of_eq; cases b <;> simp [objects.same_region_as]
  split_ifs <;> simp_all [eq_comm]

theorem fresh_of_inactive {mem : U64 → U64} {kb : U64} {G : MdbGhost} (hHA : HandlersActive mem kb G)
    {irq : U64} (hin : mem (irqStA kb irq) = 0#u64) :
    ∀ y ∈ G.chains.flatten, srB (.IrqHandler irq) (capV mem y) = false := by
  intro y hy
  rw [srB_irqH_left]
  by_contra h
  simp only [decide_eq_false_iff_not, not_not] at h
  exact (hHA y hy irq h).2 hin

theorem genObjRefs_irqH (i : U64) :
    Fl4Spec.genObjRefs (absCap (.IrqHandler i)) = {Fl4Spec.GenObjRef.iRQRef (BitVec.ofNat 8 i.val)} := by
  ext g
  simp [Fl4Spec.genObjRefs, absCap, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archCapSetMap]

/-- A cap overlapping an IRQ handler cap is one, for the same 8-bit IRQ. -/
theorem ovl_irqH {i : U64} {c : capability.Cap} (h : Ovl (absCap (.IrqHandler i)) (absCap c)) :
    ∃ j, c = .IrqHandler j ∧ (BitVec.ofNat 8 j.val : BitVec 8) = BitVec.ofNat 8 i.val := by
  unfold Ovl at h
  rw [genObjRefs_irqH, ← Set.nonempty_iff_ne_empty] at h
  obtain ⟨g, hg1, hg2⟩ := h
  rw [Set.mem_singleton_iff.1 hg1] at hg2
  cases c <;> simp [Fl4Spec.genObjRefs, absCap, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt] at hg2 ⊢
  exact hg2.symm

/-- **A new IRQ handler cap for an inactive IRQ overlaps no cap of the MDB.** -/
theorem ovl_fresh_irq {mem : U64 → U64} {kb : U64} {G : MdbGhost} (hHA : HandlersActive mem kb G)
    {irq : U64} (hirq : irq.val < 128) (hin : mem (irqStA kb irq) = 0#u64) :
    ∀ y ∈ G.chains.flatten, ¬ Ovl (absCap (.IrqHandler irq)) (absCap (capV mem y)) := by
  intro y hy ho
  obtain ⟨j, hj, he⟩ := ovl_irqH ho
  have hj128 := (hHA y hy j hj).1
  have e : j = irq := ofNat8_inj hj128 hirq he
  subst e
  exact (hHA y hy j hj).2 hin

theorem ucast8_ofNat (w : U64) : (Fl4Spec.ucast 8 w.bv : BitVec 8) = BitVec.ofNat 8 w.val := by
  apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast]

/-- The spec's state changes outside the CSpace keep the relations. -/
theorem crel_irq_of {th : TypedHeap} {mem : U64 → U64} {kb : U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    (hCR : CRel th mem σ G) (hIR : IrqRel mem kb σ) (hk : σ'.kheap = σ.kheap) (hc : σ'.cdt = σ.cdt)
    (ho : σ'.isOriginalCap = σ.isOriginalCap) (hs : σ'.interruptStates = σ.interruptStates)
    (hn : σ'.interruptIrqNode = σ.interruptIrqNode) : CRel th mem σ' G ∧ IrqRel mem kb σ' := by
  refine ⟨crel_same hCR (SlotsSame.refl _ _) hk hc ho, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hs]; exact hIR.st i hi
  · rw [hn]; exact hIR.node i hi

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The outcome of an IRQControl invocation against a spec decode `m`:
the same error with the state unchanged, or an invocation after which (with
`set_thread_state Restart` first) the invocation `invk` has an outcome in
related states, with `FinInv` and `HandlersActive`; the run made of
primitive steps from `(s, ar, σ)` (`Steps`). -/
def CPost {X : Type} (invk : X → Fl4Spec.PMonad Unit Unit) (th : TypedHeap) (kb : U64) (σ : Fl4Spec.State Unit)
    (m : Fl4Spec.SEMonad Unit X) (s : S) (ar : A) : core.result.Result Unit error.Exc × S × A → Prop
  | (.Err e, s', a') => s' = s ∧ (∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∧ a' = ar
  | (.Ok (), s', a') => ∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      ∃ σ' G', (.ok (), σ') ∈ ((invk inv).run σ1).1 ∧ CRel th (L.mem s') σ' G' ∧ IrqRel (L.mem s') kb σ' ∧
        FinInv th (L.mem s') σ' G' ∧ HandlersActive (L.mem s') kb G' ∧ MdbOKV kb (L.mem s') G' ∧
        (DomPlaced (L := L) th s → DK4 (L := L) s s') ∧ (CurRun σ → Steps (L := L) arI th s ar σ s' a' σ')

variable {arI} in
theorem CPost.of_run {X : Type} {invk : X → Fl4Spec.PMonad Unit Unit} {th : TypedHeap} {kb : U64}
    {σ : Fl4Spec.State Unit} {m m' : Fl4Spec.SEMonad Unit X} (h : m.run σ = m'.run σ) {s : S} {ar : A}
    {res : core.result.Result Unit error.Exc × S × A} (hq : CPost (L := L) arI invk th kb σ m' s ar res) :
    CPost (L := L) arI invk th kb σ m s ar res := by
  obtain ⟨r, s', a'⟩ := res
  cases r with
  | Err e => obtain ⟨h1, ⟨e', h2, h3⟩, h4⟩ := hq; exact ⟨h1, ⟨e', h.trans h2, h3⟩, h4⟩
  | Ok u => obtain ⟨inv, h2, h3⟩ := hq; exact ⟨inv, h.trans h2, h3⟩

variable {arI} in
theorem CPost.congr {X : Type} {invk : X → Fl4Spec.PMonad Unit Unit} {th : TypedHeap} {kb : U64}
    {σ : Fl4Spec.State Unit} {m m' : Fl4Spec.SEMonad Unit X} (h : m.run σ = m'.run σ) {s : S} {ar : A}
    {prog : Result (core.result.Result Unit error.Exc × S × A)}
    (hp : prog ⦃ res => CPost (L := L) arI invk th kb σ m' s ar res ⦄) :
    prog ⦃ res => CPost (L := L) arI invk th kb σ m s ar res ⦄ :=
  WP.spec_mono hp (fun _ hq => CPost.of_run h hq)

variable {arI} in
theorem CPost.err {X : Type} {invk : X → Fl4Spec.PMonad Unit Unit} {th : TypedHeap} {kb : U64}
    {σ : Fl4Spec.State Unit} {m : Fl4Spec.SEMonad Unit X} {s : S} {ar : A} {e : error.Exc} {e' : Fl4Spec.SyscallError}
    (h : m.run σ = ({(.error e', σ)}, False)) (he : ErrRel e e') :
    (ok ((.Err e, s, ar) : core.result.Result Unit error.Exc × S × A)) ⦃ res =>
      CPost (L := L) arI invk th kb σ m s ar res ⦄ := by
  rw [WP.spec_ok]; exact ⟨rfl, ⟨e', h, he⟩, rfl⟩

/-! ## `set_thread_state Restart` -/

theorem stA_val {th : TypedHeap} (hP : Placed th) {t : U64} (ht : th t = some .tcb) : (stA t).val = t.val + 3328 := by
  have htf := hP.fits t _ ht
  rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp

/-- **`set_thread_state Restart`, with the interrupt relation.** -/
theorem restart_irq (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i) :
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s1 =>
      L.ksb s1 = L.ksb s ∧ SlotsSame th (L.mem s) (L.mem s1) ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        CRel th (L.mem s1) σ1 G ∧ IrqRel (L.mem s1) (L.ksb s) σ1 ∧ σ1.archState = σ.archState ∧
        σ1.curThread = σ.curThread ∧
        ∀ i : U64, i.val < 128 → L.mem s1 (irqStA (L.ksb s) i) = L.mem s (irqStA (L.ksb s) i) ⦄ := by
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  refine WP.spec_mono (WP.spec_and (WP.spec_and (set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact)
    (set_thread_state_ksb s ct sched.TS_RESTART)) (set_thread_state_cases s ct sched.TS_RESTART)) ?_
  rintro s1 ⟨⟨hS, hkb⟩, hcase⟩
  obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
  rw [← hcur] at hk
  obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, -, -⟩ := restart_rel hR hV hM hC hS hk .restart
  obtain ⟨hn1, hs1, ha1, -, hc1⟩ := setThreadState_keeps hk hst
  have hw : ∀ i : U64, i.val < 128 → L.mem s1 (irqStA (L.ksb s) i) = L.mem s (irqStA (L.ksb s) i) := by
    intro i hi
    have hsa : P1.Aligned (stA ct) := by
      unfold P1.Aligned; rw [stA_val hP htcb]; have := hP.align ct _ htcb; omega
    have hio := hL.st_out i hi
    have hne : stA ct ≠ irqStA (L.ksb s) i := by
      intro e
      have := hio.2 ct _ htcb
      have h2 := stA_val hP htcb
      rw [e] at h2
      simp [objSize] at this; omega
    rcases hcase with rfl | rfl
    · rw [L.mem_wr _ _ _ _ hsa hio.1, if_neg hne]
    · rw [L.mem_wr _ _ _ _ hact.1 hio.1, if_neg (hact2 i hi), L.mem_wr _ _ _ _ hsa hio.1, if_neg hne]
  refine ⟨hkb, hS, σ1, hst, ⟨hR1, hV1, hM1, hC1, MdbInv.of_same hM hI hS⟩, ⟨fun i hi => ?_, fun i hi => ?_⟩,
    ha1, hc1, hw⟩
  · rw [hs1, hIR.st i hi, hw i hi]
  · rw [hn1]; exact hIR.node i hi

/-! ## `invoke_irq_control` -/

/-- **`invoke_irq_control` against the spec's `set_irq_state Signal` and
`cap_insert`**, for an inactive IRQ, with the IRQ control cap at the source
and the destination empty (slots of CNodes). -/
theorem invoke_ctl_rel (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (hHA : HandlersActive (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (irq : U64) (hirq : irq.val < 128) (hin : L.mem s (irqStA (L.ksb s) irq) = 0#u64)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null) (hDL : DestLive th (L.mem s) (L.ksb s) pd) :
    interrupt.invoke_irq_control st arI s ar irq (cslotAddr (pd.bv, idxd)) (cslotAddr (ps.bv, idxs)) ⦃ r =>
      ∃ σ' G', ((), σ') ∈ ((Fl4Spec.setIrqState (Z := Unit) .irqSignal (BitVec.ofNat 8 irq.val) >>= fun _ =>
          Fl4Spec.capInsert (Z := Unit) (.irqHandlerCap (BitVec.ofNat 8 irq.val)) (ps.bv, idxs) (pd.bv, idxd)) σ).1 ∧
        CRel th (L.mem r.1) σ' G' ∧ IrqRel (L.mem r.1) (L.ksb s) σ' ∧ L.ksb r.1 = L.ksb s ∧
        FinInv th (L.mem r.1) σ' G' ∧ HandlersActive (L.mem r.1) (L.ksb s) G' ∧ MdbOKV (L.ksb s) (L.mem r.1) G' ∧
        Steps (L := L) arI th s ar σ r.1 r.2 σ' ⦄ := by
  unfold interrupt.invoke_irq_control
  obtain ⟨a1, ha1⟩ := hmask ar irq (decide (interrupt.IRQ_SIGNAL = interrupt.IRQ_INACTIVE))
  rw [set_irq_state_eq arI s ar _ irq ha1]
  simp only [bind_ok]
  set s1 := L.wr s (irqStA (L.ksb s) irq) interrupt.IRQ_SIGNAL with hs1
  have hS := IntLayout.slotsSame (L := L) hP hL s hirq interrupt.IRQ_SIGNAL
  rw [← hs1] at hS
  set σ1 := setIrqSt .irqSignal (BitVec.ofNat 8 irq.val) σ with hσ1
  have hCR1 : CRel th (L.mem s1) σ1 G := crel_same hCR hS rfl rfl rfl
  have hsig : irqSt interrupt.IRQ_SIGNAL = .irqSignal := by simp [irqSt, interrupt.IRQ_SIGNAL]
  have hIR1 : IrqRel (L.mem s1) (L.ksb s) σ1 :=
    IrqRel.wr hL hIR hirq _ σ1 (by rw [hsig]; rfl) rfl
  have hM := hCR.2.2.1
  obtain ⟨hR1, hV1, hM1, hC1, hI1⟩ := hCR1
  have hfr := fresh_of_inactive hHA hin
  have hfr1 : ∀ y ∈ G.chains.flatten, srB (.IrqHandler irq) (capV (L.mem s1) y) = false := by
    intro y hy; rw [hS.capV ((hM.members y).1 hy).1]; exact hfr y hy
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsrc1 : capAt (L.mem s1) (cslotAddr (ps.bv, idxs)) = ok .IrqControl := by rw [hS.capAt hAs.isSlot, hsrcC]
  have hdst1 : capAt (L.mem s1) (cslotAddr (pd.bv, idxd)) = ok .Null := by rw [hS.capAt hAd.isSlot, hdst]
  have hFI1 : FinInv th (L.mem s1) σ1 G := hFI.of_same hM hS (KSub.of_kheap rfl)
  have hw1 : ∀ i : U64, i.val < 128 → L.mem s1 (irqStA (L.ksb s) i) =
      if i = irq then interrupt.IRQ_SIGNAL else L.mem s (irqStA (L.ksb s) i) := by
    intro i hi
    rw [hs1, L.mem_wr _ _ _ _ (hL.st_out irq hirq).1 (hL.st_out i hi).1]
    by_cases e : i = irq
    · subst e; simp
    · rw [if_neg (fun h => e (irqStA_inj hL.fit hirq hi h).symm), if_neg e]
  have hHA1 : HandlersActive (L.mem s1) (L.ksb s) G := by
    intro y hy i hi
    rw [hS.capV ((hM.members y).1 hy).1] at hi
    obtain ⟨h1, h2⟩ := hHA y hy i hi
    refine ⟨h1, ?_⟩
    rw [hw1 i h1]
    split_ifs
    · simp [interrupt.IRQ_SIGNAL]
    · exact h2
  have hin1 : ∀ y ∈ G.chains.flatten, ¬ Ovl (absCap (.IrqHandler irq)) (absCap (capV (L.mem s1) y)) := by
    intro y hy; rw [hS.capV ((hM.members y).1 hy).1]; exact ovl_fresh_irq hHA hirq hin y hy
  have hins := insert_ctl_full_fin th s1 σ1 G hR1 hV1 hP hM1 hC1 hI1 hFI1 hps hpd hls hld hsrc1 hdst1
    (.IrqHandler irq) (show irq.val < 128 by omega) trivial (by simp [EncWf]) trivial hfr1 hin1
  have hnx : nextOf (L.mem s1) (cslotAddr (ps.bv, idxs)) = 0#u64 ∨
      IsSlot th (nextOf (L.mem s1) (cslotAddr (ps.bv, idxs))) := by
    have hsm : cslotAddr (ps.bv, idxs) ∈ G.chains.flatten := (hM1.members _).2 ⟨hAs.isSlot, _, hsrc1, by simp⟩
    rcases hM1.next_mem hsm with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ((hM1.members _).1 h).1
  have hfrm := insert_frame hP s1 (.IrqHandler irq) _ _ hAs.isSlot hAd.isSlot _ hsrc1 hnx
  refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and hins hfrm)
    (Vs.insert_frame2 hP s1 (.IrqHandler irq) _ _ hAs.isSlot hAd.isSlot _ hsrc1 hnx))
    (insert_delinv_imp hP s1 G hM1 ((hM1.members _).2 ⟨hAs.isSlot, _, hsrc1, by simp⟩) hAd.isSlot
      (capV_null_not_mem hM1 (capV_of_capAt hdst1)) hsrc1 (.IrqHandler irq) (by simp [EncWf]) (by simp) rfl)) ?_
  rintro s2 ⟨⟨⟨⟨σ2, G2, hci, hR2, hV2, hM2, hC2, hI2, hFI2, hcap2, ⟨bG2, hG2e⟩, hSt2⟩, hF2⟩, hF2'⟩, hdi⟩
  rw [WP.spec_ok]
  have hkeep := capInsert_keeps (absCap (.IrqHandler irq)) (ps.bv, idxs) (pd.bv, idxd) σ1 ((), σ2)
    (by rw [hci]; rfl)
  have hkb2 : L.ksb s2 = L.ksb s := by rw [hF2.1]; simp [s1]
  have hFRG : MdbOKV (L.ksb s) (L.mem s2) G2 := (MdbStep.same_left hM hS hSt2).okv hFR
  have hk1 : L.ksb s1 = L.ksb s := by simp [s1]
  have hstp : Steps (L := L) arI th s ar σ s2 a1 σ2 :=
    Steps.trans arI (Steps.irqWr arI hL hirq interrupt.IRQ_SIGNAL ha1 .irqSignal hsig)
      (Steps.insert arI hP hps hpd hld hci hF2' ⟨hR2, hV2, hM2, hC2, hI2⟩ hFI2 (by rw [hk1]; exact hFRG)
        (fun y hy hne => by rw [hcap2 y hy, if_neg hne]) hdst1
        (fun p sb fi d h => by rw [hcap2 _ hAd.isSlot, if_pos rfl] at h; cases h)
        (typedKept_set hcap2 (Or.inl rfl)) (hDL.same hS hk1) hdi
        (fun _ _ _ _ _ _ => by rw [hcap2 _ hAd.isSlot, if_pos rfl]; trivial)
        (fun _ _ => by rw [hcap2 _ hAd.isSlot, if_pos rfl]; trivial)
        (fun _ => by rw [hcap2 _ hAd.isSlot, if_pos rfl]; trivial)
          (by rw [hcap2 _ hAd.isSlot, if_pos rfl]; exact fun h => by cases h)
          (fun _ _ _ h => by rw [hcap2 _ hAd.isSlot, if_pos rfl] at h; cases h))
  refine ⟨σ2, G2, ?_, ⟨hR2, hV2, hM2, hC2, hI2⟩, ⟨fun i hi => ?_, fun i hi => ?_⟩, hkb2, hFI2, ?_, hFRG, hstp⟩
  rotate_right
  · intro y hy i hi
    have hys := ((hM2.members y).1 hy).1
    rw [hcap2 y hys] at hi
    rw [hF2.out (hL.st_out i ?_)]
    · split_ifs at hi with hyd
      · cases hi; refine ⟨hirq, ?_⟩; rw [hw1 irq hirq, if_pos rfl]; simp [interrupt.IRQ_SIGNAL]
      · have hyn : capV (L.mem s1) y ≠ .Null := by rw [hi]; simp
        have hym : y ∈ G.chains.flatten := (hM1.members y).2 ⟨hys, _, capAt_capV _ _, hyn⟩
        exact hHA1 y hym i hi
    · split_ifs at hi with hyd
      · cases hi; exact hirq
      · have hyn : capV (L.mem s1) y ≠ .Null := by rw [hi]; simp
        have hym : y ∈ G.chains.flatten := (hM1.members y).2 ⟨hys, _, capAt_capV _ _, hyn⟩
        exact (hHA1 y hym i hi).1
  · refine mem_bind_nd (x := ((), σ1)) (setIrqState_mem' _ _ _) ?_
    show ((), σ2) ∈ (Fl4Spec.capInsert (absCap (.IrqHandler irq)) (ps.bv, idxs) (pd.bv, idxd) σ1).1
    rw [hci]; rfl
  · rw [hkeep.1, hF2.out (hL.st_out i hi)]; exact hIR1.st i hi
  · rw [hkeep.2.1]; exact hIR1.node i hi

end

end

end Fl4Proofs.P3
