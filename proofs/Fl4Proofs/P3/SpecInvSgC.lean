/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, sg1): **the CNode, IRQ control,
IRQ handler, IO-port control and ASID-pool performs keep `S N M`** (spec side
only; imports SpecInvSgG).

* `RotOKN w ci`: a rotate's source and pivot slots are lookup destinations
  (`DestRefV`), so no IRQ-node slots; **`okv_decodeCnodeRot`** (the CNode decode
  establishes it, given the extra caps in slots). ut7's `CnOKN` gives the rest
  (insert / move / rotate-target destinations `DestRefV`).
* `sg_invokeCnode` (insert: `hv_capInsertS`; move: ut7's `hv_capMove3` at `N` and
  `M`, its slot facts give `NOV`; rotate: the swap (`nov_swap`) or two moves).
* `hv_insertCtlS` (an issue insert into a lookup slot), `sg_invokeIrqControl`,
  `sg_archInvokeIrqControl`, `sg_invokeFl4IrqControl`, `sg_performIoportControl`.
* **`sg_setIRQHandler`**: the one writer of an IRQ-node slot; it writes the
  decoded notification cap (`IrqHOKN`: `isNtfnCap`), so `NOV` holds after it;
  `IrqOutV M` by ut7's `hv_capInsertIO` (the cap sits in its own slot).
* `sg_performAsidPoolInvocation` (rewrites the slot of the PML4 cap it read).
-/
import Fl4Proofs.P3.SpecInvSgG
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

variable {N M : Irq → ObjRef}

/-! ## View lemmas -/

theorem nov_post_move {w w' : UView} (h : NOV N w) {src dest : CslotPtr} {c : Cap}
    (h1 : w'.2.1 src = some .nullCap) (h2 : w'.2.1 dest = some c)
    (h3 : ∀ x, x ≠ src → x ≠ dest → w'.2.1 x = w.2.1 x) (hd : NotNode N dest ∨ NtfnOrNull c) : NOV N w' := by
  intro irq a ha
  by_cases e1 : (N irq, ([] : CnodeIndex)) = src
  · rw [e1, h1] at ha; cases ha; exact ntfnOrNull_null
  by_cases e2 : (N irq, ([] : CnodeIndex)) = dest
  · rcases hd with hd | hd
    · exact absurd e2.symm (hd irq)
    · rw [e2, h2] at ha; cases ha; exact hd
  · rw [h3 _ e1 e2] at ha; exact h irq a ha

theorem nov_swap {w : UView} (h : NOV N w) {s1 s2 : CslotPtr} (h1 : NotNode N s1) (h2 : NotNode N s2) (c1 c2 : Cap) :
    NOV N (vCap s2 c1 (vCap s1 c2 (vRen (sw s1 s2) w))) := by
  refine nov_vCap (nov_vCap ?_ (Or.inl h1)) (Or.inl h2)
  intro irq a ha
  have e1 : sw s1 s2 (N irq, []) = (N irq, []) := by
    unfold sw; rw [if_neg (fun e => h1 irq e.symm), if_neg (fun e => h2 irq e.symm)]
  have ha' : w.2.1 (sw s1 s2 (N irq, [])) = some a := ha
  rw [e1] at ha'
  exact h irq a ha'

/-! ## The CNode decode: rotate's slots -/

/-- A rotate's source and pivot slots are lookup destinations. -/
def RotOKN (w : UView) : CnodeInvocation → Prop
  | .rotateCall _ _ s1 s2 _ => DestRefV w s1 ∧ DestRefV w s2
  | _ => True

theorem root1 {w : UView} {l : List Cap} (h : ∀ c ∈ l, ∃ s, w.2.1 s = some c) (hl : 1 < l.length) :
    ∃ s, w.2.1 s = some (the l[1]?) := by
  have h1 : l[1]? = some l[1] := List.getElem?_eq_getElem hl
  rw [h1]
  exact h _ (List.getElem_mem hl)

set_option maxHeartbeats 4000000 in
/-- **The CNode decode: a rotate's source and pivot are lookup destinations.** -/
theorem okv_decodeCnodeRot {w : UView} (label : Data) (args : List Data) (cap : Cap) (ex : List Cap)
    (hex : ∀ c ∈ ex, ∃ s, w.2.1 s = some c) :
    OkV w (RotOKN w) (decodeCnodeInvocation (Z := Unit) label args cap ex) := by
  unfold decodeCnodeInvocation
  refine okv_unlessE_bind fun _ => okv_whenE_bind fun _ => okv_returnOk_bind (okv_returnOk_bind
    (okv_returnOk_bind (okv_bind_uk (fun _ => uk_lookupTargetSlot _ _ _) fun destSlot => ?_)))
  refine okv_ite ?_ (okv_ite (okv_returnOk trivial) (okv_ite (okv_returnOk trivial) (okv_ite ?_ (okv_ite' ?_
    fun _ => okv_throw _))))
  · refine okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind ?_)))
    refine okv_bind_uk (fun _ => uk_ensureEmpty _) fun _ => ?_
    refine okv_bind_uk (fun _ => uk_lookupSourceSlot _ _ _) fun srcSlot => ?_
    refine okv_liftE_getCap_bind fun srcCap _ => okv_whenE_bind fun _ => ?_
    refine okv_bind_uk (fun _ => by uk_auto) fun x => ?_
    obtain ⟨rights, capData, isMove⟩ := x
    dsimp only
    refine okv_returnOk_bind ?_
    cases isMove
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact okv_bind_uk (fun _ => uk_deriveCap _ _) fun _ => okv_whenE_bind fun _ => okv_returnOk trivial
    · simp only [↓reduceIte]
      exact okv_returnOk_bind (okv_whenE_bind fun _ => okv_returnOk trivial)
  · repeat' okv_step
    all_goals exact okv_returnOk trivial
  · intro hc
    have hl : 1 < ex.length := hc.2.2
    refine okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind
      (okv_returnOk_bind (okv_returnOk_bind (okv_returnOk_bind ?_)))))))
    refine okv_bind (fun _ => uk_lookupSourceSlot _ _ _)
      (okv_lookupSlotForCnodeOpN true _ _ _ (root1 hex hl)) fun srcSlot hs => ?_
    refine okv_bind (fun _ => uk_lookupPivotSlot _ _ _)
      (okv_lookupSlotForCnodeOpN true _ _ _ (root0 hex (by omega))) fun pivotSlot hp => ?_
    repeat' okv_step
    all_goals exact okv_returnOk ⟨hs, hp⟩

/-! ## The CNode performs -/

/-- **`invoke_cnode` keeps `S N M`** from the decode's facts. -/
theorem sg_invokeCnode (ci : CnodeInvocation) (σ : State Unit) (hI : S N M σ) (hok : CnOKN (uV σ) ci)
    (hr : RotOKN (uV σ) ci) : ∀ y ∈ ((invokeCnode (Z := Unit) ci).run σ).1, S N M y.2 := by
  intro y hy
  cases ci with
  | revokeCall d => exact sg_capRevoke d σ hI y hy
  | deleteCall d => exact sg_capDelete d σ hI y hy
  | insertCall c src dest =>
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact hv_capInsertS c src dest σ ⟨hI, hok.1, posOK_of_destRef hI.1.1.2 hok.2,
      Or.inl (notNode_of_destRef hI.1.2 hok.2)⟩ x hx
  | moveCall c src dest =>
    obtain ⟨c0, hs, hd, hre, hc, hne, hdr⟩ := hok
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    have hp := posOK_of_destRef hI.1.1.2 hdr
    obtain ⟨hU, h1, h2, h3⟩ := hv_capMove3 hI.1 hs hd hre hc hp hne σ rfl x hx
    have hM := (hv_capMove3 (N := M) ⟨hI.1.1, hI.2.1⟩ hs hd hre hc hp hne σ rfl x hx).1
    exact ⟨hU, hM.2, nov_post_move hI.2.2 h1 h2 h3 (Or.inl (notNode_of_destRef hI.1.2 hdr))⟩
  | rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨c1', c2', h1, h2, hr1, hn1, hr2, hn2, h21, h23, hdr, h3⟩ := hok
    obtain ⟨hd1, hd2⟩ := hr
    have hN1 : NotNode N s1 := notNode_of_destRef hI.1.2 hd1
    have hN2 : NotNode N s2 := notNode_of_destRef hI.1.2 hd2
    simp only [invokeCnode, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    split at hx
    · refine ⟨hv_capSwap3 (Ne.symm h21) hr1 hr2 hn1 hn2 σ ⟨hI.1, h1, h2⟩ x hx,
        (hv_capSwap3 (N := M) (Ne.symm h21) hr1 hr2 hn1 hn2 σ ⟨⟨hI.1.1, hI.2.1⟩, h1, h2⟩ x hx).2, ?_⟩
      have hv := capSwap_view (w := uV σ) (Ne.symm h21) c1 c2 σ rfl x hx
      show NOV N (uV x.2)
      rw [hv]
      exact nov_swap hI.2.2 hN1 hN2 c1 c2
    · rename_i h13
      obtain ⟨x1, hx1, hx⟩ := hx
      have hP2 : PosOK (uV σ) s2 := posOK_of_nn hI.1.1.2 h2 (hr2.nn hn2)
      have hP3 : PosOK (uV σ) s3 := posOK_of_destRef hI.1.1.2 hdr
      obtain ⟨hI1, hs1, hd1', hoth⟩ := hv_capMove3 hI.1 h2 (h3 h13) hr2 hn2 hP3 h23 σ rfl x1 hx1
      have hM1 := (hv_capMove3 (N := M) ⟨hI.1.1, hI.2.1⟩ h2 (h3 h13) hr2 hn2 hP3 h23 σ rfl x1 hx1).1
      have hnov1 : NOV N (uV x1.2) :=
        nov_post_move hI.2.2 hs1 hd1' hoth (Or.inl (notNode_of_destRef hI.1.2 hdr))
      have h1' : (uV x1.2).2.1 s1 = some c1' := by
        rw [hoth s1 (Ne.symm h21) h13]; exact h1
      have hP2' : PosOK (uV x1.2) s2 := posOK_move h2 hr2 hs1 hd1' hoth (h3 h13) hP2
      obtain ⟨hI2, hs2, hd2', hoth2⟩ := hv_capMove3 hI1 h1' hs1 hr1 hn1 hP2' (Ne.symm h21) x1.2 rfl x hx
      have hM2 := (hv_capMove3 (N := M) ⟨hI1.1, hM1.2⟩ h1' hs1 hr1 hn1 hP2' (Ne.symm h21) x1.2 rfl x hx).1
      exact ⟨hI2, hM2.2, nov_post_move hnov1 hs2 hd2' hoth2 (Or.inl hN2)⟩
  | cancelBadgedSendsCall cap =>
    cases cap
    case endpointCap ep b r =>
      exact (show IKE (S N M) (withoutPreemption (Z := Unit) (NonDet.when (b ≠ 0) (cancelBadgedSends ep b))) by
        sg_auto) σ hI y hy
    all_goals
      obtain ⟨x, hx, -⟩ := mem_liftE' (show y ∈ ((NonDetE.liftE (ε := Unit)
        (NonDet.fail : NonDet (State Unit) Unit)).run σ).1 from hy)
      exact hx.elim

/-! ## Issue inserts -/

/-- An insert of a cap derived from the source's cap into a CNode lookup slot keeps `SV N M`. -/
theorem hv_insertCtlS {c0 c : Cap} (hR : RefRel c0 c) (src dest : CslotPtr) :
    HV (fun w => SV N M w ∧ w.2.1 src = some c0 ∧ DestRefV w dest) (SV N M) (capInsert (Z := Unit) c src dest) :=
  hv_pre (hv_capInsertS c src dest) fun _ h => ⟨h.1, ⟨c0, h.2.1, Or.inr hR⟩, posOK_of_destRef h.1.1.1.2 h.2.2,
    Or.inl (notNode_of_destRef h.1.1.2 h.2.2)⟩

macro "sctl_auto" : tactic => `(tactic| repeat' (first
  | exact hv_insertCtlS (refRel_irq _) _ _ | exact hv_insertCtlS (refRel_ioport _ _) _ _
  | (refine hv_pure_bind ?_) | (dsimp only)
  | (refine hv_bind (hv_uk fun _ => by uk_auto) fun _ => ?_)))

theorem sg_archInvokeIrqControl (i : ArchIrqControlInvocation) (σ : State Unit) (hI : S N M σ)
    (hok : ArchIrqOKN (uV σ) i) : ∀ y ∈ ((archInvokeIrqControl (Z := Unit) i).run σ).1, S N M y.2 := by
  intro y hy
  cases i with
  | issueIRQHandlerIOAPIC irq dest src ioapic pin level polarity vector =>
    simp only [archInvokeIrqControl, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => SV N M w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (SV N M) _ by sctl_auto)
      σ ⟨hI, hok⟩ x hx
  | issueIRQHandlerMSI irq dest src bus dev func handle =>
    simp only [archInvokeIrqControl, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => SV N M w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (SV N M) _ by sctl_auto)
      σ ⟨hI, hok⟩ x hx

theorem sg_invokeIrqControl (i : IrqControlInvocation) (σ : State Unit) (hI : S N M σ)
    (hok : IrqCOKN (uV σ) i) : ∀ y ∈ ((invokeIrqControl (Z := Unit) i).run σ).1, S N M y.2 := by
  intro y hy
  cases i with
  | irqControl irq dest src =>
    simp only [invokeIrqControl] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => SV N M w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (SV N M) _ by sctl_auto)
      σ ⟨hI, hok⟩ x hx
  | archIRQControl i => exact sg_archInvokeIrqControl i σ hI hok y hy

theorem sg_invokeFl4IrqControl (i : Fl4IrqControlInvocation) (σ : State Unit) (hI : S N M σ)
    (hok : Fl4IrqCOKN (uV σ) i) : ∀ y ∈ ((invokeFl4IrqControl (Z := Unit) i).run σ).1, S N M y.2 := by
  intro y hy
  cases i with
  | spec i => exact sg_invokeIrqControl i σ hI hok y hy
  | ioapicRemapped irq dest src ioapic pin level polarity vector handle =>
    simp only [invokeFl4IrqControl, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => SV N M w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (SV N M) _ by sctl_auto)
      σ ⟨hI, hok⟩ x hx

theorem sg_performIoportControl (i : IoPortControlInvocation) (σ : State Unit) (hI : S N M σ)
    (hok : IoCOKN (uV σ) i) : ∀ y ∈ (performIoportControlInvocation (Z := Unit) i σ).1, S N M y.2 := by
  cases i with
  | ioPortControlInvocation f l dest src =>
    unfold performIoportControlInvocation
    exact (show HV (fun w => SV N M w ∧ w.2.1 src = some (.archObjectCap .ioPortControlCap) ∧ DestRefV w dest)
      (SV N M) _ by sctl_auto) σ ⟨hI, hok⟩

/-! ## The IRQ handler -/

/-- **`set_irq_handler` keeps `S N M`**: it writes the decoded notification cap into the node slot. -/
theorem sg_setIRQHandler (irq : Irq) (cap : Cap) (slot : CslotPtr) (σ : State Unit) (hI : S N M σ)
    (hN : σ.interruptIrqNode = N) (hok : IrqHOKN (uV σ) (.setIRQHandler irq cap slot)) :
    ∀ y ∈ (invokeIrqHandler (Z := Unit) (.setIRQHandler irq cap slot) σ).1, S N M y.2 := by
  have hP := p3_setIRQHandler irq cap slot σ hI.1 hN hok
  obtain ⟨hc, hdr, hnt⟩ := hok
  intro y hy
  refine ⟨hP y hy, ?_⟩
  simp only [invokeIrqHandler, getIrqSlot] at hy
  obtain ⟨x1, hx1, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hx1
  obtain ⟨x2, hx2, hy⟩ := hy
  dsimp only at hx2 hy
  rw [hN] at hx2 hy
  have hne : slot ≠ (N irq, []) := notNode_of_destRef hI.1.2 hdr irq
  have hc2 : (uV x2.2).2.1 slot = some cap := (capDeleteOne_keep _ slot hne (uV σ) σ rfl x2 hx2).trans hc
  have hO2 : IrqOutV M (uV x2.2) := io_capDeleteOne (N := M) _ σ hI.2.1 x2 hx2
  have hn2 : NOV N (uV x2.2) := s_capDeleteOne_nov _ σ hI.2.2 x2 hx2
  have hntf : NtfnOrNull cap := by
    cases cap <;> simp [isNtfnCap] at hnt
    exact Or.inr ⟨_, _, _, rfl⟩
  exact ⟨hv_capInsertIO cap slot _ x2.2 ⟨hO2, fun c0 h0 => by rw [hc2] at h0; cases h0; exact subset_rfl⟩ y hy,
    nov_capInsert cap slot _ x2.2 ⟨hn2, Or.inr hntf⟩ y hy⟩

/-! ## The ASID pool -/

theorem sg_performAsidPoolInvocation (iv : AsidPoolInvocation) :
    IK (S N M) (performAsidPoolInvocation (Z := Unit) iv) := by
  refine s_of (fun _ => p3_performAsidPoolInvocation iv) fun σ h y hy => ?_
  cases iv with
  | assign asid poolPtr ctSlot =>
    refine (show HV (NOV N) (NOV N) (performAsidPoolInvocation (Z := Unit) (.assign asid poolPtr ctSlot)) from ?_)
      σ h.2.2 y hy
    unfold performAsidPoolInvocation
    refine hv_getCap_bind fun w c hw hc => ?_
    split
    · rename_i b m
      refine hv_bind (hv_pre (nov_setCap _ _) fun w' e => e ▸ ⟨hw, Or.inl (notNode_of_held hw hc ?_)⟩)
        fun _ => hv_uk fun _ => uk_storeAsidPoolEntry _ _ _
      rintro (e | ⟨_, _, _, e⟩) <;> cases e
    · intro σ _ y hy; exact hy.elim

end

end Fl4Proofs.P3.SInvG
