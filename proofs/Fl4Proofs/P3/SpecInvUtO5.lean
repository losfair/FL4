/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut7): **the IRQ control,
IRQ handler, IO-port control and ASID-pool performs keep `P3 N`** (spec side
only; imports SpecInvUtO4).

* Issue inserts (`issue_irq_handler` in its three forms and FL4's remapped
  IOAPIC form, `ioport_control`): the source is the invoked control slot
  (`irqControlCap` / `ioPortControlCap`), the new cap covers nothing
  (`RefRel`), and the destination is a CNode lookup (`DestRefV`):
  `IrqCOKN` / `ArchIrqOKN` / `Fl4IrqCOKN` / `IoCOKN`, the decodes establish them
  (`okv_decodeIrqControlN`, `okv_archDecodeIrqControlN`,
  `okv_decodeIrqControlRemappedN`, `okv_decodeFl4IrqControlN`,
  `okv_decodeIoportControlN`), the performs keep `P3 N`.
* SetIRQHandler: the cap is the extra cap in its slot, that slot is a CSpace
  lookup (`DestRefV`), so it is not the IRQ-node slot (`IrqOutV`), so
  `cap_delete_one` of the node slot keeps it; the node slot is `PosOK`
  (`posOK_irq`, the state's node is `N`): `p3_setIRQHandler`.
  `okv_lookupExtraCapsN`: every extra cap's slot is a CSpace lookup.
* `p3_performAsidPoolInvocation` (no decode fact: the perform re-reads the slot).
-/
import Fl4Proofs.P3.SpecInvUtO4
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef}

/-! ## Issue inserts -/

/-- An insert of a cap derived from the source's cap into a CNode lookup slot. -/
theorem hv_insertCtl {c0 c : Cap} (hR : RefRel c0 c) (src dest : CslotPtr) :
    HV (fun w => P3V N w ∧ w.2.1 src = some c0 ∧ DestRefV w dest) (P3V N) (capInsert (Z := Unit) c src dest) :=
  hv_pre (hv_capInsert3 c src dest) fun _ h => ⟨h.1, ⟨c0, h.2.1, Or.inr hR⟩, posOK_of_destRef h.1.1.2 h.2.2⟩

theorem refRel_irq (irq : Irq) : RefRel .irqControlCap (.irqHandlerCap irq) :=
  ⟨fun _ h => by simp [capRng, objRefs] at h, rfl, fun _ _ _ e => (by cases e), fun _ _ _ e => (by cases e),
    fun _ _ _ _ e => (by cases e)⟩

theorem refRel_ioport (f l : IoPort) :
    RefRel (.archObjectCap .ioPortControlCap) (.archObjectCap (.ioPortCap f l)) :=
  ⟨fun _ h => by simp [capRng, acRng, aobjRef] at h, rfl, fun _ _ _ e => (by cases e),
    fun _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e)⟩

/-- A UK prefix before an issue insert. -/
macro "ctl_auto" : tactic => `(tactic| repeat' (first
  | exact hv_insertCtl (refRel_irq _) _ _ | exact hv_insertCtl (refRel_ioport _ _) _ _
  | (refine hv_pure_bind ?_) | (dsimp only)
  | (refine hv_bind (hv_uk fun _ => by uk_auto) fun _ => ?_)))

def IrqSrcOK (w : UView) (dest src : CslotPtr) : Prop :=
  w.2.1 src = some .irqControlCap ∧ DestRefV w dest

def ArchIrqOKN (w : UView) : ArchIrqControlInvocation → Prop
  | .issueIRQHandlerIOAPIC _ dest src _ _ _ _ _ => IrqSrcOK w dest src
  | .issueIRQHandlerMSI _ dest src _ _ _ _ => IrqSrcOK w dest src

def IrqCOKN (w : UView) : IrqControlInvocation → Prop
  | .irqControl _ dest src => IrqSrcOK w dest src
  | .archIRQControl i => ArchIrqOKN w i

def Fl4IrqCOKN (w : UView) : Fl4IrqControlInvocation → Prop
  | .spec i => IrqCOKN w i
  | .ioapicRemapped _ dest src _ _ _ _ _ _ => IrqSrcOK w dest src

theorem p3_archInvokeIrqControl (i : ArchIrqControlInvocation) (σ : State Unit) (hI : P3 N σ)
    (hok : ArchIrqOKN (uV σ) i) : ∀ y ∈ ((archInvokeIrqControl (Z := Unit) i).run σ).1, P3 N y.2 := by
  intro y hy
  cases i with
  | issueIRQHandlerIOAPIC irq dest src ioapic pin level polarity vector =>
    simp only [archInvokeIrqControl, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => P3V N w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (P3V N) _ by ctl_auto)
      σ ⟨hI, hok⟩ x hx
  | issueIRQHandlerMSI irq dest src bus dev func handle =>
    simp only [archInvokeIrqControl, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => P3V N w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (P3V N) _ by ctl_auto)
      σ ⟨hI, hok⟩ x hx

theorem p3_invokeIrqControl (i : IrqControlInvocation) (σ : State Unit) (hI : P3 N σ)
    (hok : IrqCOKN (uV σ) i) : ∀ y ∈ ((invokeIrqControl (Z := Unit) i).run σ).1, P3 N y.2 := by
  intro y hy
  cases i with
  | irqControl irq dest src =>
    simp only [invokeIrqControl] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => P3V N w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (P3V N) _ by ctl_auto)
      σ ⟨hI, hok⟩ x hx
  | archIRQControl i => exact p3_archInvokeIrqControl i σ hI hok y hy

theorem p3_invokeFl4IrqControl (i : Fl4IrqControlInvocation) (σ : State Unit) (hI : P3 N σ)
    (hok : Fl4IrqCOKN (uV σ) i) : ∀ y ∈ ((invokeFl4IrqControl (Z := Unit) i).run σ).1, P3 N y.2 := by
  intro y hy
  cases i with
  | spec i => exact p3_invokeIrqControl i σ hI hok y hy
  | ioapicRemapped irq dest src ioapic pin level polarity vector handle =>
    simp only [invokeFl4IrqControl, withoutPreemption] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    exact (show HV (fun w => P3V N w ∧ w.2.1 src = some .irqControlCap ∧ DestRefV w dest) (P3V N) _ by ctl_auto)
      σ ⟨hI, hok⟩ x hx

def IoCOKN (w : UView) : IoPortControlInvocation → Prop
  | .ioPortControlInvocation _ _ dest src => w.2.1 src = some (.archObjectCap .ioPortControlCap) ∧ DestRefV w dest

theorem p3_performIoportControl (i : IoPortControlInvocation) (σ : State Unit) (hI : P3 N σ)
    (hok : IoCOKN (uV σ) i) : ∀ y ∈ (performIoportControlInvocation (Z := Unit) i σ).1, P3 N y.2 := by
  cases i with
  | ioPortControlInvocation f l dest src =>
    unfold performIoportControlInvocation
    exact (show HV (fun w => P3V N w ∧ w.2.1 src = some (.archObjectCap .ioPortControlCap) ∧ DestRefV w dest)
      (P3V N) _ by ctl_auto) σ ⟨hI, hok⟩

/-! ## The issue decodes -/

theorem root0 {w : UView} {l : List Cap} (h : ∀ c ∈ l, ∃ s, w.2.1 s = some c) (hl : 1 ≤ l.length) :
    ∃ s, w.2.1 s = some (the l[0]?) := by
  obtain ⟨a, t, rfl⟩ : ∃ a t, l = a :: t := by
    cases l with
    | nil => simp at hl
    | cons a t => exact ⟨a, t, rfl⟩
  exact h a List.mem_cons_self

macro "okvn_step" : tactic => `(tactic| first
  | exact okv_throw _ | exact okv_throw' _ | exact okv_liftE_fail
  | (refine okv_returnOk_bind ?_) | (refine okv_pure_bind ?_)
  | (refine okv_whenE_bind fun _ => ?_) | (refine okv_unlessE_bind fun _ => ?_)
  | (refine okv_bind (fun _ => uk_lookupTargetSlot _ _ _)
      (okv_lookupSlotForCnodeOpN false _ _ _ (root0 (by assumption) (by omega))) fun _ _ => ?_)
  | (refine okv_bind (fun _ => uk_ensureEmpty _) (okv_ensureEmpty _) fun _ _ => ?_)
  | (dsimp only)
  | (refine okv_bind_uk (fun _ => by uk_auto) fun _ => ?_))

set_option maxHeartbeats 4000000 in
theorem okv_archDecodeIrqControlN {w : UView} (label : Data) (args : List Data) (src : CslotPtr) (cps : List Cap)
    (hsrc : w.2.1 src = some .irqControlCap) (hcps : ∀ c ∈ cps, ∃ s, w.2.1 s = some c) :
    OkV w (ArchIrqOKN w) (archDecodeIrqControlInvocation (Z := Unit) label args src cps) := by
  unfold archDecodeIrqControlInvocation
  repeat' (first | okvn_step | split)
  all_goals exact okv_returnOk ⟨hsrc, by assumption⟩

set_option maxHeartbeats 4000000 in
theorem okv_decodeIrqControlN {w : UView} (label : Data) (args : List Data) (src : CslotPtr) (cps : List Cap)
    (hsrc : w.2.1 src = some .irqControlCap) (hcps : ∀ c ∈ cps, ∃ s, w.2.1 s = some c) :
    OkV w (IrqCOKN w) (decodeIrqControlInvocationWith (Z := Unit) fl4ArchCheckIrq label args src cps) := by
  unfold decodeIrqControlInvocationWith
  split
  · split
    · repeat' okvn_step
      exact okv_returnOk ⟨hsrc, by assumption⟩
    · exact okv_throw _
  · exact okv_liftME (okv_archDecodeIrqControlN label args src cps hsrc hcps)

set_option maxHeartbeats 4000000 in
theorem okv_decodeIrqControlRemappedN {w : UView} (args : List Data) (src : CslotPtr) (cps : List Cap)
    (hsrc : w.2.1 src = some .irqControlCap) (hcps : ∀ c ∈ cps, ∃ s, w.2.1 s = some c) :
    OkV w (Fl4IrqCOKN w) (decodeIrqControlRemapped (Z := Unit) args src cps) := by
  unfold decodeIrqControlRemapped
  split
  · repeat' okvn_step
    exact okv_returnOk ⟨hsrc, by assumption⟩
  · exact okv_throw _

theorem okv_decodeFl4IrqControlN {w : UView} (rm : Bool) (label : Data) (args : List Data) (src : CslotPtr)
    (cps : List Cap) (hsrc : w.2.1 src = some .irqControlCap) (hcps : ∀ c ∈ cps, ∃ s, w.2.1 s = some c) :
    OkV w (Fl4IrqCOKN w) (decodeFl4IrqControl (Z := Unit) rm label args src cps) := by
  unfold decodeFl4IrqControl
  split
  · exact okv_decodeIrqControlRemappedN args src cps hsrc hcps
  · exact okv_liftME (okv_decodeIrqControlN label args src cps hsrc hcps)

set_option maxHeartbeats 4000000 in
theorem okv_decodeIoportControlN {w : UView} (label : Data) (args : List Data) (src : CslotPtr) (cap : ArchCap)
    (cps : List Cap) (hsrc : w.2.1 src = some (.archObjectCap .ioPortControlCap))
    (hcps : ∀ c ∈ cps, ∃ s, w.2.1 s = some c) :
    OkV w (fun i => ∃ j, i = .invokeIOPortControl j ∧ IoCOKN w j)
      (decodeIoportControlInvocation (Z := Unit) label args src cap cps) := by
  unfold decodeIoportControlInvocation
  repeat' (first | okvn_step | split)
  all_goals exact okv_returnOk ⟨_, rfl, hsrc, by assumption⟩

/-! ## SetIRQHandler -/

/-- Every extra cap's slot is a CSpace lookup. -/
theorem okv_lookupSlotForThreadN {w : UView} (t : ObjRef) (cp : CapRef) :
    OkV w (fun x : CslotPtr × CapRef => DestRefV w x.1) (lookupSlotForThread (Z := Unit) t cp) := by
  unfold lookupSlotForThread
  refine okv_liftE_bind (fun _ => by uk_auto) (Q := fun tcb : Tcb => ∃ s, w.2.1 s = some tcb.tcbCtable) ?_
    fun tcb htcb => okv_resolveN _ fun _ _ _ _ => htcb
  intro σ hσ x hx
  unfold NonDet.getsThe at hx
  cases e : getTcb t σ with
  | none => rw [e] at hx; exact hx.elim
  | some a =>
    rw [e] at hx
    obtain rfl : x = (a, σ) := Set.mem_singleton_iff.1 hx
    refine ⟨(t, tcbCnodeIndex 0), ?_⟩
    rw [← hσ]
    show capAt σ _ = _
    unfold capAt
    rw [getTcb_kheap e]
    show tcbCnodeMap a (tcbCnodeIndex 0) = _
    unfold tcbCnodeMap
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]

theorem okv_lookupExtraCapsN {w : UView} (t : ObjRef) (buf : Option Data) (mi : MessageInfo) :
    OkV w (fun l => ∀ p ∈ l, w.2.1 p.2 = some p.1 ∧ DestRefV w p.2) (lookupExtraCaps (Z := Unit) t buf mi) := by
  unfold lookupExtraCaps
  refine okv_liftE_bind (fun _ => uk_getExtraCptrs _ _) (Q := fun _ => True) (fun _ _ _ _ => trivial) fun cps _ => ?_
  induction cps with
  | nil => unfold NonDetE.mapME; exact okv_pure fun p hp => absurd hp List.not_mem_nil
  | cons a as ih =>
    unfold NonDetE.mapME
    have hq : OkV w (fun p : Cap × CslotPtr => w.2.1 p.2 = some p.1 ∧ DestRefV w p.2)
        (capFaultOnFailure (Z := Unit) (ofBl a) false (lookupCapAndSlot t a)) := by
      refine okv_capFaultOnFailure _ _ ?_
      unfold lookupCapAndSlot
      refine okv_bind (fun _ => uk_lookupSlotForThread _ _) (okv_lookupSlotForThreadN _ _) fun x hx => ?_
      obtain ⟨sl, cr⟩ := x
      exact okv_liftE_getCap_bind fun c hc => okv_returnOk ⟨hc, hx⟩
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _)) hq fun p hp => ?_
    refine okv_bind (fun _ => ike_mapME (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _)) _)
      ih fun ps hps => okv_pure ?_
    intro q hq'
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact hp
    · exact hps q hq'

def IrqHOKN (w : UView) : IrqHandlerInvocation → Prop
  | .setIRQHandler _ c sl => w.2.1 sl = some c ∧ DestRefV w sl ∧ isNtfnCap c = true
  | _ => True

theorem okv_decodeIrqHandlerN {w : UView} (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr))
    (hex : ∀ p ∈ cps, w.2.1 p.2 = some p.1 ∧ DestRefV w p.2) :
    OkV w (IrqHOKN w) (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation
  split
  · exact okv_returnOk trivial
  · split
    · split
      · rename_i hne
        obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
        obtain ⟨cap, slot⟩ := a
        have hh := hex _ List.mem_cons_self
        dsimp only [List.head?, the]
        split
        · rename_i hc; exact okv_returnOk ⟨hh.1, hh.2, hc.1⟩
        · exact okv_throw _
      · exact okv_throw _
    · split
      · exact okv_returnOk trivial
      · exact okv_throw _

theorem p3_setIRQHandler (irq : Irq) (cap : Cap) (slot : CslotPtr) (σ : State Unit) (hI : P3 N σ)
    (hN : σ.interruptIrqNode = N) (hok : IrqHOKN (uV σ) (.setIRQHandler irq cap slot)) :
    ∀ y ∈ (invokeIrqHandler (Z := Unit) (.setIRQHandler irq cap slot) σ).1, P3 N y.2 := by
  obtain ⟨hc, hdr, hnt⟩ := hok
  intro y hy
  simp only [invokeIrqHandler, getIrqSlot] at hy
  obtain ⟨x1, hx1, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hx1
  obtain ⟨x2, hx2, hy⟩ := hy
  dsimp only at hx2 hy
  rw [hN] at hx2 hy
  have hne : slot ≠ (N irq, []) := by
    intro e
    obtain ⟨s1, c1, hs1, hr1, -, -⟩ := hdr
    rw [e] at hr1
    exact hI.2 irq s1 c1 hs1 (capRng_sub_covR _ (sRefs_sub_capRng _ hr1))
  have hI2 : P3 N x2.2 := p3_capDeleteOne _ σ hI x2 hx2
  have hc2 : (uV x2.2).2.1 slot = some cap := (capDeleteOne_keep _ slot hne (uV σ) σ rfl x2 hx2).trans hc
  have hR : RefRel cap cap := by
    cases cap <;> simp [isNtfnCap] at hnt
    exact refRel_self (fun _ _ _ e => (by cases e)) (fun _ _ _ _ e => (by cases e))
  exact hv_capInsert3 cap slot (N irq, []) x2.2 ⟨hI2, ⟨cap, hc2, Or.inr hR⟩, posOK_irq hI2.2 irq⟩ y hy

/-! ## The ASID pool -/

/-- **`perform_asid_pool_invocation` keeps `P3 N`** (it re-reads the slot; no decode fact). -/
theorem p3_performAsidPoolInvocation (iv : AsidPoolInvocation) : IK (P3 N) (performAsidPoolInvocation (Z := Unit) iv) := by
  cases iv with
  | assign asid poolPtr ctSlot =>
    show HV (P3V N) (P3V N) _
    unfold performAsidPoolInvocation
    refine hv_getCap_bind fun w c hw hc => ?_
    split
    · rename_i b m
      refine hv_bind (hv_setCap _ _ w) fun _ => ?_
      refine hv_mono (hv_uk fun _ => uk_storeAsidPoolEntry _ _ _) fun w' e => ?_
      subst e
      have h0 : Cap.archObjectCap (.pml4Cap b m) ≠ .nullCap := fun e => by cases e
      have hre : RefEq (.archObjectCap (.pml4Cap b m)) (.archObjectCap (.pml4Cap b (some asid))) := by
        refeq_right
      exact ⟨⟨utInv'_vCap_nn hw.1.1 ⟨fun e => (by cases e), fun _ _ _ _ e => (by cases e)⟩, utN_vCapEq hw.1.2 hc hre⟩,
        irqOut_vCap (c := .archObjectCap (.pml4Cap b (some asid))) hw.2 (covBy_of hc (fun _ h => h)) ctSlot⟩
    · intro σ _ y hy; exact hy.elim

end

end Fl4Proofs.P3.SInvU
