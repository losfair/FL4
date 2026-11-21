/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, sg1): **the arch, MakePool and
untyped performs keep `S N M`** (spec side only; imports SpecInvSgC).

`UtInv''` and both range facts come from ut8's `p3_*` lemmas at `N` and `M`; the
node slots' contents `NOV N` need only that every slot these performs write a
non-null cap into is no IRQ-node slot, a fact about addresses fixed at the start:

* `NOVS N σ := NOV N (uV σ)` and its leaves `nvk_setCap` / `nvk_capInsert` /
  `nvk_createCap` (at a `NotNode` slot), `nvk_deleteObjects` (objects only removed),
  `nvk_retype` (new objects hold null caps only: ut8's `default_null`).
* `ArchSlN w i`: a VSpace map writes a slot that holds an arch cap (the invoked
  cap's slot); **`okv_archDecodeSl`** / `okv_fl4ArchDecodeSl` (the arch decode
  establishes it).
* `sg_fl4ArchPerform` (the page / table / directory / PDPT maps and unmaps rewrite
  a slot holding an arch cap; DeriveSubframe inserts into slots of a CNode a cap
  names; IO-port control and ASID-pool by SpecInvSgC), `sg_makePool` (the parent
  holds an untyped cap, the pool's slot is a lookup destination),
  **`sg_invokeUntyped`** (the source holds an untyped cap, every destination is a
  slot of the CNode a cap names: ut8's `UtOKN`).
-/
import Fl4Proofs.P3.SpecInvSgC
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

variable {N M : Irq → ObjRef}

/-- `NOV` on a state. -/
abbrev NOVS (N : Irq → ObjRef) (σ : State Unit) : Prop := NOV N (uV σ)

/-! ## Leaves -/

theorem nvk_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK (NOVS N) m :=
  ik_of_uk (fun _ _ e hI => by show NOV N _; rw [e]; exact hI) h

theorem nvke_of_uk {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, UKE v m) : IKE (NOVS N) m := nvk_of_uk h

theorem nvk_setCap {c : Cap} {sl : CslotPtr} (h : NotNode N sl ∨ NtfnOrNull c) : IK (NOVS N) (setCap (Z := Unit) c sl) :=
  fun σ hσ y hy => nov_setCap c sl σ ⟨hσ, h⟩ y hy

theorem nvk_capInsert {c : Cap} {src dest : CslotPtr} (h : NotNode N dest ∨ NtfnOrNull c) :
    IK (NOVS N) (capInsert (Z := Unit) c src dest) :=
  fun σ hσ y hy => nov_capInsert c src dest σ ⟨hσ, h⟩ y hy

theorem nvk_deleteObjects (p : Word) (b : Nat) : IK (NOVS N) (deleteObjects (Z := Unit) p b) := by
  intro σ hσ y hy
  obtain ⟨hk, -, -, -⟩ := deleteObjects_kheap hy
  intro irq a ha
  have ha' : capAt y.2 (N irq, []) = some a := ha
  unfold capAt at ha'
  rw [hk] at ha'
  split_ifs at ha'
  exact hσ irq a ha'

theorem nvk_retype (bA : ApiObjectType → Nat → Nat) (rb : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool) :
    IK (NOVS N) (retypeRegionWith (Z := Unit) bA rb n oB ty dev) := by
  intro σ hσ y hy
  obtain ⟨-, h5⟩ := retypeRegionWith_out hy
  rcases h5 with e | ⟨hty, e⟩
  · show NOV N (uV y.2); rw [e]; exact hσ
  · intro irq a ha
    have ha' : capAt y.2 (N irq, []) = some a := ha
    rw [e] at ha'
    unfold capAt retKh at ha'
    try dsimp only at ha'
    split_ifs at ha' with hm
    · rw [default_null hty _ _ _ _ ha']; exact ntfnOrNull_null
    · exact hσ irq a ha'

theorem nvk_retypeRegion (rb : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool) :
    IK (NOVS N) (retypeRegion (Z := Unit) rb n oB ty dev) :=
  nvk_retype objBitsApi rb n oB ty dev

theorem nvk_createCap (ty : ApiObjectType) (sz : Nat) (src : CslotPtr) (dev : Bool) {d : CslotPtr} (p : ObjRef)
    (h : NotNode N d) : IK (NOVS N) (createCap (Z := Unit) ty sz src dev (d, p)) := by
  show HV (NOV N) (NOV N) _
  unfold createCap
  refine hv_gets_bind (fun w => w.2.2.1 d) (fun _ => rfl) fun w1 hw1 => ?_
  refine hv_gets_bind (fun w => w.2.2.1) (fun _ => rfl) fun w2 hw2 => ?_
  subst hw2
  refine hv_bind (R := NOV N) (hv_mono (hv_setCdt _ _) fun w' e => by subst e; exact hw1) fun _ => ?_
  refine hv_bind (R := NOV N) (hv_doExtendedOp _) fun _ => ?_
  refine hv_bind (R := NOV N) (hv_pin fun w hw => hv_mono (hv_setOriginal _ _ w) fun w' e => by subst e; exact hw) fun _ => ?_
  exact hv_pre (nov_setCap _ _) fun w hw => ⟨hw, Or.inl h⟩

theorem nvk_mapMx_mem {α γ : Type} {g : α → NonDet (State Unit) γ} :
    ∀ xs : List α, (∀ a ∈ xs, IK (NOVS N) (g a)) → IK (NOVS N) (NonDet.mapMx g xs)
  | [], _ => ik_pure' _
  | a :: xs, h => ik_bind' (h a (by simp)) fun _ => nvk_mapMx_mem xs fun b hb => h b (by simp [hb])

macro "nvk_auto" : tactic => `(tactic| repeat' (first
  | (exact nvk_setCap (Or.inl (by assumption)))
  | (exact nvk_capInsert (Or.inl (by assumption)))
  | exact nvk_deleteObjects _ _ | exact nvk_retype _ _ _ _ _ _ | exact nvk_retypeRegion _ _ _ _ _
  | (refine nvk_of_uk fun _ => ?_; uk_leaf; done) | (refine nvke_of_uk fun _ => ?_; uk_leaf; done)
  | contradiction | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE)
  | (unfold NonDet.when) | (unfold NonDet.unless)))

/-! ## The arch decode: the slots a map writes -/

/-- A map's slot holds an arch cap (the invoked cap's slot). -/
def HoldsArch (w : UView) (sl : CslotPtr) : Prop := ∃ a, w.2.1 sl = some (.archObjectCap a)

def ArchSlN (w : UView) : ArchInvocation → Prop
  | .invokePageTable (.pageTableMap _ sl _ _ _) => HoldsArch w sl
  | .invokePageDirectory (.pageDirectoryMap _ sl _ _ _) => HoldsArch w sl
  | .invokePDPT (.pdptMap _ sl _ _ _) => HoldsArch w sl
  | .invokePage (.pageMap _ sl _ _) => HoldsArch w sl
  | _ => True

def Fl4ArchSlN (w : UView) : Fl4ArchInvocation → Prop
  | .spec i => ArchSlN w i
  | _ => True

set_option maxHeartbeats 8000000 in
theorem okv_archDecodeSl {w : UView} (label : Data) (args : List Data) (xs : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (hc : w.2.1 cte = some (.archObjectCap cap)) :
    OkV w (ArchSlN w) (archDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  cases cap
  case pdPointerTableCap p m =>
    simp only [archDecodeInvocation, decodePdptInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk ⟨_, hc⟩
  case pageDirectoryCap p m =>
    simp only [archDecodeInvocation, decodePageDirectoryInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk ⟨_, hc⟩
  case pageTableCap p m =>
    simp only [archDecodeInvocation, decodePageTableInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk ⟨_, hc⟩
  case pageCap dev p R mt sz m =>
    simp only [archDecodeInvocation, decodePageInvocation]
    repeat' okva_step
    all_goals first | exact okv_returnOk trivial | exact okv_returnOk ⟨_, hc⟩
  case ioPortCap f l =>
    simp only [archDecodeInvocation]
    unfold decodePortInvocation
    split <;> okv_noasid
  all_goals (simp only [archDecodeInvocation]; okv_noasid)

set_option maxHeartbeats 8000000 in
theorem okv_fl4ArchDecodeSl {w : UView} (label : Data) (args : List Data) (xs : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (hc : w.2.1 cte = some (.archObjectCap cap)) :
    OkV w (Fl4ArchSlN w) (fl4ArchDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  cases cap
  case pageCap dev p R mt sz m =>
    simp only [fl4ArchDecodeInvocation]
    refine okv_ite (okv_liftME (okv_triv fun _ => trivial))
      (okv_ite (okv_liftME (okv_triv fun _ => trivial)) (okv_liftME (okv_archDecodeSl label args xs cte _ ex hc)))
  case pml4Cap p m =>
    simp only [fl4ArchDecodeInvocation]
    exact okv_ite (okv_liftME (okv_triv fun _ => trivial)) (okv_liftME (okv_archDecodeSl label args xs cte _ ex hc))
  all_goals (simp only [fl4ArchDecodeInvocation]; exact okv_liftME (okv_archDecodeSl label args xs cte _ ex hc))

/-! ## The arch performs -/

/-- The slot an arch invocation writes a non-null cap into. -/
def ArchWr : ArchInvocation → CslotPtr → Prop
  | .invokePageTable (.pageTableMap _ sl _ _ _), s => s = sl
  | .invokePageTable (.pageTableUnmap (.archObjectCap _) sl), s => s = sl
  | .invokePageDirectory (.pageDirectoryMap _ sl _ _ _), s => s = sl
  | .invokePageDirectory (.pageDirectoryUnmap (.archObjectCap _) sl), s => s = sl
  | .invokePDPT (.pdptMap _ sl _ _ _), s => s = sl
  | .invokePDPT (.pdptUnmap (.archObjectCap _) sl), s => s = sl
  | .invokePage (.pageMap _ sl _ _), s => s = sl
  | .invokePage (.pageUnmap _ sl), s => s = sl
  | .invokeIOPortControl (.ioPortControlInvocation _ _ d _), s => s = d
  | _, _ => False

theorem nvk_performPageInvocationUnmap (a : ArchCap) {sl : CslotPtr} (h : NotNode N sl) :
    IK (NOVS N) (performPageInvocationUnmap (Z := Unit) a sl) := by
  cases a with
  | pageCap dev p R mt sz mp => cases mp <;> (simp only [performPageInvocationUnmap]; nvk_auto)
  | _ => simp only [performPageInvocationUnmap]; nvk_auto

theorem nvk_performAsidPoolInvocation (iv : AsidPoolInvocation) :
    IK (NOVS N) (performAsidPoolInvocation (Z := Unit) iv) := by
  cases iv with
  | assign asid poolPtr ctSlot =>
    show HV (NOV N) (NOV N) _
    unfold performAsidPoolInvocation
    refine hv_getCap_bind fun w c hw hc => ?_
    split
    · rename_i b m
      refine hv_bind (hv_pre (nov_setCap _ _) fun w' e => e ▸ ⟨hw, Or.inl (notNode_of_held hw hc ?_)⟩)
        fun _ => hv_uk fun _ => uk_storeAsidPoolEntry _ _ _
      rintro (e | ⟨_, _, _, e⟩) <;> cases e
    · intro σ _ y hy; exact hy.elim

macro "nvka_auto" : tactic => `(tactic| repeat' (first
  | (exact nvk_performPageInvocationUnmap _ (by assumption))
  | exact nvk_performAsidPoolInvocation _
  | (exact nvk_setCap (Or.inl (by assumption)))
  | (exact nvk_capInsert (Or.inl (by assumption)))
  | (refine nvk_of_uk fun _ => ?_; uk_leaf; done) | (refine nvke_of_uk fun _ => ?_; uk_leaf; done)
  | contradiction | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE)
  | (unfold NonDet.when) | (unfold NonDet.unless) | split))

set_option maxHeartbeats 4000000 in
theorem nvk_archPerform (i : ArchInvocation) (hm : ∀ a, i ≠ .invokeASIDControl a)
    (hS : ∀ sl, ArchWr i sl → NotNode N sl) : IKE (NOVS N) (archPerformInvocation (Z := Unit) i) := by
  cases i with
  | invokeASIDControl a => exact absurd rfl (hm a)
  | invokePageTable iv =>
    cases iv with
    | pageTableMap c sl _ _ _ =>
      have h := hS sl (by simp [ArchWr])
      simp only [archPerformInvocation, performPageTableInvocation]; nvka_auto
    | pageTableUnmap c sl =>
      cases c
      case archObjectCap a =>
        have h := hS sl (by simp [ArchWr])
        cases a <;> (simp only [archPerformInvocation, performPageTableInvocation]; nvka_auto)
      all_goals (simp only [archPerformInvocation, performPageTableInvocation]; nvka_auto)
  | invokePageDirectory iv =>
    cases iv with
    | pageDirectoryMap c sl _ _ _ =>
      have h := hS sl (by simp [ArchWr])
      simp only [archPerformInvocation, performPageDirectoryInvocation]; nvka_auto
    | pageDirectoryUnmap c sl =>
      cases c
      case archObjectCap a =>
        have h := hS sl (by simp [ArchWr])
        cases a <;> (simp only [archPerformInvocation, performPageDirectoryInvocation]; nvka_auto)
      all_goals (simp only [archPerformInvocation, performPageDirectoryInvocation]; nvka_auto)
  | invokePDPT iv =>
    cases iv with
    | pdptMap c sl _ _ _ =>
      have h := hS sl (by simp [ArchWr])
      simp only [archPerformInvocation, performPdptInvocation]; nvka_auto
    | pdptUnmap c sl =>
      cases c
      case archObjectCap a =>
        have h := hS sl (by simp [ArchWr])
        cases a <;> (simp only [archPerformInvocation, performPdptInvocation]; nvka_auto)
      all_goals (simp only [archPerformInvocation, performPdptInvocation]; nvka_auto)
  | invokePage iv =>
    cases iv with
    | pageMap c sl _ _ =>
      have h := hS sl (by simp [ArchWr])
      simp only [archPerformInvocation, performPageInvocation]; nvka_auto
    | pageUnmap a sl =>
      have h := hS sl (by simp [ArchWr])
      cases a <;> (simp only [archPerformInvocation, performPageInvocation]; nvka_auto)
    | pageGetAddr p => simp only [archPerformInvocation, performPageInvocation]; nvka_auto
  | invokeASIDPool iv => simp only [archPerformInvocation]; nvka_auto
  | invokeIOPort iv => simp only [archPerformInvocation]; exact ike_liftE (nvk_of_uk fun _ => uk_performIoPortInvocation iv)
  | invokeIOPortControl iv =>
    cases iv with
    | ioPortControlInvocation f l d src =>
      have h := hS d (by simp [ArchWr])
      simp only [archPerformInvocation, performIoportControlInvocation]; nvka_auto

theorem archWr_notNode {σ : State Unit} (hI : S N M σ) (i : ArchInvocation) (hok : ArchSpecOKN (uV σ) i)
    (hsl : ArchSlN (uV σ) i) : ∀ sl, ArchWr i sl → NotNode N sl := by
  have hA : ∀ s a, (uV σ).2.1 s = some (.archObjectCap a) → NotNode N s := fun s a h =>
    notNode_of_held hI.2.2 h (by rintro (e | ⟨_, _, _, e⟩) <;> cases e)
  intro sl hw
  cases i with
  | invokePageTable iv =>
    cases iv with
    | pageTableMap c s _ _ _ => obtain ⟨a, ha⟩ := hsl; simp only [ArchWr] at hw; subst hw; exact hA _ _ ha
    | pageTableUnmap c s =>
      cases c <;> simp only [ArchWr] at hw
      subst hw; exact hA _ _ hok
  | invokePageDirectory iv =>
    cases iv with
    | pageDirectoryMap c s _ _ _ => obtain ⟨a, ha⟩ := hsl; simp only [ArchWr] at hw; subst hw; exact hA _ _ ha
    | pageDirectoryUnmap c s =>
      cases c <;> simp only [ArchWr] at hw
      subst hw; exact hA _ _ hok
  | invokePDPT iv =>
    cases iv with
    | pdptMap c s _ _ _ => obtain ⟨a, ha⟩ := hsl; simp only [ArchWr] at hw; subst hw; exact hA _ _ ha
    | pdptUnmap c s =>
      cases c <;> simp only [ArchWr] at hw
      subst hw; exact hA _ _ hok
  | invokePage iv =>
    cases iv with
    | pageMap c s _ _ => obtain ⟨a, ha⟩ := hsl; simp only [ArchWr] at hw; subst hw; exact hA _ _ ha
    | pageUnmap a s => simp only [ArchWr] at hw; subst hw; exact hA _ _ hok
    | pageGetAddr p => simp only [ArchWr] at hw
  | invokeIOPortControl iv =>
    cases iv with
    | ioPortControlInvocation f l d src =>
      simp only [ArchWr] at hw; subst hw; exact notNode_of_destRef hI.1.2 hok.2
  | _ => simp only [ArchWr] at hw

theorem nvk_deriveSubframe (iv : Fl4SubframeInvocation) (h : ∀ d ∈ iv.dests, NotNode N d) :
    IK (NOVS N) (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe
  exact nvk_mapMx_mem _ fun x hx => nvk_capInsert (Or.inl (h x.2 (List.of_mem_zip hx).2))

/-- **Every arch invocation but `invokeASIDControl` keeps `S N M`.** -/
theorem sg_fl4ArchPerform (ai : Fl4ArchInvocation) (hm : ∀ a, ai ≠ .spec (.invokeASIDControl a)) (σ : State Unit)
    (hI : S N M σ) (hok : ArchOKN (uV σ) ai) (hsl : Fl4ArchSlN (uV σ) ai) :
    ∀ y ∈ ((fl4ArchPerformInvocation (Z := Unit) ai).run σ).1, S N M y.2 := by
  intro y hy
  refine ⟨p3_fl4ArchPerform ai hm σ hI.1 hok y hy,
    (p3_fl4ArchPerform (N := M) ai hm σ ⟨hI.1.1, hI.2.1⟩ hok y hy).2, ?_⟩
  cases ai with
  | spec i =>
    simp only [fl4ArchPerformInvocation] at hy
    exact nvk_archPerform i (fun a e => hm a (by rw [e])) (archWr_notNode hI i hok hsl) σ hI.2.2 y hy
  | deriveSubframe iv =>
    simp only [fl4ArchPerformInvocation] at hy
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
    obtain ⟨p, r, mt, m, off, hsrc, hbase, hlen, s1, ptr, bits, g, hs1, hd⟩ := hok
    refine (ik_bind (nvk_deriveSubframe iv fun d hdm => ?_) fun _ => nvk_of_uk fun _ => by uk_auto) σ hI.2.2 x hx
    refine notNode_of_cov hI.1.2 hs1 ?_
    rw [(hd d hdm).1]
    simp [covR, capRng, objRefs]
  | _ => exact (nvke_of_uk fun _ => by simp only [fl4ArchPerformInvocation]; uk_auto) σ hI.2.2 y hy

/-! ## MakePool -/

theorem nvk_makePool (frame : ObjRef) {slot parent : CslotPtr} (base : Asid) (hp : NotNode N parent)
    (hs : NotNode N slot) :
    IK (NOVS N) (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base)) := by
  unfold performAsidControlInvocation
  repeat' (first
    | exact nvk_setCap (Or.inl hp) | exact nvk_capInsert (Or.inl hs)
    | exact nvk_deleteObjects _ _ | exact nvk_retypeRegion _ _ _ _ _
    | (refine nvk_of_uk fun _ => ?_; uk_leaf; done)
    | ik_step0 | ik_unfold)

/-- **MakePool keeps `S N M`.** -/
theorem sg_makePool {σ : State Unit} (hP : S N M σ) {a : AsidControlInvocation} (hm : MpOKN (uV σ) a) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) a σ).1, S N M y.2 := by
  intro y hy
  refine ⟨p3_makePool hP.1 hm y hy, (p3_makePool (N := M) ⟨hP.1.1, hP.2.1⟩ hm y hy).2, ?_⟩
  cases a with
  | makePool frame slot parent base =>
    obtain ⟨⟨dev, fi, hc, -⟩, hdr, -⟩ := hm
    have hp : NotNode N parent := notNode_of_held hP.2.2 hc (by rintro (e | ⟨_, _, _, e⟩) <;> cases e)
    exact nvk_makePool frame base hp (notNode_of_destRef hP.1.2 hdr) σ hP.2.2 y hy

/-! ## The untyped retype -/

set_option maxHeartbeats 4000000 in
theorem nvk_resetUntypedCap {s : CslotPtr} (hs : NotNode N s) : IKE (NOVS N) (resetUntypedCap (Z := Unit) s) := by
  intro σ hσ y hy
  unfold resetUntypedCap at hy
  obtain ⟨x, hx, hy⟩ := run_liftE_bind_mem hy
  obtain ⟨cap, s0⟩ := x
  obtain ⟨hs0, -⟩ := getCap_capAt hx
  simp only at hs0; rw [hs0] at hy
  replace hy := run_returnOk_bind_mem hy
  replace hy := run_returnOk_bind_mem hy
  dsimp only at hy
  split at hy
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ
  · obtain ⟨z, hz, hy⟩ := run_liftE_bind_mem hy
    have hz0 : NOVS N z.2 := nvk_deleteObjects _ _ σ hσ z hz
    refine (?_ : IKE (NOVS N) _) z.2 hz0 y hy
    repeat' (first
      | (exact nvk_setCap (Or.inl hs))
      | (exact ik_doMachineOp (fun _ _ h => h) _)
      | (exact nvke_of_uk fun _ => uk_preemptionPoint)
      | (exact nvk_of_uk fun _ => uk_archPostResetUntyped _ _)
      | (refine ike_mapMEx_mem _ fun _ _ => ?_)
      | ik_step0 | (unfold NonDet.unless) | (unfold NonDetE.whenE))

theorem nvk_invokeUntyped {s : CslotPtr} (reset : Bool) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat)
    {slots : List CslotPtr} (dev : Bool) (hs : NotNode N s) (hd : ∀ d ∈ slots, NotNode N d) :
    IKE (NOVS N) (fl4InvokeUntyped (Z := Unit) (.retype s reset base rb ty sz slots dev)) := by
  simp only [invokeUntypedWith]
  refine ike_bind ?_ fun _ => ike_liftE ?_
  · unfold NonDetE.whenE
    split
    · exact nvk_resetUntypedCap hs
    · exact ike_returnOk _
  · repeat' (first
      | (refine nvk_mapMx_mem _ fun x hx => ?_; obtain ⟨d, p⟩ := x;
         exact nvk_createCap _ _ _ _ p (hd d (List.of_mem_zip hx).1))
      | exact nvk_setCap (Or.inl hs)
      | exact nvk_retype _ _ _ _ _ _
      | (exact nvk_of_uk fun _ => uk_initArchObjects _ _ _ _ _ _)
      | (refine nvk_of_uk fun _ => ?_; uk_leaf; done)
      | ik_step0 | ik_unfold)

/-- **`invoke_untyped` keeps `S N M`** from the decode's facts. -/
theorem sg_invokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hP : S N M σ) (hok : UtGapOK (uV σ) ui) :
    ∀ y ∈ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui) σ).1, S N M y.2 := by
  intro y hy
  refine ⟨p3_invokeUntyped ui σ hP.1 hok y hy, (p3_invokeUntyped (N := M) ui σ ⟨hP.1.1, hP.2.1⟩ hok y hy).2, ?_⟩
  obtain ⟨h1, -, h3⟩ := hok
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  obtain ⟨bits, fi, hc, -⟩ := h1
  obtain ⟨-, s1, nc, off, win, hs1, hcn, -, he⟩ := h3
  have hsN : NotNode N s := notNode_of_held hP.2.2 hc (by rintro (e | ⟨_, _, _, e⟩) <;> cases e)
  have hdN : ∀ d ∈ slots, NotNode N d := by
    intro d hd
    rw [he] at hd
    obtain ⟨cref, -, rfl⟩ := List.mem_map.1 hd
    cases nc <;> simp [isCnodeCap] at hcn
    exact notNode_of_cov hP.1.2 hs1 (by simp [objRefOf, covR, capRng, objRefs])
  exact nvk_invokeUntyped reset base rb ty sz dev hsN hdN σ hP.2.2 y hy

end

end Fl4Proofs.P3.SInvG
