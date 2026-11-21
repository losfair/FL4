/-
P3 (DESIGN.md §9), invariant line G1 (vfh1): **VfhAll in the cap view** and
the cap-write leaves (spec side only, outside the JAtZ cone).

`VfhAll` (SpecInvVfhAll, l4v `valid_tcb`'s `valid_fault_handler` of
`tcb_fault_handler`) is restated over vih2's cap view `hV` (every slot's cap as
`get_cap` reads it), so that vih2's generated frames (SpecInvValidIrqHandlersF1..F4,
`[WLH P] → IKH P f` for the 341 spec functions that write no cap) keep it:

* `VfhV σ`: every slot `(p, tcbCnodeIndex 3)` of an object whose index
  `tcbCnodeIndex 6` holds no cap holds a valid fault handler. A TCB has caps
  exactly at indices 0..5, a (well-formed) CNode holding index 3 has radix 3
  and so holds index 6 too, other objects hold none: `vfhV_iff : VfhV σ ↔
  VfhAll σ`.
* `vfh_Bad σ sl` (the written slot is a TCB's fault-handler slot, in view
  terms): `sl.2 = tcbCnodeIndex 3 ∧` index 6 of `sl.1` empty. A cap write keeps
  `VfhV` iff the slot is not `Bad` or the cap is a valid fault handler
  (`vfh_setCap_step`).
* `DomK σ σ'`: no slot that held a cap in `σ` is empty in `σ'` (cap writes
  only fill existing slots). `Bad` is anti-monotone along `DomK`, so a slot
  shown not `Bad` at an earlier state stays so. Only `retype_region` and
  `delete_objects` break `DomK`.
* `VS σ0 σ := VfhV σ ∧ DomK σ0 σ`, a `WLH` predicate: the family gives
  `IK (VS σ0) f` for every frame function; the writers here are stated as
  `IK (VS σ0)` with side conditions about the anchor `σ0` (`¬ vfh_Bad σ0 sl` or
  a valid cap).

Sources of `¬ Bad`: the slot holds a cap that is no valid fault handler
(`vfh_notBad_old`, by `VfhV`), the slot index is not `tcbCnodeIndex 3`
(`vfh_notBad_idx`: TCB indices 0,1,2,4,5, the IRQ node's `[]`, a zombie's
first slot), or the slot's object holds every index of the slot's length
(`vfh_notBad_full`: a CNode slot found by a lookup through a CNode cap of a
valid cap state, see SpecInvVfhC).
-/
import Fl4Proofs.P3.SpecInvValidIrqHandlersD
import Fl4Proofs.P3.SpecInvVfhAll
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The view form -/

theorem vfh_tcb3 (x : Tcb) : tcbCnodeMap x (tcbCnodeIndex 3) = some x.tcbFaultHandler := by
  unfold tcbCnodeMap
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]

theorem vfh_tcb6 (x : Tcb) : tcbCnodeMap x (tcbCnodeIndex 6) = none := by
  unfold tcbCnodeMap
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]

theorem vfh_len3 : (tcbCnodeIndex 3).length = 3 := by decide
theorem vfh_len6 : (tcbCnodeIndex 6).length = 3 := by decide
theorem vfh_36 : tcbCnodeIndex 6 ≠ tcbCnodeIndex 3 := by decide

/-- **VfhAll in the cap view.** -/
def VfhV (σ : State Unit) : Prop :=
  ∀ p c, capOpt (σ.kheap p) (tcbCnodeIndex 3) = some c → capOpt (σ.kheap p) (tcbCnodeIndex 6) = none →
    validFaultHandler c

/-- A CNode object whose (view) caps hold index 3 also holds index 6. -/
theorem vfh_cnode6 {sz : Nat} {cs : CnodeContents} {c : Cap}
    (h3 : capOpt (some (.cnode sz cs)) (tcbCnodeIndex 3) = some c) :
    capOpt (some (.cnode sz cs)) (tcbCnodeIndex 6) ≠ none := by
  simp only [capOpt] at h3 ⊢
  by_cases hw : wellFormedCnodeN sz cs
  · rw [if_pos hw] at h3 ⊢
    have hd3 : tcbCnodeIndex 3 ∈ dom cs := by simp only [dom, Set.mem_ofPred_eq]; rw [h3]; simp
    have hw' := hw
    unfold wellFormedCnodeN at hw'
    rw [hw'] at hd3
    have hd6 : tcbCnodeIndex 6 ∈ dom cs := by
      rw [hw']; simp only [Set.mem_setOf_eq] at hd3 ⊢; rw [vfh_len6]; rw [vfh_len3] at hd3; exact hd3
    simpa [dom] using hd6
  · rw [if_neg hw] at h3; cases h3

theorem vfhV_iff (σ : State Unit) : VfhV σ ↔ VfhAll σ := by
  constructor
  · intro h p x hp
    have := h p x.tcbFaultHandler (by rw [hp, capOpt_tcb, vfh_tcb3]) (by rw [hp, capOpt_tcb, vfh_tcb6])
    exact this
  · intro h p c h3 h6
    cases hk : σ.kheap p with
    | none => rw [hk] at h3; cases h3
    | some o =>
      rw [hk] at h3 h6
      cases o with
      | tcb x =>
        rw [capOpt_tcb, vfh_tcb3] at h3; cases h3; exact h p x hk
      | cnode sz cs => exact absurd h6 (vfh_cnode6 h3)
      | _ => cases h3

/-- The written slot is a TCB's fault-handler slot (view form). -/
def vfh_Bad (σ : State Unit) (sl : CslotPtr) : Prop :=
  sl.2 = tcbCnodeIndex 3 ∧ capOpt (σ.kheap sl.1) (tcbCnodeIndex 6) = none

/-- No slot holding a cap in `σ` is empty in `σ'`. -/
def DomK (σ σ' : State Unit) : Prop :=
  ∀ p l, capOpt (σ'.kheap p) l = none → capOpt (σ.kheap p) l = none

theorem DomK.refl (σ : State Unit) : DomK σ σ := fun _ _ h => h
theorem DomK.trans {σ1 σ2 σ3 : State Unit} (h1 : DomK σ1 σ2) (h2 : DomK σ2 σ3) : DomK σ1 σ3 :=
  fun p l h => h1 p l (h2 p l h)

theorem vfh_Bad.back {σ σ' : State Unit} (hd : DomK σ σ') {sl : CslotPtr} (h : vfh_Bad σ' sl) : vfh_Bad σ sl :=
  ⟨h.1, hd _ _ h.2⟩

theorem vfh_notBad_old {σ : State Unit} (h : VfhV σ) {sl : CslotPtr} {c : Cap}
    (hc : capOpt (σ.kheap sl.1) sl.2 = some c) (hn : ¬ validFaultHandler c) : ¬ vfh_Bad σ sl := by
  rintro ⟨e, h6⟩
  rw [e] at hc
  exact hn (h _ _ hc h6)

theorem vfh_notBad_idx {σ : State Unit} {sl : CslotPtr} (h : sl.2 ≠ tcbCnodeIndex 3) : ¬ vfh_Bad σ sl :=
  fun hb => h hb.1

theorem vfh_notBad_full {σ : State Unit} {sl : CslotPtr}
    (h : ∀ l : CnodeIndex, l.length = sl.2.length → capOpt (σ.kheap sl.1) l ≠ none) : ¬ vfh_Bad σ sl := by
  rintro ⟨e, h6⟩
  exact h (tcbCnodeIndex 6) (by rw [e, vfh_len6, vfh_len3]) h6

/-! ## CnDom: every CNode cap names a full CNode (carried, vfh2) -/

/-- The object `p` holds every slot of length `r` (view form of l4v's
`cap_table_at r p`). -/
def CnFull (σ : State Unit) (p : ObjRef) (r : Nat) : Prop :=
  ∀ l : CnodeIndex, l.length = r → capOpt (σ.kheap p) l ≠ none

/-- A cap that is a CNode cap names a full CNode of its radix. -/
def CnOk (σ : State Unit) (c : Cap) : Prop := ∀ p r g, c = .cnodeCap p r g → CnFull σ p r

/-- **CnDom** (l4v `valid_objs`/`caps_of_state_valid` + `valid_cap_def`'s
`CNodeCap ⇒ cap_table_at`, view form): every CNode cap in a slot names an
object holding every slot of the cap's radix. A carried invariant (not a
premise): boot (`boot_cnDom`), the frames (a `WLH` predicate), the cap
writers (each written cap `CnOk`: copied / derived from a slot cap, which
keeps a CNode cap's object and radix (`CnSame`), or a fresh CNode's cap). -/
abbrev CnDom (σ : State Unit) : Prop := ∀ (sl : CslotPtr) (c : Cap), capOpt (σ.kheap sl.1) sl.2 = some c → CnOk σ c

theorem CnFull.mono {σ σ' : State Unit} (hd : DomK σ σ') {p : ObjRef} {r : Nat} (h : CnFull σ p r) :
    CnFull σ' p r := fun l hl e => h l hl (hd _ _ e)

theorem CnOk.mono {σ σ' : State Unit} (hd : DomK σ σ') {c : Cap} (h : CnOk σ c) : CnOk σ' c :=
  fun p r g e => (h p r g e).mono hd

theorem cnOk_of_nc {σ : State Unit} {c : Cap} (h : ∀ p r g, c ≠ .cnodeCap p r g) : CnOk σ c :=
  fun p r g e => (h p r g e).elim

theorem cnOk_null {σ : State Unit} : CnOk σ .nullCap := cnOk_of_nc fun _ _ _ h => by cases h

theorem cnOk_zombie {σ : State Unit} (r : ObjRef) (b : Option Nat) (n : Nat) : CnOk σ (.zombie r b n) :=
  cnOk_of_nc fun _ _ _ h => by cases h

/-- `c'` is no CNode cap or a CNode cap of `c`'s object and radix. -/
def CnSame (c c' : Cap) : Prop := ∀ p r g, c' = .cnodeCap p r g → ∃ g', c = .cnodeCap p r g'

theorem CnOk.same {σ : State Unit} {c c' : Cap} (h : CnOk σ c) (hs : CnSame c c') : CnOk σ c' := by
  intro p r g e
  obtain ⟨g', e'⟩ := hs p r g e
  exact h p r g' e'

theorem cnSame_refl (c : Cap) : CnSame c c := fun p r g e => ⟨g, e⟩

theorem cnSame_nc {c c' : Cap} (h : ∀ p r g, c' ≠ .cnodeCap p r g) : CnSame c c' :=
  fun p r g e => (h p r g e).elim

theorem cnDom_of_caps {σ σ' : State Unit} (e : ∀ p l, capOpt (σ'.kheap p) l = capOpt (σ.kheap p) l)
    (h : CnDom σ) : CnDom σ' := by
  intro sl c hc p r g hpr l hl
  rw [e]
  rw [e] at hc
  exact h sl c hc p r g hpr l hl

theorem cnDom_view {σ σ' : State Unit} (e : hV σ' = hV σ) (h : CnDom σ) : CnDom σ' :=
  cnDom_of_caps (fun p l => hV_cap e p l) h

instance : WLH CnDom := wlh_of_hV fun _ _ e h => cnDom_view e h

/-- **CnDom at boot**: every cap of `initASt` is null. -/
theorem boot_cnDom : CnDom (initASt (Z := Unit)) := by
  intro sl c hc p r g e
  subst e
  exfalso
  obtain ⟨o, l⟩ := sl
  dsimp only at hc
  simp only [initASt, initKheap, Function.update_apply] at hc
  split_ifs at hc <;>
    first
    | (simp [capOpt] at hc; done)
    | (simp only [capOpt] at hc; done)
    | (simp only [capOpt, emptyCnode] at hc; split_ifs at hc <;> simp_all; done)
    | (simp only [capOpt, tcbCnodeMap, Function.update_apply] at hc; split_ifs at hc <;> simp_all; done)

/-- The working predicate: `VfhV` and `CnDom` now, no slot of the anchor emptied. -/
def VS (σ0 σ : State Unit) : Prop := VfhV σ ∧ DomK σ0 σ ∧ CnDom σ

theorem VS.refl {σ : State Unit} (h : VfhV σ ∧ CnDom σ) : VS σ σ := ⟨h.1, DomK.refl σ, h.2⟩
theorem VS.trans {σ1 σ2 σ3 : State Unit} (h1 : VS σ1 σ2) (h2 : VS σ2 σ3) : VS σ1 σ3 :=
  ⟨h2.1, h1.2.1.trans h2.2.1, h2.2.2⟩
theorem VS.cur {σ0 σ : State Unit} (h : VS σ0 σ) : VfhV σ ∧ CnDom σ := ⟨h.1, h.2.2⟩

/-- A cap read from a slot is `CnOk`. -/
theorem VS.cnOk {σ0 σ : State Unit} (h : VS σ0 σ) {sl : CslotPtr} {c : Cap}
    (hc : capOpt (σ.kheap sl.1) sl.2 = some c) : CnOk σ c := h.2.2 sl c hc

theorem vfhV_view {σ σ' : State Unit} (e : hV σ' = hV σ) (h : VfhV σ) : VfhV σ' := by
  intro p c h3 h6; rw [hV_cap e] at h3 h6; exact h p c h3 h6

theorem domK_view {σ σ' : State Unit} (e : hV σ' = hV σ) : DomK σ σ' := by
  intro p l h; rw [hV_cap e] at h; exact h

instance : WLH VfhV := wlh_of_hV fun _ _ e h => vfhV_view e h

instance (σ0 : State Unit) : WLH (VS σ0) :=
  wlh_of_hV fun _ _ e h => ⟨vfhV_view e h.1, h.2.1.trans (domK_view e), cnDom_view e h.2.2⟩

/-- Everything a frame function of the family keeps. -/
abbrev VK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ0, IK (VS σ0) m
abbrev VKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := ∀ σ0, IKE (VS σ0) m

/-- A `VK` step from a `VfhV` state. -/
theorem VK.step {α : Type} {m : NonDet (State Unit) α} (h : VK m) {σ : State Unit} (hσ : VfhV σ ∧ CnDom σ) :
    ∀ x ∈ (m σ).1, VS σ x.2 := fun x hx => h σ σ (VS.refl hσ) x hx

/-- Re-anchoring: a pinned proof at the current state lifts to any anchor. -/
theorem vs_reanchor {α : Type} {m : NonDet (State Unit) α} {σ0 σ : State Unit} (h0 : VS σ0 σ)
    (h : IKp (VS σ) σ m) : ∀ x ∈ (m σ).1, VS σ0 x.2 :=
  fun x hx => h0.trans (h (VS.refl h0.cur) x hx)

/-! ## `set_cap` -/

/-- The caps after `set_cap`: the slot updated, everything else kept. -/
theorem vfh_setCap_view {c : Cap} {o : ObjRef} {r : CnodeIndex} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setCap (Z := Unit) c (o, r) σ).1) (p : ObjRef) (l : CnodeIndex) :
    capOpt (x.2.kheap p) l = if p = o ∧ l = r then some c else capOpt (σ.kheap p) l := by
  unfold setCap at hx
  dsimp only at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap o = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap o with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  have key : ∀ k', (∀ cref, capOpt (some k') cref = Function.update (capOpt (some k)) r (some c) cref) →
      x ∈ (setObject (Z := Unit) o k' σ).1 →
      capOpt (x.2.kheap p) l = if p = o ∧ l = r then some c else capOpt (σ.kheap p) l := by
    intro k' hk' hx'
    rw [Ipc.setObject_out hx']
    dsimp only
    by_cases hp : p = o
    · subst hp
      rw [Function.update_self, hk', hk]
      by_cases hr : l = r
      · subst hr; rw [Function.update_self, if_pos ⟨rfl, rfl⟩]
      · rw [Function.update_of_ne hr, if_neg (fun h => hr h.2)]
    · rw [Function.update_of_ne hp, if_neg (fun h => hp h.1)]
  have pb : ∀ o', x ∈ ((pure o' >>= fun obj' => setObject (Z := Unit) o obj') σ).1 →
      x ∈ (setObject (Z := Unit) o o' σ).1 := by
    intro o' hx'; obtain ⟨z, hz, hx'⟩ := hx'; rw [Set.mem_singleton_iff.1 hz] at hx'; exact hx'
  have fb : ∀ (f : KernelObject → NonDet (State Unit) Unit), x ∈ ((NonDet.fail >>= f) σ).1 → False := by
    intro f hx'; obtain ⟨z, hz, -⟩ := hx'; exact hz
  cases k with
  | cnode sz cs =>
    dsimp only at hx
    split at hx
    · rename_i hc
      exact key _ (vih_capOpt_cnode_set c hc) (pb _ hx)
    · exact (fb _ hx).elim
  | tcb t =>
    dsimp only at hx
    repeat' split at hx
    all_goals first
      | exact (fb _ hx).elim
      | (rename_i h; subst h
         first
          | exact key _ (vih_capOpt_tcb_set t (i := 0) (by decide) c) (pb _ hx)
          | exact key _ (vih_capOpt_tcb_set t (i := 1) (by decide) c) (pb _ hx)
          | exact key _ (vih_capOpt_tcb_set t (i := 2) (by decide) c) (pb _ hx)
          | exact key _ (vih_capOpt_tcb_set t (i := 3) (by decide) c) (pb _ hx)
          | exact key _ (vih_capOpt_tcb_set t (i := 4) (by decide) c) (pb _ hx)
          | exact key _ (vih_capOpt_tcb_set t (i := 5) (by decide) c) (pb _ hx))
  | _ => dsimp only at hx; exact (fb _ hx).elim

theorem vfh_setCap_domK {c : Cap} {sl : CslotPtr} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setCap (Z := Unit) c sl σ).1) : DomK σ x.2 := by
  obtain ⟨o, r⟩ := sl
  intro p l h
  rw [vfh_setCap_view hx p l] at h
  split at h
  · cases h
  · exact h

/-- **`set_cap` keeps `VfhV` and `CnDom`** when the slot is no fault-handler
slot or the cap is a valid fault handler, and the cap is `CnOk`. -/
theorem vfh_setCap_step {c : Cap} {sl : CslotPtr} {σ : State Unit} (h : VfhV σ) (hd : CnDom σ)
    (hc : vfh_Bad σ sl → validFaultHandler c) (hk : CnOk σ c) : ∀ x ∈ (setCap (Z := Unit) c sl σ).1, VS σ x.2 := by
  obtain ⟨o, r⟩ := sl
  intro x hx
  have dk := vfh_setCap_domK hx
  refine ⟨fun p c' h3 h6 => ?_, dk, fun sl' c' h' => ?_⟩
  · have h6' := dk p _ h6
    rw [vfh_setCap_view hx p] at h3
    split at h3
    · rename_i e
      obtain ⟨rfl, rfl⟩ := e
      cases h3
      exact hc ⟨rfl, h6'⟩
    · exact h p c' h3 h6'
  · obtain ⟨p, l⟩ := sl'
    rw [vfh_setCap_view hx p l] at h'
    split at h'
    · cases h'; exact hk.mono dk
    · exact (hd (p, l) _ h').mono dk

/-- `set_cap` as a `VS` leaf, the side conditions at the anchor. -/
theorem vs_setCap {σ0 : State Unit} {c : Cap} {sl : CslotPtr} (hc : vfh_Bad σ0 sl → validFaultHandler c)
    (hk : CnOk σ0 c) : IK (VS σ0) (setCap (Z := Unit) c sl) := fun σ hσ x hx =>
  hσ.trans (vfh_setCap_step hσ.1 hσ.2.2 (fun hb => hc (hb.back hσ.2.1)) (hk.mono hσ.2.1) x hx)

theorem vs_setCap_vfh {σ0 : State Unit} {c : Cap} (sl : CslotPtr) (hc : validFaultHandler c) (hk : CnOk σ0 c) :
    IK (VS σ0) (setCap (Z := Unit) c sl) := vs_setCap (fun _ => hc) hk

theorem vfh_null : validFaultHandler .nullCap := Or.inr rfl

theorem vs_setCap_null {σ0 : State Unit} (sl : CslotPtr) : IK (VS σ0) (setCap (Z := Unit) .nullCap sl) :=
  vs_setCap_vfh sl vfh_null cnOk_null

/-- `set_cap` at a slot not `Bad` at the anchor. -/
theorem vs_setCap_nb {σ0 : State Unit} {c : Cap} {sl : CslotPtr} (h : ¬ vfh_Bad σ0 sl) (hk : CnOk σ0 c) :
    IK (VS σ0) (setCap (Z := Unit) c sl) := vs_setCap (fun hb => (h hb).elim) hk

/-- A pinned proof from the current state, re-anchored. -/
theorem vs_pin {α : Type} {m : NonDet (State Unit) α} {σ0 σ : State Unit} (h0 : VS σ0 σ) (h : IK (VS σ) m) :
    ∀ x ∈ (m σ).1, VS σ0 x.2 :=
  fun x hx => h0.trans (h σ (VS.refl h0.cur) x hx)

/-! ## State fields `VS` does not read -/

theorem vs_of_kheap {σ0 σ σ' : State Unit} (hk : σ'.kheap = σ.kheap) (h : VS σ0 σ) : VS σ0 σ' := by
  refine ⟨fun p c h3 h6 => ?_, fun p l hl => h.2.1 p l ?_, cnDom_of_caps (fun p l => by rw [hk]) h.2.2⟩
  · rw [hk] at h3 h6; exact h.1 p c h3 h6
  · rw [hk] at hl; exact hl

theorem vs_modify_kheap {σ0 : State Unit} {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    IK (VS σ0) (NonDet.modify g) := ik_modify fun σ h => vs_of_kheap (hg σ) h

theorem vs_setCdt {σ0 : State Unit} (t : Cdt) : IK (VS σ0) (setCdt (Z := Unit) t) := by
  unfold setCdt
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact vs_of_kheap rfl hσ

theorem vs_updateCdt {σ0 : State Unit} (f : Cdt → Cdt) : IK (VS σ0) (updateCdt (Z := Unit) f) := by
  unfold updateCdt
  exact ik_bind (ik_gets _) fun _ => vs_setCdt _

theorem vs_setOriginal {σ0 : State Unit} (sl : CslotPtr) (b : Bool) : IK (VS σ0) (setOriginal (Z := Unit) sl b) := by
  unfold setOriginal
  exact ik_bind (ik_gets _) fun _ => ik_modify fun _ h => vs_of_kheap rfl h

theorem vs_doExtendedOp {σ0 : State Unit} (eop : DetExtMonad Unit) : IK (VS σ0) (doExtendedOp (Z := Unit) eop) :=
  ik_doExtendedOp (fun _ _ h => vs_of_kheap rfl h) eop

theorem vs_setIrqState {σ0 : State Unit} (st : IrqState) (i : Irq) : IK (VS σ0) (setIrqState (Z := Unit) st i) := by
  intro σ hσ x hx
  obtain ⟨hk, -⟩ := setIrqState_out hx
  exact vs_of_kheap hk hσ

end

end Fl4Proofs.P3.SInv
