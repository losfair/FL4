/-
P3 (DESIGN.md §9), invariant line G1 (vfh2): **the IPC cap transfer keeps
`VS`** with no outside fact (spec side only, outside the JAtZ cone).

* `vfh_okv_lookupExtraCaps`: the extra caps are slot caps (`CnOk` by `CnDom`).
* `vfh_getReceiveSlots`: the receive slot is a target slot of a looked-up CNode
  cap, so full (`vfh_lookupSlotForCnodeOp`), hence no fault-handler slot.
* `vs_transferCaps` (caps `CnOk` at a state with the same caps),
  **`vs_doNormalTransfer : VK (doNormalTransfer …)`**: the extra caps are looked
  up in the same transfer, and every step between the lookup and the inserts
  keeps the caps (`hV`).
-/
import Fl4Proofs.P3.SpecInvVfhD
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

theorem VS.view {σ0 s s' : State Unit} (e : hV s' = hV s) (h : VS σ0 s) : VS σ0 s' :=
  ⟨vfhV_view e h.1, h.2.1.trans (domK_view e), cnDom_view e h.2.2⟩

theorem vfh_okv_lookupExtraCaps (σ0 : State Unit) (hd : CnDom σ0) (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    OkV σ0 (fun caps : List (Cap × CslotPtr) => ∀ c ∈ caps, CnOk σ0 c.1) (lookupExtraCaps (Z := Unit) t b mi) := by
  unfold lookupExtraCaps
  refine okv_bind (okv_frame fun v => ike_liftE (P := fun s => hV s = v) (hv_getExtraCptrs _ _)) fun cptrs _ => ?_
  refine okv_mapME (Pr := fun c : Cap × CslotPtr => CnOk σ0 c.1) (fun cptr => ?_) cptrs
  unfold capFaultOnFailure
  exact vfh_okv_handleE (okv_mono (vfh_lookupCapAndSlot σ0 hd _ _) fun r h => h.1) (fun e s0 => okdAt_throw _)

/-- **The receive slots are full slots.** -/
theorem vfh_getReceiveSlots (σ0 : State Unit) (hd : CnDom σ0) (t : ObjRef) (b : Option ObjRef) (s : State Unit)
    (hs : hV s = hV σ0) :
    ∀ y ∈ (getReceiveSlots (Z := Unit) t b s).1, hV y.2 = hV σ0 ∧ ∀ sl ∈ y.1, CnFull σ0 sl.1 sl.2.length := by
  intro y hy
  have e : hV y.2 = hV σ0 := (hv_getReceiveSlots (P := fun x => hV x = hV s) t b s rfl y hy).trans hs
  refine ⟨e, ?_⟩
  cases b with
  | none => unfold getReceiveSlots at hy; rw [Set.mem_singleton_iff.1 hy]; intro _ h; cases h
  | some buf =>
    unfold getReceiveSlots at hy
    obtain ⟨⟨ct, s1⟩, h1, hy⟩ := hy
    have e1 : hV s1 = hV σ0 := (hv_loadCapTransfer (P := fun x => hV x = hV s) _ s rfl _ h1).trans hs
    unfold emptyOnFailure NonDetE.catch at hy
    obtain ⟨⟨r, s2⟩, h2, hy⟩ := hy
    cases r with
    | error _ => rw [Set.mem_singleton_iff.1 hy]; intro _ h; cases h
    | ok l =>
      rw [Set.mem_singleton_iff.1 hy]
      have key : OkV σ0 (fun l : List CslotPtr => ∀ sl ∈ l, CnFull σ0 sl.1 sl.2.length) (do
          let cnode ← unifyFailure (Z := Unit) (lookupCap t ct.ctReceiveRoot)
          let slot ← unifyFailure (Z := Unit) (lookupTargetSlot cnode ct.ctReceiveIndex (unat ct.ctReceiveDepth))
          let cap ← NonDetE.liftE (getCap (Z := Unit) slot)
          NonDetE.whenE (cap ≠ .nullCap) (NonDetE.throwError ())
          NonDetE.returnOk [slot]) := by
        unfold unifyFailure lookupTargetSlot
        refine okv_bind (vfh_okv_handleE (vfh_lookupCap σ0 hd _ _) fun _ _ => okdAt_throw _) fun cnode hcn => ?_
        refine okv_bind (vfh_okv_handleE (vfh_lookupSlotForCnodeOp σ0 hd _ cnode _ _ hcn)
          fun _ _ => okdAt_throw _) fun sl hsl => ?_
        refine okv_bind (okv_frame fun v => by hv_auto) fun _ _ => ?_
        refine vfh_okv_whenE_bind _ _ fun _ => ?_
        exact okv_returnOk (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hsl)
      exact (key s1 e1 l s2 h2).2

/-- **`transfer_caps`** of caps that are `CnOk` at a state `σ1` with the same caps. -/
theorem vs_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (recv : ObjRef)
    (rbuf : Option ObjRef) (σ1 : State Unit) (hcs : ∀ c ∈ caps, CnOk σ1 c.1) (σ0 s : State Unit) (hs : VS σ0 s)
    (e : hV s = hV σ1) : ∀ x ∈ (transferCaps (Z := Unit) info caps ep recv rbuf s).1, VS σ0 x.2 := by
  intro x hx
  unfold transferCaps at hx
  obtain ⟨⟨slots, s1⟩, h1, hx⟩ := hx
  have hd1 : CnDom σ1 := cnDom_view e.symm hs.2.2
  obtain ⟨e1, hfull⟩ := vfh_getReceiveSlots σ1 hd1 recv rbuf s e _ h1
  have hs1 : VS σ0 s1 := hs.view (e1.trans e.symm)
  obtain ⟨⟨mi', s1'⟩, hz, hx⟩ := hx
  have hz' := Set.mem_singleton_iff.1 hz
  simp only [Prod.mk.injEq] at hz'
  obtain ⟨rfl, e'⟩ := hz'
  rw [e'] at hx
  dsimp only at hx
  cases rbuf with
  | none => rw [Set.mem_singleton_iff.1 hx]; exact hs1
  | some rb =>
    dsimp only at hx
    refine hs1.trans (vs_transferCapsLoop (σ0 := s1) ep rb 0 caps slots _ (fun sl hsl => ?_) (fun c hc => ?_) s1
      (VS.refl hs1.cur) x hx)
    · exact vfh_notBad_cnFull (cnFull_view e1 (hfull sl hsl))
    · exact cnOk_view e1 (hcs c hc)

/-- The tail of `do_normal_transfer` after the extra-cap lookup. -/
theorem vs_dnt_tail (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (receiver : ObjRef)
    (rbuf : Option ObjRef) (mi : MessageInfo) (caps : List (Cap × CslotPtr)) (σ0 s1 s2 : State Unit)
    (hs2 : VS σ0 s2) (e2 : hV s2 = hV s1) (hcs : ∀ c ∈ caps, CnOk s1 c.1) :
    ∀ x ∈ ((do
      let mrsTransferred ← copyMrs (Z := Unit) sender sbuf receiver rbuf mi.miLength
      let mi' ← transferCaps mi caps ep receiver rbuf
      setMessageInfo receiver
          { miLength := mrsTransferred, miExtraCaps := mi'.miExtraCaps, miCapsUnwrapped := mi'.miCapsUnwrapped,
            miLabel := mi.miLabel }
      asUser receiver (setRegister badge_register badge)) s2).1, VS σ0 x.2 := by
  intro x hx
  obtain ⟨⟨mt, s3⟩, h3, hx⟩ := hx
  have e3 : hV s3 = hV s2 := hv_copyMrs (P := fun y => hV y = hV s2) _ _ _ _ _ s2 rfl _ h3
  have hs3 : VS σ0 s3 := hs2.view e3
  obtain ⟨⟨mi', s4⟩, h4, hx⟩ := hx
  have hs4 : VS σ0 s4 := vs_transferCaps mi caps ep receiver rbuf s1 hcs σ0 s3 hs3 (e3.trans e2) _ h4
  exact (ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _ : IK (VS σ0) _) s4 hs4 x hx

/-- **`do_normal_transfer` keeps `VS`** (no outside fact). -/
theorem vs_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (receiver : ObjRef) (rbuf : Option ObjRef) : VK (doNormalTransfer (Z := Unit) sender sbuf ep badge grant receiver rbuf) := by
  intro σ0 σ hσ x hx
  unfold doNormalTransfer at hx
  obtain ⟨⟨mi, s1⟩, h1, hx⟩ := hx
  have e1 : hV s1 = hV σ := hv_getMessageInfo (P := fun y => hV y = hV σ) _ σ rfl _ h1
  have hs1 : VS σ0 s1 := hσ.view e1
  dsimp only at hx
  cases grant
  · simp only [Bool.false_eq_true, ↓reduceIte] at hx
    obtain ⟨⟨caps, s2⟩, h2, hx⟩ := hx
    have h2' := Set.mem_singleton_iff.1 h2
    simp only [Prod.mk.injEq] at h2'
    obtain ⟨hc, hs⟩ := h2'
    rw [hc, hs] at hx
    exact vs_dnt_tail sender sbuf ep badge receiver rbuf mi [] σ0 s1 s1 hs1 rfl (fun c h => by cases h) x hx
  · simp only [↓reduceIte] at hx
    obtain ⟨⟨caps, s2⟩, h2, hx⟩ := hx
    unfold NonDetE.catch at h2
    obtain ⟨⟨r, s'⟩, hr, h2⟩ := h2
    have e' : hV s' = hV s1 := hv_lookupExtraCaps (P := fun y => hV y = hV s1) _ _ _ s1 rfl _ hr
    cases r with
    | ok a =>
      have h2' := Set.mem_singleton_iff.1 h2
      simp only [Prod.mk.injEq] at h2'
      obtain ⟨hc, hs⟩ := h2'
      rw [hc, hs] at hx
      exact vs_dnt_tail sender sbuf ep badge receiver rbuf mi a σ0 s1 s' (hs1.view e') e'
        (vfh_okv_lookupExtraCaps s1 hs1.2.2 _ _ _ s1 rfl a s' hr).2 x hx
    | error _ =>
      have h2' := Set.mem_singleton_iff.1 h2
      simp only [Prod.mk.injEq] at h2'
      obtain ⟨hc, hs⟩ := h2'
      rw [hc, hs] at hx
      exact vs_dnt_tail sender sbuf ep badge receiver rbuf mi [] σ0 s1 s' (hs1.view e') e'
        (fun c h => by cases h) x hx

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vs_doNormalTransfer _ _ _ _ _ _ _ _)

end

end Fl4Proofs.P3.SInv
