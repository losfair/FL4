/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut1): **(ii) for the
reset: after `reset_untyped_cap` no object lies in the untyped's region**
(spec side only).

* `reset_region_empty`: from a state with `UtInv` whose slot holds the untyped
  cap `(dev, b, n, fi)`, every outcome of `reset_untyped_cap` (finished or
  preempted) has no object at an address of `[b, b + 2^n)`: with `fi = 0` by
  UtFree, otherwise `delete_objects` empties the region and the rest of the
  reset (`set_cap` of the slot, `clear_memory`, `preemption_point`,
  `arch_post_reset_untyped`) adds no heap address (the frames of SpecInvUtF*).
* With `utRet_fresh_reset` (SpecInvUt) this gives (i) for a reset retype: every
  address it writes held no object.
-/
import Fl4Proofs.P3.SpecInvUtF4
import Fl4Proofs.P3.SpecInvUtW
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- No object at an address of `[b, b + 2^n)`. -/
def REmp (b : ObjRef) (n : Nat) (τ : State Unit) : Prop := ∀ q, q.toNat ∈ utR b n → (τ.kheap q).isSome = false

theorem ik_remp_of_uk {b : ObjRef} {n : Nat} {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) :
    IK (REmp b n) m :=
  ik_of_uk (fun σ σ' e hσ q hq => by
    have := congrArg (fun w : UView => w.1 q) e
    simp only [uV] at this
    rw [this]; exact hσ q hq) h

theorem ik_remp_setCap (b : ObjRef) (n : Nat) (c : Cap) (sl : CslotPtr) : IK (REmp b n) (setCap (Z := Unit) c sl) :=
  fun σ hσ x hx q hq => by rw [(setCap_out hx).1 q]; exact hσ q hq

theorem run_liftE_bind_mem {ε α β : Type} {m : NonDet (State Unit) α} {k : α → NonDetE (State Unit) ε β}
    {σ : State Unit} {y : Except ε β × State Unit} (hy : y ∈ (ExceptT.run (NonDetE.liftE m >>= k) σ).1) :
    ∃ x ∈ (m σ).1, y ∈ (ExceptT.run (k x.1) x.2).1 := by
  unfold NonDetE.liftE at hy
  rw [ExceptT.run_bind, ExceptT.run_lift] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, hz⟩ := hz
  obtain rfl := Set.mem_singleton_iff.1 hz
  exact ⟨x, hx, hy⟩

theorem run_returnOk_bind_mem {ε α β : Type} {a : α} {g : α → NonDetE (State Unit) ε β}
    {σ : State Unit} {y : Except ε β × State Unit} (hy : y ∈ (ExceptT.run (NonDetE.returnOk a >>= g) σ).1) :
    y ∈ (ExceptT.run (g a) σ).1 := by
  rw [ExceptT.run_bind] at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz
  exact hy

/-- `get_cap` reads the slot's cap (`capAt`) and keeps the state. -/
theorem getCap_capAt {sl : CslotPtr} {σ : State Unit} {x : Cap × State Unit}
    (hx : x ∈ (getCap (Z := Unit) sl σ).1) : x.2 = σ ∧ capAt σ sl = some x.1 := by
  obtain ⟨o, r⟩ := sl
  unfold getCap at hx
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨obj, z2⟩ := z
  simp only at hk hs; subst hs
  dsimp only at hx
  have fin : ∀ cs : CnodeContents, capView obj = cs → ∀ τ, τ = z2 →
      x ∈ (NonDet.assertOpt (cs r) τ).1 → x.2 = z2 ∧ capAt z2 (o, r) = some x.1 := by
    intro cs hcv τ hτ hm
    rw [hτ] at hm
    revert hm
    cases hc : cs r with
    | none => intro hm; exact hm.elim
    | some c =>
      intro hm
      obtain rfl := Set.mem_singleton_iff.1 hm
      exact ⟨rfl, by unfold capAt; simp only [hk, hcv, hc]⟩
  cases obj with
  | cnode sz cn =>
    dsimp only at hx
    obtain ⟨u, ⟨hwf, rfl⟩, hx⟩ := hx
    dsimp only at hx
    obtain ⟨w, hw, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hw
    exact fin cn (by rw [capView_cnode, if_pos hwf]) _ rfl hx
  | tcb t =>
    dsimp only at hx
    obtain ⟨w, hw, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 hw
    exact fin (tcbCnodeMap t) rfl _ rfl hx
  | _ =>
    dsimp only at hx
    obtain ⟨w, hw, -⟩ := hx
    exact hw.elim

macro "remp_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact ik_remp_setCap _ _ _ _)
  | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _)
  | (exact ik_remp_of_uk (fun _ => uk_preemptionPoint))
  | (exact ik_remp_of_uk (fun _ => uk_archPostResetUntyped _ _))
  | ik_step0 | (unfold NonDet.unless) | (unfold NonDetE.whenE)))

/-- **(ii) for the reset: no object lies in the region afterwards.** -/
theorem reset_region_empty {σ : State Unit} (hI : UtInv σ) {srcSlot : CslotPtr} {dev : Bool} {b : ObjRef}
    {n fi : Nat} (hc : capAt σ srcSlot = some (.untypedCap dev b n fi)) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) srcSlot) σ).1, ∀ q, q.toNat ∈ utR b n → y.2.kheap q = none := by
  intro y hy
  suffices h : REmp b n y.2 by
    intro q hq
    have := h q hq
    cases e : y.2.kheap q with
    | none => rfl
    | some _ => rw [e] at this; cases this
  unfold resetUntypedCap at hy
  obtain ⟨x, hx, hy⟩ := run_liftE_bind_mem hy
  obtain ⟨cap, s⟩ := x
  obtain ⟨hs, hcx⟩ := getCap_capAt hx
  simp only at hs hcx; rw [hs] at hy
  rw [hc] at hcx; cases hcx
  replace hy := run_returnOk_bind_mem hy
  replace hy := run_returnOk_bind_mem hy
  dsimp only at hy
  obtain ⟨hn, hfit⟩ := UtWf.fit (σ := σ) hI.2.1 hc
  by_cases h0 : fi = 0
  · rw [if_pos (show freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    intro q hq
    cases e : σ.kheap q with
    | none => rfl
    | some _ =>
      exfalso
      subst h0
      refine hI.1 srcSlot dev b n 0 hc q (show (σ.kheap q).isSome = true by rw [e]; rfl) ?_
      exact ⟨by have := hq.1; omega, hq.2⟩
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := run_liftE_bind_mem hy
    simp only [bitsOf, objRefOf] at hz
    have hz0 : REmp b n z.2 := by
      intro q hq
      rw [(deleteObjects_kheap hz).1 q, if_pos ((mem_delR_iff hn hfit q).2 hq)]
      rfl
    refine (?_ : IKE (REmp b n) _) z.2 hz0 y hy
    try dsimp only
    remp_auto

/-- **(i) for a reset retype**: after the reset every address the retype writes
held no object. -/
theorem utRet_fresh_after_reset {σ : State Unit} (hI : UtInv σ) {srcSlot : CslotPtr} {base rb : ObjRef}
    {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool}
    (hok : UtRetOK σ (.retype srcSlot true base rb ty sz slots dev)) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) srcSlot) σ).1,
      ∀ q ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz), y.2.kheap q = none := by
  have hok' := hok
  obtain ⟨bits, fi, hc, -⟩ := hok'
  intro y hy
  exact utRet_fresh_reset hI.2.1 hok hc (reset_region_empty hI hc y hy)

end

end Fl4Proofs.P3.SInvU
