/-
P3 (DESIGN.md §9), invariant line G1 (ctq11): **`RT` across
`perform_invocation`** (spec side only).

Every arm but the untyped invocation and MakePool is a generated `rt_*` leaf
(SpecInvCqGF1..F5). Those two take sl4's perform-state facts, exactly as
`slGap` does: sl's `SPF` (its `ScLiveT`, `UtInv''`, the idle SC outside every
cap's range) with the idle thread outside every cap's range, and ut7's
`DecodedFrom` for ut8's `GapOKN` (`UtGapOK` / `MpOKN`). No new premise.
-/
import Fl4Proofs.P3.SpecInvCqGU
import Fl4Proofs.P3.SpecInvSlA
open Classical

namespace Fl4Proofs.P3.SInvQ.R11
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL

noncomputable section

set_option maxHeartbeats 2000000

set_option maxHeartbeats 8000000 in
/-- **`perform_invocation` keeps `RT`** (the untyped / MakePool arms from sl4's perform-state facts). -/
theorem rt_fl4PerformInvocation (I : ObjRef × ObjRef) (N : Irq → ObjRef) (K L : List ObjRef) (d : Prop) (t : ObjRef)
    (bl call don : Bool) (inv : Fl4Invocation) (σ : State Unit) (hR : RT σ) (hσ : SPF I K L d t N σ)
    (hI1 : IrqOutV (fun _ => I.1) (uV σ)) (hD : DecodedFrom (uV σ) inv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don inv).run σ).1, RT y.2 := by
  have hS : ScLiveT I σ := hσ.1.1.1.1
  have hU : UtInv'' σ := hσ.2.2.1.1
  have hI2 : IrqOutV (fun _ => I.2) (uV σ) := fun irq s c h => by
    have := hσ.2.2.2.2.2.2 irq s c h
    rwa [show σ.idleSc = I.2 from hσ.2.2.2.2.1] at this
  obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
  have hf : GapOKN (uV σ) inv :=
    okv_fl4DecodeG fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv _ s0 hmem
  intro y hy
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]; exact rt_invokeUntyped ui σ hR hS hU hI1 hI2 hf z hz
  | invokeArchObject ai =>
    simp only [fl4PerformInvocation] at hy
    have hok : ArchOKN (uV σ) ai := hf
    cases ai with
    | spec i =>
      cases i with
      | invokeASIDControl a =>
        cases a with
        | makePool frame slot parent base =>
          simp only [fl4ArchPerformInvocation, archPerformInvocation] at hy
          obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
          obtain ⟨z, hz, hx⟩ := hx
          rw [Set.mem_singleton_iff.1 hx]
          exact rt_makePool frame slot parent base σ hR hS hU hI1 hI2 hok z hz
      | _ =>
        refine (?_ : RTKE _) σ hR y hy
        simp only [fl4ArchPerformInvocation, archPerformInvocation]
        rt_auto
    | _ =>
      refine (?_ : RTKE _) σ hR y hy
      simp only [fl4ArchPerformInvocation, archNoReturn]
      rt_auto
  | _ =>
    refine (?_ : RTKE _) σ hR y hy
    simp only [fl4PerformInvocation]
    rt_auto

end

end Fl4Proofs.P3.SInvQ.R11
