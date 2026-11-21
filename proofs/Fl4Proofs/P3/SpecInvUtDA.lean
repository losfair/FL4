/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut3): **the decode's facts
for `UtInv'`, the arch decode and the dispatcher** (`okv_fl4Decode`; see
SpecInvUtD).
-/
import Fl4Proofs.P3.SpecInvUtD
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- Steps of a decode none of whose results is a MakePool. -/
macro "okv_noasid" : tactic => `(tactic| repeat' (first
  | exact okv_throw _ | exact okv_throw' _ | exact okv_liftE_fail
  | (exact okv_returnOk trivial) | (exact okv_pure trivial)
  | contradiction
  | (refine okv_returnOk_bind ?_) | (refine okv_pure_bind ?_)
  | (exact okv_liftME (okv_triv fun _ => trivial))
  | (refine okv_bind_uk (fun _ => by uk_auto) fun _ => ?_)
  | (refine okv_ite ?_ ?_) | split | (dsimp only) | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE)
  | ik_unfold))

set_option maxHeartbeats 8000000 in
/-- **The x64 arch decode**: MakePool's checks (`MpOK`), every other result unconstrained. -/
theorem okv_archDecode {w : UView} (label : Data) (args : List Data) (xs : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (hex : ∀ p ∈ ex, w.2.1 p.2 = some p.1) :
    OkV w (fun i => ArchOKV w (.spec i)) (archDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  cases cap
  case asidControlCap =>
    simp only [archDecodeInvocation]
    split
    · split
      · rename_i hlen
        generalize hq : the ex[0]? = q
        obtain ⟨untyped, parentSlot⟩ := q
        dsimp only
        have hpu : w.2.1 parentSlot = some untyped := by
          have h0 : ex[0]? = some ex[0] := List.getElem?_eq_getElem (by omega)
          have hm : ex[0] ∈ ex := List.mem_iff_getElem?.2 ⟨0, h0⟩
          have := hex _ hm
          rw [h0] at hq; simp only [the] at hq
          rw [hq] at this; exact this
        refine okv_bind_uk (fun _ => by uk_auto) fun _ => okv_returnOk_bind (okv_whenE_bind fun _ =>
          okv_bind_uk (fun _ => by uk_auto) fun _ => okv_returnOk_bind ?_)
        split
        · rename_i p n f
          refine okv_returnOk_bind ?_
          dsimp only
          refine okv_bind (Q := fun fr : ObjRef => n = pageBits ∧ fr = p ∧ ∀ c, w.2.2.1 c ≠ some parentSlot)
            (fun _ => by uk_auto) ?_ fun fr hfr => ?_
          · split
            · rename_i hn
              exact okv_bind (fun _ => uk_ensureNoChildren _) (okv_ensureNoChildren _) fun _ hk => okv_returnOk ⟨hn, rfl, hk⟩
            · exact okv_throw _
          obtain ⟨hn, rfl, hk⟩ := hfr
          refine okv_bind_uk (fun _ => uk_lookupTargetSlot _ _ _) fun destSlot => ?_
          refine okv_bind_uk (fun _ => uk_ensureEmpty _) fun _ => okv_returnOk ?_
          refine ⟨false, f, ?_, hk⟩
          rw [hpu, hn]; rfl
        · exact okv_throw_bind _
      · exact okv_throw _
    · exact okv_throw _
  all_goals (simp only [archDecodeInvocation]; okv_noasid)

set_option maxHeartbeats 4000000 in
theorem okv_fl4ArchDecode {w : UView} (label : Data) (args : List Data) (xs : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (hex : ∀ p ∈ ex, w.2.1 p.2 = some p.1) :
    OkV w (ArchOKV w) (fl4ArchDecodeInvocation (Z := Unit) label args xs cte cap ex) := by
  unfold fl4ArchDecodeInvocation
  split
  all_goals repeat' (first
    | (exact okv_liftME (okv_triv fun _ => trivial))
    | (exact okv_liftME (okv_archDecode label args xs cte _ ex hex))
    | (refine okv_ite ?_ ?_))

set_option maxHeartbeats 4000000 in
/-- **Every decoded invocation satisfies `InvOKV`**, given the shell's lookups:
the invoked slot holds the invoked cap and every extra cap is in its slot. -/
theorem okv_fl4Decode {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (hc : w.2.1 sl = some cap)
    (hex : ∀ p ∈ ex, w.2.1 p.2 = some p.1) :
    OkV w (InvOKV w) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | untypedCap d p n f =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_decodeUntyped label args sl _ hc)
  | cnodeCap r b g =>
    unfold fl4DecodeInvocation
    exact okv_ite (okv_throw _) (okv_liftME (okv_decodeCnode label args _ _))
  | irqHandlerCap irq =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_decodeIrqHandler label irq ex)
  | archObjectCap ac =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_fl4ArchDecode label args ci sl ac ex hex)
  | _ =>
    unfold fl4DecodeInvocation
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_)
      | (unfold fl4DecodeTcbInvocation)
      | (dsimp only)
      | split)

end

end Fl4Proofs.P3.SInvU
