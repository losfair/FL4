/-
Capability access, the capability derivation tree, and the refill unblock
check (MCS).

Ports, in theory order:
- `spec/abstract/CSpaceAcc_A`;
- `spec/abstract/Sporadic_A`.

The notations of CSpaceAcc_A (`t ⊢ p cdt_parent_of c` and friends) are
plain definitions here; Sporadic_A's `thm` checks are not ported.
-/
import Fl4Spec.KHeap
import Mathlib.Logic.Relation

namespace Fl4Spec

open Classical

noncomputable section

/-! ## CSpaceAcc_A: capability access -/

section
variable {Z : Type} [StateExt Z]

/-- l4v: CSpaceAcc_A.get_cap: a capability may reside in a CNode or a TCB;
read it from either. -/
def getCap : CslotPtr → SMonad Z Cap := fun (oref, cref) => do
  let obj ← getObject oref
  let caps ← match obj with
    | .cnode sz cnode => do
        NonDet.assert (wellFormedCnodeN sz cnode)
        pure cnode
    | .tcb tcb => pure (tcbCnodeMap tcb)
    | _ => NonDet.fail
  NonDet.assertOpt (caps cref)

/-- l4v: CSpaceAcc_A.set_cap. -/
def setCap (cap : Cap) : CslotPtr → SMonad Z Unit := fun (oref, cref) => do
  let obj ← getObject oref
  let obj' ← match obj with
    | .cnode sz cn =>
        if cref ∈ dom cn ∧ wellFormedCnodeN sz cn
        then pure (KernelObject.cnode sz (Function.update cn cref (some cap)))
        else NonDet.fail
    | .tcb tcb =>
        if cref = tcbCnodeIndex 0 then
          pure (KernelObject.tcb { tcb with tcbCtable := cap })
        else if cref = tcbCnodeIndex 1 then
          pure (KernelObject.tcb { tcb with tcbVtable := cap })
        else if cref = tcbCnodeIndex 2 then
          pure (KernelObject.tcb { tcb with tcbIpcframe := cap })
        else if cref = tcbCnodeIndex 3 then
          pure (KernelObject.tcb { tcb with tcbFaultHandler := cap })
        else if cref = tcbCnodeIndex 4 then
          pure (KernelObject.tcb { tcb with tcbTimeoutHandler := cap })
        else if cref = tcbCnodeIndex 5 then
          pure (KernelObject.tcb { tcb with tcbEpt := cap })
        else
          NonDet.fail
    | _ => NonDet.fail
  setObject oref obj'

/-- l4v: CSpaceAcc_A.ensure_empty: ensure a capability slot is empty. -/
def ensureEmpty (slot : CslotPtr) : SEMonad Z Unit := do
  let cap ← NonDetE.liftE (getCap slot)
  NonDetE.whenE (cap ≠ .nullCap) (NonDetE.throwError .deleteFirst)

/-! ## CSpaceAcc_A: the capability derivation tree -/

/-- l4v: CSpaceAcc_A.set_cdt. -/
def setCdt (t : Cdt) : SMonad Z Unit := do
  let s ← NonDet.get
  NonDet.put { s with cdt := t }

/-- l4v: CSpaceAcc_A.update_cdt. -/
def updateCdt (f : Cdt → Cdt) : SMonad Z Unit := do
  let t ← NonDet.gets fun s : State Z => s.cdt
  setCdt (f t)

/-- l4v: CSpaceAcc_A.set_original: set the original flag of a slot. -/
def setOriginal (slot : CslotPtr) (v : Bool) : SMonad Z Unit := do
  let r ← NonDet.gets fun s : State Z => s.isOriginalCap
  NonDet.modify fun s => { s with isOriginalCap := Function.update r slot v }

end

/-- l4v: CSpaceAcc_A.is_cdt_parent. -/
def isCdtParent (t : Cdt) (p c : CslotPtr) : Prop := t c = some p

/-- l4v: CSpaceAcc_A.cdt_parent_rel. -/
def cdtParentRel (t : Cdt) : Set (CslotPtr × CslotPtr) := {pc | isCdtParent t pc.1 pc.2}

/-- l4v: CSpaceAcc_A.parent_of (`abbreviation`, `t ⊢ p cdt_parent_of c`,
`t ⊨ p ↝ c`). -/
abbrev parentOf (t : Cdt) (p c : CslotPtr) : Prop := (p, c) ∈ cdtParentRel t

/-- l4v: CSpaceAcc_A.parent_of_trancl (`abbreviation`,
`t ⊢ x cdt_parent_of⁺ y`, `t ⊨ x → y`): the transitive closure. -/
abbrev parentOfTrancl (t : Cdt) (x y : CslotPtr) : Prop := Relation.TransGen (parentOf t) x y

/-- l4v: CSpaceAcc_A.parent_of_rtrancl (`abbreviation`,
`t ⊢ x cdt_parent_of* y`, `t ⊨ x →* y`): the reflexive transitive
closure. -/
abbrev parentOfRtrancl (t : Cdt) (x y : CslotPtr) : Prop := Relation.ReflTransGen (parentOf t) x y

/-- l4v: CSpaceAcc_A.descendants_of: the descendants of a slot in the CDT. -/
def descendantsOf (p : CslotPtr) (t : Cdt) : Set CslotPtr := {q | parentOfTrancl t p q}

/-! ## Sporadic_A -/

section
variable {Z : Type} [StateExt Z]

/-- l4v: Sporadic_A.is_round_robin. -/
def isRoundRobin (scPtr : ObjRef) : SMonad Z Bool := do
  let sc ← getSchedContext scPtr
  return decide (sc.scPeriod = 0)

/-- l4v: Sporadic_A.refill_pop_head. -/
def refillPopHead (scPtr : ObjRef) : SMonad Z Refill := do
  let head ← getRefillHead scPtr
  updateSchedContext scPtr (scRefillsUpdate List.tail)
  return head

/-- l4v: Sporadic_A.refill_head_overlapping. -/
def refillHeadOverlapping (scPtr : ObjRef) : RMonad Z Bool := do
  let sc ← readSchedContext scPtr
  Lookup.oreturn (decide (sc.scRefills.length > 1 ∧
    (the sc.scRefills.tail.head?).rTime ≤ (refillHd sc).rTime + (refillHd sc).rAmount))

/-- l4v: Sporadic_A.update_refill_hd. -/
def updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : SMonad Z Unit :=
  updateSchedContext scPtr (scRefillsUpdate fun refills => f (the refills.head?) :: refills.tail)

end

/-- l4v: Sporadic_A.can_merge_refill. -/
def canMergeRefill (r1 r2 : Refill) : Prop := r2.rTime ≤ r1.rTime + r1.rAmount

/-- l4v: Sporadic_A.merge_refill. -/
def mergeRefill (r1 r2 : Refill) : Refill := { rTime := r1.rTime, rAmount := r2.rAmount + r1.rAmount }

section
variable {Z : Type} [StateExt Z]

/-- l4v: Sporadic_A.merge_overlapping_refills. -/
def mergeOverlappingRefills (scPtr : ObjRef) : SMonad Z Unit := do
  let head ← refillPopHead scPtr
  updateRefillHd scPtr (mergeRefill head)

/-- l4v: Sporadic_A.refill_head_overlapping_loop. -/
def refillHeadOverlappingLoop (scPtr : ObjRef) : SMonad Z Unit :=
  NonDet.whileLoop (fun _ s => the (refillHeadOverlapping scPtr s) = true)
    (fun _ => mergeOverlappingRefills scPtr) ()

/-- l4v: Sporadic_A.refill_unblock_check. -/
def refillUnblockCheck (scPtr : ObjRef) : SMonad Z Unit := do
  let robin ← isRoundRobin scPtr
  let ready ← getScRefillReady scPtr
  NonDet.when (ready ∧ ¬robin) <| do
    let ct ← NonDet.gets fun s : State Z => s.curTime
    updateRefillHd scPtr fun r => { r with rTime := ct }
    NonDet.modify fun s => { s with reprogramTimer := true }
    refillHeadOverlappingLoop scPtr

/-- l4v: Sporadic_A.if_cond_refill_unblock_check: call
`refill_unblock_check` under one of several guards. `active`: `none` for
constant bandwidth, `some true` for sporadic and active, `some false` for
sporadic. `asst`: `none` for no test on `cur_sc`, `some true` for an
assertion that the pointer is not `cur_sc` (currently a test, as `some
false`), `some false` for a test that it is not `cur_sc`. -/
def ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : SMonad Z Unit :=
  NonDet.maybeM (fun scp => do
    let sc ← getSchedContext scp
    let curScPtr ← NonDet.gets fun s : State Z => s.curSc
    let guard ← pure (match active with
      | none => ¬sc.scSporadic
      | some true => sc.scSporadic ∧ scActive sc
      | some false => sc.scSporadic = true)
    NonDet.when (guard ∧ (asst = some false → scp ≠ curScPtr)) <|
      NonDet.when (asst = some true → scp ≠ curScPtr) <| refillUnblockCheck scp) scOpt

/-- l4v: Sporadic_A.if_sporadic_cur_sc_assert_refill_unblock_check
(`abbreviation`). -/
abbrev ifSporadicCurScAssertRefillUnblockCheck (scOpt : Option ObjRef) : SMonad Z Unit :=
  ifCondRefillUnblockCheck scOpt (some false) (some true)

/-- l4v: Sporadic_A.if_sporadic_and_active_refill_unblock_check
(`abbreviation`). -/
abbrev ifSporadicAndActiveRefillUnblockCheck (scOpt : Option ObjRef) : SMonad Z Unit :=
  ifCondRefillUnblockCheck scOpt (some true) none

/-- l4v: Sporadic_A.if_sporadic_cur_sc_test_refill_unblock_check
(`abbreviation`). -/
abbrev ifSporadicCurScTestRefillUnblockCheck (scOpt : Option ObjRef) : SMonad Z Unit :=
  ifCondRefillUnblockCheck scOpt (some false) (some false)

/-- l4v: Sporadic_A.if_sporadic_active_cur_sc_test_refill_unblock_check
(`abbreviation`). -/
abbrev ifSporadicActiveCurScTestRefillUnblockCheck (scOpt : Option ObjRef) : SMonad Z Unit :=
  ifCondRefillUnblockCheck scOpt (some true) (some false)

/-- l4v: Sporadic_A.if_sporadic_active_cur_sc_assert_refill_unblock_check
(`abbreviation`). -/
abbrev ifSporadicActiveCurScAssertRefillUnblockCheck (scOpt : Option ObjRef) : SMonad Z Unit :=
  ifCondRefillUnblockCheck scOpt (some true) (some true)

/-- l4v: Sporadic_A.if_constant_bandwidth_refill_unblock_check
(`abbreviation`). -/
abbrev ifConstantBandwidthRefillUnblockCheck (scOpt : Option ObjRef) : SMonad Z Unit :=
  ifCondRefillUnblockCheck scOpt none none

end

end

end Fl4Spec
