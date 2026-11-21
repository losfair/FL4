/-
P3 (DESIGN.md §9), untyped: **the Untyped decode at `J`** (`Retype` of a RAM
untyped cap, native object types).

FL4's `untyped::decode` (crates/fl4-core/src/untyped.rs `decode`) makes no
write before `set_thread_state(Restart)`: every refusal leaves FL4's state and
arch state as they were, so `JAt` holds after it from `JAtZ` at the start, and
the spec refuses with a related error (`untyped_decode_refines_fl4`, l4v
`decode_untyped_invocation`). What is left is the invocation itself, from the
decoded arguments (`RetCtx`): the restart and `untyped::retype` (reset of a
childless used region, the untyped cap's new free index, `create_new_objects`)
against l4v `invoke_untyped` (`reset_untyped_cap`, `retype_region`,
`createNewObjects`, the cap insertion).

* `UtRetPostJ`: the invocation's outcome at `J`: a spec outcome of the
  restart and `invoke_untyped` related by the CSpace relations, `DomRel`,
  `MdbOKV`, and `JAt` after (`JAtPre` after a preemption in the reset).
* `JUtRetHyp` [W]: the retype after the restart ends in `UtRetPostJ`, from
  the decoded arguments (`RetCtx`, RAM untyped `dev = false`). l4v: the
  refinement `invoke_untyped_corres` with `invoke_untyped_invs`. Open because
  there is no XTop retype producer: `XTopAt` after the retype needs the
  object sets re-indexed (the reset's region dropped from `Z.th`, `H`, the
  sets and the spec's heap; the new objects added), see handoff/utj.md.
* `decode_invocation_untypedJ`: the Untyped cap's `XCapP` at `JAt`/`JAtPre`
  from `JAtZ`, the decode's errors proved, the success path `JUtRetHyp`.
  Device untypeds (losfair/FL4#34) and the VT-x object types (14 to 18) stay
  outside (XTopJointEntry's `JPath`: `JCapOpen`, `JVtxScope`).
-/
import Fl4Proofs.P3.XTopJointCnDel
import Fl4Proofs.P3.UntypedDecode
import Fl4Proofs.P3.IrqIssue
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **An untyped invocation's outcome at `J`**: the spec's restart and
`invoke_untyped inv` have an outcome of FL4's kind (done, or preempted in the
reset), related by the CSpace relations, `DomRel` and `MdbOKV`, with `JAt`
after (`JAtPre` if preempted): `TopPostDMXP`'s success branch for
`invokeUntyped inv`. -/
def UtRetPostJ (AR : A → Fl4Spec.Cr3 → Prop) (σ : Fl4Spec.State Unit) (blk call don : Bool)
    (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeUntyped inv)).run σ1).1, (∃ th' G',
      ((res.1 = .Ok () ∧ y.1 = .ok []) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
      DomRel (L.mem res.2.1) (L.ksb res.2.1) y.2 ∧ MdbOKV (L.ksb res.2.1) (L.mem res.2.1) G') ∧
      (if res.1 = .Err .Preempted then JAtPre (L := L) arI AR res.2.1 res.2.2 y.2
        else JAt (L := L) arI AR res.2.1 res.2.2 y.2)

/-- **[W] The retype of a RAM untyped at `J`** (l4v `invoke_untyped_corres`
with `invoke_untyped_invs`; sub-steps `reset_untyped_cap`, `retype_region`,
`createNewObjects` and the cap insertion): from the decoded arguments
(`RetCtx` at the decode's start, `dev = false`), the restart and
`untyped::retype` end in `UtRetPostJ` for the decoded invocation. Narrowed
from the whole decode (`JCapOpen`): the decode's refusals are proved
(`decode_invocation_untypedJ`); FL4 makes no write before the restart. -/
def JUtRetHypD (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (sl : Fl4Spec.CslotPtr) (p sb fi : U64) (dev : Bool) (ct : U64) (blk call don : Bool) (argsU : List U64) : Prop :=
  ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
    argsU.head? = some nt → RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r reset fiv →
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr sl) reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us
        dest off win dev) ⦃ res =>
      UtRetPostJ (L := L) arI AR σ blk call don (.retype sl reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev)
        res ⦄

/-- `JUtRetHypD` of a RAM untyped cap (`dev = false`). -/
abbrev JUtRetHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (sl : Fl4Spec.CslotPtr) (p sb fi ct : U64) (blk call don : Bool) (argsU : List U64) : Prop :=
  JUtRetHypD (L := L) arI AR th s ar σ sl p sb fi false ct blk call don argsU

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **An untyped cap's decode at `J`** (RAM or device: `untyped_decode_refines_fl4` is generic in the device flag; the invocation is `JUtRetHypD` at the cap's flag): `XCapP` at `JAt` (`JAtPre` if
preempted). The decode's refusals (wrong label, too few arguments, a bad
type or size, the destination lookup, a non-empty window, not enough
memory) leave FL4's state and arch state unchanged with the spec's related
error (`untyped_decode_refines_fl4`), so `JAt` from `J`; the invocation is
`JUtRetHyp` [W]. Taken as at the other J decodes: the front end's label and
extra slot [W], the native types (`hNative`: the VT-x types are
`JVtxScope`), `retypeFanOutLimit` [P]. -/
theorem decode_invocation_untypedJ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (argsU : List U64)
    (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hNative : ∀ x, argsU.head? = some x → x.val < 14 ∨ 19 ≤ x.val)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (p sb fi : U64) {dev : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : JUtRetHypD (L := L) arI AR Z.th s ar σ sl p sb fi dev ct blk call don argsU) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPre (L := L) arI AR) s ar σ lbl length (cslotAddr sl)
      (.Untyped p sb fi dev) blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hX0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (untyped_decode_refines_fl4 arI Z.th s ar σ Z.G hSR hV hP hM hC hI lbl slbl hlbl length buf ct
    hct argsU hlen hargs hNative _ sl rfl hAs p sb fi dev hc extra x0 hx0 _ hex hfan
    (fun inv res => UtRetPostJ (L := L) arI AR σ blk call don inv res) hR) ?_
  rintro res (⟨e, e', rfl, h1, h2⟩ | ⟨inv, hrun, σ1, hst, y, hy, hrel, hx⟩)
  · exact TopPostDMX.errP ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, hX0⟩
  · exact Or.inr ⟨.invokeUntyped inv, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, y, hy, hrel, hx⟩

end

end

end Fl4Proofs.P3
