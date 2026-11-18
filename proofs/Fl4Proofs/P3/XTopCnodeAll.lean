/-
P3 (DESIGN.md §9), CSpace: **the CNode cap at `XTop`, every label**
(TopXAll's `CnodeXHyp`, the `XCap` of a CNode cap).

* `decode_invocation_cnode_illegalX`: the labels outside `CNodeRevoke ..=
  CNodeRotate` (FL4's `cnode::decode` and the spec's
  `decode_cnode_invocation` both fail with `IllegalOperation`, the state
  unchanged). MCS seL4 has no `SaveCaller`; FL4's CNode labels are 25..32.
* `decode_invocation_cnodeX`: the dispatch: Revoke and Delete
  (XTopDelW), CancelBadgedSends (`decode_invocation_cnode_cancelXI`),
  copy, mint, move, mutate, rotate (`decode_invocation_cnode_copyX`), the
  rest illegal.
-/
import Fl4Proofs.P3.XTopDelW
import Fl4Proofs.P3.XTopCnodeX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`CnodeXHyp` at the labels outside the CNode invocations**: both sides
fail with `IllegalOperation`, the state unchanged. -/
theorem decode_invocation_cnode_illegalX {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ)
    (lbl : U64) (hlo : lbl.val < 25 ∨ 32 < lbl.val) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List Fl4Spec.Data)
    (p r gs g : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl
      args ci sl excaps buffer ct := by
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
    rw [hlbl]; unfold cnodeLabelOf
    simp only [show lbl.val ≠ 25 by omega, show lbl.val ≠ 26 by omega, show lbl.val ≠ 27 by omega,
      show lbl.val ≠ 28 by omega, show lbl.val ≠ 29 by omega, show lbl.val ≠ 30 by omega,
      show lbl.val ≠ 31 by omega, show lbl.val ≠ 32 by omega, ↓reduceIte]
  have hdec := decode_illegal slbl args (absCap (.CNode p r gs g)) (excaps.map Prod.fst) σ (by rw [hg]; decide)
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold cnode.decode
    rcases hlo with h | h
    · have n1 : lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
      rw [if_pos n1]
      simp only [error.illegal, bind_ok]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err hdec, Or.inl trivial⟩, ⟨Z, hX⟩⟩
    · have n1 : ¬ lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
      have n2 : lbl > fl4_abi.label.CNodeRotate := by have := lbl_rotate_val; scalar_tac
      rw [if_neg n1, if_pos n2]
      simp only [error.illegal, bind_ok]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err hdec, Or.inl trivial⟩, ⟨Z, hX⟩⟩
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, hX⟩⟩

/-- **`CnodeXHyp`: the CNode cap at `XTop`, every label.** The premises are
the labels' (each used by its labels only):

* Revoke, Delete: the deletion's premises at `XTop` (`XFinHyps` [W],
  `XPreemptHyp` [W], `XPostDelHyp` [W]), the bound `K` on CNode sizes and
  `DelE` (`DelInv`, the fuel bound) [J];
* CancelBadgedSends: the caller's state code below 3,
  and at every `XTopAt` sets `KsApart`, `BufWordRel`, the IPC placement, the caller among
  the TCBs, the switch target ready, the endpoint of a full-rights endpoint
  cap among the endpoints [J];
* copy, mint, move, mutate, rotate: the extra caps (`ExtraRel2`), `ARMask`
  [P], `XDelNtfnHyp` [W];
* all: `XTopAt` at the typed heap with `KsApart` [J], the typed heap's TCBs
  in `Z.T` [J], the caller runnable (`CurRun`) [J]. -/
theorem decode_invocation_cnodeX [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} (hAM : ARMask arI AR) {Z : XSets} (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (hX : XTopAt (L := L) AR Z s ar σ)
    (hKA : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) (hC : CurRun σ) (hTh : ∀ t, Z.th t = some .tcb → t ∈ Z.T)
    (hDel : XDelNtfnHyp (L := L) arI AR Z.th)
    (hXF : XFinHyps (L := L) arI AR Z.th) (hXP : XPreemptHyp (L := L) arI AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th)
    (K : Nat) (hK : ∀ p r, Z.th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K) (hDE : DelE (L := L) Z.th K s σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (hroot : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .CNode p r gs g)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel2 Z.th (L.mem s) x0 x1 (excaps.map Prod.fst))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv)
    (hrun : ∀ xt, σ.kheap ct.bv = some (.tcb xt) → tsCode xt.tcbState < 3)
    (hZ : ∀ Z' : XSets, XTopAt (L := L) AR Z' s ar σ → KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s) ∧
      BufWordRel Z'.T (L.mem s) σ ∧ IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B ∧ ct ∈ Z'.T)
    (hQ : ∀ e, EpQPre σ e) (hsw : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv)
    (hE : ∀ (Z' : XSets) (e b : U64) (sl : Fl4Spec.CslotPtr), XTopAt (L := L) AR Z' s ar σ → AbsSlot Z.th sl →
      capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z'.E)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (XTop (L := L) AR) s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  by_cases hlo : lbl.val < 25 ∨ 32 < lbl.val
  · exact decode_invocation_cnode_illegalX arI s ar σ hX lbl hlo slbl hlbl length buf ct hct _ p r gs g extra excaps
      slot blk call don fp ci sl buffer
  by_cases hcp : 28 ≤ lbl.val ∧ lbl.val ≤ 32
  · exact decode_invocation_cnode_copyX arI hAM s ar σ hX hKA hC hTh hDel lbl hcp slbl hlbl length buf ct hct args
      hlen hargs p r gs g hwf hcv hroot extra x0 x1 hx0 hx1 excaps hex hact hcur slot blk call don fp ci sl buffer
  have hcase : lbl.val = 25 ∨ lbl.val = 26 ∨ lbl.val = 27 := by omega
  rcases hcase with h | h | h
  · have e : lbl = fl4_abi.label.CNodeRevoke := UScalar.eq_of_val_eq (by rw [h, lbl_revoke_val])
    subst e
    exact decode_invocation_cnode_revokeX arI s ar σ hX hKA hC hTh hXF hXP hXD K hK hK6 hDE slbl
      (by rw [hlbl]; simp [cnodeLabelOf]) length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps hact hcur
      slot blk call don fp ci sl buffer
  · have e : lbl = fl4_abi.label.CNodeDelete := UScalar.eq_of_val_eq (by rw [h, lbl_delete_val])
    subst e
    exact decode_invocation_cnode_deleteX arI s ar σ hX hKA hC hTh hXF hXP hXD K hK hK6 hDE slbl
      (by rw [hlbl]; simp [cnodeLabelOf]) length buf ct hct args hlen hargs p r gs g hwf hcv extra excaps hact hcur
      slot blk call don fp ci sl buffer
  · have e : lbl = fl4_abi.label.CNodeCancelBadgedSends := UScalar.eq_of_val_eq (by rw [h, lbl_cancel_val])
    subst e
    exact decode_invocation_cnode_cancelXI arI s ar σ hX hC slbl (by rw [hlbl]; simp [cnodeLabelOf]) length buf ct
      hct args hlen hargs p r gs g hwf hcv extra excaps hact hcur hrun hZ hQ hsw hE slot blk call don fp ci sl buffer

end

end

end Fl4Proofs.P3
