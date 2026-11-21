/-
P3 (DESIGN.md §9), invariant line G1 (rd8d): **`do_ipc_transfer` keeps every
TCB's state, fault and SC** (spec side only, outside the JAtZ cone).

`receive_ipc`'s sender arm reads the sender's fault after `do_ipc_transfer`
and donates / wakes on it; R3 exempts a send-blocked thread holding a timeout
fault, so the sender's readiness comes from R3 at the read state, which needs
the sender still `BlockedOnSend` there. `TVv σ q := tcbV (kheap q)` (rd8c's
`tcbV`: a TCB's state, fault, SC), `TV V σ := TVv σ = V`, `TVK V m := IK (TV
V) m`. The family is ctq2's q1 family (SpecInvCqF1-F3) restricted to
`do_ipc_transfer`'s subtree with the predicate replaced
(proofs/scratch/rd8d/mkt.py, untracked); hand leaves (as SpecInvCqK's):
`tv_setObject_p` (a write of a non-TCB, or of a TCB keeping the three
fields; `a_type` pins the old object's kind), `tv_setTcb_p`, `tv_threadSet`,
`tv_archThreadSet`, `tv_asUser`, `tv_setMrs`, `tv_setCap`. Top:
**`tv_doIpcTransfer`**.
-/
import Fl4Proofs.P3.SpecInvRd8cV
open Classical

namespace Fl4Proofs.P3.SInvR.B8d
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- Every TCB's state, fault and SC (rd8c's `tcbV`). -/
def TVv (σ : State Unit) : ObjRef → Option (ThreadState × Option Fault × Option ObjRef) :=
  fun q => B8c.tcbV (σ.kheap q)

def TV (V : ObjRef → Option (ThreadState × Option Fault × Option ObjRef)) (σ : State Unit) : Prop := TVv σ = V

abbrev TVK (V : ObjRef → Option (ThreadState × Option Fault × Option ObjRef)) {α : Type}
    (m : NonDet (State Unit) α) : Prop := IK (TV V) m
abbrev TVKE (V : ObjRef → Option (ThreadState × Option Fault × Option ObjRef)) {ε α : Type}
    (m : NonDetE (State Unit) ε α) : Prop := IKE (TV V) m

variable {V : ObjRef → Option (ThreadState × Option Fault × Option ObjRef)}

theorem tv_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : ∀ x, σ.kheap p = some (.tcb x) → ∀ y, o = .tcb y →
      y.tcbState = x.tcbState ∧ y.tcbFault = x.tcbFault ∧ y.tcbSchedContext = x.tcbSchedContext) :
    IKp (TV V) σ (setObject (Z := Unit) p o) := by
  intro hσ y hy
  obtain ⟨k, hk, ht, e⟩ := SInvE.mem_setObjectV hy
  rw [e]
  unfold TV at hσ ⊢
  rw [← hσ]
  funext q
  unfold TVv
  by_cases eq : q = p
  · subst eq
    dsimp only
    rw [Function.update_self, hk]
    by_cases hot : ∃ y0, o = .tcb y0
    · obtain ⟨y0, rfl⟩ := hot
      obtain ⟨x, rfl⟩ := SInvQ.q1_aType_tcb (o := k) (by rw [ht]; rfl)
      obtain ⟨h1, h2, h3⟩ := ho x hk y0 rfl
      simp only [B8c.tcbV, h1, h2, h3]
    · have hkt : ∀ x, k ≠ .tcb x := by
        rintro x rfl
        exact hot (SInvQ.q1_aType_tcb (o := o) (by rw [← ht]; rfl))
      rw [B8c.tcbV_none (fun x e => hot ⟨x, e⟩), B8c.tcbV_none hkt]
  · dsimp only
    rw [Function.update_of_ne eq]

theorem tv_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → False) :
    TVK V (setObject (Z := Unit) p o) :=
  fun σ => tv_setObject_p p o σ fun _ _ y e => (ho y e).elim

/-- A TCB write keeping state, fault and SC. -/
theorem tv_setTcb_p (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (hy : y.tcbState = x.tcbState ∧ y.tcbFault = x.tcbFault ∧ y.tcbSchedContext = x.tcbSchedContext) :
    IKp (TV V) σ (setObject (Z := Unit) p (.tcb y)) :=
  tv_setObject_p _ _ σ fun x0 hk y' e => by
    rw [hx] at hk; cases hk; cases e; exact hy

theorem tv_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbState = x.tcbState ∧ (f x).tcbFault = x.tcbFault ∧
      (f x).tcbSchedContext = x.tcbSchedContext) :
    TVK V (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx => tv_setTcb_p _ x σ (getTcb_kheap hx) _ (hf x)

theorem tv_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) :
    TVK V (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => tv_setTcb_p _ x σ (getTcb_kheap hx) _ ⟨rfl, rfl, rfl⟩

theorem tv_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : TVK V (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (tv_setTcb_p _ x σ (getTcb_kheap hx) _ ⟨rfl, rfl, rfl⟩) fun _ => ik_pure _

macro "tv_mach" : tactic => `(tactic| repeat' (first | ik_step0 |
  (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold))

theorem tv_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : TVK V (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (tv_setTcb_p _ x σ (getTcb_kheap hx) _ ⟨rfl, rfl, rfl⟩) fun _ => ?_
  tv_mach

theorem tv_setCap (c : Cap) (sl : CslotPtr) : TVK V (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (tv_setObject_p _ _ σ fun _ _ _ e => by cases e)
    · exact ikp_fail_bind
  · rename_i tcb
    split
    · exact ikp_pure_bind (tv_setTcb_p _ tcb σ hk _ ⟨rfl, rfl, rfl⟩)
    split
    · exact ikp_pure_bind (tv_setTcb_p _ tcb σ hk _ ⟨rfl, rfl, rfl⟩)
    split
    · exact ikp_pure_bind (tv_setTcb_p _ tcb σ hk _ ⟨rfl, rfl, rfl⟩)
    split
    · exact ikp_pure_bind (tv_setTcb_p _ tcb σ hk _ ⟨rfl, rfl, rfl⟩)
    split
    · exact ikp_pure_bind (tv_setTcb_p _ tcb σ hk _ ⟨rfl, rfl, rfl⟩)
    split
    · exact ikp_pure_bind (tv_setTcb_p _ tcb σ hk _ ⟨rfl, rfl, rfl⟩)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

macro "tv_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _; exact ⟨rfl, rfl, rfl⟩)
  | (simp; done)
  | decide)

syntax "tv_leaf" : tactic
macro_rules | `(tactic| tv_leaf) => `(tactic| fail "no tv_leaf")

macro "tv_auto" : tactic => `(tactic| repeat' (first | tv_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| tv_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); tv_side))
macro_rules | `(tactic| tv_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); tv_side))
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| tv_leaf) => `(tactic| ((with_reducible refine tv_setObject _ _ ?_); tv_side))
macro_rules | `(tactic| tv_leaf) => `(tactic| ((with_reducible refine tv_threadSet _ _ ?_); tv_side))
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_archThreadSet _ _)
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_asUser _ _)
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_setMrs _ _ _)
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_setCap _ _)

/-! ## The generated family (q1's, restricted to `do_ipc_transfer`'s subtree) -/

theorem tv_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : TVK V (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_threadGet _ _)

theorem tv_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : TVK V (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_updateSchedContext _ _)

theorem tv_getCap (a0 : CslotPtr) : TVK V (getCap (Z := Unit) a0) := by
  unfold getCap; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_getCap _)

theorem tv_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : TVK V (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_lookupIpcBuffer _ _)

theorem tv_setMessageInfo (thread : ObjRef) (info : MessageInfo) : TVK V (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_setMessageInfo _ _)

theorem tv_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : TVK V (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_storeWordOffs _ _ _)

theorem tv_getSchedContext (ptr : ObjRef) : TVK V (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_getSchedContext _)

theorem tv_schedContextUpdateConsumed (scPtr : ObjRef) : TVK V (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_schedContextUpdateConsumed _)

theorem tv_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : TVKE V m) : TVKE V (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; tv_auto
  all_goals first | exact h_m
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible refine tv_lookupErrorOnFailure _ _ ?_)

theorem tv_resolveAddressBits' (p : Cap × CapRef) : TVKE V (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by tv_auto)) fun nc => ?_
        split
        · exact tv_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_resolveAddressBits' _)

theorem tv_resolveAddressBits (a0 : Cap × CapRef) : TVKE V (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_resolveAddressBits _)

theorem tv_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : TVKE V (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_lookupSlotForCnodeOp _ _ _ _)

theorem tv_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : TVKE V (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_lookupTargetSlot _ _ _)

theorem tv_ensureNoChildren (cslotPtr : CslotPtr) : TVKE V (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_ensureNoChildren _)

theorem tv_archDeriveCap (c : ArchCap) : TVKE V (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_archDeriveCap _)

theorem tv_setOriginal (slot : CslotPtr) (v : Bool) : TVK V (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_setOriginal _ _)

theorem tv_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : TVK V (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_setUntypedCapAsFull _ _ _)

theorem tv_setCdt (t : Cdt) : TVK V (setCdt (Z := Unit) t) := by
  unfold setCdt; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_setCdt _)

theorem tv_updateCdt (f : Cdt → Cdt) : TVK V (updateCdt (Z := Unit) f) := by
  unfold updateCdt; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_updateCdt _)

theorem tv_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : TVK V (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_capInsert _ _ _)

theorem tv_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : TVKE V m) : TVKE V (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; tv_auto
  all_goals first | exact h_m
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible refine tv_capFaultOnFailure _ _ _ ?_)

theorem tv_captransferFromWords (ptr : Word) : TVK V (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_captransferFromWords _)

theorem tv_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : TVK V (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_makeArchFaultMsg _ _)

theorem tv_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : TVK V (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_makeFaultMsg _ _)

theorem tv_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : TVK V (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_doFaultTransfer _ _ _ _)

theorem tv_loadWordOffs (ptr : ObjRef) (offs : Nat) : TVK V (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_loadWordOffs _ _)

theorem tv_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : TVK V (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_copyMrs _ _ _ _ _)

theorem tv_getMessageInfo (thread : ObjRef) : TVK V (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_getMessageInfo _)

theorem tv_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : TVK V (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; tv_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_getExtraCptrs _ _)

theorem tv_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : TVKE V (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_lookupSlotForThread _ _)

theorem tv_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : TVKE V (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_lookupCapAndSlot _ _)

theorem tv_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : TVKE V (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_lookupExtraCaps _ _ _)

theorem tv_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : TVKE V m) : TVK V (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; tv_auto
  all_goals first | exact h_m
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible refine tv_emptyOnFailure _ ?_)

theorem tv_loadCapTransfer (buffer : ObjRef) : TVK V (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_loadCapTransfer _)

theorem tv_lookupCap (thread : ObjRef) (ref : CapRef) : TVKE V (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_lookupCap _ _)

theorem tv_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : TVKE V m) : TVKE V (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; tv_auto
  all_goals first | exact h_m
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible refine tv_unifyFailure _ ?_)

theorem tv_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : TVK V (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_getReceiveSlots _ _)

theorem tv_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : TVKE V m) : TVK V (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; tv_auto
  all_goals first | exact h_m
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible refine tv_constOnFailure _ _ ?_)

theorem tv_deriveCap (slot : CslotPtr) (cap : Cap) : TVKE V (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_deriveCap _ _)

theorem tv_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : TVK V (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_setExtraBadge _ _ _)

theorem tv_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      TVK V (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; tv_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => tv_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | tv_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_transferCapsLoop _ _ _ _ _ _)

theorem tv_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : TVK V (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_transferCaps _ _ _ _ _)

theorem tv_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : TVK V (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_doNormalTransfer _ _ _ _ _ _ _)

theorem tv_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : TVK V (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; tv_auto
macro_rules | `(tactic| tv_leaf) => `(tactic| with_reducible exact tv_doIpcTransfer _ _ _ _ _)


end

end Fl4Proofs.P3.SInvR.B8d
