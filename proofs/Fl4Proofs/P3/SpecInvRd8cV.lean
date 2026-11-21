/-
P3 (DESIGN.md §9), invariant line G1 (rd8c): **the lookups and the decode keep
every TCB's state, fault and SC binding, every SC and the time** (spec side
only, outside the `JAtZ` cone; KENTRY-PLAN rd8b handoff 2).

`BKv σ` is that view (`tcbV`: a TCB's state, fault and SC; epq1's `scAt`: the SC
object at `p`, with its size; `cur_time`); `BKK V m := IK (BK V) m`. It carries
the decode's `BindRel` (rd8b: an SC bind / `decode_update_sc` sees both ends
unbound and a blocked TCB's new SC released) from the decode's start to its
outcome. The lemmas are epq1's `VZ` family (SpecInvEqV, the functions below the
lookups and `fl4DecodeInvocation`) with the view replaced (sed of SpecInvEqV,
proofs/scratch/rd8c/mkv.sh, untracked); hand leaves: `bk_setObject` (an object
neither a TCB nor an SC / CNode: by `a_type` the old one is neither), the TCB
writers `bk_threadSet` (keeping the three fields), `bk_archThreadSet`,
`bk_asUser`, `bk_setMrs` (register / buffer writes only), `bk_setSimpleKo`.
-/
import Fl4Proofs.P3.SpecInvEqV
import Fl4Proofs.P3.SpecInvRd8cB
open Classical

namespace Fl4Proofs.P3.SInvR.B8c
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvE

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-! ## The view -/

/-- A TCB's state, fault and SC. -/
def tcbV : Option KernelObject → Option (ThreadState × Option Fault × Option ObjRef)
  | some (.tcb x) => some (x.tcbState, x.tcbFault, x.tcbSchedContext)
  | _ => none

abbrev BKw := (ObjRef → Option (ThreadState × Option Fault × Option ObjRef)) ×
  (ObjRef → Option (SchedContext × Nat)) × Time

/-- The view. -/
def BKv (σ : State Unit) : BKw := (fun q => tcbV (σ.kheap q), scAt σ, σ.curTime)

def BK (V : BKw) (σ : State Unit) : Prop := BKv σ = V

abbrev BKK (V : BKw) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (BK V) m
abbrev BKKE (V : BKw) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (BK V) m

variable {V : BKw}

theorem tcbV_none {o : KernelObject} (h : ∀ x, o ≠ .tcb x) : tcbV (some o) = none := by
  cases o with
  | tcb x => exact absurd rfl (h x)
  | _ => rfl

theorem bkv_put {σ : State Unit} {p : ObjRef} {k o : KernelObject} (hk : σ.kheap p = some k)
    (hko : ∀ y n, k ≠ .schedContext y n) (ho : ∀ y n, o ≠ .schedContext y n) (ht : tcbV (some o) = tcbV (some k)) :
    BKv { σ with kheap := Function.update σ.kheap p (some o) } = BKv σ := by
  unfold BKv
  rw [scAt_put hk hko ho]
  congr 1
  funext q
  by_cases e : q = p
  · subst e; dsimp only; rw [Function.update_self, hk]; exact ht
  · dsimp only; rw [Function.update_of_ne e]

theorem bk_setObject (p : ObjRef) (o : KernelObject) (ho : NSC o) (hot : ∀ x, o ≠ .tcb x) :
    BKK V (setObject (Z := Unit) p o) := by
  intro σ hσ y hy
  obtain ⟨k, hk, ht, e⟩ := mem_setObjectV hy
  rw [e]
  have ho' : ∀ y n, o ≠ .schedContext y n := fun y n e => by subst e; exact ho
  have hkt : ∀ x, k ≠ .tcb x := by
    rintro x rfl
    obtain ⟨y', hy'⟩ := SInvQ.q1_aType_tcb (o := o) (by rw [← ht]; rfl)
    exact hot y' hy'
  unfold BK at hσ ⊢
  rw [bkv_put hk (nsc_old ht ho) ho' (by rw [tcbV_none hot, tcbV_none hkt])]
  exact hσ

/-- A TCB write keeping the state, fault and SC. -/
theorem bk_setTcb {σ : State Unit} {p : ObjRef} {x x' : Tcb} (hk : σ.kheap p = some (.tcb x))
    {y : Unit × State Unit} (hy : y ∈ (setObject (Z := Unit) p (.tcb x') σ).1)
    (hx : x'.tcbState = x.tcbState ∧ x'.tcbFault = x.tcbFault ∧ x'.tcbSchedContext = x.tcbSchedContext) :
    BKv y.2 = BKv σ := by
  obtain ⟨k, hk', -, e⟩ := mem_setObjectV hy
  rw [hk] at hk'; cases hk'
  rw [e]
  refine bkv_put hk (fun _ _ h => by cases h) (fun _ _ h => by cases h) ?_
  simp only [tcbV, hx.1, hx.2.1, hx.2.2]

theorem bk_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbState = x.tcbState ∧ (f x).tcbFault = x.tcbFault ∧ (f x).tcbSchedContext = x.tcbSchedContext) :
    BKK V (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => ?_
  intro hσ y hy
  unfold BK at hσ ⊢
  rw [bk_setTcb (getTcb_kheap hx) hy (hf x)]; exact hσ

theorem bk_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : BKK V (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  refine ik_getsThe_bind fun x σ hx => ?_
  intro hσ y hy
  unfold BK at hσ ⊢
  rw [bk_setTcb (getTcb_kheap hx) hy ⟨rfl, rfl, rfl⟩]; exact hσ

theorem bk_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : BKK V (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  intro hσ y hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  obtain ⟨⟨a, uc'⟩, s2⟩ := z2
  obtain ⟨-, e2⟩ := hz2
  simp only at e2; subst e2
  try dsimp only at hy
  obtain ⟨z3, hz3, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz3
  obtain ⟨z4, hz4, hy⟩ := hy
  have h4 := bk_setTcb (getTcb_kheap hx) hz4 ⟨rfl, rfl, rfl⟩
  obtain rfl := Set.mem_singleton_iff.1 hy
  unfold BK at hσ ⊢
  rw [h4]; exact hσ

macro "bk_side" : tactic => `(tactic| first
  | trivial
  | (intro _ _ h; exact h)
  | (intro _ h; exact h))

macro "bk0_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine ik_doMachineOp ?_ _); bk_side)
  | ((with_reducible refine ik_doExtendedOp ?_ _); bk_side)
  | with_reducible exact ik_getObject _
  | ((with_reducible refine bk_setObject _ _ ?_ ?_); first | trivial | (intro _ h; cases h))
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem bk_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : BKK V (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  intro hσ y hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  have h3 : BK V z3.2 := by
    unfold BK at hσ ⊢; rw [bk_setTcb (getTcb_kheap hx) hz3 ⟨rfl, rfl, rfl⟩]; exact hσ
  refine (?_ : BKK V _) z3.2 h3 y hy
  bk0_auto

theorem bk_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    BKK V (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo setObject
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hsimp, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨hk3, hs3⟩ := mem_getObject hy3
  obtain ⟨obj', y3⟩ := y3
  simp only at hk3 hs3 hsimp; subst hs3
  rw [hk] at hk3; cases hk3
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  have hn : ∀ o : KernelObject, (aType o = .aEndpoint ∨ aType o = .aNTFN ∨ aType o = .aReply) →
      ∀ y n, o ≠ .schedContext y n := by
    intro o h y n e; subst e; simp only [aType] at h; split_ifs at h <;> simp at h
  have hnt : ∀ o : KernelObject, (aType o = .aEndpoint ∨ aType o = .aNTFN ∨ aType o = .aReply) →
      ∀ x, o ≠ .tcb x := by
    intro o h x e; subst e; simp [aType] at h
  simp only [isSimpleType, Set.mem_insert_iff, Set.mem_singleton_iff] at hsimp
  have hs2 : aType (f e) = .aEndpoint ∨ aType (f e) = .aNTFN ∨ aType (f e) = .aReply := by rw [← hty]; exact hsimp
  unfold BK at hσ ⊢
  rw [bkv_put hk (hn obj hsimp) (hn (f e) hs2) (by rw [tcbV_none (hnt _ hs2), tcbV_none (hnt _ hsimp)])]
  exact hσ

syntax "bk_leaf" : tactic
macro_rules | `(tactic| bk_leaf) => `(tactic| fail "no bk_leaf")

macro "bk_auto" : tactic => `(tactic| repeat' (first | bk_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| bk_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); bk_side))
macro_rules | `(tactic| bk_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); bk_side))
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| bk_leaf) => `(tactic| ((with_reducible refine bk_setObject _ _ ?_ ?_); first | trivial | (intro _ h; cases h)))
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_setSimpleKo _ _ _)
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_archThreadSet _ _)
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_asUser _ _)
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_setMrs _ _ _)

theorem bk_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : BKK V (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_threadGet _ _)

theorem bk_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : BKK V (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getTcbObjRef _ _)

theorem bk_getCap (a0 : CslotPtr) : BKK V (getCap (Z := Unit) a0) := by
  unfold getCap; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getCap _)

theorem bk_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : BKK V (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_lookupIpcBuffer _ _)

theorem bk_setMessageInfo (thread : ObjRef) (info : MessageInfo) : BKK V (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_setMessageInfo _ _)

theorem bk_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : BKK V (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_storeWordOffs _ _ _)

theorem bk_replyFromKernel (thread : ObjRef) (x : Data × List Data) : BKK V (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_replyFromKernel _ _)

theorem bk_getSchedContext (ptr : ObjRef) : BKK V (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getSchedContext _)

theorem bk_getThreadState (ref : ObjRef) : BKK V (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getThreadState _)

theorem bk_ensureEmpty (slot : CslotPtr) : BKKE V (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_ensureEmpty _)

theorem bk_isIoportRangeFree (f l : IoPort) : BKK V (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_isIoportRangeFree _ _)

theorem bk_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : BKKE V m) : BKKE V (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; bk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible refine bk_lookupErrorOnFailure _ _ ?_)

theorem bk_resolveAddressBits' (p : Cap × CapRef) : BKKE V (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by bk_auto)) fun nc => ?_
        split
        · exact bk_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_resolveAddressBits' _)

theorem bk_resolveAddressBits (a0 : Cap × CapRef) : BKKE V (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_resolveAddressBits _)

theorem bk_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : BKKE V (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_lookupSlotForCnodeOp _ _ _ _)

theorem bk_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : BKKE V (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_lookupTargetSlot _ _ _)

theorem bk_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : BKKE V (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeIoportControlInvocation _ _ _ _ _)

theorem bk_getAsidPool (ptr : ObjRef) : BKK V (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getAsidPool _)

theorem bk_findVspaceForAsid (asid : Asid) : BKKE V (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_findVspaceForAsid _)

theorem bk_getPdpt (ptr : ObjRef) : BKK V (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getPdpt _)

theorem bk_getPdpte (ptr : ObjRef) : BKK V (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getPdpte _)

theorem bk_isFinalCap (cap : Cap) : BKK V (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_isFinalCap _)

theorem bk_getPml4 (ptr : ObjRef) : BKK V (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getPml4 _)

theorem bk_getPml4e (ptr : ObjRef) : BKK V (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getPml4e _)

theorem bk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : BKKE V (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_lookupPdptSlot _ _)

theorem bk_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : BKKE V (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodePageDirectoryInvocation _ _ _ _ _)

theorem bk_checkVpAlignment (sz : VMPageSize) (vptr : Word) : BKKE V (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_checkVpAlignment _ _)

theorem bk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : BKKE V (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_lookupPdSlot _ _)

theorem bk_getPd (ptr : ObjRef) : BKK V (getPd (Z := Unit) ptr) := by
  unfold getPd; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getPd _)

theorem bk_getPde (ptr : ObjRef) : BKK V (getPde (Z := Unit) ptr) := by
  unfold getPde; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getPde _)

theorem bk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : BKKE V (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_lookupPtSlot _ _)

theorem bk_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : BKKE V (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_createMappingEntries _ _ _ _ _ _)

theorem bk_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : BKKE V (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_ensureSafeMapping _)

theorem bk_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : BKKE V (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodePageInvocation _ _ _ _ _)

theorem bk_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : BKKE V (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodePageTableInvocation _ _ _ _ _)

theorem bk_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : BKKE V (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodePdptInvocation _ _ _ _ _)

theorem bk_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : BKKE V (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_ensurePortOperationAllowed _ _ _)

theorem bk_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : BKKE V (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodePortInvocation _ _ _)

theorem bk_ensureNoChildren (cslotPtr : CslotPtr) : BKKE V (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_ensureNoChildren _)

theorem bk_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : BKK V (selectExt (Z := Unit) a S) := by
  unfold selectExt; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_selectExt _ _)

theorem bk_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : BKKE V (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_archDecodeInvocation _ _ _ _ _ _)

theorem bk_getIrqState (irq : Irq) : BKK V (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getIrqState _)

theorem bk_isIrqActive (irq : Irq) : BKK V (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_isIrqActive _)

theorem bk_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : BKKE V (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_archDecodeIrqControlInvocation _ _ _ _)

theorem bk_archDeriveCap (c : ArchCap) : BKKE V (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_archDeriveCap _)

theorem bk_getPt (ptr : ObjRef) : BKK V (getPt (Z := Unit) ptr) := by
  unfold getPt; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getPt _)

theorem bk_getPte (ptr : ObjRef) : BKK V (getPte (Z := Unit) ptr) := by
  unfold getPte; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getPte _)

theorem bk_getTcbQueue (d : Domain) (prio : Priority) : BKK V (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getTcbQueue _ _)

theorem bk_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : BKK V (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_setTcbQueue _ _ _)

theorem bk_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : BKK V (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_tcbSchedAction _ _)

theorem bk_tcbReleaseRemove (tcbPtr : ObjRef) : BKK V (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_tcbReleaseRemove _)

theorem bk_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : BKK V (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getSimpleKo _ _)

theorem bk_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : BKK V (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getSkObjRef _ _ _)

theorem bk_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : BKK V (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getScObjRef _ _)

theorem bk_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : BKKE V m) : BKKE V (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; bk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible refine bk_capFaultOnFailure _ _ _ ?_)

theorem bk_loadWordOffs (ptr : ObjRef) (offs : Nat) : BKK V (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_loadWordOffs _ _)

theorem bk_getMessageInfo (thread : ObjRef) : BKK V (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getMessageInfo _)
theorem bk_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : BKK V (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; bk_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getExtraCptrs _ _)

theorem bk_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : BKKE V (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_lookupSlotForThread _ _)

theorem bk_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : BKKE V (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_lookupCapAndSlot _ _)

theorem bk_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : BKKE V (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_lookupExtraCaps _ _ _)

theorem bk_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : BKKE V m) : BKK V (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; bk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible refine bk_constOnFailure _ _ ?_)

theorem bk_deriveCap (slot : CslotPtr) (cap : Cap) : BKKE V (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_deriveCap _ _)

theorem bk_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : BKKE V (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_checkHandlerEp _ _)

theorem bk_checkPrio (newPrio : Data) (authTcb : ObjRef) : BKKE V (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_checkPrio _ _)

theorem bk_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : BKKE V (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_checkValidIpcBuffer _ _)

theorem bk_dataToObjType (type : Data) : BKKE V (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_dataToObjType _)

theorem bk_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : BKKE V (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeBindNotification _ _)

theorem bk_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : BKKE V (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_lookupPivotSlot _ _ _)

theorem bk_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : BKKE V (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_lookupSourceSlot _ _ _)

theorem bk_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : BKKE V (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeCnodeInvocation _ _ _ _)

theorem bk_slotCapLongRunningDelete (slot : CslotPtr) : BKK V (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_slotCapLongRunningDelete _)

theorem bk_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : BKKE V (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeCvSpace _ _ _ _)
theorem bk_subframeNode (nodeCap : Cap) (index depth : Data) : BKKE V (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_subframeNode _ _ _)

theorem bk_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : BKKE V (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeDeriveSubframe _ _ _ _)

theorem bk_decodeDomainScheduleConfigure (args : List Data) : BKKE V (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeDomainScheduleConfigure _)

theorem bk_decodeDomainScheduleSetStart (args : List Data) : BKKE V (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeDomainScheduleSetStart _)

theorem bk_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : BKKE V (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeDomainSet _ _)

theorem bk_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : BKKE V (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeDomainInvocation _ _ _)

theorem bk_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : BKK V (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_fl4GetMr _ _ _)

theorem bk_fl4Arg (buf : Option ObjRef) (i : Nat) : BKKE V (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_fl4Arg _ _)

theorem bk_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : BKKE V (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeFl4ConfigureSingleStepping _ _)

theorem bk_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : BKKE V (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeFl4FpuTransfer _ _ _ _)

theorem bk_fl4CheckBpNum (bp : Data) : BKKE V (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_fl4CheckBpNum _)

theorem bk_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : BKKE V (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeFl4GetBreakpoint _ _)

theorem bk_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, BKKE V (check x0)) : BKKE V (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; bk_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible refine bk_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem bk_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : BKKE V (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeIrqControlRemapped _ _ _)

theorem bk_fl4ArchCheckIrq (irq : Data) : BKKE V (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_fl4ArchCheckIrq _)

theorem bk_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : BKKE V (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeFl4IrqControl _ _ _ _ _)

theorem bk_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : BKKE V (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeFl4SetBreakpoint _ _)

theorem bk_decodeFl4SetFlags (args : List Data) (t : ObjRef) : BKKE V (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeFl4SetFlags _ _)

theorem bk_decodeFl4SetTimer (args : List Data) (t : ObjRef) : BKKE V (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeFl4SetTimer _ _)

theorem bk_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : BKKE V (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeFl4UnsetBreakpoint _ _)

theorem bk_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : BKKE V (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeFl4TcbExt _ _ _ _ _)

theorem bk_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : BKKE V (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeIrqHandlerInvocation _ _ _)

theorem bk_getScReleased (scPtr : ObjRef) : BKK V (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getScReleased _)

theorem bk_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : BKKE V (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSchedContextBind _ _)

theorem bk_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : BKKE V (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSchedContextUnbindObject _ _)

theorem bk_decodeSchedContextYieldTo (scPtr : ObjRef) : BKKE V (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSchedContextYieldTo _)

theorem bk_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : BKKE V (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSchedContextInvocation _ _ _)

theorem bk_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : BKKE V (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSchedControlInvocationFlags _ _ _)

theorem bk_rangeCheck (v minV maxV : Word) : BKKE V (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_rangeCheck _ _ _)

theorem bk_decodeSetFlags (args : List Data) (cap : Cap) : BKKE V (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSetFlags _ _)

theorem bk_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : BKKE V (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSetIpcBuffer _ _ _ _)

theorem bk_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : BKKE V (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSetMcpriority _ _ _ _)

theorem bk_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : BKKE V (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSetPriority _ _ _ _)

theorem bk_isBlocked (thread : ObjRef) : BKK V (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_isBlocked _)

theorem bk_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : BKKE V (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeUpdateSc _ _ _)

theorem bk_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : BKKE V (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSetSchedParams _ _ _ _)

theorem bk_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : BKKE V (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSetSpace _ _ _ _)

theorem bk_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : BKKE V (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSetTimeoutEp _ _ _)

theorem bk_decodeSetTlsBase (args : List Data) (cap : Cap) : BKKE V (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeSetTlsBase _ _)

theorem bk_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : BKKE V (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeTcbConfigure _ _ _ _)

theorem bk_decodeUnbindNotification (cap : Cap) : BKKE V (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem bk_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : BKKE V (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeTcbInvocation _ _ _ _ _)

theorem bk_decodePml4Flush (cap : ArchCap) : BKKE V (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodePml4Flush _)

theorem bk_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : BKKE V (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_frameMappingSlot _ _ _ _)

theorem bk_decodeTestAndClearAccessed (cap : ArchCap) : BKKE V (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeTestAndClearAccessed _)

theorem bk_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : BKKE V (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem bk_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : BKK V (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getMrs _ _ _)

theorem bk_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : BKKE V (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem bk_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    BKKE V (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem bk_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : BKKE V (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem bk_getCapReg (reg : Register) : BKK V (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; bk_auto
macro_rules | `(tactic| bk_leaf) => `(tactic| with_reducible exact bk_getCapReg _)

end

end Fl4Proofs.P3.SInvR.B8c
