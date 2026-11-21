/-
P3 (DESIGN.md §9), invariant line G1 (ft2): **a generic object-pointwise
frame** for FaultTcbsS and the notification-queue invariant (spec side only,
outside the JAtZ cone).

* `FQ`: a per-thread predicate `R p fault state` closed under the TCB writes
  of the spec functions that wake no thread and set no fault (a fault clear,
  `set_thread_state … Inactive`, a fresh `defaultTcb`); every other TCB write
  keeps fault and state, so keeps `R` definitionally.
* `GW F S p o`: a TCB at `p` satisfies `F.R p`, a notification at `p` has its
  queue inside `S`; `OPG F S C σ`: every object satisfies `GW F S`, and the
  current thread satisfies `C` (`C := fun _ => True` for the scheduler,
  which switches threads).
* Instances (SpecInvFaultTcbsN): `F := ftlQ L` (FaultTcbsS with the
  no-fault list `L`), the exempt form for `sendFaultIpc`, the per-thread
  "no fault, not BlockedOnSend/Reply" form; `S := univ` (no constraint) or
  the queued threads of the start state (notification queues only shrink).
* Leaves: the object writers (copies of SpecInvFaultTcbsT's `tp_*` for
  `OPG`), the notification writers that keep or shrink the queue
  (`updateSkObjRef` of a field other than `ntfnObj`, `tcbNtfnDequeue`, a write
  of an idle/active notification), `setThreadState` with a state `R` allows.
  The functions are generated in SpecInvFaultTcbsG1..G6 (`fg_auto`).
-/
import Fl4Proofs.P3.SpecInvFaultTcbs
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

/-- A per-thread predicate on (pointer, fault, state), closed under the TCB
writes of the functions that wake no thread. -/
structure FQ where
  R : ObjRef → Option Fault → ThreadState → Prop
  clr : ∀ p f s, R p f s → R p none s
  st : ∀ p f s, R p f s → R p f .inactive
  dflt : ∀ p, R p none .inactive

/-- The object predicate: TCBs satisfy `F.R`, notification queues lie in `S`. -/
def GW (F : FQ) (S : Set ObjRef) (p : ObjRef) : KernelObject → Prop
  | .tcb x => F.R p x.tcbFault x.tcbState
  | .notification n => ∀ t, t ∈ n.ntfnObj.ntfnQueue → t ∈ S
  | _ => True

/-- Every object satisfies `GW F S`. -/
def OPG (F : FQ) (S : Set ObjRef) (C : ObjRef → Prop) (σ : State Unit) : Prop :=
  (∀ p o, σ.kheap p = some o → GW F S p o) ∧ C σ.curThread

abbrev FGK {α : Type} (F : FQ) (S : Set ObjRef) (C : ObjRef → Prop) (m : NonDet (State Unit) α) : Prop :=
  IK (OPG F S C) m
abbrev FGKE {ε α : Type} (F : FQ) (S : Set ObjRef) (C : ObjRef → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  IKE (OPG F S C) m

theorem ik_and {A B : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (ha : IK A m) (hb : IK B m) :
    IK (fun σ => A σ ∧ B σ) m :=
  fun σ h x hx => ⟨ha σ h.1 x hx, hb σ h.2 x hx⟩

theorem partialInv_eqG {α β : Type} [Nonempty α] {g : α → β} {b : β} {a : α} (h : partialInv g b = some a) :
    g a = b := by
  unfold partialInv at h
  split_ifs at h with hu
  cases h
  unfold The; rw [dite_eq_left hu]; exact (Classical.choose_spec hu).1

theorem mem_getSimpleKo {α : Type} [Nonempty α] {C : α → KernelObject} {p : ObjRef} {σ : State Unit}
    {y : α × State Unit} (h : y ∈ (getSimpleKo (Z := Unit) C p σ).1) : σ.kheap p = some (C y.1) ∧ y.2 = σ := by
  unfold getSimpleKo at h
  obtain ⟨y1, h1, h⟩ := h
  obtain ⟨hk, hs⟩ := mem_getObject h1
  obtain ⟨o, σ1⟩ := y1
  simp only at hk hs; subst σ1
  obtain ⟨z, ⟨-, rfl⟩, h⟩ := h
  dsimp only at h
  rcases he : partialInv C o with _ | e
  · rw [he] at h; exact h.elim
  · rw [he] at h
    rw [Set.mem_singleton_iff.1 h]
    exact ⟨by rw [hk, partialInv_eqG he], rfl⟩

/-- A `get_simple_ko` read, pinned. -/
theorem ik_getSimpleKo_bind {P : State Unit → Prop} {α β : Type} [Nonempty α] {C : α → KernelObject}
    {p : ObjRef} {k : α → NonDet (State Unit) β}
    (h : ∀ σ a, σ.kheap p = some (C a) → IKp P σ (k a)) : IK P (getSimpleKo (Z := Unit) C p >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getSimpleKo hy
  obtain ⟨a, s⟩ := y
  simp only at hs hk; subst s
  exact h σ a hk hσ x hx

section G
variable {F : FQ} {S : Set ObjRef} {C : ObjRef → Prop}

theorem opg_update {σ : State Unit} (h : OPG F S C σ) (p : ObjRef) (o : KernelObject) (ho : GW F S p o) :
    OPG F S C { σ with kheap := Function.update σ.kheap p (some o) } := by
  refine ⟨fun q x hq => ?_, h.2⟩
  dsimp only at hq
  rw [Function.update_apply] at hq
  split_ifs at hq with e
  · subst e; cases hq; exact ho
  · exact h.1 q x hq

theorem fg_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : OPG F S C σ → GW F S p o) : IKp (OPG F S C) σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨-, e2⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at e2; subst y2
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact opg_update hσ p o (ho hσ)

theorem fg_setObject (p : ObjRef) (o : KernelObject) (ho : GW F S p o) : FGK F S C (setObject (Z := Unit) p o) :=
  fun σ => fg_setObject_p p o σ (fun _ => ho)

/-- `set_simple_ko` with a new object satisfying `GW` (always, for endpoints and replies). -/
theorem fg_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α)
    (he : GW F S p (f e)) : FGK F S C (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo
  refine ik_bind (ik_getObject _) fun _ => ik_bind (ik_assert _) fun _ => ik_bind (ik_assert _) fun _ => ?_
  exact fg_setObject _ _ he

/-- `set_simple_ko`, the new object depending on the old one at the same state. -/
theorem fg_setSimpleKo_p {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) (σ : State Unit)
    (he : OPG F S C σ → GW F S p (f e)) : IKp (OPG F S C) σ (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨-, e2⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at e2; subst y2
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  exact fg_setObject_p p (f e) σ he hσ x hx

/-- `update_sk_obj_ref` of a field the object predicate does not read. -/
theorem fg_updateSkObjRef {α : Type} [Nonempty α] (Ck : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef)
    (hf : ∀ a, GW F S ref (Ck a) → GW F S ref (Ck (f (fun _ => new) a))) :
    FGK F S C (updateSkObjRef (Z := Unit) Ck f ref new) := by
  unfold updateSkObjRef
  exact ik_getSimpleKo_bind fun σ a ha => fg_setSimpleKo_p _ _ _ σ fun hσ => hf a (hσ.1 _ _ ha)

theorem removeAll_sub {t x : ObjRef} {q : List ObjRef} (h : x ∈ removeAll t q) : x ∈ q :=
  (List.mem_filter.1 h).1

/-- `tcb_ntfn_dequeue`: the queue shrinks. -/
theorem fg_tcbNtfnDequeue (t n : ObjRef) : FGK F S C (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue
  refine ik_getSimpleKo_bind (C := KernelObject.notification) fun σ a ha => ?_
  refine ikp_pure_bind (ikp_keep (fun y hy => by rw [hy.2]) fun _ => ikp_pure_bind (ikp_pure_bind ?_))
  refine fg_setSimpleKo_p _ _ _ σ fun hσ => ?_
  have h0 : ∀ x, x ∈ a.ntfnObj.ntfnQueue → x ∈ S := hσ.1 _ _ ha
  intro x hx
  simp only [ntfnObjUpdate] at hx
  split at hx
  · simp [Ntfn.ntfnQueue] at hx
  · simp only [Ntfn.ntfnQueue] at hx
    exact h0 x (removeAll_sub hx)

theorem fg_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, F.R t x.tcbFault x.tcbState → F.R t (f x).tcbFault (f x).tcbState) :
    FGK F S C (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => fg_setObject_p _ _ σ fun hσ => ?_
  exact hf x (hσ.1 _ _ (getTcb_kheap hx))

theorem fg_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : FGK F S C (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => fg_setObject_p _ _ σ fun hσ => (hσ.1 _ _ (getTcb_kheap hx) : F.R _ _ _)

theorem fg_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : FGK F S C (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (fg_setObject_p _ _ σ fun hσ => (hσ.1 _ _ (getTcb_kheap hx) : F.R _ _ _)) fun _ => ik_pure _

theorem fg_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : FGK F S C (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (fg_setObject_p _ _ σ fun hσ => (hσ.1 _ _ (getTcb_kheap hx) : F.R _ _ _)) fun _ => ?_
  ti_mach

theorem fg_setCap (c : Cap) (sl : CslotPtr) : FGK F S C (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (fg_setObject_p _ _ σ fun _ => trivial)
    · exact ikp_fail_bind
  · rename_i tcb
    have hq : OPG F S C σ → F.R o tcb.tcbFault tcb.tcbState := fun hσ => hσ.1 _ _ hk
    split
    · exact ikp_pure_bind (fg_setObject_p _ _ σ fun hσ => hq hσ)
    split
    · exact ikp_pure_bind (fg_setObject_p _ _ σ fun hσ => hq hσ)
    split
    · exact ikp_pure_bind (fg_setObject_p _ _ σ fun hσ => hq hσ)
    split
    · exact ikp_pure_bind (fg_setObject_p _ _ σ fun hσ => hq hσ)
    split
    · exact ikp_pure_bind (fg_setObject_p _ _ σ fun hσ => hq hσ)
    split
    · exact ikp_pure_bind (fg_setObject_p _ _ σ fun hσ => hq hσ)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem gw_defaultObject (p : ObjRef) {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (n : Nat)
    (d : Domain) : GW F S p (defaultObject ty dev n d) := by
  cases ty with
  | untyped => exact absurd rfl hty
  | tcbObject => exact F.dflt p
  | notificationObject => intro t ht; simp [defaultNotification, defaultNtfn, Ntfn.ntfnQueue] at ht
  | _ => trivial

theorem opg_foldr_update (ps : List ObjRef) (o : ObjRef → KernelObject) (ho : ∀ p, GW F S p (o p)) (kh : KHeap)
    (h : ∀ p x, kh p = some x → GW F S p x) :
    ∀ p x, (ps.foldr (fun p kh => Function.update kh p (some (o p))) kh) p = some x → GW F S p x := by
  induction ps with
  | nil => exact h
  | cons a ps ih =>
    intro p x hp
    simp only [List.foldr_cons, Function.update_apply] at hp
    split_ifs at hp with e
    · subst e; cases hp; exact ho _
    · exact ih p x hp

theorem fg_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oBits : Nat)
    (ty : ApiObjectType) (dev : Bool) : FGK F S C (retypeRegionWith (Z := Unit) bA ptr n oBits ty dev) := by
  unfold retypeRegionWith
  refine ik_bind (ik_pure _) fun _ => ik_bind (ik_pure _) fun ptrs => ik_bind ?_ fun _ => ik_pure _
  unfold NonDet.when
  split
  · rename_i hty
    refine ik_gets_bind fun σ => ikp_gets_bind (ikp_pure_bind (ikp_modify fun hσ => ?_))
    exact ⟨opg_foldr_update _ (fun _ => _) (fun p => gw_defaultObject p hty _ _ _) _ hσ.1, hσ.2⟩
  · exact ik_pure' _

theorem fg_retypeRegion (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType) (dev : Bool) :
    FGK F S C (retypeRegion (Z := Unit) ptr n oBits ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact fg_retypeRegionWith _ _ _ _ _ _

theorem opg_detype (D : Set ObjRef) {σ : State Unit} (h : OPG F S C σ) : OPG F S C (detype D σ) := by
  refine ⟨fun p x hp => ?_, h.2⟩
  unfold detype at hp
  dsimp only at hp
  split_ifs at hp
  exact h.1 p x hp

theorem fg_deleteObjects (ptr : Word) (bits : Nat) : FGK F S C (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  exact ik_bind (ik_doMachineOp (fun _ _ h => h) _) fun _ => ik_modify fun _ h => opg_detype _ h

theorem fg_doMachineOp {α : Type} (mop : NonDet MachineState α) : FGK F S C (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) _

theorem fg_doExtendedOp (eop : DetExtMonad Unit) : FGK F S C (doExtendedOp (Z := Unit) eop) :=
  ik_doExtendedOp (fun _ _ h => h) _

end G

set_option maxErrors 2000

/-- The side conditions of the leaves. -/
macro "fg_side" : tactic => `(tactic| first
  | (intro _ hx; exact hx)
  | (intro x hx; exact FQ.clr _ _ _ _ hx)
  | (intro _ _ hx; exact FQ.st _ _ _ _ hx)
  | trivial
  | (intro _ hx; simpa [ntfnObjUpdate, Ntfn.ntfnQueue] using hx)
  | (intro _ _ hx; exact hx)
  | (intro t ht; simp [ntfnObjUpdate, Ntfn.ntfnQueue] at ht; done))

syntax "fg_leaf" : tactic
macro_rules | `(tactic| fg_leaf) => `(tactic| fail "no fg_leaf")

macro "fg_auto" : tactic => `(tactic| repeat' (first | fg_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_doMachineOp _)
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_doExtendedOp _)
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| fg_leaf) => `(tactic| ((with_reducible refine fg_setObject _ _ ?_); fg_side))
macro_rules | `(tactic| fg_leaf) => `(tactic| ((with_reducible refine fg_setSimpleKo _ _ _ ?_); fg_side))
macro_rules | `(tactic| fg_leaf) => `(tactic| ((with_reducible refine fg_threadSet _ _ ?_); fg_side))
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archThreadSet _ _)
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_asUser _ _)
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setMrs _ _ _)
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setCap _ _)
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_deleteObjects _ _)
macro_rules | `(tactic| fg_leaf) => `(tactic| ((with_reducible refine fg_updateSkObjRef _ _ _ _ ?_); fg_side))
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbNtfnDequeue _ _)

section G2
variable {F : FQ} {S : Set ObjRef} {C : ObjRef → Prop}

/-- `set_thread_state` with a state `F.R` allows from any. -/
theorem fg_setThreadState (t : ObjRef) (ts : ThreadState) (h : ∀ f s, F.R t f s → F.R t f ts) :
    FGK F S C (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (fg_threadSet _ _ fun x hx => h _ _ hx) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; fg_auto

theorem fg_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, F.R t x.tcbFault x.tcbState → F.R t (fn v x).tcbFault (fn v x).tcbState) :
    FGK F S C (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact fg_threadSet _ _ (h _)

end G2

macro_rules | `(tactic| fg_leaf) => `(tactic| ((with_reducible refine fg_setThreadState _ _ ?_); intro _ _ hx; exact FQ.st _ _ _ _ hx))
macro_rules | `(tactic| fg_leaf) => `(tactic| ((with_reducible refine fg_optionUpdateThread _ _ _ ?_); intro _ _ hx; exact hx))

end

end Fl4Proofs.P3.SInv
