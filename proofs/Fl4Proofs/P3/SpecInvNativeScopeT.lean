/-
P3 (DESIGN.md §9), invariant line G1 (invA): **per-TCB invariants and the
writers of TCB objects** (spec side only; imports only Fl4Spec and
SpecInvNativeScopeK).

* `TI Q σ`: every TCB of the heap satisfies `Q` (VfhAll, FaultTcbs and
  NativeScope are of this form).
* `IKp P σ m`: `IK` pinned at one start state, for the reads before a write
  (`ik_getsThe_bind`: a `getsThe` read gives its value at the pinned state).
* The TCB writers of the spec, each a leaf: `setObject` (any object with the
  new TCB satisfying `Q`), `setSimpleKo` (by the two type assertions the new
  object is an endpoint, notification or reply), `threadSet` / `archThreadSet`
  / `asUser` / `setMrs` (the old TCB read at the same state, so `Q` of the new
  one from `Q` of the old one), `setCap` (a CNode slot, or one of the six TCB
  slots), the creation of objects (`retypeRegion(With)`: the default objects)
  and `deleteObjects` (`detype` removes objects).
-/
import Fl4Proofs.P3.SpecInvNativeScopeK
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

/-- Every TCB of the heap satisfies `Q`. -/
def TI (Q : Tcb → Prop) (σ : State Unit) : Prop := ∀ p x, σ.kheap p = some (.tcb x) → Q x

/-- `IK` at one start state. -/
def IKp (P : State Unit → Prop) (σ : State Unit) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  P σ → ∀ x, x ∈ (m σ).1 → P x.2

section Pin
variable {P : State Unit → Prop}

theorem ik_getsThe_bind {α β : Type} {g : State Unit → Option α} {k : α → NonDet (State Unit) β}
    (h : ∀ a σ, g σ = some a → IKp P σ (k a)) : IK P (NonDet.getsThe g >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  unfold NonDet.getsThe at hy
  cases e : g σ with
  | none => rw [e] at hy; exact hy.elim
  | some a =>
    rw [e] at hy
    have hy' : y = (a, σ) := Set.mem_singleton_iff.1 hy
    subst hy'
    exact h a σ e hσ x hx

theorem ikp_of_ik {α : Type} {m : NonDet (State Unit) α} (h : IK P m) (σ : State Unit) : IKp P σ m :=
  fun hσ x hx => h σ hσ x hx

theorem ikp_keep {α β : Type} {σ : State Unit} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : ∀ y, y ∈ (m σ).1 → y.2 = σ) (hg : ∀ a, IKp P σ (g a)) : IKp P σ (m >>= g) := by
  intro hσ x ⟨y, hy, hx⟩
  have e := hm y hy
  obtain ⟨a, s⟩ := y
  simp only at e; subst e
  exact hg a hσ x hx

theorem ikp_pure_bind {α β : Type} {σ : State Unit} {a : α} {g : α → NonDet (State Unit) β}
    (h : IKp P σ (g a)) : IKp P σ ((pure a : NonDet (State Unit) α) >>= g) := by
  intro hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h hσ x hx

theorem ikp_fail_bind {α β : Type} {σ : State Unit} {g : α → NonDet (State Unit) β} :
    IKp P σ ((NonDet.fail : NonDet (State Unit) α) >>= g) := by
  intro _ x ⟨y, hy, _⟩; exact hy.elim

theorem ik_gets_bind {α β : Type} {g : State Unit → α} {k : α → NonDet (State Unit) β}
    (h : ∀ σ, IKp P σ (k (g σ))) : IK P (NonDet.gets g >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ hσ x hx

theorem ikp_gets_bind {α β : Type} {σ : State Unit} {g : State Unit → α} {k : α → NonDet (State Unit) β}
    (h : IKp P σ (k (g σ))) : IKp P σ (NonDet.gets g >>= k) := by
  intro hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h hσ x hx

theorem ikp_modify {σ : State Unit} {f : State Unit → State Unit} (h : P σ → P (f σ)) :
    IKp P σ (NonDet.modify f) := by
  intro hσ x hx; rw [Set.mem_singleton_iff.1 hx]; exact h hσ

theorem ikp_bind {α β : Type} {σ : State Unit} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : IKp P σ m) (hg : ∀ a, IK P (g a)) : IKp P σ (m >>= g) := by
  intro hσ x ⟨y, hy, hx⟩
  exact hg y.1 y.2 (hm hσ y hy) x hx

end Pin

section TI
variable {Q : Tcb → Prop}

theorem ti_update {σ : State Unit} (h : TI Q σ) (p : ObjRef) (o : KernelObject)
    (ho : ∀ t, o = .tcb t → Q t) : TI Q { σ with kheap := Function.update σ.kheap p (some o) } := by
  intro q x hq
  dsimp only at hq
  rw [Function.update_apply] at hq
  split_ifs at hq with e
  · exact ho x (Option.some.inj hq)
  · exact h q x hq

theorem getTcb_kheap {σ : State Unit} {t : ObjRef} {x : Tcb} (h : getTcb t σ = some x) :
    σ.kheap t = some (.tcb x) := by
  unfold getTcb readObject at h
  split at h
  · cases h
  · rename_i k hk
    split at h
    · cases h; exact hk
    · cases h

/-- `setObject` from a state where the new object is no TCB or a TCB satisfying `Q`. -/
theorem ti_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : TI Q σ → ∀ t, o = .tcb t → Q t) : IKp (TI Q) σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨y1, y2⟩ := y
  have e2 : y2 = σ := by
    unfold getObject NonDet.getsThe at hy
    cases e : readObject p σ with
    | none => rw [e] at hy; exact hy.elim
    | some a => rw [e] at hy; exact (Prod.mk.inj (Set.mem_singleton_iff.1 hy)).2
  subst e2
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ti_update hσ p o (ho hσ)

theorem ti_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → Q t) :
    IK (TI Q) (setObject (Z := Unit) p o) :=
  fun σ => ti_setObject_p p o σ (fun _ => ho)

theorem mem_getObject {p : ObjRef} {σ : State Unit} {y : KernelObject × State Unit}
    (h : y ∈ (getObject (Z := Unit) p σ).1) : σ.kheap p = some y.1 ∧ y.2 = σ := by
  unfold getObject NonDet.getsThe at h
  cases hr : readObject p σ with
  | none => rw [hr] at h; exact h.elim
  | some a =>
    rw [hr] at h
    have hy := Set.mem_singleton_iff.1 h
    subst hy; exact ⟨hr, rfl⟩

theorem ti_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    IK (TI Q) (setSimpleKo (Z := Unit) f p e) := by
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
  refine ti_update hσ p _ fun t ht => ?_
  exfalso
  rw [ht] at hty
  simp only [isSimpleType, Set.mem_insert_iff, Set.mem_singleton_iff] at hsimp
  rcases hsimp with h | h | h <;> rw [h] at hty <;> simp [aType] at hty

theorem ti_threadSet (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, Q x → Q (f x)) :
    IK (TI Q) (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => ti_setObject_p _ _ σ fun hσ t' ht => ?_
  cases ht
  exact hf x (hσ _ _ (getTcb_kheap hx))

theorem ti_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef)
    (hA : ∀ x a, Q x → Q { x with tcbArch := a }) : IK (TI Q) (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  refine ik_getsThe_bind fun x σ hx => ti_setObject_p _ _ σ fun hσ t' ht => ?_
  cases ht
  exact hA x _ (hσ _ _ (getTcb_kheap hx))

theorem ti_asUser {α : Type} (t : ObjRef) (u : UserMonad α)
    (hA : ∀ x a, Q x → Q { x with tcbArch := a }) : IK (TI Q) (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (ti_setObject_p _ _ σ fun hσ t' ht => ?_) fun _ => ik_pure _
  cases ht
  exact hA x _ (hσ _ _ (getTcb_kheap hx))

/-- The rest of `setMrs` after the register write: IPC-buffer stores. -/
macro "ti_mach" : tactic => `(tactic| repeat' (first | ik_step0 |
  (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold))

theorem ti_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message)
    (hA : ∀ x a, Q x → Q { x with tcbArch := a }) : IK (TI Q) (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (ti_setObject_p _ _ σ fun hσ t' ht => ?_) fun _ => ?_
  · cases ht
    exact hA x _ (hσ _ _ (getTcb_kheap hx))
  · ti_mach

/-- The six TCB slots `setCap` can write. -/
def CapSlotsOK (Q : Tcb → Prop) (c : Cap) : Prop :=
  ∀ x, Q x → Q { x with tcbCtable := c } ∧ Q { x with tcbVtable := c } ∧ Q { x with tcbIpcframe := c } ∧
    Q { x with tcbFaultHandler := c } ∧ Q { x with tcbTimeoutHandler := c } ∧ Q { x with tcbEpt := c }

theorem ti_setCap (c : Cap) (sl : CslotPtr) (hC : CapSlotsOK Q c) : IK (TI Q) (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (ti_setObject_p _ _ σ fun _ t ht => by cases ht)
    · exact ikp_fail_bind
  · rename_i tcb
    have hq : TI Q σ → Q tcb := fun hσ => hσ _ _ hk
    split
    · exact ikp_pure_bind (ti_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ (hq hσ)).1)
    split
    · exact ikp_pure_bind (ti_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ (hq hσ)).2.1)
    split
    · exact ikp_pure_bind (ti_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ (hq hσ)).2.2.1)
    split
    · exact ikp_pure_bind (ti_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ (hq hσ)).2.2.2.1)
    split
    · exact ikp_pure_bind (ti_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ (hq hσ)).2.2.2.2.1)
    split
    · exact ikp_pure_bind (ti_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ (hq hσ)).2.2.2.2.2)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem ti_foldr_update (ps : List ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → Q t) (kh : KHeap)
    (h : ∀ p x, kh p = some (.tcb x) → Q x) :
    ∀ p x, (ps.foldr (fun p kh => Function.update kh p (some o)) kh) p = some (.tcb x) → Q x := by
  induction ps with
  | nil => exact h
  | cons a ps ih =>
    intro p x hp
    simp only [List.foldr_cons, Function.update_apply] at hp
    split_ifs at hp
    · exact ho x (Option.some.inj hp)
    · exact ih p x hp

theorem defaultObject_tcb {ty : ApiObjectType} {dev : Bool} {n : Nat} {d : Domain} {t : Tcb}
    (hty : ty ≠ .untyped) (h : defaultObject ty dev n d = .tcb t) : t = defaultTcb d := by
  cases ty with
  | untyped => exact absurd rfl hty
  | tcbObject => cases h; rfl
  | archObject a => cases h
  | _ => cases h

theorem ti_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oBits : Nat)
    (ty : ApiObjectType) (dev : Bool) (hD : ∀ d, Q (defaultTcb d)) :
    IK (TI Q) (retypeRegionWith (Z := Unit) bA ptr n oBits ty dev) := by
  unfold retypeRegionWith
  refine ik_bind (ik_pure _) fun _ => ik_bind (ik_pure _) fun ptrs => ik_bind ?_ fun _ => ik_pure _
  unfold NonDet.when
  split
  · rename_i hty
    refine ik_gets_bind fun σ => ikp_gets_bind (ikp_pure_bind (ikp_modify fun hσ => ?_))
    exact ti_foldr_update _ _ (fun t ht => by rw [defaultObject_tcb hty ht]; exact hD _) _ hσ
  · exact ik_pure' _

theorem ti_retypeRegion (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType) (dev : Bool)
    (hD : ∀ d, Q (defaultTcb d)) : IK (TI Q) (retypeRegion (Z := Unit) ptr n oBits ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact ti_retypeRegionWith _ _ _ _ _ _ hD

theorem ti_detype (S : Set ObjRef) {σ : State Unit} (h : TI Q σ) : TI Q (detype S σ) := by
  intro p x hp
  unfold detype at hp
  dsimp only at hp
  split_ifs at hp
  exact h p x hp

theorem ti_deleteObjects (ptr : Word) (bits : Nat) : IK (TI Q) (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  exact ik_bind (ik_doMachineOp (fun _ _ h => h) _) fun _ => ik_modify fun _ h => ti_detype _ h

end TI

end

end Fl4Proofs.P3.SInv
