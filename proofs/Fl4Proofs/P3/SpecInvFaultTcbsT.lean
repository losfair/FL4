/-
P3 (DESIGN.md §9), invariant line G1 (invA2): **pointer-dependent per-TCB
invariants** `TP Q σ` (every TCB at `p` satisfies `Q p`), with the TCB writers
as leaves: SpecInvNativeScopeT's `TI` lemmas with `Q p` for `Q` (`tp_*`). Used
by FaultTcbsS with a set of exempt threads and a list of threads known to have
no fault (SpecInvFaultTcbsF).
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

/-- Every TCB at `p` satisfies `Q p`. -/
def TP (Q : ObjRef → Tcb → Prop) (σ : State Unit) : Prop := ∀ p x, σ.kheap p = some (.tcb x) → Q p x

section TP
variable {Q : ObjRef → Tcb → Prop}

theorem tp_update {σ : State Unit} (h : TP Q σ) (p : ObjRef) (o : KernelObject)
    (ho : ∀ t, o = .tcb t → Q p t) : TP Q { σ with kheap := Function.update σ.kheap p (some o) } := by
  intro q x hq
  dsimp only at hq
  rw [Function.update_apply] at hq
  split_ifs at hq with e
  · subst e; exact ho x (Option.some.inj hq)
  · exact h q x hq

/-- `setObject` from a state where the new object is no TCB or a TCB satisfying `Q`. -/
theorem tp_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : TP Q σ → ∀ t, o = .tcb t → Q p t) : IKp (TP Q) σ (setObject (Z := Unit) p o) := by
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
  exact tp_update hσ p o (ho hσ)

theorem tp_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → Q p t) :
    IK (TP Q) (setObject (Z := Unit) p o) :=
  fun σ => tp_setObject_p p o σ (fun _ => ho)

theorem tp_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    IK (TP Q) (setSimpleKo (Z := Unit) f p e) := by
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
  refine tp_update hσ p _ fun t ht => ?_
  exfalso
  rw [ht] at hty
  simp only [isSimpleType, Set.mem_insert_iff, Set.mem_singleton_iff] at hsimp
  rcases hsimp with h | h | h <;> rw [h] at hty <;> simp [aType] at hty

theorem tp_threadSet (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, Q t x → Q t (f x)) :
    IK (TP Q) (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => tp_setObject_p _ _ σ fun hσ t' ht => ?_
  cases ht
  exact hf x (hσ _ _ (getTcb_kheap hx))

theorem tp_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef)
    (hA : ∀ x a, Q t x → Q t { x with tcbArch := a }) : IK (TP Q) (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  refine ik_getsThe_bind fun x σ hx => tp_setObject_p _ _ σ fun hσ t' ht => ?_
  cases ht
  exact hA x _ (hσ _ _ (getTcb_kheap hx))

theorem tp_asUser {α : Type} (t : ObjRef) (u : UserMonad α)
    (hA : ∀ x a, Q t x → Q t { x with tcbArch := a }) : IK (TP Q) (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  refine ikp_bind (tp_setObject_p _ _ σ fun hσ t' ht => ?_) fun _ => ik_pure _
  cases ht
  exact hA x _ (hσ _ _ (getTcb_kheap hx))

theorem tp_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message)
    (hA : ∀ x a, Q t x → Q t { x with tcbArch := a }) : IK (TP Q) (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (tp_setObject_p _ _ σ fun hσ t' ht => ?_) fun _ => ?_
  · cases ht
    exact hA x _ (hσ _ _ (getTcb_kheap hx))
  · ti_mach

/-- The six TCB slots `setCap` can write. -/
def CapSlotsOKp (Q : ObjRef → Tcb → Prop) (c : Cap) : Prop :=
  ∀ p x, Q p x → Q p { x with tcbCtable := c } ∧ Q p { x with tcbVtable := c } ∧ Q p { x with tcbIpcframe := c } ∧
    Q p { x with tcbFaultHandler := c } ∧ Q p { x with tcbTimeoutHandler := c } ∧ Q p { x with tcbEpt := c }

theorem tp_setCap (c : Cap) (sl : CslotPtr) (hC : CapSlotsOKp Q c) : IK (TP Q) (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (tp_setObject_p _ _ σ fun _ t ht => by cases ht)
    · exact ikp_fail_bind
  · rename_i tcb
    have hq : TP Q σ → Q o tcb := fun hσ => hσ _ _ hk
    split
    · exact ikp_pure_bind (tp_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ _ (hq hσ)).1)
    split
    · exact ikp_pure_bind (tp_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ _ (hq hσ)).2.1)
    split
    · exact ikp_pure_bind (tp_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ _ (hq hσ)).2.2.1)
    split
    · exact ikp_pure_bind (tp_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ _ (hq hσ)).2.2.2.1)
    split
    · exact ikp_pure_bind (tp_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ _ (hq hσ)).2.2.2.2.1)
    split
    · exact ikp_pure_bind (tp_setObject_p _ _ σ fun hσ t ht => by cases ht; exact (hC _ _ (hq hσ)).2.2.2.2.2)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem tp_foldr_update (ps : List ObjRef) (o : KernelObject) (ho : ∀ p t, o = .tcb t → Q p t) (kh : KHeap)
    (h : ∀ p x, kh p = some (.tcb x) → Q p x) :
    ∀ p x, (ps.foldr (fun p kh => Function.update kh p (some o)) kh) p = some (.tcb x) → Q p x := by
  induction ps with
  | nil => exact h
  | cons a ps ih =>
    intro p x hp
    simp only [List.foldr_cons, Function.update_apply] at hp
    split_ifs at hp
    · exact ho p x (Option.some.inj hp)
    · exact ih p x hp

theorem tp_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oBits : Nat)
    (ty : ApiObjectType) (dev : Bool) (hD : ∀ p d, Q p (defaultTcb d)) :
    IK (TP Q) (retypeRegionWith (Z := Unit) bA ptr n oBits ty dev) := by
  unfold retypeRegionWith
  refine ik_bind (ik_pure _) fun _ => ik_bind (ik_pure _) fun ptrs => ik_bind ?_ fun _ => ik_pure _
  unfold NonDet.when
  split
  · rename_i hty
    refine ik_gets_bind fun σ => ikp_gets_bind (ikp_pure_bind (ikp_modify fun hσ => ?_))
    exact tp_foldr_update _ _ (fun p t ht => by rw [defaultObject_tcb hty ht]; exact hD _ _) _ hσ
  · exact ik_pure' _

theorem tp_retypeRegion (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType) (dev : Bool)
    (hD : ∀ p d, Q p (defaultTcb d)) : IK (TP Q) (retypeRegion (Z := Unit) ptr n oBits ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact tp_retypeRegionWith _ _ _ _ _ _ hD

theorem tp_detype (S : Set ObjRef) {σ : State Unit} (h : TP Q σ) : TP Q (detype S σ) := by
  intro p x hp
  unfold detype at hp
  dsimp only at hp
  split_ifs at hp
  exact h p x hp

theorem tp_deleteObjects (ptr : Word) (bits : Nat) : IK (TP Q) (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  exact ik_bind (ik_doMachineOp (fun _ _ h => h) _) fun _ => ik_modify fun _ h => tp_detype _ h

end TP

end

end Fl4Proofs.P3.SInv
