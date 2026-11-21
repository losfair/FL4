/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, invA): **spec invariants
kept by a computation** (spec side only, outside the JAtZ cone; imports only
Fl4Spec).

* `IK P m`: every outcome of `m` from a `P` state is a `P` state (l4v's
  `⦃P⦄ m ⦃λ_. P⦄`); `IKE P m := IK P (ExceptT.run m)` for the exception
  monads (`SEMonad`, `PMonad`, `FMonad`, `LFMonad`).
* The combinators mirror VsDom's projection frame `FK` (bind, `if`, `when`,
  loops, the exception monad's `liftE`/`handleE`/`catch` …): `ik_step0` is
  `dk_step0` for `IK`. They are generic in `P`; the field modules
  (SpecInvNativeScope, …) add their own leaves (the writers of the field) and
  an `*_auto` tactic over `ik_step0` and `ik_unfold` (unfold the spec function
  at the head of the goal).
-/
import Fl4Spec.Ext.Entry
import Mathlib.Data.Set.Lattice.Order
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

/-- Every outcome of `m` from a `P` state is a `P` state. -/
def IK (P : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ x, x ∈ (m σ).1 → P x.2

/-- `IK` for the exception monad. -/
abbrev IKE (P : State Unit → Prop) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  IK P (ExceptT.run m)

section Comb
variable {P : State Unit → Prop}

theorem ik_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : IK P m)
    (hg : ∀ a, IK P (g a)) : IK P (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  exact hg y.1 y.2 (hm σ hσ y hy) x hx

theorem ik_bind' {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : IK P m)
    (hg : ∀ a, IK P (g a)) : IK P (NonDet.bind m g) := ik_bind hm hg

theorem ik_of_eq {α : Type} {m : NonDet (State Unit) α} (h : ∀ σ x, x ∈ (m σ).1 → x.2 = σ) : IK P m := by
  intro σ hσ x hx; rw [h σ x hx]; exact hσ

theorem ik_pure {α : Type} (a : α) : IK P (pure a : NonDet (State Unit) α) :=
  ik_of_eq fun _ _ hx => by rw [Set.mem_singleton_iff.1 hx]

theorem ik_pure' {α : Type} (a : α) : IK P (NonDet.pure a : NonDet (State Unit) α) := ik_pure a

theorem ik_gets {α : Type} (g : State Unit → α) : IK P (NonDet.gets g) :=
  ik_of_eq fun _ _ hx => by rw [Set.mem_singleton_iff.1 hx]

theorem ik_get : IK P (NonDet.get : NonDet (State Unit) (State Unit)) :=
  ik_of_eq fun _ _ hx => by rw [Set.mem_singleton_iff.1 hx]

theorem ik_assert (Q : Prop) : IK P (NonDet.assert Q : NonDet (State Unit) Unit) :=
  ik_of_eq fun _ _ hx => by obtain ⟨-, rfl⟩ := hx; rfl

theorem ik_stateAssert (Q : State Unit → Prop) : IK P (NonDet.stateAssert Q) :=
  ik_of_eq fun _ _ hx => by obtain ⟨-, rfl⟩ := hx; rfl

theorem ik_fail {α : Type} : IK P (NonDet.fail : NonDet (State Unit) α) := fun _ _ _ hx => hx.elim

theorem ik_assertOpt {α : Type} (o : Option α) : IK P (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact ik_fail
  · exact ik_pure' _

theorem ik_getsThe {α : Type} (g : State Unit → Option α) : IK P (NonDet.getsThe g) := by
  intro σ hσ x hx; exact ik_assertOpt (g σ) σ hσ x hx

theorem ik_selectF {α : Type} (S : Set α × Prop) : IK P (NonDet.selectF S : NonDet (State Unit) α) :=
  ik_of_eq fun _ _ hx => hx.2

theorem ik_select {α : Type} (S : Set α) : IK P (NonDet.select S : NonDet (State Unit) α) :=
  ik_of_eq fun _ _ hx => hx.2

theorem ik_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α} (h1 : IK P m1)
    (h2 : IK P m2) : IK P (if Q then m1 else m2) := by
  split <;> assumption

theorem ik_when (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : IK P m) :
    IK P (NonDet.when Q m) := by
  unfold NonDet.when; exact ik_ite Q h (ik_pure' _)

theorem ik_unless (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : IK P m) :
    IK P (NonDet.unless Q m) := by
  unfold NonDet.unless; exact ik_ite Q (ik_pure' _) h

theorem ik_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, IK P (g a)) (o : Option α) :
    IK P (NonDet.maybeM g o) := by
  cases o
  · exact ik_pure' _
  · exact h _

theorem ik_liftM {α γ : Type} (g : α → γ) {m : NonDet (State Unit) α} (h : IK P m) :
    IK P (NonDet.liftM g m) := ik_bind' h fun _ => ik_pure' _

theorem ik_modify {g : State Unit → State Unit} (hg : ∀ σ, P σ → P (g σ)) : IK P (NonDet.modify g) := by
  intro σ hσ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ hσ

theorem ik_put_get {g : State Unit → State Unit} (hg : ∀ σ, P σ → P (g σ)) :
    IK P (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hg σ hσ

theorem ik_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, IK P (B r)) (r : α) : IK P (NonDet.whileLoop C B r) := by
  intro σ hσ x hx
  induction hx with
  | done _ => exact hσ
  | step _ hm _ ih => exact ih (hB _ _ hσ _ hm)

theorem ik_mapMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, IK P (g a)) (xs : List α) :
    IK P (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact ik_pure' _
  | cons a xs' ih => exact ik_bind' (h a) fun _ => ih

theorem ik_forMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, IK P (g a)) (xs : List α) :
    IK P (NonDet.forMx xs g) := ik_mapMx h xs

theorem ik_mapM {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, IK P (g a)) (xs : List α) :
    IK P (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact ik_pure' _
  | cons a xs' ih => exact ik_bind' (h a) fun _ => ik_bind' ih fun _ => ik_pure' _

theorem ik_zipWithMx {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, IK P (g a b)) :
    ∀ (xs : List α) (ys : List β), IK P (NonDet.zipWithMx g xs ys)
  | a :: as, b :: bs => by unfold NonDet.zipWithMx; exact ik_bind' (h a b) fun _ => ik_zipWithMx h as bs
  | [], _ => by unfold NonDet.zipWithMx; exact ik_pure' _
  | _ :: _, [] => by unfold NonDet.zipWithMx; exact ik_pure' _

theorem ik_zipWithM {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, IK P (g a b)) :
    ∀ (xs : List α) (ys : List β), IK P (NonDet.zipWithM g xs ys)
  | a :: as, b :: bs => by
    unfold NonDet.zipWithM; exact ik_bind' (h a b) fun _ => ik_bind' (ik_zipWithM h as bs) fun _ => ik_pure' _
  | [], _ => by unfold NonDet.zipWithM; exact ik_pure' _
  | _ :: _, [] => by unfold NonDet.zipWithM; exact ik_pure' _

theorem ik_pure_bind {α γ : Type} {a : α} {g : α → NonDet (State Unit) γ} (h : IK P (g a)) :
    IK P ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ hσ x hx

theorem ik_pure_bind' {α γ : Type} {a : α} {g : α → NonDet (State Unit) γ} (h : IK P (g a)) :
    IK P (NonDet.bind (NonDet.pure a) g) := ik_pure_bind h

/-- CnodeRevoke's `lfp_le_prefixed` (copied: CnodeRevoke is in the JAtZ cone). -/
theorem ik_lfp_le {σ α ι : Type} (F : (ι → NonDet σ α) → ι → NonDet σ α) (f : ι → NonDet σ α)
    (hf : ∀ k t, F f k t ≤ f k t) (i : ι) (s : σ) : NonDet.lfp F i s ≤ f i s := by
  let S := {f : ι → σ → Set (α × σ) × Prop | ∀ k t, F f k t ≤ f k t}
  have hl : NonDet.lfp F = (sInf S : ι → σ → Set (α × σ) × Prop) := rfl
  rw [hl]
  have h2 : sInf S ≤ (f : ι → σ → Set (α × σ) × Prop) :=
    @sInf_le (ι → σ → Set (α × σ) × Prop) _ S f hf
  exact h2 i s

/-- The least fixed point (`rec_del`, `cap_revoke`) keeps `P` if every step of
its functional does, its recursive calls keeping `P`. -/
theorem ik_lfp {ι α : Type} {F : (ι → NonDet (State Unit) α) → ι → NonDet (State Unit) α}
    (hF : ∀ f : ι → NonDet (State Unit) α, (∀ k, IK P (f k)) → ∀ k, IK P (F f k)) (i : ι) :
    IK P (NonDet.lfp F i) := by
  intro σ hσ x hx
  let f : ι → NonDet (State Unit) α := fun _ t => ({y | P t → P y.2}, True)
  have hf : ∀ k t, F f k t ≤ f k t := fun k t =>
    ⟨fun y hy => fun ht => hF f (fun _ _ ht' _ hz => hz ht') k t ht y hy, fun _ => trivial⟩
  exact (ik_lfp_le F f hf i σ).1 hx hσ

theorem ik_getObject (p : ObjRef) : IK P (getObject (Z := Unit) p) := ik_getsThe _

end Comb

section CombE
variable {P : State Unit → Prop} {ε : Type}

theorem ike_bind {α γ : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε γ} (hm : IKE P m)
    (hg : ∀ a, IKE P (g a)) : IKE P (m >>= g) := by
  unfold IKE; rw [ExceptT.run_bind]
  refine ik_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact ik_pure _

theorem ike_pure {α : Type} (a : α) : IKE P (pure a : NonDetE (State Unit) ε α) := ik_pure _

theorem ike_returnOk {α : Type} (a : α) : IKE P (NonDetE.returnOk a : NonDetE (State Unit) ε α) := ik_pure _

theorem ike_throw {α : Type} (e : ε) : IKE P (NonDetE.throwError e : NonDetE (State Unit) ε α) := ik_pure _

theorem ike_throw' {α : Type} (e : ε) : IKE P (throw e : NonDetE (State Unit) ε α) := ik_pure _

theorem ike_pure_bind {α γ : Type} {a : α} {g : α → NonDetE (State Unit) ε γ} (h : IKE P (g a)) :
    IKE P ((pure a : NonDetE (State Unit) ε α) >>= g) := by
  unfold IKE; rw [ExceptT.run_bind, ExceptT.run_pure]
  exact ik_pure_bind h

theorem ike_returnOk_bind {α γ : Type} {a : α} {g : α → NonDetE (State Unit) ε γ} (h : IKE P (g a)) :
    IKE P (NonDetE.returnOk a >>= g) := ike_pure_bind h

theorem ike_liftE {α : Type} {m : NonDet (State Unit) α} (h : IK P m) : IKE P (NonDetE.liftE (ε := ε) m) := by
  unfold IKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact ik_bind h fun _ => ik_pure _

theorem ike_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDetE (State Unit) ε α} (h1 : IKE P m1)
    (h2 : IKE P m2) : IKE P (if Q then m1 else m2) := by
  split <;> assumption

theorem ike_whenE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : IKE P m) :
    IKE P (NonDetE.whenE Q m) := by
  unfold NonDetE.whenE; exact ike_ite Q h (ike_pure _)

theorem ike_unlessE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : IKE P m) :
    IKE P (NonDetE.unlessE Q m) := by
  unfold NonDetE.unlessE; exact ike_ite Q (ike_pure _) h

theorem ike_throwOpt {α : Type} (e : ε) (o : Option α) : IKE P (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact ike_throw' e
  · exact ike_pure _

theorem ike_assertE (Q : Prop) : IKE P (NonDetE.assertE Q : NonDetE (State Unit) ε Unit) :=
  ike_liftE (ik_assert Q)

theorem ik_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : IKE P m)
    (hh : ∀ e, IK P (h e)) : IK P (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine ik_bind' hm fun r => ?_
  cases r with
  | ok a => exact ik_pure' _
  | error e => exact hh e

theorem ike_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : IKE P m) (hh : ∀ e, IKE P (h e)) : IKE P (NonDetE.handleE m h) := by
  unfold NonDetE.handleE IKE
  rw [ExceptT.run_mk]
  refine ik_bind' hm fun r => ?_
  cases r with
  | ok a => exact ik_pure' _
  | error e => exact hh e

theorem ike_liftME {α γ : Type} (g : α → γ) {m : NonDetE (State Unit) ε α} (h : IKE P m) :
    IKE P (NonDetE.liftME g m) := by
  unfold NonDetE.liftME; exact ike_bind h fun _ => ike_pure _

theorem ike_mapMEx {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, IKE P (F a)) :
    ∀ xs : List α, IKE P (NonDetE.mapMEx F xs)
  | [] => by unfold NonDetE.mapMEx; exact ike_pure _
  | a :: as => by unfold NonDetE.mapMEx; exact ike_bind (h a) fun _ => ike_mapMEx h as

theorem ike_mapME {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, IKE P (F a)) :
    ∀ xs : List α, IKE P (NonDetE.mapME F xs)
  | [] => by unfold NonDetE.mapME; exact ike_pure _
  | a :: as => by
    unfold NonDetE.mapME; exact ike_bind (h a) fun _ => ike_bind (ike_mapME h as) fun _ => ike_pure _

end CombE

/-! ## Machine and extended operations: `P` reads neither -/

section Ops
variable {P : State Unit → Prop}

theorem ik_doMachineOp {α : Type} (hP : ∀ σ ms, P σ → P { σ with machineState := ms })
    (mop : NonDet MachineState α) : IK P (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine ik_bind (ik_gets _) (fun _ => ik_bind (ik_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact ik_bind (ik_modify fun σ h => hP σ _ h) (fun _ => ik_pure _)

theorem ik_doExtendedOp (hP : ∀ σ e, P σ → P { σ with exst := e }) (eop : DetExtMonad Unit) :
    IK P (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine ik_bind ik_get (fun _ => ik_bind (ik_selectF _) (fun _ => ?_))
  split
  exact ik_modify fun σ h => hP σ _ h

end Ops

/-- One step of an `IK` proof (VsDom's `dk_step0` for `IK`); a `modify` /
`get >>= put` of fields `P` does not read is closed by `exact h`. -/
macro "ik_step0" : tactic => `(tactic| first
  | with_reducible exact ik_pure _ | with_reducible exact ik_pure' _ | with_reducible exact ik_fail
  | with_reducible exact ik_gets _ | with_reducible exact ik_get
  | with_reducible exact ik_assert _ | with_reducible exact ik_assertOpt _
  | with_reducible exact ik_stateAssert _
  | with_reducible exact ik_getsThe _
  | with_reducible exact ik_selectF _ | with_reducible exact ik_select _
  | ((with_reducible apply ik_modify); intro _ h; exact h)
  | ((with_reducible apply ik_put_get); intro _ h; exact h)
  | (exact ik_put_get (fun _ h => h))
  | with_reducible exact ik_getObject _
  | (with_reducible refine ik_pure_bind ?_) | (with_reducible refine ik_pure_bind' ?_)
  | (with_reducible refine ike_pure_bind ?_) | (with_reducible refine ike_returnOk_bind ?_)
  | (with_reducible refine ik_bind ?_ (fun _ => ?_))
  | (with_reducible refine ik_bind' ?_ (fun _ => ?_))
  | (with_reducible apply ik_ite) | (with_reducible apply ik_when) | (with_reducible apply ik_unless)
  | (with_reducible refine ik_maybeM (fun _ => ?_) _) | (with_reducible apply ik_liftM)
  | (with_reducible refine ik_whileLoop (fun _ => ?_) _)
  | (with_reducible refine ik_mapMx (fun _ => ?_) _)
  | (with_reducible refine ik_mapM (fun _ => ?_) _)
  | (with_reducible refine ik_forMx (fun _ => ?_) _)
  | (with_reducible refine ik_zipWithMx (fun _ _ => ?_) _ _)
  | (with_reducible refine ik_zipWithM (fun _ _ => ?_) _ _)
  | with_reducible exact ike_pure _ | with_reducible exact ike_returnOk _ | with_reducible exact ike_throw _
  | with_reducible exact ike_throw' _ | with_reducible exact ike_throwOpt _ _ | with_reducible exact ike_assertE _
  | (with_reducible refine ike_bind ?_ (fun _ => ?_))
  | (with_reducible apply ike_liftE) | (with_reducible apply ike_ite) | (with_reducible apply ike_whenE)
  | (with_reducible apply ike_unlessE) | (with_reducible refine ik_catch ?_ (fun _ => ?_))
  | (with_reducible refine ike_handleE ?_ (fun _ => ?_)) | (with_reducible apply ike_liftME)
  | (with_reducible refine ike_mapMEx (fun _ => ?_) _) | (with_reducible refine ike_mapME (fun _ => ?_) _)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (exact ik_pure _))

open Lean Meta Elab Tactic in
/-- Unfold the spec function at the head of an `IK`/`IKE` goal. -/
elab "ik_unfold" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let args := t.getAppArgs
  if args.size == 0 then throwError "ik_unfold: no arguments"
  let m := args.back!
  let m := if m.isAppOf ``ExceptT.run then m.getAppArgs.back! else m
  match m.getAppFn with
  | .const n _ =>
    if (`Fl4Spec).isPrefixOf n && !(`Fl4Spec.NonDet).isPrefixOf n && !(`Fl4Spec.NonDetE).isPrefixOf n then
      evalTactic (← `(tactic| unfold $(mkIdent n):ident))
    else throwError "ik_unfold: {n} is not a spec function"
  | _ => throwError "ik_unfold: no head constant"

end

end Fl4Proofs.P3.SInv
