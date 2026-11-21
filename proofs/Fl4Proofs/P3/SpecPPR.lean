/-
P3 (DESIGN.md §9), CSpace: **the spec's `finalise_cap` keeps `PPR0`**
(ScPPR; spec side only), discharging XTopJointDelR's `JFinPPHyp`.

* `TR E W σ σ'`: the time, the consumed time and the current SC kept, the
  release queue shrunk, the current SC active after only if active before
  with the same head refill, and a thread bound to the current SC and in the
  release queue after either bound to it before or in `E`, and (kp12,
  `tst`) a TCB blocked on nothing (`NotBlk`) before is blocked on nothing after,
  with its SC link kept or cleared, unless in `E` (reflexive,
  transitive). `TK E W c m`: from a state whose current SC is `c`, every
  outcome of `m` is `TR E`-related to its start (the combinators and
  `tk_auto`, as ScMaxKeep's `MK`/`mk_auto`; the leaves as DomRecDel's).
* Object steps: `set_object` of an object neither an SC nor a TCB;
  `thread_set` keeping a TCB's SC link or clearing it (`tk_threadSet`), any
  `thread_set` of a thread in `E`; `update_sched_context` keeping an active
  SC's activity and head (`tk_updateSchedContext`), any update of an SC
  other than `c` (`tk_updateSchedContext_ne`); the CNode steps (`NKN`), the
  arch finalisation (`archF`).
* The other leaves: `tcb_release_remove` (the queue filtered),
  `sched_context_set_inactive` (the SC inactive after), the sporadic unblock
  check of `cancel_all_ipc`/`cancel_all_signals` (an SC other than the
  current one: `if_sporadic_cur_sc_assert_refill_unblock_check`),
  `sched_context_donate` and `reply_remove` to a thread in `E` (`TKN`: `TK`
  with the thread added to `E`; `TR.unE` removes it again from a start where
  it is blocked on the reply and outside the release queue). Every
  `set_thread_state` of the deletion sets a state blocked on nothing.
* `tr_finaliseCap`: from an `Inv` state, every outcome of `finalise_cap` is
  `TR`-related with `E` empty: `reply_remove`'s donee is blocked on the
  reply, hence (`Inv.rel`) outside the release queue, which only shrinks.
  `PPR0` is kept by `TR` (`PPR0.of_tr`): `ppr0_finaliseCap`.
-/
import Fl4Proofs.P3.DomRecDel
import Fl4Proofs.P3.XTopJointFinVsSpec
import Fl4Proofs.P3.XTopFinSc
import Fl4Proofs.P3.DelW
import Fl4Proofs.P3.ScPPR
open Classical

namespace Fl4Proofs.P3.PPS
open Fl4Spec

noncomputable section

/-! ## The relation -/

/-- **What the deletion keeps for `PPR0`** (module docstring). -/
structure TR (E : ObjRef → Prop) (W : Prop) (σ σ' : State Unit) : Prop where
  cons : σ'.consumedTime = σ.consumedTime
  time : σ'.curTime = σ.curTime
  csc : σ'.curSc = σ.curSc
  rel : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue
  sc : ∀ y n, σ'.kheap σ.curSc = some (.schedContext y n) → scActive y = true →
    ∃ y0 n0, σ.kheap σ.curSc = some (.schedContext y0 n0) ∧ scActive y0 = true ∧ refillHd y = refillHd y0
  own : ∀ u xt, σ'.kheap u = some (.tcb xt) → xt.tcbSchedContext = some σ.curSc → u ∈ σ'.releaseQueue →
    E u ∨ ∃ x0, σ.kheap u = some (.tcb x0) ∧ x0.tcbSchedContext = some σ.curSc
  tst : ∀ u y, σ'.kheap u = some (.tcb y) → E u ∨ ∃ x, σ.kheap u = some (.tcb x) ∧
    (NotBlk x.tcbState → NotBlk y.tcbState ∧ (y.tcbSchedContext = x.tcbSchedContext ∨ y.tcbSchedContext = none))
  /-- kp13 (with `W`): a thread bound to the current SC and not inactive after
  was so before (l4v `cur_sc_chargeable` kept), unless in `E`. -/
  chg : W → ∀ u y, σ'.kheap u = some (.tcb y) → y.tcbSchedContext = some σ.curSc → y.tcbState ≠ .inactive →
    E u ∨ ∃ x, σ.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some σ.curSc ∧ x.tcbState ≠ .inactive

variable {E : ObjRef → Prop} {W : Prop}

theorem TR.of_eq {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap) (h1 : σ'.consumedTime = σ.consumedTime)
    (h2 : σ'.curTime = σ.curTime) (h3 : σ'.curSc = σ.curSc) (h4 : σ'.releaseQueue = σ.releaseQueue) :
    TR E W σ σ' :=
  ⟨h1, h2, h3, fun u hu => by rw [h4] at hu; exact hu,
    fun y n hy ha => ⟨y, n, by rw [← hk]; exact hy, ha, rfl⟩,
    fun u xt hu hs _ => Or.inr ⟨xt, by rw [← hk]; exact hu, hs⟩,
    fun u y hu => Or.inr ⟨y, by rw [← hk]; exact hu, fun h => ⟨h, Or.inl rfl⟩⟩,
    fun _ u y hu hs hn => Or.inr ⟨y, by rw [← hk]; exact hu, hs, hn⟩⟩

theorem TR.refl (σ : State Unit) : TR E W σ σ := TR.of_eq rfl rfl rfl rfl rfl

theorem TR.trans {σ1 σ2 σ3 : State Unit} (h1 : TR E W σ1 σ2) (h2 : TR E W σ2 σ3) : TR E W σ1 σ3 := by
  refine ⟨h2.cons.trans h1.cons, h2.time.trans h1.time, h2.csc.trans h1.csc,
    fun u hu => h1.rel u (h2.rel u hu), fun y n hy ha => ?_, fun u xt hu hs hr => ?_, fun u y hu => ?_,
    fun hW u y hu hs hn => ?_⟩
  · rw [← h1.csc] at hy
    obtain ⟨y2, n2, hy2, ha2, e2⟩ := h2.sc y n hy ha
    rw [h1.csc] at hy2
    obtain ⟨y1, n1, hy1, ha1, e1⟩ := h1.sc y2 n2 hy2 ha2
    exact ⟨y1, n1, hy1, ha1, e2.trans e1⟩
  · rw [← h1.csc] at hs
    rcases h2.own u xt hu hs hr with h | ⟨x2, hx2, hs2⟩
    · exact Or.inl h
    · rw [h1.csc] at hs2
      exact h1.own u x2 hx2 hs2 (h2.rel u hr)
  · rcases h2.tst u y hu with h | ⟨x2, hx2, h2b⟩
    · exact Or.inl h
    · rcases h1.tst u x2 hx2 with h | ⟨x1, hx1, h1b⟩
      · exact Or.inl h
      · refine Or.inr ⟨x1, hx1, fun hb => ?_⟩
        obtain ⟨hb2, hl2⟩ := h1b hb
        obtain ⟨hb3, hl3⟩ := h2b hb2
        refine ⟨hb3, ?_⟩
        rcases hl3 with e | e
        · rw [e]; exact hl2
        · exact Or.inr e
  · rw [← h1.csc] at hs
    rcases h2.chg hW u y hu hs hn with h | ⟨x2, hx2, hs2, hn2⟩
    · exact Or.inl h
    · rw [h1.csc] at hs2
      exact h1.chg hW u x2 hx2 hs2 hn2

/-- From a state whose current SC is `c`, every outcome of `m` is
`TR E`-related to its start. -/
def TK (E : ObjRef → Prop) (W : Prop) (c : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, σ.curSc = c → ∀ x, x ∈ (m σ).1 → TR E W σ x.2

/-- `TK` for the exception monad. -/
def TKE (E : ObjRef → Prop) (W : Prop) (c : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  TK E W c (ExceptT.run m)

section Comb
variable {c : ObjRef}

theorem tk_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : TK E W c m)
    (hg : ∀ a, TK E W c (g a)) : TK E W c (m >>= g) := by
  intro σ hc x ⟨y, hy, hx⟩
  have h1 := hm σ hc y hy
  exact h1.trans (hg y.1 y.2 (h1.csc.trans hc) x hx)

theorem tk_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : TK E W c m)
    (hg : ∀ a, TK E W c (g a)) : TK E W c (NonDet.bind m g) := tk_bind hm hg

theorem tk_pure {α : Type} (a : α) : TK E W c (pure a : NonDet (State Unit) α) := by
  intro σ _ x hx; rw [Set.mem_singleton_iff.1 hx]; exact TR.refl _

theorem tk_pure' {α : Type} (a : α) : TK E W c (NonDet.pure a : NonDet (State Unit) α) := tk_pure a

theorem tk_gets {α : Type} (g : State Unit → α) : TK E W c (NonDet.gets g) := by
  intro σ _ x hx; rw [Set.mem_singleton_iff.1 hx]; exact TR.refl _

theorem tk_get : TK E W c (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ _ x hx; rw [Set.mem_singleton_iff.1 hx]; exact TR.refl _

theorem tk_assert (P : Prop) : TK E W c (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ _ x hx; obtain ⟨-, rfl⟩ := hx; exact TR.refl _

theorem tk_fail {α : Type} : TK E W c (NonDet.fail : NonDet (State Unit) α) := by
  intro σ _ x hx; exact hx.elim

theorem tk_assertOpt {α : Type} (o : Option α) : TK E W c (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact tk_fail
  · exact tk_pure' _

theorem tk_getsThe {α : Type} (g : State Unit → Option α) : TK E W c (NonDet.getsThe g) := by
  intro σ hc x hx; exact tk_assertOpt (g σ) σ hc x hx

theorem tk_selectF {α : Type} (S : Set α × Prop) : TK E W c (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ _ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact TR.refl _

theorem tk_select {α : Type} (S : Set α) : TK E W c (NonDet.select S : NonDet (State Unit) α) := by
  intro σ _ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact TR.refl _

theorem tk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : TK E W c m1)
    (h2 : TK E W c m2) : TK E W c (if P then m1 else m2) := by
  split <;> assumption

theorem tk_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : TK E W c m) :
    TK E W c (NonDet.when P m) := by
  unfold NonDet.when; exact tk_ite P h (tk_pure' _)

theorem tk_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : TK E W c m) :
    TK E W c (NonDet.unless P m) := by
  unfold NonDet.unless; exact tk_ite P (tk_pure' _) h

theorem tk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, TK E W c (g a)) (o : Option α) :
    TK E W c (NonDet.maybeM g o) := by
  cases o
  · exact tk_pure' _
  · exact h _

theorem tk_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : TK E W c m) :
    TK E W c (NonDet.liftM g m) := tk_bind' h fun _ => tk_pure' _

theorem tk_modify {g : State Unit → State Unit} (hg : ∀ σ, TR E W σ (g σ)) : TK E W c (NonDet.modify g) := by
  intro σ _ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ

theorem tk_get_put {g : State Unit → State Unit} (hg : ∀ σ, TR E W σ (g σ)) :
    TK E W c (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ _ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hg σ

theorem tk_get_put' {g : State Unit → State Unit} (hg : ∀ σ, TR E W σ (g σ)) :
    TK E W c (do let s ← NonDet.get; NonDet.put (g s)) := tk_get_put hg

theorem tk_getObject (p : ObjRef) : TK E W c (getObject (Z := Unit) p) := tk_getsThe _

theorem tk_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, TK E W c (B r)) (r : α) : TK E W c (NonDet.whileLoop C B r) := by
  intro σ hc x hx
  induction hx with
  | done _ => exact TR.refl _
  | step _ hm _ ih =>
    have h1 := hB _ _ hc _ hm
    exact h1.trans (ih (h1.csc.trans hc))

theorem tk_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, TK E W c (g a)) (xs : List α) :
    TK E W c (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact tk_pure' _
  | cons a xs' ih => exact tk_bind' (h a) fun _ => ih

theorem tk_forMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, TK E W c (g a)) (xs : List α) :
    TK E W c (NonDet.forMx xs g) := tk_mapMx h xs

theorem tk_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, TK E W c (g a)) (xs : List α) :
    TK E W c (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact tk_pure' _
  | cons a xs' ih => exact tk_bind' (h a) fun _ => tk_bind' ih fun _ => tk_pure' _

theorem tk_doMachineOp {α : Type} (mop : NonDet MachineState α) : TK E W c (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine tk_bind (tk_gets _) (fun _ => tk_bind (tk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact tk_bind (tk_modify (fun σ => TR.of_eq rfl rfl rfl rfl rfl)) (fun _ => tk_pure _)

theorem tk_doExtendedOp (eop : DetExtMonad Unit) : TK E W c (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine tk_bind tk_get (fun _ => tk_bind (tk_selectF _) (fun _ => ?_))
  split
  exact tk_modify (fun σ => TR.of_eq rfl rfl rfl rfl rfl)

end Comb

section CombE
variable {c : ObjRef} {ε : Type}

theorem tke_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : TKE E W c m)
    (hg : ∀ a, TKE E W c (g a)) : TKE E W c (m >>= g) := by
  unfold TKE; rw [ExceptT.run_bind]
  refine tk_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact tk_pure _

theorem tke_pure {α : Type} (a : α) : TKE E W c (pure a : NonDetE (State Unit) ε α) := tk_pure _

theorem tke_returnOk {α : Type} (a : α) : TKE E W c (NonDetE.returnOk a : NonDetE (State Unit) ε α) := tk_pure _

theorem tke_throw {α : Type} (e : ε) : TKE E W c (NonDetE.throwError e : NonDetE (State Unit) ε α) := tk_pure _

theorem tke_throw' {α : Type} (e : ε) : TKE E W c (throw e : NonDetE (State Unit) ε α) := tk_pure _

theorem tke_liftE {α : Type} {m : NonDet (State Unit) α} (h : TK E W c m) : TKE E W c (NonDetE.liftE (ε := ε) m) := by
  unfold TKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact tk_bind h fun _ => tk_pure _

theorem tke_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : TKE E W c m1)
    (h2 : TKE E W c m2) : TKE E W c (if P then m1 else m2) := by
  split <;> assumption

theorem tke_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : TKE E W c m) :
    TKE E W c (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact tke_ite P h (tke_pure _)

theorem tke_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : TKE E W c m) :
    TKE E W c (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact tke_ite P (tke_pure _) h

theorem tke_throwOpt {α : Type} (e : ε) (o : Option α) : TKE E W c (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact tke_throw' e
  · exact tke_pure _

theorem tke_assertE (P : Prop) : TKE E W c (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  tke_liftE (tk_assert P)

theorem tk_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : TKE E W c m)
    (hh : ∀ e, TK E W c (h e)) : TK E W c (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine tk_bind' hm fun r => ?_
  cases r with
  | ok a => exact tk_pure' _
  | error e => exact hh e

theorem tke_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : TKE E W c m) (hh : ∀ e, TKE E W c (h e)) : TKE E W c (NonDetE.handleE m h) := by
  unfold NonDetE.handleE TKE
  rw [ExceptT.run_mk]
  refine tk_bind' hm fun r => ?_
  cases r with
  | ok a => exact tk_pure' _
  | error e => exact hh e

theorem tke_liftME {α β : Type} (f : α → β) {m : NonDetE (State Unit) ε α} (h : TKE E W c m) :
    TKE E W c (NonDetE.liftME f m) := by
  unfold NonDetE.liftME; exact tke_bind h fun _ => tke_pure _

end CombE

/-- One step of a `TK` proof. -/
macro "tk_step0" : tactic => `(tactic| first
  | with_reducible exact tk_pure _ | with_reducible exact tk_pure' _ | with_reducible exact tk_fail
  | with_reducible exact tk_gets _ | with_reducible exact tk_get
  | with_reducible exact tk_assert _ | with_reducible exact tk_assertOpt _
  | with_reducible exact tk_getsThe _
  | with_reducible exact tk_selectF _ | with_reducible exact tk_select _
  | ((with_reducible apply tk_modify); intro _; exact TR.of_eq rfl rfl rfl rfl rfl)
  | ((with_reducible apply tk_get_put); intro _; exact TR.of_eq rfl rfl rfl rfl rfl)
  | (exact tk_get_put' (fun _ => TR.of_eq rfl rfl rfl rfl rfl))
  | (exact tk_get_put (fun _ => TR.of_eq rfl rfl rfl rfl rfl))
  | with_reducible exact tk_getObject _
  | with_reducible exact tk_doMachineOp _ | with_reducible exact tk_doExtendedOp _
  | (with_reducible refine tk_bind ?_ (fun _ => ?_))
  | (with_reducible refine tk_bind' ?_ (fun _ => ?_))
  | (with_reducible apply tk_ite) | (with_reducible apply tk_when) | (with_reducible apply tk_unless)
  | (with_reducible refine tk_maybeM (fun _ => ?_) _) | (with_reducible apply tk_liftM)
  | (with_reducible refine tk_whileLoop (fun _ => ?_) _)
  | (with_reducible refine tk_mapMx (fun _ => ?_) _)
  | (with_reducible refine tk_mapM (fun _ => ?_) _)
  | (with_reducible refine tk_forMx (fun _ => ?_) _)
  | with_reducible exact tke_pure _ | with_reducible exact tke_returnOk _ | with_reducible exact tke_throw _
  | with_reducible exact tke_throw' _ | with_reducible exact tke_throwOpt _ _ | with_reducible exact tke_assertE _
  | (with_reducible refine tke_bind ?_ (fun _ => ?_))
  | (with_reducible apply tke_liftE) | (with_reducible apply tke_ite) | (with_reducible apply tke_whenE)
  | (with_reducible apply tke_unlessE) | (with_reducible refine tk_catch ?_ (fun _ => ?_))
  | (with_reducible refine tke_handleE ?_ (fun _ => ?_)) | (with_reducible apply tke_liftME)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact tk_pure _)
  | (exact tk_pure _))

/-- A `TK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "tk_leaf" : tactic
macro_rules | `(tactic| tk_leaf) => `(tactic| fail "no tk_leaf")

macro "tk_auto" : tactic => `(tactic| repeat' (first | tk_leaf | tk_step0))

/-! ## Object steps -/

section Obj
variable {c : ObjRef}

/-- `set_object` of an object neither an SC nor a TCB. -/
theorem tk_setObject (p : ObjRef) (o : KernelObject) (h1 : ∀ y n, o ≠ .schedContext y n)
    (h2 : ∀ t, o ≠ .tcb t) : TK E W c (setObject (Z := Unit) p o) := by
  intro σ _ x hx
  obtain ⟨k, -, -, e⟩ := MaxK.mk_setObject_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_, fun u xt hu => ?_,
    fun _ u xt hu hs hn => ?_⟩
  · by_cases hq : σ.curSc = p
    · rw [hq] at hy; simp only [Function.update_self, Option.some.injEq] at hy; exact absurd hy (h1 y n)
    · simp only [Function.update_of_ne hq] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = p
    · subst hq; simp only [Function.update_self, Option.some.injEq] at hu; exact absurd hu (h2 xt)
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩
  · by_cases hq : u = p
    · subst hq; simp only [Function.update_self, Option.some.injEq] at hu; exact absurd hu (h2 xt)
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, fun h => ⟨h, Or.inl rfl⟩⟩
  · by_cases hq : u = p
    · subst hq; simp only [Function.update_self, Option.some.injEq] at hu; exact absurd hu (h2 xt)
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs, hn⟩

theorem getTcb_kh {σ : State Unit} {t : ObjRef} {x : Tcb} (h : getTcb (Z := Unit) t σ = some x) :
    σ.kheap t = some (.tcb x) := by
  cases hk : σ.kheap t with
  | none => simp [getTcb, readObject, hk] at h
  | some k => cases k <;> simp_all [getTcb, readObject]

/-- The outcome of `thread_set`. -/
theorem threadSet_mem {σ : State Unit} {t : ObjRef} {f : Tcb → Tcb} {x : Unit × State Unit}
    (hx : x ∈ (threadSet (Z := Unit) f t σ).1) :
    ∃ x0, σ.kheap t = some (.tcb x0) ∧ x.2 = { σ with kheap := Function.update σ.kheap t (some (.tcb (f x0))) } := by
  unfold threadSet at hx
  obtain ⟨y, hy, hx⟩ := hx
  unfold NonDet.getsThe at hy
  cases hg : getTcb (Z := Unit) t σ with
  | none => rw [hg] at hy; exact hy.elim
  | some x0 =>
    rw [hg] at hy
    obtain rfl : y = (x0, σ) := hy
    obtain ⟨-, -, -, e⟩ := MaxK.mk_setObject_mem hx
    exact ⟨x0, getTcb_kh hg, e⟩

/-- `thread_set` keeping the TCB's SC link or clearing it. -/
theorem tk_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext ∨ (f x).tcbSchedContext = none)
    (hb : ∀ x, NotBlk x.tcbState → NotBlk (f x).tcbState)
    (hi : W → ∀ x, x.tcbState = .inactive → (f x).tcbState = .inactive) :
    TK E W c (threadSet (Z := Unit) f t) := by
  intro σ _ x hx
  obtain ⟨x0, hk, e⟩ := threadSet_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_, fun u xt hu => ?_,
    fun _ u xt hu hs hn => ?_⟩
  rotate_left 2
  · by_cases hq : u = t
    · subst hq; simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hu
      subst hu
      exact Or.inr ⟨x0, hk, fun h => ⟨hb x0 h, hf x0⟩⟩
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, fun h => ⟨h, Or.inl rfl⟩⟩
  · rename_i hW
    by_cases hq : u = t
    · subst hq; simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hu
      subst hu
      refine Or.inr ⟨x0, hk, ?_, fun h0 => hn (hi hW x0 h0)⟩
      rcases hf x0 with h | h
      · rw [← h]; exact hs
      · rw [h] at hs; cases hs
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs, hn⟩
  · by_cases hq : σ.curSc = t
    · rw [hq] at hy; simp at hy
    · simp only [Function.update_of_ne hq] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = t
    · subst hq; simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hu
      subst hu
      rcases hf x0 with h | h
      · exact Or.inr ⟨x0, hk, by rw [← h]; exact hs⟩
      · rw [h] at hs; cases hs
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩

/-- Any `thread_set` of a thread in `E`. -/
theorem tk_threadSet_E (f : Tcb → Tcb) (t : ObjRef) (hE : E t) : TK E W c (threadSet (Z := Unit) f t) := by
  intro σ _ x hx
  obtain ⟨x0, hk, e⟩ := threadSet_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_, fun u xt hu => ?_,
    fun _ u xt hu hs hn => ?_⟩
  · by_cases hq : σ.curSc = t
    · rw [hq] at hy; simp at hy
    · simp only [Function.update_of_ne hq] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = t
    · subst hq; exact Or.inl hE
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩
  · by_cases hq : u = t
    · subst hq; exact Or.inl hE
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, fun h => ⟨h, Or.inl rfl⟩⟩
  · by_cases hq : u = t
    · subst hq; exact Or.inl hE
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs, hn⟩

/-- `update_sched_context` keeping an active SC's activity and head. -/
theorem tk_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, scActive (f y) = true → scActive y = true ∧ refillHd (f y) = refillHd y) :
    TK E W c (updateSchedContext (Z := Unit) q f) := by
  intro σ _ x hx
  obtain ⟨y0, n0, hk, e⟩ := MaxK.updSc_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_, fun u xt hu => ?_,
    fun _ u xt hu hs hn => ?_⟩
  · by_cases hq : σ.curSc = q
    · rw [hq] at hy ⊢
      simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      obtain ⟨h1, h2⟩ := hf y0 ha
      exact ⟨y0, _, hk, h1, h2⟩
    · simp only [Function.update_of_ne hq] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = q
    · subst hq; simp at hu
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩
  · by_cases hq : u = q
    · subst hq; simp at hu
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, fun h => ⟨h, Or.inl rfl⟩⟩
  · by_cases hq : u = q
    · subst hq; simp at hu
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs, hn⟩

/-- Any `update_sched_context` of an SC other than the current one. -/
theorem tk_updateSchedContext_ne (q : ObjRef) (f : SchedContext → SchedContext) (hq : q ≠ c) :
    TK E W c (updateSchedContext (Z := Unit) q f) := by
  intro σ hc x hx
  obtain ⟨y0, n0, hk, e⟩ := MaxK.updSc_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_, fun u xt hu => ?_,
    fun _ u xt hu hs hn => ?_⟩
  · have hq' : σ.curSc ≠ q := fun h => hq (by rw [← hc, h])
    simp only [Function.update_of_ne hq'] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = q
    · subst hq; simp at hu
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩
  · by_cases hq : u = q
    · subst hq; simp at hu
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, fun h => ⟨h, Or.inl rfl⟩⟩
  · by_cases hq : u = q
    · subst hq; simp at hu
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs, hn⟩

/-- The CNode steps (`CnK`: every SC kept, every TCB's SC link kept). -/
theorem tk_of_nkn {α : Type} {m : NonDet (State Unit) α} (h : Ipc.NKN m) : TK E W c m := by
  intro σ _ x hx
  have hk := PPK.of_cnK (h σ x hx)
  exact ⟨hk.cons, hk.time, hk.csc, hk.rel, fun y n hy ha => ⟨y, n, hk.sc _ y n hy, ha, rfl⟩,
    fun u xt hu hs _ => let ⟨x0, h0, e, _⟩ := hk.tcb u xt hu; Or.inr ⟨x0, h0, by rw [e]; exact hs⟩,
    fun u xt hu => let ⟨x0, h0, e, hb⟩ := hk.tcb u xt hu; Or.inr ⟨x0, h0, fun h => ⟨hb h, Or.inl e.symm⟩⟩,
    fun _ u xt hu hs hn => by
      rcases (h σ x hx).2 u with h' | ⟨r, cs, cs', h1, h2⟩ | ⟨x0, y', h1, h2, hc⟩
      · rw [h'] at hu; exact Or.inr ⟨xt, hu, hs, hn⟩
      · rw [h2] at hu; cases hu
      · rw [h2] at hu; cases hu
        exact Or.inr ⟨x0, h1, by rw [← hc.2.2.2.2.2.1]; exact hs, by rw [← hc.1]; exact hn⟩⟩

/-- The arch finalisation (`archF`: every non-arch object kept, the
scheduler's fields kept). -/
theorem tk_of_archF {α : Type} {m : NonDet (State Unit) α} (h : Vs.FK archF m) : TK E W c m := by
  intro σ _ x hx
  have e := h σ x hx
  simp only [archF, Prod.mk.injEq] at e
  obtain ⟨e1, -, -, -, -, -, e5, e6, e7, -, -, -, -, e12, -, -, -⟩ := e
  have k : ∀ q o, (∀ a, o ≠ KernelObject.archObj a) → x.2.kheap q = some o → σ.kheap q = some o := by
    intro q o ho hq
    have := congrFun e1 q
    try simp only at this
    rw [hq] at this
    cases o with
    | archObj a => exact absurd rfl (ho a)
    | _ =>
      cases hσ : σ.kheap q with
      | none => rw [hσ] at this; simp [eraseA] at this
      | some k => rw [hσ] at this; cases k <;> simp_all [eraseA]
  refine ⟨e5, e6, e7, fun u hu => by rw [e12] at hu; exact hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_,
    fun u xt hu => ?_, fun _ u xt hu hs hn => ?_⟩
  · exact ⟨y, n, k _ _ (fun _ h => by cases h) hy, ha, rfl⟩
  · exact Or.inr ⟨xt, k _ _ (fun _ h => by cases h) hu, hs⟩
  · exact Or.inr ⟨xt, k _ _ (fun _ h => by cases h) hu, fun h => ⟨h, Or.inl rfl⟩⟩
  · exact Or.inr ⟨xt, k _ _ (fun _ h => by cases h) hu, hs, hn⟩

end Obj

/-! ## Reading a TCB, then writing it back with its SC link -/

section Tka
variable {c : ObjRef}

/-- From a state where `t` holds the TCB `x`. -/
def TKA (E : ObjRef → Prop) (W : Prop) (c t : ObjRef) (x : Tcb) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, σ.curSc = c → σ.kheap t = some (.tcb x) → ∀ z, z ∈ (m σ).1 → TR E W σ z.2

theorem tr_setTcb {σ : State Unit} {t : ObjRef} {x y : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hs : y.tcbSchedContext = x.tcbSchedContext) (hb : NotBlk x.tcbState → NotBlk y.tcbState)
    (hi : W → x.tcbState = .inactive → y.tcbState = .inactive) :
    TR E W σ { σ with kheap := Function.update σ.kheap t (some (.tcb y)) } := by
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y' n hy ha => ?_, fun u xt hu hs' _ => ?_, fun u xt hu => ?_,
    fun hW u xt hu hs' hn => ?_⟩
  rotate_left 2
  · by_cases hq : u = t
    · subst hq; simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hu
      subst hu
      exact Or.inr ⟨x, hk, fun h => ⟨hb h, Or.inl hs⟩⟩
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, fun h => ⟨h, Or.inl rfl⟩⟩
  · by_cases hq : u = t
    · subst hq; simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hu
      subst hu
      exact Or.inr ⟨x, hk, by rw [← hs]; exact hs', fun h0 => hn (hi hW h0)⟩
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs', hn⟩
  · by_cases hq : σ.curSc = t
    · rw [hq] at hy; simp at hy
    · simp only [Function.update_of_ne hq] at hy; exact ⟨y', n, hy, ha, rfl⟩
  · by_cases hq : u = t
    · subst hq; simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hu
      subst hu
      exact Or.inr ⟨x, hk, by rw [← hs]; exact hs'⟩
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs'⟩

theorem tka_getTcb {t : ObjRef} {α : Type} {g : Tcb → NonDet (State Unit) α} (h : ∀ x, TKA E W c t x (g x)) :
    TK E W c (NonDet.getsThe (getTcb (Z := Unit) t) >>= g) := by
  intro σ hc z ⟨y, hy, hz⟩
  unfold NonDet.getsThe at hy
  cases hg : getTcb (Z := Unit) t σ with
  | none => rw [hg] at hy; exact hy.elim
  | some x0 =>
    rw [hg] at hy
    obtain rfl : y = (x0, σ) := hy
    exact h x0 σ hc (getTcb_kh hg) z hz

theorem tka_pure_bind {t : ObjRef} {x : Tcb} {α β : Type} {a : α} {g : α → NonDet (State Unit) β}
    (h : TKA E W c t x (g a)) : TKA E W c t x ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ hc hk z ⟨y, hy, hz⟩
  obtain rfl : y = (a, σ) := hy
  exact h σ hc hk z hz

theorem tka_selectF_bind {t : ObjRef} {x : Tcb} {α β : Type} {S : Set α × Prop} {g : α → NonDet (State Unit) β}
    (h : ∀ a, TKA E W c t x (g a)) : TKA E W c t x (NonDet.selectF S >>= g) := by
  intro σ hc hk z ⟨y, hy, hz⟩
  obtain ⟨-, e⟩ := hy
  obtain ⟨a, s⟩ := y
  simp only at e; subst e
  exact h a _ hc hk z hz

theorem tka_setObject {t : ObjRef} {x y : Tcb} (hs : y.tcbSchedContext = x.tcbSchedContext)
    (hb : NotBlk x.tcbState → NotBlk y.tcbState := by exact id)
    (hi : W → x.tcbState = .inactive → y.tcbState = .inactive := by exact fun _ h => h) :
    TKA E W c t x (setObject (Z := Unit) t (.tcb y)) := by
  intro σ _ hk z hz
  obtain ⟨-, -, -, e⟩ := MaxK.mk_setObject_mem hz
  rw [e]; exact tr_setTcb hk hs hb hi

theorem tka_setObject_bind {t : ObjRef} {x y : Tcb} {β : Type} {g : Unit → NonDet (State Unit) β}
    (hs : y.tcbSchedContext = x.tcbSchedContext) (h : ∀ u, TK E W c (g u))
    (hb : NotBlk x.tcbState → NotBlk y.tcbState := by exact id)
    (hi : W → x.tcbState = .inactive → y.tcbState = .inactive := by exact fun _ h => h) :
    TKA E W c t x (setObject (Z := Unit) t (.tcb y) >>= g) := by
  intro σ hc hk z ⟨w, hw, hz⟩
  have h1 := tka_setObject (E := E) (c := c) hs hb hi σ hc hk w hw
  exact h1.trans (h w.1 w.2 (h1.csc.trans hc) z hz)

end Tka

/-! ## A thread outside the release queue (`reply_remove`'s donation) -/

section Tkn
variable {c : ObjRef}

/-- `TK` with `t` added to `E` (kp12: `t` is the reply's caller, blocked on
the reply and outside the release queue at the start, `TR.unE`). -/
def TKN (E : ObjRef → Prop) (W : Prop) (c t : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  TK (fun u => E u ∨ u = t) W c m

theorem TR.mono {E' : ObjRef → Prop} {σ σ' : State Unit} (h : TR E W σ σ') (hE : ∀ u, E u → E' u) : TR E' W σ σ' :=
  ⟨h.cons, h.time, h.csc, h.rel, h.sc, fun u xt hu hs hr => (h.own u xt hu hs hr).imp_left (hE u),
    fun u y hu => (h.tst u y hu).imp_left (hE u), fun hW u y hu hs hn => (h.chg hW u y hu hs hn).imp_left (hE u)⟩

/-- **`TR` with `t` added to `E`, from a start where `t` is outside the
release queue and blocked on a reply, to an end where `t` is inactive**
(kp13: `reply_remove` ends with `reply_unlink_tcb`'s `Inactive`). -/
theorem TR.unE {t : ObjRef} {σ σ' : State Unit} (h : TR (fun u => E u ∨ u = t) W σ σ')
    (ht : t ∉ σ.releaseQueue) {x0 : Tcb} (hk : σ.kheap t = some (.tcb x0)) (hb : ¬ NotBlk x0.tcbState)
    (hi : W → ∀ y, σ'.kheap t = some (.tcb y) → y.tcbState = .inactive) :
    TR E W σ σ' := by
  refine ⟨h.cons, h.time, h.csc, h.rel, h.sc, fun u xt hu hs hr => ?_, fun u y hu => ?_,
    fun hW u y hu hs hn => ?_⟩
  · rcases h.own u xt hu hs hr with (h' | rfl) | h'
    · exact Or.inl h'
    · exact absurd (h.rel _ hr) ht
    · exact Or.inr h'
  · rcases h.tst u y hu with (h' | rfl) | h'
    · exact Or.inl h'
    · exact Or.inr ⟨x0, hk, fun h' => absurd h' hb⟩
    · exact Or.inr h'
  · rcases h.chg hW u y hu hs hn with (h' | rfl) | h'
    · exact Or.inl h'
    · exact absurd (hi hW y hu) hn
    · exact Or.inr h'

theorem tkn_of {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : TK E W c m) : TKN E W c t m :=
  fun σ hc x hx => (h σ hc x hx).mono fun _ => Or.inl

theorem tkn_bind {t : ObjRef} {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : TKN E W c t m) (hg : ∀ a, TKN E W c t (g a)) : TKN E W c t (m >>= g) := tk_bind hm hg

theorem tkn_when {t : ObjRef} (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : TKN E W c t m) :
    TKN E W c t (NonDet.when P m) := by
  unfold NonDet.when; split
  · exact h
  · exact tkn_of (tk_pure' _)

/-- Any `thread_set` of `t`, outside the release queue. -/
theorem tkn_threadSet (f : Tcb → Tcb) (t : ObjRef) : TKN E W c t (threadSet (Z := Unit) f t) :=
  tk_threadSet_E f t (Or.inr rfl)

end Tkn

/-! ## The leaves -/

section Leaves
variable {c : ObjRef}

/-- The two shapes of "not this constructor" side goals. -/
macro "tk_neq" : tactic => `(tactic| first | (intro _ _ h; cases h) | (intro _ h; cases h))

macro_rules | `(tactic| tk_leaf) => `(tactic| ((with_reducible refine tk_setObject _ _ ?_ ?_) <;> tk_neq))
/-- The `NotBlk` side goal of a TCB write (kp12): the state kept, a parameter's, or a constant. -/
macro "tk_nobor" : tactic => `(tactic| first
  | (intro _ h; exact h) | (intro _ _; assumption) | assumption | (intro _ _; exact ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ _ h => by cases h⟩) | exact ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ _ h => by cases h⟩)

macro_rules | `(tactic| tk_leaf) => `(tactic|
  ((with_reducible refine tk_threadSet _ _ ?_ ?_ ?_); (intro _; first | exact Or.inl rfl | exact Or.inr rfl); tk_nobor;
    first | (intro _ _ h; exact h) | (intro _ _ _; rfl)))
macro_rules | `(tactic| tk_leaf) => `(tactic|
  ((with_reducible refine tk_updateSchedContext _ _ ?_); intro _ h; exact ⟨h, rfl⟩))
macro_rules | `(tactic| tk_leaf) => `(tactic|
  (with_reducible refine tk_updateSchedContext_ne _ _ ?_; assumption))

theorem tk_setCap (cp : Cap) (sl : CslotPtr) : TK E W c (setCap (Z := Unit) cp sl) := tk_of_nkn (Ipc.nkn_setCap _ _)
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setCap _ _)

theorem tk_getCap (sl : CslotPtr) : TK E W c (getCap (Z := Unit) sl) := tk_of_nkn (Ipc.nkn_getCap _)
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getCap _)

theorem tk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α)
    (h1 : ∀ y n, C e ≠ .schedContext y n) (h2 : ∀ t, C e ≠ .tcb t) : TK E W c (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo
  exact tk_bind (tk_getObject _) fun _ => tk_bind (tk_assert _) fun _ => tk_bind (tk_assert _) fun _ =>
    tk_setObject _ _ h1 h2
macro_rules | `(tactic| tk_leaf) => `(tactic| ((with_reducible refine tk_setSimpleKo' _ _ _ ?_ ?_) <;> tk_neq))

theorem tk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    TK E W c (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getSimpleKo' _ _)

theorem tk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef)
    (h1 : ∀ e y n, C e ≠ .schedContext y n) (h2 : ∀ e t, C e ≠ .tcb t) :
    TK E W c (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef
  exact tk_bind (tk_getSimpleKo' _ _) fun _ => tk_setSimpleKo' _ _ _ (h1 _) (h2 _)
macro_rules | `(tactic| tk_leaf) => `(tactic|
  ((with_reducible refine tk_updateSkObjRef' _ _ _ _ ?_ ?_) <;> first | (intro _ _ _ h; cases h) | (intro _ _ h; cases h)))

theorem tk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : TK E W c (threadGet (Z := Unit) f t) := by
  unfold threadGet; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_threadGet' _ _)

theorem tk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : TK E W c (asUser (Z := Unit) t u) := by
  unfold asUser
  refine tka_getTcb fun x => ?_
  refine tka_pure_bind ?_
  refine tka_selectF_bind fun z => ?_
  obtain ⟨a, uc'⟩ := z
  refine tka_pure_bind ?_
  exact tka_setObject_bind rfl fun _ => tk_pure _
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_asUser' _ _)

theorem tk_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : TK E W c (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact tka_getTcb fun x => tka_setObject rfl
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_archThreadSet' _ _)

theorem tk_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, TK E W c (g a b)) :
    ∀ l1 l2, TK E W c (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => tk_bind (h a b) (fun _ => tk_zipWithMx' h l1 l2)
  | [], _ => tk_pure' _
  | _ :: _, [] => tk_pure' _
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible refine tk_zipWithMx' (fun _ _ => ?_) _ _)

theorem tk_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : TK E W c (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_storeWordOffs' _ _ _)

theorem tk_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : TK E W c (setMrs (Z := Unit) t b m) := by
  unfold setMrs
  refine tka_getTcb fun x => ?_
  refine tka_pure_bind ?_
  refine tka_pure_bind ?_
  refine tka_setObject_bind rfl fun _ => ?_
  tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setMrs' _ _ _)

/-- `tcb_release_remove`: the queue filtered. -/
theorem tk_tcbReleaseRemove' (t : ObjRef) : TK E W c (tcbReleaseRemove (Z := Unit) t) := by
  intro σ _ x hx
  unfold tcbReleaseRemove at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain rfl : y = (σ.releaseQueue, σ) := hy
  obtain ⟨z, hz, hx⟩ := hx
  have hz2 : z.2.releaseQueue = σ.releaseQueue ∧ z.2.kheap = σ.kheap ∧ z.2.curSc = σ.curSc ∧
      z.2.curTime = σ.curTime ∧ z.2.consumedTime = σ.consumedTime := by
    unfold NonDet.when at hz
    split at hz
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨w, hw, hx⟩ := hx
  obtain rfl : w = (tcbSchedDequeue t σ.releaseQueue, z.2) := hw
  rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨e1, e2, e3, e4, e5⟩ := hz2
  refine ⟨e5, e4, e3, fun u hu => ?_, fun y n hy ha => ⟨y, n, by rw [← e2]; exact hy, ha, rfl⟩,
    fun u xt hu hs _ => Or.inr ⟨xt, by rw [← e2]; exact hu, hs⟩,
    fun u xt hu => Or.inr ⟨xt, by rw [← e2]; exact hu, fun h => ⟨h, Or.inl rfl⟩⟩,
    fun _ u xt hu hs hn => Or.inr ⟨xt, by rw [← e2]; exact hu, hs, hn⟩⟩
  exact (List.mem_filter.1 hu).1
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_tcbReleaseRemove' _)

/-- `sched_context_set_inactive`: the SC inactive after. -/
theorem tk_schedContextSetInactive' (p : ObjRef) : TK E W c (schedContextSetInactive (Z := Unit) p) := by
  intro σ _ x hx
  have hk : ∃ y0 n0, σ.kheap p = some (.schedContext y0 n0) := by
    unfold schedContextSetInactive at hx
    obtain ⟨y, hy, -⟩ := hx
    obtain ⟨y0, n0, hk, -⟩ := MaxK.updSc_mem hy
    exact ⟨y0, n0, hk⟩
  obtain ⟨y0, n0, hk⟩ := hk
  rw [Sched.setInactive_eq hk] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_, fun u xt hu => ?_,
    fun _ u xt hu hs hn => ?_⟩
  · by_cases hq : σ.curSc = p
    · rw [hq] at hy; simp [Notif.updK] at hy
      obtain ⟨rfl, -⟩ := hy
      exact absurd ha (by rw [show scActive (Sched.inactSc y0) = false from rfl]; decide)
    · simp [Notif.updK, Function.update_of_ne hq] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = p
    · subst hq; simp [Notif.updK] at hu
    · simp [Notif.updK, Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩
  · by_cases hq : u = p
    · subst hq; simp [Notif.updK] at hu
    · simp [Notif.updK, Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, fun h => ⟨h, Or.inl rfl⟩⟩
  · by_cases hq : u = p
    · subst hq; simp [Notif.updK] at hu
    · simp [Notif.updK, Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs, hn⟩
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextSetInactive' _)

theorem tk_getThreadState' (t : ObjRef) : TK E W c (getThreadState (Z := Unit) t) := by
  unfold getThreadState; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getThreadState' _)

theorem tk_setThreadState' (t : ObjRef) (ts : ThreadState) (hts : NotBlk ts) (hi : W → ts = .inactive) :
    TK E W c (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine tk_bind (tk_threadSet _ _ (fun _ => Or.inl rfl) (fun _ _ => hts) (fun hW _ _ => hi hW)) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; tk_auto
/-- The `W → ts = .inactive` side goal of `tk_setThreadState'` (kp13). -/
macro "tk_inact" : tactic => `(tactic| first | (intro _; rfl) | (intro h; exact h.elim))
macro_rules | `(tactic| tk_leaf) => `(tactic| ((with_reducible refine tk_setThreadState' _ _ ?_ ?_); tk_nobor; tk_inact))

theorem tk_getSchedContext' (q : ObjRef) : TK E W c (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getSchedContext' _)

theorem tk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) :
    TK E W c (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getSkObjRef' _ _ _)

theorem tk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : TK E W c (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getScObjRef' _ _)

theorem tk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : TK E W c (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getTcbObjRef' _ _)

theorem tk_replyUnlinkTcb' (t r : ObjRef) : TK E W c (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_replyUnlinkTcb' _ _)

theorem tk_getIrqSlot' (irq : Irq) : TK E W c (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getIrqSlot' _)

theorem tk_isFinalCap' (cp : Cap) : TK E W c (isFinalCap (Z := Unit) cp) := by
  unfold isFinalCap; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_isFinalCap' _)

theorem tk_setIoportMask' (f l : IoPort) (val : Bool) : TK E W c (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setIoportMask' _ _ _)

theorem tk_setOriginal' (slot : CslotPtr) (v : Bool) : TK E W c (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setOriginal' _ _)

theorem tk_updateCdt' (f : Cdt → Cdt) : TK E W c (updateCdt (Z := Unit) f) := by
  unfold updateCdt setCdt; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_updateCdt' _)

theorem tk_freeIoportRange' (f l : IoPort) : TK E W c (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_freeIoportRange' _ _)

theorem tk_archPostCapDeletion' (cp : ArchCap) : TK E W c (archPostCapDeletion (Z := Unit) cp) := by
  unfold archPostCapDeletion; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_archPostCapDeletion' _)

theorem tk_setIrqState' (i : IrqState) (irq : Irq) : TK E W c (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setIrqState' _ _)

theorem tk_deletedIrqHandler' (irq : Irq) : TK E W c (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_deletedIrqHandler' _)

theorem tk_lookupIpcBuffer' (b : Bool) (t : ObjRef) : TK E W c (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_lookupIpcBuffer' _ _)

theorem tk_setMessageInfo' (t : ObjRef) (i : MessageInfo) : TK E W c (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setMessageInfo' _ _)

theorem tk_saveFpuState' (t : ObjRef) : TK E W c (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_saveFpuState' _)

theorem tk_loadFpuState' (t : ObjRef) : TK E W c (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_loadFpuState' _)

theorem tk_setX64CurrentFpuOwner' (o : Option ObjRef) : TK E W c (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setX64CurrentFpuOwner' _)

theorem tk_switchLocalFpuOwner' (o : Option ObjRef) : TK E W c (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_switchLocalFpuOwner' _)

theorem tk_getTcbQueue' (d : Domain) (p : Priority) : TK E W c (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getTcbQueue' _ _)

theorem tk_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : TK E W c (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setTcbQueue' _ _ _)

theorem tk_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    TK E W c (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_tcbSchedAction' _ _)

theorem tk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : TK E W c (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getScRefillSufficient' _ _)

theorem tk_getScRefillReady' (sc : ObjRef) : TK E W c (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getScRefillReady' _)

theorem tk_rescheduleRequired' : TK E W c (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_rescheduleRequired')

theorem tk_possibleSwitchTo' (t : ObjRef) : TK E W c (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo setSchedulerAction; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_possibleSwitchTo' _)

theorem tk_testReschedule' (t : ObjRef) : TK E W c (testReschedule (Z := Unit) t) := by
  unfold testReschedule; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_testReschedule' _)

theorem tk_tcbEpDequeue' (t e : ObjRef) : TK E W c (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_tcbEpDequeue' _ _)

theorem tk_tcbNtfnDequeue' (t n : ObjRef) : TK E W c (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_tcbNtfnDequeue' _ _)

theorem tk_isRoundRobin' (sc : ObjRef) : TK E W c (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_isRoundRobin' _)

theorem tk_getRefillHead' (sc : ObjRef) : TK E W c (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getRefillHead' _)

/-- The sporadic unblock check of an SC other than the current one. -/
theorem tk_refillUnblockCheck_ne (sc : ObjRef) (h : sc ≠ c) : TK E W c (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck refillHeadOverlappingLoop mergeOverlappingRefills refillPopHead updateRefillHd
  tk_auto

/-- `if_sporadic_cur_sc_assert_refill_unblock_check`: the check only of an SC
other than the current one. -/
theorem tk_gets_curSc_bind {α : Type} {g : ObjRef → NonDet (State Unit) α} (h : TK E W c (g c)) :
    TK E W c (NonDet.gets (fun s : State Unit => s.curSc) >>= g) := by
  intro σ hc x ⟨y, hy, hx⟩
  obtain rfl : y = (σ.curSc, σ) := hy
  simp only at hx
  rw [hc] at hx
  exact h σ hc x hx

theorem tk_when_cond (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : P → TK E W c m) :
    TK E W c (NonDet.when P m) := by
  unfold NonDet.when; split
  · exact h ‹P›
  · exact tk_pure' _

theorem tk_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) :
    TK E W c (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck ifCondRefillUnblockCheck
  refine tk_maybeM (fun scp => ?_) o
  refine tk_bind (tk_getSchedContext' _) fun _ => ?_
  refine tk_gets_curSc_bind ?_
  refine tk_bind (tk_pure _) fun _ => tk_when _ (tk_when_cond _ fun hP => ?_)
  exact tk_refillUnblockCheck_ne scp (hP rfl)
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem tk_replyUnlinkSc' (sc r : ObjRef) : TK E W c (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_replyUnlinkSc' _ _)

theorem tk_schedContextUpdateConsumed' (sc : ObjRef) : TK E W c (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUpdateConsumed' _)

theorem tk_replyFromKernel' (t : ObjRef) (x : Data × List Data) : TK E W c (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_replyFromKernel' _ _)

theorem tk_setConsumed' (sc t : ObjRef) : TK E W c (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setConsumed' _ _)

theorem tk_schedContextCancelYieldTo' (t : ObjRef) : TK E W c (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextCancelYieldTo' _)

theorem tk_fpuRelease' (t : ObjRef) : TK E W c (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_fpuRelease' _)

theorem tk_cancelIpc' (t : ObjRef) : TK E W c (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc blockedCancelIpc getBlockingObject cancelSignal replyRemoveTcb
  tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_cancelIpc' _)

theorem tk_suspend' (t : ObjRef) : TK E W c (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_suspend' _)

theorem tk_restartThreadIfNoFault' (t : ObjRef) : TK E False c (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_restartThreadIfNoFault' _)

theorem tk_removeAndRestartEpQueuedThread' (t e : ObjRef) :
    TK E False c (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_removeAndRestartEpQueuedThread' _ _)

theorem tk_removeAndRestartNtfnQueuedThread' (t n : ObjRef) :
    TK E False c (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_removeAndRestartNtfnQueuedThread' _ _)

theorem tk_postCapDeletion' (cp : Cap) : TK E W c (postCapDeletion (Z := Unit) cp) := by
  unfold postCapDeletion; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_postCapDeletion' _)

theorem tk_emptySlot' (sl : CslotPtr) (cp : Cap) : TK E W c (emptySlot (Z := Unit) sl cp) := by
  unfold emptySlot; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_emptySlot' _ _)

theorem tk_cancelAllIpc' (e : ObjRef) : TK E False c (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_cancelAllIpc' _)

theorem tk_schedContextMaybeUnbindNtfn' (n : ObjRef) : TK E W c (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextMaybeUnbindNtfn' _)

theorem tk_unbindMaybeNotification' (n : ObjRef) : TK E W c (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_unbindMaybeNotification' _)

theorem tk_cancelAllSignals' (n : ObjRef) : TK E False c (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_cancelAllSignals' _)

theorem tk_unbindNotification' (t : ObjRef) : TK E W c (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_unbindNotification' _)

theorem tk_schedContextUnbindTcb' (sc : ObjRef) : TK E W c (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUnbindTcb' _)

theorem tk_completeYieldTo' (t : ObjRef) : TK E W c (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_completeYieldTo' _)

theorem tk_unbindFromSc' (t : ObjRef) : TK E W c (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_unbindFromSc' _)

theorem tk_schedContextUnbindAllTcbs' (sc : ObjRef) : TK E W c (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUnbindAllTcbs' _)

theorem tk_schedContextUnbindNtfn' (sc : ObjRef) : TK E W c (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUnbindNtfn' _)

theorem tk_schedContextUnbindReply' (sc : ObjRef) : TK E W c (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUnbindReply' _)

theorem tk_schedContextUnbindYieldFrom' (sc : ObjRef) : TK E W c (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUnbindYieldFrom' _)

theorem tk_prepareThreadDelete' (t : ObjRef) : TK E W c (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_prepareThreadDelete' _)

/-- `sched_context_donate` to a thread outside the release queue. -/
theorem tkn_schedContextDonate (sc t : ObjRef) : TKN E W c t (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate
  refine tkn_bind (tkn_of (tk_getScObjRef' _ _)) fun _ => tkn_bind (tkn_of (by tk_auto)) fun _ =>
    tkn_bind (tkn_of (by tk_auto)) fun _ => tkn_threadSet _ _

/-- One step of a `TKN` proof. -/
macro "tkn_step" : tactic => `(tactic| first
  | with_reducible exact tkn_schedContextDonate _ _
  | (with_reducible refine tkn_when _ ?_)
  | (with_reducible refine tkn_bind ?_ (fun _ => ?_))
  | split
  | (simp only [letFun])
  | exact tkn_of (by tk_auto))

/-- `reply_remove` of a caller outside the release queue. -/
theorem tkn_replyRemove (t r : ObjRef) : TKN E W c t (replyRemove (Z := Unit) t r) := by
  unfold replyRemove
  repeat' tkn_step

end Leaves

/-! ## From an `Inv` state: the reply's caller outside the release queue -/

section Tks
variable {c : ObjRef}

/-- Every thread in the release queue is runnable (`Inv.rel`). -/
def RQRun (σ : State Unit) : Prop :=
  ∀ u ∈ σ.releaseQueue, ∃ x, σ.kheap u = some (.tcb x) ∧ runnable x.tcbState = true

theorem rqRun_of_inv {σ : State Unit} (h : Sched.Inv σ) : RQRun σ := fun u hu =>
  let ⟨x, _, _, _, hk, _, hr, _⟩ := h.rel u hu; ⟨x, hk, hr⟩

/-- From a state satisfying `P`. -/
def TKS (E : ObjRef → Prop) (W : Prop) (c : ObjRef) (P : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, σ.curSc = c → P σ → ∀ x, x ∈ (m σ).1 → TR E W σ x.2

variable {P : State Unit → Prop}

theorem tks_of {α : Type} {m : NonDet (State Unit) α} (h : TK E W c m) : TKS E W c P m :=
  fun σ hc _ x hx => h σ hc x hx

theorem tks_bind_tk {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : TKS E W c P m) (hg : ∀ a, TK E W c (g a)) : TKS E W c P (m >>= g) := by
  intro σ hc hP x ⟨y, hy, hx⟩
  have h1 := hm σ hc hP y hy
  exact h1.trans (hg y.1 y.2 (h1.csc.trans hc) x hx)

/-- A read (the state kept) then a `TKS` step. -/
theorem tks_read_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : Vs.FK (fun s : State Unit => s) m) (hg : ∀ a, TKS E W c P (g a)) : TKS E W c P (m >>= g) := by
  intro σ hc hP x ⟨y, hy, hx⟩
  have e : y.2 = σ := hm σ y hy
  rw [← e] at hc hP ⊢
  exact hg y.1 y.2 hc hP x hx

theorem tks_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α} (h1 : TKS E W c P m1)
    (h2 : TKS E W c P m2) : TKS E W c P (if Q then m1 else m2) := by
  split <;> assumption

theorem tks_when (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : TKS E W c P m) :
    TKS E W c P (NonDet.when Q m) := by
  unfold NonDet.when; exact tks_ite Q h (tks_of (tk_pure' _))

theorem tks_unless (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : TKS E W c P m) :
    TKS E W c P (NonDet.unless Q m) := by
  unfold NonDet.unless; exact tks_ite Q (tks_of (tk_pure' _)) h

theorem tks_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : TKS E W c P m) :
    TKS E W c P (NonDet.liftM g m) := tks_bind_tk h fun _ => tk_pure' _

theorem fk_getReplyTcb (r : ObjRef) : Vs.FK (fun s : State Unit => s) (getReplyTcb (Z := Unit) r) := by
  show Vs.FK _ (NonDet.liftM Reply.replyTcb (getSimpleKo KernelObject.reply r))
  unfold getSimpleKo; dk_auto0

theorem getThreadState_mem {σ : State Unit} {t : ObjRef} {w : ThreadState × State Unit}
    (hw : w ∈ (getThreadState (Z := Unit) t σ).1) :
    w.2 = σ ∧ ∃ xt, σ.kheap t = some (.tcb xt) ∧ xt.tcbState = w.1 := by
  unfold getThreadState threadGet at hw
  obtain ⟨y, hy, hw⟩ := hw
  unfold NonDet.getsThe at hy
  cases hg : getTcb (Z := Unit) t σ with
  | none => rw [hg] at hy; exact hy.elim
  | some x0 =>
    rw [hg] at hy
    obtain rfl : y = (x0, σ) := hy
    obtain rfl : w = (x0.tcbState, σ) := hw
    exact ⟨rfl, x0, getTcb_kh hg, rfl⟩

/-- Every outcome of `m` leaves `t` inactive, if a TCB (kp13). -/
def EndIn (t : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → ∀ y, x.2.kheap t = some (.tcb y) → y.tcbState = .inactive

theorem endIn_bind {t : ObjRef} {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (h : ∀ a, EndIn t (g a)) : EndIn t (m >>= g) := by
  intro σ x ⟨y, _, hx⟩; exact h y.1 y.2 x hx

theorem endIn_sts (t : ObjRef) : EndIn t (setThreadState (Z := Unit) t .inactive) := by
  intro σ x hx y hy
  have hx0 := hx
  obtain ⟨z, hz, -⟩ := hx0
  obtain ⟨x0, hk, -⟩ := threadSet_mem hz
  rw [Sched.setThreadState_eq' hk] at hx
  rw [Set.mem_singleton_iff.1 hx] at hy
  simp only [Notif.stsAct_kheap, Notif.updK, Function.update_self, Option.some.injEq,
    KernelObject.tcb.injEq] at hy
  rw [← hy]

/-- **`reply_remove` leaves its caller inactive** (its last step,
`reply_unlink_tcb`). -/
theorem endIn_replyUnlinkTcb (t r : ObjRef) : EndIn t (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb
  refine endIn_bind fun _ => endIn_bind fun _ => endIn_bind fun _ => endIn_bind fun _ => endIn_bind fun _ => ?_
  exact endIn_sts t

theorem endIn_replyRemove (t r : ObjRef) : EndIn t (replyRemove (Z := Unit) t r) := by
  unfold replyRemove
  refine endIn_bind fun _ => endIn_bind fun _ => endIn_bind fun _ => ?_
  dsimp only
  split
  · exact endIn_replyUnlinkTcb t r
  · repeat (first | exact endIn_replyUnlinkTcb t r | refine endIn_bind fun _ => ?_)

/-- **A final reply cap's work** (`finalise_cap`'s and `fast_finalise`'s):
`reply_remove` of a caller blocked on the reply, outside the release queue
(`RQRun`), or `cancel_ipc`. -/
theorem tks_replyBody (r : ObjRef) : TKS E W c RQRun (do
    let tptr ← getReplyTcb (Z := Unit) r
    match tptr with
    | none => return ()
    | some tp => do
      let state ← getThreadState tp
      match state with
      | .blockedOnReply r => replyRemove tp r
      | _ => cancelIpc tp) := by
  refine tks_read_bind (fk_getReplyTcb r) fun tptr => ?_
  cases tptr with
  | none => exact tks_of (tk_pure _)
  | some tp =>
    intro σ hc hR x ⟨w, hw, hx⟩
    obtain ⟨e, xt, hk, hst⟩ := getThreadState_mem hw
    obtain ⟨st, s⟩ := w
    simp only at e hst hx
    subst e
    cases st with
    | blockedOnReply r' =>
      refine (tkn_replyRemove (E := E) tp r' s hc x hx).unE (fun h => ?_) hk (fun hb => hb.1 r' hst)
        (fun _ => endIn_replyRemove tp r' s x hx)
      obtain ⟨x', hk', hr'⟩ := hR tp h
      rw [hk] at hk'; cases hk'
      rw [hst] at hr'; cases hr'
    | _ => exact tk_cancelIpc' tp s hc x hx

theorem tks_fastFinalise (cp : Cap) (b : Bool) : TKS E False c RQRun (fastFinalise (Z := Unit) cp b) := by
  cases cp <;> simp only [fastFinalise] <;>
    first | exact tks_when _ (tks_replyBody _) | exact tks_of (by tk_auto)

theorem tks_capDeleteOne (sl : CslotPtr) : TKS E False c RQRun (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne
  refine tks_read_bind (fk_getCapG _ _) fun cp => tks_unless _ ?_
  refine tks_read_bind (Vs.dk_gets _) fun b => ?_
  exact tks_bind_tk (tks_fastFinalise _ _) fun _ => tk_emptySlot' _ _

theorem tks_deletingIrqHandler (irq : Irq) : TKS E False c RQRun (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler getIrqSlot
  exact tks_read_bind (Vs.dk_gets _) fun _ => tks_capDeleteOne _

/-- **Every outcome of `finalise_cap`** from a state with `RQRun`. -/
theorem tks_finaliseCap (cp : Cap) (b : Bool) : TKS E False c RQRun (finaliseCap (Z := Unit) cp b) := by
  cases cp with
  | replyCap r _ =>
    simp only [finaliseCap]
    exact tks_liftM _ (tks_when _ (tks_replyBody r))
  | irqHandlerCap irq =>
    simp only [finaliseCap]
    exact tks_ite _ (tks_bind_tk (tks_deletingIrqHandler irq) fun _ => tk_pure _) (tks_of (tk_pure _))
  | archObjectCap a =>
    simp only [finaliseCap]
    exact tks_of (tk_of_archF (fa_archFinaliseCap a b))
  | _ => exact tks_of (by simp only [finaliseCap]; tk_auto)

/-- The caps whose finalisation restarts no thread (kp13): not an endpoint,
a notification or an IRQ handler (whose slot holds a notification cap). -/
def NoRestartCap : Cap → Prop
  | .endpointCap _ _ _ => False
  | .notificationCap _ _ _ => False
  | .irqHandlerCap _ => False
  | _ => True

/-- **`tks_finaliseCap` with `chg`** for a cap whose finalisation restarts
no thread (kp13). -/
theorem tks_finaliseCapW (cp : Cap) (b : Bool) (hc : NoRestartCap cp) :
    TKS E W c RQRun (finaliseCap (Z := Unit) cp b) := by
  cases cp with
  | replyCap r _ =>
    simp only [finaliseCap]
    exact tks_liftM _ (tks_when _ (tks_replyBody r))
  | irqHandlerCap irq => exact hc.elim
  | endpointCap _ _ _ => exact hc.elim
  | notificationCap _ _ _ => exact hc.elim
  | archObjectCap a =>
    simp only [finaliseCap]
    exact tks_of (tk_of_archF (fa_archFinaliseCap a b))
  | _ => exact tks_of (by simp only [finaliseCap]; tk_auto)

end Tks

/-! ## `PPR0` kept -/

/-- **`PPR0` kept by `TR`**, given `Chg` after (kp13: proved by `Chg.of_tr`
for the finalisations that restart no thread, and from the endpoint and
notification frames for the others, SpecPPRC). -/
theorem PPR0.of_tr {W : Prop} {σ σ' : State Unit} (hP : PPR0 σ) (h : TR (fun _ => False) W σ σ')
    (hct : σ'.curThread = σ.curThread) (hid : σ'.idleThread = σ.idleThread)
    (hns : (∀ u, σ.schedulerAction ≠ .switchThread u) → ∀ u, σ'.schedulerAction ≠ .switchThread u)
    (hC : Chg σ') (hQ : CtNQ σ') : PPR0 σ' := by
  refine ⟨⟨by rw [hct, hid]; exact hP.1.1, hns hP.1.2.1, fun yt hy => ?_, hC, hQ⟩, fun h0 => ?_⟩
  · rw [hct] at hy
    rcases h.tst _ yt hy with h' | ⟨x, hx, hb⟩
    · exact h'.elim
    obtain ⟨h1, h2⟩ := hP.1.2.2.1 x hx
    obtain ⟨h3, h4⟩ := hb h2
    rw [h.csc]
    refine ⟨?_, h3⟩
    rcases h4 with e | e
    · rw [e]; exact h1
    · exact Or.inr e
  rw [h.cons] at h0
  obtain ⟨h1, h2⟩ := hP.2 h0
  refine ⟨fun y n hy ha => ?_, fun u xt hu hs hr => ?_⟩
  · rw [h.csc] at hy
    obtain ⟨y0, n0, hy0, ha0, e⟩ := h.sc y n hy ha
    rw [h.time, e]; exact h1 y0 n0 hy0 ha0
  · rw [h.csc] at hs
    rcases h.own u xt hu hs hr with h' | ⟨x0, hx0, hs0⟩
    · exact h'.elim
    · exact h2 u x0 hx0 hs0 (h.rel u hr)

/-- **`Chg` kept by `TR` with `chg`** (kp13). -/
theorem Chg.of_tr {σ σ' : State Unit} (hC : Chg σ) (h : TR (fun _ => False) True σ σ')
    (hct : σ'.curThread = σ.curThread) : Chg σ' := by
  intro u y hu hs
  by_cases hn : y.tcbState = .inactive
  · exact Or.inr hn
  rw [h.csc] at hs
  rcases h.chg trivial u y hu hs hn with h' | ⟨x, hx, hxs, hxn⟩
  · exact h'.elim
  · rcases hC u x hx hxs with e | e
    · exact Or.inl (e.trans hct.symm)
    · exact absurd e hxn

/-- **`finalise_cap` keeps `PPR0`** from an `Inv` state, given `Chg` after
(module docstring; the current and idle threads and no pending switch kept:
`hct`/`hid`/`hns`, from VsDom's `DK`, SpecGlobFK's `GK` and SpecNoSwitch's
`AK` at the caller; `Chg` by SpecPPRC). -/
theorem ppr0_finaliseCap {cp : Cap} {b : Bool} {σ : State Unit} {x : (Cap × Cap) × State Unit}
    (hI : Sched.Inv σ) (hx : x ∈ (finaliseCap (Z := Unit) cp b σ).1) (hP : PPR0 σ)
    (hct : x.2.curThread = σ.curThread) (hid : x.2.idleThread = σ.idleThread)
    (hns : (∀ u, σ.schedulerAction ≠ .switchThread u) → ∀ u, x.2.schedulerAction ≠ .switchThread u)
    (hC : Chg x.2) (hQ : CtNQ x.2) : PPR0 x.2 :=
  PPR0.of_tr hP (tks_finaliseCap (E := fun _ => False) cp b σ rfl (rqRun_of_inv hI) x hx) hct hid hns hC hQ

/-- **`Chg` after a finalisation that restarts no thread** (kp13). -/
theorem chg_finaliseCapW {cp : Cap} {b : Bool} {σ : State Unit} {x : (Cap × Cap) × State Unit}
    (hI : Sched.Inv σ) (hx : x ∈ (finaliseCap (Z := Unit) cp b σ).1) (hc : NoRestartCap cp) (hC : Chg σ)
    (hct : x.2.curThread = σ.curThread) : Chg x.2 :=
  Chg.of_tr hC (tks_finaliseCapW (E := fun _ => False) cp b hc σ rfl (rqRun_of_inv hI) x hx) hct

end

end Fl4Proofs.P3.PPS
