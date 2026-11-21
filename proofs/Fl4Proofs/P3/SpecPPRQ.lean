/-
P3 (DESIGN.md §9), CSpace: **the spec's `finalise_cap` keeps the current
thread out of the ready queues** (ScPPR's `CtNQ`, kp16; l4v `ct_not_queued`
kept by the deletion), the part of `PPR0` neither SpecPPR's `TR` nor
SpecPPRC sees.

* `NQ c σ`: `c` in no ready queue and no switch to `c` pending. `QK c m`:
  every outcome of `m` from an `NQ c` state is `NQ c` (the combinators and
  `qk_auto`, as SpecNoSwitch's `AK`/`ak_auto`; the leaves as its leaves).
  The steps writing the ready queues or the action: `tcb_sched_dequeue`,
  `tcb_sched_enqueue` / `possible_switch_to` / a switch of a thread other
  than `c`, `reschedule_required` (its enqueued target is the pending switch
  target, not `c` by `NQ`), `choose_new_thread`.
* The enqueues of the deletion are `cancel_all_ipc`'s / `cancel_all_signals`'s
  restarts of the threads queued on the endpoint / notification
  (`qk_cancelAllIpc`, `qk_ntfnBody` from a state where `c` is in no such
  queue); every other finalisation step only dequeues (`qk_auto`).
* `nq_finaliseCap`: from `Inv`/`SchedValid`/`EpQB` (the queued threads are
  blocked on their object) and a current thread blocked on nothing
  (`CtOK`), `finalise_cap` keeps `NQ ct`; `ctnq_finaliseCap` (PPR0 → CtNQ
  after).
-/
import Fl4Proofs.P3.SpecPPRC
open Classical

namespace Fl4Proofs.P3.PPNQ
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- `c` in no ready queue and no switch to it pending. -/
def NQ (c : ObjRef) (σ : State Unit) : Prop :=
  (∀ d p, c ∉ σ.readyQueues d p) ∧ σ.schedulerAction ≠ .switchThread c

/-- Every outcome of `m` from an `NQ c` state is `NQ c`. -/
def QK (c : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → NQ c σ → NQ c x.2

/-- `QK` for the exception monad. -/
def QKE (c : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := QK c (ExceptT.run m)

section Comb
variable {c : ObjRef}

theorem qk_of_archF {α : Type} {m : NonDet (State Unit) α} (h : FK archF m) : QK c m := by
  intro σ x hx hN
  have e := h σ x hx
  simp only [archF, Prod.mk.injEq] at e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ha, -, hq, -⟩ := e
  exact ⟨by rw [hq]; exact hN.1, by rw [ha]; exact hN.2⟩

theorem qk_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : QK c m)
    (hg : ∀ a, QK c (g a)) : QK c (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩ hN
  exact hg y.1 y.2 x hx (hm σ y hy hN)

theorem qk_bind' {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : QK c m)
    (hg : ∀ a, QK c (g a)) : QK c (NonDet.bind m g) := qk_bind hm hg

theorem qk_pure {α : Type} (a : α) : QK c (pure a : NonDet (State Unit) α) := by
  intro σ x hx hN; rw [Set.mem_singleton_iff.1 hx]; exact hN

theorem qk_pure' {α : Type} (a : α) : QK c (NonDet.pure a : NonDet (State Unit) α) := qk_pure a

theorem qk_gets {α : Type} (g : State Unit → α) : QK c (NonDet.gets g) := by
  intro σ x hx hN; rw [Set.mem_singleton_iff.1 hx]; exact hN

/-- A read whose continuation knows the value read. -/
theorem qk_gets_bind {α β : Type} {g : State Unit → α} {k : α → NonDet (State Unit) β}
    (h : ∀ a σ x, g σ = a → x ∈ (k a σ).1 → NQ c σ → NQ c x.2) : QK c (NonDet.gets g >>= k) := by
  intro σ x ⟨y, hy, hx⟩ hN
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h _ σ x rfl hx hN

theorem qk_get : QK c (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx hN; rw [Set.mem_singleton_iff.1 hx]; exact hN

theorem qk_assert (P : Prop) : QK c (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx hN; obtain ⟨-, rfl⟩ := hx; exact hN

theorem qk_fail {α : Type} : QK c (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem qk_assertOpt {α : Type} (o : Option α) : QK c (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact qk_fail
  · exact qk_pure' _

theorem qk_getsThe {α : Type} (g : State Unit → Option α) : QK c (NonDet.getsThe g) := by
  intro σ x hx; exact qk_assertOpt (g σ) σ x hx

theorem qk_selectF {α : Type} (S : Set α × Prop) : QK c (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx hN; obtain ⟨-, h⟩ := hx; rw [h]; exact hN

theorem qk_select {α : Type} (S : Set α) : QK c (NonDet.select S : NonDet (State Unit) α) := by
  intro σ x hx hN; obtain ⟨-, h⟩ := hx; rw [h]; exact hN

theorem qk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : QK c m1)
    (h2 : QK c m2) : QK c (if P then m1 else m2) := by
  split <;> assumption

theorem qk_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : QK c m) :
    QK c (NonDet.when P m) := by
  unfold NonDet.when; exact qk_ite P h (qk_pure' _)

theorem qk_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : QK c m) :
    QK c (NonDet.unless P m) := by
  unfold NonDet.unless; exact qk_ite P (qk_pure' _) h

theorem qk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, QK c (g a)) (o : Option α) :
    QK c (NonDet.maybeM g o) := by
  cases o
  · exact qk_pure' _
  · exact h _

theorem qk_liftM {α γ : Type} (g : α → γ) {m : NonDet (State Unit) α} (h : QK c m) :
    QK c (NonDet.liftM g m) := qk_bind' h fun _ => qk_pure' _

theorem qk_modify {g : State Unit → State Unit} (hg : ∀ σ, NQ c σ → NQ c (g σ)) : QK c (NonDet.modify g) := by
  intro σ x hx hN; rw [Set.mem_singleton_iff.1 hx]; exact hg σ hN

theorem qk_get_put {g : State Unit → State Unit} (hg : ∀ σ, NQ c σ → NQ c (g σ)) :
    QK c (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩ hN
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hg σ hN

theorem qk_get_put' {g : State Unit → State Unit} (hg : ∀ σ, NQ c σ → NQ c (g σ)) :
    QK c (do let s ← NonDet.get; NonDet.put (g s)) := qk_get_put hg

theorem qk_getObject (p : ObjRef) : QK c (getObject (Z := Unit) p) := qk_getsThe _

theorem qk_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, QK c (B r)) (r : α) : QK c (NonDet.whileLoop C B r) := by
  intro σ x hx hN
  induction hx with
  | done _ => exact hN
  | step _ hm _ ih => exact ih (hB _ _ _ hm hN)

theorem qk_mapMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, QK c (g a)) (xs : List α) :
    QK c (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact qk_pure' _
  | cons a xs' ih => exact qk_bind' (h a) fun _ => ih

/-- `mapMx` over a list whose members are all `QK`. -/
theorem qk_mapMx_mem {α γ : Type} {g : α → NonDet (State Unit) γ} :
    ∀ (xs : List α), (∀ a ∈ xs, QK c (g a)) → QK c (NonDet.mapMx g xs)
  | [], _ => qk_pure' _
  | a :: xs', h => qk_bind' (h a (List.mem_cons_self ..)) fun _ =>
      qk_mapMx_mem xs' fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem qk_forMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, QK c (g a)) (xs : List α) :
    QK c (NonDet.forMx xs g) := qk_mapMx h xs

theorem qk_mapM {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, QK c (g a)) (xs : List α) :
    QK c (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact qk_pure' _
  | cons a xs' ih => exact qk_bind' (h a) fun _ => qk_bind' ih fun _ => qk_pure' _

theorem qk_doMachineOp {α : Type} (mop : NonDet MachineState α) : QK c (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine qk_bind (qk_gets _) (fun _ => qk_bind (qk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact qk_bind (qk_modify (fun σ h => h)) (fun _ => qk_pure _)

theorem qk_doExtendedOp (eop : DetExtMonad Unit) : QK c (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine qk_bind qk_get (fun _ => qk_bind (qk_selectF _) (fun _ => ?_))
  split
  exact qk_modify (fun σ h => h)

end Comb

section CombE
variable {c : ObjRef} {ε : Type}

theorem qke_bind {α γ : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε γ} (hm : QKE c m)
    (hg : ∀ a, QKE c (g a)) : QKE c (m >>= g) := by
  unfold QKE; rw [ExceptT.run_bind]
  refine qk_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact qk_pure _

theorem qke_pure {α : Type} (a : α) : QKE c (pure a : NonDetE (State Unit) ε α) := qk_pure _

theorem qke_returnOk {α : Type} (a : α) : QKE c (NonDetE.returnOk a : NonDetE (State Unit) ε α) := qk_pure _

theorem qke_throw {α : Type} (e : ε) : QKE c (NonDetE.throwError e : NonDetE (State Unit) ε α) := qk_pure _

theorem qke_throw' {α : Type} (e : ε) : QKE c (throw e : NonDetE (State Unit) ε α) := qk_pure _

theorem qke_liftE {α : Type} {m : NonDet (State Unit) α} (h : QK c m) : QKE c (NonDetE.liftE (ε := ε) m) := by
  unfold QKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact qk_bind h fun _ => qk_pure _

theorem qke_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : QKE c m1)
    (h2 : QKE c m2) : QKE c (if P then m1 else m2) := by
  split <;> assumption

theorem qke_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : QKE c m) :
    QKE c (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact qke_ite P h (qke_pure _)

theorem qke_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : QKE c m) :
    QKE c (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact qke_ite P (qke_pure _) h

theorem qke_throwOpt {α : Type} (e : ε) (o : Option α) : QKE c (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact qke_throw' e
  · exact qke_pure _

theorem qke_assertE (P : Prop) : QKE c (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  qke_liftE (qk_assert P)

theorem qk_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : QKE c m)
    (hh : ∀ e, QK c (h e)) : QK c (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine qk_bind' hm fun r => ?_
  cases r with
  | ok a => exact qk_pure' _
  | error e => exact hh e

theorem qke_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : QKE c m) (hh : ∀ e, QKE c (h e)) : QKE c (NonDetE.handleE m h) := by
  unfold NonDetE.handleE QKE
  rw [ExceptT.run_mk]
  refine qk_bind' hm fun r => ?_
  cases r with
  | ok a => exact qk_pure' _
  | error e => exact hh e

theorem qke_liftME {α γ : Type} (g : α → γ) {m : NonDetE (State Unit) ε α} (h : QKE c m) :
    QKE c (NonDetE.liftME g m) := by
  unfold NonDetE.liftME; exact qke_bind h fun _ => qke_pure _

end CombE

/-! ## The queue and action writes -/

section Q
variable {c : ObjRef}

theorem threadGet_out' {α : Type} {f : Tcb → α} {t : ObjRef} {σ : State Unit} {x : α × State Unit}
    (h : x ∈ (threadGet (Z := Unit) f t σ).1) : x.2 = σ ∧ ∃ tcb, σ.kheap t = some (.tcb tcb) ∧ x.1 = f tcb := by
  unfold threadGet at h
  obtain ⟨⟨tcb, σa⟩, ha, hx⟩ := h
  simp only [NonDet.getsThe] at ha
  cases hg : getTcb (Z := Unit) t σ with
  | none => rw [hg] at ha; exact ha.elim
  | some tcb0 =>
    rw [hg] at ha
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 ha)
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨rfl, _, PPS.getTcb_kh hg, rfl⟩

/-- **`tcb_sched_action f t`** with `f t` never adding `c`. -/
theorem qk_tcbSchedAction (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef)
    (hf : ∀ q, c ∉ q → c ∉ f t q) : QK c (tcbSchedAction (Z := Unit) f t) := by
  intro σ x hx hN
  unfold tcbSchedAction at hx
  obtain ⟨y1, h1, hx⟩ := hx
  obtain ⟨e1, -⟩ := threadGet_out' h1
  obtain ⟨y2, h2, hx⟩ := hx
  obtain ⟨e2, -⟩ := threadGet_out' h2
  obtain ⟨y3, h3, hx⟩ := hx
  unfold getTcbQueue at h3
  obtain ⟨y4, h4, h3⟩ := h3
  rw [Set.mem_singleton_iff.1 h4] at h3
  rw [Set.mem_singleton_iff.1 h3] at hx
  obtain ⟨y5, h5, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 h5] at hx
  unfold setTcbQueue at hx
  rw [Set.mem_singleton_iff.1 hx]
  simp only at e1 e2 ⊢
  rw [e2, e1]
  refine ⟨fun d p => ?_, hN.2⟩
  dsimp only
  split
  · rename_i hdp
    obtain ⟨rfl, rfl⟩ := hdp
    exact hf _ (hN.1 _ _)
  · exact hN.1 d p

theorem qk_tcbSchedDequeue (t : ObjRef) : QK c (tcbSchedAction (Z := Unit) tcbSchedDequeue t) :=
  qk_tcbSchedAction _ t fun q hq h => hq (List.mem_of_mem_filter h)

theorem qk_tcbSchedEnqueue {t : ObjRef} (ht : t ≠ c) : QK c (tcbSchedAction (Z := Unit) tcbSchedEnqueue t) :=
  qk_tcbSchedAction _ t fun q hq h => by
    unfold tcbSchedEnqueue at h
    split at h
    · rcases List.mem_cons.1 h with e | e
      · exact ht e.symm
      · exact hq e
    · exact hq h

theorem qk_setSchedulerAction {a : SchedulerAction} (ha : a ≠ .switchThread c) :
    QK c (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; exact qk_modify fun σ h => ⟨h.1, ha⟩

theorem qk_setSchedulerAction_choose : QK c (setSchedulerAction (Z := Unit) .chooseNewThread) :=
  qk_setSchedulerAction (fun e => by cases e)

theorem qk_setSchedulerAction_sw {t : ObjRef} (ht : t ≠ c) : QK c (setSchedulerAction (Z := Unit) (.switchThread t)) :=
  qk_setSchedulerAction (fun e => ht (by cases e; rfl))

end Q

/-- One step of a `QK` proof. -/
macro "qk_step0" : tactic => `(tactic| first
  | with_reducible exact qk_tcbSchedDequeue _
  | with_reducible exact qk_setSchedulerAction_choose
  | (with_reducible exact qk_tcbSchedEnqueue (by assumption))
  | (with_reducible exact qk_setSchedulerAction_sw (by assumption))
  | with_reducible exact qk_pure _ | with_reducible exact qk_pure' _ | with_reducible exact qk_fail
  | with_reducible exact qk_gets _ | with_reducible exact qk_get
  | with_reducible exact qk_assert _ | with_reducible exact qk_assertOpt _
  | with_reducible exact qk_getsThe _
  | with_reducible exact qk_selectF _ | with_reducible exact qk_select _
  | ((with_reducible apply qk_modify); intro _ h; first | exact h | exact ⟨h.1, fun e => by cases e⟩)
  | ((with_reducible apply qk_get_put); intro _ h; first | exact h | exact ⟨h.1, fun e => by cases e⟩)
  | (exact qk_get_put' (fun _ h => h))
  | (exact qk_get_put (fun _ h => h))
  | with_reducible exact qk_getObject _
  | with_reducible exact qk_doMachineOp _ | with_reducible exact qk_doExtendedOp _
  | (with_reducible refine qk_bind ?_ (fun _ => ?_))
  | (with_reducible refine qk_bind' ?_ (fun _ => ?_))
  | (with_reducible apply qk_ite) | (with_reducible apply qk_when) | (with_reducible apply qk_unless)
  | (with_reducible refine qk_maybeM (fun _ => ?_) _) | (with_reducible apply qk_liftM)
  | (with_reducible refine qk_whileLoop (fun _ => ?_) _)
  | (with_reducible refine qk_mapMx (fun _ => ?_) _)
  | (with_reducible refine qk_mapM (fun _ => ?_) _)
  | (with_reducible refine qk_forMx (fun _ => ?_) _)
  | with_reducible exact qke_pure _ | with_reducible exact qke_returnOk _ | with_reducible exact qke_throw _
  | with_reducible exact qke_throw' _ | with_reducible exact qke_throwOpt _ _ | with_reducible exact qke_assertE _
  | (with_reducible refine qke_bind ?_ (fun _ => ?_))
  | (with_reducible apply qke_liftE) | (with_reducible apply qke_ite) | (with_reducible apply qke_whenE)
  | (with_reducible apply qke_unlessE) | (with_reducible refine qk_catch ?_ (fun _ => ?_))
  | (with_reducible refine qke_handleE ?_ (fun _ => ?_)) | (with_reducible apply qke_liftME)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact qk_pure _)
  | (exact qk_pure _))

/-- A `QK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "qk_leaf" : tactic
macro_rules | `(tactic| qk_leaf) => `(tactic| fail "no qk_leaf")

macro "qk_auto" : tactic => `(tactic| repeat' (first | qk_leaf | qk_step0))

section Leaves
variable {c : ObjRef}

theorem qk_setObject' (p : ObjRef) (o : KernelObject) : QK c (setObject (Z := Unit) p o) := by
  unfold setObject; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_setObject' _ _)

theorem qk_setCap' (cp : Cap) (sl : CslotPtr) : QK c (setCap (Z := Unit) cp sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_setCap' _ _)

theorem qk_getCap' (sl : CslotPtr) : QK c (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getCap' _)

theorem qk_setOriginal' (slot : CslotPtr) (v : Bool) : QK c (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_setOriginal' _ _)

theorem qk_updateCdt' (f : Cdt → Cdt) : QK c (updateCdt (Z := Unit) f) := by
  unfold updateCdt; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_updateCdt' _)

theorem qk_setIoportMask' (f l : IoPort) (val : Bool) : QK c (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_setIoportMask' _ _ _)

theorem qk_threadSet' (f : Tcb → Tcb) (t : ObjRef) : QK c (threadSet (Z := Unit) f t) := by
  unfold threadSet; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_threadSet' _ _)

theorem qk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : QK c (threadGet (Z := Unit) f t) := by
  unfold threadGet; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_threadGet' _ _)

theorem qk_setThreadState' (t : ObjRef) (ts : ThreadState) : QK c (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_setThreadState' _ _)

theorem qk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    QK c (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getSimpleKo' _ _)

theorem qk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    QK c (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_setSimpleKo' _ _ _)

theorem qk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    QK c (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_updateSkObjRef' _ _ _ _)

theorem qk_getSchedContext' (q : ObjRef) : QK c (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getSchedContext' _)

theorem qk_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    QK c (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_updateSchedContext' _ _)

theorem qk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : QK c (asUser (Z := Unit) t u) := by
  unfold asUser; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_asUser' _ _)

theorem qk_replyUnlinkTcb' (t r : ObjRef) : QK c (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_replyUnlinkTcb' _ _)

theorem qk_getThreadState' (t : ObjRef) : QK c (getThreadState (Z := Unit) t) := by
  unfold getThreadState; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getThreadState' _)

theorem qk_cancelIpc' (t : ObjRef) : QK c (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_cancelIpc' _)

theorem qk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) :
    QK c (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getSkObjRef' _ _ _)

theorem qk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : QK c (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getScObjRef' _ _)

theorem qk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : QK c (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getTcbObjRef' _ _)

theorem qk_tcbReleaseRemove' (t : ObjRef) : QK c (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_tcbReleaseRemove' _)

theorem qk_schedContextCancelYieldTo' (t : ObjRef) : QK c (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_schedContextCancelYieldTo' _)

theorem qk_suspend' (t : ObjRef) : QK c (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_suspend' _)

theorem qk_getIrqSlot' (irq : Irq) : QK c (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getIrqSlot' _)

theorem qk_isFinalCap' (cp : Cap) : QK c (isFinalCap (Z := Unit) cp) := by
  unfold isFinalCap; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_isFinalCap' _)

theorem qk_freeIoportRange' (f l : IoPort) : QK c (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_freeIoportRange' _ _)

theorem qk_setIrqState' (i : IrqState) (irq : Irq) : QK c (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_setIrqState' _ _)

theorem qk_deletedIrqHandler' (irq : Irq) : QK c (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_deletedIrqHandler' _)

theorem qk_lookupIpcBuffer' (b : Bool) (t : ObjRef) : QK c (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_lookupIpcBuffer' _ _)

theorem qk_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, QK c (g a b)) :
    ∀ l1 l2, QK c (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => qk_bind (h a b) (fun _ => qk_zipWithMx' h l1 l2)
  | [], _ => qk_pure' _
  | _ :: _, [] => qk_pure' _
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible refine qk_zipWithMx' (fun _ _ => ?_) _ _)

theorem qk_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : QK c (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_storeWordOffs' _ _ _)

theorem qk_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : QK c (setMrs (Z := Unit) t b m) := by
  unfold setMrs; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_setMrs' _ _ _)

theorem qk_setMessageInfo' (t : ObjRef) (i : MessageInfo) : QK c (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_setMessageInfo' _ _)

theorem qk_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : QK c (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_archThreadSet' _ _)

theorem qk_saveFpuState' (t : ObjRef) : QK c (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_saveFpuState' _)

theorem qk_loadFpuState' (t : ObjRef) : QK c (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_loadFpuState' _)

theorem qk_setX64CurrentFpuOwner' (o : Option ObjRef) : QK c (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_setX64CurrentFpuOwner' _)

theorem qk_switchLocalFpuOwner' (o : Option ObjRef) : QK c (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_switchLocalFpuOwner' _)

theorem qk_getTcbQueue' (d : Domain) (p : Priority) : QK c (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getTcbQueue' _ _)

theorem qk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : QK c (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getScRefillSufficient' _ _)

theorem qk_getScRefillReady' (sc : ObjRef) : QK c (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getScRefillReady' _)

/-- **`reschedule_required`**: its enqueued target is the pending switch
target, not `c` (`NQ`); the action is then `choose_new_thread`. -/
theorem qk_rescheduleRequired' : QK c (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  refine qk_gets_bind fun a σ x ha hx hN => ?_
  cases a with
  | switchThread t =>
    have ht : t ≠ c := fun e => hN.2 (by rw [ha, e])
    refine (?_ : QK c _) σ x hx hN
    qk_auto
  | _ => refine (?_ : QK c _) σ x hx hN; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_rescheduleRequired')

theorem qk_testReschedule' (t : ObjRef) : QK c (testReschedule (Z := Unit) t) := by
  unfold testReschedule; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_testReschedule' _)

theorem qk_tcbEpDequeue' (t e : ObjRef) : QK c (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_tcbEpDequeue' _ _)

theorem qk_tcbNtfnDequeue' (t n : ObjRef) : QK c (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_tcbNtfnDequeue' _ _)

theorem qk_isRoundRobin' (sc : ObjRef) : QK c (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_isRoundRobin' _)

theorem qk_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : QK c (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_updateRefillHd' _ _)

theorem qk_getRefillHead' (sc : ObjRef) : QK c (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_getRefillHead' _)

theorem qk_refillPopHead' (sc : ObjRef) : QK c (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_refillPopHead' _)

theorem qk_mergeOverlappingRefills' (sc : ObjRef) : QK c (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_mergeOverlappingRefills' _)

theorem qk_refillHeadOverlappingLoop' (sc : ObjRef) : QK c (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_refillHeadOverlappingLoop' _)

theorem qk_refillUnblockCheck' (sc : ObjRef) : QK c (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_refillUnblockCheck' _)

theorem qk_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) :
    QK c (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_ifCondRefillUnblockCheck' _ _ _)

theorem qk_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) :
    QK c (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem qk_replyUnlinkSc' (sc r : ObjRef) : QK c (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_replyUnlinkSc' _ _)

theorem qk_schedContextDonate' (sc t : ObjRef) : QK c (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_schedContextDonate' _ _)

theorem qk_schedContextUpdateConsumed' (sc : ObjRef) : QK c (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_schedContextUpdateConsumed' _)

theorem qk_replyFromKernel' (t : ObjRef) (x : Data × List Data) : QK c (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_replyFromKernel' _ _)

theorem qk_setConsumed' (sc t : ObjRef) : QK c (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_setConsumed' _ _)

theorem qk_fpuRelease' (t : ObjRef) : QK c (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_fpuRelease' _)

theorem qk_archPostCapDeletion' (cp : ArchCap) : QK c (archPostCapDeletion (Z := Unit) cp) := by
  unfold archPostCapDeletion; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_archPostCapDeletion' _)

theorem qk_postCapDeletion' (cp : Cap) : QK c (postCapDeletion (Z := Unit) cp) := by
  unfold postCapDeletion; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_postCapDeletion' _)

theorem qk_emptySlot' (sl : CslotPtr) (cp : Cap) : QK c (emptySlot (Z := Unit) sl cp) := by
  unfold emptySlot; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_emptySlot' _ _)

theorem qk_schedContextMaybeUnbindNtfn' (n : ObjRef) : QK c (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_schedContextMaybeUnbindNtfn' _)

theorem qk_unbindMaybeNotification' (n : ObjRef) : QK c (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_unbindMaybeNotification' _)

theorem qk_replyRemove' (t r : ObjRef) : QK c (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_replyRemove' _ _)

theorem qk_unbindNotification' (t : ObjRef) : QK c (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_unbindNotification' _)

theorem qk_schedContextUnbindTcb' (sc : ObjRef) : QK c (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_schedContextUnbindTcb' _)

theorem qk_completeYieldTo' (t : ObjRef) : QK c (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_completeYieldTo' _)

theorem qk_unbindFromSc' (t : ObjRef) : QK c (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_unbindFromSc' _)

theorem qk_schedContextUnbindAllTcbs' (sc : ObjRef) : QK c (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_schedContextUnbindAllTcbs' _)

theorem qk_schedContextUnbindNtfn' (sc : ObjRef) : QK c (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_schedContextUnbindNtfn' _)

theorem qk_schedContextUnbindReply' (sc : ObjRef) : QK c (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_schedContextUnbindReply' _)

theorem qk_schedContextUnbindYieldFrom' (sc : ObjRef) : QK c (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_schedContextUnbindYieldFrom' _)

theorem qk_schedContextSetInactive' (sc : ObjRef) : QK c (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_schedContextSetInactive' _)

theorem qk_prepareThreadDelete' (t : ObjRef) : QK c (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_prepareThreadDelete' _)

theorem qk_archFinaliseCap' (cp : ArchCap) (x : Bool) : QK c (archFinaliseCap (Z := Unit) cp x) :=
  qk_of_archF (fa_archFinaliseCap cp x)
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_archFinaliseCap' _ _)

/-! ### The restarts, of a thread other than `c` -/

theorem qk_possibleSwitchTo {t : ObjRef} (ht : t ≠ c) : QK c (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; qk_auto

theorem qk_restartThreadIfNoFault {t : ObjRef} (ht : t ≠ c) : QK c (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault
  refine qk_bind (qk_threadGet' _ _) fun _ => qk_ite _ ?_ (qk_setThreadState' _ _)
  exact qk_bind (qk_setThreadState' _ _) fun _ => qk_bind (qk_getTcbObjRef' _ _) fun _ =>
    qk_bind (qk_ifSporadicCurScAssertRefillUnblockCheck' _) fun _ => qk_possibleSwitchTo ht

theorem qk_removeAndRestartEpQueuedThread {t : ObjRef} (e : ObjRef) (ht : t ≠ c) :
    QK c (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread
  refine qk_bind (qk_tcbEpDequeue' _ _) fun _ => qk_bind (qk_getThreadState' _) fun _ => ?_
  refine qk_bind (qk_pure _) fun _ => qk_bind (qk_maybeM (fun _ => qk_replyUnlinkTcb' _ _) _) fun _ => ?_
  exact qk_restartThreadIfNoFault ht

theorem qk_removeAndRestartNtfnQueuedThread {t : ObjRef} (n : ObjRef) (ht : t ≠ c) :
    QK c (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread
  exact qk_bind (qk_tcbNtfnDequeue' _ _) fun _ => qk_bind (qk_setThreadState' _ _) fun _ =>
    qk_bind (qk_getTcbObjRef' _ _) fun _ => qk_bind (qk_ifSporadicCurScAssertRefillUnblockCheck' _) fun _ =>
      qk_possibleSwitchTo ht

end Leaves

/-! ## The finalisations -/

/-- `c` is queued on no endpoint and no notification. -/
def NoQ (c : ObjRef) (σ : State Unit) : Prop :=
  (∀ e x, σ.kheap e = some (.endpoint x) → c ∉ x.epQueue) ∧
    ∀ n x, σ.kheap n = some (.notification x) → c ∉ ntfnQueueOf x

theorem qk_pure_bind {c : ObjRef} {α β : Type} {a : α} {k : α → NonDet (State Unit) β} (h : QK c (k a)) :
    QK c (pure a >>= k) := by
  intro σ x ⟨y, hy, hx⟩ hN
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx hN

/-- **`cancel_all_ipc` of an endpoint not queueing `c`.** -/
theorem qk_cancelAllIpc {c e : ObjRef} {σ : State Unit} {x : Unit × State Unit}
    (hq : ∀ xe, σ.kheap e = some (.endpoint xe) → c ∉ xe.epQueue)
    (hx : x ∈ (cancelAllIpc (Z := Unit) e σ).1) (hN : NQ c σ) : NQ c x.2 := by
  unfold cancelAllIpc at hx
  obtain ⟨⟨ep, σ1⟩, hy, hx⟩ := hx
  obtain ⟨hk, e1⟩ := Sched.getEndpoint_mem hy
  simp only at hk e1 hx
  subst e1
  have hc := hq ep hk
  have hb : ∀ q : List ObjRef, c ∉ q →
      QK c (do
        let queue ← pure q
        NonDet.mapMx (fun t => removeAndRestartEpQueuedThread (Z := Unit) t e) queue
        rescheduleRequired (Z := Unit)) := fun q hq' =>
    qk_pure_bind (qk_bind (qk_mapMx_mem _ fun t ht => qk_removeAndRestartEpQueuedThread e
      (fun h => hq' (by subst h; exact ht))) fun _ => qk_rescheduleRequired')
  cases ep with
  | idleEP => rw [Set.mem_singleton_iff.1 hx]; exact hN
  | sendEP q => exact hb q hc _ x hx hN
  | recvEP q => exact hb q hc _ x hx hN

/-- **`cancel_all_signals` of a notification not queueing `c`.** -/
theorem qk_cancelAllSignals {c r : ObjRef} {σ : State Unit} {n : Notification} {x : Unit × State Unit}
    (hk : σ.kheap r = some (.notification n)) (hc : c ∉ ntfnQueueOf n)
    (hx : x ∈ (cancelAllSignals (Z := Unit) r σ).1) (hN : NQ c σ) : NQ c x.2 := by
  unfold cancelAllSignals at hx
  rw [nd_bind_one (Notif.getNotification_eq hk)] at hx
  revert hx hc
  rcases n with ⟨o, b, sc⟩
  cases o with
  | waitingNtfn q =>
    intro hc hx
    exact (qk_bind (qk_mapMx_mem _ fun t ht => qk_removeAndRestartNtfnQueuedThread r
      (fun h => hc (by subst h; exact ht))) fun _ => qk_rescheduleRequired') σ x hx hN
  | _ => intro _ hx; rw [Set.mem_singleton_iff.1 hx]; exact hN

/-- **A final notification cap's work** (unbinds, then `cancel_all_signals`). -/
theorem nq_ntfnBody {c r : ObjRef} {σ : State Unit} {x : Unit × State Unit} (hI : Sched.Inv σ)
    (hV : Sched.SchedValid σ) (hq : ∀ n, σ.kheap r = some (.notification n) → c ∉ ntfnQueueOf n)
    (hm : x ∈ ((do
      schedContextMaybeUnbindNtfn (Z := Unit) r
      unbindMaybeNotification (Z := Unit) r
      cancelAllSignals (Z := Unit) r) σ).1) (hN : NQ c σ) : NQ c x.2 := by
  obtain ⟨⟨⟨⟩, σ1⟩, h1, hm⟩ := hm
  obtain ⟨⟨⟨⟩, σ2⟩, h2, h3⟩ := hm
  have hN1 := qk_schedContextMaybeUnbindNtfn' r σ _ h1 hN
  have hN2 := qk_unbindMaybeNotification' r σ1 _ h2 hN1
  have h10 := h1
  unfold schedContextMaybeUnbindNtfn at h10
  obtain ⟨z, hz, -⟩ := h10
  obtain ⟨n, hkn⟩ := PPS.getNtfnRef_mem hz
  obtain ⟨-, -, n1, hk1, ho1, hb1⟩ := Sched.msu_nfr hkn (fun c hc => hI.ntfnSc r n c hkn hc) h1
  have hb' : ∀ t, n1.ntfnBoundTcb = some t → ∃ x, σ1.kheap t = some (.tcb x) := by
    intro t ht
    obtain ⟨xt, hxt⟩ := hV.ntfnTcb r n t hkn (hb1 ▸ ht)
    obtain ⟨F1, -⟩ := Sched.msu_nfr hkn (fun c hc => hI.ntfnSc r n c hkn hc) h1
    obtain ⟨st, bn, ar, hx', -⟩ := F1.tcbF hxt
    exact ⟨_, hx'⟩
  obtain ⟨-, -, n2, hk2, ho2, -⟩ := Sched.umn_nfr hk1 hb' h2
  have hq2 : ntfnQueueOf n2 = ntfnQueueOf n := by simp only [ntfnQueueOf, ho2, ho1]
  exact qk_cancelAllSignals hk2 (by rw [hq2]; exact hq n hkn) h3 hN2

/-- **`fast_finalise`** from a state where `c` is queued nowhere. -/
theorem nq_fastFinalise {c : ObjRef} {σ : State Unit} {cp : Cap} {b : Bool} {y : Unit × State Unit}
    (hI : Sched.Inv σ) (hV : Sched.SchedValid σ) (hH : NoQ c σ)
    (hm : y ∈ (fastFinalise (Z := Unit) cp b σ).1) (hN : NQ c σ) : NQ c y.2 := by
  cases cp with
  | replyCap r _ =>
    simp only [fastFinalise] at hm
    exact (show QK c _ by qk_auto) σ y hm hN
  | endpointCap r _ _ =>
    simp only [fastFinalise, NonDet.when] at hm
    split at hm
    · exact qk_cancelAllIpc (fun xe hk => hH.1 r xe hk) hm hN
    · rw [Set.mem_singleton_iff.1 hm]; exact hN
  | notificationCap r _ _ =>
    simp only [fastFinalise, NonDet.when] at hm
    split at hm
    · exact nq_ntfnBody hI hV (fun n hk => hH.2 r n hk) hm hN
    · rw [Set.mem_singleton_iff.1 hm]; exact hN
  | nullCap =>
    simp only [fastFinalise] at hm
    rw [Set.mem_singleton_iff.1 hm]; exact hN
  | _ => simp only [fastFinalise] at hm; exact hm.elim

/-- **`deleting_irq_handler`.** -/
theorem nq_deletingIrqHandler {c : ObjRef} {σ : State Unit} {irq : Irq} {y : Unit × State Unit}
    (hI : Sched.Inv σ) (hV : Sched.SchedValid σ) (hH : NoQ c σ)
    (hm : y ∈ (deletingIrqHandler (Z := Unit) irq σ).1) (hN : NQ c σ) : NQ c y.2 := by
  unfold deletingIrqHandler getIrqSlot at hm
  obtain ⟨y0, hy0, hm⟩ := hm
  have e0 : y0.2 = σ := Vs.dk_gets (f := fun s : State Unit => s) _ σ y0 hy0
  unfold capDeleteOne at hm
  obtain ⟨y1, hy1, hm⟩ := hm
  have e1 : y1.2 = y0.2 := fk_getCapG (fun s => s) _ _ y1 hy1
  unfold NonDet.unless at hm
  beta_reduce at hm
  split at hm
  · rw [Set.mem_singleton_iff.1 hm]; simp only; rw [e1, e0]; exact hN
  · obtain ⟨y2, hy2, hm⟩ := hm
    have e2 : y2.2 = y1.2 := Vs.dk_gets (f := fun s : State Unit => s) _ _ y2 hy2
    obtain ⟨y3, hy3, hm⟩ := hm
    rw [e2, e1, e0] at hy3
    exact qk_emptySlot' _ _ y3.2 y hm (nq_fastFinalise hI hV hH hy3 hN)

/-- **`finalise_cap` keeps `NQ c`** from a state where `c` is queued on no
endpoint or notification (module docstring). -/
theorem nq_finaliseCap {c : ObjRef} {cp : Cap} {b : Bool} {σ : State Unit} {x : (Cap × Cap) × State Unit}
    (hI : Sched.Inv σ) (hV : Sched.SchedValid σ) (hH : NoQ c σ)
    (hx : x ∈ (finaliseCap (Z := Unit) cp b σ).1) (hN : NQ c σ) : NQ c x.2 := by
  cases cp with
  | endpointCap r _ _ =>
    simp only [finaliseCap, NonDet.liftM, NonDet.when] at hx
    obtain ⟨y, hy, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
    split at hy
    · exact qk_cancelAllIpc (fun xe hk => hH.1 r xe hk) hy hN
    · rw [Set.mem_singleton_iff.1 hy]; exact hN
  | notificationCap r _ _ =>
    simp only [finaliseCap, NonDet.liftM, NonDet.when] at hx
    obtain ⟨y, hy, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
    split at hy
    · exact nq_ntfnBody hI hV (fun n hk => hH.2 r n hk) hy hN
    · rw [Set.mem_singleton_iff.1 hy]; exact hN
  | irqHandlerCap irq =>
    simp only [finaliseCap] at hx
    split at hx
    · obtain ⟨y, hy, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 hx]
      exact nq_deletingIrqHandler hI hV hH hy hN
    · rw [Set.mem_singleton_iff.1 hx]; exact hN
  | _ => exact (show QK c (finaliseCap (Z := Unit) _ b) by unfold finaliseCap; qk_auto) σ x hx hN

/-- **The current thread is queued nowhere** when blocked on nothing
(`CtOK`), the endpoint queues' threads being blocked on their endpoint
(`EpQB`) and the notification queues' on their notification
(`SchedValid.ntfnQ`). -/
theorem noQ_of {σ : State Unit} (hV : Sched.SchedValid σ) (hQ : PPS.EpQB σ) (hc : CtOK σ) :
    NoQ σ.curThread σ := by
  refine ⟨fun e x hk hm => ?_, fun n x hk hm => ?_⟩
  · obtain ⟨xu, hu, hb⟩ := (hQ e x hk).2 _ hm
    have hn := (hc xu hu).2
    revert hb
    cases hts : xu.tcbState <;> intro hb <;> simp [epBlocked] at hb
    all_goals first | exact hn.2.2.2 _ _ _ hts | exact hn.2.2.1 _ _ hts
  · obtain ⟨xu, hu, hb⟩ := (hV.ntfnQ n x hk).2 _ hm
    exact (hc xu hu).2.2.1 n hb

/-- **`finalise_cap` keeps `CtNQ`** (ScPPR) from a `PPR0` state with the
queue facts (module docstring). -/
theorem ctnq_finaliseCap {cp : Cap} {b : Bool} {σ : State Unit} {x : (Cap × Cap) × State Unit}
    (hI : Sched.Inv σ) (hV : Sched.SchedValid σ) (hQ : PPS.EpQB σ) (hP : PPR0 σ)
    (hx : x ∈ (finaliseCap (Z := Unit) cp b σ).1) : CtNQ x.2 := by
  have hct := (Vs.dk_finaliseCap cp b).ct hx
  have h := nq_finaliseCap hI hV (noQ_of hV hQ hP.1.2.2.1) hx ⟨hP.1.2.2.2.2, hP.1.2.1 _⟩
  intro d p; rw [hct]; exact h.1 d p

end

end Fl4Proofs.P3.PPNQ
