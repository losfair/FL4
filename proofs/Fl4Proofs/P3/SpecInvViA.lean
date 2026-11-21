/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi1): **valid_idle** (l4v MCS
`valid_idle` with its scheduling-context part `idle_sc_at`), spec side only, outside
the JAtZ cone. Part A: the carried predicate and the leaves.

l4v (rt, Invariants_AI): `valid_idle s ≡ idle_tcb_at_proj (λ(st, ntfn, sc, yt, arch).
idle st ∧ ntfn = None ∧ sc = Some idle_sc_ptr ∧ yt = None ∧ valid_arch_idle arch)
(idle_thread s) s ∧ idle_thread s = idle_thread_ptr ∧ idle_sc_at idle_sc_ptr s`, with
`idle_sc_at` = a `SchedContext sc 0` with `sc_tcb = Some idle_thread_ptr`, no
notification / yield-from, `sc_replies = []`, period / badge 0, `MIN_REFILLS`.
Adaptation (FL4: the idle pointers are state fields `idleThread` / `idleSc`, never
written): `VIT N S T b σ` below. Kept of `idle_sc_at`: `sc_tcb = Some idle`, `sc_replies = []`
(the spec reads it: `reply_remove`'s `sc_with_reply`) and a valid size (FL4's idle SC
size is not fixed at 0; the spec only needs `set_object`'s type check to keep it an SC).
Period / refill-max / badge / notification / yield-from are not read by any consumer
(ctnq1's T2, off1's R6) and are left out.

`VI` also carries the parts of l4v's `sym_refs` / `valid_objs` / `idle_only_sc_refs`
the preservation proof needs (l4v proves them from those invariants):
* every other TCB is not bound to `S`, every other SC is not bound to `N`
  (`sym_refs` of the TCB↔SC binding, `idle_only_sc_refs`);
* `N` is in no endpoint / notification queue (l4v: `valid_objs`' queue states:
  queued threads are blocked, idle is not).
`b = true` adds "the current thread is not idle" (l4v `ct_active` at a syscall).
`T` pins one thread that has an SC (`VIT N S T b`; `VI N S b := VIT N S N b`, where it says
nothing new): `send_ipc`'s donation `sched_context_donate (the sender_sc) dest` needs the
sender bound to an SC (l4v: `cur_sc_tcb` + `sym_refs` for the current thread), else
`the None` is an unspecified SC that could be `S`.
-/
import Fl4Proofs.P3.SpecInvFaultTcbsW
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- The facts `VI` asks of the object at `p`. -/
def ObjOK (N S T p : ObjRef) : KernelObject → Prop
  | .tcb x => (p = N → x.tcbState = .idleThreadState ∧ x.tcbBoundNotification = none ∧
      x.tcbSchedContext = some S ∧ x.tcbYieldTo = none) ∧ (p ≠ N → x.tcbSchedContext ≠ some S) ∧
      (p = T → x.tcbSchedContext ≠ none)
  | .schedContext sc n => (p = S → sc.scTcb = some N ∧ sc.scReplies = [] ∧ validSchedContextSize n) ∧
      (p ≠ S → sc.scTcb ≠ some N)
  | .endpoint ep => N ∉ ep.epQueue
  | .notification nt => N ∉ nt.ntfnObj.ntfnQueue
  | _ => True

/-- **valid_idle (carried form)**: the idle pointers are `N` / `S`, `N` is a TCB and `S` an
SC, every object satisfies `ObjOK`; with `b`, the current thread is not idle. -/
def VIT (N S T : ObjRef) (b : Bool) (σ : State Unit) : Prop :=
  σ.idleThread = N ∧ σ.idleSc = S ∧ (b = true → σ.curThread ≠ N) ∧
    (∃ x, σ.kheap N = some (.tcb x)) ∧ (∃ sc n, σ.kheap S = some (.schedContext sc n)) ∧
    ∀ p o, σ.kheap p = some o → ObjOK N S T p o

/-- `VIT` with no extra pinned thread. -/
abbrev VI (N S : ObjRef) (b : Bool) : State Unit → Prop := VIT N S N b

/-- **`ValidIdle σ`**: the G1 field (l4v `valid_idle` + the reference facts above). -/
def ValidIdle (σ : State Unit) : Prop := VI σ.idleThread σ.idleSc false σ

variable {N S T : ObjRef} {b : Bool}

theorem vi_obj {σ : State Unit} (h : VIT N S T b σ) {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o) :
    ObjOK N S T p o := h.2.2.2.2.2 p o hp

/-- The l4v shape of `valid_idle`. -/
theorem vi_idle {σ : State Unit} (h : VIT N S T b σ) : ∃ x, σ.kheap σ.idleThread = some (.tcb x) ∧
    x.tcbState = .idleThreadState ∧ x.tcbBoundNotification = none ∧ x.tcbSchedContext = some σ.idleSc ∧
    x.tcbYieldTo = none := by
  obtain ⟨h1, h2, -, ⟨x, hx⟩, -, h6⟩ := h
  subst h1 h2
  exact ⟨x, hx, (h6 _ _ hx).1 rfl⟩

theorem vi_idleSc {σ : State Unit} (h : VIT N S T b σ) : ∃ sc n, σ.kheap σ.idleSc = some (.schedContext sc n) ∧
    sc.scTcb = some σ.idleThread ∧ sc.scReplies = [] ∧ validSchedContextSize n := by
  obtain ⟨h1, h2, -, -, ⟨sc, n, hs⟩, h6⟩ := h
  subst h1 h2
  exact ⟨sc, n, hs, (h6 _ _ hs).1 rfl⟩

theorem vi_ne {σ : State Unit} (h : VIT N S T b σ) : N ≠ S := by
  obtain ⟨-, -, -, ⟨x, hx⟩, ⟨sc, n, hs⟩, -⟩ := h
  intro e; subst e; rw [hx] at hs; cases hs

/-- A thread whose state is not `IdleThreadState` is not the idle thread. -/
theorem vi_ne_of_st {σ : State Unit} (h : VIT N S T b σ) {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hs : x.tcbState ≠ .idleThreadState) : t ≠ N := by
  intro e; subst e; exact hs ((vi_obj h hx).1 rfl).1

/-- **The idle thread is not schedulable** (ctnq1's T2 / off1's R6 consequence). -/
theorem vi_not_schedulable {σ : State Unit} (h : VIT N S T b σ) : schedulable N σ = false := by
  obtain ⟨-, -, -, ⟨x, hx⟩, -, h6⟩ := h
  have hst := ((h6 _ _ hx).1 rfl).1
  simp [schedulable, optPred, optMapSome, optMap, tcbsOfKh, tcbOf, hx, hst, runnable]

theorem vi_ne_of_schedulable {σ : State Unit} (h : VIT N S T b σ) {t : ObjRef} (hs : schedulable t σ = true) :
    t ≠ N := by
  rintro rfl; rw [vi_not_schedulable h] at hs; cases hs

/-! ## Writing one object -/

theorem vi_put {σ : State Unit} (h : VIT N S T b σ) {p : ObjRef} {k o : KernelObject} (hk : σ.kheap p = some k)
    (ht : aType k = aType o) (ho : ObjOK N S T p o) :
    VIT N S T b { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨h1, h2, h3, ⟨x, hx⟩, ⟨sc, n, hs⟩, h6⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · show ∃ x, Function.update σ.kheap p (some o) N = some (.tcb x)
    by_cases e : p = N
    · subst e; rw [hx] at hk; cases hk
      cases o <;> simp only [aType] at ht <;> (try split at ht) <;> (try cases ht)
      exact ⟨_, Function.update_self _ _ _⟩
    · exact ⟨x, by rw [Function.update_of_ne (Ne.symm e)]; exact hx⟩
  · show ∃ sc n, Function.update σ.kheap p (some o) S = some (.schedContext sc n)
    by_cases e : p = S
    · subst e; rw [hs] at hk; cases hk
      have hv := ((h6 _ _ hs).1 rfl).2.2
      rw [show aType (.schedContext sc n) = .aSchedContext n by simp only [aType, if_pos hv]] at ht
      cases o <;> simp only [aType] at ht <;> (try split at ht) <;> (try cases ht)
      exact ⟨_, _, Function.update_self _ _ _⟩
    · exact ⟨sc, n, by rw [Function.update_of_ne (Ne.symm e)]; exact hs⟩
  · intro q o' hq
    change Function.update σ.kheap p (some o) q = some o' at hq
    by_cases e : q = p
    · subst e; rw [Function.update_self] at hq; cases hq; exact ho
    · rw [Function.update_of_ne e] at hq; exact h6 q o' hq

theorem mem_setObject' {p : ObjRef} {o : KernelObject} {σ : State Unit} {y : Unit × State Unit}
    (h : y ∈ (setObject (Z := Unit) p o σ).1) :
    ∃ k, σ.kheap p = some k ∧ aType k = aType o ∧
      y.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  unfold setObject at h
  obtain ⟨⟨y1, y2⟩, hy, hx⟩ := h
  obtain ⟨e1, e2⟩ := mem_getObject hy
  simp only at e1 e2; subst e2
  obtain ⟨z, ⟨hz, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  exact ⟨y1, e1, hz, by rw [Set.mem_singleton_iff.1 hx]⟩

/-- `set_object p o`, the new object's facts from the old one (pinned at the write state). -/
theorem vi_setObject_p (p : ObjRef) (o : KernelObject)
    (ho : ∀ σ k, VIT N S T b σ → σ.kheap p = some k → aType k = aType o → ObjOK N S T p o) :
    IK (VIT N S T b) (setObject (Z := Unit) p o) := by
  intro σ hσ y hy
  obtain ⟨k, hk, ht, e⟩ := mem_setObject' hy
  rw [e]; exact vi_put hσ hk ht (ho σ k hσ hk ht)

theorem vi_setObject (p : ObjRef) (o : KernelObject) (ho : ObjOK N S T p o) :
    IK (VIT N S T b) (setObject (Z := Unit) p o) :=
  vi_setObject_p p o fun _ _ _ _ _ => ho

/-! ## Pinned object reads -/

/-- `get_object p`, the continuation knowing the object's facts. -/
theorem vi_gobj_bind {β : Type} (p : ObjRef) {k : KernelObject → NonDet (State Unit) β}
    (hk : ∀ o, ObjOK N S T p o → IK (VIT N S T b) (k o)) : IK (VIT N S T b) (getObject (Z := Unit) p >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk', e⟩ := mem_getObject hy
  rw [e] at hx
  exact hk y.1 (vi_obj hσ hk') σ hσ x hx

/-- `gets_the (get_tcb t)`, the continuation knowing the TCB's facts. -/
theorem vi_gtcb_bind {β : Type} (t : ObjRef) {k : Tcb → NonDet (State Unit) β}
    (hk : ∀ x, ObjOK N S T t (.tcb x) → IK (VIT N S T b) (k x)) :
    IK (VIT N S T b) (NonDet.getsThe (getTcb (Z := Unit) t) >>= k) :=
  ik_getsThe_bind fun x σ hx => fun hσ => hk x (vi_obj hσ (getTcb_kheap hx)) σ hσ

theorem vi_ite_bind {P : State Unit → Prop} {α β : Type} (c : Prop) [Decidable c] {m1 m2 : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (h1 : IK P (m1 >>= g)) (h2 : IK P (m2 >>= g)) :
    IK P ((if c then m1 else m2) >>= g) := by
  split <;> assumption

theorem vi_fail_bind {P : State Unit → Prop} {α β : Type} {g : α → NonDet (State Unit) β} :
    IK P ((NonDet.fail : NonDet (State Unit) α) >>= g) :=
  fun _ _ _ ⟨_, hy, _⟩ => hy.elim

/-! ## Automation -/

macro "vi_side" : tactic => `(tactic| first
  | trivial
  | (intro _ _ h; exact h)
  | (intro _; exact ⟨rfl, rfl, rfl, rfl⟩)
  | (intro _; exact ⟨rfl, rfl⟩)
  | (intro _ h; exact h)
  | (simp [ObjOK, Ntfn.ntfnQueue, Endpoint.epQueue]; done)
  | (simp_all [ObjOK]; done))

macro "vi0_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine ik_doMachineOp ?_ _); vi_side)
  | ((with_reducible refine ik_doExtendedOp ?_ _); vi_side)
  | with_reducible exact ik_getObject _
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

syntax "vi_leaf" : tactic
macro_rules | `(tactic| vi_leaf) => `(tactic| fail "no vi_leaf")

macro "vi_auto" : tactic => `(tactic| repeat' (first
  | vi_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE)
  | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); vi_side))
macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); vi_side))
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine vi_setObject _ _ ?_); vi_side))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gobj_bind _ fun _ _ => ?_))
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_gtcb_bind _ fun _ _ => ?_))

/-! ## TCB writers -/

/-- Same idle-relevant TCB fields. -/
def SameT (x y : Tcb) : Prop := y.tcbState = x.tcbState ∧ y.tcbBoundNotification = x.tcbBoundNotification ∧
  y.tcbSchedContext = x.tcbSchedContext ∧ y.tcbYieldTo = x.tcbYieldTo

theorem objOK_sameT {p : ObjRef} {x y : Tcb} (e : SameT x y) (h : ObjOK N S T p (.tcb x)) : ObjOK N S T p (.tcb y) := by
  obtain ⟨e1, e2, e3, e4⟩ := e
  simp only [ObjOK, e1, e2, e3, e4] at h ⊢; exact h

/-- `thread_set f t`, the new TCB's facts from the old one. -/
theorem vi_threadSet (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, ObjOK N S T t (.tcb x) → ObjOK N S T t (.tcb (f x))) :
    IK (VIT N S T b) (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact vi_gtcb_bind t fun x hx => vi_setObject _ _ (hf x hx)

theorem vi_threadSet_same (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, SameT x (f x)) :
    IK (VIT N S T b) (threadSet (Z := Unit) f t) :=
  vi_threadSet f t fun x h => objOK_sameT (hf x) h

theorem vi_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : IK (VIT N S T b) (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; vi_auto

theorem vi_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : IK (VIT N S T b) (asUser (Z := Unit) t u) := by
  unfold asUser; vi_auto

theorem vi_setMrs (t : ObjRef) (bf : Option ObjRef) (ms : List Message) :
    IK (VIT N S T b) (setMrs (Z := Unit) t bf ms) := by
  unfold setMrs; vi_auto

theorem mem_pure_viA {α : Type} {a : α} {σ : State Unit} {y : α × State Unit}
    (h : y ∈ ((pure a : NonDet (State Unit) α) σ).1) : y = (a, σ) := Set.mem_singleton_iff.1 h

/-- `set_cap`: the written object is the old CNode / TCB with one cap replaced (concrete
objects per arm, the old object's `ObjOK` carried over). -/
theorem vi_setCap (c : Cap) (sl : CslotPtr) : IK (VIT N S T b) (setCap (Z := Unit) c sl) := by
  obtain ⟨oref, cref⟩ := sl
  intro σ hσ y hy
  unfold setCap at hy
  obtain ⟨⟨o, s⟩, hz, hy⟩ := hy
  obtain ⟨hk, e⟩ := mem_getObject hz
  simp only at hk e; subst e
  cases o with
  | cnode sz cn =>
    (try simp only [letFun] at hy)
    split at hy
    · obtain ⟨⟨o', s'⟩, h1, hy⟩ := hy
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_pure_viA h1)
      obtain ⟨k, hk', ht, e⟩ := mem_setObject' hy
      rw [e]; exact vi_put hσ hk' ht trivial
    · obtain ⟨_, h1, _⟩ := hy; exact h1.elim
  | tcb x =>
    (try simp only [letFun] at hy)
    repeat' (split at hy)
    all_goals first
      | (obtain ⟨_, h1, _⟩ := hy; exact h1.elim)
      | (obtain ⟨⟨o', s'⟩, h1, hy⟩ := hy
         obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_pure_viA h1)
         obtain ⟨k, hk', ht, e⟩ := mem_setObject' hy
         rw [e]; exact vi_put hσ hk' ht (objOK_sameT (x := x) ⟨rfl, rfl, rfl, rfl⟩ (vi_obj hσ hk)))
  | _ =>
    (try simp only [letFun] at hy)
    obtain ⟨_, h1, _⟩ := hy; exact h1.elim

/-- `set_thread_state t ts`: `t` is not idle or the state stays idle. -/
theorem vi_setThreadState (t : ObjRef) (ts : ThreadState) (h : t = N → ts = .idleThreadState) :
    IK (VIT N S T b) (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (vi_threadSet _ _ fun x hx => ?_) fun _ => ?_
  · simp only [ObjOK] at hx ⊢
    exact ⟨fun e => ⟨h e, (hx.1 e).2⟩, hx.2.1, hx.2.2⟩
  · unfold setThreadStateAct setSchedulerAction
    repeat' ik_step0

/-! ## SC writers -/

/-- `update_sched_context p f`, the new SC's facts from the old one. -/
theorem vi_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ sc n, ObjOK N S T p (.schedContext sc n) → ObjOK N S T p (.schedContext (f sc) n)) :
    IK (VIT N S T b) (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  refine vi_gobj_bind p fun o ho => ?_
  cases o with
  | schedContext sc n => exact vi_setObject _ _ (hf sc n ho)
  | _ => exact ik_fail

/-- Same idle-relevant SC fields. -/
def SameS (x y : SchedContext) : Prop := y.scTcb = x.scTcb ∧ y.scReplies = x.scReplies

theorem vi_updateSchedContext_same (p : ObjRef) (f : SchedContext → SchedContext) (hf : ∀ x, SameS x (f x)) :
    IK (VIT N S T b) (updateSchedContext (Z := Unit) p f) :=
  vi_updateSchedContext p f fun sc n h => by
    obtain ⟨e1, e2⟩ := hf sc
    simp only [ObjOK, e1, e2] at h ⊢; exact h

/-! ## Endpoints, notifications, replies -/

/-- `set_simple_ko`: the old object is an endpoint / notification / reply. -/
theorem vi_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α)
    (h : ObjOK N S T p (f e)) : IK (VIT N S T b) (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo
  refine ik_bind (ik_getObject _) fun _ => ik_bind (ik_assert _) fun _ => ik_bind (ik_assert _) fun _ => ?_
  exact vi_setObject _ _ h

theorem vi_the_spec {α : Type} [Nonempty α] {P : α → Prop} (h : ∃! x, P x) : P (The P) := by
  unfold The; rw [dif_pos h]; exact (Classical.choose_spec h).1

theorem partialInv_some {α β : Type} [Nonempty α] {f : α → β} {x : β} {a : α} (h : partialInv f x = some a) :
    f a = x := by
  unfold partialInv at h
  by_cases hu : ∃! y, f y = x
  · rw [if_pos hu] at h; cases h; exact vi_the_spec hu
  · rw [if_neg hu] at h; cases h

theorem mem_getSimpleKo {α : Type} [Nonempty α] {f : α → KernelObject} {p : ObjRef} {σ : State Unit}
    {y : α × State Unit} (h : y ∈ (getSimpleKo (Z := Unit) f p σ).1) : σ.kheap p = some (f y.1) ∧ y.2 = σ := by
  unfold getSimpleKo at h
  obtain ⟨⟨o, s⟩, hz, hy⟩ := h
  obtain ⟨hk, e⟩ := mem_getObject hz
  simp only at hk e
  rw [e] at hy
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  cases hpi : partialInv f o with
  | none => rw [hpi] at hy; exact hy.elim
  | some a =>
    rw [hpi] at hy
    have hy' : y = (a, σ) := Set.mem_singleton_iff.1 hy
    subst hy'
    exact ⟨by rw [partialInv_some hpi]; exact hk, rfl⟩

/-- `update_sk_obj_ref`: the new object's facts from the old one. -/
theorem vi_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef)
    (h : ∀ a, ObjOK N S T ref (C a) → ObjOK N S T ref (C (f (fun _ => new) a))) :
    IK (VIT N S T b) (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨hk, e⟩ := mem_getSimpleKo hz
  rw [e] at hy
  exact vi_setSimpleKo C ref _ (h z.1 (vi_obj hσ hk)) σ hσ y hy

macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine vi_setSimpleKo _ _ _ ?_); vi_side))
macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine vi_updateSkObjRef _ _ _ _ ?_); vi_side))
macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine vi_threadSet_same _ _ ?_); vi_side))
macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine vi_updateSchedContext_same _ _ ?_); vi_side))
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archThreadSet _ _)
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_asUser _ _)
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setMrs _ _ _)
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setCap _ _)

end

end Fl4Proofs.P3.SInvI
