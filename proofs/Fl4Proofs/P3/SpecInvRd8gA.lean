/-
P3 (DESIGN.md §9), invariant line G1 (rd8g): **`Sched.BlockedScActive`
carried spec-side: the frame kit** (spec side only, outside the JAtZ cone;
KENTRY-PLAN rd8e handoff 1).

`Sched.BlockedScActive σ` (ScInv.lean; l4v `active_if_bound_sc_tcb_at` for
ipc-queued threads and `active_reply_scs`) reads the heap only: of each SC
its bound TCB, whether its reply stack is empty and whether it is active
(`scRefillMax`), and of each TCB whether its state is ipc-queued. So every
`modify` of another state field keeps it (`ik_step0`'s `exact h`), and a heap
write keeps it when it is `OKB`:

* a TCB written in an ipc-queued state was a TCB in an ipc-queued state;
* an SC written over an SC is active, or keeps / clears its bound TCB, does
  not make an empty reply stack non-empty, and does not deactivate.

* `BSA`, `BAK` / `BAKE` (the family `IK BSA`), `OKB`, **`bsa_upd`**.
* Leaves: `ba_setObject_p` (pinned), `ba_setObject` (`NTS`), `ba_setSimpleKo`,
  `ba_setTcb_keep`, `ba_threadSet` (state kept), `ba_threadSet_nq` /
  **`ba_setThreadState`** (to a state that is not ipc-queued),
  `ba_setThreadStateAct`, `ba_archThreadSet`, `ba_asUser`, `ba_setMrs`,
  `ba_setCap`, `ba_optionUpdateThread`, **`ba_updateSchedContext`** (`SCK`:
  bound TCB kept or cleared, reply stack not grown from empty, refill max kept); `ba_side` / `ba_leaf` / `ba_auto`.
  The generated family over them: SpecInvRd8gF1..F5 (scratch/rd8g, untracked).
-/
import Fl4Proofs.P3.SpecInvRdC
import Fl4Proofs.P3.ScInv
open Classical

namespace Fl4Proofs.P3.SInvR.B8g
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-- The carried fact (ScInv.lean's `Sched.BlockedScActive`). -/
abbrev BSA (σ : State Unit) : Prop := Sched.BlockedScActive σ

abbrev BAK {α : Type} (m : NonDet (State Unit) α) : Prop := IK BSA m
abbrev BAKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE BSA m

/-- A heap write of `o` over `old` that `BSA` allows. -/
def OKB (old : Option KernelObject) (o : KernelObject) : Prop :=
  (∀ y, o = .tcb y → ipcQueuedThreadState y.tcbState = true →
    ∃ x, old = some (.tcb x) ∧ ipcQueuedThreadState x.tcbState = true) ∧
  (∀ y n, o = .schedContext y n → scActive y = true ∨ ∃ x m, old = some (.schedContext x m) ∧ (y.scTcb = x.scTcb ∨ y.scTcb = none) ∧
    (y.scReplies ≠ [] → x.scReplies ≠ []) ∧ (scActive x = true → scActive y = true))

/-- **`BSA` across one `OKB` heap write.** -/
theorem bsa_upd {σ : State Unit} (h : BSA σ) (p : ObjRef) (o : KernelObject) (hp : OKB (σ.kheap p) o) :
    BSA { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨h1, h2⟩ := hp
  have hk : ∀ q, q ≠ p → (Function.update σ.kheap p (some o)) q = σ.kheap q :=
    fun q e => Function.update_of_ne e _ _
  have hkp : (Function.update σ.kheap p (some o)) p = some o := Function.update_self _ _ _
  constructor
  · intro q y n t x hq hy ht hst
    change Function.update σ.kheap p (some o) q = _ at hq
    change Function.update σ.kheap p (some o) t = _ at ht
    by_cases eq : q = p
    · rw [eq, hkp] at hq
      rcases h2 y n (Option.some.inj hq) with hA | ⟨x0, m, ho, e1, -, e3⟩
      · exact hA
      have etp : t ≠ p := by
        rintro rfl
        rw [hkp] at ht
        have := (Option.some.inj ht).symm.trans (Option.some.inj hq)
        cases this
      rw [hk t etp] at ht
      rw [eq] at *
      rcases e1 with e1 | e1
      · exact e3 (h.tcb p x0 m t x ho (e1.symm.trans hy) ht hst)
      · rw [e1] at hy; cases hy
    · rw [hk q eq] at hq
      by_cases etp : t = p
      · rw [etp, hkp] at ht
        obtain ⟨x0, ho, hq0⟩ := h1 x (Option.some.inj ht) hst
        rw [etp] at hy
        exact h.tcb q y n p x0 hq hy ho hq0
      · rw [hk t etp] at ht; exact h.tcb q y n t x hq hy ht hst
  · intro q y n hq hr
    change Function.update σ.kheap p (some o) q = _ at hq
    by_cases eq : q = p
    · rw [eq, hkp] at hq
      rcases h2 y n (Option.some.inj hq) with hA | ⟨x0, m, ho, -, e2, e3⟩
      · exact hA
      exact e3 (h.replies p x0 m ho (e2 hr))
    · rw [hk q eq] at hq; exact h.replies q y n hq hr

/-- `BSA` reads the heap only. -/
theorem bsa_kh {σ σ' : State Unit} (h : BSA σ) (e : σ'.kheap = σ.kheap) : BSA σ' := by
  constructor
  · intro q y n t x hq hy ht hst
    rw [e] at hq ht; exact h.tcb q y n t x hq hy ht hst
  · intro q y n hq hr
    rw [e] at hq; exact h.replies q y n hq hr

theorem ba_modify (g : State Unit → State Unit) (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    BAK (NonDet.modify g) :=
  ik_modify fun σ h => bsa_kh h (hg σ)

theorem okb_ntb {old : Option KernelObject} {o : KernelObject} (h1 : ∀ y, o ≠ .tcb y)
    (h2 : ∀ y n, o ≠ .schedContext y n) : OKB old o :=
  ⟨fun y e => absurd e (h1 y), fun y n e => absurd e (h2 y n)⟩

/-- Writing an active SC over an SC. -/
theorem okb_act {y z : SchedContext} {n m : Nat} (h : scActive z = true) :
    OKB (some (.schedContext y n)) (.schedContext z m) :=
  ⟨(fun _ e => by cases e), (fun z' m' e => by cases e; exact Or.inl h)⟩

theorem okb_nts {old : Option KernelObject} {o : KernelObject} (ho : NTS o) : OKB old o := by
  refine okb_ntb (fun y e => ?_) (fun y n e => ?_) <;> (subst e; exact False.elim ho)

theorem okb_simple {old : Option KernelObject} {o : KernelObject}
    (h : aType o ∈ ({.aEndpoint, .aNTFN, .aReply} : Set AType)) : OKB old o := by
  refine okb_ntb (fun y e => ?_) (fun y n e => ?_) <;> subst e
  · simp [aType] at h
  · simp only [aType] at h; split_ifs at h <;> simp at h

/-- A TCB rewrite keeping the state. -/
theorem okb_tcb {x y : Tcb} (h1 : y.tcbState = x.tcbState) : OKB (some (.tcb x)) (.tcb y) := by
  refine ⟨fun y' e hq => ?_, fun _ _ e => by cases e⟩
  cases e; exact ⟨x, rfl, by rw [← h1]; exact hq⟩

/-- A TCB written in a state that is not ipc-queued. -/
theorem okb_nq {old : Option KernelObject} {y : Tcb} (h : ipcQueuedThreadState y.tcbState = false) :
    OKB old (.tcb y) := by
  refine ⟨fun y' e hq => ?_, fun _ _ e => by cases e⟩
  cases e; rw [h] at hq; cases hq

/-! ## Heap writes -/

theorem ba_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit) (hp : OKB (σ.kheap p) o) :
    IKp BSA σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact bsa_upd hσ p o hp

theorem ba_setObject (p : ObjRef) (o : KernelObject) (ho : NTS o) : BAK (setObject (Z := Unit) p o) :=
  fun σ => ba_setObject_p p o σ (okb_nts ho)

theorem ba_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    BAK (setSimpleKo (Z := Unit) f p e) := by
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
  have hsimp' : aType (f e) ∈ ({.aEndpoint, .aNTFN, .aReply} : Set AType) := by rw [← hty]; exact hsimp
  exact bsa_upd hσ p _ (okb_simple hsimp')

theorem ba_setTcb_keep (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (h1 : y.tcbState = x.tcbState) : IKp BSA σ (setObject (Z := Unit) p (.tcb y)) :=
  ba_setObject_p _ _ σ (by rw [hx]; exact okb_tcb h1)

theorem ba_threadSet (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, (f x).tcbState = x.tcbState) :
    BAK (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx => ba_setTcb_keep _ x σ (getTcb_kheap hx) _ (hf x)

theorem ba_threadSet_nq (ts : ThreadState) (t : ObjRef) (h : ipcQueuedThreadState ts = false) :
    BAK (threadSet (Z := Unit) (fun tcb => { tcb with tcbState := ts }) t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx => ba_setObject_p _ _ σ (okb_nq h)

theorem ba_setThreadStateAct (t : ObjRef) : BAK (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct setSchedulerAction
  repeat' (first | ((with_reducible refine ba_modify _ ?_); intro _; rfl) | ik_step0)

theorem ba_setThreadState (t : ObjRef) (ts : ThreadState) (h : ipcQueuedThreadState ts = false) :
    BAK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ik_bind (ba_threadSet_nq ts t h) fun _ => ba_setThreadStateAct t

theorem ba_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : BAK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => ba_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl

theorem ba_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : BAK (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (ba_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl) fun _ => ik_pure _

theorem ba_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : BAK (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (ba_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl) fun _ => ?_
  repeat' (first | ((with_reducible refine ba_modify _ ?_); intro _; rfl) | (with_reducible exact ik_doMachineOp (fun _ _ h => bsa_kh h rfl) _) | ik_step0 | ik_unfold)

theorem ba_setCap (c : Cap) (sl : CslotPtr) : BAK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (ba_setObject_p _ _ σ (okb_ntb (fun _ e => by cases e) (fun _ _ e => by cases e)))
    · exact ikp_fail_bind
  · rename_i tcb
    split
    · exact ikp_pure_bind (ba_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (ba_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (ba_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (ba_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (ba_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (ba_setTcb_keep _ tcb σ hk _ rfl)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem ba_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbState = x.tcbState) :
    BAK (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact ba_threadSet _ _ (h _)

/-- An SC rewrite that `BSA` allows: bound TCB kept or cleared, an empty reply stack stays empty, refill max kept. -/
def SCK (y z : SchedContext) : Prop :=
  (z.scTcb = y.scTcb ∨ z.scTcb = none) ∧ (z.scReplies ≠ [] → y.scReplies ≠ []) ∧
    z.scRefillMax = y.scRefillMax

theorem okb_sc {y : SchedContext} {n : Nat} (f : SchedContext → SchedContext)
    (hf : SCK y (f y)) : OKB (some (.schedContext y n)) (.schedContext (f y) n) := by
  refine ⟨(fun _ e => by cases e), fun y' m e => ?_⟩
  cases e
  refine Or.inr ⟨y, n, rfl, hf.1, hf.2.1, fun h => ?_⟩
  show activeSc (f y).scRefillMax = true
  rw [hf.2.2]; exact h

theorem ba_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, SCK y (f y)) : BAK (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  dsimp only at hx
  split at hx
  · rename_i sc n
    refine ba_setObject_p _ _ _ ?_ hσ x hx
    rw [hk]; exact okb_sc f (hf sc)
  · exact hx.elim

/-! ## `ba_auto` -/

macro "ba_side" : tactic => `(tactic| first
  | trivial
  | rfl
  | (intro _; rfl)
  | (intro _ _; rfl)
  | (intro _; exact ⟨rfl, rfl, rfl⟩)
  | (intro _ _; exact ⟨rfl, rfl, rfl⟩)
  | (intro _; exact ⟨rfl, rfl⟩)
  | (intro _; exact ⟨Or.inl rfl, id, rfl⟩)
  | (intro _; exact ⟨Or.inr rfl, id, rfl⟩)
  | (intro _; exact ⟨Or.inl rfl, fun h => absurd rfl h, rfl⟩)
  | (intro _; refine ⟨Or.inl rfl, fun h e => h ?_, rfl⟩; simp [scRepliesUpdate, e])
  | (intro _ h; cases h; done)
  | tq_side)

syntax "ba_leaf" : tactic
macro_rules | `(tactic| ba_leaf) => `(tactic| fail "no ba_leaf")

macro "ba_auto" : tactic => `(tactic| repeat' (first | ba_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| ba_leaf) => `(tactic| ((with_reducible refine ba_modify _ ?_); intro _; rfl))
macro_rules | `(tactic| ba_leaf) => `(tactic| ((with_reducible apply ik_put_get); intro _ h; exact bsa_kh h rfl))
macro_rules | `(tactic| ba_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact bsa_kh h rfl))
macro_rules | `(tactic| ba_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); intro _ _ h; exact bsa_kh h rfl))
macro_rules | `(tactic| ba_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| ba_leaf) => `(tactic| ((with_reducible refine ba_setObject _ _ ?_); ba_side))
macro_rules | `(tactic| ba_leaf) => `(tactic| with_reducible exact ba_setSimpleKo _ _ _)
macro_rules | `(tactic| ba_leaf) => `(tactic| ((with_reducible refine ba_threadSet _ _ ?_); ba_side))
macro_rules | `(tactic| ba_leaf) => `(tactic| with_reducible exact ba_archThreadSet _ _)
macro_rules | `(tactic| ba_leaf) => `(tactic| with_reducible exact ba_asUser _ _)
macro_rules | `(tactic| ba_leaf) => `(tactic| with_reducible exact ba_setMrs _ _ _)
macro_rules | `(tactic| ba_leaf) => `(tactic| with_reducible exact ba_setCap _ _)
macro_rules | `(tactic| ba_leaf) => `(tactic| ((with_reducible refine ba_setThreadState _ _ ?_); ba_side))
macro_rules | `(tactic| ba_leaf) => `(tactic| ((with_reducible refine ba_optionUpdateThread _ _ _ ?_); ba_side))
macro_rules | `(tactic| ba_leaf) => `(tactic| ((with_reducible refine ba_updateSchedContext _ _ ?_); ba_side))
macro_rules | `(tactic| ba_leaf) => `(tactic| with_reducible exact ba_setThreadStateAct _)

end

end Fl4Proofs.P3.SInvR.B8g
