/-
P3 (DESIGN.md §9), invariant line G1 (invA2): **FaultTcbsS across the spec
functions that wake a thread** (spec side only), by hand: at a read of the woken
thread's state or fault, `FTL L` gives it no fault (`ftl_cons`), the rest runs
in `FTL (t :: L)` by the generated lemmas (SpecInvFaultTcbsF*), and the wake-up
is `ft_setThreadState`'s `t ∈ t :: L` case.
-/
import Fl4Proofs.P3.SpecInvFaultTcbsF6
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

variable {L : List ObjRef}

/-! ## Moving a thread into `L` -/

theorem ftl_cons {σ : State Unit} (h : FTL L σ) {t : ObjRef}
    (ht : ∀ x, σ.kheap t = some (.tcb x) → x.tcbFault = none) : FTL (t :: L) σ := by
  intro p x hp
  refine ⟨(h p x hp).1, fun hm => ?_⟩
  rcases List.mem_cons.1 hm with rfl | hm
  · exact ht x hp
  · exact (h p x hp).2 hm

theorem ftl_tail {σ : State Unit} {t : ObjRef} (h : FTL (t :: L) σ) : FTL L σ :=
  fun p x hp => ⟨(h p x hp).1, fun hm => (h p x hp).2 (List.mem_cons_of_mem _ hm)⟩

/-- A thread whose state holds no fault (Running, Restart, a receive, idle) has none. -/
theorem ftl_noFault {σ : State Unit} (h : FTL L σ) {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hs : ¬ faultTcbSt x.tcbState) : x.tcbFault = none := by
  by_contra hf
  exact hs ((h t x hx).1 hf)

/-- Run `m` with `t` added to `L`, from a state where `t` has no fault. -/
theorem ikp_cons {α : Type} {σ : State Unit} {t : ObjRef} {m : NonDet (State Unit) α}
    (ht : FTL L σ → ∀ x, σ.kheap t = some (.tcb x) → x.tcbFault = none) (hm : FTK (t :: L) m) :
    IKp (FTL L) σ m :=
  fun hσ y hy => ftl_tail (hm σ (ftl_cons hσ (ht hσ)) y hy)

theorem mem_threadGet {β : Type} {f : Tcb → β} {t : ObjRef} {σ : State Unit} {y : β × State Unit}
    (h : y ∈ (threadGet (Z := Unit) f t σ).1) : ∃ x, σ.kheap t = some (.tcb x) ∧ y = (f x, σ) := by
  unfold threadGet at h
  obtain ⟨z, hz, hy⟩ := h
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    have hz' := Set.mem_singleton_iff.1 hz
    subst hz'
    exact ⟨a, getTcb_kheap e, Set.mem_singleton_iff.1 hy⟩

/-- A `thread_get` read, pinned: the continuation runs at the read's state with the TCB there. -/
theorem ik_threadGet_bind {P : State Unit → Prop} {β γ : Type} {f : Tcb → β} {t : ObjRef}
    {k : β → NonDet (State Unit) γ}
    (h : ∀ σ x, σ.kheap t = some (.tcb x) → IKp P σ (k (f x))) : IK P (threadGet (Z := Unit) f t >>= k) := by
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hz
  exact h σ x hx hσ y hy


/-! ## Clearing a fault: `t` joins `L` -/

/-- Pre/post form of `IK`. -/
def HK (P Q : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ x, x ∈ (m σ).1 → Q x.2

theorem hk_bind {P R Q : State Unit → Prop} {α γ : Type} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) γ} (hm : HK P R m) (hg : ∀ a, HK R Q (g a)) : HK P Q (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  exact hg y.1 y.2 (hm σ hσ y hy) x hx

theorem hk_of_ik {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : IK P m) : HK P P m := h

theorem ik_of_hk {α : Type} {t : ObjRef} {m : NonDet (State Unit) α} (h : HK (FTL L) (FTL (t :: L)) m) :
    FTK L m :=
  fun σ hσ x hx => ftl_tail (h σ hσ x hx)

theorem mem_setObject {p : ObjRef} {o : KernelObject} {σ : State Unit} {y : Unit × State Unit}
    (h : y ∈ (setObject (Z := Unit) p o σ).1) :
    y.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  unfold setObject at h
  obtain ⟨⟨y1, y2⟩, hy, hx⟩ := h
  obtain ⟨-, e2⟩ := mem_getObject hy
  simp only at e2; subst e2
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]

/-- After `thread_set (tcb_fault := None)` on `t`, `t` has no fault. -/
theorem clearFault_post (t : ObjRef) {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t σ).1) :
    ∀ x, y.2.kheap t = some (.tcb x) → x.tcbFault = none := by
  unfold threadSet at hy
  obtain ⟨z, hz, hy⟩ := hy
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    have hz' := Set.mem_singleton_iff.1 hz
    subst hz'
    rw [mem_setObject hy]
    intro x hx
    dsimp only at hx
    simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hx
    rw [← hx]

/-- `thread_set (tcb_fault := None)`: afterwards `t` has no fault. -/
theorem hk_clearFault (t : ObjRef) :
    HK (FTL L) (FTL (t :: L)) (threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t) :=
  fun σ hσ y hy => ftl_cons ((by ft_auto : FTK L (threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t)) σ hσ y hy)
    (clearFault_post t hy)

/-- `cancel_ipc`: it clears the fault first; afterwards `t` has no fault. -/
theorem hk_cancelIpc (t : ObjRef) : HK (FTL L) (FTL (t :: L)) (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc
  refine hk_bind (hk_of_ik (by ft_auto)) fun st => hk_bind (hk_clearFault t) fun _ => hk_of_ik ?_
  ft_auto

theorem ik_hk_bind {α γ : Type} {t : ObjRef} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ}
    (hm : HK (FTL L) (FTL (t :: L)) m) (hg : ∀ a, FTK (t :: L) (g a)) : FTK L (m >>= g) :=
  ik_of_hk (hk_bind hm fun a => hk_of_ik (hg a))

/-- One step of a wake-up proof: a state read adds the thread to `L` when its
state holds no fault; a fault read adds it when the fault is none; a fault clear
(`thread_set`, `cancel_ipc`) adds it. -/
macro "ftw_rds" : tactic => `(tactic| (show IK _ (getThreadState (Z := Unit) _ >>= _); unfold getThreadState; refine ik_threadGet_bind fun σ x hx => ?_; (try dsimp only); cases hs : x.tcbState <;> (try dsimp only) <;> first | (refine ikp_cons (fun hσ y hy => by rw [hx] at hy; cases hy; exact ftl_noFault hσ hx (by rw [hs]; exact fun h => h)) ?_) | (refine ikp_of_ik ?_ σ)))

macro "ftw_rdf" : tactic => `(tactic| (show IK _ (threadGet (Z := Unit) Tcb.tcbFault _ >>= _); refine ik_threadGet_bind fun σ x hx => ?_; (try dsimp only); cases hf : x.tcbFault <;> (try dsimp only) <;> first | (refine ikp_cons (fun _ y hy => by rw [hx] at hy; cases hy; exact hf) ?_) | (refine ikp_of_ik ?_ σ)))

macro "ftw_rd" : tactic => `(tactic| first | ftw_rds | ftw_rdf | (refine ik_hk_bind (hk_clearFault _) fun _ => ?_) | (refine ik_hk_bind (hk_cancelIpc _) fun _ => ?_))

macro "ftw_auto" : tactic => `(tactic| repeat' (first | ftw_rd | ft_leaf | (show IK _ (ite _ _ _); split) | (show IK _ (ite _ _ _ >>= _); split) | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless) | (exfalso; contradiction)))

/-! ## The wake-ups -/

theorem ft_restartThreadIfNoFault (t : ObjRef) : FTK L (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; ftw_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_restartThreadIfNoFault _)

theorem ft_activateThread : FTK L (activateThread (Z := Unit)) := by
  unfold activateThread; ftw_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_activateThread)

theorem ft_restart (t : ObjRef) : FTK L (restart (Z := Unit) t) := by
  unfold restart; ftw_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_restart _)

end

end Fl4Proofs.P3.SInv
