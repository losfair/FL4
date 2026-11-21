/-
P3 (DESIGN.md §9), invariant line G1 (nq1): **NtfnQB across the budget
charge, object creation / deletion and `perform_invocation`** (spec side only).

* Budget: `end_timeslice` from a state whose current thread is runnable (so
  in no queue; `charge_budget` calls it only after reading `schedulable ct`),
  `charge_budget`, `check_budget`, `check_budget_restart`, `preemption_path`,
  `handle_yield`: no premise; a timeout fault may block the current thread on
  its handler's endpoint, so the posts are `NQ []` (nq2).
* Object creation / deletion (the only writers that can replace a queued TCB):
  `delete_objects` of a region holding no queued thread (`nq_deleteObjects_p`),
  `retype_region` at addresses no queued thread occupies
  (`nq_retypeRegionWith_p`; default TCBs are Inactive, default notifications
  idle). `reset_untyped_cap` / `invoke_untyped` from the decode's facts
  (`SInvU.UtRetOK`, `SInvU.UtInv`: the retype addresses hold no object, ut1's
  `utRet_fresh` / `utRet_fresh_after_reset`) and the [J] fact `NqDet` for the
  reset's detype; MakePool's `perform_asid_control_invocation` from `NqMp`.
* `nq_fl4PerformInvocation`: from `NQ K`, the current thread in `K` (the
  sender of an endpoint invocation), `PJ K` (nq3: the threads of `K` are not
  blocked on an endpoint nor BlockedOnReply; the current thread is Restart)
  and the decode facts `NqDec` with `UtInv`, `NqDet` (untyped / MakePool);
  post `NQ []`, and `NQ K` for a non-blocking invocation (nq3: only a
  blocking send may queue a thread of `K`; a reply's receiver and a
  `set_priority` target that is moved are no threads of `K` by `PJ K`).
-/
import Fl4Proofs.P3.SpecInvNtfnQG2
import Fl4Proofs.P3.SpecInvNtfnQP2
import Fl4Proofs.P3.SpecInvUtR
import Fl4Proofs.P3.SpecInvUtN
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

variable {K : List ObjRef}

/-! ## The budget charge -/

theorem ik_eq_isRoundRobin (p : ObjRef) (σ : State Unit) :
    IK (fun s => s = σ) (isRoundRobin (Z := Unit) p) := by
  unfold isRoundRobin; repeat' (first | ik_step0 | ik_unfold)

/-- `end_timeslice` from a state whose current thread is runnable (a timeout
fault may block it, so the post forgets `K`). -/
theorem nq_endTimeslice_p (cto : Bool) (σ : State Unit)
    (hct : ∀ x, σ.kheap σ.curThread = some (.tcb x) → runnable x.tcbState = true) :
    HKp (NQ K) (NQ []) σ (endTimeslice (Z := Unit) cto) := by
  intro hσ y hy
  unfold endTimeslice at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have e2 : y2.2 = σ := ik_eq_isRoundRobin _ σ σ rfl y2 h2
  obtain ⟨r2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  rw [mem_gets h3] at hy
  obtain ⟨y4, h4, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet h4
  have hb : ¬ isBoN x.tcbState := by
    have := hct x hx; revert this; cases x.tcbState <;> simp [runnable, isBoN]
  have he : epBlocked x.tcbState = none := by
    have := hct x hx; revert this; cases x.tcbState <;> simp [runnable, epBlocked]
  refine (?_ : HK (NQ (σ.curThread :: K)) (NQ []) _) σ (nq_consR hσ hx hb he) y hy
  have hc : σ.curThread ∈ σ.curThread :: K := List.mem_cons_self ..
  have htail : ∀ valid : Bool, HK (NQ (σ.curThread :: K)) (NQ [])
      (if cto = true ∧ ¬r2 = true ∧ valid = true then do
        let sc ← getSchedContext (Z := Unit) σ.curSc
        handleTimeout σ.curThread (.timeout sc.scBadge)
      else do
        let ready ← getScRefillReady σ.curSc
        let sufficient ← getScRefillSufficient σ.curSc 0
        if ready = true ∧ sufficient = true
        then tcbSchedAction tcbSchedAppend σ.curThread
        else postpone σ.curSc) := by
    intro valid
    split
    · refine hk_bind (hk_of_ik (by nq2_auto)) fun sc => ?_
      exact hk_post (nq_handleTimeout _ _ hc) nq_weak_nil
    · exact hk_post (hk_of_ik (by nq2_auto)) nq_weak_nil
  (try dsimp only)
  by_cases hv : x.tcbState = .runningVM
  · rw [if_pos hv]; exact hk_bind (hk_of_ik (ik_pure _)) fun v => htail v
  · rw [if_neg hv]; exact hk_bind (hk_of_ik (by nq2_auto)) fun v => htail v

theorem nq_chargeBudget (n : Ticks) (cto : Bool) : HK (NQ K) (NQ []) (chargeBudget (Z := Unit) n cto) := by
  intro σ hσ y hy
  unfold chargeBudget at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [mem_gets h2] at hy
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : NQ K y3.2 := (?_ : NQK K _) _ hσ y3 h3
  · obtain ⟨y4, h4, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 h4] at hy
    have hb4 : NQ K { y3.2 with consumedTime := 0 } := hb3
    obtain ⟨y5, h5, hy⟩ := hy
    rw [mem_gets h5] at hy
    obtain ⟨y6, h6, hy⟩ := hy
    rw [mem_gets h6] at hy
    (try dsimp only at hy)
    unfold NonDet.when at hy
    split at hy
    · rename_i hs
      have hrun := sched_runnable hs
      obtain ⟨y7, h7, hy⟩ := hy
      have hb7 := nq_endTimeslice_p (K := K) cto _ hrun hb4 y7 h7
      refine (?_ : NQK [] _) _ hb7 y hy
      nq_auto
    · rw [Set.mem_singleton_iff.1 hy]; exact nq_weak_nil _ hb4
  · nq_auto
macro_rules | `(tactic| nqh_leaf) => `(tactic| (exact hk_post (nq_chargeBudget _ _) nq_weak_nil))
macro_rules | `(tactic| nqh_leaf) => `(tactic| (refine hk_bind (nq_chargeBudget _ _) fun _ => ?_))

theorem nq_checkBudget : HK (NQ K) (NQ []) (checkBudget (Z := Unit)) := by
  unfold checkBudget
  refine hk_bind (hk_of_ik (by nq2_auto)) fun csc => ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun consumed => ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun suff => ?_
  split
  · exact hk_post (hk_of_ik (by nq2_auto)) nq_weak_nil
  · refine hk_bind (hk_of_ik (by nq2_auto)) fun c => ?_
    exact hk_bind (nq_chargeBudget _ _) fun _ => hk_of_ik (ik_pure _)
macro_rules | `(tactic| nqh_leaf) => `(tactic| (exact hk_post nq_checkBudget nq_weak_nil))
macro_rules | `(tactic| nqh_leaf) => `(tactic| (refine hk_bind nq_checkBudget fun _ => ?_))

/-- `check_budget_restart`: the current thread is read; it is written only when runnable (so in no queue). -/
theorem nq_checkBudgetRestart : HK (NQ K) (NQ []) (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart
  refine hk_bind nq_checkBudget fun r => ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun cur => ?_
  unfold getThreadState
  refine hk_threadGet_bind fun σ x hx => ?_
  by_cases hr : runnable x.tcbState = true
  · refine hkp_nqcons (fun _ y hy => by
      rw [hx] at hy; cases hy; revert hr; cases x.tcbState <;> simp [runnable, isBoN, epBlocked]) ?_
    exact hk_post (hk_of_ik (by nq2_auto)) nq_weak_nil
  · unfold NonDet.when
    rw [if_neg (by simp [hr])]
    exact hkp_of_hk (hk_of_ik (by nq2_auto)) σ

theorem nq_preemptionPath : HK (NQ K) (NQ []) (preemptionPath (Z := Unit)) := by
  unfold preemptionPath
  have htail : HK (NQ []) (NQ []) (maybeHandleInterrupt (Z := Unit) true) := hk_of_ik (by nq2_auto)
  refine hk_bind (hk_of_ik (by nq2_auto)) fun ct => ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun sched => ?_
  cases sched
  · refine hk_bind (hk_of_ik (by nq2_auto)) fun csc => ?_
    refine hk_bind (hk_of_ik (by nq2_auto)) fun active => ?_
    cases active
    · exact hk_post (hk_of_ik (by nq2_auto)) nq_weak_nil
    · refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
      refine hk_bind (nq_chargeBudget _ _) fun _ => ?_
      first | exact htail | exact hk_pure_bind htail
  · refine hk_bind nq_checkBudget fun _ => ?_
    first | exact htail | exact hk_pure_bind htail

theorem nq_handleYield : HK (NQ K) (NQ []) (handleYield (Z := Unit)) := by
  unfold handleYield
  refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
  exact hk_bind (nq_chargeBudget _ _) fun _ => hk_of_ik (by nq2_auto)

/-! ## Deletion and creation of objects -/

theorem queued_of_kheap {σ σ' : State Unit} (e : σ'.kheap = σ.kheap) {t : ObjRef} (h : queued σ' t) :
    queued σ t := by
  obtain ⟨n, x, hn, hq⟩ := h
  exact ⟨n, x, by rw [← e]; exact hn, hq⟩

theorem not_queued_of_none {σ : State Unit} (h : NtfnQB σ) {q : ObjRef} (hq : σ.kheap q = none) :
    ¬ queued σ q := fun h' => by
  obtain ⟨y, hy, _⟩ := h.tcb h'
  rw [hq] at hy; cases hy

theorem not_queuedE_of_none {σ : State Unit} (h : EpQB σ) {q : ObjRef} (hq : σ.kheap q = none) :
    ¬ queuedE σ q := fun ⟨e, x, he, ht⟩ => by
  obtain ⟨y, hy, _⟩ := h e x q he ht
  rw [hq] at hy; cases hy

/-- `t` is in a notification queue or an endpoint queue. -/
def qd (σ : State Unit) (t : ObjRef) : Prop := queued σ t ∨ queuedE σ t

/-- A detype of a set holding no queued thread. -/
theorem nq_detype {σ : State Unit} (D : Set ObjRef) (h : NQ K σ) (hD : ∀ t, qd σ t → t ∉ D) :
    NQ K (detype D σ) := by
  have hk : ∀ x, (detype D σ).kheap x = if x ∈ D then none else σ.kheap x := fun _ => rfl
  have hsub : ∀ u, queued (detype D σ) u → queued σ u := by
    rintro u ⟨n, x, hn, hq⟩
    rw [hk] at hn
    split_ifs at hn
    exact ⟨n, x, hn, hq⟩
  have hsubE : ∀ u, queuedE (detype D σ) u → queuedE σ u := by
    rintro u ⟨n, x, hn, hq⟩
    rw [hk] at hn
    split_ifs at hn
    exact ⟨n, x, hn, hq⟩
  refine ⟨⟨fun n x t hn ht => ?_, fun n x t hn ht => ?_⟩, fun u hu =>
    ⟨fun hq => (h.2 u hu).1 (hsub u hq), fun y hy => ?_, fun hq => (h.2 u hu).2.2 (hsubE u hq)⟩⟩
  · rw [hk] at hn
    split_ifs at hn with hnD
    obtain ⟨y, hy, hs⟩ := h.1.1 n x t hn ht
    refine ⟨y, ?_, hs⟩
    rw [hk, if_neg (hD t (Or.inl ⟨n, x, hn, ht⟩))]; exact hy
  · rw [hk] at hn
    split_ifs at hn with hnD
    obtain ⟨y, hy, hs⟩ := h.1.2 n x t hn ht
    refine ⟨y, ?_, hs⟩
    rw [hk, if_neg (hD t (Or.inr ⟨n, x, hn, ht⟩))]; exact hy
  · rw [hk] at hy
    split_ifs at hy
    exact (h.2 u hu).2.1 y hy

theorem qd_of_kheap {σ σ' : State Unit} (e : σ'.kheap = σ.kheap) {t : ObjRef} (h : qd σ' t) : qd σ t := by
  rcases h with ⟨n, x, hn, hq⟩ | ⟨n, x, hn, hq⟩
  · exact Or.inl ⟨n, x, by rw [← e]; exact hn, hq⟩
  · exact Or.inr ⟨n, x, by rw [← e]; exact hn, hq⟩

/-- `delete_objects`: the state is a detype of the region (after a machine operation). -/
theorem deleteObjects_out {ptr : Word} {bits : Nat} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (deleteObjects (Z := Unit) ptr bits σ).1) :
    ∃ s1 : State Unit, s1.kheap = σ.kheap ∧ y.2 = detype (SInvU.delR ptr bits) s1 := by
  unfold deleteObjects at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hk1 : y1.2.kheap = σ.kheap :=
    (ik_doMachineOp (P := fun s => s.kheap = σ.kheap) (fun _ _ h => h) _) σ rfl y1 h1
  exact ⟨y1.2, hk1, by rw [Set.mem_singleton_iff.1 hy]; rfl⟩

/-- `delete_objects` of a region holding no queued thread. -/
theorem nq_deleteObjects_p (ptr : Word) (bits : Nat) (σ : State Unit)
    (hD : ∀ t, qd σ t → t ∉ SInvU.delR ptr bits) : IKp (NQ K) σ (deleteObjects (Z := Unit) ptr bits) := by
  intro hσ y hy
  unfold deleteObjects at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hk1 : y1.2.kheap = σ.kheap :=
    (ik_doMachineOp (P := fun s => s.kheap = σ.kheap) (fun _ _ h => h) _) σ rfl y1 h1
  have hb1 : NQ K y1.2 := nq_doMachineOp _ σ hσ y1 h1
  rw [Set.mem_singleton_iff.1 hy]
  exact nq_detype _ hb1 fun t ht => hD t (qd_of_kheap hk1 ht)

theorem dflt_ok {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (o : Nat) (d : Domain) :
    (∀ x, defaultObject ty dev o d = .notification x → x.ntfnObj.ntfnQueue = []) ∧
    (∀ y, defaultObject ty dev o d = .tcb y → ¬ isBoN y.tcbState) ∧
    (∀ x, defaultObject ty dev o d = .endpoint x → x.epQueue = []) := by
  cases ty with
  | untyped => exact absurd rfl hty
  | tcbObject => exact ⟨fun x h => (by cases h), fun y h => (by cases h; exact fun h => h), fun x h => (by cases h)⟩
  | notificationObject => exact ⟨fun x h => (by cases h; rfl), fun y h => (by cases h), fun x h => (by cases h)⟩
  | endpointObject => exact ⟨fun x h => (by cases h), fun y h => (by cases h), fun x h => (by cases h; rfl)⟩
  | _ => exact ⟨fun x h => (by cases h), fun y h => (by cases h), fun x h => (by cases h)⟩

/-- Default objects at addresses no queued thread occupies. -/
theorem nq_retype_kh {σ : State Unit} (ps : List ObjRef) (dO : KernelObject) (h : NQ K σ)
    (hF : ∀ q ∈ ps, ¬ qd σ q)
    (hd : (∀ x, dO = .notification x → x.ntfnObj.ntfnQueue = []) ∧ (∀ y, dO = .tcb y → ¬ isBoN y.tcbState) ∧
      (∀ x, dO = .endpoint x → x.epQueue = [])) :
    NQ K { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } := by
  have hk : ∀ q, ({ σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } :
      State Unit).kheap q = if q ∈ ps then some dO else σ.kheap q := fun q => SInvU.foldr_upd ps dO σ.kheap q
  have hsub : ∀ u, queued { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } u →
      queued σ u := by
    rintro u ⟨n, x, hn, hq⟩
    rw [hk] at hn
    split_ifs at hn
    · cases hn; rw [hd.1 x rfl] at hq; cases hq
    · exact ⟨n, x, hn, hq⟩
  have hsubE : ∀ u, queuedE { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } u →
      queuedE σ u := by
    rintro u ⟨n, x, hn, hq⟩
    rw [hk] at hn
    split_ifs at hn
    · cases hn; rw [hd.2.2 x rfl] at hq; cases hq
    · exact ⟨n, x, hn, hq⟩
  refine ⟨⟨fun n x t hn ht => ?_, fun n x t hn ht => ?_⟩, fun u hu =>
    ⟨fun hq => (h.2 u hu).1 (hsub u hq), fun y hy => ?_, fun hq => (h.2 u hu).2.2 (hsubE u hq)⟩⟩
  · rw [hk] at hn
    split_ifs at hn
    · cases hn; rw [hd.1 x rfl] at ht; cases ht
    · obtain ⟨y, hy, hs⟩ := h.1.1 n x t hn ht
      refine ⟨y, ?_, hs⟩
      rw [hk, if_neg (fun hm => hF t hm (Or.inl ⟨n, x, hn, ht⟩))]; exact hy
  · rw [hk] at hn
    split_ifs at hn
    · cases hn; rw [hd.2.2 x rfl] at ht; cases ht
    · obtain ⟨y, hy, hs⟩ := h.1.2 n x t hn ht
      refine ⟨y, ?_, hs⟩
      rw [hk, if_neg (fun hm => hF t hm (Or.inr ⟨n, x, hn, ht⟩))]; exact hy
  · rw [hk] at hy
    split_ifs at hy
    · cases hy; exact hd.2.1 y rfl
    · exact (h.2 u hu).2.1 y hy

/-- `retype_region` at addresses no queued thread occupies. -/
theorem nq_retypeRegionWith_p (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n o : Nat) (ty : ApiObjectType)
    (dev : Bool) (σ : State Unit) (hF : ∀ q ∈ SInvU.retPtrs ptr n (bA ty o), ¬ qd σ q) :
    IKp (NQ K) σ (retypeRegionWith (Z := Unit) bA ptr n o ty dev) := by
  intro hσ y hy
  unfold retypeRegionWith at hy
  obtain ⟨z1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨z2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  show NQ K z3.2
  unfold NonDet.when at h3
  split at h3
  · rename_i hty
    obtain ⟨w1, hw1, h3⟩ := h3
    rw [mem_gets hw1] at h3
    obtain ⟨w2, hw2, h3⟩ := h3
    rw [mem_gets hw2] at h3
    obtain ⟨w3, hw3, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 hw3] at h3
    rw [Set.mem_singleton_iff.1 h3]
    exact nq_retype_kh _ _ hσ hF (dflt_ok hty dev o _)
  · rw [Set.mem_singleton_iff.1 h3]; exact hσ

/-! ## Untyped and MakePool performs -/

/-- IPC-blocked: BlockedOnNotification, BlockedOnSend or BlockedOnReceive
(by NtfnQB / EpQB, every queued thread is). -/
def ipcBlk (s : ThreadState) : Prop := isBoN s ∨ epBlocked s ≠ none

theorem qd_blk {σ : State Unit} (hN : NtfnQB σ ∧ EpQB σ) {t : ObjRef} (h : qd σ t) :
    ∃ y, σ.kheap t = some (.tcb y) ∧ ipcBlk y.tcbState := by
  rcases h with ⟨n, x, hn, hq⟩ | ⟨e, x, he, hq⟩
  · obtain ⟨y, hy, hs⟩ := hN.1 n x t hn hq
    exact ⟨y, hy, Or.inl (by rw [hs]; trivial)⟩
  · obtain ⟨y, hy, hs⟩ := hN.2 e x t he hq
    exact ⟨y, hy, Or.inr (by rw [hs]; simp)⟩

/-- **[J] NqDet** (l4v `if_live_then_nonz_cap` + `untyped_children_in_mdb`: an
IPC-blocked thread is live (`live (TCB t)` holds for every state but Inactive
/ IdleThreadState), so some cap refers to it, and such a cap is a CDT
descendant of every untyped cap whose region holds the thread; a childless
untyped therefore holds none): the region of a childless untyped cap holds no
IPC-blocked TCB. Read by the reset's and MakePool's detype only (through
`nqDet_qd`: no queued thread there). -/
def NqDet (σ : State Unit) : Prop :=
  ∀ u dev b n fi, SInvU.capAt σ u = some (.untypedCap dev b n fi) → (∀ c, σ.cdt c ≠ some u) →
    ∀ t ∈ SInvU.delR b n, ∀ y, σ.kheap t = some (.tcb y) → ¬ ipcBlk y.tcbState

theorem nqDet_qd {σ : State Unit} (hN : NtfnQB σ ∧ EpQB σ) (hD : NqDet σ) {u : CslotPtr} {dev : Bool}
    {b : ObjRef} {n fi : Nat} (hc : SInvU.capAt σ u = some (.untypedCap dev b n fi))
    (hk : ∀ c, σ.cdt c ≠ some u) : ∀ t, qd σ t → t ∉ SInvU.delR b n := by
  intro t ht hm
  obtain ⟨y, hy, hb⟩ := qd_blk hN ht
  exact hD u dev b n fi hc hk t hm y hy hb

/-- **[J] IfLiveB** (l4v `if_live_then_nonz_cap`, at the IPC-blocked TCBs
inside an untyped's region: such a TCB is live (`live (TCB t)` for a state
other than Inactive / IdleThreadState), so some cap refers to it). -/
def IfLiveB (σ : State Unit) : Prop :=
  ∀ t y, σ.kheap t = some (.tcb y) → ipcBlk y.tcbState → SInvU.InUtV (SInvU.uV σ) t →
    ∃ s c, SInvU.capAt σ s = some c ∧ t ∈ objRefs c

/-- **`NqDet` from ut4's `UtInv''`** (its UtCh: a cap naming an object inside
an untyped's region is a CDT descendant of that untyped, so the untyped has a
child) and `IfLiveB`. -/
theorem nqDet_of_live {σ : State Unit} (hU : SInvU.UtInv'' σ) (hL : IfLiveB σ) : NqDet σ := by
  intro u dev b n fi hc hk t ht y hy hb
  obtain ⟨s, c, hs, hr⟩ := hL t y hy hb ⟨u, dev, b, n, fi, hc, ht⟩
  exact SInvU.desc_noKids hk (hU.2.1 u dev b n fi hc s c t hs (SInvU.objRefs_sub_capRng c hr) ht)

/-- `reset_untyped_cap` of a slot whose untyped region holds no queued thread. -/
theorem nq_resetUntypedCap (s : CslotPtr) {σ : State Unit} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ s = some (.untypedCap dev b n fi)) (hD : ∀ t, qd σ t → t ∉ SInvU.delR b n) :
    IKp (NQ K) σ (ExceptT.run (resetUntypedCap (Z := Unit) s)) := by
  intro hσ y hy
  unfold resetUntypedCap at hy
  obtain ⟨x, hx, hy⟩ := SInvU.run_liftE_bind_mem hy
  obtain ⟨cap, s'⟩ := x
  obtain ⟨hs, hcx⟩ := SInvU.getCap_capAt hx
  simp only at hs hcx; rw [hs] at hy
  rw [hc] at hcx; cases hcx
  replace hy := SInvU.run_returnOk_bind_mem hy
  replace hy := SInvU.run_returnOk_bind_mem hy
  dsimp only at hy
  by_cases h0 : fi = 0
  · rw [if_pos (show freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact hσ
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := SInvU.run_liftE_bind_mem hy
    simp only [bitsOf, objRefOf] at hz
    have hz0 : NQ K z.2 := nq_deleteObjects_p b n σ hD hσ z hz
    refine (?_ : NQKE K _) z.2 hz0 y hy
    try dsimp only
    nq_auto

/-- The untyped retype's body after the reset, from a state where the retype addresses hold no object. -/
theorem nq_utBody (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat) (slots : List CslotPtr)
    (dev : Bool) (σ : State Unit) (hfr : ∀ q ∈ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none) :
    IKp (NQ K) σ (do
      let cap ← getCap (Z := Unit) s
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (bitsOf cap) (unat (freeRef - base))) s
      let orefs ← retypeRegionWith fl4ObjBitsApi rb slots.length sz ty dev
      initArchObjects ty dev rb slots.length sz orefs
      NonDet.mapMx (createCap ty sz s dev) (slots.zip orefs)) := by
  intro hσ x hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1; subst s1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  have hb4 : NQ K x4.2 := nq_setCap _ _ _ hσ x4 hx4
  have hk4 := (SInvU.setCap_out hx4).1
  obtain ⟨x5, hx5, hx⟩ := hx
  have hb5 := nq_retypeRegionWith_p (K := K) fl4ObjBitsApi rb slots.length sz ty dev x4.2
    (fun q hq => by
      have hn : x4.2.kheap q = none := by have := hk4 q; rw [hfr q hq] at this; simpa using this
      rintro (h | h)
      · exact not_queued_of_none hb4.1.1 hn h
      · exact not_queuedE_of_none hb4.1.2 hn h) hb4 x5 hx5
  refine (?_ : NQK K _) x5.2 hb5 _ hx
  nq_auto

/-- **`invoke_untyped`** from the decode's facts (`UtRetOK`, ut1) with `UtInv`
and, for a reset, `NqDet`. -/
theorem nq_invokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hI : SInvU.UtInv σ)
    (hok : SInvU.UtRetOK σ ui) (hD : NqDet σ) :
    IKp (NQ K) σ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui)) := by
  intro hσ y hy
  cases ui with
  | retype s reset base rb ty sz slots dev =>
    cases reset
    · have hfr := SInvU.utRet_fresh hI hok
      simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
      replace hy := SInvU.run_returnOk_bind_mem hy
      obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
      exact nq_utBody s base rb ty sz slots dev σ hfr hσ x hx
    · have hok' := hok
      obtain ⟨bits, fi, hc, -, -, -, -, hr⟩ := hok'
      simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
      rw [ExceptT.run_bind] at hy
      obtain ⟨z, hz, hy⟩ := hy
      have hbz := nq_resetUntypedCap (K := K) s hc (nqDet_qd hσ.1 hD hc (hr rfl)) hσ z hz
      have hfz := SInvU.utRet_fresh_after_reset hI hok z hz
      obtain ⟨r, s1⟩ := z
      cases r with
      | error e =>
        first
          | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
          | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
      | ok u =>
        try dsimp only at hy
        obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
        exact nq_utBody s base rb ty sz slots dev s1 hfz hbz x hx

/-- MakePool's facts: the frame region holds no queued thread, and it contains the frame. -/
def NqMp (σ : State Unit) (frame : ObjRef) : Prop :=
  (∀ t, qd σ t → t ∉ SInvU.delR frame page_bits) ∧ frame ∈ SInvU.delR frame page_bits

/-- MakePool (`perform_asid_control_invocation`). -/
theorem nq_makePool (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit) (hP : NqMp σ frame) :
    IKp (NQ K) σ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base)) := by
  intro hσ y hy
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 := nq_deleteObjects_p (K := K) frame page_bits σ hP.1 hσ y1 h1
  have hn1 : y1.2.kheap frame = none := by
    obtain ⟨s1, -, e1⟩ := deleteObjects_out h1
    rw [e1]; show (if frame ∈ SInvU.delR frame page_bits then none else s1.kheap frame) = none
    rw [if_pos hP.2]
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt h2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : NQ K y3.2 := nq_setCap _ _ _ hb1 y3 h3
  have hn3 : y3.2.kheap frame = none := by
    have := (SInvU.setCap_out h3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, h4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at h4
  have hb4 := nq_retypeRegionWith_p (K := K) objBitsApi frame 1 0 _ false y3.2 (fun q hq => by
    simp only [SInvU.retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    have hq' : q = frame := by rw [hq]; simp [ptrAdd]
    subst hq'
    rintro (h | h)
    · exact not_queued_of_none hb3.1.1 hn3 h
    · exact not_queuedE_of_none hb3.1.2 hn3 h) hb3 y4 h4
  refine (?_ : NQK K _) y4.2 hb4 y hy
  nq_auto

/-! ## `perform_invocation` -/

/-- **The decode's facts the untyped and MakePool performs need** (the
`NqDecW` [W] of the shell): an untyped retype passed the decode's checks
(`SInvU.UtRetOK`), a MakePool's parent slot holds a childless untyped cap of
page size at the frame. -/
def NqDec (σ : State Unit) (i : Fl4Invocation) : Prop :=
  (∀ ui, i = .invokeUntyped ui → SInvU.UtRetOK σ ui) ∧
  (∀ frame slot parent base, i = .invokeArchObject (.spec (.invokeASIDControl (.makePool frame slot parent base))) →
    ∃ dev fi, SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi) ∧ ∀ c, σ.cdt c ≠ some parent)

theorem nqDec_view {σ σ' : State Unit} (h : SInvU.uV σ' = SInvU.uV σ) {i : Fl4Invocation} (hd : NqDec σ i) :
    NqDec σ' i := by
  have hcap : SInvU.capAt σ' = SInvU.capAt σ := congrArg (fun w : SInvU.UView => w.2.1) h
  have hcdt : σ'.cdt = σ.cdt := congrArg (fun w : SInvU.UView => w.2.2.1) h
  refine ⟨fun ui e => SInvU.utRetOK_view h (hd.1 ui e), fun fr sl pa ba e => ?_⟩
  obtain ⟨dev, fi, hc, hk⟩ := hd.2 fr sl pa ba e
  exact ⟨dev, fi, by rw [hcap]; exact hc, by rw [hcdt]; exact hk⟩

/-- MakePool's facts from the decode's: the parent untyped's region holds no queued thread (`NqDet`), and it contains the frame (UtWf). -/
theorem nqMp_of {σ : State Unit} (hN : NtfnQB σ ∧ EpQB σ) (hI : SInvU.UtInv σ) (hD : NqDet σ) {parent : CslotPtr} {dev : Bool}
    {frame : ObjRef} {fi : Nat} (hc : SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi))
    (hk : ∀ c, σ.cdt c ≠ some parent) : NqMp σ frame := by
  refine ⟨nqDet_qd hN hD hc hk, ?_⟩
  obtain ⟨hn, hfit⟩ := SInvU.UtWf.fit (σ := σ) hI.2.1 hc
  exact (SInvU.mem_delR_iff hn hfit _).2 ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩

/-! ## `invoke_tcb` keeping `K` when its threads are in an `okSt` state -/

/-- `set_priority` keeps `K` when its target, if in `K`, is not blocked on an endpoint. -/
theorem nq_setPriority_K (t : ObjRef) (prio : Priority) :
    HK (fun s => NQ K s ∧ (t ∈ K → ∀ x, s.kheap t = some (.tcb x) → epBlocked x.tcbState = none)) (NQ K)
      (setPriority (Z := Unit) t prio) := by
  intro σ ⟨hσ, he⟩ y hy
  by_cases ht : t ∈ K
  · revert y hy
    refine (?_ : HK (fun s => s = σ) (NQ K) (setPriority (Z := Unit) t prio)) σ rfl
    unfold setPriority getThreadState
    refine hk_threadGet_bind fun σ' x hx => ?_
    intro e
    subst e
    cases hs : x.tcbState
    case blockedOnNotification n => exact absurd (by rw [hs]; trivial) ((hσ.2 t ht).2.1 x hx)
    case blockedOnSend e d => exact absurd (he ht x hx) (by rw [hs]; simp [epBlocked])
    case blockedOnReceive e r d => exact absurd (he ht x hx) (by rw [hs]; simp [epBlocked])
    all_goals
      simp only [runnable, epBlocked, ntfnBlocked, NonDet.maybeM, Bool.false_eq_true, ↓reduceIte]
      exact fun y hy => ikp_of_ik (by nq_auto) σ' hσ y hy
  · refine nq_mono (nq_setPriority t prio σ hσ y hy) fun u hu => ?_
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hu, fun e => ht (e ▸ hu)⟩

theorem ik_nqpj {α : Type} {m : NonDet (State Unit) α} (h1 : NQK K m) (h2 : PJK K m) :
    IK (fun s => NQ K s ∧ PJ K s) m :=
  ik_and h1 h2

/-- `invoke_tcb` keeps `K` when the threads of `K` are in an `okSt` state (the
current thread, Restart during `perform_invocation`). -/
theorem nq_invokeTcbK (a0 : TcbInvocation) :
    HKE (fun s => NQ K s ∧ PJ K s) (NQ K) (invokeTcb (Z := Unit) a0) := by
  cases a0
  case threadControlSched target slot fh mcp prio sc =>
    cases prio with
    | none =>
      refine fun σ hσ y hy =>
        (?_ : NQKE K (invokeTcb (Z := Unit) (.threadControlSched target slot fh mcp none sc))) σ hσ.1 y hy
      simp only [invokeTcb, NonDet.maybeM]
      nq2_auto
    | some p =>
      obtain ⟨p1, p2⟩ := p
      simp only [invokeTcb, NonDet.maybeM]
      refine hke_bind (hk_of_ik (ik_nqpj (by nq2_auto) (by pj_auto))) (fun _ => ?_) (fun _ h => h.1)
      refine hke_bind (hk_of_ik (ik_nqpj (by nq2_auto) (by pj_auto))) (fun _ => ?_) (fun _ h => h.1)
      refine hke_bind (R := NQ K) (hk_liftE (hk_pre (nq_setPriority_K target p1) fun s h =>
        ⟨h.1, fun ht x hx => pj_epB h.2 ht hx⟩)) (fun _ => hk_of_ik (by nq2_auto)) (fun _ h => h)
  case writeRegisters => exact fun σ hσ y hy => nq_invokeTcb_wr _ _ _ _ σ hσ.1 y hy
  case readRegisters => exact fun σ hσ y hy => nq_invokeTcb_rd _ _ _ _ σ hσ.1 y hy
  case copyRegisters => exact fun σ hσ y hy => nq_invokeTcb_copy _ _ _ _ _ _ _ σ hσ.1 y hy
  case threadControlCaps => exact fun σ hσ y hy => nq_invokeTcb_caps _ _ _ _ _ _ _ σ hσ.1 y hy
  case suspend => exact fun σ hσ y hy => nq_invokeTcb_suspend _ σ hσ.1 y hy
  case resume => exact fun σ hσ y hy => nq_invokeTcb_resume _ σ hσ.1 y hy
  case notificationControl => exact fun σ hσ y hy => nq_invokeTcb_ntfn _ _ σ hσ.1 y hy
  case setTLSBase => exact fun σ hσ y hy => nq_invokeTcb_tls _ _ σ hσ.1 y hy
  case setFlags => exact fun σ hσ y hy => nq_invokeTcb_flags _ _ _ σ hσ.1 y hy

theorem nqP_of {bl : Bool} {s : State Unit} (h : NQ K s) : NQ [] s ∧ (bl = false → NQ K s) :=
  ⟨nq_weak_nil _ h, fun _ => h⟩

set_option maxHeartbeats 4000000 in
/-- `perform_invocation`: the post keeps `K` unless the invocation blocks (a
blocking send may queue the sender); otherwise it forgets `K`. A reply's
receiver and a TCB invocation's target cannot be a thread of `K`, whose state
is `okSt` (`PJ K`: the current thread is Restart). -/
theorem nq_fl4PerformInvocation (bl call don : Bool) (i : Fl4Invocation) :
    HKE (fun σ => NQ K σ ∧ σ.curThread ∈ K ∧ PJ K σ ∧ NqDec σ i ∧ SInvU.UtInv σ ∧ NqDet σ)
      (fun s => NQ [] s ∧ (bl = false → NQ K s)) (fl4PerformInvocation (Z := Unit) bl call don i) := by
  cases i
  case invokeUntyped ui =>
    intro σ hσ y hy
    simp only [fl4PerformInvocation] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hbz := nq_invokeUntyped (K := K) ui σ hσ.2.2.2.2.1 (hσ.2.2.2.1.1 ui rfl) hσ.2.2.2.2.2 hσ.1 z hz
    obtain ⟨r, s1⟩ := z
    cases r with
    | error e =>
      first
        | (obtain rfl := Set.mem_singleton_iff.1 hy; exact nqP_of hbz)
        | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact nqP_of hbz)
    | ok u =>
      try dsimp only at hy
      obtain rfl := Set.mem_singleton_iff.1 hy; exact nqP_of hbz
  case invokeEndpoint ep bd g gr =>
    simp only [fl4PerformInvocation, withoutPreemption]
    refine hk_liftE ?_
    intro σ hσ y ⟨y1, h1, hy⟩
    rw [mem_gets h1] at hy
    obtain ⟨y2, h2, hy⟩ := hy
    have hb2 := nq_sendIpc bl call bd g gr don σ.curThread ep hσ.2.1 σ hσ.1 y2 h2
    rw [Set.mem_singleton_iff.1 hy]
    refine ⟨nq_weak_nil _ hb2, fun hb => ?_⟩
    subst hb
    exact nq_sendIpc_nb call bd g gr don σ.curThread ep hσ.2.1 σ hσ.1 y2 h2
  case invokeTCB ti =>
    simp only [fl4PerformInvocation]
    exact fun σ hσ y hy => nqP_of (nq_invokeTcbK ti σ ⟨hσ.1, hσ.2.2.1⟩ y hy)
  case invokeReply rp gr =>
    simp only [fl4PerformInvocation]
    refine hk_liftE ?_
    intro σ hσ y ⟨y1, h1, hy⟩
    rw [mem_gets h1] at hy
    obtain ⟨y2, h2, hy⟩ := hy
    have hb2 := nq_doReplyTransfer (Kq := K) K (fun _ h => h) σ.curThread rp gr σ ⟨hσ.1, pj_noRpl hσ.2.2.1⟩ y2 h2
    rw [Set.mem_singleton_iff.1 hy]; exact nqP_of hb2
  case invokeArchObject a =>
    cases a
    case spec a =>
      cases a
      case invokeASIDControl oper =>
        cases oper with
        | makePool frame slot parent base =>
          intro σ hσ y hy
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation] at hy
          obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
          obtain ⟨x1, hx1, hx⟩ := hx
          obtain ⟨dev, fi, hc, hk⟩ := hσ.2.2.2.1.2 frame slot parent base rfl
          have hb1 := nq_makePool (K := K) frame slot parent base σ
            (nqMp_of hσ.1.1 hσ.2.2.2.2.1 hσ.2.2.2.2.2 hc hk) hσ.1 x1 hx1
          rw [Set.mem_singleton_iff.1 hx]; exact nqP_of hb1
      all_goals
        refine fun σ hσ y hy => nqP_of ((?_ : NQKE K _) σ hσ.1 y hy)
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
        nq_auto
    all_goals
      refine fun σ hσ y hy => nqP_of ((?_ : NQKE K _) σ hσ.1 y hy)
      simp only [fl4PerformInvocation, fl4ArchPerformInvocation]
      nq_auto
  all_goals
    refine fun σ hσ y hy => nqP_of ((?_ : NQKE K _) σ hσ.1 y hy)
    simp only [fl4PerformInvocation, withoutPreemption]
    nq2_auto

end

end Fl4Proofs.P3.SInv
