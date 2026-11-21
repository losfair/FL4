/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ctq2): **T1 by hand:
`tcb_sched_dequeue` empties every queue of the thread, `set_domain`,
`set_priority`** (spec side only, outside the JAtZ cone; SpecInvCqK for T1
and the leaves, SpecInvCqF1..F5 for the generated family).

* `q1_dequeue_hk`: from T1, after `tcb_sched_action tcb_sched_dequeue t` the
  thread is in no ready queue (T1 puts it only in its own queue `(domain,
  priority)`, which the filter clears), so a following `thread_set` may change
  its domain or priority (`q1_threadSet_nq`).
* `q1_setDomain`, `q1_invokeSetDomain`, `q1_invokeDomain`: no premise.
* `q1_setPriority_p`: the runnable branches need nothing (dequeue first, or
  the thread is in no queue because it is not in its own); the non-runnable
  branch writes the priority without a dequeue, so it needs the thread in no
  queue: `hR` at the call's state, l4v `valid_ready_qs`' runnable half
  ("queued ⇒ runnable", not carried; KENTRY-PLAN ctq2).
-/
import Fl4Proofs.P3.SpecInvCqF5
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- Pre/post form of `IK`. -/
def HK1 (P Q : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ x, x ∈ (m σ).1 → Q x.2

theorem hk1_bind {P R Q : State Unit → Prop} {α γ : Type} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) γ} (hm : HK1 P R m) (hg : ∀ a, HK1 R Q (g a)) : HK1 P Q (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  exact hg y.1 y.2 (hm σ hσ y hy) x hx

theorem hk1_of_ik {α : Type} {m : NonDet (State Unit) α} (h : Q1K m) : HK1 T1 T1 m :=
  fun σ hσ x hx => h σ hσ x hx

/-- T1 and `t` in no ready queue. -/
abbrev NQ1 (t : ObjRef) (σ : State Unit) : Prop := T1 σ ∧ ∀ d p, t ∉ σ.readyQueues d p

/-- The outcome of `tcb_sched_action`. -/
theorem q1_tsa_out {act : ObjRef → List ObjRef → List ObjRef} {t : ObjRef} {σ : State Unit}
    {y : Unit × State Unit} (hy : y ∈ (tcbSchedAction (Z := Unit) act t σ).1) :
    ∃ x, σ.kheap t = some (.tcb x) ∧ y.2 = { σ with readyQueues := (fun d1 p1 =>
      if d1 = x.tcbDomain ∧ p1 = x.tcbPriority then act t (σ.readyQueues x.tcbDomain x.tcbPriority)
      else σ.readyQueues d1 p1) } := by
  unfold tcbSchedAction getTcbQueue setTcbQueue at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x', hx', rfl⟩ := q1_mem_threadGet hz
  rw [hx] at hx'; cases hx'
  obtain ⟨z, ⟨w, hw, hz⟩, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hw
  obtain rfl := Set.mem_singleton_iff.1 hz
  obtain ⟨w, hw, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hw
  obtain rfl := Set.mem_singleton_iff.1 hy
  exact ⟨x, hx, rfl⟩

/-- **After a dequeue the thread is in no ready queue.** -/
theorem q1_dequeue_hk (t : ObjRef) : HK1 T1 (NQ1 t) (tcbSchedAction (Z := Unit) tcbSchedDequeue t) := by
  intro σ hσ y hy
  refine ⟨q1_tcbSchedAction _ t (q1_deq t) σ hσ y hy, fun d p ht => ?_⟩
  obtain ⟨x, hx, e⟩ := q1_tsa_out hy
  rw [e] at ht
  dsimp only at ht
  split at ht
  · unfold tcbSchedDequeue at ht
    have h2 := (List.mem_filter.1 ht).2
    simp at h2
  · rename_i hne
    obtain ⟨x', hx', h1, h2⟩ := hσ d p t ht
    rw [hx] at hx'; cases hx'
    exact hne ⟨h1.symm, h2.symm⟩

/-- `setObject` at a pointer in no ready queue. -/
theorem q1_setObject_nq (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (hq : ∀ d pr, p ∉ σ.readyQueues d pr) : IKp T1 σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact q1_update hσ p o fun d pr hp => (hq d pr hp).elim

/-- **Any `thread_set` of a thread in no ready queue.** -/
theorem q1_threadSet_nq (f : Tcb → Tcb) (t : ObjRef) : HK1 (NQ1 t) T1 (threadSet (Z := Unit) f t) := by
  unfold threadSet
  intro σ hσ y ⟨z, hz, hy⟩
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    exact q1_setObject_nq _ _ σ hσ.2 hσ.1 y hy

/-! ## `set_domain` -/

/-- **`set_domain` keeps T1** (dequeue, write, enqueue in the new queue). -/
theorem q1_setDomain (t : ObjRef) (dom : Domain) : Q1K (setDomain (Z := Unit) t dom) := by
  unfold setDomain threadSetDomain
  refine hk1_bind (hk1_of_ik (ik_gets _)) fun cur => ?_
  refine hk1_bind (q1_dequeue_hk t) fun _ => ?_
  refine hk1_bind (q1_threadSet_nq _ t) fun _ => ?_
  exact hk1_of_ik (by q1_auto)
macro_rules | `(tactic| q1_leaf) => `(tactic| with_reducible exact q1_setDomain _ _)

theorem q1_invokeSetDomain (t : ObjRef) (dom : Domain) : Q1K (invokeSetDomain (Z := Unit) t dom) := by
  unfold invokeSetDomain; q1_auto
macro_rules | `(tactic| q1_leaf) => `(tactic| with_reducible exact q1_invokeSetDomain _ _)

theorem q1_invokeDomain (i : DomainInvocation) : Q1K (invokeDomain (Z := Unit) i) := by
  unfold invokeDomain; split <;> q1_auto
macro_rules | `(tactic| q1_leaf) => `(tactic| with_reducible exact q1_invokeDomain _)

/-! ## `set_priority` -/

/-- **`set_priority` keeps T1** when, should the thread not be runnable, it is
in no ready queue (`hR`: l4v `valid_ready_qs`' runnable half at this state;
the runnable branches need nothing). -/
theorem q1_setPriority_p (t : ObjRef) (prio : Priority) (σ : State Unit)
    (hR : T1 σ → ∀ x, σ.kheap t = some (.tcb x) → runnable x.tcbState = false →
      ∀ d p, t ∉ σ.readyQueues d p) :
    IKp T1 σ (setPriority (Z := Unit) t prio) := by
  unfold setPriority getThreadState threadSetPriority getTcbQueue
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  dsimp only at hy
  split at hy
  · obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨x1, hx1, rfl⟩ := q1_mem_threadGet hz
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨x2, hx2, rfl⟩ := q1_mem_threadGet hz
    rw [hx] at hx1 hx2; cases hx1; cases hx2
    obtain ⟨z, ⟨w, hw, hz⟩, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hw
    obtain rfl := Set.mem_singleton_iff.1 hz
    obtain ⟨w, hw, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hw
    dsimp only at hy
    split at hy
    · exact (hk1_bind (q1_dequeue_hk t) fun _ => hk1_bind (q1_threadSet_nq _ t) fun _ =>
        hk1_of_ik (by q1_auto)) σ hσ y hy
    · rename_i hn
      refine q1_threadSet_nq _ t σ ⟨hσ, fun d p hp => ?_⟩ y hy
      obtain ⟨x', hx', h1, h2⟩ := hσ d p t hp
      rw [hx] at hx'; cases hx'
      subst h1; subst h2
      exact hn (Or.inl hp)
  · rename_i hrun
    exact (hk1_bind (q1_threadSet_nq _ t) fun _ => hk1_of_ik (by q1_auto)) σ
      ⟨hσ, hR hσ x hx (by simpa using hrun)⟩ y hy

/-! ## Retype: a step that keeps every existing object -/

/-- **A step keeping the ready queues and every existing object keeps T1**
(new objects land only at empty addresses, which T1 shows are not queued).
With ut1's `retype_keeps_old` (UtFree: no object in an untyped's free part)
this is the no-reset `retype_region` of an Untyped invocation. -/
theorem q1_of_keep {σ σ' : State Unit} (h : T1 σ) (hq : σ'.readyQueues = σ.readyQueues)
    (hk : ∀ q, σ.kheap q ≠ none → σ'.kheap q = σ.kheap q) : T1 σ' := by
  intro d p t ht
  rw [hq] at ht
  obtain ⟨x, hx, h1, h2⟩ := h d p t ht
  exact ⟨x, by rw [hk t (by rw [hx]; exact Option.some_ne_none _), hx], h1, h2⟩

/-! ## The entry shell for the events that invoke nothing -/

/-- The syscalls that perform no invocation (receive, wait, yield): the others
reach `fl4PerformInvocation`, whose `set_priority` (non-runnable branch) and
untyped / MakePool retype and detype need facts T1 does not carry
(KENTRY-PLAN ctq2). -/
def NoInvSys : Syscall → Prop
  | .sysRecv | .sysWait | .sysNBRecv | .sysNBWait | .sysYield => True
  | _ => False

/-- Events that perform no invocation: every non-syscall event (interrupt,
faults, ...) and the `NoInvSys` syscalls. -/
def NoInvEv : Event → Prop
  | .syscallEvent c => NoInvSys c
  | _ => True

theorem q1_fl4HandleSyscall_noInv (rep : Bool) (c : Syscall) (hc : NoInvSys c) :
    Q1KE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [NoInvSys] at hc <;> simp only [fl4HandleSyscall] <;> q1_auto

set_option maxHeartbeats 8000000 in
/-- The non-syscall events (no invocation). -/
theorem q1_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    Q1KE (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; q1_auto

set_option maxHeartbeats 4000000 in
theorem q1_fl4HandleEvent_noInv (rep : Bool) (ev : Event) (hev : NoInvEv ev) :
    Q1KE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    exact ike_bind (by q1_auto) fun _ => ike_bind (by q1_auto) fun _ =>
      ike_whenE _ (q1_fl4HandleSyscall_noInv rep c hev)
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact q1_handleEvent_other ev fun c e => h ⟨c, e⟩

theorem q1_fl4CallKernel_noInv (rep : Bool) (ev : Event) (hev : NoInvEv ev) :
    Q1K (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ik_bind (ike_handleE (q1_fl4HandleEvent_noInv rep ev hev) fun _ => by q1_auto) fun _ => ?_
  exact ik_bind q1_fl4Awaken fun _ => ik_bind q1_schedule fun _ => q1_activateThread

/-- **(b), partial: T1 across a syscall entry that performs no invocation**
(Recv, Wait, NBRecv, NBWait, Yield). No premise. -/
theorem kentry_t1_noInv {c : Syscall} (hc : NoInvSys c) {σ : State Unit} (h : T1 σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c σ).1), T1 y.2 := by
  intro y hy
  refine (show Q1K (fl4KernelEntrySyscall (Z := Unit) true c) from ?_) σ h y hy
  unfold fl4KernelEntrySyscall
  exact ik_bind (ik_gets _) fun ct => ik_bind (q1_fl4SyscallFaultIP ct) fun _ =>
    q1_fl4CallKernel_noInv true _ hc

/-- **(c), partial: T1 across every kernel event that performs no invocation**
(every non-syscall event: interrupt / timer, faults; and the `NoInvSys`
syscalls). No premise. -/
theorem kcall_t1_noInv (rep : Bool) {ev : Event} (hev : NoInvEv ev) {σ : State Unit} (h : T1 σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev σ).1), T1 y.2 :=
  fun y hy => q1_fl4CallKernel_noInv rep ev hev σ h y hy

end

end Fl4Proofs.P3.SInvQ
