/-
P3 (DESIGN.md §9), INV-PLAN §4 G1/G4 (g1b): **g1a's per-entry [J] premise `EntryJ`
(l4v `ct_active`) from a carried exit fact** (spec side only; outside the `JAtZ`
cone; namespace `Fl4Proofs.P3.SInvAll`).

* **`CtExit σ`**: the current thread is a TCB in `Running` or `IdleThreadState`.
  The exit's `activate_thread` alone establishes it (no premise): it reads the current
  thread's state after `complete_yield_to` (which keeps `cur_thread`, nq's
  `ct_completeYieldTo`); `Running` returns, `Restart` sets the PC and becomes
  `Running` (`set_thread_state … Running`: the TCB write, then
  `set_thread_state_act`, which only changes the scheduler action), `IdleThreadState`
  runs `arch_activate_idle_thread` (`return ()` on x64), every other state fails.
  `kentry_ctExit` / `kcall_ctExit` (every event): no premise.
* **`OnlyIdle σ`** [J] (l4v `only_idle`: `st_tcb_at idle t s → t = idle_thread s`).
  `CtExit` with `cur_thread ≠ idle_thread` does NOT give `ct_active`: a non-idle
  current thread in `IdleThreadState` satisfies `CtExit` and vi1's carried
  `ValidIdle` (`ObjOK` only says the idle thread is in `IdleThreadState`; it has no
  `only_idle` part), and the spec's `schedule` has no `assert (sched ∨ ct = idle)`
  at `resume_cur_thread`. `OnlyIdle` is true in every reachable state (the spec
  writes `IdleThreadState` nowhere but `initKheap`: every `set_thread_state` has
  another literal state, a new TCB is `defaultTcb` = Inactive, `idle_thread` is never
  written), so it is a per-state premise of the tops here, to be carried as a G1
  field (the NativeScope pattern with the idle pointer exempt; not done here).
  `boot_onlyIdle`.
* **`entryJ_of : CtExit σ → σ.curThread ≠ σ.idleThread → OnlyIdle σ → EntryJ σ`**;
  **`entryJEv_of`** for any event: an interrupt needs nothing (`ct_running ∨ ct_idle`),
  every other event needs `ct ≠ idle` (a trap or fault comes from a user thread, [S]).
* **`SInvA' := SInvA ∧ CtExit`**, **`kentry_sinvA' hnd c h hct hoi`**,
  **`kcall_sinvA' hnd rep ev h hev hoi`**, `kcall_sinvA'_sys`, **`boot_sinvA'`**.
  Premises: `hnd : numDomains = 1` [P] (g1a), `hct : σ.curThread ≠ σ.idleThread`
  (syscall; `JReach.step` has it) / `hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread`
  (events), `hoi : OnlyIdle σ` [J] (above). `EntryJ` / `EntryJEv` are gone.
-/
import Fl4Proofs.P3.SpecInvAll
import Fl4Proofs.P3.SpecInvNtfnQC1

open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The exit fact -/

/-- **The carried exit fact**: the current thread is a TCB in `Running` or
`IdleThreadState` (what `activate_thread` leaves). -/
def CtExit (σ : State Unit) : Prop :=
  ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ (x.tcbState = .running ∨ x.tcbState = .idleThreadState)

/-- **[J] l4v `only_idle`**: only the idle thread is in `IdleThreadState`. -/
def OnlyIdle (σ : State Unit) : Prop :=
  ∀ t x, σ.kheap t = some (.tcb x) → x.tcbState = .idleThreadState → t = σ.idleThread

/-- `set_thread_state ct Running` leaves `CtExit`. -/
theorem ctExit_setThreadState_running (t : ObjRef) (s : State Unit) (hs : s.curThread = t) :
    ∀ y ∈ (setThreadState (Z := Unit) t .running s).1, CtExit y.2 := by
  unfold setThreadState
  intro y ⟨z, hz, hy⟩
  obtain ⟨x, -, hz2⟩ := SInvB.mem_threadSet hz
  have hP : SInv.IK (fun s : State Unit => s.curThread = t ∧
      s.kheap t = some (.tcb { x with tcbState := .running })) (setThreadStateAct (Z := Unit) t) := by
    unfold setThreadStateAct
    repeat' (first | ik_step0 | ik_unfold)
  have h0 := hP z.2 ⟨by rw [hz2]; exact hs, by rw [hz2]; simp⟩ y hy
  exact ⟨_, by rw [h0.1]; exact h0.2, Or.inl rfl⟩

/-- **`activate_thread` leaves `CtExit`** (no premise). -/
theorem ctExit_activateThread : SInvQ.PostK CtExit (activateThread (Z := Unit)) := by
  unfold activateThread
  intro σ y ⟨z, hz, hy⟩
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨w, hw, hy⟩ := hy
  unfold getTcbObjRef at hw
  obtain ⟨x0, -, rfl⟩ := SInvQ.q1_mem_threadGet hw
  obtain ⟨v, hv, hy⟩ := hy
  have hvc : v.2.curThread = σ.curThread :=
    SInv.ik_when _ (SInv.ct_completeYieldTo (cq := σ.curThread) _) σ rfl v hv
  obtain ⟨u, hu, hy⟩ := hy
  unfold getThreadState at hu
  obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hu
  have hx' : v.2.kheap v.2.curThread = some (.tcb x) := by rw [hvc]; exact hx
  revert hy
  dsimp only
  cases hs : x.tcbState <;> intro hy
  case running =>
    rw [Set.mem_singleton_iff.1 hy]; exact ⟨x, hx', Or.inl hs⟩
  case restart =>
    obtain ⟨a, ha, hy⟩ := hy
    have ha' : a.2.curThread = σ.curThread := SInv.ct_asUser (cq := σ.curThread) _ _ v.2 hvc a ha
    obtain ⟨b, hb, hy⟩ := hy
    have hb' : b.2.curThread = σ.curThread := SInv.ct_asUser (cq := σ.curThread) _ _ a.2 ha' b hb
    exact ctExit_setThreadState_running _ b.2 hb' y hy
  case idleThreadState =>
    unfold archActivateIdleThread at hy
    rw [Set.mem_singleton_iff.1 hy]; exact ⟨x, hx', Or.inr hs⟩
  all_goals exact hy.elim

theorem ctExit_fl4CallKernel (rep : Bool) (ev : Event) : SInvQ.PostK CtExit (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  exact SInvQ.post_bind fun _ => SInvQ.post_bind fun _ => SInvQ.post_bind fun _ => ctExit_activateThread

/-- **`CtExit` after every syscall entry** (no premise). -/
theorem kentry_ctExit (c : Syscall) (σ : State Unit) :
    ∀ y ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1, CtExit y.2 := by
  unfold fl4KernelEntrySyscall
  exact SInvQ.post_bind (fun _ => SInvQ.post_bind fun _ => ctExit_fl4CallKernel true _) σ

/-- **`CtExit` after every kernel event** (no premise). -/
theorem kcall_ctExit (rep : Bool) (ev : Event) (σ : State Unit) :
    ∀ y ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, CtExit y.2 :=
  ctExit_fl4CallKernel rep ev σ

/-! ## `EntryJ` from the exit fact -/

/-- **g1a's `EntryJ` [J]** from `CtExit`, `ct ≠ idle` and `OnlyIdle`. -/
theorem entryJ_of {σ : State Unit} (he : CtExit σ) (hct : σ.curThread ≠ σ.idleThread) (hoi : OnlyIdle σ) :
    EntryJ σ := by
  obtain ⟨x, hx, hs⟩ := he
  refine ⟨⟨x, hx, ?_⟩⟩
  rcases hs with hs | hs
  · rw [hs]; exact trivial
  · exact absurd (hoi _ x hx hs) hct

/-- **g1a's `EntryJEv ev` [J]** from `CtExit`: an interrupt needs nothing more; any other
event needs `ct ≠ idle` (and `OnlyIdle`). -/
theorem entryJEv_of {ev : Event} {σ : State Unit} (he : CtExit σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (hoi : OnlyIdle σ) : EntryJEv ev σ := by
  obtain ⟨x, hx, hs⟩ := he
  refine ⟨⟨x, hx, ?_⟩⟩
  rcases hs with hs | hs
  · left; rw [hs]; exact trivial
  · by_cases hi : ev = .interrupt
    · exact Or.inr ⟨hi, hs⟩
    · exact absurd (hoi _ x hx hs) (hev hi)

/-! ## The bundle with the exit fact -/

/-- **`SInvA'`**: g1a's bundle and the exit fact. -/
abbrev SInvA' (σ : State Unit) : Prop := SInvA σ ∧ CtExit σ

/-- **`SInvA'` across the syscall entry.** Premises: the bundle, `hnd` [P],
`hct : ct ≠ idle` (a syscall comes from a user thread; `JReach.step`), `hoi : OnlyIdle σ` [J]. -/
theorem kentry_sinvA' (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvA' σ)
    (hct : σ.curThread ≠ σ.idleThread) (hoi : OnlyIdle σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvA' y.2 :=
  fun y hy => ⟨kentry_sinvA hnd c h.1 (entryJ_of h.2 hct hoi) y hy, kentry_ctExit c σ y hy⟩

/-- **`SInvA'` across every kernel event.** Premises: the bundle, `hnd` [P],
`hev : ev ≠ interrupt → ct ≠ idle` (traps and faults come from a user thread; an
interrupt may arrive in the idle thread), `hoi : OnlyIdle σ` [J]. -/
theorem kcall_sinvA' (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvA' σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (hoi : OnlyIdle σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvA' y.2 :=
  fun y hy => ⟨kcall_sinvA hnd rep ev h.1 (entryJEv_of h.2 hev hoi) y hy, kcall_ctExit rep ev σ y hy⟩

theorem kcall_sinvA'_sys (hnd : numDomains = 1) (rep : Bool) (c : Syscall) {σ : State Unit} (h : SInvA' σ)
    (hct : σ.curThread ≠ σ.idleThread) (hoi : OnlyIdle σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep (.syscallEvent c)) σ).1, SInvA' y.2 :=
  kcall_sinvA' hnd rep _ h (fun _ => hct) hoi

/-! ## Boot (non-vacuity only) -/

theorem boot_ctExit : CtExit (initASt (Z := Unit)) := by
  obtain ⟨x0, h0, -⟩ := SInvB.initKheap_idleThread
  refine ⟨x0, h0, Or.inr ?_⟩
  have h1 := h0
  unfold initKheap at h1
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self] at h1
  cases h1
  rfl

theorem boot_onlyIdle : OnlyIdle (initASt (Z := Unit)) := by
  intro t x ht _
  change initKheap t = some (.tcb x) at ht
  exact (SInvB.init_tcb ht).1

theorem boot_sinvA' : SInvA' (initASt (Z := Unit)) := ⟨boot_sinvA, boot_ctExit⟩

end

end Fl4Proofs.P3.SInvAll
