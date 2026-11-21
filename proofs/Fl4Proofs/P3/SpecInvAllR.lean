/-
P3 (DESIGN.md §9), invariant line G1 (ctq20): **`RS` (the action is
`resume_cur_thread`) at every kernel exit, and the bundle `SInvCR := SInvCQ ∧
RS`** (spec side only, outside the JAtZ cone). `RS σ` is `Entered σ`'s second
half (l4v `schact_is_rct` at kernel entry); `kernel_entryJ30D`
(XTopJointKEntry30D) reads it from `SInvCR`.

* **`schedule` ends at `resume_cur_thread`** (ctq5's `rs_schedule`, no premise).
* **`activate_thread` does NOT keep it unconditionally** (FINDING): on a
  `Restart` current thread it runs `set_thread_state ct Running`, whose
  `set_thread_state_act` sets `choose_new_thread` when ct is not
  `schedulable` (runnable, bound to an active SC, not released). `P20.act_rs`:
  from `RS`, every outcome of `activate_thread` has `RS`, or ct is a
  `Running` TCB that is not schedulable there. The write only changes the
  action, so the exit state itself decides it.
* **`P20.rs_exit` (no premise beyond facts at the exit state)**: at every
  outcome `r` of `schedule ; activate_thread`, `RS r` follows from
  (a) rd's `CAx r` (ct, unless idle, bound to an active SC; l4v
  `active_sc_tcb_at ct`), (b) ct not released at `r`, (c) the idle thread in
  `IdleThreadState` at `r`. `P20.kcall_rs_exit` / `P20.kentry_rs_exit` for
  `call_kernel` / the syscall entry.
* (b) and (c) are already carried: `SInvCQ.notRel` (ctq6's `RB`: its `NP ct`
  half is unconditional) and `SInvCQ.idleSt` (vi3's `ValidIdle` in SInvB), at
  every exit by `kentry_sinvCQ` / `kcall_sinvCQ`.
* (a) is **rd's**: `CAx` at every exit is the third conjunct of rd10's
  `kentry_rdyOff3` / `kcall_rdyOff3i`, which still take the rd line's open
  hypotheses. Nothing in `SInvCQ` implies it (no carried field says ct's SC is
  active; `CurScT` only binds ct to `cur_sc`). So, as g1d's `_ofRdy`, the
  bundle tops take it **by name**: `kentry_rs_ofCA` / `kcall_rs_ofCA` (hCA :
  CAx at every exit of this operation) and the rd-composed
  `kentry_rs_ofRd` / `kcall_rs_ofRd` (exactly rd10's remaining hypotheses).
  `RS` at the entry is not read (`schedule` re-establishes it).
* `boot_rs : RS initASt` (`initASt.schedulerAction = .resumeCurThread`, by
  `rfl`: boot needs nothing). `SInvCR`, `boot_sinvCR`, `kentry_sinvCR_ofCA` /
  `kcall_sinvCR_ofCA`, `kentry_sinvCR_ofRd` / `kcall_sinvCR_ofRd`.
-/
import Fl4Proofs.P3.SpecInvAllQ
import Fl4Proofs.P3.SpecInvRd10A3
open Classical

namespace Fl4Proofs.P3.SInvQ.P20
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

theorem rs_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : IK RS (asUser (Z := Unit) t u) := by
  unfold asUser; fr_auto

theorem rs_completeYieldTo (t : ObjRef) : IK RS (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; fr_auto

/-- `set_thread_state ct Running` from `RS`: the action stays, or ct is a
`Running` TCB that is not schedulable (then `choose_new_thread`). -/
theorem rs_setRun (t : ObjRef) (s : State Unit) (hs : s.curThread = t) (hr : RS s) :
    ∀ y ∈ (setThreadState (Z := Unit) t .running s).1, y.2.curThread = t ∧ (RS y.2 ∨
      (schedulable t y.2 = false ∧ ∃ x, y.2.kheap t = some (.tcb x) ∧ x.tcbState = .running)) := by
  unfold setThreadState
  intro y ⟨z, hz, hy⟩
  obtain ⟨x, -, hz2⟩ := Fl4Proofs.P3.SInvB.mem_threadSet hz
  have hk : z.2.kheap t = some (.tcb { x with tcbState := .running }) := by rw [hz2]; simp
  have hzr : RS z.2 := by rw [hz2]; exact hr
  have hzc : z.2.curThread = t := by rw [hz2]; exact hs
  unfold setThreadStateAct at hy
  dsimp only at hy
  rw [Notif.nd_gets_bind, Notif.nd_gets_bind, Notif.nd_gets_bind] at hy
  unfold NonDet.when at hy
  split at hy
  · rename_i hc
    unfold setSchedulerAction NonDet.modify at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact ⟨hzc, Or.inr ⟨Bool.eq_false_iff.2 hc.2.2, _, hk, rfl⟩⟩
  · unfold NonDet.pure at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact ⟨hzc, Or.inl hzr⟩

/-- **`activate_thread` from `RS`**: `RS`, or ct is a `Running` TCB that is not
schedulable at the outcome. -/
theorem act_rs (s : State Unit) (hr : RS s) :
    ∀ y ∈ (activateThread (Z := Unit) s).1, RS y.2 ∨
      (schedulable y.2.curThread y.2 = false ∧
        ∃ x, y.2.kheap y.2.curThread = some (.tcb x) ∧ x.tcbState = .running) := by
  unfold activateThread
  intro y ⟨z, hz, hy⟩
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨w, hw, hy⟩ := hy
  unfold getTcbObjRef at hw
  obtain ⟨x0, -, rfl⟩ := q1_mem_threadGet hw
  obtain ⟨v, hv, hy⟩ := hy
  have hvc : v.2.curThread = s.curThread :=
    SInv.ik_when _ (SInv.ct_completeYieldTo (cq := s.curThread) _) s rfl v hv
  have hvr : RS v.2 := SInv.ik_when _ (rs_completeYieldTo _) s hr v hv
  obtain ⟨u, hu, hy⟩ := hy
  unfold getThreadState at hu
  obtain ⟨x, -, rfl⟩ := q1_mem_threadGet hu
  revert hy
  dsimp only
  cases hs : x.tcbState <;> intro hy
  case running =>
    rw [Set.mem_singleton_iff.1 hy]; exact Or.inl hvr
  case restart =>
    obtain ⟨a, ha, hy⟩ := hy
    have ha' : a.2.curThread = s.curThread := SInv.ct_asUser (cq := s.curThread) _ _ v.2 hvc a ha
    have har : RS a.2 := rs_asUser _ _ v.2 hvr a ha
    obtain ⟨b, hb, hy⟩ := hy
    have hb' : b.2.curThread = s.curThread := SInv.ct_asUser (cq := s.curThread) _ _ a.2 ha' b hb
    have hbr : RS b.2 := rs_asUser _ _ a.2 har b hb
    obtain ⟨hyc, h | ⟨h1, h2⟩⟩ := rs_setRun _ b.2 hb' hbr y hy
    · exact Or.inl h
    · right; rw [hyc]; exact ⟨h1, h2⟩
  case idleThreadState =>
    unfold archActivateIdleThread at hy
    rw [Set.mem_singleton_iff.1 hy]; exact Or.inl hvr
  all_goals exact hy.elim

/-- **`RS` at the kernel exit** from facts at the exit state: rd's `CAx`, ct
not released, the idle thread in `IdleThreadState`. -/
theorem rs_exit (σ : State Unit) :
    ∀ r ∈ ((schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) σ).1,
      SInvR.CAx r.2 → r.2.curThread ∉ r.2.releaseQueue →
      (∀ x, r.2.kheap r.2.idleThread = some (.tcb x) → x.tcbState = .idleThreadState) → RS r.2 := by
  intro r ⟨z, hz, hr⟩ hCA hq hI
  rcases act_rs z.2 (rs_schedule σ trivial z hz) r hr with h | ⟨hsf, x, hx, hrun⟩
  · exact h
  · exfalso
    by_cases hi : r.2.curThread = r.2.idleThread
    · rw [hi] at hx
      have h1 := hI x hx
      rw [hrun] at h1; cases h1
    · obtain ⟨x', c, y, n, hx', hc, hy, ha⟩ := hCA hi
      rw [hx] at hx'
      cases hx'
      have h1 := Fl4Proofs.P3.Sched.schedulable_of hx hc (by rw [hrun]; rfl) hy ha hq
      rw [hsf] at h1; cases h1

/-- `rs_exit` for every outcome of `call_kernel`. -/
theorem kcall_rs_exit (rep : Bool) (ev : Event) (σ : State Unit) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1,
      SInvR.CAx r.2 → r.2.curThread ∉ r.2.releaseQueue →
      (∀ x, r.2.kheap r.2.idleThread = some (.tcb x) → x.tcbState = .idleThreadState) → RS r.2 := by
  intro r hr
  unfold fl4CallKernel at hr
  obtain ⟨y1, -, hr⟩ := hr
  obtain ⟨y2, -, hr⟩ := hr
  exact rs_exit y2.2 r hr

/-- `rs_exit` for every outcome of the syscall entry. -/
theorem kentry_rs_exit (rep : Bool) (c : Syscall) (σ : State Unit) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1,
      SInvR.CAx r.2 → r.2.curThread ∉ r.2.releaseQueue →
      (∀ x, r.2.kheap r.2.idleThread = some (.tcb x) → x.tcbState = .idleThreadState) → RS r.2 := by
  intro r ⟨y1, h1, hr⟩
  obtain rfl := Set.mem_singleton_iff.1 h1
  obtain ⟨w, -, hr⟩ := hr
  exact kcall_rs_exit rep _ w.2 r hr

end

end Fl4Proofs.P3.SInvQ.P20

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec

noncomputable section

/-- ctq6's `RB` gives ct not released (its `NP ct` half, unconditional). -/
theorem SInvCQ.notRel {σ : State Unit} (h : SInvCQ σ) : σ.curThread ∉ σ.releaseQueue :=
  (h.2.2.1.1.2.1 rfl).2.2

/-- vi3's `ValidIdle`: the idle thread is in `IdleThreadState`. -/
theorem SInvCQ.idleSt {σ : State Unit} (h : SInvCQ σ) :
    ∀ x, σ.kheap σ.idleThread = some (.tcb x) → x.tcbState = .idleThreadState := fun x hx => by
  obtain ⟨y0, hy0, hs, -⟩ := SInvI.vi_idle h.1.1.1.vi
  rw [hy0] at hx; cases hx; exact hs

/-- **`RS` at boot** (`initASt`'s action is `resumeCurThread`). -/
theorem boot_rs : SInvQ.RS (initASt (Z := Unit)) := rfl

set_option maxHeartbeats 1000000 in
/-- **`RS` after the syscall entry**, given rd's `CAx` at every exit (the open
gap, by name). Premises: `hnd` [P], `hct` (SInvB's own [S]). -/
theorem kentry_rs_ofCA (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvCQ σ)
    (hct : σ.curThread ≠ σ.idleThread)
    (hCA : ∀ r ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvR.CAx r.2) :
    ∀ r ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvQ.RS r.2 := fun r hr =>
  have hq := kentry_sinvCQ hnd c h hct r hr
  SInvQ.P20.kentry_rs_exit true c σ r hr (hCA r hr) hq.notRel hq.idleSt

set_option maxHeartbeats 1000000 in
/-- **`RS` after every kernel event**, given rd's `CAx` at every exit. -/
theorem kcall_rs_ofCA (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvCQ σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hCA : ∀ r ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvR.CAx r.2) :
    ∀ r ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvQ.RS r.2 := fun r hr =>
  have hq := kcall_sinvCQ hnd rep ev h hev r hr
  SInvQ.P20.kcall_rs_exit rep ev σ r hr (hCA r hr) hq.notRel hq.idleSt

set_option maxHeartbeats 1000000 in
/-- **`RS` after the syscall entry**, `CAx` from rd10's `kentry_rdyOff3`: the
remaining hypotheses are exactly rd10's (`hEF`, `hX` carried by the rd line;
`hW` its open body facts). -/
theorem kentry_rs_ofRd (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvCQ σ)
    (hct : σ.curThread ≠ σ.idleThread) (hEF : SInvR.A8.EF σ) (hX : SInvR.A10.EV10 σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      SInvR.A9.RdBody true c w.2 ∧ (c ≠ .sysYield → SInvR.A9.OsBody true c w.2) ∧
        ∀ y ∈ (SInvR.A8.evRun true (.syscallEvent c) w.2).1, SInvQ.SQ4 y.2) :
    ∀ r ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvQ.RS r.2 :=
  kentry_rs_ofCA hnd c h hct fun r hr => (SInvR.A10.kentry_rdyOff3 true c σ hEF hX hW r hr).2.2

set_option maxHeartbeats 1000000 in
/-- **`RS` after every kernel event**, `CAx` from rd10's `kcall_rdyOff3i`
(exactly rd10's remaining hypotheses). -/
theorem kcall_rs_ofRd (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvCQ σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hEF : ∀ c, ev = .syscallEvent c → SInvR.A8.EF σ) (hEFI : ev = .interrupt → SInvR.A10.EFI σ)
    (hX : SInvR.A10.EV10 σ)
    (hRdB : ∀ c, ev = .syscallEvent c → SInvR.A9.RdBody rep c σ)
    (hOsB : ∀ c, ev = .syscallEvent c → c ≠ .sysYield → SInvR.A9.OsBody rep c σ)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt →
      ∀ y ∈ (SInvR.A8.evRun rep ev σ).1, SInvR.A8.SS y.2 ∧ SInv.NQ [] y.2)
    (hQ4 : ∀ y ∈ (SInvR.A8.evRun rep ev σ).1, SInvQ.SQ4 y.2) :
    ∀ r ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvQ.RS r.2 :=
  kcall_rs_ofCA hnd rep ev h hev fun r hr =>
    (SInvR.A10.kcall_rdyOff3i rep ev σ hEF hEFI hX hev hRdB hOsB hEvO hQ4 r hr).2.2

/-! ## The bundle -/

/-- **`SInvCQ` with `RS`** (`Entered`'s action half). -/
abbrev SInvCR (σ : State Unit) : Prop := SInvCQ σ ∧ SInvQ.RS σ

/-- **`SInvCR` at boot.** -/
theorem boot_sinvCR : SInvCR (initASt (Z := Unit)) := ⟨boot_sinvCQ, boot_rs⟩

/-- **`SInvCR` across the syscall entry**, given rd's `CAx` at every exit (by name). -/
theorem kentry_sinvCR_ofCA (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvCR σ)
    (hct : σ.curThread ≠ σ.idleThread)
    (hCA : ∀ r ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvR.CAx r.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvCR y.2 := fun y hy =>
  ⟨kentry_sinvCQ hnd c h.1 hct y hy, kentry_rs_ofCA hnd c h.1 hct hCA y hy⟩

/-- **`SInvCR` across every kernel event**, given rd's `CAx` at every exit (by name). -/
theorem kcall_sinvCR_ofCA (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvCR σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hCA : ∀ r ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvR.CAx r.2) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvCR y.2 := fun y hy =>
  ⟨kcall_sinvCQ hnd rep ev h.1 hev y hy, kcall_rs_ofCA hnd rep ev h.1 hev hCA y hy⟩

/-- **`SInvCR` across the syscall entry**, rd10's hypotheses for `CAx`. -/
theorem kentry_sinvCR_ofRd (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvCR σ)
    (hct : σ.curThread ≠ σ.idleThread) (hEF : SInvR.A8.EF σ) (hX : SInvR.A10.EV10 σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      SInvR.A9.RdBody true c w.2 ∧ (c ≠ .sysYield → SInvR.A9.OsBody true c w.2) ∧
        ∀ y ∈ (SInvR.A8.evRun true (.syscallEvent c) w.2).1, SInvQ.SQ4 y.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvCR y.2 :=
  kentry_sinvCR_ofCA hnd c h hct fun r hr => (SInvR.A10.kentry_rdyOff3 true c σ hEF hX hW r hr).2.2

/-- **`SInvCR` across every kernel event**, rd10's hypotheses for `CAx`. -/
theorem kcall_sinvCR_ofRd (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvCR σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hEF : ∀ c, ev = .syscallEvent c → SInvR.A8.EF σ) (hEFI : ev = .interrupt → SInvR.A10.EFI σ)
    (hX : SInvR.A10.EV10 σ)
    (hRdB : ∀ c, ev = .syscallEvent c → SInvR.A9.RdBody rep c σ)
    (hOsB : ∀ c, ev = .syscallEvent c → c ≠ .sysYield → SInvR.A9.OsBody rep c σ)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt →
      ∀ y ∈ (SInvR.A8.evRun rep ev σ).1, SInvR.A8.SS y.2 ∧ SInv.NQ [] y.2)
    (hQ4 : ∀ y ∈ (SInvR.A8.evRun rep ev σ).1, SInvQ.SQ4 y.2) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvCR y.2 :=
  kcall_sinvCR_ofCA hnd rep ev h hev fun r hr =>
    (SInvR.A10.kcall_rdyOff3i rep ev σ hEF hEFI hX hev hRdB hOsB hEvO hQ4 r hr).2.2

end

end Fl4Proofs.P3.SInvAll
