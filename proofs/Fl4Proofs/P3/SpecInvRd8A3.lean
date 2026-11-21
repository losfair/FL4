/-
P3 (DESIGN.md §9), invariant line G1 (rd8a, KENTRY-PLAN rd7 handoff 1(d) and
3): **the wrapper and the tops `kcall_rdy` / `kcall_offReady` /
`kentry_rdy` / `kentry_offReady`** (spec side only, outside the JAtZ cone).

* The facts at `schedule`'s start: this line's **`SS s := Rdy ∧ OS ∧ RCA ∧
  CtR ∧ HRC`** (`HRC` = rd4's `hRC`: under resume ct is bound to cur_sc) and
  the other lines' **`XS s := RNE ∧ ScBackS ∧ ValidIdle ∧ AW ∧ cur_sc an
  SC`** (sb2's ScInv, vi3's ValidIdle, ctq's AW).
* `or_activateThread` (OffReady kept by activate_thread), **`exit_top`**
  (`SS ∧ XS` at schedule's start ⇒ `Rdy ∧ OffReady ∧ CAx` at the exit:
  rd4's `rd_scheduleOff`, RdF's `rd_activateThread`, A2's `cax_exit`).
* **`kcall_of_ev`** (fo1's `fo_fl4CallKernel_of` shape): from `SS ∧ NQ []`
  at every outcome of the event part `evRun` (event, preemption path on an
  error), A1's `ro_fl4Awaken` plus `hAw` (RCA / CtR / HRC across
  fl4Awaken), and `XS` at schedule's start.
* The syscall event part: `evRun_sys_cases` (an outcome is a `false` front
  outcome, or a body outcome after a `true` front); **`front_false`**: `SS ∧
  NQ []` at a `false` front outcome (rd7's `rd_front` for Rdy / OS; when
  check_budget does not charge (domain expired): RCA from CAx, HRC from
  CurScT, CtR from OffReady + CurScT (`ctR_of_off`), kept by the Restart
  write (SVS + CFK); when it charges: the action is not resume afterwards
  (`nr_charge`, rd_cbr's argument), so RCA / HRC hold vacuously; CtR there
  is the hypothesis `hCtRc` (handoff)); **`ev_sys`**.
* Tops: `kcall_rdyOff_sys`, `kcall_rdy`, `kcall_offReady` (+ CAx), and the
  kentry forms through the FaultIP write (`fip_*` transports).
-/
import Fl4Proofs.P3.SpecInvRd8A2
import Fl4Proofs.P3.SpecInvFaultTcbsH8
import Fl4Proofs.P3.SpecInvNtfnQH2
import Fl4Proofs.P3.SpecInvNtfnQF6
import Fl4Proofs.P3.SpecInvNtfnQF5
import Fl4Proofs.P3.SpecInvSbF4
import Fl4Proofs.P3.SpecInvSgI6
open Classical

namespace Fl4Proofs.P3.SInvR.A8
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The facts at `schedule`'s start -/

/-- rd4's `hRC`: under resume the current thread is bound to `cur_sc`. -/
abbrev HRC (s : State Unit) : Prop :=
  s.schedulerAction = .resumeCurThread → ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc

/-- This line's facts at `schedule`'s start. -/
abbrev SS (s : State Unit) : Prop := Rdy s ∧ OS s ∧ RCA s ∧ CtR s ∧ HRC s

/-- The other lines' facts at `schedule`'s start (sb2, vi3, ctq). -/
abbrev XS (s : State Unit) : Prop :=
  SInvB.RNE s ∧ SInvB.ScBackS s ∧ SInvI.ValidIdle s ∧ AW s ∧ ∃ x n, s.kheap s.curSc = some (.schedContext x n)

/-! ## `OffReady` across `activate_thread` -/

theorem or_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scRefills = y.scRefills) : IK Sched.OffReady (updateSchedContext (Z := Unit) q f) := by
  intro s hs y hy
  obtain ⟨y0, n0, hk, e⟩ := SVK.updSc_mem hy
  rw [e]
  intro z n hz
  show (refillHd z).rTime.toNat + s.consumedTime.toNat ≤ s.curTime.toNat
  have hz' : Function.update s.kheap q (some (.schedContext (f y0) n0)) s.curSc = some (.schedContext z n) := hz
  by_cases ec : s.curSc = q
  · rw [ec, Function.update_self] at hz'
    have ez : f y0 = z := by injection hz' with h; injection h
    have := hs y0 n0 (by rw [ec]; exact hk)
    rw [← ez]; unfold refillHd at this ⊢; rw [hf]; exact this
  · rw [Function.update_of_ne ec] at hz'; exact hs z n hz'

theorem or_threadSet (f : Tcb → Tcb) (t : ObjRef) : IK Sched.OffReady (threadSet (Z := Unit) f t) := by
  intro s hs y hy
  obtain ⟨x, -, e⟩ := SInv.mem_threadSet hy
  rw [e]
  intro z n hz
  have hz' : Function.update s.kheap t (some (.tcb (f x))) s.curSc = some (.schedContext z n) := hz
  by_cases ec : s.curSc = t
  · rw [ec, Function.update_self] at hz'; cases hz'
  · rw [Function.update_of_ne ec] at hz'; exact hs z n hz'

theorem offReady_svcf {s s' : State Unit} (hs : Sched.OffReady s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s) :
    Sched.OffReady s' := by
  have ec : s'.curSc = s.curSc := congrArg (fun p => p.2.1) hc
  have eu : s'.consumedTime = s.consumedTime := congrArg (fun p => p.1) hc
  intro z n hz
  rw [ec] at hz
  rw [eu, hS.2.1]
  have e1 := hS.1 s.curSc
  rw [hz] at e1
  obtain ⟨y0, h0, r1, -, -⟩ := SVK.sv_sc (o := s.kheap s.curSc) e1.symm
  have := hs y0 n h0
  unfold refillHd at this ⊢; rw [← r1]; exact this

theorem or_of_svcf {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m) : IK Sched.OffReady m :=
  fun s hs y hy => offReady_svcf hs (h1 s y hy) (h2 s y hy)

syntax "or_leaf" : tactic
macro_rules | `(tactic| or_leaf) => `(tactic| fail "no or_leaf")
macro_rules | `(tactic| or_leaf) => `(tactic| (refine or_updateSchedContext _ _ ?_; intro _; rfl))
macro_rules | `(tactic| or_leaf) => `(tactic| with_reducible exact or_threadSet _ _)
macro_rules | `(tactic| or_leaf) => `(tactic| exact ik_doMachineOp (fun _ _ h => h) _)
macro_rules | `(tactic| or_leaf) => `(tactic|
  (refine or_of_svcf ?_ ?_ <;> first | (sv_leaf; done) | (cfk_leaf; done)))

macro "or_auto" : tactic => `(tactic| repeat' (first | or_leaf | ik_step0))

theorem or_setThreadState (t : ObjRef) (ts : ThreadState) : IK Sched.OffReady (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct; or_auto
macro_rules | `(tactic| or_leaf) => `(tactic| with_reducible exact or_setThreadState _ _)

theorem or_completeYieldTo (t : ObjRef) : IK Sched.OffReady (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo setConsumed schedContextUpdateConsumed schedContextCancelYieldTo replyFromKernel; or_auto

/-- **`activate_thread` keeps `OffReady`.** -/
theorem or_activateThread : IK Sched.OffReady (activateThread (Z := Unit)) := by
  unfold activateThread
  refine ik_bind (ik_gets _) fun _ => ik_bind (by or_auto) fun _ =>
    ik_bind (ik_when _ (or_completeYieldTo _)) fun _ => ik_bind (by or_auto) fun st => ?_
  cases st <;> (try dsimp only) <;> or_auto

/-! ## The exit -/

/-- **The exit**: `SS ∧ XS` at `schedule`'s start give `Rdy ∧ OffReady ∧ CAx`
after `schedule ; activate_thread`. -/
theorem exit_top {s : State Unit} (h : SS s) (hx : XS s) :
    ∀ r ∈ ((schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) s).1,
      Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  obtain ⟨hR, hO, hA, hC, hH⟩ := h
  obtain ⟨hRN, hB, hV, hAW, x, n, hk⟩ := hx
  intro r hr
  have hc := cax_exit s hR hRN hC hAW hA r hr
  obtain ⟨z, hz, hr'⟩ := hr
  obtain ⟨h1, h2⟩ := rd_scheduleOff s hR hRN hC hAW hk hO hB hV hR.2.2.2.2.2 hH z hz
  exact ⟨rd_activateThread z.2 h1 r hr', or_activateThread z.2 h2 r hr', hc⟩

/-! ## The wrapper -/

/-- The event part of `fl4CallKernel` (the event; the preemption path on an error). -/
abbrev evRun (rep : Bool) (ev : Event) : NonDet (State Unit) (Except Unit Unit) :=
  ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev) (fun _ => withoutPreemption (Z := Unit) preemptionPath))

/-- **The wrapper** (fo1's `fo_fl4CallKernel_of` shape). -/
theorem kcall_of_ev (rep : Bool) (ev : Event) (σ : State Unit)
    (hE : ∀ y ∈ (evRun rep ev σ).1, SS y.2 ∧ NQ [] y.2)
    (hAw : ∀ y ∈ (evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, RCA y2.2 ∧ CtR y2.2 ∧ HRC y2.2)
    (hX : ∀ y ∈ (evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, XS y2.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  intro r hr
  unfold fl4CallKernel at hr
  obtain ⟨y1, h1, hr⟩ := hr
  obtain ⟨y2, h2, hr⟩ := hr
  obtain ⟨hS, hN⟩ := hE y1 h1
  obtain ⟨hR2, hO2, -⟩ := ro_fl4Awaken y1.2 ⟨hS.1, hS.2.1, hN⟩ y2 h2
  obtain ⟨hA2, hC2, hH2⟩ := hAw y1 h1 y2 h2
  exact exit_top ⟨hR2, hO2, hA2, hC2, hH2⟩ (hX y1 h1 y2 h2) r hr

/-! ## The syscall event part -/

/-- The syscall body with the preemption path. -/
abbrev bodyRun (rep : Bool) (c : Syscall) : NonDet (State Unit) (Except Unit Unit) :=
  ExceptT.run (NonDetE.handleE (fl4HandleSyscall (Z := Unit) rep c) (fun _ => withoutPreemption (Z := Unit) preemptionPath))

/-- The syscall front. -/
abbrev front : NonDet (State Unit) Bool := updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart (Z := Unit)

theorem evRun_sys_cases {rep : Bool} {c : Syscall} {σ : State Unit} {y : Except Unit Unit × State Unit}
    (hy : y ∈ (evRun rep (.syscallEvent c) σ).1) :
    ∃ v ∈ (front σ).1, (v.1 = false ∧ y.2 = v.2) ∨ (v.1 = true ∧ y ∈ (bodyRun rep c v.2).1) := by
  dsimp only [evRun] at hy
  unfold NonDetE.handleE at hy
  obtain ⟨z, hz, hy⟩ := hy
  simp only [fl4HandleEvent] at hz
  obtain ⟨w, hw, ⟨a, ha, hz⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hz
  · obtain ⟨w', hw', rfl⟩ := ft_mem_liftE hw
    obtain ⟨u, hu, ⟨b, hb, hz⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hz
    · obtain ⟨u', hu', rfl⟩ := ft_mem_liftE hu
      simp only [Except.ok.injEq] at hb; subst hb
      refine ⟨u', ⟨w', hw', hu'⟩, ?_⟩
      unfold NonDetE.whenE at hz
      split at hz
      · rename_i hr; exact Or.inr ⟨by simpa using hr, ⟨z, hz, hy⟩⟩
      · rename_i hr
        refine Or.inl ⟨by simpa using hr, ?_⟩
        have hz' := Set.mem_singleton_iff.1 hz
        subst hz'
        exact congrArg Prod.snd (Set.mem_singleton_iff.1 hy)
    · obtain ⟨_, -, e'⟩ := ft_mem_liftE hu; rw [e'] at he; cases he
  · obtain ⟨_, -, e'⟩ := ft_mem_liftE hw; rw [e'] at he; cases he

/-- `check_budget_restart`'s outcomes, with the Restart write's guard. -/
theorem cbr_cases {σ : State Unit} {r : Bool × State Unit} (hr : r ∈ (checkBudgetRestart (Z := Unit) σ).1) :
    ∃ z, z ∈ (checkBudget (Z := Unit) σ).1 ∧ r.1 = z.1 ∧
      (r.2 = z.2 ∨ (z.1 = false ∧ (∃ x, z.2.kheap z.2.curThread = some (.tcb x) ∧ runnable x.tcbState = true) ∧
        ((), r.2) ∈ (setThreadState (Z := Unit) z.2.curThread .restart z.2).1)) := by
  unfold checkBudgetRestart at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨z1, hz1, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hz1
  obtain ⟨z2, hz2, hr⟩ := hr
  unfold getThreadState at hz2
  obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hz2
  obtain ⟨⟨u, s3⟩, hz3, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hr
  cases u
  refine ⟨z, hz, rfl, ?_⟩
  unfold NonDet.when at hz3
  split_ifs at hz3 with hc
  · right; exact ⟨by simpa using hc.1, ⟨x, hx, by simpa using hc.2⟩, hz3⟩
  · left; exact (Prod.mk.inj (Set.mem_singleton_iff.1 hz3)).2

/-- CtR from OffReady when ct is bound to cur_sc. -/
theorem ctR_of_off {s : State Unit} (hb : ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc)
    (hO : Sched.OffReady s) : CtR s := by
  intro x hx _ hA _
  obtain ⟨x', c, y, n, h1, h2, h3, h4⟩ := hA
  have ex : x = x' := KernelObject.tcb.inj (Option.some.inj (hx.symm.trans h1))
  have h2' : x.tcbSchedContext = some c := by rw [ex]; exact h2
  have hc : c = s.curSc := Option.some.inj (h2'.symm.trans (hb x hx))
  subst hc
  exact ⟨x, s.curSc, y, n, hx, h2', h3, h4, ready_of_nat (Nat.le_trans (Nat.le_add_right _ _) (hO y n h3))⟩

/-- A step keeping the scheduler view and `cfS` keeps `RCA`, `HRC` and the
CtR-from-OffReady situation. -/
theorem keep_svcf {s s' : State Unit} (hS : SVK.SVS s s') (hc : cfS s' = cfS s) :
    (RCA s → RCA s') ∧ (HRC s → HRC s') ∧
      ((∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc) →
        ∀ x, s'.kheap s'.curThread = some (.tcb x) → x.tcbSchedContext = some s'.curSc) := by
  have ec : s'.curSc = s.curSc := congrArg (fun p => p.2.1) hc
  have et : s'.curThread = s.curThread := congrArg (fun p => p.2.2.1) hc
  have ei : s'.idleThread = s.idleThread := congrArg (fun p => p.2.2.2.1) hc
  have hres : s'.schedulerAction = .resumeCurThread → s.schedulerAction = .resumeCurThread :=
    (cw_of_svs (c := s.curSc) hS).2
  have hb : ∀ x', s'.kheap s'.curThread = some (.tcb x') → ∃ x, s.kheap s.curThread = some (.tcb x) ∧
      x'.tcbSchedContext = x.tcbSchedContext := by
    intro x' hx'
    rw [et] at hx'
    have e1 := hS.1 s.curThread
    rw [hx'] at e1
    cases h : s.kheap s.curThread with
    | none => rw [h] at e1; simp [SVK.sv] at e1
    | some o =>
      rw [h] at e1
      cases o <;> simp [SVK.sv] at e1
      exact ⟨_, rfl, e1⟩
  refine ⟨fun h e hn => ?_, fun h e x' hx' => ?_, fun h x' hx' => ?_⟩
  · rw [et] at hn ⊢; rw [ei] at hn
    exact actB_svs (h (hres e) hn) hS
  · obtain ⟨x, hx, ex⟩ := hb x' hx'
    rw [ex, ec]; exact h (hres e) x hx
  · obtain ⟨x, hx, ex⟩ := hb x' hx'
    rw [ex, ec]; exact h x hx

/-- After a charge, the action is not resume (rd_cbr's argument). -/
theorem nr_charge {σ : State Unit} (hR : Rdy σ) (hS : SInvB.ScInv σ)
    (hcs : SInvQ.CurScT σ) {xt : Tcb} (hct : σ.kheap σ.curThread = some (.tcb xt))
    (hst : xt.tcbState = .running ∨ xt.tcbState = .idleThreadState)
    (hQ : SInvQ.CtQ σ) (hSi : SInvQ.Simple σ) (hCB : SInvQ.CB σ)
    (hHB : σ.schedulerAction = .resumeCurThread → σ.curThread ∉ σ.releaseQueue)
    (hCA : CAx σ) (hni : σ.curThread ≠ σ.idleThread) {z : Unit × State Unit}
    (hc : z ∈ (chargeBudget (Z := Unit) σ.consumedTime true σ).1) : z.2.schedulerAction ≠ .resumeCurThread := by
  obtain ⟨xa, c, y, n, hxa, hca, hky, hact⟩ := hCA hni
  rw [hct] at hxa; cases hxa
  have hb : xt.tcbSchedContext = some σ.curSc := hcs xt hct
  rw [hb] at hca; cases hca
  obtain ⟨y0, k0, hy0, -, hne⟩ := hS.back σ.curThread xt σ.curSc hct hb
  rw [hky] at hy0; cases hy0
  have hne' : y.scRefills ≠ [] := hne (Or.inr hact)
  obtain ⟨s1, hR1, hO1, hr1⟩ := rd_chargeBudget_head hR hky
    (fun _ => ⟨hact, hne', fun _ => excl_entry hS.back hcs hct hst hQ hSi⟩) _ true hc
  obtain ⟨z0, e, e1, e2, e3, e4, e5, e6⟩ := hO1
  subst e
  have hk1 : ({ updSc σ σ.curSc z0 n with consumedTime := 0 } : State Unit).kheap σ.curSc =
      some (.schedContext z0 n) := kh_upd _ _ _ _
  have ha1 : scActive z0 = true := by simp only [scActive, e2]; exact hact
  have hcs' : σ.curThread ≠ σ.curSc := fun e => by rw [e, hky] at hct; cases hct
  have hct1 : ({ updSc σ σ.curSc z0 n with consumedTime := 0 } : State Unit).kheap σ.curThread =
      some (.tcb xt) := by simp [Notif.updK, hcs', hct]
  obtain ⟨-, hA⟩ := rd_cbTail' true _ hR1 hk1 ha1 hct1 hb (fwd_chargeOut hS.fwd hky e1) hr1
  obtain ⟨-, hid⟩ := cbTail_cf hr1
  by_cases hres : σ.schedulerAction = .resumeCurThread
  · have hrun : runnable xt.tcbState = true := by
      rcases hCB hres with ⟨x', hx', hr'⟩ | hi
      · rw [hct] at hx'; cases hx'; exact hr'
      · exact absurd hi hni
    have hsch : schedulable σ.curThread ({ updSc σ σ.curSc z0 n with consumedTime := 0 } : State Unit) = true :=
      Sched.schedulable_of hct1 hb hrun hk1 ha1 (hHB hres)
    exact fun e => by have h := hA hsch; (try dsimp only at h); rw [h] at e; cases e
  · by_cases hsch : schedulable σ.curThread ({ updSc σ σ.curSc z0 n with consumedTime := 0 } : State Unit) = true
    · exact fun e => by have h := hA hsch; (try dsimp only at h); rw [h] at e; cases e
    · have h := hid (Bool.eq_false_iff.mpr hsch); (try dsimp only at h); rw [h]; exact hres

theorem actB_svs_back {σ σ' : State Unit} {t : ObjRef} (h : ActB σ' t) (hS : SVK.SVS σ σ') : ActB σ t := by
  obtain ⟨x, c, y, n, hx, hc, hy, h1⟩ := h
  have e1 := hS.1 t; rw [hx] at e1
  obtain ⟨x', hx', hxs⟩ := SVK.sv_tcb (o := σ.kheap t) e1.symm
  have e2 := hS.1 c; rw [hy] at e2
  obtain ⟨y', hy', -, hm, -⟩ := SVK.sv_sc (o := σ.kheap c) e2.symm
  refine ⟨x', c, y', n, hx', hxs.trans hc, hy', ?_⟩
  show activeSc y'.scRefillMax = true
  rw [hm]; exact h1

/-- `set_thread_state` keeps the release queue. -/
theorem rq_setThreadState (R : List ObjRef) (t : ObjRef) (ts : ThreadState) :
    IK (fun s : State Unit => s.releaseQueue = R) (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  repeat' (first | ik_step0 | ik_unfold)

/-- The entry facts `rd_front` reads, at the kernel-call state. -/
structure EF (σ : State Unit) : Prop where
  rdy : Rdy σ
  off : Sched.OffReady σ
  vmt : SInvV.ValidMachineTime σ
  sc : SInvB.ScInv σ
  cs : SInvQ.CurScT σ
  ct : ∃ xt, σ.kheap σ.curThread = some (.tcb xt) ∧ (xt.tcbState = .running ∨ xt.tcbState = .idleThreadState)
  q : SInvQ.CtQ σ
  si : SInvQ.Simple σ
  cb : SInvQ.CB σ
  hb : σ.schedulerAction = .resumeCurThread → σ.curThread ∉ σ.releaseQueue
  ca : CAx σ
  ni : σ.curThread ≠ σ.idleThread
  nq : NQ [] σ

/-- **The `false` front outcome** (module docstring); `hCtRc`: CtR after a charging check_budget. -/
theorem front_false {σ : State Unit} (h : EF σ)
    (hCtRc : ∀ y ∈ (updateTimeStamp (Z := Unit) σ).1, ∀ z ∈ (chargeBudget (Z := Unit) y.2.consumedTime true y.2).1,
      CtR z.2)
    {v : Bool × State Unit} (hv : v ∈ (front σ).1) (hf : v.1 = false) : SS v.2 ∧ NQ [] v.2 := by
  obtain ⟨xt, hct, hst⟩ := h.ct
  obtain ⟨hR1, hO1, -⟩ := rd_front h.rdy h.off h.vmt h.sc h.cs hct hst h.q h.si h.cb h.hb h.ca h.ni hv
  have hN : NQ [] v.2 := by
    obtain ⟨y, hy, hv'⟩ := hv
    exact nq_checkBudgetRestart y.2 (nq_updateTimeStamp σ h.nq y hy) v hv'
  refine ⟨⟨hR1, hO1, ?_⟩, hN⟩
  obtain ⟨y, hy, hv'⟩ := hv
  -- the facts at the time-stamp outcome (rd_front's preamble)
  obtain ⟨ek, ec, -, -⟩ := SInvO.uts_off hy
  obtain ⟨eq, ea, er, ei⟩ := qa_updateTimeStamp σ.readyQueues σ.schedulerAction σ.releaseQueue σ.idleSc σ
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  obtain ⟨et, eit⟩ := ci_updateTimeStamp σ.curThread σ.idleThread σ ⟨rfl, rfl⟩ y hy
  have hO' := SInvO.offReady_updateTimeStamp h.vmt h.off hy
  have hS' : SInvB.ScInv y.2 := by
    unfold SInvB.ScInv SInvB.ScSym SInvB.ScBackS SInvB.ScFwd SInvB.RNE; rw [ek]; exact h.sc
  have hcs' : SInvQ.CurScT y.2 := by intro x hx; rw [ek, et] at hx; rw [ec]; exact h.cs x hx
  have hct' : y.2.kheap y.2.curThread = some (.tcb xt) := by rw [ek, et]; exact hct
  have hQ' : SInvQ.CtQ y.2 := by intro d p; rw [eq, et]; exact h.q d p
  have hSi' : SInvQ.Simple y.2 := by intro t; rw [ea]; exact h.si t
  have hCB' : SInvQ.CB y.2 := by
    intro e; rw [ea] at e
    rcases h.cb e with h' | h'
    · left; rw [ek, et]; exact h'
    · right; rw [et, eit]; exact h'
  have hHB' : y.2.schedulerAction = .resumeCurThread → y.2.curThread ∉ y.2.releaseQueue := by
    intro e; rw [ea] at e; rw [et, er]; exact h.hb e
  have hCA' : CAx y.2 := by
    intro h'; rw [et, eit] at h'
    obtain ⟨x, c, z, n, h1, h2, h3, h4⟩ := h.ca h'
    exact ⟨x, c, z, n, by rw [ek, et]; exact h1, h2, by rw [ek]; exact h3, h4⟩
  have hni' : y.2.curThread ≠ y.2.idleThread := by rw [et, eit]; exact h.ni
  have hR' : Rdy y.2 := rdy_updateTimeStamp h.vmt h.rdy hy
  obtain ⟨z, hz, e1, hz2⟩ := cbr_cases hv'
  -- the facts at check_budget's outcome
  have key : RCA z.2 ∧ HRC z.2 ∧ CtR z.2 ∧
      ((∀ x, z.2.kheap z.2.curThread = some (.tcb x) → x.tcbSchedContext = some z.2.curSc) ∧ Sched.OffReady z.2 ∨
        z.2.schedulerAction ≠ .resumeCurThread) := by
    rcases checkBudget_cases hz with ⟨e, -⟩ | ⟨-, hc⟩
    · rw [e]
      exact ⟨fun _ => hCA', fun _ => hcs', ctR_of_off hcs' hO', Or.inl ⟨hcs', hO'⟩⟩
    · have hnr := nr_charge hR' hS' hcs' hct' hst hQ' hSi' hCB' hHB' hCA' hni' hc
      exact ⟨fun e => absurd e hnr, fun e => absurd e hnr, hCtRc y hy _ hc, Or.inr hnr⟩
  obtain ⟨kA, kH, kC, kO⟩ := key
  rcases hz2 with e | ⟨-, ⟨xr, hxr, hrun⟩, hs⟩
  · rw [e]; exact ⟨kA, kC, kH⟩
  · -- the Restart write
    have hS := SVK.sv_setThreadState' _ .restart z.2 _ hs
    have hc := cfk_setThreadState' _ .restart z.2 _ hs
    obtain ⟨m1, m2, m3⟩ := keep_svcf hS hc
    refine ⟨m1 kA, ?_, m2 kH⟩
    rcases kO with ⟨hb, hOz⟩ | hnr
    · exact ctR_of_off (m3 hb) (offReady_svcf hOz hS hc)
    · -- not resume: CtR from CtR at z.2 (ct runnable there; release queue kept)
      intro x hx hrn hA hn
      have et2 : v.2.curThread = z.2.curThread := congrArg (fun p => p.2.2.1) hc
      have hrq : v.2.releaseQueue = z.2.releaseQueue :=
        rq_setThreadState z.2.releaseQueue _ _ z.2 rfl _ hs
      rw [et2] at hx hA hn ⊢; rw [hrq] at hn
      have hA0 : ActB z.2 z.2.curThread := actB_svs_back hA hS
      exact rdyT_svs (kC xr hxr hrun hA0 hn) hS

/-- **The syscall event part** keeps `SS ∧ NQ []`: the front here, the body by `hBody`. -/
theorem ev_sys (rep : Bool) (c : Syscall) (σ : State Unit) (h : EF σ)
    (hCtRc : ∀ y ∈ (updateTimeStamp (Z := Unit) σ).1, ∀ z ∈ (chargeBudget (Z := Unit) y.2.consumedTime true y.2).1,
      CtR z.2)
    (hBody : ∀ v ∈ (front σ).1, v.1 = true → ∀ y ∈ (bodyRun rep c v.2).1, SS y.2 ∧ NQ [] y.2) :
    ∀ y ∈ (evRun rep (.syscallEvent c) σ).1, SS y.2 ∧ NQ [] y.2 := by
  intro y hy
  obtain ⟨v, hv, ⟨hf, e⟩ | ⟨ht, hb⟩⟩ := evRun_sys_cases hy
  · rw [e]; exact front_false h hCtRc hv hf
  · exact hBody v hv ht y hb

/-! ## The tops -/

/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event** (module docstring;
the hypotheses are listed in KENTRY-PLAN rd8a). -/
theorem kcall_rdyOff (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → EF σ)
    (hCtRc : ∀ c, ev = .syscallEvent c → ∀ y ∈ (updateTimeStamp (Z := Unit) σ).1,
      ∀ z ∈ (chargeBudget (Z := Unit) y.2.consumedTime true y.2).1, CtR z.2)
    (hBody : ∀ c, ev = .syscallEvent c → ∀ v ∈ (front σ).1, v.1 = true → ∀ y ∈ (bodyRun rep c v.2).1,
      SS y.2 ∧ NQ [] y.2)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ∀ y ∈ (evRun rep ev σ).1, SS y.2 ∧ NQ [] y.2)
    (hAw : ∀ y ∈ (evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, RCA y2.2 ∧ CtR y2.2 ∧ HRC y2.2)
    (hX : ∀ y ∈ (evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, XS y2.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  refine kcall_of_ev rep ev σ ?_ hAw hX
  by_cases hs : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := hs
    exact ev_sys rep c σ (hEF c rfl) (hCtRc c rfl) (hBody c rfl)
  · exact hEvO fun c e => hs ⟨c, e⟩

/-! ## Through the FaultIP write -/

/-- The FaultIP write keeps the scalar / queue fields. -/
theorem ek_fip (t : ObjRef) (Q : Domain → Priority → List ObjRef) (A : SchedulerAction) (R : List ObjRef)
    (c i : ObjRef) (T : Time) (M : MachineState) :
    IK (fun s : State Unit => s.readyQueues = Q ∧ s.schedulerAction = A ∧ s.releaseQueue = R ∧ s.curThread = c ∧
      s.idleThread = i ∧ s.curTime = T ∧ s.machineState = M) (fl4SyscallFaultIP (Z := Unit) t) := by
  unfold fl4SyscallFaultIP asUser
  repeat' (first | ik_step0 | ik_unfold)

theorem sv_fip (t : ObjRef) : SVK.SVM (fl4SyscallFaultIP (Z := Unit) t) := by
  unfold fl4SyscallFaultIP; exact SVK.sv_asUser' _ _

theorem cfk_fip (t : ObjRef) : CFK (fl4SyscallFaultIP (Z := Unit) t) := by
  unfold fl4SyscallFaultIP; exact cfk_asUser' _ _

theorem fk_fip (t : ObjRef) (K : ObjRef → Option KernelObject) (c0 : ObjRef) (u : Ticks) (T : Time) (I S : ObjRef) :
    IK (FK K c0 u T I S) (fl4SyscallFaultIP (Z := Unit) t) := by
  unfold fl4SyscallFaultIP; exact fk_asUser K c0 u T I S _ _

/-- **The entry facts survive the FaultIP write.** -/
theorem ef_fip {σ : State Unit} (h : EF σ) : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, EF w.2 := by
  intro w hw
  obtain ⟨eQ, eA, eR, eC, eI, eT, eM⟩ := ek_fip σ.curThread σ.readyQueues σ.schedulerAction σ.releaseQueue
    σ.curThread σ.idleThread σ.curTime σ.machineState σ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ w hw
  have hS := sv_fip σ.curThread σ w hw
  have hc := cfk_fip σ.curThread σ w hw
  have hF := fk_fip σ.curThread σ.kheap σ.curSc σ.consumedTime σ.curTime σ.idleThread σ.idleSc σ (fk_self σ) w hw
  obtain ⟨xt, hct, hst⟩ := h.ct
  obtain ⟨x', hx', ex⟩ := hv_tcb ((hF.1 σ.curThread).trans (congrArg HV hct))
  have hst' : x'.tcbState = xt.tcbState := hvT_st ex
  obtain ⟨-, -, m3⟩ := keep_svcf hS hc
  refine ⟨rd_fl4SyscallFaultIP _ σ h.rdy w hw, offReady_svcf h.off hS hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact SInvV.vmt_tl σ w.2 (by unfold SInvV.tl; rw [eT, eM]) h.vmt
  · exact SInvB.sik_of_sbk (fun _ => SInvB.sb_fl4SyscallFaultIP _) σ h.sc w hw
  · exact m3 h.cs
  · exact ⟨x', by rw [eC]; exact hx', by rw [hst']; exact hst⟩
  · intro d p; rw [eQ, eC]; exact h.q d p
  · intro t; rw [eA]; exact h.si t
  · intro e; rw [eA] at e
    rcases h.cb e with ⟨x0, hx0, hr0⟩ | hi
    · left; rw [hct] at hx0; cases hx0
      exact ⟨x', by rw [eC]; exact hx', by rw [hst']; exact hr0⟩
    · right; rw [eC, eI]; exact hi
  · intro e; rw [eA] at e; rw [eC, eR]; exact h.hb e
  · exact cax_of_ci (fun _ => SInv.ct_fl4SyscallFaultIP _) (fun _ => SInvG.idk_fl4SyscallFaultIP _)
      (ab_of_sv (sv_fip _)) σ h.ca w hw
  · rw [eC, eI]; exact h.ni
  · exact nq_fl4SyscallFaultIP _ σ h.nq w hw

/-- **The syscall entry** (`fl4KernelEntrySyscall`): `Rdy ∧ OffReady ∧ CAx`
afterwards, from the entry facts at the entry state; the remaining
hypotheses are stated at the FaultIP outcome (KENTRY-PLAN rd8a). -/
theorem kentry_rdyOff (rep : Bool) (c : Syscall) (σ : State Unit) (h : EF σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      (∀ y ∈ (updateTimeStamp (Z := Unit) w.2).1, ∀ z ∈ (chargeBudget (Z := Unit) y.2.consumedTime true y.2).1,
        CtR z.2) ∧
      (∀ v ∈ (front w.2).1, v.1 = true → ∀ y ∈ (bodyRun rep c v.2).1, SS y.2 ∧ NQ [] y.2) ∧
      (∀ y ∈ (evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1,
        RCA y2.2 ∧ CtR y2.2 ∧ HRC y2.2) ∧
      (∀ y ∈ (evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, XS y2.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  intro r ⟨y1, h1, hr⟩
  obtain rfl := Set.mem_singleton_iff.1 h1
  obtain ⟨w, hw, hr⟩ := hr
  obtain ⟨hC, hB, hA, hX⟩ := hW w hw
  exact kcall_of_ev rep _ w.2 (ev_sys rep c w.2 (ef_fip h w hw) hC hB) hA hX r hr

theorem kentry_rdy (rep : Bool) (c : Syscall) (σ : State Unit) (h : EF σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      (∀ y ∈ (updateTimeStamp (Z := Unit) w.2).1, ∀ z ∈ (chargeBudget (Z := Unit) y.2.consumedTime true y.2).1,
        CtR z.2) ∧
      (∀ v ∈ (front w.2).1, v.1 = true → ∀ y ∈ (bodyRun rep c v.2).1, SS y.2 ∧ NQ [] y.2) ∧
      (∀ y ∈ (evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1,
        RCA y2.2 ∧ CtR y2.2 ∧ HRC y2.2) ∧
      (∀ y ∈ (evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, XS y2.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 :=
  fun r hr => (kentry_rdyOff rep c σ h hW r hr).1

theorem kentry_offReady (rep : Bool) (c : Syscall) (σ : State Unit) (h : EF σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      (∀ y ∈ (updateTimeStamp (Z := Unit) w.2).1, ∀ z ∈ (chargeBudget (Z := Unit) y.2.consumedTime true y.2).1,
        CtR z.2) ∧
      (∀ v ∈ (front w.2).1, v.1 = true → ∀ y ∈ (bodyRun rep c v.2).1, SS y.2 ∧ NQ [] y.2) ∧
      (∀ y ∈ (evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1,
        RCA y2.2 ∧ CtR y2.2 ∧ HRC y2.2) ∧
      (∀ y ∈ (evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, XS y2.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Sched.OffReady r.2 :=
  fun r hr => (kentry_rdyOff rep c σ h hW r hr).2.1

theorem kcall_rdy (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → EF σ)
    (hCtRc : ∀ c, ev = .syscallEvent c → ∀ y ∈ (updateTimeStamp (Z := Unit) σ).1,
      ∀ z ∈ (chargeBudget (Z := Unit) y.2.consumedTime true y.2).1, CtR z.2)
    (hBody : ∀ c, ev = .syscallEvent c → ∀ v ∈ (front σ).1, v.1 = true → ∀ y ∈ (bodyRun rep c v.2).1,
      SS y.2 ∧ NQ [] y.2)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ∀ y ∈ (evRun rep ev σ).1, SS y.2 ∧ NQ [] y.2)
    (hAw : ∀ y ∈ (evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, RCA y2.2 ∧ CtR y2.2 ∧ HRC y2.2)
    (hX : ∀ y ∈ (evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, XS y2.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 :=
  fun r hr => (kcall_rdyOff rep ev σ hEF hCtRc hBody hEvO hAw hX r hr).1

theorem kcall_offReady (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → EF σ)
    (hCtRc : ∀ c, ev = .syscallEvent c → ∀ y ∈ (updateTimeStamp (Z := Unit) σ).1,
      ∀ z ∈ (chargeBudget (Z := Unit) y.2.consumedTime true y.2).1, CtR z.2)
    (hBody : ∀ c, ev = .syscallEvent c → ∀ v ∈ (front σ).1, v.1 = true → ∀ y ∈ (bodyRun rep c v.2).1,
      SS y.2 ∧ NQ [] y.2)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ∀ y ∈ (evRun rep ev σ).1, SS y.2 ∧ NQ [] y.2)
    (hAw : ∀ y ∈ (evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, RCA y2.2 ∧ CtR y2.2 ∧ HRC y2.2)
    (hX : ∀ y ∈ (evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, XS y2.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Sched.OffReady r.2 :=
  fun r hr => (kcall_rdyOff rep ev σ hEF hCtRc hBody hEvO hAw hX r hr).2.1

end

end Fl4Proofs.P3.SInvR.A8
