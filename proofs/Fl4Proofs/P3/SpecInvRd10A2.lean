/-
P3 (DESIGN.md §9), invariant line G1 (rd10, KENTRY-PLAN rd9 handoff 1):
**the body's start, `charge_budget`, and `handle_yield`** for `OsBody` (spec side
only).

* `SS4 s := OS ∧ RCA ∧ CtR ∧ HRC` (rd8a's `SS` without `Rdy`: this line's
  part of the body carry; `Rdy` is rd8e/f's `hRdB`).
* **`BS`** (the facts at the body's start: rd8a's `EF` without the machine
  time, plus `Suff`); `bs_uts` (EF across update_time_stamp, front_false's
  preamble), **`bs_front`** (a `true` front outcome), `ss4_of_bs`.
* Frames: `os_svcf` / `suff_svcf` (OS across an `SVS ∧ cfS` step), `ctR_sv`
  (CtR across an `SVS ∧ cfS` step keeping ct's state and the release queue),
  **`ss4_updSc`** (an SC update keeping refills / max / TCB, e.g. the
  `sc_consumed` write).
* **`charge_ss4 (h : BS s) u c`**: every outcome of `charge_budget u c` has
  `SS4` (consumed 0 and the action not resume: rd_cbr / nr_charge's
  argument for any amount; CtR: rd8a's `cq_endTimeslice` for either `c`,
  `cq_cbTail'`).
* **`ss4_handleYield`**, **`osBody_yield : A9.OsBody rep .sysYield σ`** from
  rd8a's `EF σ` (NQ by nq3's `nq_handleYield`). No premise.
-/
import Fl4Proofs.P3.SpecInvRd10A1
import Fl4Proofs.P3.SpecInvEqB
open Classical

namespace Fl4Proofs.P3.SInvR.A10
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-- This line's part of `SS` (without `Rdy`). -/
abbrev SS4 (s : State Unit) : Prop := OS s ∧ A8.RCA s ∧ CtR s ∧ A8.HRC s

/-! ## The body's start -/

/-- The facts at the body's start (rd8a's `EF` without the machine time). -/
structure BS (s : State Unit) : Prop where
  rdy : Rdy s
  off : Sched.OffReady s
  sc : SInvB.ScInv s
  cs : SInvQ.CurScT s
  ct : ∃ xt, s.kheap s.curThread = some (.tcb xt) ∧ (xt.tcbState = .running ∨ xt.tcbState = .idleThreadState)
  q : SInvQ.CtQ s
  si : SInvQ.Simple s
  cb : SInvQ.CB s
  hb : s.schedulerAction = .resumeCurThread → s.curThread ∉ s.releaseQueue
  ca : CAx s
  ni : s.curThread ≠ s.idleThread
  nq : NQ [] s

/-- rd8a's `EF` across `update_time_stamp` (front_false's preamble). -/
theorem bs_uts {σ : State Unit} (h : A8.EF σ) {y : Unit × State Unit} (hy : y ∈ (updateTimeStamp (Z := Unit) σ).1) :
    BS y.2 := by
  obtain ⟨xt, hct, hst⟩ := h.ct
  obtain ⟨ek, ec, -, -⟩ := SInvO.uts_off hy
  obtain ⟨eq, ea, er, ei⟩ := qa_updateTimeStamp σ.readyQueues σ.schedulerAction σ.releaseQueue σ.idleSc σ
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  obtain ⟨et, eit⟩ := ci_updateTimeStamp σ.curThread σ.idleThread σ ⟨rfl, rfl⟩ y hy
  refine ⟨rdy_updateTimeStamp h.vmt h.rdy hy, SInvO.offReady_updateTimeStamp h.vmt h.off hy, ?_, ?_,
    ⟨xt, by rw [ek, et]; exact hct, hst⟩, ?_, ?_, ?_, ?_, ?_, ?_, nq_updateTimeStamp σ h.nq y hy⟩
  · unfold SInvB.ScInv SInvB.ScSym SInvB.ScBackS SInvB.ScFwd SInvB.RNE; rw [ek]; exact h.sc
  · intro x hx; rw [ek, et] at hx; rw [ec]; exact h.cs x hx
  · intro d p; rw [eq, et]; exact h.q d p
  · intro t; rw [ea]; exact h.si t
  · intro e; rw [ea] at e
    rcases h.cb e with h' | h'
    · left; rw [ek, et]; exact h'
    · right; rw [et, eit]; exact h'
  · intro e; rw [ea] at e; rw [et, er]; exact h.hb e
  · intro h'; rw [et, eit] at h'
    obtain ⟨x, c, z, n, h1, h2, h3, h4⟩ := h.ca h'
    exact ⟨x, c, z, n, by rw [ek, et]; exact h1, h2, by rw [ek]; exact h3, h4⟩
  · rw [et, eit]; exact h.ni

/-- **A `true` front outcome** is an update_time_stamp outcome with `Suff`. -/
theorem bs_front {σ : State Unit} (h : A8.EF σ) {v : Bool × State Unit} (hv : v ∈ (A8.front σ).1)
    (ht : v.1 = true) : BS v.2 ∧ Suff v.2 := by
  obtain ⟨xt, hct, hst⟩ := h.ct
  obtain ⟨-, -, h3⟩ := rd_front h.rdy h.off h.vmt h.sc h.cs hct hst h.q h.si h.cb h.hb h.ca h.ni hv
  obtain ⟨y, hy, e, hs⟩ := h3 ht
  rw [e]; exact ⟨bs_uts h hy, hs⟩

theorem ss4_of_bs {s : State Unit} (h : BS s) (hs : Suff s) : SS4 s :=
  ⟨Or.inl ⟨h.off, hs⟩, fun _ => h.ca, A8.ctR_of_off h.cs h.off, fun _ => h.cs⟩

/-! ## Frames -/

theorem suff_svcf {s s' : State Unit} (hs : Suff s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s) : Suff s' := by
  have ec : s'.curSc = s.curSc := congrArg (fun p => p.2.1) hc
  have eu : s'.consumedTime = s.consumedTime := congrArg (fun p => p.1) hc
  have ei : s'.idleSc = s.idleSc := congrArg (fun p => p.2.2.2.2.1) hc
  intro z n hz ha hne
  rw [ec] at hz hne; rw [ei] at hne; rw [eu]
  have e1 := hS.1 s.curSc
  rw [hz] at e1
  obtain ⟨y0, h0, r1, m1, -⟩ := SVK.sv_sc (o := s.kheap s.curSc) e1.symm
  have ha0 : scActive y0 = true := by simp only [scActive, m1]; exact ha
  have := hs y0 n h0 ha0 hne
  unfold refillHd at this ⊢; rw [← r1]; exact this

theorem os_svcf {s s' : State Unit} (hs : OS s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s) : OS s' := by
  rcases hs with ⟨hO, hSf⟩ | ⟨h0, hn⟩ | ⟨hid, hin, hna⟩
  · exact Or.inl ⟨A8.offReady_svcf hO hS hc, suff_svcf hSf hS hc⟩
  · have eu : s'.consumedTime = s.consumedTime := congrArg (fun p => p.1) hc
    refine Or.inr (Or.inl ⟨eu.trans h0, ?_⟩)
    rcases hS.2.2 with e | e
    · rw [e]; exact hn
    · rw [e]; exact fun e => by cases e
  · have ec : s'.curSc = s.curSc := congrArg (fun p => p.2.1) hc
    have ei : s'.idleSc = s.idleSc := congrArg (fun p => p.2.2.2.2.1) hc
    refine Or.inr (Or.inr ⟨by rw [ec, ei]; exact hid, fun z n hz => ?_, ?_⟩)
    · rw [ec] at hz
      have e1 := hS.1 s.curSc
      rw [hz] at e1
      obtain ⟨y0, h0, -, m1, -⟩ := SVK.sv_sc (o := s.kheap s.curSc) e1.symm
      have := hin y0 n h0
      simp only [scActive, m1] at this
      exact this
    · rcases hS.2.2 with e | e
      · rw [e]; exact hna
      · rw [e]; exact fun e => by cases e

/-- CtR across an `SVS ∧ cfS` step keeping ct's state and the release queue. -/
theorem ctR_sv {s s' : State Unit} (h : CtR s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s)
    (hr : s'.releaseQueue = s.releaseQueue)
    (ht : ∀ x, s'.kheap s'.curThread = some (.tcb x) → ∃ x0, s.kheap s.curThread = some (.tcb x0) ∧
      x0.tcbState = x.tcbState) : CtR s' := by
  have et : s'.curThread = s.curThread := congrArg (fun p => p.2.2.1) hc
  intro x hx hrun hA hn
  obtain ⟨x0, hx0, es⟩ := ht x hx
  rw [et] at hA hn ⊢; rw [hr] at hn
  exact rdyT_svs (h x0 hx0 (by rw [es]; exact hrun) (A8.actB_svs_back hA hS) hn) hS

/-- **An SC update keeping refills, max and TCB keeps `SS4`.** -/
theorem ss4_updSc (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scRefills = y.scRefills ∧ (f y).scRefillMax = y.scRefillMax ∧ (f y).scTcb = y.scTcb) :
    IK SS4 (updateSchedContext (Z := Unit) q f) := by
  intro s h y hy
  have hS := SVK.sv_updateSchedContext q f hf s y hy
  have hc := cfk_updateSchedContext' q f s y hy
  obtain ⟨m1, m2, -⟩ := A8.keep_svcf hS hc
  obtain ⟨y0, n0, hk0, e⟩ := SInvB.mem_updateSchedContext hy
  refine ⟨os_svcf h.1 hS hc, m1 h.2.1, ctR_sv h.2.2.1 hS hc (by rw [e]) ?_, m2 h.2.2.2⟩
  intro x hx
  rw [e] at hx
  simp only at hx
  by_cases hq : s.curThread = q
  · rw [hq, Function.update_self] at hx; cases hx
  · rw [Function.update_of_ne hq] at hx; exact ⟨x, hx, rfl⟩

/-! ## `charge_budget` from the body's start facts -/

/-- rd8a's `cq_cbTail` for either `canTimeout`. -/
theorem cq_cbTail' (c : Bool) (s : State Unit) {z : SchedContext} {n : Nat} {xt : Tcb} (hR : Rdy s)
    (hk : s.kheap s.curSc = some (.schedContext z n)) (ha : scActive z = true)
    (hct : s.kheap s.curThread = some (.tcb xt)) (hb : xt.tcbSchedContext = some s.curSc)
    (hp : z.scTcb = some s.curThread) (hs : schedulable s.curThread s = true)
    {r : Unit × State Unit} (hr : r ∈ (cbTail c s).1) : A8.CQ s.curThread r.2 := by
  have hrun : runnable xt.tcbState = true := SInv.sched_runnable hs xt hct
  unfold cbTail at hr
  rw [nd_gets_bind, nd_gets_bind] at hr
  rw [NonDet.when, if_pos hs] at hr
  obtain ⟨y1, hy1, hr⟩ := hr
  obtain ⟨y2, hy2, hr⟩ := hr
  have q1 := A8.cq_endTimeslice c s hR hk ha hct hb hp hrun A9.tmoNR y1 hy1
  obtain ⟨k2, t2, r2, -⟩ := A8.ktr_rescheduleRequired y1.2.kheap y1.2.curTime y1.2.releaseQueue y1.2.curThread y1.2
    ⟨rfl, rfl, rfl, rfl⟩ y2 hy2
  have q2 := A8.cq_ktc q1 k2 t2 r2
  obtain rfl := Set.mem_singleton_iff.1 hr
  exact q2

/-- **`charge_budget u c` from the body's start facts**: consumed 0, the action
not resume, CtR (rd_cbr / nr_charge / ctR_charge for any amount and `c`). -/
theorem charge_ss4 {s : State Unit} (h : BS s) (u : Ticks) (c : Bool) {z : Unit × State Unit}
    (hz : z ∈ (chargeBudget (Z := Unit) u c s).1) : SS4 z.2 := by
  obtain ⟨xt, hct, hst⟩ := h.ct
  obtain ⟨xa, c0, y, n, hxa, hca, hky, hact⟩ := h.ca h.ni
  rw [hct] at hxa; cases hxa
  have hb : xt.tcbSchedContext = some s.curSc := h.cs xt hct
  rw [hb] at hca; cases hca
  obtain ⟨y0, k0, hy0, hyT, hne⟩ := h.sc.back s.curThread xt s.curSc hct hb
  rw [hky] at hy0; cases hy0
  have hne' : y.scRefills ≠ [] := hne (Or.inr hact)
  obtain ⟨s1, hR1, hO1, hr1⟩ := rd_chargeBudget_head h.rdy hky
    (fun _ => ⟨hact, hne', fun _ => excl_entry h.sc.back h.cs hct hst h.q h.si⟩) u c hz
  obtain ⟨z0, e, e1, e2, e3, e4, e5, e6⟩ := hO1
  subst e
  have hk1 : ({ updSc s s.curSc z0 n with consumedTime := 0 } : State Unit).kheap s.curSc =
      some (.schedContext z0 n) := kh_upd _ _ _ _
  have ha1 : scActive z0 = true := by simp only [scActive, e2]; exact hact
  have hcs' : s.curThread ≠ s.curSc := fun e => by rw [e, hky] at hct; cases hct
  have hct1 : ({ updSc s s.curSc z0 n with consumedTime := 0 } : State Unit).kheap s.curThread =
      some (.tcb xt) := by simp [Notif.updK, hcs', hct]
  obtain ⟨-, hA⟩ := rd_cbTail' c _ hR1 hk1 ha1 hct1 hb (fwd_chargeOut h.sc.fwd hky e1) hr1
  obtain ⟨hcf, hid⟩ := cbTail_cf hr1
  have hc0 : z.2.consumedTime = 0 := by
    simp only [cfS, Prod.mk.injEq] at hcf; rw [hcf.1]
  have hnr : z.2.schedulerAction ≠ .resumeCurThread := by
    by_cases hres : s.schedulerAction = .resumeCurThread
    · have hrun : runnable xt.tcbState = true := by
        rcases h.cb hres with ⟨x', hx', hr'⟩ | hi
        · rw [hct] at hx'; cases hx'; exact hr'
        · exact absurd hi h.ni
      have hsch : schedulable s.curThread ({ updSc s s.curSc z0 n with consumedTime := 0 } : State Unit) = true :=
        Sched.schedulable_of hct1 hb hrun hk1 ha1 (h.hb hres)
      exact fun e => by have h' := hA hsch; (try dsimp only at h'); rw [h'] at e; cases e
    · by_cases hsch : schedulable s.curThread ({ updSc s s.curSc z0 n with consumedTime := 0 } : State Unit) = true
      · exact fun e => by have h' := hA hsch; (try dsimp only at h'); rw [h'] at e; cases e
      · have h' := hid (Bool.eq_false_iff.mpr hsch); (try dsimp only at h'); rw [h']; exact hres
  have ect : z.2.curThread = s.curThread := congrArg (fun p => p.2.2.1) hcf
  have hC : CtR z.2 := by
    by_cases hsch : schedulable s.curThread ({ updSc s s.curSc z0 n with consumedTime := 0 } : State Unit) = true
    · apply A8.ctR_of_cq
      rw [ect]
      exact cq_cbTail' c _ hR1 hk1 ha1 hct1 hb (e1.trans hyT) hsch hr1
    · have e' := hid (Bool.eq_false_iff.mpr hsch)
      rw [e']
      exact A8.ctR_unsched (Bool.eq_false_iff.mpr hsch)
  exact ⟨Or.inr (Or.inl ⟨hc0, hnr⟩), fun e => absurd e hnr, hC, fun e => absurd e hnr⟩

/-! ## `handle_yield` -/

/-- **`handle_yield` from the body's start facts.** -/
theorem ss4_handleYield {s : State Unit} (h : BS s) : ∀ y ∈ (handleYield (Z := Unit) s).1, SS4 y.2 := by
  intro y hy
  unfold handleYield at hy
  rw [nd_gets_bind] at hy
  obtain ⟨w1, hw1, hy⟩ := hy
  obtain ⟨n1, hk1, e1⟩ := SInvE.mem_getSchedContext hw1
  rw [e1] at hy
  beta_reduce at hy
  rw [nd_gets_bind] at hy
  obtain ⟨w2, hw2, hy⟩ := hy
  obtain ⟨-, rfl⟩ := SInvE.mem_getRefillHead hk1 hw2
  obtain ⟨w3, hw3, hy⟩ := hy
  beta_reduce at hy
  -- the real write of `set_sc_obj_ref sc_consumed_update`: only `sc_consumed` changes
  exact ss4_updSc s.curSc (scConsumedUpdate fun _ => w1.1.scConsumed + s.consumedTime)
    (fun _ => ⟨rfl, rfl, rfl⟩) w3.2 (charge_ss4 h _ false hw3) y hy

/-- Outcomes of a handled `withoutPreemption` computation are its outcomes. -/
theorem mem_handleE_wp {α ε' : Type} {m : SMonad Unit α} {hd : Unit → NonDetE (State Unit) ε' α}
    {s : State Unit} {y : Except ε' α × State Unit}
    (hy : y ∈ (ExceptT.run (NonDetE.handleE (withoutPreemption (Z := Unit) m) hd) s).1) :
    ∃ w ∈ (m s).1, y.2 = w.2 := by
  unfold NonDetE.handleE at hy
  rw [ExceptT.run_mk] at hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨w', hw', rfl⟩ := ft_mem_liftE hw
  exact ⟨w', hw', by rw [Set.mem_singleton_iff.1 hy]⟩

/-- **`OsBody` for `Yield`**, no premise beyond rd8a's entry facts. -/
theorem osBody_yield (rep : Bool) {σ : State Unit} (h : A8.EF σ) : A9.OsBody rep .sysYield σ := by
  intro v hv ht y hy
  obtain ⟨hB, hSf⟩ := bs_front h hv ht
  obtain ⟨w, hw, e⟩ := mem_handleE_wp (m := handleYield (Z := Unit)) hy
  rw [e]
  obtain ⟨a1, a2, a3, a4⟩ := ss4_handleYield hB w hw
  exact ⟨a1, a2, a3, a4, nq_handleYield v.2 hB.nq w hw⟩

/-! ## The tops -/

/-- `OsBody` from the Yield arm (proved) and the other arms. -/
theorem osBody_of (rep : Bool) (c : Syscall) {σ : State Unit} (h : A8.EF σ)
    (hO : c ≠ .sysYield → A9.OsBody rep c σ) : A9.OsBody rep c σ := by
  by_cases e : c = .sysYield
  · subst e; exact osBody_yield rep h
  · exact hO e

/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event** (rd10 top): remaining
`hRdB` (rd8e/f), `hOsB` for the syscalls other than Yield, `hEvO` (the other
events) and `hQ4` (ctq's SQ4 at the event part's outcomes). -/
theorem kcall_rdyOff3 (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → A8.EF σ) (hX : EV10 σ)
    (hni : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hOsB : ∀ c, ev = .syscallEvent c → c ≠ .sysYield → A9.OsBody rep c σ)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2)
    (hQ4 : ∀ y ∈ (A8.evRun rep ev σ).1, SQ4 y.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kcall_rdyOff3a rep ev σ hEF hX hni hRdB (fun c e => osBody_of rep c (hEF c e) (hOsB c e)) hEvO hQ4

/-- **The syscall entry** (rd10 top). -/
theorem kentry_rdyOff3 (rep : Bool) (c : Syscall) (σ : State Unit) (h : A8.EF σ) (hX : EV10 σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ (c ≠ .sysYield → A9.OsBody rep c w.2) ∧
        ∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, SQ4 y.2) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kentry_rdyOff3a rep c σ h hX fun w hw =>
    ⟨(hW w hw).1, osBody_of rep c (A8.ef_fip h w hw) (hW w hw).2.1, (hW w hw).2.2⟩

end

end Fl4Proofs.P3.SInvR.A10
