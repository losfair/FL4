/-
P3 (DESIGN.md §9), invariant line G1 (rd8a, KENTRY-PLAN rd7 handoff 1(d)):
**CtR after a charging `check_budget`** (spec side only, outside the JAtZ
cone): rd8a-A3's `hCtRc` narrowed to one fact about `handle_timeout`.

* `NRun t s` (t not runnable), `CQ t s := RdyT s t ∨ t ∈ release queue ∨
  NRun t s`; `ctR_of_cq`, `ctR_unsched` (ct not schedulable ⇒ CtR
  vacuously), `ktr_rescheduleRequired` (heap, time, release queue, ct kept),
  `mem_append` (`tcb_sched_append t` puts t in its ready queue).
* **`TmoNR`**: after `handle_timeout t (timeout b)` of a runnable `t`, `t`
  is not runnable (send_fault_ipc sets the fault, then send_ipc blocks the
  sender: BlockedOnSend, or BlockedOnReply / Inactive when a receiver
  waits; the receiver, blocked on receive at its dequeue, is not `t`). The
  one remaining fact of 1(d) (handoff); true in every state.
* **`cq_endTimeslice`** (the three arms: timeout by `TmoNR`; append: R1 at
  the append state (RdD's `rd_append_p`); postpone: the release queue,
  RdL's `rq_postpone`), **`ctR_charge`**, **`hCtRc_of`** (rd8a-A3's `hCtRc`
  from `EF` and `TmoNR`), and the tops `kcall_rdyOff'` / `kentry_rdyOff'`
  with `TmoNR` for `hCtRc`.
-/
import Fl4Proofs.P3.SpecInvRd8A3
open Classical

namespace Fl4Proofs.P3.SInvR.A8
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

abbrev NRun (t : ObjRef) (s : State Unit) : Prop := ∀ x, s.kheap t = some (.tcb x) → runnable x.tcbState = false

abbrev CQ (t : ObjRef) (s : State Unit) : Prop := RdyT s t ∨ t ∈ s.releaseQueue ∨ NRun t s

/-- **The remaining fact of 1(d)** (module docstring). -/
abbrev TmoNR : Prop :=
  ∀ (s : State Unit) (t : ObjRef) (b : Data), (∃ x, s.kheap t = some (.tcb x) ∧ runnable x.tcbState = true) →
    ∀ w ∈ (handleTimeout (Z := Unit) t (.timeout b) s).1, NRun t w.2

theorem ctR_of_cq {s : State Unit} (h : CQ s.curThread s) : CtR s := by
  intro x hx hrun _ hn
  rcases h with h | h | h
  · exact h
  · exact absurd h hn
  · rw [h x hx] at hrun; cases hrun

theorem ctR_unsched {s : State Unit} (h : schedulable s.curThread s = false) : CtR s := by
  intro x hx hrun hA hn
  obtain ⟨x', c, y, n, h1, h2, h3, h4⟩ := hA
  have ex : x = x' := KernelObject.tcb.inj (Option.some.inj (hx.symm.trans h1))
  subst ex
  rw [Sched.schedulable_of hx h2 hrun h3 h4 hn] at h; cases h

theorem ktr_rescheduleRequired (K : ObjRef → Option KernelObject) (T : Time) (R : List ObjRef) (c : ObjRef) :
    IK (KTC K T R c) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  repeat' (first | ik_step0 | ik_unfold)

theorem cq_ktc {t : ObjRef} {s s' : State Unit} (h : CQ t s) (hk : s'.kheap = s.kheap) (ht : s'.curTime = s.curTime)
    (hr : s'.releaseQueue = s.releaseQueue) : CQ t s' := by
  rcases h with h | h | h
  · exact Or.inl (rdyT_kt h hk ht)
  · exact Or.inr (Or.inl (by rw [hr]; exact h))
  · exact Or.inr (Or.inr fun x hx => h x (by rw [← hk]; exact hx))

theorem mem_append {t : ObjRef} {s : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (tcbSchedAction (Z := Unit) tcbSchedAppend t s).1) : ∃ d p, t ∈ y.2.readyQueues d p := by
  obtain ⟨x, -, e⟩ := SInvQ.q1_tsa_out hy
  refine ⟨x.tcbDomain, x.tcbPriority, ?_⟩
  rw [e]
  dsimp only
  rw [if_pos ⟨rfl, rfl⟩]
  unfold tcbSchedAppend
  by_cases h : t ∈ s.readyQueues x.tcbDomain x.tcbPriority <;> simp [h]

/-- **`end_timeslice` leaves ct `RdyT`, released-queued or not runnable.** -/
theorem cq_endTimeslice (c : Bool) (s : State Unit) {z : SchedContext} {n : Nat} {xt : Tcb} (hR : Rdy s)
    (hk : s.kheap s.curSc = some (.schedContext z n)) (ha : scActive z = true)
    (hct : s.kheap s.curThread = some (.tcb xt)) (hb : xt.tcbSchedContext = some s.curSc)
    (hp : z.scTcb = some s.curThread) (hrun : runnable xt.tcbState = true) (hT : TmoNR) :
    ∀ w ∈ (endTimeslice (Z := Unit) c s).1, CQ s.curThread w.2 := by
  intro w hw
  unfold endTimeslice at hw
  rw [nd_gets_bind] at hw
  obtain ⟨r1, h1, hw⟩ := hw
  have e1 : r1.2 = s := SInvQ.cq5_ro (fun _ => by unfold isRoundRobin; repeat' (first | ik_step0 | ik_unfold)) h1
  obtain ⟨rr, s1⟩ := r1
  simp only at e1
  subst s1
  dsimp only at hw
  rw [nd_gets_bind] at hw
  obtain ⟨r2, h2, hw⟩ := hw
  obtain ⟨x2, -, rfl⟩ := SInvQ.q1_mem_threadGet h2
  dsimp only at hw
  split at hw <;> (obtain ⟨r3, h3, hw⟩ := hw)
  all_goals
    have e3 : r3.2 = s := by
      first
        | exact congrArg Prod.snd (Set.mem_singleton_iff.1 h3)
        | exact SInvQ.cq5_ro (fun _ => by unfold isValidTimeoutHandler; repeat' (first | ik_step0 | ik_unfold)) h3
    obtain ⟨vl, s3⟩ := r3
    simp only at e3
    subst s3
    dsimp only at hw
    split at hw
    · obtain ⟨r4, h4, hw⟩ := hw
      have e4 : r4.2 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h4
      obtain ⟨sc, s4⟩ := r4
      simp only at e4
      subst s4
      exact Or.inr (Or.inr (hT s _ _ ⟨xt, hct, hrun⟩ w hw))
    · obtain ⟨w1, hw1, hw⟩ := hw
      obtain rfl := mem_getScRefillReady hk hw1
      obtain ⟨w2, hw2, hw⟩ := hw
      obtain rfl := mem_getScRefillSufficient hk 0 hw2
      dsimp only at hw
      split at hw
      · rename_i hc
        have hRw := rd_append_p _ s ⟨xt, _, z, n, hct, hb, hk, ha, hc.1⟩ hR w hw
        obtain ⟨d, p, hm⟩ := mem_append hw
        exact Or.inl (hRw.1 d p _ hm)
      · exact Or.inr (Or.inl (rq_postpone (fun y m hy => by rw [hk] at hy; cases hy; exact hp) hw))

/-- `charge_budget`'s tail when ct is schedulable. -/
theorem cq_cbTail (s : State Unit) {z : SchedContext} {n : Nat} {xt : Tcb} (hR : Rdy s)
    (hk : s.kheap s.curSc = some (.schedContext z n)) (ha : scActive z = true)
    (hct : s.kheap s.curThread = some (.tcb xt)) (hb : xt.tcbSchedContext = some s.curSc)
    (hp : z.scTcb = some s.curThread) (hT : TmoNR) (hs : schedulable s.curThread s = true)
    {r : Unit × State Unit} (hr : r ∈ (cbTail true s).1) : CQ s.curThread r.2 := by
  have hrun : runnable xt.tcbState = true := SInv.sched_runnable hs xt hct
  unfold cbTail at hr
  rw [nd_gets_bind, nd_gets_bind] at hr
  rw [NonDet.when, if_pos hs] at hr
  obtain ⟨y1, hy1, hr⟩ := hr
  obtain ⟨y2, hy2, hr⟩ := hr
  have q1 := cq_endTimeslice true s hR hk ha hct hb hp hrun hT y1 hy1
  obtain ⟨k2, t2, r2, -⟩ := ktr_rescheduleRequired y1.2.kheap y1.2.curTime y1.2.releaseQueue y1.2.curThread y1.2
    ⟨rfl, rfl, rfl, rfl⟩ y2 hy2
  have q2 := cq_ktc q1 k2 t2 r2
  obtain rfl := Set.mem_singleton_iff.1 hr
  exact q2

/-- **CtR after `charge_budget … true`** at the entry, from `TmoNR`. -/
theorem ctR_charge {σ : State Unit} (hR : Rdy σ) (hS : SInvB.ScInv σ)
    (hcs : SInvQ.CurScT σ) {xt : Tcb} (hct : σ.kheap σ.curThread = some (.tcb xt))
    (hst : xt.tcbState = .running ∨ xt.tcbState = .idleThreadState)
    (hQ : SInvQ.CtQ σ) (hSi : SInvQ.Simple σ) (hCA : CAx σ) (hni : σ.curThread ≠ σ.idleThread) (hT : TmoNR)
    {z : Unit × State Unit} (hc : z ∈ (chargeBudget (Z := Unit) σ.consumedTime true σ).1) : CtR z.2 := by
  obtain ⟨xa, c, y, n, hxa, hca, hky, hact⟩ := hCA hni
  rw [hct] at hxa; cases hxa
  have hb : xt.tcbSchedContext = some σ.curSc := hcs xt hct
  rw [hb] at hca; cases hca
  obtain ⟨y0, k0, hy0, hyT, hne⟩ := hS.back σ.curThread xt σ.curSc hct hb
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
  obtain ⟨hcf, hid⟩ := cbTail_cf hr1
  have ect : z.2.curThread = σ.curThread := congrArg (fun p => p.2.2.1) hcf
  by_cases hsch : schedulable σ.curThread ({ updSc σ σ.curSc z0 n with consumedTime := 0 } : State Unit) = true
  · apply ctR_of_cq
    rw [ect]
    exact cq_cbTail _ hR1 hk1 ha1 hct1 hb (e1.trans hyT) hT hsch hr1
  · have e' := hid (Bool.eq_false_iff.mpr hsch)
    rw [e']
    exact ctR_unsched (Bool.eq_false_iff.mpr hsch)

/-- **rd8a-A3's `hCtRc`** from the entry facts and `TmoNR`. -/
theorem hCtRc_of {σ : State Unit} (h : EF σ) (hT : TmoNR) :
    ∀ y ∈ (updateTimeStamp (Z := Unit) σ).1, ∀ z ∈ (chargeBudget (Z := Unit) y.2.consumedTime true y.2).1,
      CtR z.2 := by
  intro y hy z hz
  obtain ⟨xt, hct, hst⟩ := h.ct
  obtain ⟨ek, ec, -, -⟩ := SInvO.uts_off hy
  obtain ⟨eq, ea, -, -⟩ := qa_updateTimeStamp σ.readyQueues σ.schedulerAction σ.releaseQueue σ.idleSc σ
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  obtain ⟨et, eit⟩ := ci_updateTimeStamp σ.curThread σ.idleThread σ ⟨rfl, rfl⟩ y hy
  have hS' : SInvB.ScInv y.2 := by
    unfold SInvB.ScInv SInvB.ScSym SInvB.ScBackS SInvB.ScFwd SInvB.RNE; rw [ek]; exact h.sc
  have hcs' : SInvQ.CurScT y.2 := by intro x hx; rw [ek, et] at hx; rw [ec]; exact h.cs x hx
  have hct' : y.2.kheap y.2.curThread = some (.tcb xt) := by rw [ek, et]; exact hct
  have hQ' : SInvQ.CtQ y.2 := by intro d p; rw [eq, et]; exact h.q d p
  have hSi' : SInvQ.Simple y.2 := by intro t; rw [ea]; exact h.si t
  have hCA' : CAx y.2 := by
    intro h'; rw [et, eit] at h'
    obtain ⟨x, c, z, n, h1, h2, h3, h4⟩ := h.ca h'
    exact ⟨x, c, z, n, by rw [ek, et]; exact h1, h2, by rw [ek]; exact h3, h4⟩
  have hni' : y.2.curThread ≠ y.2.idleThread := by rw [et, eit]; exact h.ni
  exact ctR_charge (rdy_updateTimeStamp h.vmt h.rdy hy) hS' hcs' hct' hst hQ' hSi' hCA' hni' hT hz

/-! ## The tops with `TmoNR` for `hCtRc` -/

theorem kcall_rdyOff' (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → EF σ) (hT : TmoNR)
    (hBody : ∀ c, ev = .syscallEvent c → ∀ v ∈ (front σ).1, v.1 = true → ∀ y ∈ (bodyRun rep c v.2).1,
      SS y.2 ∧ NQ [] y.2)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ∀ y ∈ (evRun rep ev σ).1, SS y.2 ∧ NQ [] y.2)
    (hAw : ∀ y ∈ (evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, RCA y2.2 ∧ CtR y2.2 ∧ HRC y2.2)
    (hX : ∀ y ∈ (evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, XS y2.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kcall_rdyOff rep ev σ hEF (fun c e => hCtRc_of (hEF c e) hT) hBody hEvO hAw hX

theorem kentry_rdyOff' (rep : Bool) (c : Syscall) (σ : State Unit) (h : EF σ) (hT : TmoNR)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      (∀ v ∈ (front w.2).1, v.1 = true → ∀ y ∈ (bodyRun rep c v.2).1, SS y.2 ∧ NQ [] y.2) ∧
      (∀ y ∈ (evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1,
        RCA y2.2 ∧ CtR y2.2 ∧ HRC y2.2) ∧
      (∀ y ∈ (evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, XS y2.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kentry_rdyOff rep c σ h fun w hw =>
    ⟨hCtRc_of (ef_fip h w hw) hT, (hW w hw).1, (hW w hw).2.1, (hW w hw).2.2⟩

end

end Fl4Proofs.P3.SInvR.A8
