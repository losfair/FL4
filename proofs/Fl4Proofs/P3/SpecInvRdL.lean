/-
P3 (DESIGN.md §9), invariant line G1 (rd7): **`send_signal` keeps `Rdy`**
(spec side only, outside the JAtZ cone; KENTRY-PLAN rd6 handoff 2, the
signals, incl. FL4's timer signals `fl4Awaken`).

`send_signal n b` wakes a receive-blocked bound thread (`cancel_ipc`) or
the head of the notification's queue (`update_waiting_ntfn`), then runs the
wake tail: `set_thread_state t Running`, the badge, `maybe_donate_sc t n`,
`possible_switch_to t` when `t` is schedulable, the sporadic unblock check.

* The woken thread was `BlkR` (receive-blocked, or queued on `n`: nq's
  `NtfnQB`), so when bound it is `RdyT` (R3); `SVS` (IpcSV) carries that
  through `cancel_ipc`'s receive arm (`rs_cancelIpc_recv`: Rdy and SVS) and
  `tcb_ntfn_dequeue`.
* When unbound, `maybe_donate_sc` may donate the notification's SC `p`
  (bound to no TCB): `rd_schedContextDonate_free` (`t` is in no ready
  queue, not the switch target, not released — all three would need an SC
  by R1 / R2 / R4 — and running, so `Rdy` keeps under the new binding:
  `rdy_upd_bind`), then `sched_context_resume p` postpones `t` unless its
  head is ready (`sr_schedContextResume`). `SR t s := schedulable t s →
  RdyT s t` is what `possible_switch_to t` under its `schedulable` guard
  needs (`rd_maybeDonateSc_sr`).
* **`rd_sendSignal (hR : Rdy σ) (hN : NtfnQB σ) : ∀ y ∈ send_signal n b σ,
  Rdy y.2`**.
-/
import Fl4Proofs.P3.SpecInvRdK
open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Binding a thread outside the scheduler's sets -/

theorem rdy_upd_bind {σ : State Unit} (h : Rdy σ) (p : ObjRef) (x y : Tcb) (hx : σ.kheap p = some (.tcb x))
    (hnb : ¬ BlkR y.tcbState y.tcbFault) (hq : ∀ d q, p ∉ σ.readyQueues d q)
    (ha : σ.schedulerAction ≠ .switchThread p) (hr : p ∉ σ.releaseQueue) :
    Rdy { σ with kheap := Function.update σ.kheap p (some (.tcb y)) } := by
  set σ' : State Unit := { σ with kheap := Function.update σ.kheap p (some (.tcb y)) }
  have hk : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q := fun q hq => by simp [σ', hq]
  have hp : σ'.kheap p = some (.tcb y) := by simp [σ']
  have F : ∀ {t}, t ≠ p → RdyT σ t → RdyT σ' t := by
    intro t htp ⟨x0, c, y0, n, hx0, hc, hy0, h1, h2⟩
    have hcp : c ≠ p := by rintro rfl; rw [hx] at hy0; cases hy0
    exact ⟨x0, c, y0, n, by rw [hk t htp]; exact hx0, hc, by rw [hk c hcp]; exact hy0, h1, h2⟩
  have G : ∀ {t}, t ≠ p → ActB σ t → ActB σ' t := by
    intro t htp ⟨x0, c, y0, n, hx0, hc, hy0, h1⟩
    have hcp : c ≠ p := by rintro rfl; rw [hx] at hy0; cases hy0
    exact ⟨x0, c, y0, n, by rw [hk t htp]; exact hx0, hc, by rw [hk c hcp]; exact hy0, h1⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun d q t hm => F (fun e => hq d q (e ▸ hm)) (h1 d q t hm),
    fun t e => F (fun e' => ha (e' ▸ e)) (h2 t e), fun t x' c hx' hb hc => ?_, fun q z n hz hz' => ?_,
    fun t hm => G (fun e => hr (e ▸ hm)) (h5 t hm), fun z m hz => ?_⟩
  rotate_right
  · have e : σ.idleSc ≠ p := by rintro e; rw [← e] at hp; change σ'.kheap σ.idleSc = _ at hz; rw [hp] at hz; cases hz
    change σ'.kheap σ.idleSc = _ at hz; rw [hk _ e] at hz; exact h6 z m hz
  · by_cases e : t = p
    · subst e; rw [hp] at hx'; cases hx'; exact absurd hb hnb
    · rw [hk t e] at hx'; exact F e (h3 t x' c hx' hb hc)
  · by_cases e : q = p
    · subst e; rw [hp] at hz; cases hz
    · rw [hk q e] at hz; exact h4 q z n hz hz'

/-- An unbound thread is in no ready queue, not the switch target, not released. -/
theorem free_of_rdy {σ : State Unit} (h : Rdy σ) {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hn : x.tcbSchedContext = none) :
    (∀ d q, t ∉ σ.readyQueues d q) ∧ σ.schedulerAction ≠ .switchThread t ∧ t ∉ σ.releaseQueue := by
  have nr : ¬ RdyT σ t := fun ⟨x', c, _, _, hx', hc, _⟩ => by
    rw [hx] at hx'; cases hx'; rw [hn] at hc; cases hc
  have na : ¬ ActB σ t := fun ⟨x', c, _, _, hx', hc, _⟩ => by
    rw [hx] at hx'; cases hx'; rw [hn] at hc; cases hc
  obtain ⟨h1, h2, -, -, h5, -⟩ := h
  exact ⟨fun d q hm => nr (h1 d q t hm), fun e => nr (h2 t e), fun hm => na (h5 t hm)⟩

/-! ## The donation of an SC bound to no thread -/

/-- **`sched_context_donate p t`** of an SC bound to no TCB to an unbound,
non-blocked thread: `Rdy` kept, and afterwards `p` and `t` are bound to each other. -/
theorem rd_schedContextDonate_free (p t : ObjRef) (σ : State Unit) (hR : Rdy σ) {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) (hn : x.tcbSchedContext = none) (hnb : ¬ BlkR x.tcbState x.tcbFault)
    (hp : ∀ y n, σ.kheap p = some (.schedContext y n) → y.scTcb = none)
    {r : Unit × State Unit} (hr : r ∈ (schedContextDonate (Z := Unit) p t σ).1) :
    Rdy r.2 ∧ (∀ y n, r.2.kheap p = some (.schedContext y n) → y.scTcb = some t) ∧
      (∀ x', r.2.kheap t = some (.tcb x') → x'.tcbSchedContext = some p) := by
  unfold schedContextDonate at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨e, sc, n, hk, hv⟩ := SInvQ.cq5_mem_getScObjRef hz
  obtain ⟨z1, z2⟩ := z
  simp only at e hv; subst z2
  rw [hp sc n hk] at hv; subst hv
  obtain ⟨w, hw, hr⟩ := hr
  unfold NonDet.when at hw
  rw [if_neg (by simp)] at hw
  obtain rfl : w = ((), σ) := hw
  obtain ⟨w2, hw2, hr⟩ := hr
  have hR2 : Rdy w2.2 :=
    rd_updateSchedContext p (scTcbUpdate fun _ => some t) (fun _ => ⟨rfl, rfl, rfl⟩) σ hR w2 hw2
  obtain ⟨y2, n2, hk2, e2⟩ := SInvB.mem_updateSchedContext hw2
  rw [hk] at hk2; cases hk2
  have hpt : p ≠ t := fun e => by rw [e, hx] at hk; cases hk
  have hx2 : w2.2.kheap t = some (.tcb x) := by rw [e2]; simp [Function.update_of_ne (Ne.symm hpt), hx]
  have hkp2 : w2.2.kheap p = some (.schedContext (scTcbUpdate (fun _ => some t) sc) n) := by rw [e2]; simp
  obtain ⟨x3, hx3, e3⟩ := SInv.mem_threadSet hr
  rw [hx2] at hx3; cases hx3
  obtain ⟨hq, ha, hrq⟩ := free_of_rdy hR2 hx2 hn
  refine ⟨?_, fun y m hy => ?_, fun x' hx' => ?_⟩
  · rw [e3]; exact rdy_upd_bind hR2 t x _ hx2 hnb hq ha hrq
  · rw [e3] at hy; dsimp only at hy
    rw [Function.update_of_ne hpt, hkp2] at hy; cases hy; rfl
  · rw [e3] at hx'; dsimp only at hx'
    rw [Function.update_self] at hx'; cases hx'; rfl

/-! ## `sched_context_resume` and the guard of `possible_switch_to` -/

/-- `t`, when schedulable, is released. -/
def SR (t : ObjRef) (s : State Unit) : Prop := schedulable t s = true → RdyT s t

theorem sr_of_rdyT {s : State Unit} {t : ObjRef} (h : RdyT s t) : SR t s := fun _ => h

theorem sr_unbound {s : State Unit} {t : ObjRef} {x : Tcb} (hx : s.kheap t = some (.tcb x))
    (hn : x.tcbSchedContext = none) : SR t s := fun hs => by
  obtain ⟨x', scp, _, _, hx', hsc, _⟩ := Sched.schedulable_inv hs
  rw [hx] at hx'; cases hx'; rw [hn] at hsc; cases hsc

theorem t_mem_orderedInsert {α β : Type} [Nonempty β] {t : α} {ts : List α} {f : α → RMonad Unit β}
    {R : β → β → Prop} {σ : State Unit} {y : List α × State Unit}
    (hy : y ∈ (orderedInsert (Z := Unit) t ts f R σ).1) : y.2 = σ ∧ t ∈ y.1 := by
  unfold orderedInsert at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  have e1 : y1.2 = σ := SInvQ.cq5_ro (fun _ => by repeat' ik_step0) hy1
  rw [e1] at hy
  obtain ⟨y2, hy2, hy⟩ := hy
  have e2 : y2.2 = σ := SInvQ.cq5_ro (fun _ => by repeat' ik_step0) hy2
  rw [e2] at hy
  obtain ⟨y3, hy3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy3] at hy
  obtain ⟨y4, hy4, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy4] at hy
  rw [Set.mem_singleton_iff.1 hy]
  refine ⟨rfl, ?_⟩
  simp

theorem rq_tcbReleaseEnqueue {t : ObjRef} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (tcbReleaseEnqueue (Z := Unit) t σ).1) : t ∈ y.2.releaseQueue := by
  unfold tcbReleaseEnqueue readyTimesAppend setReleaseQueue at hy
  obtain ⟨z0, hz0, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz0
  obtain ⟨z, hz, hy⟩ := hy
  have hm := t_mem_orderedInsert hz
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  unfold NonDet.when at hy
  split_ifs at hy <;> rw [Set.mem_singleton_iff.1 hy] <;> exact hm.2

theorem rq_tcbSchedAction (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) (R : List ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (tcbSchedAction (Z := Unit) act t) := by
  unfold tcbSchedAction
  repeat' (first | ik_step0 | ik_unfold)

theorem rq_postpone {p t : ObjRef} {σ : State Unit}
    (hp : ∀ y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some t) {y : Unit × State Unit}
    (hy : y ∈ (postpone (Z := Unit) p σ).1) : t ∈ y.2.releaseQueue := by
  unfold postpone at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨e, sc, n, hk, hv⟩ := SInvQ.cq5_mem_getScObjRef hz
  obtain ⟨z1, z2⟩ := z
  simp only at e hv; subst z2
  rw [hp sc n hk] at hv; subst hv
  obtain ⟨a, ha, hy⟩ := hy
  obtain ⟨ha1, ha2⟩ := SInvQ.cq5_mem_assertOpt ha
  obtain ⟨u, a2⟩ := a
  simp only at ha1 ha2; subst a2; cases ha1
  obtain ⟨w1, hw1, hy⟩ := hy
  obtain ⟨w2, hw2, hy⟩ := hy
  have h2 := rq_tcbReleaseEnqueue hw2
  rw [Set.mem_singleton_iff.1 hy]
  exact h2

/-- **`sched_context_resume p`**, `p` and `t` bound to each other: afterwards
`t`, when schedulable, is released. -/
theorem sr_schedContextResume (p t : ObjRef) (σ : State Unit)
    (hp : ∀ y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some t)
    (hb : ∀ x, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some p)
    {r : Unit × State Unit} (hr : r ∈ (schedContextResume (Z := Unit) p σ).1) : SR t r.2 := by
  unfold schedContextResume at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨e, n, hk⟩ := SInvQ.cq5_mem_getSc hz
  obtain ⟨scv, z2⟩ := z
  simp only at e hk; subst z2
  obtain ⟨a, ha, hr⟩ := hr
  obtain ⟨ha1, ha2⟩ := SInvQ.cq5_mem_assertOpt ha
  obtain ⟨u, a2⟩ := a
  simp only at ha1 ha2; subst a2
  rw [hp scv n hk] at ha1; cases ha1
  obtain ⟨w, hw, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hw
  dsimp only at hr
  unfold NonDet.when at hr
  split_ifs at hr with hs
  · obtain ⟨w1, hw1, hr⟩ := hr
    obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hw1
    obtain ⟨w2, hw2, hr⟩ := hr
    obtain rfl := mem_getScRefillReady hk hw2
    obtain ⟨w3, hw3, hr⟩ := hr
    obtain ⟨y3, n3, hk3, rfl⟩ := mem_getScRefillSufficient' hw3
    rw [hk] at hk3; cases hk3
    dsimp only at hr
    split_ifs at hr with hc
    · -- postponed: released
      intro hs'
      obtain ⟨_, _, _, _, _, _, _, _, _, hq⟩ := Sched.schedulable_inv hs'
      refine absurd ?_ hq
      obtain ⟨v1, hv1, hr⟩ := hr
      obtain ⟨x1, -, rfl⟩ := SInvQ.q1_mem_threadGet hv1
      obtain ⟨v2, hv2, hr⟩ := hr
      obtain ⟨x2, -, rfl⟩ := SInvQ.q1_mem_threadGet hv2
      obtain ⟨v3, hv3, hr⟩ := hr
      have e3 : v3.2 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hv3
      obtain ⟨v4, hv4, hr⟩ := hr
      obtain ⟨-, e4⟩ := hv4
      rw [e4, e3] at hr
      exact rq_postpone hp hr
    · obtain rfl : r = ((), σ) := hr
      intro _
      obtain ⟨x', scp, y', n', hx', hsc, hrun, hky, hact, -⟩ := Sched.schedulable_inv hs
      rw [hx] at hx'; cases hx'
      rw [hb x hx] at hsc; cases hsc
      rw [hk] at hky; cases hky
      have hrd : refillReady σ.curTime (refillHd scv) = true := by
        by_contra hne
        exact hc ⟨hrun, hact, fun h => hne h.1⟩
      exact ⟨x, p, scv, n, hx, hb x hx, hk, hact, hrd⟩
  · obtain rfl : r = ((), σ) := hr
    exact fun hs' => absurd hs' hs

/-! ## `maybe_donate_sc` -/

/-- **`maybe_donate_sc t n`** of a running thread `t`, `RdyT` when bound:
`Rdy` kept and `SR t` afterwards. -/
theorem rd_maybeDonateSc_sr (t n : ObjRef) (σ : State Unit) (hR : Rdy σ) {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) (hnb : ¬ BlkR x.tcbState x.tcbFault)
    (hRT : ∀ c, x.tcbSchedContext = some c → RdyT σ t)
    {r : Unit × State Unit} (hr : r ∈ (maybeDonateSc (Z := Unit) t n σ).1) : Rdy r.2 ∧ SR t r.2 := by
  unfold maybeDonateSc at hr
  obtain ⟨z, hz, hr⟩ := hr
  unfold getTcbObjRef at hz
  obtain ⟨x1, hx1, rfl⟩ := SInvQ.q1_mem_threadGet hz
  rw [hx] at hx1; cases hx1
  dsimp only at hr
  unfold NonDet.when at hr
  split_ifs at hr with hn
  · obtain ⟨w, hw, hr⟩ := hr
    have ew : w.2 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hw
    obtain ⟨w1, w2⟩ := w
    simp only at ew; subst w2
    cases w1 with
    | none =>
      obtain rfl : r = ((), σ) := hr
      exact ⟨hR, sr_unbound hx hn⟩
    | some p =>
      dsimp only [NonDet.maybeM] at hr
      obtain ⟨v, hv, hr⟩ := hr
      obtain ⟨ev, sc, m, hk, hv1⟩ := SInvQ.cq5_mem_getScObjRef hv
      obtain ⟨v1, v2⟩ := v
      simp only at ev hv1; subst v2; subst hv1
      dsimp only at hr
      split_ifs at hr with hsc
      · obtain ⟨d, hd, hr⟩ := hr
        have hp : ∀ y n, σ.kheap p = some (.schedContext y n) → y.scTcb = none := by
          intro y n' hy; rw [hk] at hy; cases hy; exact hsc
        obtain ⟨hRd, hpd, hbd⟩ := rd_schedContextDonate_free p t σ hR hx hn hnb hp hd
        exact ⟨rd_schedContextResume p d.2 hRd r hr, sr_schedContextResume p t d.2 hpd hbd hr⟩
      · obtain rfl : r = ((), σ) := hr
        exact ⟨hR, sr_unbound hx hn⟩
  · obtain rfl : r = ((), σ) := hr
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hn
    exact ⟨hR, sr_of_rdyT (hRT c hc)⟩

/-! ## The wake tail -/

theorem kh_setThreadStateAct (K : ObjRef → Option KernelObject) (t : ObjRef) :
    IK (fun s : State Unit => s.kheap = K) (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct
  repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when) | (unfold setSchedulerAction))

theorem tcb_setThreadState {t : ObjRef} {ts : ThreadState} {s : State Unit} {x : Tcb}
    (hx : s.kheap t = some (.tcb x)) {y : Unit × State Unit} (hy : y ∈ (setThreadState (Z := Unit) t ts s).1) :
    y.2.kheap t = some (.tcb { x with tcbState := ts }) := by
  unfold setThreadState at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x1, hx1, e⟩ := SInv.mem_threadSet hz
  rw [hx] at hx1; cases hx1
  rw [kh_setThreadStateAct _ t z.2 rfl y hy, e]
  simp

/-- **The wake tail of `send_signal` / `update_waiting_ntfn`** from a state
with `Rdy`, the woken thread `RdyT` when bound. -/
theorem rd_wake (t n : ObjRef) (b : Badge) (s : State Unit) (hs : Rdy s) {x : Tcb}
    (hx : s.kheap t = some (.tcb x)) (hRT : ∀ c, x.tcbSchedContext = some c → RdyT s t)
    (y : Unit × State Unit)
    (hy : y ∈ ((do
      setThreadState (Z := Unit) t .running
      asUser (Z := Unit) t <| setRegister badge_register b
      maybeDonateSc (Z := Unit) t n
      let sched ← NonDet.gets (schedulable t)
      NonDet.when sched <| possibleSwitchTo (Z := Unit) t
      let scopt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t
      ifSporadicCurScTestRefillUnblockCheck (Z := Unit) scopt) s).1) : Rdy y.2 := by
  obtain ⟨z1, h1, hy⟩ := hy
  have e1 : Rdy z1.2 := rd_setThreadState t .running trivial s hs z1 h1
  have v1 : SVK.SVS s z1.2 := SVK.sv_setThreadState' t .running s z1 h1
  have k1 := tcb_setThreadState hx h1
  obtain ⟨z2, h2, hy⟩ := hy
  have e2 : Rdy z2.2 := rd_asUser t _ z1.2 e1 z2 h2
  have v2 : SVK.SVS s z2.2 := v1.trans (SVK.sv_asUser' t _ z1.2 z2 h2)
  obtain ⟨hv2, -⟩ := fk_asUser (K := z1.2.kheap) (c := z1.2.curSc) (u := z1.2.consumedTime)
    (T := z1.2.curTime) (I := z1.2.idleThread) (S := z1.2.idleSc) t _ z1.2 (fk_self z1.2) z2 h2
  have hv := hv2 t
  rw [k1] at hv
  obtain ⟨x2, hx2, ex2⟩ := hv_tcb hv
  have hst2 : x2.tcbState = .running := hvT_st (x := { x with tcbState := .running }) ex2
  have hsc2 : x2.tcbSchedContext = x.tcbSchedContext := hvT_sc (x := { x with tcbState := .running }) ex2
  have hRT2 : ∀ c, x2.tcbSchedContext = some c → RdyT z2.2 t := fun c hc =>
    rdyT_svs (hRT c (hsc2 ▸ hc)) v2
  have hnb2 : ¬ BlkR x2.tcbState x2.tcbFault := not_blkR_run (Or.inl hst2)
  obtain ⟨z3, h3, hy⟩ := hy
  obtain ⟨e3, sr3⟩ := rd_maybeDonateSc_sr t n z2.2 e2 hx2 hnb2 hRT2 h3
  obtain ⟨z4, h4, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 h4
  obtain ⟨z5, h5, hy⟩ := hy
  have e5 : Rdy z5.2 := by
    revert h5
    unfold NonDet.when
    split_ifs with hsch
    · intro h5
      refine rd_possibleSwitchTo_q t z3.2 (fun _ _ _ _ => sr3 hsch) e3 z5 h5
    · intro h5; rw [Set.mem_singleton_iff.1 h5]; exact e3
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, -, rfl⟩ := SInvQ.q1_mem_threadGet h6
  exact (rd_ifCond x6.tcbSchedContext (some false) (some false) z5.2 e5 hy).1

/-! ## `cancel_ipc` of a receive-blocked thread -/

/-- `Rdy` and the scheduler view from `σ0`. -/
abbrev RS (σ0 s : State Unit) : Prop := Rdy s ∧ SVK.SVS σ0 s

theorem rs_of {α : Type} {m : NonDet (State Unit) α} (h1 : RdK m) (h2 : SVK.SVM m) (σ0 : State Unit) :
    IK (RS σ0) m := fun s hs y hy => ⟨h1 s hs.1 y hy, hs.2.trans (h2 s y hy)⟩

theorem sv_tcbEpDequeue (t e : ObjRef) : SVK.SVM (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; sv_auto

theorem sv_tcbNtfnDequeue (t e : ObjRef) : SVK.SVM (tcbNtfnDequeue (Z := Unit) t e) := by
  unfold tcbNtfnDequeue; sv_auto

theorem rs_blockedCancelIpc (σ0 : State Unit) (st : ThreadState) (t : ObjRef) (rp : Option ObjRef) :
    IK (RS σ0) (blockedCancelIpc (Z := Unit) st t rp) := by
  unfold blockedCancelIpc getBlockingObject
  refine ik_bind (ik_assertOpt _) fun ep => ik_bind (rs_of (rd_tcbEpDequeue t ep) (sv_tcbEpDequeue t ep) σ0)
    fun _ => ?_
  dsimp only
  cases rp with
  | none => exact rs_of (rd_setThreadState t .inactive trivial) (SVK.sv_setThreadState' t .inactive) σ0
  | some r =>
    exact ik_bind (rs_of (rd_replyUnlinkTcb t r) (SVK.sv_replyUnlinkTcb t r) σ0)
      fun _ => rs_of (rd_setThreadState t .inactive trivial) (SVK.sv_setThreadState' t .inactive) σ0

/-- **`cancel_ipc t`** of a receive-blocked thread: `Rdy` and `SVS`. -/
theorem rs_cancelIpc_recv (t : ObjRef) (σ : State Unit) (hR : Rdy σ) {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) (hrb : receiveBlocked x.tcbState = true)
    {r : Unit × State Unit} (hr : r ∈ (cancelIpc (Z := Unit) t σ).1) : RS σ r.2 := by
  unfold cancelIpc at hr
  obtain ⟨z, hz, hr⟩ := hr
  unfold getThreadState at hz
  obtain ⟨x1, hx1, rfl⟩ := SInvQ.q1_mem_threadGet hz
  rw [hx] at hx1; cases hx1
  obtain ⟨z2, hz2, hr⟩ := hr
  obtain ⟨x2, hx2, e2⟩ := SInv.mem_threadSet hz2
  rw [hx] at hx2; cases hx2
  have hblk : BlkR x.tcbState x.tcbFault := by
    unfold receiveBlocked at hrb
    split at hrb
    · rename_i e r d h; exact Or.inr (Or.inr ⟨e, r, d, h⟩)
    · cases hrb
  have hR2 : Rdy z2.2 := by
    rw [e2]
    refine rdy_upd hR t _ ⟨fun x0 h => ?_, fun x' h hb hc => ?_, by rw [hx]; rfl⟩
    · rw [hx] at h; cases h; exact ⟨_, rfl, rfl⟩
    · cases h; exact ⟨x, hx, rfl, hblk⟩
  have hS2 : SVK.SVS σ z2.2 := SVK.sv_threadSet' (fun tcb => { tcb with tcbFault := none }) (fun _ => rfl) t σ z2 hz2
  dsimp only at hr
  unfold receiveBlocked at hrb
  split at hrb
  · rename_i e rp d hst
    rw [hst] at hr
    exact rs_blockedCancelIpc σ _ t rp z2.2 ⟨hR2, hS2⟩ r hr
  · cases hrb

/-! ## `send_signal` -/

/-- The woken thread, `BlkR` at `s` and bound, is `RdyT`; carried along `SVS`. -/
theorem rdyT_blk {s s' : State Unit} (hR : Rdy s) {t : ObjRef} {x : Tcb} (hx : s.kheap t = some (.tcb x))
    (hb : BlkR x.tcbState x.tcbFault) (hS : SVK.SVS s s') :
    ∃ x', s'.kheap t = some (.tcb x') ∧ ∀ c, x'.tcbSchedContext = some c → RdyT s' t := by
  have e1 := hS.1 t; rw [hx] at e1
  obtain ⟨x', hx', hxs⟩ := SVK.sv_tcb (o := s'.kheap t) e1
  refine ⟨x', hx', fun c hc => rdyT_svs ?_ hS⟩
  obtain ⟨-, -, h3, -⟩ := hR
  exact h3 t x c hx hb (hxs ▸ hc)

theorem rd_updateWaitingNtfn (n : ObjRef) (q : List ObjRef) (b : Badge) (σ : State Unit) (hR : Rdy σ)
    (hq : ∀ t ∈ q, ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbState = .blockedOnNotification n) :
    ∀ y ∈ (updateWaitingNtfn (Z := Unit) n q b σ).1, Rdy y.2 := by
  intro y hy
  unfold updateWaitingNtfn at hy
  obtain ⟨z, ⟨hne, rfl⟩, hy⟩ := hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  have hR2 := rd_tcbNtfnDequeue _ _ σ hR z2 hz2
  have hS2 := sv_tcbNtfnDequeue _ _ σ z2 hz2
  have hmem : the q.head? ∈ q := by
    cases q with
    | nil => exact absurd rfl hne
    | cons a l => exact List.mem_cons_self
  obtain ⟨x, hx, hst⟩ := hq _ hmem
  obtain ⟨x2, hx2, hRT2⟩ := rdyT_blk hR hx (Or.inl ⟨n, hst⟩) hS2
  exact rd_wake _ n b z2.2 hR2 hx2 hRT2 y hy

/-- **`send_signal` keeps `Rdy`** (module docstring). -/
theorem rd_sendSignal (n : ObjRef) (b : Badge) (σ : State Unit) (hR : Rdy σ) (hN : SInv.NtfnQB σ) :
    ∀ y ∈ (sendSignal (Z := Unit) n b σ).1, Rdy y.2 := by
  intro y hy
  unfold sendSignal at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, e⟩ := SInv.mem_getSimpleKo hz
  obtain ⟨nt, z2⟩ := z
  simp only at hk e; subst z2
  dsimp only at hy
  cases h1 : nt.ntfnObj with
  | idleNtfn =>
    cases h2 : nt.ntfnBoundTcb with
    | none =>
      rw [h1, h2] at hy
      exact rd_setSimpleKo _ _ _ σ hR y hy
    | some tcb =>
      rw [h1, h2] at hy
      obtain ⟨w, hw, hy⟩ := hy
      unfold getThreadState at hw
      obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hw
      dsimp only at hy
      split at hy
      · rename_i hrb
        obtain ⟨c1, hc1, hy⟩ := hy
        obtain ⟨hR1, hS1⟩ := rs_cancelIpc_recv tcb σ hR hx hrb hc1
        have hblk : BlkR x.tcbState x.tcbFault := by
          unfold receiveBlocked at hrb
          split at hrb
          · rename_i e r d h; exact Or.inr (Or.inr ⟨e, r, d, h⟩)
          · cases hrb
        obtain ⟨x1, hx1, hRT1⟩ := rdyT_blk hR hx hblk hS1
        exact rd_wake tcb n b c1.2 hR1 hx1 hRT1 y hy
      · exact rd_setSimpleKo _ _ _ σ hR y hy
  | waitingNtfn queue =>
    rw [h1] at hy
    refine rd_updateWaitingNtfn n queue b σ hR (fun t ht => ?_) y hy
    exact hN n nt t hk (by rw [h1]; exact ht)
  | activeNtfn badge' =>
    rw [h1] at hy
    exact rd_setSimpleKo _ _ _ σ hR y hy

end

end Fl4Proofs.P3.SInvR
