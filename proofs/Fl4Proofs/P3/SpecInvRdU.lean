/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd3): **`Rdy` across the
unbinding writers** (spec side only, outside the `JAtZ` cone; KENTRY-PLAN rd2
handoff 4, the `R4` writers of lead decision (b)).

A thread losing its SC must not be read by `R1`, `R2` or `R4` afterwards:

* `rdy_upd_unbind` / **`rd_threadSet_unbind`**: unbinding a thread in no ready
  queue, not the switch target, not released.
* **`rd_schedContextUnbindTcb_p`**: `sched_context_unbind_tcb` dequeues and
  release-removes its thread first, and reschedules when it is the current
  thread; otherwise its thread must not be the switch target at the start
  (`hA`; l4v's `sched_context_unbind_tcb` precondition, ctq5's `Simple` at a
  perform). Ready-queue membership is only in the thread's own queue (ctq's
  `T1`). **`rd_schedContextUnbindAllTcbs_p`**.
* **`rd_maybeReturnSc_p`**: the unbound thread (the blocking receiver) in no
  queue, not the switch target, not released (ctq5's `CtQ` / `NP` / `RD`).
* **`rd_schedContextSetInactive_p`**: no thread bound to the SC (it runs only
  after `sched_context_unbind_all_tcbs`; sb2's `ScSym` gives this from
  `sc_tcb = none`); the SC becomes inactive, so `RV` is vacuous for it.
-/
import Fl4Proofs.P3.SpecInvRdS
open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Unbinding one thread -/

theorem rdy_upd_unbind {σ : State Unit} (h : Rdy σ) (p : ObjRef) (x y : Tcb) (hx : σ.kheap p = some (.tcb x))
    (hy : y.tcbSchedContext = none) (hq : ∀ d q, p ∉ σ.readyQueues d q)
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
    · subst e; rw [hp] at hx'; cases hx'; rw [hy] at hc; cases hc
    · rw [hk t e] at hx'; exact F e (h3 t x' c hx' hb hc)
  · by_cases e : q = p
    · subst e; rw [hp] at hz; cases hz
    · rw [hk q e] at hz; exact h4 q z n hz hz'

/-- **Unbinding a thread** in no ready queue, not the switch target, not released. -/
theorem rd_threadSet_unbind (t : ObjRef) (σ : State Unit) (hq : ∀ d p, t ∉ σ.readyQueues d p)
    (ha : σ.schedulerAction ≠ .switchThread t) (hr : t ∉ σ.releaseQueue) :
    IKp Rdy σ (threadSet (Z := Unit) (tcbSchedContextUpdate fun _ => none) t) := by
  unfold threadSet
  intro hσ r ⟨z, hz, hr'⟩
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some x =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    unfold setObject at hr'
    obtain ⟨y, hy, hr'⟩ := hr'
    obtain ⟨hk, hs⟩ := mem_getObject hy
    obtain ⟨y1, y2⟩ := y
    simp only at hk hs; subst hs
    obtain ⟨z, ⟨-, rfl⟩, hr'⟩ := hr'
    obtain ⟨w, hw, hr'⟩ := hr'
    rw [Set.mem_singleton_iff.1 hw] at hr'
    rw [Set.mem_singleton_iff.1 hr']
    exact rdy_upd_unbind hσ t x _ (getTcb_kheap e) rfl hq ha hr

/-! ## The unbinding operations -/

/-- Heap, ready queues and action, fixed. -/
abbrev KQA (K : ObjRef → Option KernelObject) (Q : Domain → Priority → List ObjRef) (A : SchedulerAction)
    (σ : State Unit) : Prop := σ.kheap = K ∧ σ.readyQueues = Q ∧ σ.schedulerAction = A

theorem kqa_tcbReleaseRemove (K : ObjRef → Option KernelObject) (Q : Domain → Priority → List ObjRef)
    (A : SchedulerAction) (t : ObjRef) : IK (KQA K Q A) (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove
  repeat' (first | ik_step0 | ik_unfold)

/-- **`sched_context_unbind_tcb`** (module docstring). -/
theorem rd_schedContextUnbindTcb_p (sc : ObjRef) (σ : State Unit) (h1 : T1 σ)
    (hA : ∀ y n t, σ.kheap sc = some (.schedContext y n) → y.scTcb = some t → t ≠ σ.curThread →
      σ.schedulerAction ≠ .switchThread t) :
    IKp Rdy σ (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb
  intro hσ r ⟨z, hz, hr⟩
  obtain ⟨e, n, hk⟩ := cq5_mem_getSc hz
  obtain ⟨scv, z2⟩ := z
  simp only at e hk; subst z2
  obtain ⟨a, ha, hr⟩ := hr
  obtain ⟨ha1, ha2⟩ := cq5_mem_assertOpt ha
  obtain ⟨t, a2⟩ := a
  simp only at ha1 ha2; subst a2
  obtain ⟨b, hb, hr⟩ := hr
  rw [Set.mem_singleton_iff.1 hb] at hr
  obtain ⟨w, hw, hr⟩ := hr
  have hw' : Rdy w.2 ∧ T1 w.2 ∧ w.2.schedulerAction ≠ .switchThread t := by
    unfold NonDet.when at hw
    split_ifs at hw with ec
    · exact ⟨rd_rescheduleRequired σ hσ w hw, q1_rescheduleRequired σ h1 w hw,
        by rw [rescheduleRequired_cn σ w hw]; exact fun e => by cases e⟩
    · rw [Set.mem_singleton_iff.1 hw]
      exact ⟨hσ, h1, hA scv n t hk ha1 ec⟩
  obtain ⟨w1, w2, w3⟩ := hw'
  obtain ⟨v, hv, hr⟩ := hr
  have v1 := rd_dequeue t w.2 w1 v hv
  obtain ⟨-, v3⟩ := q1_dequeue_hk t w.2 w2 v hv
  obtain ⟨x, -, ev⟩ := q1_tsa_out hv
  have v4 : v.2.schedulerAction ≠ .switchThread t := by rw [ev]; exact w3
  obtain ⟨u, hu, hr⟩ := hr
  have u1 := rd_tcbReleaseRemove t v.2 v1 u hu
  obtain ⟨-, eq, ea⟩ := kqa_tcbReleaseRemove v.2.kheap v.2.readyQueues v.2.schedulerAction t v.2 ⟨rfl, rfl, rfl⟩ u hu
  obtain ⟨-, -, -, er⟩ := mem_tcbReleaseRemove hu
  obtain ⟨s, hs, hr⟩ := hr
  have s1 := rd_threadSet_unbind t u.2 (fun d p hm => v3 d p (by rw [eq] at hm; exact hm))
    (by rw [ea]; exact v4) (by rw [er]; intro hm; simp [tcbSchedDequeue] at hm) u1 s hs
  exact rd_updateSchedContext sc (scTcbUpdate fun _ => none) (fun y => ⟨rfl, rfl, rfl⟩) s.2 s1 r hr

theorem rd_schedContextUnbindAllTcbs_p (sc : ObjRef) (σ : State Unit) (h1 : T1 σ)
    (hA : ∀ y n t, σ.kheap sc = some (.schedContext y n) → y.scTcb = some t → t ≠ σ.curThread →
      σ.schedulerAction ≠ .switchThread t) :
    IKp Rdy σ (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_gets_bind ?_
  exact ikp_when _ fun _ => rd_schedContextUnbindTcb_p sc σ h1 hA

/-- **`maybe_return_sc`** (module docstring). -/
theorem rd_maybeReturnSc_p (nt t : ObjRef) (σ : State Unit) (hq : ∀ d p, t ∉ σ.readyQueues d p)
    (ha : σ.schedulerAction ≠ .switchThread t) (hr : t ∉ σ.releaseQueue) :
    IKp Rdy σ (maybeReturnSc (Z := Unit) nt t) := by
  unfold maybeReturnSc
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_when _ fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' ik_step0) hy) fun _ => ?_
  refine ikp_bind (rd_threadSet_unbind t σ hq ha hr) fun _ => ?_
  refine ik_bind (rd_updateSchedContext _ (scTcbUpdate fun _ => none) fun y => ⟨rfl, rfl, rfl⟩) fun _ => ?_
  refine ik_gets_bind fun s => ikp_of_ik ?_ s
  exact ik_when _ rd_rescheduleRequired

/-! ## `sched_context_set_inactive` -/

/-- One SC rewritten to an inactive one, no thread bound to it. -/
theorem rdy_freeSc {σ : State Unit} {p : ObjRef} {y z : SchedContext} {n : Nat} (h : Rdy σ)
    (hn : ∀ t x, σ.kheap t = some (.tcb x) → x.tcbSchedContext ≠ some p)
    (hk : σ.kheap p = some (.schedContext y n)) (hz : scActive z = false) (hI : p ≠ σ.idleSc) :
    Rdy (Sched.updSc σ p z n) := by
  have hkq : ∀ q, q ≠ p → (Sched.updSc σ p z n).kheap q = σ.kheap q := fun q hq => by simp [Notif.updK, hq]
  have hkp : (Sched.updSc σ p z n).kheap p = some (.schedContext z n) := kh_upd _ _ _ _
  have htp : ∀ {t x}, σ.kheap t = some (.tcb x) → t ≠ p := fun {t x} hx e => by
    subst e; rw [hk] at hx; cases hx
  have F : ∀ {t}, RdyT σ t → RdyT (Sched.updSc σ p z n) t := by
    intro t ⟨x, c, y0, m, hx, hc, hy0, h1, h2⟩
    have hcp : c ≠ p := fun e => hn t x hx (e ▸ hc)
    exact ⟨x, c, y0, m, by rw [hkq t (htp hx)]; exact hx, hc, by rw [hkq c hcp]; exact hy0, h1, h2⟩
  have G : ∀ {t}, ActB σ t → ActB (Sched.updSc σ p z n) t := by
    intro t ⟨x, c, y0, m, hx, hc, hy0, h1⟩
    have hcp : c ≠ p := fun e => hn t x hx (e ▸ hc)
    exact ⟨x, c, y0, m, by rw [hkq t (htp hx)]; exact hx, hc, by rw [hkq c hcp]; exact hy0, h1⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun d q t hm => F (h1 d q t hm), fun t e => F (h2 t e), fun t x c hx hb hc => ?_,
    fun q w m hw hw' => ?_, fun t hm => G (h5 t hm), fun w m hw => ?_⟩
  rotate_right
  · change (Sched.updSc σ p z n).kheap σ.idleSc = _ at hw
    rw [hkq _ (Ne.symm hI)] at hw; exact h6 w m hw
  · have e : t ≠ p := by rintro rfl; rw [hkp] at hx; cases hx
    rw [hkq t e] at hx; exact F (h3 t x c hx hb hc)
  · by_cases e : q = p
    · subst e; rw [hkp] at hw; cases hw; rw [hz] at hw'; cases hw'
    · rw [hkq q e] at hw; exact h4 q w m hw hw'

theorem updateSchedContext_none {σ : State Unit} {p : ObjRef} (hk : ∀ y n, σ.kheap p ≠ some (.schedContext y n))
    {f : SchedContext → SchedContext} {r : Unit × State Unit}
    (hr : r ∈ (updateSchedContext (Z := Unit) p f σ).1) : False := by
  unfold updateSchedContext at hr
  obtain ⟨y, hy, hr⟩ := hr
  obtain ⟨hk', hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk' hs; subst hs
  dsimp only at hr
  split at hr
  · rename_i sc m; exact hk sc m hk'
  · exact hr.elim

/-- **`sched_context_set_inactive`** of an SC no thread is bound to. -/
theorem rd_schedContextSetInactive_p (sc : ObjRef) (σ : State Unit)
    (hn : ∀ t x, σ.kheap t = some (.tcb x) → x.tcbSchedContext ≠ some sc) (hI : sc ≠ σ.idleSc) :
    IKp Rdy σ (schedContextSetInactive (Z := Unit) sc) := by
  intro hσ r hr
  unfold schedContextSetInactive at hr
  by_cases hk : ∃ y n, σ.kheap sc = some (.schedContext y n)
  · obtain ⟨y, n, hk⟩ := hk
    rw [Notif.nd_bind_one (Sched.updateSchedContext_eq hk _),
      Notif.nd_bind_one (Sched.updateSchedContext_eq (kh_upd _ _ _ _) _), Sched.updSc_updSc,
      Notif.nd_bind_one (Sched.updateSchedContext_eq (kh_upd _ _ _ _) _), Sched.updSc_updSc,
      Sched.updateSchedContext_eq (kh_upd _ _ _ _), Sched.updSc_updSc] at hr
    rw [Set.mem_singleton_iff.1 hr]
    exact rdy_freeSc hσ hn hk rfl hI
  · exfalso
    obtain ⟨z, hz, -⟩ := hr
    exact updateSchedContext_none (fun y n e => hk ⟨y, n, e⟩) hz

end

end Fl4Proofs.P3.SInvR
