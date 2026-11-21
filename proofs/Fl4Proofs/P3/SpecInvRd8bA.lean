/-
P3 (DESIGN.md §9), invariant line G1 (rd8b): **`Rdy` across the priority and
yield-to writers of the syscall body** (spec side only, outside the JAtZ cone;
KENTRY-PLAN rd7 handoff 2).

* `W σ0 s`: `s` is `SVS`-related to `σ0` (IpcSV: every TCB's SC binding, every
  SC's refills / refill max / bound TCB, the time, the action kept or
  `choose_new_thread`) and keeps rd7's `cfS` (consumed time, current SC and
  thread, idle thread / SC, time). `ikp_bind_w`: a step keeping `Rdy`, `SVS`
  and `cfS` carries `W` from a pinned start. `rdyT_w`: `RdyT` along `W`;
  `fwd_svs`: sb2's `ScFwd` along `SVS`.
* `CtRdy σ`: the current thread, when runnable, is `RdyT`. At a perform the
  current thread is `Restart` (runnable), bound to `cur_sc` (ctq5's
  `kentry_curScT`), active (rd7's `CAx`, ct ≠ idle), not released (ctq's `RB`
  resume clause) and `cur_sc`'s head is ready (`OffReady`): rd's `CtR`.
* **`rd_setPriority`**: FL4's `set_priority` re-enqueues the thread when it was
  queued (`R1`) or is the current thread (`CtRdy`; l4v re-enqueues only under
  `schedulable`, the spec enqueues the current thread unconditionally).
* **`rd_schedContextYieldTo`** (`ScFwd`, `RdyT` of the current thread):
  `sched_context_resume` postpones the SC's thread unless its head is ready
  (rd7's `sr_schedContextResume`, the thread bound back by `ScFwd`), so the
  `schedulable` guard gives `RdyT` (the spec drops l4v's
  `assert (sufficient ∧ ready)`); the second arm enqueues the current thread
  unconditionally (`RdyT` carried by `W`).
-/
import Fl4Proofs.P3.SpecInvRdL
open Classical

namespace Fl4Proofs.P3.SInvR.B8
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

/-! ## The carried relation -/

/-- `SVS` from `σ0` and the scalar fields kept. -/
def W (σ0 s : State Unit) : Prop := SVK.SVS σ0 s ∧ cfS s = cfS σ0

theorem W.refl (σ : State Unit) : W σ σ := ⟨SVK.SVS.refl σ, rfl⟩

theorem W.trans {σ1 σ2 σ3 : State Unit} (h1 : W σ1 σ2) (h2 : W σ2 σ3) : W σ1 σ3 :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

theorem W.ct {σ0 s : State Unit} (h : W σ0 s) : s.curThread = σ0.curThread := by
  have e := h.2; unfold cfS at e; simp only [Prod.mk.injEq] at e; exact e.2.2.1

/-- A step keeping `Rdy`, `SVS` and `cfS`, from a pinned start `W`-related to `σ0`. -/
theorem ikp_bind_w {α β : Type} {σ0 σ : State Unit} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : RdK m) (hs : SVK.SVM m) (hc : CFK m) (h0 : W σ0 σ)
    (hg : ∀ a s, W σ0 s → IKp Rdy s (g a)) : IKp Rdy σ (m >>= g) := by
  intro hσ x ⟨y, hy, hx⟩
  exact hg y.1 y.2 (h0.trans ⟨hs σ y hy, hc σ y hy⟩) (hm σ hσ y hy) x hx

theorem rdyT_w {σ0 s : State Unit} {t : ObjRef} (h : RdyT σ0 t) (hw : W σ0 s) : RdyT s t := rdyT_svs h hw.1

/-- The current thread's `RdyT` along `W`. -/
theorem rdyT_ct_w {σ0 s : State Unit} (h : RdyT σ0 σ0.curThread) (hw : W σ0 s) : RdyT s s.curThread := by
  rw [hw.ct]; exact rdyT_w h hw

/-- sb2's `ScFwd` along `SVS` (it reads only bindings and bound TCBs). -/
theorem fwd_svs {σ σ' : State Unit} (h : SInvB.ScFwd σ) (hS : SVK.SVS σ σ') : SInvB.ScFwd σ' := by
  intro p y n u hy hu
  have e := hS.1 p; rw [hy] at e
  obtain ⟨y0, hy0, -, -, ht⟩ := SVK.sv_sc (o := σ.kheap p) e.symm
  obtain ⟨x, hx, hb⟩ := h p y0 n u hy0 (ht.trans hu)
  have e2 := hS.1 u; rw [hx] at e2
  obtain ⟨x', hx', hxs⟩ := SVK.sv_tcb (o := σ'.kheap u) e2
  exact ⟨x', hx', hxs.trans hb⟩

/-- An SC's bound TCB read back along `SVS`. -/
theorem scTcb_svs {σ σ' : State Unit} (hS : SVK.SVS σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hy : σ'.kheap p = some (.schedContext y n)) :
    ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧ y0.scTcb = y.scTcb := by
  have e := hS.1 p; rw [hy] at e
  obtain ⟨y0, hy0, -, -, ht⟩ := SVK.sv_sc (o := σ.kheap p) e.symm
  exact ⟨y0, hy0, ht⟩

/-! ## Two `SVM` leaves -/

theorem sv_completeYieldTo' (t : ObjRef) : SVK.SVM (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo setConsumed replyFromKernel schedContextCancelYieldTo; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_completeYieldTo' _)

theorem sv_schedContextResume' (p : ObjRef) : SVK.SVM (schedContextResume (Z := Unit) p) := by
  unfold schedContextResume postpone tcbReleaseEnqueue readyTimesAppend orderedInsert; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_schedContextResume' _)

/-! ## `set_priority` -/

/-- The current thread, when runnable, is `RdyT`. -/
def CtRdy (σ : State Unit) : Prop :=
  ∀ x, σ.kheap σ.curThread = some (.tcb x) → runnable x.tcbState = true → RdyT σ σ.curThread

theorem mem_getTcbQueue {d : Domain} {p : Priority} {σ : State Unit} {y : ReadyQueue × State Unit}
    (h : y ∈ (getTcbQueue (Z := Unit) d p σ).1) : y = (σ.readyQueues d p, σ) := by
  unfold getTcbQueue at h
  obtain ⟨z, hz, h⟩ := h
  obtain rfl := Set.mem_singleton_iff.1 hz
  exact Set.mem_singleton_iff.1 h

/-- **`set_priority t prio`** keeps `Rdy` when the current thread, if runnable, is `RdyT`. -/
theorem rd_setPriority (t : ObjRef) (prio : Priority) (σ : State Unit) (hC : CtRdy σ) :
    IKp Rdy σ (setPriority (Z := Unit) t prio) := by
  unfold setPriority getThreadState threadSetPriority
  refine SInvQ.ikp_threadGet_bind fun x hx => ?_
  try dsimp only
  split
  · rename_i hrun
    intro hσ y hy
    obtain ⟨z1, hz1, hy⟩ := hy
    obtain ⟨x1, -, rfl⟩ := SInvQ.q1_mem_threadGet hz1
    obtain ⟨z2, hz2, hy⟩ := hy
    obtain ⟨x2, -, rfl⟩ := SInvQ.q1_mem_threadGet hz2
    obtain ⟨z3, hz3, hy⟩ := hy
    obtain rfl := mem_getTcbQueue hz3
    obtain ⟨z4, hz4, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hz4
    dsimp only at hy
    split at hy
    · rename_i hin
      have hT : RdyT σ t := by
        rcases hin with hq | e
        · exact hσ.1 _ _ t hq
        · subst e; exact hC x hx hrun
      obtain ⟨w1, hw1, hy⟩ := hy
      have hR1 := rd_dequeue t σ hσ w1 hw1
      have hS1 := SVK.sv_tcbSchedAction' _ t σ w1 hw1
      obtain ⟨w2, hw2, hy⟩ := hy
      have hR2 := rd_threadSet (fun tcb : Tcb => { tcb with tcbPriority := prio }) t (fun _ => ⟨rfl, rfl, rfl⟩) w1.2 hR1 w2 hw2
      have hS2 := SVK.sv_threadSet' (fun tcb : Tcb => { tcb with tcbPriority := prio }) (fun _ => rfl) t w1.2 w2 hw2
      obtain ⟨w3, hw3, hy⟩ := hy
      have hT3 : RdyT w2.2 t := rdyT_svs hT (hS1.trans hS2)
      have hR3 := rd_tsa_p _ t w2.2 (fun q u hu => (SInvQ.q1_enq t q u hu).imp id fun e => ⟨e, hT3⟩) hR2 w3 hw3
      exact rd_rescheduleRequired w3.2 hR3 y hy
    · exact rd_threadSet (fun tcb : Tcb => { tcb with tcbPriority := prio }) t (fun _ => ⟨rfl, rfl, rfl⟩) σ hσ y hy
  · intro hσ y hy
    obtain ⟨w1, hw1, hy⟩ := hy
    have hR1 := rd_threadSet (fun tcb : Tcb => { tcb with tcbPriority := prio }) t (fun _ => ⟨rfl, rfl, rfl⟩) σ hσ w1 hw1
    obtain ⟨w2, hw2, hy⟩ := hy
    have hR2 := ik_maybeM (fun ep => rd_reorderEp ep t) _ w1.2 hR1 w2 hw2
    exact ik_maybeM (fun n => rd_reorderNtfn n t) _ w2.2 hR2 y hy

/-! ## `sched_context_yield_to` -/

/-- **`sched_context_yield_to p`** keeps `Rdy` (sb2's `ScFwd`, the current thread `RdyT`). -/
theorem rd_schedContextYieldTo (p : ObjRef) (σ : State Unit) (hF : SInvB.ScFwd σ)
    (hct : RdyT σ σ.curThread) : IKp Rdy σ (schedContextYieldTo (Z := Unit) p) := by
  unfold schedContextYieldTo
  refine ikp_bind_w (σ0 := σ) (by rd_auto) (by sv_auto) (by cfk_auto) (W.refl σ) fun _ s1 w1 => ?_
  refine ikp_bind_w (σ0 := σ) (by rd_auto)
    (by sv_auto) (by cfk_auto) w1 fun _ s2 w2 => ?_
  intro hs2 y hy
  obtain ⟨r, hr, hy⟩ := hy
  have hRr : Rdy r.2 := rd_schedContextResume p s2 hs2 r hr
  have hwr : W σ r.2 := w2.trans ⟨sv_schedContextResume' p s2 r hr, cfk_schedContextResume' p s2 r hr⟩
  obtain ⟨z, hz, hy⟩ := hy
  have hRz : Rdy z.2 := by
    obtain ⟨a1, ha1, hz⟩ := hz
    obtain ⟨ea1, sc', n', hk', hv'⟩ := SInvQ.cq5_mem_getScObjRef ha1
    obtain ⟨tt, a1s⟩ := a1
    simp only at ea1 hv'; subst a1s
    obtain ⟨a2, ha2, hz⟩ := hz
    obtain ⟨ha2e, ha2s⟩ := SInvQ.cq5_mem_assertOpt ha2
    obtain ⟨t, a2s⟩ := a2
    simp only at ha2e ha2s; subst a2s; subst ha2e
    -- the SC's thread, when schedulable, is released
    have hS2r : SVK.SVS s2 r.2 := sv_schedContextResume' p s2 r hr
    obtain ⟨y0, hy0, hyt⟩ := scTcb_svs hS2r hk'
    have hp : ∀ y n, s2.kheap p = some (.schedContext y n) → y.scTcb = some t := by
      intro y n hy; rw [hy0] at hy; cases hy; rw [hyt, hv']
    have hb : ∀ x, s2.kheap t = some (.tcb x) → x.tcbSchedContext = some p := by
      intro x hx
      obtain ⟨x', hx', hb'⟩ := fwd_svs hF w2.1 p y0 n' t hy0 (by rw [hyt, hv'])
      rw [hx] at hx'; cases hx'; exact hb'
    have hSR : SR t r.2 := sr_schedContextResume p t s2 hp hb hr
    obtain ⟨a3, ha3, hz⟩ := hz
    obtain rfl := Set.mem_singleton_iff.1 ha3
    dsimp only at hz
    split at hz
    · rename_i hsch
      have hTt : RdyT r.2 t := hSR hsch
      have hTc : RdyT r.2 r.2.curThread := rdyT_ct_w hct hwr
      obtain ⟨b1, hb1, hz⟩ := hz
      obtain rfl := Set.mem_singleton_iff.1 hb1
      obtain ⟨b2, hb2, hz⟩ := hz
      obtain ⟨_, -, rfl⟩ := SInvQ.q1_mem_threadGet hb2
      obtain ⟨b3, hb3, hz⟩ := hz
      obtain ⟨_, -, rfl⟩ := SInvQ.q1_mem_threadGet hb3
      dsimp only at hz
      split at hz
      · obtain ⟨c1, hc1, hz⟩ := hz
        have hR1 := rd_dequeue t r.2 hRr c1 hc1
        have hS1 := SVK.sv_tcbSchedAction' _ t r.2 c1 hc1
        obtain ⟨c2, hc2, hz⟩ := hz
        have hR2 := rd_tsa_p _ t c1.2
          (fun q u hu => (SInvQ.q1_enq t q u hu).imp id fun e => ⟨e, rdyT_svs hTt hS1⟩) hR1 c2 hc2
        obtain rfl := Set.mem_singleton_iff.1 hz
        exact hR2
      · obtain ⟨c1, hc1, hz⟩ := hz
        have hR1 := rd_threadSet (tcbYieldToUpdate fun _ => some p) r.2.curThread (fun _ => ⟨rfl, rfl, rfl⟩) r.2 hRr c1 hc1
        have hS1 := SVK.sv_threadSet' (tcbYieldToUpdate fun _ => some p) (fun _ => rfl) r.2.curThread r.2 c1 hc1
        obtain ⟨c2, hc2, hz⟩ := hz
        have hR2 := rd_updateSchedContext p (scYieldFromUpdate fun _ => some r.2.curThread) (fun _ => ⟨rfl, rfl, rfl⟩) c1.2 hR1 c2 hc2
        have hS2 := SVK.sv_updateSchedContext p (scYieldFromUpdate fun _ => some r.2.curThread) (fun _ => ⟨rfl, rfl, rfl⟩) c1.2 c2 hc2
        obtain ⟨c3, hc3, hz⟩ := hz
        have hR3 := rd_dequeue t c2.2 hR2 c3 hc3
        have hS3 := SVK.sv_tcbSchedAction' _ t c2.2 c3 hc3
        have hS13 : SVK.SVS r.2 c3.2 := (hS1.trans hS2).trans hS3
        obtain ⟨c4, hc4, hz⟩ := hz
        have hR4 := rd_tsa_p _ _ c3.2
          (fun q u hu => (SInvQ.q1_enq _ q u hu).imp id fun e => ⟨e, rdyT_svs hTc hS13⟩) hR3 c4 hc4
        have hS4 := SVK.sv_tcbSchedAction' _ _ c3.2 c4 hc4
        obtain ⟨c5, hc5, hz⟩ := hz
        have hR5 := rd_tsa_p _ t c4.2
          (fun q u hu => (SInvQ.q1_enq t q u hu).imp id fun e => ⟨e, rdyT_svs hTt (hS13.trans hS4)⟩) hR4 c5 hc5
        obtain ⟨c6, hc6, hz⟩ := hz
        have hR6 := rd_rescheduleRequired c5.2 hR5 c6 hc6
        obtain rfl := Set.mem_singleton_iff.1 hz
        exact hR6
    · obtain rfl := Set.mem_singleton_iff.1 hz
      exact hRr
  dsimp only at hy
  split at hy
  · exact rd_returnConsumed p z.2 hRz y hy
  · obtain rfl := Set.mem_singleton_iff.1 hy
    exact hRz

end

end Fl4Proofs.P3.SInvR.B8
