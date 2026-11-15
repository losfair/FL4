/-
P1: `restart` (sched.rs; seL4 `restart`, MCS) keeps the queue invariant,
`BoundInv` and `XInv`.

`cancel_ipc` and the `Restart` state are `KeepT` steps, which keep the
thread's SC words (its `TCB`/`CORE` words and ring header), so the SC is
still well formed for `refill_unblock_check`, whose writes stay in the
ring and the current core's `REPROGRAM`; `schedcontext::resume` may
`postpone` the SC's thread (by `ScExtra`, the thread itself); a schedulable
thread then goes through `possible_switch_to`.
-/
import Fl4Proofs.P1.QueueSuspend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {A : Type _} {ar : machine.Arch A}

theorem ts_restart : sched.TS_RESTART = 2#u64 := ts_vals.2.1

theorem runnable_restart : Runnable sched.TS_RESTART := Or.inr (Or.inl rfl)
theorem not_blocked_restart : ¬ Blocked sched.TS_RESTART := by
  obtain ⟨-, -, h3, h4, h6⟩ := ts_vals
  unfold Blocked; rw [h3, h4, h6, ts_restart]; decide

theorem sporadic.sufficient.ok (hA : P0.ArchTotal ar) (s : S) (a : A) (sc : obj.Sc) (u : U64) :
    sporadic.sufficient st ar s a sc u ⦃ _ => True ⦄ := by
  unfold sporadic.sufficient sporadic.capacity
  step with sporadic.head.spec as ⟨r⟩
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun _ _ => ?_
  · split
    · simp
    · step*
  · step with sporadic.min_budget.ok hA as ⟨m⟩

theorem sporadic.sc_sporadic.spec (s : S) (sc : obj.Sc) :
    sporadic.sc_sporadic st s sc ⦃ b => b = true → sc ≠ 0#u64 ∧ L.mem s (sporA sc) ≠ 0#u64 ⦄ := by
  unfold sporadic.sc_sporadic
  step with obj.Sc.is_null.spec as ⟨b, b_post⟩
  split
  · simp
  · rename_i hb
    unfold obj.Sc.sporadic
    simp only [lift, bind_ok, L.read_eq, WP.spec_ok]
    intro e; exact ⟨by simpa [b_post] using hb, by simpa [sporA] using e⟩

theorem sched.is_stopped.spec (s : S) (t : obj.Tcb) :
    sched.is_stopped st s t ⦃ b => b = true → ¬ Runnable (L.mem s (stA t)) ⦄ := by
  have nb : ∀ v : U64, (v = sched.TS_BLOCKED_ON_RECV ∨ v = sched.TS_BLOCKED_ON_SEND ∨ v = sched.TS_BLOCKED_ON_NTFN ∨
      v = sched.TS_BLOCKED_ON_REPLY) → ¬ Runnable v := by
    obtain ⟨h1, h2, h3, h4, h6⟩ := ts_vals
    intro v hv hr
    unfold Runnable at hr
    rw [h1, h2] at hr; rw [h3, h4, h6, ts_reply] at hv
    rcases hr with rfl | rfl | rfl <;> rcases hv with e | e | e | e <;> simp [sched.TS_RUNNING_VM] at e
  unfold sched.is_stopped
  step with obj.Tcb.state.spec as ⟨v, v_post⟩
  split
  · rename_i e; simp only [WP.spec_ok]; intro _
    rw [← v_post, e]; exact not_runnable_inactive
  · unfold sched.is_blocked
    step with obj.Tcb.state.spec as ⟨w, w_post⟩
    rw [← v_post] at w_post
    subst w_post
    split
    · rename_i e; simp only [WP.spec_ok]; intro _; rw [← v_post]; exact nb _ (Or.inl e)
    split
    · rename_i _ e; simp only [WP.spec_ok]; intro _; rw [← v_post]; exact nb _ (Or.inr (Or.inl e))
    split
    · rename_i _ _ e; simp only [WP.spec_ok]; intro _; rw [← v_post]; exact nb _ (Or.inr (Or.inr (Or.inl e)))
    · simp only [WP.spec_ok]; intro e; rw [← v_post]; exact nb _ (Or.inr (Or.inr (Or.inr (by simpa using e))))


/-! ## `postpone` and `resume` -/

/-- `postpone`, with `BoundInv` and `XInv`: the SC's thread is bound. -/
theorem sched.postpone.all (s : S) (sc : obj.Sc) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : L.mem s (scTcbA sc) ∈ T)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hr0 : (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_RELEASE) = 0#u64)
    (hcore : OutsideObjs st T Cs s (scCoreA sc)) (hcs : L.mem s (scCoreA sc) ∈ Cs)
    (hrun : Runnable (L.mem s (stA (L.mem s (scTcbA sc))))) (hna : L.actionW s ≠ L.mem s (scTcbA sc))
    (hbd : L.mem s (scA (L.mem s (scTcbA sc))) ≠ 0#u64) (hba : L.mem s (scA (L.mem s (scTcbA sc))) ∈ Ac) :
    sched.postpone st s sc ⦃ s' => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SgOK st Ω Sg s' ∧ Fr st T Sg s s' ∧
      L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ⦄ := by
  unfold sched.postpone
  step as ⟨t, t_post⟩
  subst t_post
  set t := L.mem s (scTcbA sc) with ht_def
  have hT := h.tcbs
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hR1 := h.ready _ hc
  have hmemq := (h.queued t ht).1
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) hmemq)) ?_
  rintro s1 ⟨h1, hw1, hinq1⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  obtain ⟨hB1, hX1, fr1, ea1, ec1, -⟩ := bx_qfoot h hB hX hSg hW1 hc ht p128 hw1
    (fun hf => by rw [hinq1] at hf; split_ifs at hf with e
                  · rw [andn_qq_qq] at hf; exact absurd rfl hf
                  · exact Or.inl hf)
    (fun hf => by rw [hinq1] at hf; split_ifs at hf with e
                  · rw [andn_qq_qr] at hf; exact Or.inr (Or.inl hf)
                  · exact Or.inr (Or.inl hf))
  have hSg1 := hSg.fr fr1
  have core1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) :=
    hw1.mem_eq hcore.1 (qfoot_out hT hW1 hN hN' ht hc h.cur hcore)
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hcn
    exact notQ_after_dequeue h ht _ (h1.aff t ht) _ (h1.prio t ht) ((h1.queued t ht).1 hcn)
  have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact h.notR ht hr0 (h1.aff t ht) ((h1.released t ht).1 hcn)
  have hT1 := h1.tcbs
  have hc1 := h1.aff t ht
  have hN1 := h1.nodes _ hc1
  have hN1' := h1.nodes _ h1.cur
  obtain ⟨hsb1, -, -⟩ := ext_qfoot hT hW1 hN hN' ht hc h.cur hw1
  refine WP.spec_bind (WP.spec_and (sched.release_enqueue.inv s1 t _ R h1 ht hq1 hr1
      (by rw [(hsb1 t ht).1]; exact hrun) (by rw [ea1]; exact hna))
    (sched.release_enqueue.foot s1 t _ hT1 ht (h1.notR ht hr1 hc1) hN1 hN1' (h1.release _ hc1))) ?_
  rintro s2 ⟨h2, hw2, hinq2⟩
  have hW2 : ∀ w ∈ t :: R (L.mem s1 (affA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h1.memTR hc1 hw
  obtain ⟨hB2, hX2, fr2, ea2, ec2, -⟩ := bx_qfoot h1 hB1 hX1 hSg1 hW2 hc1 ht prel hw2
    (fun hf => by rw [hinq2, or_qr_qq] at hf; exact Or.inl hf)
    (fun _ => Or.inr (Or.inr ⟨by rw [fr1.sc t ht]; exact hbd, by rw [fr1.sc t ht]; exact hba⟩))
  have hSg2 := hSg1.fr fr2
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hw2.mem_eq hcore.1 (qfoot_out hT1 hW2 hN1 hN1' ht hc1 h1.cur (hcore.ksb hw1.1))).trans core1
  step as ⟨cpu, cpu_post⟩
  rw [core2] at cpu_post
  subst cpu_post
  step as ⟨s3, s3_post⟩
  subst s3_post
  have hN2 := h2.nodes _ hcs
  have hN2' := h2.nodes _ h2.cur
  have e : L.actionW (L.wr s2 (L.nodeAt s2 (L.mem s (scCoreA sc)) layout.node.REPROGRAM) 1#u64) = L.actionW s2 := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    by_cases hcc : L.mem s (scCoreA sc) = L.cpu s2
    · rw [hcc, rd_node_wr_node hN2' (by rw [repr_val]; omega) (by rw [act_val]; omega) (by rw [repr_val])
        (by rw [act_val]), if_neg (by rw [repr_val, act_val]; omega)]
    · exact rd_node_wr_node_cpu hN2' hN2 (by rw [repr_val]; omega) (by rw [act_val]; omega) (by rw [repr_val])
        (by rw [act_val]) hcc
  have o0 := nodeword_other (v := 1#u64) h2 hcs h2.cur (o := layout.node.REPROGRAM) (o' := layout.node.CUR_THREAD)
    (by rw [repr_val]; omega) (by rw [repr_val]) (by rw [curth0]; omega) (by rw [curth0])
    (fun _ => by rw [repr_val, curth0]; omega)
  have o8 := nodeword_other (v := 1#u64) h2 hcs h2.cur (o := layout.node.REPROGRAM) (o' := layout.node.IDLE_THREAD)
    (by rw [repr_val]; omega) (by rw [repr_val]) (by rw [idle8]; omega) (by rw [idle8])
    (fun _ => by rw [repr_val, idle8]; omega)
  obtain ⟨hB3, hX3⟩ := bx_wr (v := 1#u64) h2 hB2 hX2 (nodeAt_aligned hN2 (by rw [repr_val]; omega) (by rw [repr_val]))
    (not_prot_node h2 hX2.1 hSg2.sub hcs (by rw [repr_val]; omega))
    (fun y hy => ⟨fun e' => node_ne_field hN2 (by rw [repr_val]; omega) hy (h2.tcbs y hy) (K := 3464#u64)
        (by decide) (by rw [scA_eq] at e'; exact UScalar.eq_of_val_eq e'),
      fun e' => node_ne_field hN2 (by rw [repr_val]; omega) hy (h2.tcbs y hy) (K := 3592#u64)
        (by decide) (by rw [inqA_eq] at e'; exact UScalar.eq_of_val_eq e')⟩)
    (fun o ho e' => by
      by_cases hcc : L.mem s (scCoreA sc) = L.cpu s2
      · rw [hcc, nodeAt_val hN2' (by rw [repr_val]; omega), nodeAt_val hN2' (by omega), repr_val] at e'; omega
      · exact nodeAt_ne_cpu hN2 hN2' (by rw [repr_val]; omega) (by omega) hcc (UScalar.eq_of_val_eq e'))
    (hX2.tn_node h2 hSg2.sub hcs (by rw [repr_val]; omega) (by rw [repr_val]) (by rw [repr_val]; omega))
  exact ⟨_, _, inv_wr_node_low h2 hcs (by rw [repr_val]; omega) (by rw [repr_val]; omega) (by rw [repr_val])
    (by rw [e]; exact h2.action) (by rw [e]; exact h2.actOK) (by rw [o0]; exact h2.curT) (by rw [o8]; exact h2.idleT),
    hB3, hX3, ⟨hSg2.sub, fun b hb => by rw [L.ksb_wr]; exact hSg2.ks b hb,
      fun o h1' h2' => by rw [L.ksb_wr]; exact hSg2.ksΩ o h1' h2'⟩,
    fr1.trans (fr2.trans (fr_node (hi8 := fun _ => by simp [layout.node.SCHED_ACTION, layout.node.REPROGRAM, layout.node.CUR_THREAD]) h2 hSg2 hcs (by rw [repr_val]; omega) (by rw [repr_val])
      (fun _ => by rw [repr_val]; omega) ⟨by rw [repr_val]; omega, by rw [repr_val]; omega⟩)),
    e.trans (ea2.trans ea1), by
      have := ec2.trans ec1
      unfold LawfulStore.curW at this ⊢
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      rw [o0]; exact this⟩

/-- seL4 `schedContext_resume`, with `BoundInv` and `XInv`. -/
theorem schedcontext.resume.all (hA : P0.ArchTotal ar) (s : S) (a : A) (sc : obj.Sc)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hsc : sc ≠ 0#u64 → L.mem s (scTcbA sc) ≠ 0#u64 →
      L.mem s (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s (scCoreA sc) ∧ L.mem s (scCoreA sc) ∈ Cs ∧
        L.actionW s ≠ L.mem s (scTcbA sc)) :
    schedcontext.resume st ar s a sc ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ∧
      BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SgOK st Ω Sg s' ∧ Fr st T Sg s s' ⦄ := by
  unfold schedcontext.resume
  step with obj.Sc.is_null.spec as ⟨b, b_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h, hB, hX, hSg, Fr.refl _ _⟩
  rename_i hb
  have hsc0 : sc ≠ 0#u64 := by simpa [b_post] using hb
  step with obj.Sc.tcb.spec as ⟨i, i_post⟩
  step with obj.Tcb.is_null.spec as ⟨b1, b1_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h, hB, hX, hSg, Fr.refl _ _⟩
  rename_i hb1
  have hi0 : L.mem s (scTcbA sc) ≠ 0#u64 := by rw [← i_post]; simpa [b1_post] using hb1
  obtain ⟨hiT, hcore, hcs, hna⟩ := hsc hsc0 hi0
  step with sched.is_schedulable.spec' as ⟨b2, b2_post⟩
  split
  · rename_i hb2
    obtain ⟨hrun, hbd, hr0, hmx⟩ := b2_post hb2
    rw [i_post] at hrun hr0 hbd hmx
    have hba : L.mem s (scA (L.mem s (scTcbA sc))) ∈ Ac :=
      (hS.act _ (hX.2.2.bound _ hiT hbd).1).2 hmx
    have post := sched.postpone.all s sc Q R h hiT hB hX hSg hr0 hcore hcs hrun hna hbd hba
    step with sporadic.ready.spec as ⟨b3⟩
    split
    · step with sporadic.sufficient.ok (st := st) hA as ⟨b4⟩
      split
      · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h, hB, hX, hSg, Fr.refl _ _⟩
      · exact WP.spec_bind post fun s1 h1 => by
          obtain ⟨Q', R', a1, a2, a3, a4, a5, -, -⟩ := h1
          have h1' : ∃ Q' R', SchedQueuesInv st T Cs Ω H s1 Q' R' ∧ BoundInv st T Ac s1 ∧
              XInv st T Cs Ω Sg Rp Scs Nt Z s1 ∧ SgOK st Ω Sg s1 ∧ Fr st T Sg s s1 := ⟨Q', R', a1, a2, a3, a4, a5⟩
          simpa using h1'
    · exact WP.spec_bind post fun s1 h1 => by
        obtain ⟨Q', R', a1, a2, a3, a4, a5, -, -⟩ := h1
        have h1' : ∃ Q' R', SchedQueuesInv st T Cs Ω H s1 Q' R' ∧ BoundInv st T Ac s1 ∧
            XInv st T Cs Ω Sg Rp Scs Nt Z s1 ∧ SgOK st Ω Sg s1 ∧ Fr st T Sg s s1 := ⟨Q', R', a1, a2, a3, a4, a5⟩
        simpa using h1'
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h, hB, hX, hSg, Fr.refl _ _⟩

/-! ## `restart` -/

/-- seL4 `restart` (MCS) keeps the queue invariant, `BoundInv` and `XInv`. -/
theorem sched.restart.all (hA : P0.ArchTotal ar) (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) :
    sched.restart st ar s a t ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ TmFr st T Cs Nt s s' ⦄ := by
  have hSg := hS.sg
  have hsub := hSg.sub
  have hT := h.tcbs
  unfold sched.restart
  step with sched.is_stopped.spec as ⟨b, b_post⟩
  split
  swap
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h, hB, hX, hS, TmFr.refl (L := L) _⟩
  rename_i hb
  have hnr : ¬ Runnable (L.mem s (stA t)) := b_post hb
  have hna : L.actionW s ≠ t := fun e => hnr (by have := (h.actOK (e ▸ ht)).1; rwa [e] at this)
  refine WP.spec_bind (ipc.cancel_ipc.all s a t Q R h ht hB hX hsub) ?_
  rintro ⟨s1, a1⟩ ⟨h1, hB1, hX1, nb1, nr1, hst1, k1, -⟩
  try simp only [WP.uncurry'_pair]
  have na1 : L.actionW s1 ≠ t := by
    rcases hst1 with e | ⟨-, e⟩
    · intro ea
      have := (h1.actOK (ea ▸ ht)).1; rw [ea, e] at this; exact not_runnable_inactive this
    · rw [e]; exact hna
  -- the `Restart` state
  refine WP.spec_bind (WP.spec_and (sched.set_thread_state.inv s1 t _ Q R h1 ht not_blocked_restart (Or.inr nb1)
    ⟨fun _ _ _ _ _ => runnable_restart, fun _ _ _ => runnable_restart, fun _ => runnable_restart⟩)
    (sched.set_thread_state.state s1 t _ Q R h1 ht hX1.1 hsub)) ?_
  rintro s2 ⟨h2', e2, k2⟩
  have h2 : SchedQueuesInv st T Cs Ω H s2 Q R := h2'.congrX empty_congr
  have nrr : sched.TS_RESTART ≠ sched.TS_BLOCKED_ON_REPLY ∧ sched.TS_RESTART ≠ sched.TS_BLOCKED_ON_RECV := by
    obtain ⟨-, -, h3', -⟩ := ts_vals
    rw [ts_restart, ts_reply, h3']; decide
  have hB2 := hB1.keepT h1 k2 (by rw [e2]; exact not_blocked_restart) (by rw [e2]; exact nrr.1)
  have hX2 := hX1.keepT k2 (by rw [e2]; exact nrr)
    (fun r hr e => absurd e (hX1.noref (h1.tcbs t ht) nr1 (fun e' => nb1 (Or.inr (Or.inl e'))) r hr))
  have hS2 : SCsOK st T Ω Sg Scs Z Ac s2 := (hS.keepT hX k1).keepT hX1 k2
  have k12 := k1.trans k2
  have tm2 : TmFr st T Cs Nt s s2 := TmFr.of_keepT k12
  have hSg2 : SgOK st Ω Sg s2 := ⟨hsub, fun b hb => by rw [k12.ksb]; exact hSg.ks b hb,
    fun o h1' h2'' => by rw [k12.ksb]; exact hSg.ksΩ o h1' h2''⟩
  have na2 : L.actionW s2 ≠ t := by
    rcases k2.act with e | e
    · rw [e]; exact na1
    · rw [e]; intro e'; exact notT_small hT (by simp) (e' ▸ ht)
  have sc2 : L.mem s2 (scA t) = L.mem s (scA t) := k12.scf ht
  -- the SC: unblock check
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  refine WP.spec_bind (Pₘ := fun s3 => SchedQueuesInv st T Cs Ω H s3 Q R ∧ BoundInv st T Ac s3 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s3 ∧ SgOK st Ω Sg s3 ∧ L.actionW s3 ≠ t ∧ L.mem s3 (scA t) = i ∧
      SCsOK st T Ω Sg Scs Z Ac s3 ∧ TmFr st T Cs Nt s2 s3) ?_ ?_
  · split
    · rename_i hb1
      obtain ⟨hi0, hsp⟩ := b1_post hb1
      have hbt : L.mem s2 (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
      obtain ⟨hiS, -, -⟩ := hX2.2.2.bound t ht hbt
      rw [← i_post] at hiS
      -- a sporadic SC is active, so well formed
      have hW2 : RefillsWF st s2 i (Z i) := hS2.wf hiS (hS2.spor i hiS hsp)
      have hSCin : SCin st s2 Ω i (Z i) := ⟨hW2, hX2.1.scW i hiS⟩
      step with sched.cur_sc.spec as ⟨c4, _⟩
      step with sc_ne.spec as ⟨b2⟩
      split
      · have hN' := h2.nodes _ h2.cur
        have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
        have aR : Aligned (L.nodeA s2 layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
        have oR : Outside (L.nodeA s2 layout.node.REPROGRAM) i (Z i) :=
          hSCin.node_out h2.omega h2.cur hN' (by rw [rp]; omega) (by rw [rp])
        refine WP.spec_mono (WP.spec_and (sporadic.unblock_check.fr hW2 ⟨aR, oR⟩)
          (sporadic.unblock_check.wf hW2 ⟨aR, oR⟩)) fun s3 hw3 => ?_
        have w3 := hw3.1
        have hS3 := SCsOK.ring h2 hS2 hX2 hiS w3 hw3.2
        have wF : WritesIn st s2 s3 (L.Free s2 Ω Cs) := w3.mono' fun b hb hh => by
          rcases hh with hh | hh
          · exact Or.inl (hX2.1.scW i hiS b hb hh.inSC)
          · exact hh ▸ free_cur_node h2.cur (by simp [rp, LowFree])
        have h3 := inv_of_free h2 wF
        have hB3 := hB2.free h2 wF
        have nP : ∀ b, (InRing i (Z i) b ∨ b = L.nodeA s2 layout.node.REPROGRAM) → Aligned b →
            ¬ Prot T Rp Scs Nt b := fun b hh hb => by
          rcases hh with hh | hh
          · exact not_prot_ring h2 hX2.1 hiS hb (Or.inl hh)
          · exact hh ▸ not_prot_node h2 hX2.1 hsub h2.cur (by rw [rp]; omega)
        have kn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 →
            L.mem s3 (L.nodeA s2 o) = L.mem s2 (L.nodeA s2 o) := fun o ho h8 h56 => by
          refine w3.mem_eq (nodeAt_aligned hN' ho h8) ?_
          rintro (hh | hh)
          · have hm := hX2.1.scW i hiS _ (nodeAt_aligned hN' ho h8) hh.inSC
            exact out_ne_node (h2.omega _ hm) h2.cur hN' ho rfl
          · have := congrArg UScalar.val hh
            simp only [LawfulStore.nodeA] at this
            rw [nodeAt_val hN' ho, nodeAt_val hN' (by rw [rp]; omega), rp] at this; omega
        have hX3 : XInv st T Cs Ω Sg Rp Scs Nt Z s3 := hX2.writes hT
          (w3.mono' fun b hb hh => fun hp => nP b hh hb hp) (fun b hb => hb) (by
            unfold LawfulStore.cscW; rw [cscW_eq w3.1 w3.2.1, kn _ (by simp [layout.node.CUR_SC])
              (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]; exact hX2.2.2.cur)
            (hX2.tn (TmFr.of_ring h2 hX2 hsub hiS w3)) (by
              unfold LawfulStore.idleW; rw [w3.2.1, nodeAt_of_ksb w3.1]
              exact kn _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega))
        refine ⟨h3, hB3, hX3, ⟨hsub, fun b hb => by rw [w3.1]; exact hSg2.ks b hb,
          fun o h1' h2'' => by rw [w3.1]; exact hSg2.ksΩ o h1' h2''⟩, ?_⟩
        unfold LawfulStore.actionW
        rw [w3.2.1, nodeAt_of_ksb w3.1]
        rw [show L.mem s3 (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) =
            L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) from
          kn _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)]
        refine ⟨na2, ?_, hS3, TmFr.of_ring h2 hX2 hsub hiS w3⟩
        rw [w3.mem_eq (scA_aligned (hT t ht)) ?_, i_post]
        rintro (hh | hh)
        · have hm := hX2.1.scW i hiS _ (scA_aligned (hT t ht)) hh.inSC
          rw [scA_eq] at hm
          exact out_ne_field (h2.omega _ hm) ht (hT t ht) (by simp) rfl
        · rw [scA_eq] at hh
          exact node_ne_field hN' (by rw [rp]; omega) ht (hT t ht) (by simp) hh.symm
      · exact (WP.spec_ok _).2 ⟨h2, hB2, hX2, hSg2, na2, i_post.symm, hS2, TmFr.refl (L := L) _⟩
    · exact (WP.spec_ok _).2 ⟨h2, hB2, hX2, hSg2, na2, i_post.symm, hS2, TmFr.refl (L := L) _⟩
  rintro s3 ⟨h3, hB3, hX3, hSg3, na3, sc3, hS3, tm3⟩
  -- `resume`
  refine WP.spec_bind (schedcontext.resume.all hA s3 a1 i Q R h3 hB3 hX3 hSg3 hS3 fun hi0 _ => ?_) ?_
  · obtain ⟨hiS, hti, hci⟩ := hX3.2.2.bound t ht (by rw [sc3]; exact hi0)
    rw [sc3] at hiS hti hci
    rw [hti]
    exact ⟨ht, h3.omega _ ((objs_omega hX3.1 hsub).2 i hiS).2.1, hci, na3⟩
  rintro ⟨s4, a2⟩ ⟨Q4, R4, h4, hB4, hX4, hSg4, fr4⟩
  have hS4 := hS3.fr fr4
  have tm4 : TmFr st T Cs Nt s s4 := tm2.trans (tm3.trans (TmFr.of_fr fr4 hX3.1 h3.nodes))
  try simp only [WP.uncurry'_pair]
  -- `possible_switch_to`
  step with sched.is_schedulable.spec' as ⟨b2, b2_post⟩
  split
  · rename_i hb2
    obtain ⟨hrun4, hbd4, -, hmx4⟩ := b2_post hb2
    refine WP.spec_bind (sched.possible_switch_to.sch s4 t Q4 R4 h4 hB4 hSg4 ht hrun4
      (fun _ => (hS4.act _ (hX4.2.2.bound t ht hbd4).1).2 hmx4)) ?_
    rintro s5 ⟨⟨hi5, hB5, f5⟩, -, -⟩
    simp only [WP.spec_ok, WP.uncurry'_pair]
    obtain ⟨Q5, R5, h5⟩ := hi5
    exact ⟨Q5, R5, h5, hB5, hX4.fr f5, hS4.fr f5, tm4.trans (TmFr.of_fr f5 hX4.1 h4.nodes)⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q4, R4, h4, hB4, hX4, hS4, tm4⟩

end

end Fl4Proofs.P1
