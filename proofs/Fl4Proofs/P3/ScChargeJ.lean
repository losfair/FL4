/-
P3 (DESIGN.md §9), scheduling contexts: **`charge_budget` without timeout
faults at `J`** (KENTRY-PLAN item 8; `can_timeout_fault = false`: Yield and
the preemption point's branch for a thread that is not schedulable).

* P1: `sched.end_timeslice.allF`, `sched.charge_budget.allF` (QueueBudgetG's
  `.allG` at `can = false`, without the timeout-fault premise `TmoKG`).
-/
import Fl4Proofs.P3.ScChargeG
import Fl4Proofs.P3.XTopJointRunPost
import Fl4Proofs.P3.ScTmo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {A : Type _} {ar : machine.Arch A} {Ac : Set U64}

/-- seL4 `endTimeslice` without timeout faults (QueueBudgetG's `.allG` at
`cto = false`: no `TmoKG`). -/
theorem sched.end_timeslice.allF (hA : P0.ArchTotal ar) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hc : CurOK st T s)
    {G : S → Prop} (hGF : ∀ s1 s2 : S, G s1 → Foot st T Cs Sg Scs Z (EH H) s1 s2 → G s2) (hG : G s) :
    sched.end_timeslice st ar s a false ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ G s' ⦄ := by
  have E := end_suffG hA s a Q R h hB hX hSg hS hc hGF hG
  unfold sched.end_timeslice
  step with sched.cur_sc.spec as ⟨sc, sc_post⟩
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  have e1 : sc = L.cscW s := sc_post
  have e2 : ct = L.curW s := ct_post
  subst e1 e2
  step with sporadic.is_round_robin.spec as ⟨rr⟩
  step with obj.Tcb.state.spec
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun valid _ => ?_
  · split
    · exact P0.faults.valid_timeout_handler.p0 st s _ L.total
    · simp
  split
  · rename_i hf; exact absurd hf Bool.false_ne_true
  · exact E

/-- seL4 `chargeBudget` without timeout faults (QueueBudgetG's `.allG` at
`cto = false`: no `TmoKG`). -/
theorem sched.charge_budget.allF (hA : P0.ArchTotal ar) (s : S) (a : A) (used : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hSg : SgOK st Ω Sg s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)))
    (hna : L.actionW s ≠ L.curW s) (hcA : L.cscW s ∈ Ac)
    {G : S → Prop} (hGF : ∀ s1 s2 : S, G s1 → Foot st T Cs Sg Scs Z (EH H) s1 s2 → G s2) (hG : G s) :
    sched.charge_budget st ar s a used false ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ G s' ⦄ := by
  have hcS : L.cscW s ∈ Scs := hX.2.2.cur
  have hcT0 : L.curW s ∈ T := h.curT
  have hW : RefillsWF st s (L.cscW s) (Z (L.cscW s)) := hS.wf hcS hcA
  unfold sched.charge_budget
  step with sched.cur_sc.spec as ⟨sc, sc_post⟩
  have e1 : sc = L.cscW s := sc_post
  subst e1
  step with sched.idle_sc.spec as ⟨s1⟩
  step with sc_ne.spec as ⟨b⟩
  -- the ring and the SC's `CONSUMED` word
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (fun b => InRing (L.cscW s) (Z (L.cscW s)) b ∨
      b = core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) ∧ RefillsWF st s2 (L.cscW s) (Z (L.cscW s))) ?_ ?_
  · split
    · step with sporadic.is_round_robin.spec as ⟨b1⟩
      refine WP.spec_bind (Pₘ := fun s3 => RefillsWF st s3 (L.cscW s) (Z (L.cscW s)) ∧
          WritesIn st s s3 (InRing (L.cscW s) (Z (L.cscW s)))) ?_ ?_
      · split
        · step with obj.Sc.refill_head.spec as ⟨hi, hi_post⟩
          step with obj.Sc.refill_tail.spec as ⟨ti, ti_post⟩
          step with sporadic.get.spec as ⟨hh, hh_post⟩
          step with sporadic.get.spec as ⟨tt, tt_post⟩
          step as ⟨i, _⟩
          step with sporadic.put.spec as ⟨s4, s4_post⟩
          subst hi_post ti_post s4_post
          have h4 := hW.putS (r := { hh with amount := i }) hW.head_lt
          have w4 := hW.frame_putS (r := { hh with amount := i }) hW.head_lt
          obtain ⟨h8, -, -⟩ := hW.bounds
          have hfit : (L.cscW s).val + 96 + 16 * (L.rhead s (L.cscW s)).val + 16 ≤ 2 ^ 64 := by
            have := hW.bounds.2.2; have := hW.inside; have := hW.head_lt; have := hW.le_abs
            have := absMax_lt (Z (L.cscW s)); obtain ⟨-, hm, -⟩ := hW.bounds; omega
          have htl : (L.rtail s (L.cscW s)).val < (L.rmax (L.putS s (L.cscW s) (L.rhead s (L.cscW s))
              { hh with amount := i }) (L.cscW s)).val := by
            rw [rmax_putS h8 hfit]; exact hW.tail_lt
          step with sporadic.put.spec as ⟨s5, s5_post⟩
          subst s5_post
          exact ⟨h4.putS htl, w4.trans1 (h4.frame_putS htl)⟩
        · exact WP.spec_mono (WP.spec_and (sporadic.budget_check.wf hA a used hW rfl)
            (sporadic.budget_check.fr hA a used hW rfl)) fun s3 hh3 => hh3
      · rintro s3 ⟨h3, w3⟩
        step with obj.Sc.consumed.spec as ⟨ci⟩
        step as ⟨total, _⟩
        step with obj.Sc.set_consumed.spec as ⟨s4, s4_post⟩
        subst s4_post
        have hal : Aligned (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED) := by
          obtain ⟨hP, hz⟩ := hX.1.sc _ hcS
          obtain ⟨h8, -, -⟩ := sc_lo hP hz
          unfold Aligned; rw [sc_word_val hP hz (by simp [layout.sc.CONSUMED])]; simp [layout.sc.CONSUMED]; omega
        exact ⟨(w3.trans (writesIn_wr hal)).mono fun b hb => by
          rcases hb with hb | hb
          · exact Or.inl hb
          · exact Or.inr hb, h3.wr_cons⟩
    · simp only [WP.spec_ok]; exact ⟨WritesIn.refl _ _, hW⟩
  rintro s2 ⟨w2, wf2⟩
  have hS2 := SCsOK.ringc h hS hX hcS w2 wf2
  obtain ⟨h2, hB2, hX2, hSg2, ea2, ec2, ecs2, f2⟩ := ring_bx h hB hX hSg hcS w2
  -- the node's `CONSUMED`
  step with sched.set_consumed.spec as ⟨s3, s3_post⟩
  rw [show L.nodeA s2 layout.node.CONSUMED = L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED from rfl] at s3_post
  obtain ⟨h3, hB3, hX3, hSg3, ea3, ec3, ecs3, f3⟩ := node_bx (o := layout.node.CONSUMED) (v := 0#u64) h2 hB2 hX2 hSg2
    (by simp [layout.node.CONSUMED, LowFree]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have hS3 : SCsOK st T Ω Sg Scs Z Ac (L.wr s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) 0#u64) := by
    have hN2 := h2.nodes _ h2.cur
    obtain ⟨-, hc⟩ := objs_omega hX2.1 hS2.sub
    have hco : (layout.node.CONSUMED).val = 40 := by simp [layout.node.CONSUMED]
    refine SCsOK.wr h2 hS2 hX2 (nodeAt_aligned hN2 (by rw [hco]; omega) (by rw [hco])) (fun y hy => ?_) ?_
      (fun c hc' => ?_) (fun c hc' => out_ne_node (h2.omega _ (spor_omega hX2.1 hc')) h2.cur hN2 (by rw [hco]; omega))
      (fun c hc' e => absurd e (out_ne_node (h2.omega _ (hS2.sub _ (hX2.1.repW c hc'))) h2.cur hN2 (by rw [hco]; omega)))
    · rw [scA_eq]; exact fun e => node_ne_field hN2 (by rw [hco]; omega) hy (h2.tcbs y hy) (by simp)
        (UScalar.eq_of_val_eq e)
    · intro e
      simp only [LawfulStore.nodeA] at e
      rw [nodeAt_val hN2 (by rw [hco]; omega), nodeAt_val hN2 (by simp [layout.node.CUR_SC]), hco] at e
      simp [layout.node.CUR_SC] at e
    · obtain ⟨-, -, c3, c4, c5⟩ := hc c hc'
      exact ⟨out_ne_node (h2.omega _ c3) h2.cur hN2 (by rw [hco]; omega),
        out_ne_node (h2.omega _ c4) h2.cur hN2 (by rw [hco]; omega),
        out_ne_node (h2.omega _ c5) h2.cur hN2 (by rw [hco]; omega)⟩
  rw [← s3_post] at h3 hB3 hX3 hSg3 ea3 ec3 ecs3 f3 hS3
  have W3 : WritesIn st s s3 (ChgW st Scs Z s) := by
    obtain ⟨hP, hz⟩ := hX.1.sc _ hcS
    obtain ⟨-, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hN2 := h2.nodes _ h2.cur
    have wn : WritesIn st s2 s3 (fun b => b = L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) := by
      rw [s3_post]; exact writesIn_wr (nodeAt_aligned hN2 (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
    refine (w2.trans wn).mono fun b hb => ?_
    rcases hb with (hh | rfl) | rfl
    · exact Or.inl ⟨_, hcS, hh.inSC⟩
    · exact Or.inl ⟨_, hcS, by rw [hv]; simp, by rw [hv]; simp [layout.sc.CONSUMED]; omega⟩
    · exact Or.inr (by rw [nodeAt_of_ksb w2.1, w2.2.1])
  have G3 : G s3 := hGF _ _ hG (Foot.of W3 fun b hb => by
    rcases hb with ⟨c, hc', hin⟩ | e
    · exact kw_sc hc' hin
    · rw [e]; exact kw_node h.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
  have K3 : CurK st s s3 := CurK.of h.tcbs hcT0 (ec3.trans ec2) ((f3 _ hcT0).1.trans (f2 _ hcT0).1)
    (Or.inl (ea3.trans ea2))
  step with sched.cur_thread.spec as ⟨ct, ct_post⟩
  have e2 : ct = L.curW s3 := ct_post
  subst e2
  step with sched.is_schedulable.spec' as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hrun, hbd, hrl, hrm⟩ := b1_post hb1
    have hcT : L.curW s ∈ T := h.curT
    have esc : L.mem s3 (scA (L.curW s3)) = L.mem s (scA (L.curW s)) := by
      rw [ec3, ec2, (f3 _ hcT).1, (f2 _ hcT).1]
    have hc : CurOK st T s3 := ⟨hrun, hbd, hrl, by
      rw [ecs3, ecs2, esc]; exact hcsc (by rw [← esc]; exact hbd), by rw [ea3, ea2, ec3, ec2]; exact hna, hrm⟩
    refine WP.spec_bind (sched.end_timeslice.allF hA s3 a Q R h3 hB3 hX3 hSg3 hS3 hc hGF G3) ?_
    rintro ⟨s4, a1⟩ ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hSg4, hS4⟩, g4⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (WP.spec_and (sched.reschedule_required.sch s4 Q4 R4 h4 hB4 hSg4)
      (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s4 h4)) ?_
    rintro s5 ⟨⟨⟨⟨Q5, R5, h5⟩, hB5, f5⟩, ea5, ec5, -⟩, k5⟩
    refine WP.spec_bind (WP.spec_and (sched.set_reprogram.sch s5 Q5 R5 h5 hB5 (hSg4.fr f5))
      (sched.set_reprogram.spec s5)) ?_
    rintro s6 ⟨⟨⟨h6, hB6, f6⟩, ea6, ec6⟩, e6⟩
    simp only [WP.spec_ok, WP.uncurry'_pair]
    have g6 : G s6 := by
      rw [e6]
      exact hGF _ _ (hGF _ _ g4 k5) (foot_node (h5.nodes _ h5.cur) h5.cur (o := layout.node.REPROGRAM)
        (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
    exact ⟨⟨⟨Q5, R5, h6⟩, hB6, (hX4.fr f5).fr f6, (hSg4.fr f5).fr f6, (hS4.fr f5).fr f6⟩, g6⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨⟨⟨Q, R, h3⟩, hB3, hX3, hSg3, hS3⟩, G3⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

section Spec

/-- The spec's steps of `charge_budget` without timeout faults change no
thread state (`NKT`). -/
theorem nkt_chargeBudgetF (u : Ticks) : NKT (chargeBudget (Z := Unit) u false) := by
  unfold chargeBudget endTimeslice refillResetRr refillBudgetCheck handleOverrun chargeEntireHeadRefill
    headInsufficientLoop mergeNonoverlappingHeadRefill scheduleUsed refillPopHead updateRefillHd updateRefillTl
    refillAddTail isRoundRobin getRefillHead getRefillTail getRefills refillSingle refillSize refillFull
    getScRefillReady getScRefillSufficient getThreadState isValidTimeoutHandler getCap
  try simp only [Bool.false_eq_true, false_and, ↓reduceIte]
  repeat (any_goals (first | nkt_step | unfold getRefills | unfold getRefillHead | unfold getRefillTail | exact nkt_postpone _ | exact nkt_rescheduleRequired))

theorem pres_chargeBudgetF (f : Bool × Bool) (u : Ticks) : Pres f (chargeBudget (Z := Unit) u false) := by
  unfold chargeBudget endTimeslice refillResetRr refillBudgetCheck handleOverrun chargeEntireHeadRefill
    headInsufficientLoop mergeNonoverlappingHeadRefill scheduleUsed refillPopHead updateRefillHd updateRefillTl
    refillAddTail isRoundRobin getRefillHead getRefillTail getRefills refillSingle refillSize refillFull
    getScRefillReady getScRefillSufficient getThreadState isValidTimeoutHandler getCap
  try simp only [Bool.false_eq_true, false_and, ↓reduceIte]
  repeat (any_goals (first | pres_step | unfold getRefills | unfold getRefillHead | unfold getRefillTail | (exact pres_postpone f _) | (exact pres_rescheduleRequired f) | (apply pres_updateSchedContext; intro _ _; exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩)))

theorem lkm_chargeBudgetF (W : ObjRef → Prop) (u : Ticks) : LKM W (chargeBudget (Z := Unit) u false) := by
  unfold chargeBudget endTimeslice refillResetRr refillBudgetCheck handleOverrun chargeEntireHeadRefill
    headInsufficientLoop mergeNonoverlappingHeadRefill scheduleUsed refillPopHead updateRefillHd updateRefillTl
    refillAddTail isRoundRobin getRefillHead getRefillTail getRefills refillSingle refillSize refillFull
    getScRefillReady getScRefillSufficient getThreadState isValidTimeoutHandler getCap
  try simp only [Bool.false_eq_true, false_and, ↓reduceIte]
  repeat (any_goals (first | lkm_step | unfold getRefills | unfold getRefillHead | unfold getRefillTail | exact lkm_postpone _ | exact lkm_rescheduleRequired))

theorem fk_chargeBudgetF (u : Ticks) : FKA (chargeBudget (Z := Unit) u false) := by
  unfold chargeBudget endTimeslice refillResetRr refillBudgetCheck handleOverrun chargeEntireHeadRefill
    headInsufficientLoop mergeNonoverlappingHeadRefill scheduleUsed refillPopHead updateRefillHd updateRefillTl
    refillAddTail isRoundRobin getRefillHead getRefillTail getRefills refillSingle refillSize refillFull
    getScRefillReady getScRefillSufficient getThreadState isValidTimeoutHandler getCap
  try simp only [Bool.false_eq_true, false_and, ↓reduceIte]
  repeat (any_goals (first | fk_step | fk_unf))

/-- The kheap after the tail of `charge_budget` without timeout faults is the
kheap before it. -/
theorem kh_chargeTailF : Vs.KhK (chargeTail false) := by
  unfold chargeTail endTimeslice isRoundRobin getThreadState isValidTimeoutHandler getCap getScRefillReady
    getScRefillSufficient postpone tcbReleaseEnqueue readyTimesAppend orderedInsert setReleaseQueue
    rescheduleRequired setSchedulerAction tcbSchedAction getTcbQueue setTcbQueue getScObjRef
  try simp only [Bool.false_eq_true, false_and, ↓reduceIte]
  repeat (any_goals (first | exact Vs.kh_doMachineOp _ | exact Vs.kh_doExtendedOp _ | dk_step0 | unfold getSchedContext | unfold threadGet | unfold getObject | unfold getScRefillSufficient | unfold getScRefillReady | unfold getScObjRef | unfold getTcbQueue | unfold setTcbQueue | unfold tcbSchedAction | unfold tcbReleaseEnqueue | unfold readyTimesAppend | unfold orderedInsert | unfold setReleaseQueue | unfold setSchedulerAction))

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 32000000 in
/-- **`charge_budget` without timeout faults at `J`** (KENTRY-PLAN item 8):
from `JAtZ` with the current thread's `CurInv` (l4v `cur_sc_tcb_are_bound`,
`cur_sc_active`, `ct_not_in_release_q`, `cur_sc_not_blocked`), not the idle
thread and not the switch target, FL4's `charge_budget used false` refines
the spec's `charge_budget used False` and ends at `JAtZ` (same ghosts but the
call lists): an SC step (`JAtZ.sc_frame`). The platform's `MAX_RELEASE_TIME`
and `MIN_BUDGET` ([P], `hmrt`, `hmb`) as ScCharge6's. -/
theorem JAtZ.chargeBudgetJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) (used : U64) :
    sched.charge_budget st arI s a used false ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv false σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  have hP0 := J.ip
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, hsc0, htw, hts, hact, hnr, hnb⟩ := CurInv.facts hS J.inv hC
  have hct : nodeW st s Z.c layout.node.CUR_THREAD ∈ Z.T := hc.curT
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hthc : Z.th (nodeW st s Z.c layout.node.CUR_THREAD) = some .tcb := (hJ.tcb _).2 (J.zH.1 _ hct)
  have ecur : L.curW s = nodeW st s Z.c layout.node.CUR_THREAD := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have ecsc : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  -- the current SC is not the idle SC (the idle SC is the idle thread's)
  obtain ⟨xt, hkt, hxs, hnbt⟩ := hC.tcb
  have hcsI : σ.curSc ≠ σ.idleSc := by
    intro e
    obtain ⟨y, n, hky, hyt⟩ := J.inv.back _ xt _ hkt hxs
    obtain ⟨xi, hki, hxi, -, -⟩ := J.act.2
    rw [← e] at hxi
    obtain ⟨y', n', hky', hyt'⟩ := J.inv.back _ xi _ hki hxi
    rw [hky] at hky'; cases hky'
    exact hni (Option.some.inj (hyt.symm.trans hyt'))
  have hpc : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.curSc := hs.curSc.symm
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hxa : Fl4Spec.scActive x = true := hact (by rw [hpc]; exact hcsI) x n hk
  have hscS : nodeW st s Z.c layout.node.CUR_SC ∈ P1.Heap.scs H := ⟨_, (hJ.sc _ x n hsc0 hk).2⟩
  have hcA : L.cscW s ∈ Ac := by
    rw [ecsc]; exact (J.blk.2.2.2.1.act _ hscS).2 (fun e => hx.rmax_ne hxa (by rw [e]; rfl))
  have hne : σ.curThread ≠ (nodeW st s Z.c layout.node.CUR_SC).bv := fun e => by
    rw [e, hk] at hkt; cases hkt
  -- P1
  obtain ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩ := J.blk
  have hcsc1 : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s)) := fun _ => by
    rw [ecur, ecsc, hts]
  have hna : L.actionW s ≠ L.curW s := by
    rw [ecur]; exact actionW_ne_of hS hct (by rw [← hs.curThread]; exact hnsw)
  have hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st Z.N Z.T Z.C Z.c s' σ' →
      TmoKeep st (nodeW st s Z.c layout.node.CUR_THREAD) s σ s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s Z.c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s Z.c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄ :=
    fun s' σ' _ hK => hval_of_rel J.xtop.rel.1 J.xtop.rel.2.1.1 hthc s' σ' hK
  refine WP.spec_mono (WP.spec_and (charge_budget_refinesF (ar := arI) s a σ hAT hS hR J.nsc J.inv hscC hsc0
    htw hts hS.idle hact hnr hnb hmrt hmb hval used)
    (P1.sched.charge_budget.allF (G := fun s' => P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H)
      (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s') hAT s a used Q1 R1 h1 hB1 hX1 hSg1 hS1 hcsc1 hna hcA
      (fun _ _ g1 g2 => g1.trans g2) (P1.WritesIn.refl _ _))) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', hsp, hS', hI', hR', hN', hact', hcons, hAI, hWK, hra, σ2, hH, ht2⟩, hP1⟩
  try simp only [WP.uncurry'_pair] at hP1
  obtain ⟨hbx, hfoot⟩ := hP1
  refine ⟨hra, σ', hsp, ?_⟩
  -- the spec step
  have mem : ((), σ') ∈ (Fl4Spec.chargeBudget (Z := Unit) used.bv false σ).1 := by
    rw [hsp]; exact Set.mem_singleton _
  have hK : ScTKw (fun _ => False) σ σ' := nkt_chargeBudgetF _ σ _ mem
  have hsok : SOK (true, true) σ σ' := pres_chargeBudgetF _ _ σ _ mem
  have hlk : LK (fun _ => False) σ σ' := lkm_chargeBudgetF _ _ σ _ mem
  have hfk : FK σ σ' := fk_chargeBudgetF _ σ _ mem
  have ek : σ'.kheap = σ2.kheap := kh_chargeTailF σ2 ((), σ') (by rw [ht2]; exact Set.mem_singleton _)
  obtain ⟨-, -, -, -, -, -, -, -, hfr2, hsck2⟩ := hH
  have hkp : ∀ q, q ≠ (nodeW st s Z.c layout.node.CUR_SC).bv → σ'.kheap q = σ.kheap q := fun q hq => by
    rw [ek]; exact hfr2 q hq
  obtain ⟨y, hky, hyt, hym⟩ := hsck2 x n hk
  have hky' : σ'.kheap (nodeW st s Z.c layout.node.CUR_SC).bv = some (.schedContext y n) := by rw [ek]; exact hky
  have hya : Fl4Spec.scActive y = true := by simp only [Fl4Spec.scActive, hym]; exact hxa
  -- FL4's writes and the relation
  have hW : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.tfoot_of_kfoot hWK
  have hX' : XTopAt (L := L) AR Z s' a σ' :=
    xtop_sc_step (ct := σ.curThread) J.xtop hP0 J.nk hW hK.ofFalse hS' hR' id
  have hY : YieldRel Z.T Z.C (L.mem s') σ' :=
    J.yld.frame (fun y1 hy1 => hWK.mem_eq (yieldA_aligned hT hy1) fun hb => hb.ne_yield hS hy1 rfl)
      (hsok.ykeep rfl)
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_tr hS J.rp J.mcp J.call J.rfree ⟨hS', hR', hN', hI'⟩ hY (hW.mono fun _ h => Or.inl h) hsok rfl
  have hAI' := hAI J.act
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hidW := J.idleW_keep hS' hfk.2.1 hfk.2.2
  have hblk' : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' :=
    ⟨hbx.1, hbx.2.1, hbx.2.2.1, hbx.2.2.2.2, hbx.2.2.2.1⟩
  -- the scheduler facts
  have hcur' : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases hact' with e | hH'
    · exact Or.inl e
    · right
      obtain ⟨hcs, hcc, hrq, -, -, -, -, -, -, -⟩ := hH'
      refine ⟨⟨xt, by rw [hcc, hkp _ hne]; exact hkt, by rw [hcs]; exact hxs, hnbt⟩,
        ⟨y, n, by rw [hcs, ← hpc]; exact hky'⟩, fun _ y1 n1 hy1 => ?_, by rw [hcc, hrq]; exact hC.notRel⟩
      rw [hcs, ← hpc, hky'] at hy1; cases hy1; exact hya
  have hown' : CurOwnW Z.T Z.C σ' := by
    obtain ⟨u, hu, xu, hku, hxu, hou, -⟩ := curOwn_of_curInv hS J.inv hC
    have hup : u.bv ≠ (nodeW st s Z.c layout.node.CUR_SC).bv := fun e => by rw [e, hk] at hku; cases hku
    refine Or.inl ⟨u, hu, xu, by rw [hkp _ hup]; exact hku, by rw [hfk.1]; exact hxu, fun y1 n1 hy1 => ?_,
      fun h0 => absurd h0 (by rw [hcons]; decide)⟩
    rw [hfk.1, ← hpc, hky'] at hy1; cases hy1
    rw [hyt]; exact hou x n (by rw [← hpc]; exact hk)
  have hoff : OffOK σ' := fun h0 => absurd h0 (by rw [hcons]; decide)
  have hcr : CurRunM σ' := by
    rcases hact' with e | hH'
    · exact Or.inl (act_cn_nr e)
    · obtain ⟨-, hcc, -, hac, -, hid, -, -, -, -⟩ := hH'
      rcases J.curRun with h | h
      · exact Or.inl (by rw [hac]; exact h)
      · right
        rcases h with h | h
        · left; intro y1 hy1; rw [hcc, hkp _ hne] at hy1; exact h y1 hy1
        · right; rw [hcc, hid]; exact h
  have hbsa : BlockedScActive σ' := by
    refine J.bsa.back (fun q y1 n1 hq ha => ?_) (fun t x1 hx1 hq => ?_)
    · by_cases e : q = (nodeW st s Z.c layout.node.CUR_SC).bv
      · rw [e, hky'] at hq; cases hq; rw [hya] at ha; cases ha
      · exact ⟨y1, by rw [← hkp q e]; exact hq, ha, fun _ h => h, id⟩
    · have e : t ≠ (nodeW st s Z.c layout.node.CUR_SC).bv := fun e => by rw [e, hky'] at hx1; cases hx1
      exact ⟨x1, by rw [← hkp t e]; exact hx1, hq⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_stepQ hX' hW hK (fun _ h => h.elim) hlk hfk hAI'.1 hY' ((hsok.ykeep rfl).dk q.bv) (fun h => h)
      (J.jcov.dead q hq)
  exact ⟨Lst', J.sc_frame hW hK hX' hCR' hRF' hY' hM' (J.sc_buf hW hK) hRP' (J.sc_apart hW hK)
    (J.sc_jpl hW hK hidW.2) (J.sc_jcov hW hdead (fun q hq hn => absurd hq hn) hidW)
    (J.sc_kern hW hK hfk hX' hDbg fun _ h => h) (J.sc_utc hW hK hDbg) hN' hI' hcur' hown' hoff hAI' hbsa hcr
    hblk' hKd hidW.1 J.zD⟩

end

end

end Fl4Proofs.P3

