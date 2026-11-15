/-
P3 (DESIGN.md §9), scheduler: **`schedule_tcb` refines l4v
`set_thread_state_act`** (and so `set_thread_state` refines
`set_thread_state`), discharging `SchedHyps.scheduleTcb`.

`is_schedulable` computes the spec's `schedulable` (`is_schedulable_eq`):
the thread is runnable (state word 1 or 2 ↔ Running / Restart, from the
notification relation's `TcbRel1`), has an SC (`tcb_sched_context`) that is
active (`REFILL_MAX` > 0 ↔ `sc_refill_max` > 0), and is not in the release
queue (`IN_QUEUES` release bit ↔ membership of `R` ↔ of `release_queue`).
-/
import Fl4Proofs.P3.SchedRel
import Fl4Proofs.P1.QueueCallers
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! ## Specs of the accessors -/

@[step] theorem sched.cur_thread.spec' (s : S) :
    sched.cur_thread st s ⦃ v => v = nodeW st s (L.cpu s) layout.node.CUR_THREAD ⦄ := by
  unfold sched.cur_thread; step*; simp_all [nodeW]
@[step] theorem sched.action.spec' (s : S) :
    sched.action st s ⦃ v => v = nodeW st s (L.cpu s) layout.node.SCHED_ACTION ⦄ := by
  unfold sched.action; step*; simp_all [nodeW]
@[step] theorem sched.set_action.spec' (s : S) (v : U64) :
    sched.set_action st s v ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v ⦄ := by
  unfold sched.set_action; step*; simp_all

theorem rel_bit_iff (x : U64) : (x &&& sched.Q_RELEASE = 0#u64) ↔ x.val &&& 2 = 0 := by
  have e : sched.Q_RELEASE = 2#u64 := by unfold sched.Q_RELEASE; rfl
  rw [e]; constructor
  · intro h; have := congrArg UScalar.val h; simpa using this
  · intro h; apply UScalar.eq_of_val_eq; simpa using h

@[step] theorem obj.Sc.is_null.spec' (sc : obj.Sc) : obj.Sc.is_null sc ⦃ b => b = decide (sc = 0#u64) ⦄ := by
  unfold obj.Sc.is_null; simp

@[step] theorem sporadic.sc_active.spec' (s : S) (sc : obj.Sc) :
    sporadic.sc_active st s sc ⦃ b => b = decide (L.rmax s sc > 0#u64) ⦄ := by
  unfold sporadic.sc_active
  step* <;> simp_all

/-- `is_schedulable`: runnable, with an active SC, not released. -/
@[step] theorem sched.is_schedulable.spec' (s : S) (t : obj.Tcb) :
    sched.is_schedulable st s t ⦃ b => b = decide ((L.mem s (tStA t) = sched.TS_RUNNING ∨
      L.mem s (tStA t) = sched.TS_RESTART ∨ L.mem s (tStA t) = sched.TS_RUNNING_VM) ∧ L.mem s (scA t) ≠ 0#u64 ∧ L.rmax s (L.mem s (scA t)) > 0#u64 ∧
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) ⦄ := by
  unfold sched.is_schedulable
  step with Fl4Proofs.P1.sched.is_runnable.spec
  split <;> (try simp only [bind_ok]) <;> step* <;> try simp_all [rel_bit_iff, stA, tStA]
  all_goals first
    | exact fun _ => of_decide_eq_true b_post
    | (intro hr; exact False.elim ((of_decide_eq_false b_post) hr))

/-! ## `is_schedulable` is `schedulable` -/

theorem mem_map_bv {xs : List U64} {t : U64} : t.bv ∈ xs.map UScalar.bv ↔ t ∈ xs := by
  constructor
  · intro h; obtain ⟨y, hy, e⟩ := List.mem_map.1 h; exact eq_of_bv e ▸ hy
  · exact List.mem_map_of_mem

theorem runnable_iff {w : U64} {ts : Fl4Spec.ThreadState} (h : w.val = tsCode ts) :
    (w = sched.TS_RUNNING ∨ w = sched.TS_RESTART ∨ w = sched.TS_RUNNING_VM) ↔ Fl4Spec.runnable ts = true := by
  have e1 : sched.TS_RUNNING = 1#u64 := tsVals.1
  have e2 : sched.TS_RESTART = 2#u64 := tsVals.2.1
  have e8 : sched.TS_RUNNING_VM = 8#u64 := by unfold sched.TS_RUNNING_VM; rfl
  rw [e1, e2, e8]
  have v : ∀ k : U64, w = k ↔ w.val = k.val := fun k => ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩
  rw [v, v, v, h]
  cases ts <;> simp [tsCode, Fl4Spec.runnable]

theorem schedulable_eq {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    decide ((L.mem s (tStA t) = sched.TS_RUNNING ∨ L.mem s (tStA t) = sched.TS_RESTART ∨ L.mem s (tStA t) = sched.TS_RUNNING_VM) ∧
      L.mem s (scA t) ≠ 0#u64 ∧ L.rmax s (L.mem s (scA t)) > 0#u64 ∧
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) = Fl4Spec.schedulable t.bv σ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, h1, -, h3, -⟩ := hs.tcb t ht
  have hx := hR.at_tcb ht hk
  unfold Fl4Spec.schedulable
  apply decide_eq_decide.2
  have p1 : Fl4Spec.optPred (fun st => Fl4Spec.runnable st = true)
      (Fl4Spec.optMapSome (Fl4Spec.tcbsOf σ) Fl4Spec.Tcb.tcbState) t.bv ↔ Fl4Spec.runnable x.tcbState = true := by
    simp [Fl4Spec.optPred, Fl4Spec.optMapSome, Fl4Spec.optMap, Fl4Spec.tcbsOfKh, Fl4Spec.tcbOf, hk]
  have p3 : t.bv ∉ σ.releaseQueue ↔ (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    rw [hs.rel, mem_map_bv, ← not_iff_not, not_not, ← hc.released t ht]
  have p2 : Fl4Spec.optPred (fun sc => Fl4Spec.scActive sc = true)
      (Fl4Spec.optMap (Fl4Spec.optMap (Fl4Spec.tcbsOf σ) Fl4Spec.Tcb.tcbSchedContext) (Fl4Spec.scsOf σ)) t.bv ↔
      (L.mem s (scA t) ≠ 0#u64 ∧ L.rmax s (L.mem s (scA t)) > 0#u64) := by
    by_cases h0 : L.mem s (scA t) = 0#u64
    · rw [h0, optRef_zero] at h3
      simp [Fl4Spec.optPred, Fl4Spec.optMap, Fl4Spec.tcbsOfKh, Fl4Spec.tcbOf, hk, h3, h0]
    · rw [optRef_ne h0] at h3
      obtain ⟨y, n, hky, e⟩ := hs.scs _ (hs.scMem t ht h0)
      simp only [Fl4Spec.optPred, Fl4Spec.optMap, Fl4Spec.tcbsOfKh, Fl4Spec.tcbOf, hk, h3, Fl4Spec.scsOfKh,
        hky, Fl4Spec.scOf, Fl4Spec.scActive, Fl4Spec.activeSc, decide_eq_true_eq, ne_eq, h0, not_false_eq_true,
        true_and, gt_iff_val]
      rw [e.max]; simp
  rw [p1, p2, p3, ← runnable_iff hx.st]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, ⟨b, c⟩, d⟩, fun ⟨a, ⟨b, c⟩, d⟩ => ⟨a, b, c, d⟩⟩

/-! ## Writing a node word -/

theorem nodeAt_ne_tfield {T : Set U64} {s : S} {c o y K : U64} (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (hy : y ∈ T) (hya : TcbAddr y) (hK : K.val < 4096) : L.nodeAt s c o ≠ core.num.U64.wrapping_add y K := by
  intro e
  have hv := congrArg UScalar.val e
  rw [tfield_val hya hK] at hv
  have := nodeAt_out hN ho hy; omega

/-- Writing a node word of core `c` keeps the notification footprint. -/
theorem node_wr_foot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {o v : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    FootEq N T (L.mem s) (L.mem (L.wr s (L.nodeAt s c o) v)) := by
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  intro a ha hf
  refine rd_wr_ne (nodeAt_aligned hc.node ho h8) ha ?_
  rintro rfl
  rcases hf with hf | ⟨t, ht, e | e | e | e | e | e⟩
  · exact hS.nodeNW o ho (Or.inl hf)
  · exact hS.nodeNW o ho (Or.inr ⟨t, ht, Or.inl e⟩)
  · exact hS.nodeNW o ho (Or.inr ⟨t, ht, Or.inr (Or.inl e)⟩)
  · exact hS.nodeNW o ho (Or.inr ⟨t, ht, Or.inr (Or.inr (Or.inl e))⟩)
  · exact nodeAt_ne_tfield hc.node ho ht (hc.tcbs t ht) (K := 3448#u64) (by simp) e
  · exact hS.nodeNW o ho (Or.inr ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inl e)))⟩)
  · exact hS.nodeNW o ho (Or.inr ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inr e)))⟩)

/-- A node write leaves the `DOMAIN_TIME` word alone. -/
theorem dt_wr_node {T : Set U64} {s : S} {c o v : U64} (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) : L.mem (L.wr s (L.nodeAt s c o) v) (dtA st s) = L.mem s (dtA st s) := by
  refine rd_wr_ne (nodeAt_aligned hN ho h8) (dtA_aligned hN) fun e => ?_
  have := congrArg UScalar.val e
  rw [nodeAt_val hN ho, dtA_val hN] at this
  have h2 := hN.fits
  simp only [LawfulStore.nodeBase] at this h2; omega

/-- Writing the action word. -/
theorem SchedRel.set_action {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {w : U64} (hw : w = 0#u64 ∨ w = 1#u64 ∨ w ∈ T) {a : Fl4Spec.SchedulerAction}
    (ha : ActRel w a) :
    SchedRel st N T C c (L.wr s (L.nodeAt s c layout.node.SCHED_ACTION) w) { σ with schedulerAction := a } := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have h16 : layout.node.SCHED_ACTION.val = 16 := by simp [layout.node.SCHED_ACTION]
  have hA : Aligned (L.nodeAt s c layout.node.SCHED_ACTION) := nodeAt_aligned hN (by omega) (by omega)
  set s' := L.wr s (L.nodeAt s c layout.node.SCHED_ACTION) w
  have hk : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have hag : SAgree st T C c s s' := by
    refine ⟨hk, L.cpu_wr _ _ _, fun o ho h8 hne _ => ?_, fun y hy K hK => ?_, ?_, ?_, fun sc hsc => ?_⟩
    · refine rd_wr_ne hA (nodeAt_aligned hN ho h8) fun e => hne ?_
      have := congrArg UScalar.val e
      rw [nodeAt_val hN (by omega), nodeAt_val hN ho] at this; omega
    · obtain ⟨h1, h2, -⟩ := schedField_ok hK
      exact rd_wr_ne hA (field_aligned (hc.tcbs y hy) h1 h2) (nodeAt_ne_tfield hN (by omega) hy (hc.tcbs y hy) h1)
    · have hal : Aligned (curDomA st s) := by
        have h1 := hN.align; have h2 := hN.fits
        unfold Aligned curDomA
        simp only [LawfulStore.nodeBase] at h1 h2
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      refine rd_wr_ne hA hal fun e => ?_
      have := congrArg UScalar.val e
      rw [nodeAt_val hN (by omega)] at this
      have h2 := hN.fits
      simp only [LawfulStore.nodeBase] at this h2
      simp [curDomA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at this; omega
    · refine rd_wr_ne hA (dtA_aligned hN) fun e => ?_
      have := congrArg UScalar.val e
      rw [nodeAt_val hN (by omega), dtA_val hN] at this
      have h2 := hN.fits
      simp only [LawfulStore.nodeBase] at this h2; omega
    · intro a hal hin
      refine rd_wr_ne hA hal fun e => ?_
      have := congrArg UScalar.val e
      rw [nodeAt_val hN (by omega)] at this
      have := (hS.scOutIn hsc hin).2.1; omega
  have hw' : nodeW st s' c layout.node.SCHED_ACTION = w := by
    unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk]; exact rd_wr_eq hA
  have hm := hs.rmax_eq hag.sc
  refine ⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk]; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk]; exact hS.domNW, by rw [dtA_ksb hk]; exact hS.dtNW,
    scOut_transfer hk (SzKeep.of_kheap rfl) hS.scOut, scDisj_transfer (SzKeep.of_kheap rfl) hS.scDisj,
    by rw [hw']; exact hw, by rw [hw']; exact ha, ?_, hs.core_eq hag.sc hS.core, Q, R, hc.agree hag.toC, ?_⟩
  · have e : nodeW st s' c layout.node.REPROGRAM = nodeW st s c layout.node.REPROGRAM := by
      unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk]
      refine rd_wr_ne hA (nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])) ?_
      intro e; have := congrArg UScalar.val e
      rw [nodeAt_val hN (by omega), nodeAt_val hN (by simp [layout.node.REPROGRAM])] at this
      simp [layout.node.REPROGRAM] at this
    rw [e]; exact hS.repr
  have hs' := hs.agree hag
  exact ⟨hs'.rq, hs'.rqDom, hs'.rel, hs'.curThread, hs'.curSc, hs'.curTime, hs'.consumed,
    hs'.curDom, hs'.tcb, hs'.scMem, hs'.scs, hs'.idleSc, hs'.domTime, hs'.idleTh⟩

/-! ## `schedule_tcb` -/

theorem bv_ne {x y : U64} (h : x ≠ y) : x.bv ≠ y.bv := fun e => h (eq_of_bv e)

theorem stsAct_eq_self {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef}
    (h : ¬ (t = σ.curThread ∧ σ.schedulerAction = .resumeCurThread ∧ ¬ Fl4Spec.schedulable t σ = true)) :
    stsAct σ t = σ := by
  unfold stsAct; simp only [h, ↓reduceIte]

/-- **`schedule_tcb` refines `set_thread_state_act`** (`SchedHyps.scheduleTcb`). -/
theorem schedule_tcb_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) (t : U64) (ht : t ∈ T) :
    sched.schedule_tcb st s t ⦃ s' => FootEq N T (L.mem s) (L.mem s') ∧ SchedRel st N T C c s' (stsAct σ t.bv) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hcur := hc.cur
  have hsch := schedulable_eq hR hS ht
  have ha := hS.act
  have hfoot0 : FootEq N T (L.mem s) (L.mem s) := fun _ _ _ => rfl
  unfold sched.schedule_tcb
  step
  step
  rw [t1_post, hcur] at b_post
  by_cases e1 : t = nodeW st s c layout.node.CUR_THREAD
  · have hb : b = true := by rw [b_post]; exact decide_eq_true e1
    simp only [hb, ↓reduceIte]
    step
    rw [i_post, hcur]
    by_cases e2 : nodeW st s c layout.node.SCHED_ACTION = sched.ACTION_RESUME_CURRENT
    · have hres : σ.schedulerAction = .resumeCurThread := by
        have e0 : sched.ACTION_RESUME_CURRENT = 0#u64 := by unfold sched.ACTION_RESUME_CURRENT; rfl
        rw [e2, e0] at ha
        cases h : σ.schedulerAction <;> rw [h] at ha <;> simp only [ActRel] at ha <;>
          first | rfl | exact absurd rfl ha.1 | exact absurd ha (by decide)
      simp only [e2, ↓reduceIte]
      step
      rw [hsch] at b1_post
      by_cases e3 : Fl4Spec.schedulable t.bv σ = true
      · simp only [b1_post, e3, ↓reduceIte, WP.spec_ok]
        refine ⟨hfoot0, ?_⟩
        rw [stsAct_eq_self (by intro h; exact h.2.2 e3)]; exact hS
      · simp only [b1_post, e3, Bool.false_eq_true, ↓reduceIte]
        step
        subst s'_post
        rw [hcur]
        have e4 : stsAct σ t.bv = { σ with schedulerAction := .chooseNewThread } := by
          unfold stsAct
          have h' : t.bv = σ.curThread ∧ σ.schedulerAction = .resumeCurThread ∧
            ¬ Fl4Spec.schedulable t.bv σ = true := ⟨by rw [hs.curThread, e1], hres, e3⟩
          split_ifs with hh
          · rfl
          · exact absurd h' hh
        have hch : sched.ACTION_CHOOSE_NEW = 1#u64 := by unfold sched.ACTION_CHOOSE_NEW; rfl
        rw [e4, hch]
        exact ⟨node_wr_foot hS (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]),
          hS.set_action (Or.inr (Or.inl rfl)) rfl⟩
    · simp only [e2, ↓reduceIte, WP.spec_ok]
      refine ⟨hfoot0, ?_⟩
      have hnr : σ.schedulerAction ≠ .resumeCurThread := by
        intro h; rw [h] at ha
        have e0 : sched.ACTION_RESUME_CURRENT = 0#u64 := by unfold sched.ACTION_RESUME_CURRENT; rfl
        exact e2 (by rw [e0]; exact ha)
      rw [stsAct_eq_self (by intro h; exact hnr h.2.1)]; exact hS
  · have hb : b = false := by rw [b_post]; exact decide_eq_false e1
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨hfoot0, ?_⟩
    rw [stsAct_eq_self (by intro h; exact bv_ne e1 (h.1.trans hs.curThread))]; exact hS

end

end

end Fl4Proofs.P3.Sched
