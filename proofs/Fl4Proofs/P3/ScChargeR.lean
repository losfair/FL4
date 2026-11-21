/-
P3 (DESIGN.md §9), scheduling contexts: **`charge_budget` with
`can_timeout_fault = true` for a round-robin current SC** (KENTRY-PLAN kp4/kp5
(b): `check_budget`'s charge when the current thread has an endpoint timeout
handler but its SC is round-robin).

`end_timeslice` raises a timeout fault only when the current SC is not
round-robin (FL4 `!rr`, spec `¬roundRobin`). For a round-robin SC the head
charge is `refill_reset_rr` plus the consumed update, which keep the SC's
period (0), so at `end_timeslice` both sides take the `can = false` path:

* `endTimeslice_rr` / `end_timeslice_rr`: the two `end_timeslice`s are equal
  when the current SC is round-robin (spec: `scPeriod = 0`; FL4: the period
  word 0).
* `chargeHead_rr`: the spec's head charge of a round-robin SC keeps its period
  (an explicit `updSc`).
* `charge_budget_rr` (SchedRel level, `charge_budget_refinesF`'s premises):
  `charge_budget used true = charge_budget used false` on both sides (the
  period word after the head from `SchedRel` there and the spec's SC, by
  determinism of the head).
* `NoTmoSend σ`: the current thread has no endpoint timeout handler, or the
  current SC is round-robin: no timeout fault can be raised by the charge.
* `JAtZ.chargeBudgetRJ` / `JAtZ.chargeBudgetTJ`: ScChargeJ's
  `JAtZ.chargeBudgetJ` for `can = true` with a round-robin SC / under
  `NoTmoSend` (with ScChargeN's `chargeBudgetNJ`).
-/
import Fl4Proofs.P3.ScChargeN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **`endTimeslice` with a round-robin current SC** does not depend on
`canTimeout`. -/
theorem endTimeslice_rr {σ : State Unit} {x : SchedContext} {n : Nat}
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) (hp : x.scPeriod = 0) :
    endTimeslice (Z := Unit) true σ = endTimeslice false σ := by
  unfold endTimeslice
  simp only [nd_gets_bind, nd_bind_one (isRoundRobin_eq hk), hp, decide_true, not_true_eq_false, false_and,
    and_false, Bool.false_eq_true, ↓reduceIte]

/-- **The head charge of a round-robin SC** keeps its period. -/
theorem chargeHead_rr {σ : State Unit} {x : SchedContext} {n : Nat} (u : Ticks)
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) (hp : x.scPeriod = 0) (hid : σ.curSc ≠ σ.idleSc)
    {rs : List sporadic.Refill} (hx : x.scRefills = rs.map toRefill) (hne : rs ≠ []) :
    ∃ y : SchedContext, y.scPeriod = 0 ∧ chargeHead u σ = ({((), updSc σ σ.curSc y n)}, False) := by
  refine ⟨{ { x with scRefills := (rrResetL rs).map toRefill } with
    scConsumed := x.scConsumed + u }, hp, ?_⟩
  have hk1 : (updSc σ σ.curSc { x with scRefills := (rrResetL rs).map toRefill } n).kheap σ.curSc =
      some (.schedContext { x with scRefills := (rrResetL rs).map toRefill } n) := by simp [updK]
  unfold chargeHead
  rw [nd_gets_bind, nd_gets_bind]
  unfold Fl4Spec.NonDet.when
  rw [if_pos hid, nd_bind_one (isRoundRobin_eq hk)]
  simp only [hp, decide_true, ↓reduceIte]
  rw [nd_bind_one (refillResetRr_eq hk hx hne), updateSchedContext_eq hk1, updSc_updSc]
  simp only [hp]

/-- **`chargeBudget` with a round-robin current SC** does not depend on
`canTimeout`. -/
theorem chargeBudget_rr {σ : State Unit} (u : Ticks) {x : SchedContext} {n : Nat}
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) (hp : x.scPeriod = 0) (hid : σ.curSc ≠ σ.idleSc)
    {rs : List sporadic.Refill} (hx : x.scRefills = rs.map toRefill) (hne : rs ≠ []) :
    chargeBudget (Z := Unit) u true σ = chargeBudget u false σ := by
  obtain ⟨y, hy, h2⟩ := chargeHead_rr u hk hp hid hx hne
  rw [chargeBudget_eq, chargeBudget_eq, nd_bind_one h2, nd_bind_one h2, chargeTail_eq true _ rfl,
    chargeTail_eq false _ rfl]
  split_ifs
  · refine nd_bind_congr ?_
    exact endTimeslice_rr (σ := { updSc σ σ.curSc y n with consumedTime := 0 }) (x := y) (n := n)
      (by simp [updK]) hy
  · rfl

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **FL4's `end_timeslice` with a round-robin current SC** (period word 0)
does not depend on `can_timeout_fault`. -/
theorem end_timeslice_rr (s : S) (a : A) {sc : U64} (hsc : sched.cur_sc st s = ok sc)
    (hrr : L.rperiod s sc = 0#u64) :
    sched.end_timeslice st ar s a true = sched.end_timeslice st ar s a false := by
  obtain ⟨ct, hct, -⟩ := spec_exists (sched.cur_thread.spec' (L := L) s)
  obtain ⟨rr, hr, err⟩ := spec_exists (sporadic.is_round_robin.spec (L := L) s sc)
  rw [hrr] at err
  simp only [decide_true] at err
  subst err
  unfold sched.end_timeslice
  rw [hsc, hct]
  simp only [bind_ok]
  rw [hr]
  simp only [bind_ok, ↓reduceIte, Bool.false_eq_true]

/-- **`charge_budget` with `can_timeout_fault = true` and a round-robin
current SC** is `charge_budget` with `can_timeout_fault = false`, on both
sides (module docstring; `charge_budget_refinesF`'s premises). -/
theorem charge_budget_rr {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    (htw : L.mem s (scW (nodeW st s c layout.node.CUR_SC) 24#u64) = nodeW st s c layout.node.CUR_THREAD)
    (hidle : (nodeW st s c layout.node.IDLE_SC).bv = σ.idleSc)
    (hact : (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hnr : (nodeW st s c layout.node.CUR_THREAD).bv ∉ σ.releaseQueue)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hid : (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc)
    (hp : ∀ x n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → x.scPeriod = 0)
    (used : U64) :
    sched.charge_budget st ar s a used true = sched.charge_budget st ar s a used false ∧
      Fl4Spec.chargeBudget (Z := Unit) used.bv true σ = Fl4Spec.chargeBudget used.bv false σ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  set sc := nodeW st s c layout.node.CUR_SC with hscd
  set ct := nodeW st s c layout.node.CUR_THREAD with hctd
  have hct : ct ∈ T := hc.curT
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hscC
  have hx' := hx.strong (hact hid x n hk)
  have ecs : σ.curSc = sc.bv := hs.curSc
  have hp0 : x.scPeriod = 0 := hp x n hk
  have hkc : σ.kheap σ.curSc = some (.schedContext x n) := by rw [ecs]; exact hk
  obtain ⟨y, hy, h2⟩ := chargeHead_rr used.bv hkc hp0 (by rw [ecs]; exact hid) hx'.refills (refills_ne' hx'.wf)
  have hb : decide (sc ≠ nodeW st s c layout.node.IDLE_SC) = decide (sc.bv ≠ σ.idleSc) := by
    rw [← hidle]
    apply decide_eq_decide.2
    exact ⟨fun h e => h (eq_of_bv e), fun h e => h (by rw [e])⟩
  have H := charge_head_refinesK s a σ hS hR hN hI hscC htw hact hnr hmrt hmb used _ hb
  refine ⟨?_, chargeBudget_rr used.bv hkc hp0 (by rw [ecs]; exact hid) hx'.refills (refills_ne' hx'.wf)⟩
  obtain ⟨v1, hv1, ev1⟩ := spec_exists (sched.cur_sc.spec' (L := L) s)
  obtain ⟨v2, hv2, ev2⟩ := spec_exists (sched.idle_sc.spec' (L := L) s)
  rw [hc.cur] at ev1 ev2
  subst ev1 ev2
  unfold sched.charge_budget
  rw [hv1, hv2]
  simp only [bind_ok]
  rw [sc_ne_eq]
  simp only [bind_ok]
  refine bind_congr_spec H ?_
  rintro s2 ⟨σ2', h2', hS2, -, -, -, hK, -, -⟩
  obtain ⟨hcs2, hcc, -, -, -, -, -, -, -, -⟩ := hK
  have e2 : σ2' = updSc σ σ.curSc y n := pair_eq (h2.symm.trans h2')
  have hc2 := hS2.lists.choose_spec.choose_spec.1.cur
  obtain ⟨s3, hs3e, hs3⟩ := spec_exists (sched.set_consumed.spec' (L := L) s2 0#u64)
  rw [hc2] at hs3
  subst hs3
  rw [hs3e]
  simp only [bind_ok]
  obtain ⟨hS3, -, -⟩ := hS2.set_node_consumed 0#u64
  obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
  have e1 : nodeW st (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64) c layout.node.CUR_THREAD = ct :=
    eq_of_bv (by rw [← hs3.curThread]; exact hcc.trans hs.curThread)
  have e3 : nodeW st (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64) c layout.node.CUR_SC = sc :=
    eq_of_bv (by rw [← hs3.curSc]; exact hcs2.trans ecs)
  -- the period word after the head is 0
  have hper3 : L.rperiod (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64) sc = 0#u64 := by
    obtain ⟨y3, n3, hk3, hy3⟩ := hs3.scs sc hscC
    have hk3' : ({ σ2' with consumedTime := (0#u64).bv } : Fl4Spec.State Unit).kheap sc.bv =
        some (.schedContext y n) := by
      show σ2'.kheap sc.bv = _
      rw [e2, ← ecs]; simp [updK]
    rw [hk3'] at hk3; cases hk3
    exact eq_of_bv (by rw [← hy3.period, hy]; rfl)
  obtain ⟨v3, hv3, ev3⟩ := spec_exists (sched.cur_thread.spec' (L := L) (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64))
  rw [hc3.cur, e1] at ev3
  subst ev3
  rw [hv3]
  simp only [bind_ok]
  obtain ⟨v4, hv4, ev4⟩ := spec_exists (sched.cur_sc.spec' (L := L) (L.wr s2 (L.nodeAt s2 c layout.node.CONSUMED) 0#u64))
  rw [hc3.cur, e3] at ev4
  subst ev4
  refine bind_congr_spec (sched.is_schedulable.spec' (L := L) _ ct) ?_
  intro b1 _
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte]
    rw [end_timeslice_rr _ a hv4 hper3]

end

section Spec
open Fl4Spec

/-- **No timeout fault can be raised by the charge**: the current thread has
no endpoint cap as its timeout handler, or the current SC is round-robin. -/
def NoTmoSend (σ : State Unit) : Prop :=
  (∀ xt, σ.kheap σ.curThread = some (.tcb xt) → isEpCap xt.tcbTimeoutHandler = false) ∨
    (∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod = 0)

theorem NoTmoSend.of_eq {σ σ' : State Unit} (h : NoTmoSend σ) (ek : σ'.kheap = σ.kheap)
    (ect : σ'.curThread = σ.curThread) (ecs : σ'.curSc = σ.curSc) : NoTmoSend σ' := by
  unfold NoTmoSend; rw [ek, ect, ecs]; exact h

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

/-- The current SC of a non-idle current thread under `CurInv` is not the
idle SC (`Inv.back`, `ActIdle`). -/
theorem curSc_ne_idleSc_of {σ : Fl4Spec.State Unit} (hI : Inv σ) (hA : ActIdle σ) (hC : CurInv σ)
    (hni : σ.curThread ≠ σ.idleThread) : σ.curSc ≠ σ.idleSc := by
  intro e
  obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
  obtain ⟨y, n, hky, hyt⟩ := hI.back _ xt _ hkt hxs
  obtain ⟨xi, hki, hxi, -, -⟩ := hA.2
  rw [← e] at hxi
  obtain ⟨y', n', hky', hyt'⟩ := hI.back _ xi _ hki hxi
  rw [hky] at hky'; cases hky'
  exact hni (Option.some.inj (hyt.symm.trans hyt'))

set_option maxHeartbeats 8000000 in
/-- **`charge_budget` with `can_timeout_fault = true` at `J`, round-robin
current SC** (module docstring): `JAtZ.chargeBudgetJ` through
`charge_budget_rr`. -/
theorem JAtZ.chargeBudgetRJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hp : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod = 0)
    (used : U64) :
    sched.charge_budget st arI s a used true ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv true σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, htw, -, hact, hnr, -⟩ := CurInv.facts hS J.inv hC
  have hid := curSc_ne_idleSc_of J.inv J.act hC hni
  obtain ⟨e1, e2⟩ := charge_budget_rr (ar := arI) s a σ hS hR J.nsc J.inv hscC htw hS.idle hact hnr hmrt hmb
    (by rw [← hs.curSc]; exact hid) (fun x n hx => hp x n (by rw [hs.curSc]; exact hx)) used
  rw [e1]
  refine WP.spec_mono (J.chargeBudgetJ hAT hC hni hnsw hmrt hmb used) ?_
  rintro r ⟨h1, σ', h2, h3⟩
  exact ⟨h1, σ', by rw [e2]; exact h2, h3⟩

/-- **`charge_budget` with `can_timeout_fault = true` at `J` when no timeout
fault can be raised** (`NoTmoSend`: no endpoint timeout handler, or a
round-robin current SC). -/
theorem JAtZ.chargeBudgetTJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread)
    (hnsw : σ.schedulerAction ≠ .switchThread σ.curThread)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hnt : NoTmoSend σ) (used : U64) :
    sched.charge_budget st arI s a used true ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.chargeBudget (Z := Unit) used.bv true σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  rcases hnt with h | h
  · exact J.chargeBudgetNJ hAT hC hni hnsw hmrt hmb h used
  · exact J.chargeBudgetRJ hAT hC hni hnsw hmrt hmb h used

end

end

end Fl4Proofs.P3
