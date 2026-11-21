/-
P3 (DESIGN.md §9), kernel entry: **`budget_ok` at `J` when it stops the
system call** (KENTRY-PLAN item 10, the false branch), for a current thread
without an endpoint timeout handler.

* `OTK.tcb_false`: an object step with no thread-state change keeps a TCB a
  TCB with its state.
* `JAtZ.restartRunJ`: XTopJointTcbInstall's `JAtZ.restartJ` (the current
  thread's `set_thread_state Restart` at `J`) from a runnable current thread
  instead of `Entered` (after the charge a reschedule is pending).
* `JAtZ.budgetOkF`: from `JAtZ` at kernel entry with `Entered`, `CurInv` and
  `NoTmoSend` (no endpoint timeout handler of the current thread, or a
  round-robin current SC: ScChargeR), when FL4's `budget_ok`
  returns `false`, l4v's `update_time_stamp; check_budget_restart` returns
  `false` and `JAtZ` holds after: ScChargeH's `JAtZ.timestampJH` (the hole
  after `update_timestamp`, where `OffOK` fails), `JHole.checkBudgetF` (the
  insufficient head, the charge with `can_timeout_fault = true`), then the
  restart of the still-runnable current thread (`restartRunJ`) or nothing.
  With an endpoint timeout handler and a non-round-robin SC the charge sends
  the current thread's timeout fault (KENTRY-PLAN (a), not covered).
-/
import Fl4Proofs.P3.ScChargeH
import Fl4Proofs.P3.XTopJointBudgetOk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- A `TKObj False` step keeps a TCB a TCB with the same thread state. -/
theorem OTK.tcb_false {x : Fl4Spec.Tcb} {o' : Option Fl4Spec.KernelObject} (h : OTK False (some (.tcb x)) o') :
    ∃ y, o' = some (.tcb y) ∧ y.tcbState = x.tcbState := by
  cases o' with
  | none => exact absurd h (by simp [OTK])
  | some o =>
    simp only [OTK] at h
    rcases h with rfl | ⟨x1, y, e1, rfl, -, hs⟩ | ⟨_, _, _, e, -⟩ | ⟨_, _, e, -⟩ | ⟨_, _, e, -⟩
    · exact ⟨x, rfl, rfl⟩
    · cases e1
      exact ⟨y, rfl, hs.elim id fun h => h.1.elim⟩
    all_goals cases e

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **The current thread's restart at `J` from a runnable current thread**
(XTopJointTcbInstall's `JAtZ.restartJ` without `Entered`). -/
theorem JAtZ.restartRunJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x))
    (hrun : Fl4Spec.runnable x.tcbState = true) :
    ∃ s1 σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv ∧
      sched.set_thread_state st s ct sched.TS_RESTART = ok s1 ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 a σ1 := by
  obtain ⟨hcur, -, -⟩ := J.curEq hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  obtain ⟨s1, σ1, -, hs1, hst1, -, -, -, -, -⟩ :=
    restart_dstate Z.th J.xtop.rel.1 s σ Z.G hDS ct hct hcur htcb J.kern.act
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    have hst := hst1
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  have h := XTopAt.restart J.xtop hcur hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨hX1, hSS, hk1⟩ := h
  obtain ⟨hkb, hkz⟩ := kback_ksz_upd (σ' := Notif.stsAct (Notif.updK σ ct.bv
    (.tcb { x with tcbState := .restart })) ct.bv) hk (by rw [stsAct_kheap]; rfl)
  obtain ⟨Ac', Lst', J1⟩ := J.restartSJ (jStepHyps arI) hcur hk htcb hrun hs1
  refine ⟨s1, σ1, hst1, e, hs1, Ac', Lst', D, ?_⟩
  subst e
  exact J1

set_option maxHeartbeats 16000000 in
/-- **`budget_ok` at `J`, when it stops the system call** (KENTRY-PLAN item 10,
false branch; module docstring): the clock [P] (`NowAgree`), one domain, the
platform's `MAX_RELEASE_TIME`/`MIN_BUDGET` [P] (`hmrt`, `hmb`), and at kernel
entry `Entered`, `CurInv` and `NoTmoSend` (`hnt`: no endpoint cap as the
current thread's timeout handler, or a round-robin current SC). -/
theorem JAtZ.budgetOkF (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hnow : NowAgree arI a σ) (hni : Entered σ)
    (hC : CurInv σ)
    (hmrt : ∀ a : A, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hnt : NoTmoSend σ) :
    syscall.budget_ok st arI s a ⦃ r => r.1 = false → ∃ σ',
      (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ = ({(false, σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ' ⦄ := by
  unfold syscall.budget_ok
  refine WP.spec_bind (J.timestampJH hAK hA hnd hnow) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, h1, hk1, -, -, hct1, -, hum1, -, hH⟩
  have Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s a σ s1 a1 σ1 := hH σ1.machineState a1 hum1 id
  obtain ⟨-, -, -, -, ekh, ect, eact, eidle, -, -, -, -⟩ := Hh.sfacts
  have hres1 : σ1.schedulerAction = .resumeCurThread := eact.trans hni.2
  have hC1 : CurInv σ1 := Hh.cur.resolve_left (by rw [hres1]; exact fun h => by cases h)
  have hni1 : σ1.curThread ≠ σ1.idleThread := by rw [ect, eidle]; exact hni.1
  have hnsw1 : σ1.schedulerAction ≠ .switchThread σ1.curThread := by rw [hres1]; exact fun h => by cases h
  have hnt1 : NoTmoSend σ1 := hnt.of_eq ekh ect (by obtain ⟨ms, tm, cn, -, e⟩ := Hh.spec; rw [e])
  unfold sched.check_budget_restart
  refine WP.spec_bind (Hh.checkBudgetF hA hC1 hni1 hnsw1 (hmrt a1) (hmb a1) hnt1) ?_
  rintro ⟨r, s2, a2⟩ hB
  step with sched.cur_thread.spec' as ⟨ct, hct⟩
  by_cases hr : r = true
  · subst hr
    rw [if_pos rfl]
    refine (WP.spec_ok _).2 ?_
    intro h; exact absurd h (by simp)
  · have hr' : r = false := by simpa using hr
    subst hr'
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨ha2, σ2, hcb, hK, Lst2, J2⟩ := hB rfl
    simp only at ha2 J2
    subst ha2
    have hct' : sched.cur_thread st s2 = ok ct := by rw [hct]; exact cur_thread_eq s2
    obtain ⟨hcur2, -, -⟩ := J2.curEq hct'
    obtain ⟨xt, hkt, -, -⟩ := hC1.tcb
    obtain ⟨y, hky, hys⟩ := OTK.tcb_false (x := xt) (o' := σ2.kheap σ2.curThread)
      (by rw [← hkt, hK.ct]; exact hK.kh σ1.curThread)
    have hky2 : σ2.kheap σ2.curThread = some (.tcb y) := hky
    have hk2 : σ2.kheap ct.bv = some (.tcb y) := by rw [← hcur2]; exact hky2
    have htcb : Z.th ct = some .tcb := (J2.xtop.curTcb hcur2).1
    have hctT : ct ∈ Z.T := J2.thT _ htcb
    have hR2 := J2.xtop.fin.1.1.2.2.1
    have hsp : Fl4Spec.checkBudgetRestart (Z := Unit) σ1 =
        (if ¬ false = true ∧ Fl4Spec.runnable y.tcbState = true then
          (Fl4Spec.setThreadState σ2.curThread .restart >>= fun _ => pure false) σ2
        else ({(false, σ2)}, False)) := by
      unfold Fl4Spec.checkBudgetRestart
      rw [Notif.nd_bind_one hcb, nd_gets_bind, Notif.nd_bind_one (getThreadState_eq hky2)]
      unfold Fl4Spec.NonDet.when
      split_ifs <;> first
        | rfl
        | (rw [Notif.nd_bind_one (rfl : Fl4Spec.NonDet.pure () σ2 = ({((), σ2)}, False))]; rfl)
        | simp_all
    have hsp0 : (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ =
        Fl4Spec.checkBudgetRestart (Z := Unit) σ1 := Notif.nd_bind_one h1 _
    step with is_runnable_spec as ⟨b, hb⟩
    have hb' : b = Fl4Spec.runnable y.tcbState := by
      rw [hb, Bool.eq_iff_iff, decide_eq_true_iff]; exact runnable_iff (hR2.at_tcb hctT hk2).st
    subst hb'
    by_cases hrun : Fl4Spec.runnable y.tcbState = true
    · simp only [hrun, ↓reduceIte]
      obtain ⟨s3, σ3, hst, -, hs3, Ac3, Lst3, D3, J3⟩ := J2.restartRunJ hct' hk2 hrun
      rw [hs3]
      simp only [bind_ok]
      refine (WP.spec_ok _).2 fun _ => ?_
      refine ⟨σ3, ?_, Ac3, Lst3, D3, J3⟩
      rw [hsp0, hsp, if_pos ⟨Bool.false_ne_true, hrun⟩, Notif.nd_bind_one hst]; rfl
    · simp only [Bool.not_eq_true] at hrun
      simp only [hrun, Bool.false_eq_true, ↓reduceIte]
      refine (WP.spec_ok _).2 fun _ => ?_
      exact ⟨σ2, by rw [hsp0, hsp, if_neg (fun h => by rw [hrun] at h; exact Bool.false_ne_true h.2)],
        Ac, Lst2, D, J2⟩

end

end

end Fl4Proofs.P3
