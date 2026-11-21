/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN budtr): **`budget_ok` at `J`
when it stops the system call and the current thread's timeout fault goes
to a receiver waiting on its handler's endpoint** (the case XTopJointBudgetT
leaves: `hcb` there needs the handler endpoint idle or sending).

* `JAtZ.budgetOkTR`: scripted copy of XTopJointBudgetT's `JAtZ.budgetOkT`
  with the handler endpoint receiving (`hkl : ∃ l, kheap p = recvEP l`) for
  `hcb`, kp17's ScChargeTR `JHole.checkBudgetTR` (the action
  `resumeCurThread`, its `Or.inl` case) for `JHole.checkBudgetT`, and the
  platform facts `hmax`/`htu` [P] that `checkBudgetTR` takes
  (`JEntryGlob.maxTU`/`tu` at the top).
-/
import Fl4Proofs.P3.ScChargeTR
import Fl4Proofs.P3.XTopJointBudgetT
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`budget_ok` at `J`, when it stops the system call and the current
thread's timeout fault goes to a receiver waiting on its handler's endpoint**
(module docstring; the clock [P] `NowAgree`, one domain, the platform's
`MAX_RELEASE_TIME`/`MIN_BUDGET`/`maxTicksToUs`/`ticks_to_us` [P]). -/
theorem JAtZ.budgetOkTR (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hnow : NowAgree arI a σ) (hni : Entered σ)
    (hC : CurInv σ)
    (hmrt : ∀ a : A, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xt))
    (hrr : xt.tcbState = .running ∨ xt.tcbState = .restart)
    {p bd : Fl4Spec.Word} {r : Fl4Spec.CapRights} (hth : xt.tcbTimeoutHandler = .endpointCap p bd r)
    (hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0)
    (hkl : ∃ l, σ.kheap p = some (.endpoint (.recvEP l))) :
    syscall.budget_ok st arI s a ⦃ res => res.1 = false → ∃ z ∈
      ((Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ).1, z.1 = false ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' res.2.1 res.2.2 z.2 ⦄ := by
  unfold syscall.budget_ok
  refine WP.spec_bind (J.timestampJH hAK hA hnd hnow) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, h1, hk1, hcs1, hrl1, hct1, -, hum1, -, hH⟩
  have Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s a σ s1 a1 σ1 := hH σ1.machineState a1 hum1 id
  obtain ⟨-, -, -, -, ekh, ect, eact, eidle, -, -, -, -⟩ := Hh.sfacts
  obtain ⟨ms1, tm1, cn1, -, eσ1⟩ := Hh.spec
  have erq : σ1.readyQueues = σ.readyQueues := by rw [eσ1]
  have hres1 : σ1.schedulerAction = .resumeCurThread := eact.trans hni.2
  have hC1 : CurInv σ1 := Hh.cur.resolve_left (by rw [hres1]; exact fun h => by cases h)
  have hni1 : σ1.curThread ≠ σ1.idleThread := by rw [ect, eidle]; exact hni.1
  have hkt1 : σ1.kheap σ1.curThread = some (.tcb xt) := by rw [ekh, ect]; exact hkt
  have hper1 : ∀ x n, σ1.kheap σ1.curSc = some (.schedContext x n) → x.scPeriod ≠ 0 := fun x n h =>
    hper x n (by rw [← ekh, ← hcs1]; exact h)
  have hkl1 : ∃ l, σ1.kheap p = some (.endpoint (.recvEP l)) := by rw [ekh]; exact hkl
  have hnq1 : ∀ d q, σ1.curThread ∉ σ1.readyQueues d q := by rw [ect, erq]; exact hnq
  unfold sched.check_budget_restart
  refine WP.spec_bind (Hh.checkBudgetTR hA hmax htu hC1 hni1 (Or.inl hres1) hnq1 (hmrt a1) (hmb a1) hkt1 hrr hth hper1 hkl1) ?_
  rintro ⟨rb, s2, a2⟩ hB
  step with sched.cur_thread.spec' as ⟨ct, hct⟩
  by_cases hr : rb = true
  · subst hr
    rw [if_pos rfl]
    refine (WP.spec_ok _).2 ?_
    intro h; exact absurd h (by simp)
  · have hr' : rb = false := by simpa using hr
    subst hr'
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨⟨zb, σ2⟩, hz, hzb, V, Ac2, Lst2, D2, J2⟩ := hB rfl
    simp only at hzb J2
    subst hzb
    have hct' : sched.cur_thread st s2 = ok ct := by rw [hct]; exact cur_thread_eq s2
    obtain ⟨hcur2, -, -⟩ := J2.curEq hct'
    have htcb : (Z.mv Z.G V).th ct = some .tcb := (J2.xtop.curTcb hcur2).1
    have hctT : ct ∈ (Z.mv Z.G V).T := J2.thT _ htcb
    have hI2 := J2.xtop.irelK J2.ks J2.buf
    obtain ⟨y, hk2, -⟩ := hI2.1.tcb ct hctT
    have hky2 : σ2.kheap σ2.curThread = some (.tcb y) := by rw [hcur2]; exact hk2
    have hR2 := J2.xtop.fin.1.1.2.2.1
    have hsp : (fun (result : Bool) => (do
          let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
          let st ← Fl4Spec.getThreadState cur
          Fl4Spec.NonDet.when (¬result = true ∧ Fl4Spec.runnable st = true) <|
            Fl4Spec.setThreadState cur .restart
          return result : Fl4Spec.SMonad Unit Bool)) false σ2 =
        (if ¬ false = true ∧ Fl4Spec.runnable y.tcbState = true then
          (Fl4Spec.setThreadState σ2.curThread .restart >>= fun _ => pure false) σ2
        else ({(false, σ2)}, False)) := by
      show (do
          let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
          let st ← Fl4Spec.getThreadState cur
          Fl4Spec.NonDet.when (¬false = true ∧ Fl4Spec.runnable st = true) <|
            Fl4Spec.setThreadState cur .restart
          return false : Fl4Spec.SMonad Unit Bool) σ2 = _
      rw [nd_gets_bind, Notif.nd_bind_one (getThreadState_eq hky2)]
      unfold Fl4Spec.NonDet.when
      split_ifs <;> first
        | rfl
        | (rw [Notif.nd_bind_one (rfl : Fl4Spec.NonDet.pure () σ2 = ({((), σ2)}, False))]; rfl)
        | simp_all
    have hsp0 : (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ =
        Fl4Spec.checkBudgetRestart (Z := Unit) σ1 := Notif.nd_bind_one h1 _
    have hmem : ∀ w, w ∈ ((fun (result : Bool) => (do
          let cur ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
          let st ← Fl4Spec.getThreadState cur
          Fl4Spec.NonDet.when (¬result = true ∧ Fl4Spec.runnable st = true) <|
            Fl4Spec.setThreadState cur .restart
          return result : Fl4Spec.SMonad Unit Bool)) false σ2).1 →
        w ∈ ((Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ).1 := by
      intro w hw
      rw [hsp0]
      unfold Fl4Spec.checkBudgetRestart
      exact mem_bind_nd (x := (false, σ2)) hz hw
    step with is_runnable_spec as ⟨b, hb⟩
    have hb' : b = Fl4Spec.runnable y.tcbState := by
      rw [hb, Bool.eq_iff_iff, decide_eq_true_iff]; exact runnable_iff (hR2.at_tcb hctT hk2).st
    subst hb'
    by_cases hrun : Fl4Spec.runnable y.tcbState = true
    · simp only [hrun, ↓reduceIte]
      obtain ⟨s3, σ3, hst, -, hs3, Ac3, Lst3, D3, J3⟩ := J2.restartRunJ hct' hk2 hrun
      rw [hs3]
      simp only [bind_ok]
      refine (WP.spec_ok _).2 fun _ => ⟨(false, σ3), hmem _ ?_, rfl, V, Ac3, Lst3, D3, J3⟩
      rw [hsp, if_pos ⟨Bool.false_ne_true, hrun⟩, Notif.nd_bind_one hst]
      exact Set.mem_singleton _
    · simp only [Bool.not_eq_true] at hrun
      simp only [hrun, Bool.false_eq_true, ↓reduceIte]
      refine (WP.spec_ok _).2 fun _ => ⟨(false, σ2), hmem _ ?_, rfl, V, Ac2, Lst2, D2, J2⟩
      rw [hsp, if_neg (fun h => by rw [hrun] at h; exact Bool.false_ne_true h.2)]
      exact Set.mem_singleton _

end

end Fl4Proofs.P3
