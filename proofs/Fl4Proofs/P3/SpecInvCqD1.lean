/-
P3 (DESIGN.md §9), invariant line G1 (ctq13): **EB across the performs**,
part 6: `restart` and the Resume / WriteRegisters / CopyRegisters arms
(spec side only, outside the JAtZ cone).

These arms run only with `firstPhase = false` (thread caps are rejected in
the first phase), so `EB false` after them is what is needed.

* At the perform (`RPq`): `EB false`, no switch pending (`Simple`, ctq5's EX),
  sb2's `ScInv`, and the current thread is not the idle thread (the shell's
  `set_thread_state ct Restart` makes ct runnable while idle is in its idle
  state, vi3).
* `restart t` acts only when `t` is read neither runnable nor idle. Then
  `AN t` (`t` not the switch target: `Simple`; under `resume_cur_thread` the
  current thread is a runnable TCB or idle (`CB`), so not `t`). `AN t` and
  the binding frame (sb2's `BRs`) are kept by `cancel_ipc`,
  `set_thread_state t Restart` and the refill check; at
  `sched_context_resume sc` (`sc` = `t`'s SC, read at the start) sb2's
  `ScBackS` gives `sc_tcb sc = t`, so ctq8's `rbf_schedContextResume_p`
  applies; `test_possible_switch_to t` is ctq7's `eb_possibleSwitchTo_p`
  (`k = false`).
* `RPq` is kept by `as_user`, `arch_post_modify_registers` and `suspend`
  (the last with `Simple`: SpecInvCqC2's `eb_suspend_p`).
-/
import Fl4Proofs.P3.SpecInvCqC5
import Fl4Proofs.P3.SpecInvSgI3
open Classical

namespace Fl4Proofs.P3.SInvQ.P13
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.P12

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The precondition -/

/-- At the Resume / WriteRegisters / CopyRegisters perform. -/
abbrev RPq (s : State Unit) : Prop :=
  EB false s ∧ Simple s ∧ SInvB.ScInv s ∧ s.curThread ≠ s.idleThread

theorem rp_of {α : Type} {m : NonDet (State Unit) α} (h1 : EBK false m) (h2 : ∀ t, IK (NSw t) m)
    (h3 : SInvB.SIK m) (h4 : ∀ C, IK (CTh C) m) (h5 : ∀ N, SInvG.IdK N m) : IK RPq m := by
  intro σ h y hy
  refine ⟨h1 σ h.1 y hy, fun t => h2 t σ (h.2.1 t) y hy, h3 σ h.2.2.1 y hy, ?_⟩
  rw [h4 σ.curThread σ rfl y hy, h5 σ.idleThread σ rfl y hy]
  exact h.2.2.2

theorem an_ifCondRefillUnblockCheck (t : ObjRef) (o : Option ObjRef) (a b : Option Bool) :
    IK (AN t) (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; an_auto

/-! ## `restart` -/

/-- What `restart t` keeps between its reads and `sched_context_resume`. -/
abbrev RA (t : ObjRef) (h0 : KHeap) (s : State Unit) : Prop := EB false s ∧ AN t s ∧ SInvB.BRs h0 s

theorem ra_of {α : Type} {t : ObjRef} {h0 : KHeap} {m : NonDet (State Unit) α} (h1 : EBK false m)
    (h2 : IK (AN t) m) (h3 : SInvB.SBK h0 m) : IK (RA t h0) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2.1 y hy, h3 σ h.2.2 y hy⟩

/-- **`restart t` keeps `EB false`** (no switch pending, `ScInv`, ct not idle). -/
theorem eb_restart_p (t : ObjRef) (σ : State Unit) (hS : Simple σ) (hI : SInvB.ScInv σ)
    (hci : σ.curThread ≠ σ.idleThread) : IKp (EB false) σ (restart (Z := Unit) t) := by
  intro hσ y hy
  unfold restart at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  unfold getThreadState at hz1
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  unfold getTcbObjRef at hz2
  obtain ⟨x2, hx2, rfl⟩ := q1_mem_threadGet hz2
  rw [hx] at hx2; cases hx2
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · rename_i hc
    obtain ⟨hnr, -⟩ := hc
    have hA : AN t σ := by
      refine ⟨hS t, fun hr e => ?_⟩
      rcases hσ.2.2 hr with ⟨y0, hy0, hry⟩ | hi
      · rw [← e, hx] at hy0; cases hy0; exact hnr hry
      · exact hci hi
    have h0 : RA t σ.kheap σ := ⟨hσ, hA, SInvB.BR.refl _⟩
    obtain ⟨z3, hz3, hy⟩ := hy
    have h3 : RA t σ.kheap z3.2 :=
      ra_of (eb_of (tq_cancelIpc t) (sa_cancelIpc t) (q4_cancelIpc t) (rb_cancelIpc t)) (an_cancelIpc t t)
        (SInvB.sb_cancelIpc t) σ h0 z3 hz3
    obtain ⟨z4, hz4, hy⟩ := hy
    have h4 : RA t σ.kheap z4.2 :=
      ra_of (eb_setThreadState_r t .restart rfl) (an_setThreadState t t _) (SInvB.sb_setThreadState t _) z3.2 h3 z4 hz4
    obtain ⟨z5, hz5, hy⟩ := hy
    have h5 : RA t σ.kheap z5.2 :=
      ra_of (eb_of (tq_ifCondRefillUnblockCheck _ _ _) (sa_ifCondRefillUnblockCheck _ _ _)
          (q4_ifCondRefillUnblockCheck _ _ _) (rb_ifCondRefillUnblockCheck _ _ _))
        (an_ifCondRefillUnblockCheck t _ _ _) (SInvB.sb_ifCondRefillUnblockCheck _ _ _) z4.2 h4 z5 hz5
    obtain ⟨z6, hz6, hy⟩ := hy
    have h6 : EB false z6.2 := by
      revert hz6
      cases hsc : x.tcbSchedContext with
      | none =>
        intro hz6
        simp only [NonDet.maybeM] at hz6
        rw [Set.mem_singleton_iff.1 hz6]; exact h5.1
      | some sc =>
        intro hz6
        simp only [NonDet.maybeM] at hz6
        obtain ⟨y0, k0, hk0, ht0, -⟩ := hI.back t x sc hx hsc
        obtain ⟨y1, n1, hk1, hkp⟩ := h5.2.2.sc sc y0 k0 hk0
        have hrb : RBk false z6.2 := by
          refine rbf_schedContextResume_p sc z5.2 h5.1.1.1.1 (fun y' n' u hk hu => ?_) h5.1.2 z6 hz6
          rw [hk1] at hk; cases hk
          rw [hkp.1, ht0] at hu; cases hu
          exact h5.2.1
        exact ⟨sq4_of (tq_schedContextResume sc) (sa_schedContextResume sc) (q4_schedContextResume sc) z5.2
          h5.1.1 z6 hz6, hrb⟩
    unfold testPossibleSwitchTo at hy
    refine (ikp_gets_bind ?_) h6 y hy
    exact ikp_when _ fun hs => eb_possibleSwitchTo_p t z6.2 (schedulable_rn hs) (fun h => by cases h)
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ

theorem hk_restart (t : ObjRef) : HK RPq (EB false) (restart (Z := Unit) t) :=
  fun σ h => eb_restart_p t σ h.2.1 h.2.2.1 h.2.2.2 h.1

/-! ## `RPq` frames -/

theorem rp_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : IK RPq (asUser (Z := Unit) t u) :=
  rp_of (eb_of (tqx_asUser t u) (sa_asUser t u) (q4_asUser t u) (rb_asUser t u))
    (fun _ => by unfold asUser; p12_nsw_auto) (SInvB.sik_of_sbk fun _ => SInvB.sb_asUser t u)
    (fun C => SInvQ.ct_asUser C t u) (fun _ => SInvG.idk_asUser t u)

theorem rp_archPostModifyRegisters (cur t : ObjRef) : IK RPq (archPostModifyRegisters (Z := Unit) cur t) :=
  rp_of (eb_of (tq_archPostModifyRegisters cur t) (sa_archPostModifyRegisters cur t)
      (q4_archPostModifyRegisters cur t) (rb_archPostModifyRegisters cur t))
    (fun _ => by unfold archPostModifyRegisters asUser; p12_nsw_auto)
    (SInvB.sik_of_sbk fun _ => SInvB.sb_archPostModifyRegisters cur t)
    (fun C => SInv.ct_archPostModifyRegisters (cq := C) cur t) (fun _ => SInvG.idk_archPostModifyRegisters cur t)

theorem nsw_suspend (u t : ObjRef) : IK (NSw u) (suspend (Z := Unit) t) := by
  unfold suspend
  refine ik_bind (nsw_cancelIpc u t) fun _ => ?_
  p12_nsw_auto

theorem rp_suspend (t : ObjRef) : IK RPq (suspend (Z := Unit) t) := by
  intro σ h y hy
  refine ⟨eb_suspend_p t σ (h.2.1 t) h.1 y hy, fun u => nsw_suspend u t σ (h.2.1 u) y hy,
    SInvB.sik_of_sbk (fun _ => SInvB.sb_suspend t) σ h.2.2.1 y hy, ?_⟩
  rw [SInv.ct_suspend (cq := σ.curThread) t σ rfl y hy, SInvG.idk_suspend (N := σ.idleThread) t σ rfl y hy]
  exact h.2.2.2

theorem rp_when {m : NonDet (State Unit) Unit} (c : Prop) [Decidable c] (h : IK RPq m) :
    IK RPq (NonDet.when c m) := by
  intro σ hσ y hy
  unfold NonDet.when at hy
  split at hy
  · exact h σ hσ y hy
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ

theorem hk_whenRestart (c : Prop) [Decidable c] (t : ObjRef) :
    HK RPq (EB false) (NonDet.when c (restart (Z := Unit) t)) := by
  intro σ hσ y hy
  unfold NonDet.when at hy
  split at hy
  · exact hk_restart t σ hσ y hy
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ.1

/-! ## The arms -/

/-- **The Resume arm** keeps `EB false`. -/
theorem eb_perfResume (bl call don : Bool) (t : ObjRef) :
    HKE RPq (EB false) (fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.resume t))) := by
  simp only [fl4PerformInvocation, invokeTcb]
  refine hk_liftE ?_
  refine hk_bind (hk_restart t) fun _ => ?_
  exact fun σ h y hy => by rw [Set.mem_singleton_iff.1 hy]; exact h

/-- **The WriteRegisters arm** keeps `EB false`. -/
theorem eb_perfWriteRegisters (bl call don : Bool) (dest : ObjRef) (b : Bool) (vs : List Data)
    (a : ArchCopyRegisterSets) :
    HKE RPq (EB false)
      (fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.writeRegisters dest b vs a))) := by
  simp only [fl4PerformInvocation, invokeTcb]
  refine hk_liftE ?_
  refine hk_bind (hk_of_ik (ik_of_ro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun _ => ?_
  refine hk_bind (hk_of_ik (ik_of_ro fun _ => by unfold archGetSanitiseRegisterInfo; repeat' (first | ik_step0 | ik_unfold))) fun _ => ?_
  refine hk_bind (hk_of_ik (rp_asUser dest _)) fun _ => ?_
  refine hk_bind (hk_of_ik (rp_archPostModifyRegisters _ dest)) fun _ => ?_
  refine hk_bind (hk_whenRestart _ dest) fun _ => ?_
  exact hk_of_ik (by eb_auto)

/-- **The CopyRegisters arm** keeps `EB false`. -/
theorem eb_perfCopyRegisters (bl call don : Bool) (dest src : ObjRef) (sS rT tF tI : Bool)
    (a : ArchCopyRegisterSets) :
    HKE RPq (EB false)
      (fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.copyRegisters dest src sS rT tF tI a))) := by
  simp only [fl4PerformInvocation, invokeTcb]
  refine hk_liftE ?_
  refine hk_bind (hk_of_ik (rp_when _ (rp_suspend src))) fun _ => ?_
  refine hk_bind (hk_whenRestart _ dest) fun _ => ?_
  exact hk_of_ik (by eb_auto)

end

end Fl4Proofs.P3.SInvQ.P13
