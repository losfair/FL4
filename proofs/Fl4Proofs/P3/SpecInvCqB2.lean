/-
P3 (DESIGN.md §9), invariant line G1 (ctq8): **the receive side, part 1**
(KENTRY-PLAN ctq7 handoff 2; spec side only, outside the JAtZ cone).

* `bc_of_curScT`: ctq8's `BC` (the current SC is bound to the current thread
  only) from ctq5's `CurScT` and sb2's `ScBackS` when the current thread is
  schedulable: what `eb_chargeBudget_p` / `eb_checkBudget_p` need at the front.
* `md_skip`: `maybe_donate_sc t n` changes nothing when `t` is a TCB with an SC.
* **`eb_receiveSignal_ct : IKp (EB true) σ (receive_signal ct cap bl)`** given
  `CurScT σ`: the blocking arm is ctq7's `eb_receiveSignalBlocked_p` (ct has
  `NPQ` under `EB true`); in the active arm the badge write and the
  notification write keep ct's SC (ctq5's `cs_auto` with a constant `g`), so
  the donation to ct is skipped and nothing enqueues or postpones ct.
-/
import Fl4Proofs.P3.SpecInvCqB1
import Fl4Proofs.P3.SpecInvSbK
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- **`BC` from CurScT and ScBack** at a state where the current thread is schedulable. -/
theorem bc_of_curScT {σ : State Unit} (hC : CurScT σ) (hS : SInvB.ScBackS σ)
    (hs : schedulable σ.curThread σ = true) : BC σ := by
  obtain ⟨x, hx, -⟩ := schedulable_rn hs
  obtain ⟨y0, k0, hk0, ht0, -⟩ := hS σ.curThread x σ.curSc hx (hC x hx)
  intro y n t hk ht
  rw [hk0] at hk
  cases hk
  rw [ht0] at ht
  cases ht
  rfl

/-- `maybe_donate_sc t n` of a TCB with an SC changes nothing. -/
theorem md_skip (t n : ObjRef) (σ : State Unit) (h : ∀ x, σ.kheap t = some (.tcb x) → x.tcbSchedContext ≠ none)
    {y : Unit × State Unit} (hy : y ∈ (maybeDonateSc (Z := Unit) t n σ).1) : y.2 = σ := by
  unfold maybeDonateSc at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  try dsimp only at hy
  unfold NonDet.when at hy
  rw [if_neg (h x hx)] at hy
  rw [Set.mem_singleton_iff.1 hy]

/-- **`receive_signal` of the current thread** keeps `EB true` (module docstring). -/
theorem eb_receiveSignal_ct (cap : Cap) (isBlocking : Bool) (σ : State Unit) (hC : CurScT σ) :
    IKp (EB true) σ (receiveSignal (Z := Unit) σ.curThread cap isBlocking) := by
  unfold receiveSignal
  intro hσ y hy
  try dsimp only at hy
  split at hy
  swap
  · obtain ⟨z, hz, -⟩ := hy
    exact hz.elim
  obtain ⟨z, hz, hy⟩ := hy
  have ez : z.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz
  obtain ⟨np, s1⟩ := z
  simp only at ez; subst s1
  obtain ⟨w, hw, hy⟩ := hy
  have ew : w.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hw
  obtain ⟨ntfn, s2⟩ := w
  simp only at ew; subst s2
  cases hn : ntfn.ntfnObj with
  | idleNtfn =>
    simp only [hn] at hy
    exact eb_receiveSignalBlocked_p _ _ _ σ (npq_ct hσ) hσ y hy
  | waitingNtfn q =>
    simp only [hn] at hy
    exact eb_receiveSignalBlocked_p _ _ _ σ (npq_ct hσ) hσ y hy
  | activeNtfn bd =>
    simp only [hn] at hy
    obtain ⟨u1, hu1, hy⟩ := hy
    have hE1 : EB true u1.2 := by
      refine (?_ : EBK true _) σ hσ u1 hu1
      eb_auto
    have hC1 : CS (fun _ => some σ.curSc) u1.2 := by
      refine (?_ : IK (CS (fun _ => some σ.curSc)) _) σ hC u1 hu1
      cs_auto
    have hT1 : CTh σ.curThread u1.2 := ct_asUser _ _ _ σ rfl u1 hu1
    obtain ⟨u2, hu2, hy⟩ := hy
    have hE2 : EB true u2.2 := by
      refine (?_ : EBK true _) u1.2 hE1 u2 hu2
      eb_auto
    have hC2 : CS (fun _ => some σ.curSc) u2.2 := by
      refine (?_ : IK (CS (fun _ => some σ.curSc)) _) u1.2 hC1 u2 hu2
      cs_auto
    have hT2 : CTh σ.curThread u2.2 := by
      refine (?_ : IK (CTh σ.curThread) _) u1.2 hT1 u2 hu2
      repeat' (first | ik_step0 | ik_unfold)
    obtain ⟨u3, hu3, hy⟩ := hy
    have e3 : u3.2 = u2.2 := md_skip _ _ u2.2 (fun x hx => by
      have hT2' : u2.2.curThread = σ.curThread := hT2
      rw [← hT2'] at hx
      rw [hC2 x hx]; simp) hu3
    obtain ⟨v3, s3⟩ := u3
    simp only at e3; subst s3
    refine (?_ : EBK true _) u2.2 hE2 y hy
    eb_auto

/-- **`complete_signal` of the current thread** (receive_ipc's active bound
notification): `EB true` to `EB false`, given at its start that the current
thread still has an SC (the donation is skipped) or the action is neither
`resume_cur_thread` nor a switch to it (`AN ct`: ctq7's `mdk_maybeDonateSc` at
`k = false`; the donated SC may postpone the current thread). -/
theorem eb_completeSignal_ct (n : ObjRef) (σ : State Unit)
    (hD : (∃ c, CS (fun _ => some c) σ) ∨ AN σ.curThread σ) :
    HKp (EB true) (EB false) σ (completeSignal (Z := Unit) n σ.curThread) := by
  unfold completeSignal
  intro hσ y ⟨w, hw, hy⟩
  have ew : w.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hw
  obtain ⟨ntfn, s2⟩ := w
  simp only at ew; subst s2
  cases hn : ntfn.ntfnObj with
  | idleNtfn => simp only [hn] at hy; exact hy.elim
  | waitingNtfn q => simp only [hn] at hy; exact hy.elim
  | activeNtfn bd =>
    simp only [hn] at hy
    obtain ⟨u1, hu1, hy⟩ := hy
    have hE1 : EB true u1.2 := by
      refine (?_ : EBK true _) σ hσ u1 hu1
      eb_auto
    have hT1 : CTh σ.curThread u1.2 := ct_asUser _ _ _ σ rfl u1 hu1
    have hD1 : (∃ c, CS (fun _ => some c) u1.2) ∨ AN σ.curThread u1.2 := by
      rcases hD with ⟨c, hc⟩ | ha
      · refine Or.inl ⟨c, ?_⟩
        refine (?_ : IK (CS (fun _ => some c)) _) σ hc u1 hu1
        cs_auto
      · exact Or.inr (an_asUser _ _ _ σ ha u1 hu1)
    obtain ⟨u2, hu2, hy⟩ := hy
    have hE2 : EB true u2.2 := by
      refine (?_ : EBK true _) u1.2 hE1 u2 hu2
      eb_auto
    have hT2 : CTh σ.curThread u2.2 := by
      refine (?_ : IK (CTh σ.curThread) _) u1.2 hT1 u2 hu2
      repeat' (first | ik_step0 | ik_unfold)
    have hD2 : (∃ c, CS (fun _ => some c) u2.2) ∨ AN σ.curThread u2.2 := by
      rcases hD1 with ⟨c, hc⟩ | ha
      · refine Or.inl ⟨c, ?_⟩
        refine (?_ : IK (CS (fun _ => some c)) _) u1.2 hc u2 hu2
        cs_auto
      · refine Or.inr ?_
        refine (?_ : IK (AN σ.curThread) _) u1.2 ha u2 hu2
        an_auto
    obtain ⟨u3, hu3, hy⟩ := hy
    have h3 : EB false u3.2 := by
      rcases hD2 with ⟨c, hc⟩ | ha
      · have e3 : u3.2 = u2.2 := md_skip _ _ u2.2 (fun x hx => by
          have hT2' : u2.2.curThread = σ.curThread := hT2
          rw [← hT2'] at hx
          rw [hc x hx]; simp) hu3
        rw [e3]; exact eb_weak hE2
      · exact ⟨sq4_of (tq_maybeDonateSc _ _) (sa_maybeDonateSc _ _) (q4_maybeDonateSc _ _) u2.2 hE2.1 u3 hu3,
          mdk_maybeDonateSc (k := false) _ _ u2.2 ⟨rbk_weak hE2.2, hE2.1.1.1, ha, fun e => by cases e⟩ u3 hu3⟩
    refine (?_ : EBK false _) u3.2 h3 y hy
    eb_auto

end

end Fl4Proofs.P3.SInvQ
