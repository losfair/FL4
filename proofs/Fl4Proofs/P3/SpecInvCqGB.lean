/-
P3 (DESIGN.md §9), invariant line G1 (ctq11): **preemption_path's `hB` from
`CK`** (ctq10 handoff item 5, the bridge; spec side only).

ctq8's `ebx_preemptionPath_p` needs `hB : schedulable ct → BC` at the
preemption state, where CurScT may be gone (a preempted deletion may unbind
or return ct's SC). The weaker l4v fact `CK` ("ct's SC is `cur_sc` or none",
the SC half of `cur_sc_tcb` / `ct_schedulable`) suffices with sb2's ScBackS:
a schedulable ct has an SC (`schedulable_sc`), so it is `cur_sc`, whose
`sc_tcb` is ct (**`bc_of_ck`**). `ck_of_curScT`: CurScT gives `CK`.
Carrying `CK` to the preemption outcomes is KENTRY-PLAN ctq11 handoff 2.
-/
import Fl4Proofs.P3.SpecInvCqB2
open Classical

namespace Fl4Proofs.P3.SInvQ.R11
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

/-- **CK**: the current thread's SC (if a TCB) is `cur_sc` or none. -/
abbrev CK (s : State Unit) : Prop :=
  ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = none ∨ x.tcbSchedContext = some s.curSc

theorem ck_of_curScT {σ : State Unit} (hC : CurScT σ) : CK σ := fun x hx => Or.inr (hC x hx)

/-- A schedulable thread is a TCB with an SC. -/
theorem schedulable_sc {σ : State Unit} {t : ObjRef} (hs : schedulable t σ = true) :
    ∃ x c, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c := by
  unfold schedulable at hs
  obtain ⟨-, h2, -⟩ := of_decide_eq_true hs
  unfold optPred optMap tcbsOf tcbsOfKh optMap at h2
  revert h2
  cases e : σ.kheap t with
  | none => simp
  | some o =>
    cases o
    case tcb x =>
      intro h2
      refine ⟨x, ?_⟩
      cases hc : x.tcbSchedContext with
      | none => simp [tcbOf, hc] at h2
      | some c => exact ⟨c, rfl, rfl⟩
    all_goals simp [tcbOf]

/-- **`BC` from `CK` and ScBack** where ct is schedulable (ctq8's `hB`). -/
theorem bc_of_ck {σ : State Unit} (hK : CK σ) (hS : SInvB.ScBackS σ) (hs : schedulable σ.curThread σ = true) :
    BC σ := by
  obtain ⟨x, c, hx, hc⟩ := schedulable_sc hs
  have hc' : x.tcbSchedContext = some σ.curSc := by
    rcases hK x hx with h | h
    · rw [h] at hc; cases hc
    · exact h
  obtain ⟨y0, k0, hk0, ht0, -⟩ := hS σ.curThread x σ.curSc hx hc'
  intro y n t hk ht
  rw [hk0] at hk
  cases hk
  rw [ht0] at ht
  cases ht
  rfl

end

end Fl4Proofs.P3.SInvQ.R11
