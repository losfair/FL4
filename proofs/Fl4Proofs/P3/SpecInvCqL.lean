/-
P3 (DESIGN.md §9), invariant line G1 (ctq4): **il1's IfLiveT gives ctq3's
IfLiveTN** (spec side only), so the untyped / MakePool steps of TQ
(`rqDet_of_live`, `tq_invokeUntyped`, `q3_fl4PerformInvocation`) take the
carried IfLiveT (il2) instead of the local [J] IfLiveTN; and **`aw_of`**: `schedule`'s
entry invariant `AW` from SchedQ, ctnq1's T4 and vi2's ValidIdle.
-/
import Fl4Proofs.P3.SpecInvCqU
import Fl4Proofs.P3.SpecInvNtfnQL
import Fl4Proofs.P3.SpecInvCqT
import Fl4Proofs.P3.SpecInvQDomK
import Fl4Proofs.P3.SpecInvViA
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

/-- **IfLiveT → IfLiveTN**: a thread neither Inactive nor idle is live; il1's
thread cap names it. -/
theorem ifLiveTN_of_ifLiveT {σ : State Unit} (h : IfLiveT σ) : IfLiveTN σ := by
  intro t y hy hs _
  refine ifLiveT_objRefs h hy ?_
  cases e : y.tcbState <;> simp_all [liveSt]

/-- **`AW` from the carried fields**: T4 puts every TCB in domain 0 =
`cur_domain`; ValidIdle gives the idle TCB the state `IdleThreadState`. -/
theorem aw_of {σ : State Unit} (hq : SchedQ σ) (h4 : T4 σ) (hv : SInvI.ValidIdle σ) : AW σ := by
  refine ⟨hq, fun t x hx => ?_, fun x hx => ?_⟩
  · rw [h4.2.1]; exact h4.2.2 t x hx
  · obtain ⟨y, hy, hs, -⟩ := SInvI.vi_idle hv
    rw [hy] at hx; cases hx; rw [hs]; rfl

end

end Fl4Proofs.P3.SInvQ
