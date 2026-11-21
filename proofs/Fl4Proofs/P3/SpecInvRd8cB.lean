/-
P3 (DESIGN.md §9), invariant line G1 (rd8c): **the decode facts the `Rdy`
performs read, carried to the perform** (spec side only, outside the JAtZ cone;
KENTRY-PLAN rd8b handoff 2).

* `CfgD inv`: a decoded configure has `MIN_BUDGET ≤ budget` (epq2's `CfgDec`) and
  `MIN_REFILLS ≤ refills` (`decode_sched_control_invocation_flags` returns
  `unat extra + MIN_REFILLS`); **`okv_fl4DecodeCfgD`**: every decode outcome
  satisfies it (state-free, so it holds at the perform). `rd_configure_d`:
  rd_configure from it.
* **`ctRdy_of`**: rd8b's `CtRdy` from rd's `CtR`, rd7's `CAx`, the current
  thread outside the release queue and the idle thread not runnable.
* **`bindRel_setThreadState`**: rd8b's `BindRel` across the shell's
  `set_thread_state ct Restart` between the decode and the perform (the bound
  ends are untouched, a `Restart` thread is not `BlkR`).
-/
import Fl4Proofs.P3.SpecInvRd8cA
import Fl4Proofs.P3.SpecInvEqC
open Classical

namespace Fl4Proofs.P3.SInvR.B8c
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Configure's decode facts -/

/-- A configure invocation's budget is at least `MIN_BUDGET` and its refill count at least
`MIN_REFILLS`. -/
def CfgD : Fl4Invocation → Prop
  | .invokeSchedControl (.invokeSchedControlConfigureFlags _ b _ mr _ _) => MIN_BUDGET ≤ b ∧ MIN_REFILLS ≤ mr
  | _ => True

theorem okv_decodeSchedControlFlagsD {w : UView} (label : Data) (args : List Data) (excaps : List Cap) :
    OkV w (fun i => CfgD (.invokeSchedControl i))
      (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags
  refine okv_unlessE_bind fun _ => okv_whenE_bind fun _ => okv_whenE_bind fun _ => okv_returnOk_bind ?_
  refine okv_whenE_bind fun hb1 => okv_returnOk_bind ?_
  refine okv_whenE_bind fun _ => okv_whenE_bind fun hb2 => okv_whenE_bind fun _ => okv_whenE_bind fun _ => ?_
  refine okv_returnOk_bind (okv_whenE_bind fun _ => okv_returnOk_bind ?_)
  refine okv_bind (fun _ => ike_assertE _) (okv_triv fun _ => trivial) fun _ _ => okv_returnOk_bind ?_
  refine okv_whenE_bind fun _ => okv_returnOk_bind (okv_returnOk_bind (okv_returnOk ?_))
  exact And.intro (SInvE.minBudget_le_usToTicks (BitVec.not_lt.1 hb2) (BitVec.not_lt.1 hb1)) (Nat.le_add_left _ _)

set_option maxHeartbeats 4000000 in
/-- **Every decoded invocation satisfies `CfgD`.** -/
theorem okv_fl4DecodeCfgD {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkV w CfgD (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | schedControlCap =>
    unfold fl4DecodeInvocation
    exact okv_ite (okv_throw _) (okv_liftME (okv_decodeSchedControlFlagsD _ _ _))
  | _ =>
    unfold fl4DecodeInvocation
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_)
      | (unfold fl4DecodeTcbInvocation)
      | (dsimp only)
      | split)

/-- **`rd_configure` from the decode fact.** -/
theorem rd_configure_d (p : ObjRef) (b per : Ticks) (mr : Nat) (badge : Badge) (flag : Data) (σ : State Unit)
    (hO : Sched.OffReady σ) (hS : Suff σ) (hSy : SInvB.ScSym σ) (hN : SInvB.RNE σ) (h1 : SInvQ.T1 σ)
    (hA : SInvQ.Simple σ)
    (hD : CfgD (.invokeSchedControl (.invokeSchedControlConfigureFlags p b per mr badge flag))) :
    IKp Rdy σ (invokeSchedControlConfigureFlags (Z := Unit)
      (.invokeSchedControlConfigureFlags p b per mr badge flag)) :=
  rd_configure p b per mr badge flag σ hO hS hSy hN h1 hA hD.1 hD.2

/-! ## The current thread at the perform -/

/-- **`CtRdy` from `CtR`** (rd), `CAx` (rd7), the current thread outside the release queue
and, when idle, not runnable. -/
theorem ctRdy_of {σ : State Unit} (hC : CtR σ) (hA : CAx σ) (hq : σ.curThread ∉ σ.releaseQueue)
    (hI : σ.curThread = σ.idleThread → ∀ x, σ.kheap σ.curThread = some (.tcb x) → runnable x.tcbState = false) :
    CtRdy σ := by
  intro x hx hrun
  by_cases e : σ.curThread = σ.idleThread
  · rw [hI e x hx] at hrun; cases hrun
  · exact hC x hx hrun (hA e) hq

/-! ## `BindRel` across the shell's `set_thread_state ct Restart` -/

theorem bindRel_setThreadState {σ : State Unit} {p t c : ObjRef} (hB : BindRel σ p t) {y : Unit × State Unit}
    (hy : y ∈ (setThreadState (Z := Unit) c .restart σ).1) : BindRel y.2 p t := by
  have hcf := cfk_setThreadState' c .restart σ y hy
  have ht : y.2.curTime = σ.curTime := by
    have := hcf; simp only [cfS, Prod.mk.injEq] at this; exact this.2.2.2.2.2
  unfold setThreadState at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, e⟩ := SInv.mem_threadSet hz
  have hk : y.2.kheap = z.2.kheap := SInvR.kh_setThreadStateAct _ c z.2 rfl y hy
  rw [e] at hk
  have hkq : ∀ q, q ≠ c → y.2.kheap q = σ.kheap q := fun q hq => by
    rw [hk]; exact Function.update_of_ne hq _ _
  have hkc : y.2.kheap c = some (.tcb { x with tcbState := .restart }) := by
    rw [hk]; exact Function.update_self _ _ _
  obtain ⟨h1, h2⟩ := hB
  refine ⟨fun y' n hy' => ?_, fun x' hx' => ?_⟩
  · have hpc : p ≠ c := by rintro rfl; rw [hkc] at hy'; cases hy'
    rw [hkq p hpc] at hy'; exact h1 y' n hy'
  · by_cases etc : t = c
    · subst etc
      rw [hkc] at hx'; cases hx'
      refine ⟨(h2 x hx).1, fun hb => absurd hb (not_blkR (by rfl))⟩
    · rw [hkq t etc] at hx'
      obtain ⟨hn, hrel⟩ := h2 x' hx'
      refine ⟨hn, fun hb => ?_⟩
      obtain ⟨y0, n0, hy0, hr0⟩ := hrel hb
      have hpc : p ≠ c := by rintro rfl; rw [hx] at hy0; cases hy0
      exact ⟨y0, n0, by rw [hkq p hpc]; exact hy0, by rw [ht]; exact hr0⟩

end

end Fl4Proofs.P3.SInvR.B8c
