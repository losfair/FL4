/-
P3 (DESIGN.md §9), invariant line G1 (rd8m, KENTRY-PLAN rd8j handoff 4): **rd13a's
top with `hRdB` discharged** (spec side only, outside the JAtZ cone).

**`kcall_rdyOff6m`** = rd13a's `kcall_rdyOff6` with `hRdB` from rd8m's
`rdBody_all`: the body's entry facts from the top's own hypotheses (`EF`; `T1`
from EX's TQ; ctq's `EB true` = ⟨⟨EX's SchedQ, T4⟩, RB⟩; `VfhAll` from
EntryOK; ctq17's `EvP` and ct ≠ idle as in rd13a's `key`), plus two carried
facts taken by name (`IdleScOutV` of ut7 / vi3, ctq20's `RS`) and the pinned
inputs `InvIn` / `PreR` (rd8j) and `RcvIn` (rd8m). Remaining as in rd13a:
`InvR` (rd14b), `RecvTA` (rd14a), `RdF` (rd8h's `rd_handleFault` proves it).
-/
import Fl4Proofs.P3.SpecInvRd8mD
open Classical

namespace Fl4Proofs.P3.SInvR.B8m
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR
open Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

noncomputable section

set_option maxHeartbeats 4000000 in
/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event**, rd13a's top with
`hRdB` discharged (module docstring). -/
theorem kcall_rdyOff6m (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hRS : σ.schedulerAction = .resumeCurThread)
    (hPs : ∀ c, ev = .syscallEvent c → ∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → B8j.InvIn r false σ)
    (hPr : ∀ c, ev = .syscallEvent c → ∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true σ)
    (hPre : ∀ c, ev = .syscallEvent c → B8j.PreR rep c σ)
    (hRc : ∀ c, ev = .syscallEvent c → RcvIn rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → A12b.InvR c σ)
    (hRA : ∀ c, ev = .syscallEvent c → A13a.RecvTA rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  have key : ∀ c, ev = .syscallEvent c → A8.EF σ ∧
      EvP σ.curThread σ.idleThread σ.idleSc I d Nq σ σ ∧ σ.curThread ≠ σ.idleThread := by
    intro c e
    subst e
    obtain ⟨hIu, hIL, hJ, -, -, -⟩ := hS c rfl
    exact ⟨hEF (by intro h; cases h), evp_start hX hR h4 hX10.vi hX10.eo hCX hIu hIL hJ,
      ne_idle_of_active hX10.vi hCX (fun x hx => (ha x hx).resolve_right fun e => by cases e)⟩
  refine A13a.kcall_rdyOff6 hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS (fun c e => ?_) hP hRA hRdF
  exact rdBody_all hnd rep c σ (key c e).1 (SInvQ.tq_t1 hX.1.1.1) ⟨⟨hX.1, h4⟩, hR⟩ hIO hX10.eo.vfh
    (key c e).2.1 (key c e).2.2 hRS (hPs c e) (hPr c e) (hPre c e) (hRc c e)

end

end Fl4Proofs.P3.SInvR.B8m
