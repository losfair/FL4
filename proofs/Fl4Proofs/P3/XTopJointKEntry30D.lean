/-
P3 (DESIGN.md §9), invariant lines G1 / G3 (ctq20): **`kernel_entryJ30D`** =
`kernel_entryJ30C` with `hS : SInvCQ σ` replaced by `hS : SInvCR σ`
(SpecInvAllR: `SInvCQ ∧ RS`, `RS σ := σ.schedulerAction = resumeCurThread`)
and `hni : Entered σ` replaced by `hct : σ.curThread ≠ σ.idleThread` ([S], l4v
`ct_active` at a syscall entry: a syscall comes from a user thread). `Entered`'s
action half is `SInvCR`'s `RS` (`SInvCR.entered`).

`RS` holds at boot (`boot_sinvCR`) and at every kernel exit given rd's `CAx`
at that exit (`kentry_sinvCR_ofCA` / `kcall_sinvCR_ofCA`, or rd10's
hypotheses: `*_ofRd`); see SpecInvAllR. The rest are J / [P] / [S] / spec
exactly as in `kernel_entryJ30C` (`hE : EpQAll σ`, `hB : OffReady …` are the rd
line's). No premise added; no cone edit.
-/
import Fl4Proofs.P3.XTopJointKEntry30C
import Fl4Proofs.P3.SpecInvAllR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvAll

/-- **`Entered`** (l4v `ct_running` ∧ `schact_is_rct`) from `SInvCR` and `ct ≠ idle`. -/
theorem SInvCR.entered {σ : Fl4Spec.State Unit} (h : SInvCR σ) (hct : σ.curThread ≠ σ.idleThread) :
    Entered σ :=
  And.intro hct h.2

end Fl4Proofs.P3.SInvAll

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`kernel_entryJ30C` with `Entered`'s action half from `SInvCR`** (module docstring):
`hS : SInvCQ` becomes `hS : SInvCR`; `hni : Entered σ` becomes `hct : ct ≠ idle` [S]. -/
theorem kernel_entryJ30D [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvCR σ) (hE : SInvE.EpQAll σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV27b (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR27 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ30C s a σ J (SInvAll.SInvCR.entered hS hct) hR hS.1 hE n c hn hflag hB hK hFin hARI hA hnd hM hKD
    hPA hIA hmrt hmb hT hmax htu

end

end

end Fl4Proofs.P3
