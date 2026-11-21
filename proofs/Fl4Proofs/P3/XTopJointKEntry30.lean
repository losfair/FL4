/-
P3 (DESIGN.md §9), invariant line G3 (g3e): **`kernel_entryJ30`**, the newest
top. Its premise list is exactly `kernel_entryJ29G`'s (g3d). The bundles inside
`hK` no longer hold the ∀-state `JEntryGlobM.sigRest`.

`JEntryGlobM.sigRest : ∀ H Cs, SignalRestJHyp` (ScSignalJ: FL4's `send_signal`
refines the spec's at EVERY `JAtZ` state whose notification has a `RunningVM`
bound thread) is false for any instance with such a state. g3e deleted the
field (XTopJointKEntry13P). Its only readers, the Notification cases of
`decOK_JM` / `decOK_JMU` (KEntry13P / 23P), now use `notifLeafJN`:
`NativeScope` at the invocation's state, carried across ct's restart by
`SInv.ns_setThreadState`, then `JAtZ.signal_atN` (g3b, moved to ScSignalJN).
`decOK_JM(U)`, `handle_invocation_entryJM(U)`, `invoke_afterJM(U)` and
`dispatch_invokeJM(U)` take `NativeScope σ`. J28's dispatch layer holds it at
the dispatch state (g3b: `ns_of_kheap` of the FaultIP state). The older tops
read it from their own ∀ `hNS` at the dispatch state's `J.toHole`.
No premise added.
-/
import Fl4Proofs.P3.XTopJointKEntry29
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The newest top** (module docstring): `kernel_entryJ29G`'s premises, with
`JEntryGlobM` (inside `hK`'s `KDispHypsKV27b`) free of the ∀-state `sigRest`. -/
theorem kernel_entryJ30 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (n : I64) (c : Fl4Spec.Syscall)
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
  kernel_entryJ29G s a σ J hni hR hS hE hQ n c hn hflag hB hK hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu

end

end

end Fl4Proofs.P3
