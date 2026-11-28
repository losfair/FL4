/-
P3 (issue #16, m72): **`kernel_entryJ42H` / `kernel_entry_reachUH`**, g5f's
`kernel_entryJ42` / `kernel_entry_reachU` without m67's `nvm` read
`hRP5 : n = SysReplyRecv → P1.RRPreAt5` [J] (KENTRY-PLAN m70 handoff (b)):
m70's `JAtZ.rrPre5At` gives `RRPreAt5` from the entry's `JAtZ`, `SInvX`
(`entered`, `sb`, `ctQ`, `offReady`) and `SInvW.rv`, all carried by `JReachU`.
-/
import Fl4Proofs.P3.XTopJointKEntryU
import Fl4Proofs.P3.XTopJointKEntryRRG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`kernel_entryJ42` without `hRP5`** (module docstring).
`hSX : StoreExt` [P]: the fast path's BLOCK_OBJ / STATE write order (`P1.rr_same`). -/
theorem kernel_entryJ42H [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hX : SInvX σ) (hI : SInvIP σ) (hLF : LargeFrOK Z.G (L.mem s))
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV42 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDL : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        ∀ ct', sched.cur_thread st s' = ok ct' → JDecMRLKQ (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct')
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) :
    syscall.handle_syscall st arI s a n ⦃ r => KPostU (L := L) arI AR MR c σ r ⦄ := by
  have hni := hX.entered hct
  exact kernel_entryJ42 (MR := MR) s a σ J hct hR hX hI hLF n c hn hflag hK hDL hFin hARI hA hnd hM hKD hIo hIoa
    hPA hIA hmrt hmb hT hmax htu hRef hPI hSX (fun _ => J.rrPre5At hni hR hX.sb hX.ctQ
      (fun _ _ => offReady_faultIPSt hX.offReady) hARI hA hnd hM hmrt hmb hmax htu (Fl4Proofs.P3.SInvW.rv hX.w))

end

end

end Fl4Proofs.P3.SInvR.G5
