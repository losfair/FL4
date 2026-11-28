/-
P3 (DESIGN.md §9), invariant line G4 (g4k, KENTRY-PLAN g4k; g4j's handoff):
**`JUtResetHyp` [W] discharged** (the Untyped retypes with a reset, `MR` at
the outcome).

* `jUtResetHyp_of`: `JUtResetHyp` at a dispatch state from `JAtZ`,
  `JEntryGlobM`, `JEntryAt`, `MachPlat`, `MRKeepD` and the Untyped path's
  facts inside `JPathM` (the ones `jDecMRLK_ofU` passes to
  `JAtZ.jUtRetHypM` / `jUtRetHypDevM`): RAM caps by UtResetMR's
  `JAtZ.jUtResetMRM`, device caps by `JAtZ.jUtResetMRDev`.
* Copies (scratch/g4k/gentops.py from XTopJointKEntry40) with
  `hDL : … → JDecMRLK VtxK …` only: `dispatch_all13PUNM4`,
  `kernel_entryJ13PUGMD4`, NEW TOPS **`kernel_entryJ41`** and
  **`kernel_entry_reachMD4`** (`kernel_entryJ40` / `kernel_entry_reachMD3`
  without `JUtResetHyp`; the old ones kept). `hDL` is asked at the same
  states as before (σb after FaultIP + a passing budget check, `KFrontB`,
  `JAtZ (Z.mv Z.G V') …`).
-/
import Fl4Proofs.P3.XTopJointKEntry40
import Fl4Proofs.P3.UtResetMR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **`JUtResetHyp` at a dispatch state** (module docstring). -/
theorem jUtResetHyp_of [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) :
    JUtResetHyp (L := L) arI AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc p sb fi dev hcE
    hNat excaps buffer hXO hXN hLb hA5 hN
  subst hcE
  obtain ⟨hDv, hU⟩ := hN
  cases dev
  · have hN := hU rfl
    exact J.jUtResetMRM hE.ni hct hsl hc hN.bufObj hN.heapH.1 hN.heapH.2 hN.core0 hG.ari.toARKeep hG.tot hG.nd hM
      hG.ppA hKD hN.rcb hE.rd0 hE.ctnq hN.vsReach hE.urz hE.utks hR hVT hVI hNat
  · have hN := hDv rfl
    exact J.jUtResetMRDev hE.ni hct hsl hc hN.bufObj hN.heapH.1 hN.heapH.2 hN.core0 hN.devApart hN.devFree hN.devGpm
      hN.rcb hN.vsReach hM hKD hG.tot hR

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`dispatch_all13PUNM3` without `JUtResetHyp`** (`jUtResetHyp_of`). `dispatch_all13PUN` with `MR` at the chosen outcome (`DispPostRM`;
module docstring): the invoking and mid syscalls by the `…M` layer, the
receiving ones and `Yield` by g4b's keeps (`JDispMR.of_keep`). -/
theorem dispatch_all13PUNM4 [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c) (hK : KDispHyps13PU (L := L) arI AR MR Z H Cs D s a σ n c)
    (hDL : ∀ ct, sched.cur_thread st s = ok ct → JDecMRLKQ (L := L) arI VtxK AR MR Z H Cs D s a σ ct)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hN : NativeScope σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a n ⦃ r =>
      DispPostRM (L := L) arI AR MR (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  have hD := dispatch_all13PUN s a σ J hni n c hn hK hR hVI hN hARI hA hnd hM hKD.toK hPA hIA hmrt hmax htu
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · obtain ⟨hG, hE, hP, hPD⟩ := hK.inv _ call bl don hct hi
    exact dispatch_invokeJAllMUNM s a σ J _ hct n call bl don hi hG hE hP hPD
      (jDecMRL_of arI s a σ J hG hE _ hct hPD hN hM hKD hIo hIoa (jDecMRL2_ofTQ arI s a σ J hG hE _ hct hM hKD (jDecMRLK_ofUQ arI s a σ J hG hE _ hct hM hKD (hDL _ hct) (jUtResetHyp_of arI s a σ J hG hE _ hct hM hKD)))) hR hK.vmt hVI hN hARI
      hA hnd hM hKD hPA hIA hmrt
  · refine WP.spec_mono (WP.spec_and hD (JDispMR.of_keep (L := L) (AR := AR) hM
      (fun hR => dispatch_recv_mr hKD hA hr hR) ?_ hR)) fun _ ⟨h1, h2⟩ => h2 h1
    rw [fl4HandleSyscall_recv true bl cr]
    intro y hy
    obtain ⟨h1, h2⟩ := MachT.mtk_withoutPreemption (MachT.mtk_handleRecvG bl cr) y hy
    exact ⟨congrArg Prod.fst h1, h2⟩
  · refine WP.spec_mono (WP.spec_and hD (JDispMR.of_keep (L := L) (AR := AR) hM
      (fun hR => dispatch_yield_mr hKD hA hR) ?_ hR)) fun _ ⟨h1, h2⟩ => h2 h1
    have e : Fl4Spec.fl4HandleSyscall (Z := Unit) true .sysYield = Fl4Spec.withoutPreemption Fl4Spec.handleYield := rfl
    rw [e]
    intro y hy
    obtain ⟨h1, h2⟩ := MachT.mtk_withoutPreemption MachT.mtk_handleYieldG y hy
    exact ⟨congrArg Prod.fst h1, h2⟩
  · obtain ⟨rg, sr, cr, hm'⟩ := midSysR_of hm
    obtain ⟨hG, hE, hP, hW, hV, hS6, hPD⟩ := hK.mid _ rg sr cr hct hm'
    obtain ⟨hs, hq⟩ := J.midCQ hni hE
    have hS : JMidRecvHypS (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA _ rg)).bv) cr σ :=
      jMidRecvHypS_of hA (jMidLeavesHyp_of2 hA (jMidLeavesHyp_of3 hA (jMidLeavesHyp_of4 hA hmax htu
        (jMidLeavesHyp_of5 hA hmax htu (jMidLeavesHyp_of6 hA hmax htu hS6)))))
    exact dispatch_midJMUNM s a σ J hni _ hct n c rg sr cr hm' hG hE hP hW.toP
      (jMidRecvHyp_of hA hG.maxTU hG.tu hs hq hW hV hS) hPD
      (jDecMRL_of arI s a σ J hG hE _ hct hPD hN hM hKD hIo hIoa (jDecMRL2_ofTQ arI s a σ J hG hE _ hct hM hKD (jDecMRLK_ofUQ arI s a σ J hG hE _ hct hM hKD (hDL _ hct) (jUtResetHyp_of arI s a σ J hG hE _ hct hM hKD)))) hR hK.vmt hVI hN hARI hA hnd hM hKD hPA hIA
      hmrt

end

/-! ## The tops -/

end

end Fl4Proofs.P3
