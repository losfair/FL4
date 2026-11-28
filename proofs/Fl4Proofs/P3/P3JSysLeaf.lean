/-
P3 (p3J gen 29): **`DispStabFoot` discharged leaf by leaf — the Yield leaf, and the premise restated over the
leaves not yet done.**

`dispatch_syscall` branches on the number into four classes (`NativeSys`): the invoking syscalls (`SysCall`,
`SysSend`, `SysNBSend`: `handle_invocation` + `after_invocation`), the receiving ones (`SysRecv`, `SysNBRecv`,
`SysWait`, `SysNBWait`: `handle_recv`), the mid ones (`SysReplyRecv`, `SysNBSendRecv`, `SysNBSendWait`: invocation,
then receive) and `SysYield` (`handle_yield`).

* **`dispYield_stFt`** (no premise): P3JSysSt's `DispStabFootAt … SysYield .sysYield` at every entry state with
  `SInvX` and a non-idle current thread. The dispatch state is `Entered` (`BudgetAt.entered`), so `CurInv` by
  `JAtZ.cur`; XTopJointYieldSys's `JAtZ.handleYieldJ` already ends at `JAtZ (Z.mv Z.G V) H Cs` (the stable
  ghosts; `JStabR` by `toR`) with the arch state unchanged; `MR` by `MachT.mtk_handleYieldG` (the spec's
  `handleYield` keeps the machine fields) and `msF_mrT`; the footprint by gen 28's `yieldProjW` (`RR` at the
  dispatch state). So the Yield leaf of `DispStabFoot` holds.
* **`DispStabFootL` [J]**: `DispStabFoot` without the Yield leaf (the case conditions also ask
  `n ≠ SysYield`): the conjunction of the three remaining classes (invoke / receive / mid), each with
  P3JSysSt's `DispStabFootAt`. Weaker than `DispStabFoot` by construction (`DispStabFoot.toL`).
  **`dispStabFoot_of_L`**: `DispStabFootL → DispStabFoot` (the Yield case by `dispYield_stFt`; `SInvX` from
  `RunMcWKR`'s `RunCK` by `jreach_invU3`).
* **`kernel_entry_runMcWKR_sysL`**: the native syscall clause, `RunMcWKR` → `RunMcWKR`, with `DispStabFootL`
  only (+ U45nv's globals as P3JSysStTop's `kernel_entry_runMcWKR_sysD`).

Named premises: `DispStabFootL` [J] (above; justified as P3JSysStTop's `DispStabFoot`, restricted to the leaves
not yet proved). No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JSysStTop
import Fl4Proofs.P3.P3JSysYield
import Fl4Proofs.P3.XTopJointYieldSys
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **The Yield leaf of `DispStabFoot` holds** (module docstring). -/
theorem dispYield_stFt (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {σ : Fl4Spec.State Unit} (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A} :
    DispStabFootAt (L := L) arI AR MR Z H Cs s a σ fl4_abi.syscall.SysYield .sysYield := by
  intro σb hBA V' Ac' Lst' D' s' a' _ J' hMb _ hRRb
  obtain ⟨x0, hk0, -⟩ := hX.sb.1.2
  have hnib := BudgetAt.entered hnd hk0 (hX.entered hct) hBA
  have hCI : CurInv σb := J'.cur.resolve_left (by rw [hnib.2]; intro h; cases h)
  have hY := J'.handleYieldJ hA hCI hnib.1 (by rw [hnib.2]; intro h; cases h) (hmrt a') (hmb a')
  have hF := yieldProjW hA J' hnib.2 hRRb
  have hct' := cur_thread_eq (L := L) s'
  generalize L.mem s' (L.nodeAt s' (L.cpu s') layout.node.CUR_THREAD) = ct at hct'
  unfold syscall.dispatch_syscall
  rw [hct']; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' ct layout.reg.CAP) ?_
  rintro c0 -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' ct layout.reg.REPLY) ?_
  rintro c1 -
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysSend; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSend; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysCall; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysWait; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBWait; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysReplyRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSendRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSendRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSendWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSendWait; decide)]
  rw [if_pos trivial]
  refine WP.spec_mono (WP.spec_and hY hF) ?_
  rintro ⟨s'', a''⟩ ⟨⟨ha, σ', hsp, V, Lst2, J2⟩, hW⟩
  simp only at ha
  subst ha
  have e : Fl4Spec.fl4HandleSyscall (Z := Unit) true .sysYield = Fl4Spec.withoutPreemption Fl4Spec.handleYield := rfl
  have hmem : ((.ok ()), σ') ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true .sysYield).run σb).1 := by
    rw [e]
    exact mem_liftE (ε := Unit) (m := Fl4Spec.handleYield (Z := Unit)) (s := σb) (x := ((), σ'))
      (by rw [hsp]; exact Set.mem_singleton _)
  have hms : MachF.msF σ' = MachF.msF σb := by
    rw [e] at hmem
    exact congrArg Prod.fst (MachT.mtk_withoutPreemption MachT.mtk_handleYieldG _ hmem).1
  exact ⟨⟨((.ok ()), σ'), hmem, Or.inl ⟨rfl, ⟨_, _, _, _, _, J2.toR⟩, msF_mrT hM hMb hms⟩⟩, hW⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **`DispStabFootL` [J]**: `DispStabFoot` on the leaves not yet proved (all but Yield; module docstring). -/
def DispStabFootL (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWKR (L := L) arI AR MR s a σ →
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
      σ.curThread ≠ σ.idleThread → NativeSys n c → n ≠ fl4_abi.syscall.SysYield → SysFlag (L := L) s →
      SysK6 (L := L) arI AR Z H Cs s a σ n c → DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- `DispStabFoot` gives `DispStabFootL` (the restriction is weaker). -/
theorem DispStabFoot.toL {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : DispStabFoot (L := L) arI AR MR s a σ) :
    DispStabFootL (L := L) arI AR MR s a σ :=
  fun hR Z H Cs Ac Lst D J hV n c hct hn _ hfl hk6 => h hR Z H Cs Ac Lst D J hV n c hct hn hfl hk6

set_option linter.unusedSimpArgs false in
/-- `NativeSys` at `SysYield` is the Yield syscall. -/
theorem nativeSys_yield {c : Fl4Spec.Syscall} (hn : NativeSys fl4_abi.syscall.SysYield c) : c = .sysYield := by
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨-, rfl⟩ | hm
  · exfalso
    rcases hi with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    all_goals first | (revert h; decide) | (revert h; simp only [fl4_abi.syscall.SysYield, fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend, fl4_abi.syscall.SysCall, fl4_abi.syscall.SysRecv, fl4_abi.syscall.SysNBRecv, fl4_abi.syscall.SysWait, fl4_abi.syscall.SysNBWait, fl4_abi.syscall.SysReplyRecv, fl4_abi.syscall.SysNBSendRecv, fl4_abi.syscall.SysNBSendWait]; decide) | (simp [fl4_abi.syscall.SysYield, fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend, fl4_abi.syscall.SysCall, fl4_abi.syscall.SysRecv, fl4_abi.syscall.SysNBRecv, fl4_abi.syscall.SysWait, fl4_abi.syscall.SysNBWait, fl4_abi.syscall.SysReplyRecv, fl4_abi.syscall.SysNBSendRecv, fl4_abi.syscall.SysNBSendWait] at h)
  · exfalso
    rcases hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    all_goals first | (revert h; decide) | (revert h; simp only [fl4_abi.syscall.SysYield, fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend, fl4_abi.syscall.SysCall, fl4_abi.syscall.SysRecv, fl4_abi.syscall.SysNBRecv, fl4_abi.syscall.SysWait, fl4_abi.syscall.SysNBWait, fl4_abi.syscall.SysReplyRecv, fl4_abi.syscall.SysNBSendRecv, fl4_abi.syscall.SysNBSendWait]; decide) | (simp [fl4_abi.syscall.SysYield, fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend, fl4_abi.syscall.SysCall, fl4_abi.syscall.SysRecv, fl4_abi.syscall.SysNBRecv, fl4_abi.syscall.SysWait, fl4_abi.syscall.SysNBWait, fl4_abi.syscall.SysReplyRecv, fl4_abi.syscall.SysNBSendRecv, fl4_abi.syscall.SysNBSendWait] at h)
  · rfl
  · exfalso
    rcases hm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    all_goals first | (revert h; decide) | (revert h; simp only [fl4_abi.syscall.SysYield, fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend, fl4_abi.syscall.SysCall, fl4_abi.syscall.SysRecv, fl4_abi.syscall.SysNBRecv, fl4_abi.syscall.SysWait, fl4_abi.syscall.SysNBWait, fl4_abi.syscall.SysReplyRecv, fl4_abi.syscall.SysNBSendRecv, fl4_abi.syscall.SysNBSendWait]; decide) | (simp [fl4_abi.syscall.SysYield, fl4_abi.syscall.SysSend, fl4_abi.syscall.SysNBSend, fl4_abi.syscall.SysCall, fl4_abi.syscall.SysRecv, fl4_abi.syscall.SysNBRecv, fl4_abi.syscall.SysWait, fl4_abi.syscall.SysNBWait, fl4_abi.syscall.SysReplyRecv, fl4_abi.syscall.SysNBSendRecv, fl4_abi.syscall.SysNBSendWait] at h)

/-- **The Yield leaf discharged**: `DispStabFootL → DispStabFoot` (module docstring). -/
theorem dispStabFoot_of_L (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR)
    (hIp : IpiF arI MR) (hT : TimeAgree arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootL (L := L) arI AR MR s a σ) : DispStabFoot (L := L) arI AR MR s a σ := by
  intro hR Z H Cs Ac Lst D J hV n c hct hn hfl hk6
  by_cases hy : n = fl4_abi.syscall.SysYield
  · subst hy
    obtain rfl := nativeSys_yield hn
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact dispYield_stFt hA hnd (MachPlatF.toT hM hIp) (fun a => hT.mrt a) hT.mb hX hct
  · exact h hR Z H Cs Ac Lst D J hV n c hct hn hy hfl hk6

set_option maxHeartbeats 4000000 in
/-- **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFootL` only** (`hDL` [J]; module
docstring). -/
theorem kernel_entry_runMcWKR_sysL [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hDL : DispStabFootL (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysD hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hR
    (dispStabFoot_of_L hA hnd hM hIp hT hDL)

end

end Fl4Proofs.P3.Mc
