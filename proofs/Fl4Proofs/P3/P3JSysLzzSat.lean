/-
P3 (p3J gen 55): **the globals of `kernel_entry_runMcWKR_sysLzz` hold jointly at one platform** (non-vacuity of
gen 54's native syscall top).

The instance is the witness platform of the boot line: store `wst` (P2/WitPlat, `LawfulStore` `wL`, `PlainStore`
`wP`), arch `warI1` (FL4's boot IRQ layout), CR3 relation `wAR`, machine relation `ipiMR`, `A :=
Fl4Spec.MachineState`, and the 2-core boot state `JBootQ.M2.w0` / `fInitASt`.

* **`sysLzz_globals_sat`**: under the opaque-constant facts only (`OpaqueWK` [P], JBootU34; `FpuImplDet` [P],
  ScFpuNd; `FpuWriteDet` [P], ArchSwThr), every global premise of `_sysLzz` holds at that one instance:
  `PlainStore wst`, `ARIface`, `ArchTotal`, `numDomains = 1`, `MachPlatF`, `IpiF`, `MRKeepD`, `hPAi`
  (`irq_pending` keeps `wAR`), `IrqPlatK`, `TimeAgree`, `hmax`, `htu`, `ArchRefines`, `StoreExt`, `SetDlDetR`,
  `FpuImplDet`, `FpuWriteDet`, and the run state `RunMcWKR` at the boot state. All from existing witnesses
  for the same `warI1` / `wAR` / `ipiMR` / `wst`: `JBootQ.M2.u40_w0I1` (15 of the arch / store globals,
  including `hPAi`), `wP`, `runMcWKR_w2`.
* **`sysLzz_w2`**: so `_sysLzz` applies at the boot state of that platform with only the three opaque facts left
  (its per-call antecedents unchanged).
* **`fInitASt_ct_idle`**: caveat: the boot state runs the idle thread (`initASt`), so `sysLzz_w2`'s per-call
  antecedent `curThread ≠ idleThread` fails there; the globals and `RunMcWKR` are inhabited, a `RunMcWKR` state
  with a non-idle current thread is not given here (the root-thread state `σ1` has `JAtZ` (`u45nv_w1I1`) and
  `σ1_nonIdle` but no `RunMcWKR` witness).
* **`opaqueSysLzz_model`**: the opaque facts other than `OpaqueWK.pin` are consistent: a `KernelConfig`, a
  `TimeConsts`, a `maxTicksToUs` value and deterministic `setDeadlineImpl` / `enableFpuImpl` / `disableFpuImpl` /
  `writeFpuStateImpl` meeting them exist (the opaque constants are neither provable nor refutable in Lean; this
  shows their premises do not contradict the constants' own types). `pin` (a port-read value at every spec state)
  constrains the opaque `in*Impl` / `in*Val` through `archPerformInvocation` and is not modelled here.

Named premises: `OpaqueWK` [P], `FpuImplDet` [P], `FpuWriteDet` [P] (existing; hypotheses of the two theorems).
None new. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMidIpcC
import Fl4Proofs.P3.JBootM2U40
import Fl4Proofs.P3.P3JMcIrqRQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBootQ.M2
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.Mc

noncomputable section

set_option maxHeartbeats 4000000 in
/-- (p3J gen 55) **Every global of `kernel_entry_runMcWKR_sysLzz` at the witness platform, and `RunMcWKR` at
its boot state**, under the opaque-constant facts `OpaqueWK`, `FpuImplDet`, `FpuWriteDet` [P] (module
docstring). -/
theorem sysLzz_globals_sat (O : OpaqueWK) (hFpu : FpuImplDet) (hFW : FpuWriteDet) :
    PlainStore wst ∧ ARIface warI1 wAR ∧ P0.ArchTotal warI1 ∧ Fl4Spec.numDomains = 1 ∧
      MachPlatF warI1 ipiMR ∧ IpiF warI1 ipiMR ∧ MRKeepD warI1 ipiMR ∧
      (∀ a c, wAR a c → warI1.irq_pending a ⦃ r => wAR r.2 c ⦄) ∧ IrqPlatA warI1 wAR ∧ TimeAgree warI1 ∧
      Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      (∀ a v, warI1.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) ∧
      ArchRefines warI1 wAR ∧ P1.StoreExt wst ∧ SetDlDetR (A := Fl4Spec.MachineState) ipiMR ∧
      FpuImplDet ∧ FpuWriteDet ∧
      RunMcWKR (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  let ⟨h1, h2, h3, h4, h5, h6, _, _, h9, h10, h11, h12, h13, h14, _, h16, h17, _, _⟩ := u40_w0I1 O
  ⟨wP, h1, h2, h3, h4, h5, h6, h9, h10, h11, h12, h13, h14, h16, h17, hFpu, hFW, runMcWKR_w2⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 55) **`kernel_entry_runMcWKR_sysLzz` at the boot state of the witness platform**: only the opaque
facts `OpaqueWK`, `FpuImplDet`, `FpuWriteDet` [P] are left (module docstring). -/
theorem sysLzz_w2 (O : OpaqueWK) (hFpu : FpuImplDet) (hFW : FpuWriteDet) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), fInitASt.curThread ≠ fInitASt.idleThread → NativeSys n c →
      SysFlag (L := wL) w0 →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := wL) warI1 wAR Z H Cs Ac Lst D w0 fInitASt.machineState fInitASt →
          SysK6 (L := wL) warI1 wAR Z H Cs w0 fInitASt.machineState fInitASt n c) →
      syscall.handle_syscall wst warI1 w0 fInitASt.machineState n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c fInitASt).1 ∧
          RunMcWKR (L := wL) warI1 wAR ipiMR r.1 r.2 σ' ⦄ :=
  let ⟨_, h1, h2, h3, h4, h5, h6, h9, h10, h11, h12, h13, h14, h16, h17, _, _, hR⟩ :=
    sysLzz_globals_sat O hFpu hFW
  kernel_entry_runMcWKR_sysLzz h1 h2 h3 h4 h5 h6 h9 h10 h11 h12 h13 h14 h16 h17 hFpu hFW hR

/-- (p3J gen 55) **The boot state runs the idle thread** (module docstring, caveat of `sysLzz_w2`). -/
theorem fInitASt_ct_idle : fInitASt.curThread = fInitASt.idleThread := rfl

/-- A deterministic `MachineRestMonad` step (`pure ()`). -/
private def detUnit : MachineRestMonad Unit := fun mr => ({((), mr)}, False)

private theorem detUnit_det (mr : MachineStateRest) (x y : Unit × MachineStateRest)
    (hx : x ∈ (detUnit mr).1) (hy : y ∈ (detUnit mr).1) : x = y := by
  simp only [detUnit, Set.mem_singleton_iff] at hx hy; rw [hx, hy]

/-- A `TimeConsts` with FL4's values (WCET 10 µs, one tick per µs, l4v's one-hour maximum period). -/
private def tcFL4 : TimeConsts :=
  { maxPeriodUs := 60 * 60 * 1000 * 1000,
    kernelWCETUs := 10, ticksPerTimerUnit := 1, timerUnit := 1,
    kernelWCET_us_pos2 := by decide
    MIN_BUDGET_le_MAX_PERIOD := by decide
    ticks_per_timer_unit_non_zero := by decide
    MIN_BUDGET_bound := by decide
    getCurrentTime_buffer_bound := by decide
    kernelWCET_pos' := by decide
    MIN_BUDGET_pos' := by decide
    init_domain_time_pos := by decide
    init_domain_time_bound := by decide
    getCurrentTime_buffer_pos := by decide }

/-- (p3J gen 55) **The opaque-constant facts of `sysLzz_w2` other than `OpaqueWK.pin` are consistent**: values
of the types of `kernelConfig`, `timeConsts`, `maxTicksToUs`, `setDeadlineImpl`, `enableFpuImpl`,
`disableFpuImpl`, `writeFpuStateImpl` meeting `OpaqueWK.nd / max / wcet / unit / per / dl`, `FpuImplDet`,
`FpuWriteDet` exist (module docstring). -/
theorem opaqueSysLzz_model :
    ∃ (kc : KernelConfig) (tc : TimeConsts) (mt : Word64) (dl : Word64 → MachineRestMonad Unit)
      (en dis : MachineRestMonad Unit) (wr : FpuState → MachineRestMonad Unit),
      kc.numDomains = 1 ∧ mt = core.num.U64.MAX.bv ∧ tc.kernelWCETUs = 10 ∧ tc.timerUnit = 1 ∧
      tc.maxPeriodUs.toNat < 2305843009213693952 ∧
      (∀ d mr (x y : Unit × MachineStateRest), x ∈ (dl d mr).1 → y ∈ (dl d mr).1 → x = y) ∧
      (∀ mr (x y : Unit × MachineStateRest), x ∈ (en mr).1 → y ∈ (en mr).1 → x = y) ∧
      (∀ mr (x y : Unit × MachineStateRest), x ∈ (dis mr).1 → y ∈ (dis mr).1 → x = y) ∧
      (∀ v mr (x y : Unit × MachineStateRest), x ∈ (wr v mr).1 → y ∈ (wr v mr).1 → x = y) := by
  obtain ⟨kc, hkc, -, -⟩ := kCfgFL4_consistent
  refine ⟨kc, tcFL4, core.num.U64.MAX.bv, fun _ => detUnit, detUnit, detUnit, fun _ => detUnit, hkc, rfl, rfl, rfl,
    by decide, fun _ => detUnit_det, detUnit_det, detUnit_det, fun _ => detUnit_det⟩

end

end Fl4Proofs.P3.JBootQ.M2
