/-
P3 (line p3J, gen 15): **a U40 start with a root thread on FL4's real boot IRQ layout** (namespace `JBootQ`).

* The witness `JBootQ.w1` / `JBootQ.σ1` (JBootQ1St … JBootQ1JAt, gen-15 verbatim copies of jboot's gen-4
  JBoot1St … JBoot1JAt by `scratch/p3J/genQ1.py`): `JBootQ.w0` / `JBootQ.fInitASt` (FL4's boot IRQ words, line 125
  `IRQ_TIMER`, 126 / 127 `IRQ_IPI`; spec 125 `irqTimer`, 126 / 127 `irqReserved`) plus a running root TCB `rT`
  on its root SC `rS`, CSpace root a radix-1 CNode `rC` holding the root's thread cap and SC cap. Only
  `w1_irqRel` and `img1_zero` were re-proved in the copies.
* `w1_jkernI1`, `w1_utcI1`, `jAtZ_w1I1` at arch `warI1`; `ipiMR_σ1Q`; `jReachU3_w1I1`, **`jReachU17_w1I1`**;
  `σ1_irqStS`, `σ1_noHandler`, **`σ1_irqCarry`** (irqfix3's carried fact: no IRQ-handler cap in `σ1`'s heap,
  no `IRQSignal` line); **`jReachU36I_w1I1`**; `warI1_ioaRelQ1`; **`jReachU40_w1I1`** (no premise);
  **`u40_w1I1 (O : OpaqueWK)`**: every premise of `kernel_entry_reachU40` at `wst` / `warI1` / `wAR` / `ipiMR`
  with this start. U41 … U46 / U45nv keep U40's start `JReachU40` verbatim and add only global [P]s on opaque
  operations / constants (`FpuImplDet`, `FpuWriteDet`, `KCfgFL4`) and, for U45nv, `NoVirt` (which `warI1`
  meets: `noVirt_warI1`), so `jReachU40_w1I1` starts all of them.
* `σ1_nonIdle` (JBootQ1Spec): the current thread is not the idle thread, so the syscall / fault / trap clauses of
  U40 … U46 are not vacuous at this start (at `JBootQ.w0` they are).

Named premises: `OpaqueWK` [P] (JBootU34) only. Caveats (jboot's): one core, one root thread.
No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootQ1JAt
import Fl4Proofs.P3.JBootQU40
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBootQ
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs

noncomputable section

/-- `JKern` at `warI1`: `w1_jkern`'s fields (its TDX clause reads the unchanged `tdx_active` / `dma_ram`). -/
theorem w1_jkernI1 : JKern (L := wL) warI1 Hw1 Csw Dw thW1 w1 σ1 :=
  { orig := w1_jkern.orig, cur := w1_jkern.cur, curT := w1_jkern.curT, act := w1_jkern.act,
    dwAl := w1_jkern.dwAl, dwObj := w1_jkern.dwObj, dwNe := w1_jkern.dwNe, head := w1_jkern.head,
    gpm := w1_jkern.gpm, ga := w1_jkern.ga, gf := w1_jkern.gf, heap := w1_jkern.heap, h0 := w1_jkern.h0,
    hks := w1_jkern.hks, hksIn := w1_jkern.hksIn, hnd := w1_jkern.hnd, ksbFit := w1_jkern.ksbFit,
    ksbAl := w1_jkern.ksbAl, nodeFit := w1_jkern.nodeFit, cpuCs := w1_jkern.cpuCs, curH := w1_jkern.curH,
    cscH := w1_jkern.cscH, csLt := w1_jkern.csLt, cs0 := w1_jkern.cs0, csN := w1_jkern.csN,
    tdx := w1_jkern.tdx }

/-- **`JAtZ.utc`** at `warI1` (vacuous: no slot of `w1` holds an untyped cap). -/
theorem w1_utcI1 : ∀ sl p sb fi dev, AbsSlot thW1 sl →
    capAt (wL.mem w1) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
    Sched.UtCapP3 (L := wL) warI1 thW1 w1 σ1 G1 sl p sb fi := by
  intro sl p sb fi dev hs h _
  rw [capAt_capV] at h
  rcases slot1_cases hs.isSlot with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at h <;> cases ok_inj h

/-- **The joint invariant at the root-thread witness, arch `warI1`.** -/
theorem jAtZ_w1I1 (a : MachineState) :
    JAtZ (L := wL) warI1 wAR Zw1 Hw1 Csw C1 (fun _ => []) Dw w1 a σ1 where
  xtop :=
    { fin := ⟨⟨w1_othersRel a, w1_topPlaced⟩, w1_vsRel, w1_ptRel, w1_poolsIn, w1_curOK⟩
      rel := ⟨placed_thW1, w1_crel, w1_finInv, w1_domRel, w1_mdbOKV, w1_ipcApart, w1_scApart⟩
      ipc := w1_ipc
      esa := w1_esa }
  call := w1_call
  rfree := w1_rfree
  rrecv := w1_rrecv
  yld := w1_yld
  mcp := w1_mcp
  buf := w1_buf
  ks := w1_ks
  thT := thT_thW1
  thk := thk_thW1
  ip := w1_ip
  rp := w1_rp
  apart := w1_apart
  nk := w1_nk
  nodeB := w1_nodeB
  jpl := w1_jpl
  cover := w1_cover
  obj := σ1_obj
  zH := w1_zH
  sfree := w1_sfree
  hset := w1_hset
  hscC := w1_hscC
  jcov := w1_jcov
  kern := w1_jkernI1
  del := w1_delInv
  ut := w1_utInv
  bound := w1_delBound
  finM := w1_finM
  utc := w1_utcI1
  nsc := σ1_nsc
  inv := σ1_inv
  cur := Or.inr σ1_curInv
  own := σ1_own
  off := σ1_off
  act := σ1_act
  c0 := w1_c0
  bsa := σ1_bsa
  sv := σ1_sv
  isorted := σ1_isorted
  slink := σ1_slink
  curRun := σ1_curRun
  blk := w1_blk
  intL := intL_thW1
  vsc := w1_vsc
  bok := w1_bok
  fcov := w1_fcov
  fcap := w1_fcap
  ext := w1_ext
  live := w1_live
  zD := w1_zD
  carry := w1_carry

/-- `σ1`'s machine state is jboot's boot machine state, `ipiMR`-related to itself. -/
theorem ipiMR_σ1Q : ipiMR σ1.machineState σ1.machineState := JBoot.fInit_ipiMR

/-- **The root-thread witness starts `JReachU3` at `warI1` / `ipiMR`.** -/
theorem jReachU3_w1I1 : JReachU3 (L := wL) warI1 wAR ipiMR w1 σ1.machineState σ1 :=
  .start (jAtZ_w1I1 _) Zw1_vx σ1_sinvX σ1_sinvIP ipiMR_σ1Q σ1_utPgR

/-- **`JReachU17` at the root-thread witness with FL4's boot IRQ layout.** -/
theorem jReachU17_w1I1 : JReachU17 (L := wL) warI1 wAR ipiMR w1 σ1.machineState σ1 :=
  ⟨jReachU3_w1I1, σ1_gpmOut, σ1_idleVtS, σ1_devRangeS⟩

/-- No line above `maxIRQ` is `IRQSignal` at `σ1` (its interrupt states are `fInitIpiASt`'s). -/
theorem σ1_irqStS : SInvIB.IrqStS σ1 := SInvIB.fInitIpi_irqStS

/-- **`σ1` holds no IRQ-handler cap** (`capAt1`: its caps are null or the three root caps). -/
theorem σ1_noHandler (p : ObjRef) (cref : CnodeIndex) (irq : Irq) :
    capOpt (σ1.kheap p) cref ≠ some (.irqHandlerCap irq) := by
  intro hc
  have h : SInvU.capAt σ1 (p, cref) = some (.irqHandlerCap irq) := by
    rw [SInvUZ.capAt_capOpt]; exact hc
  rcases capAt1 h with e | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e

/-- **irqfix3's carried fact at `σ1`.** -/
theorem σ1_irqCarry : SInvIB.IrqCarry σ1 :=
  SInvIB.irqCarry_of_noHandler σ1_noHandler σ1_irqStS

/-- **`JReachU36I` at the root-thread witness.** -/
theorem jReachU36I_w1I1 : JReachU36I (L := wL) warI1 wAR ipiMR w1 σ1.machineState σ1 :=
  ⟨jReachU17_w1I1, σ1_irqCarry⟩

/-- `IoaRel warI1` at `σ1` (its arch state is `fInitASt`'s). -/
theorem warI1_ioaRelQ1 : IoaRel warI1 σ1 := JBoot.warI1_ioaRel.frame rfl

/-- **`JReachU40` at the root-thread witness with FL4's boot IRQ layout** (no premise). -/
theorem jReachU40_w1I1 : JReachU40 (L := wL) warI1 wAR ipiMR w1 σ1.machineState σ1 :=
  ⟨jReachU36I_w1I1, warI1_ioaRelQ1⟩

/-- **Every premise of `kernel_entry_reachU40` at the witness platform with the root-thread start on FL4's
boot IRQ layout**, under `OpaqueWK` [P]. Only U40's per-entry [J]s remain. -/
theorem u40_w1I1 (O : OpaqueWK) :
    ARIface warI1 wAR ∧ P0.ArchTotal warI1 ∧ Fl4Spec.numDomains = 1 ∧ MachPlatF warI1 ipiMR ∧ IpiF warI1 ipiMR ∧
      MRKeepD warI1 ipiMR ∧ MRKeepIo warI1 ipiMR ∧ MRKeepIoapic warI1 ipiMR ∧
      (∀ a c, wAR a c → warI1.irq_pending a ⦃ r => wAR r.2 c ⦄) ∧ IrqPlatA warI1 wAR ∧ TimeAgree warI1 ∧
      Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      (∀ a v, warI1.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) ∧
      ArchRefines warI1 wAR ∧ PortInValMR warI1 ipiMR ∧ P1.StoreExt wst ∧
      SetDlDetR (A := Fl4Spec.MachineState) ipiMR ∧ IoaMap warI1 ∧
      JReachU40 (L := wL) warI1 wAR ipiMR w1 σ1.machineState σ1 :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, _⟩ := u40_w0I1 O
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, jReachU40_w1I1⟩

end

end Fl4Proofs.P3.JBootQ
