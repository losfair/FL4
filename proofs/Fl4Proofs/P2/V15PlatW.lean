/-
# P2 (line p3mc, gen 54): the re-based V15 top on jboot's witness platform — **no `irqOracle` fact**

Handoff §51b step 3 / §59. Gen 54 re-based the constant-level cone of `serializable_fl4_V15_pmKADZ` in place
(`P : LocPlat` + `hIoa` ↦ `P : LocPlatCR`, P2/E2EPU12a; `P : LocPlat` ↦ `P : LocPlatC`, P2/E2EVFl4W3; each old
declaration a one-line corollary). `LocPlatCR` is `LocPlatC` plus the two P3 facts the slot obligations read at chain
states (`ChainRun`, `ChainAct0`): §51b's claim that the trunk reads `P` only through `chainOf_exists` holds for the
execution and the tops, not for the slot obligations (`chain_run` / `chain_act0` read `P.mach`, `P.ia`, … through
`kernel_entry_nativeScopeU29` / `kernel_entry_reachU29`; handoff §59).

* **`locPlatCR_wit`**: `LocPlatCR wst warI wAR ipiMR` from `OpaqueWK` [P] only. `toC` is gen 46's `locPlatC_wit`;
  `run` is `chain_run` at `wit_locPlatK O` and `wit_ioapicI` (`MRKeepIoapic` at `ipiMR` is a theorem); `act0`
  is `chain_act0`'s argument over `kernel_entry_reachU29`. (Before collapse A, Q both were jboot gen 5's
  kernel-checked copies `Fl4ProofsQ.…` of P2/WitU34Gen; Q wrote the fixed platform back into `LocPlat`.)
* **`serializable_fl4_V15_pmKADZW`**: `serializable_fl4_V15_pmKADZ_C` (P2/InsV15Pm) at `locPlatCR_wit O`.

## Premise diff vs `serializable_fl4_V15_pmKADZ`
| removed | added |
|---|---|
| `P : LocPlat st arI AR MR` (15 platform fields: `MachPlat` with `mask` unmasking every line < 256, `IrqPlatA` with `noIpi` over all arch states — at `ipiMR` these need `OpaqueH.ipi`, the `irqOracle` fact) | `O : OpaqueWK` [P] (`OpaqueH` without `ipi`: nd, max, wcet, unit, per, dl, pin) |
| `hIoa : MRKeepIoapic arI MR` [P] | — (`wit_ioapicI`, a theorem at `ipiMR`) |
The platform is jboot's witness (`wst`, `warI`, `wAR`, `ipiMR`, 126 / 127 kept masked); `ar`, `hA`, `a0`, `B`
([P] `cs` / `lk`), `h0`, `hA0`, `hB`, `hc0`, `hM0`, the execution ([P] `MmuAD` in its `ad` step) and `hq` are
`pmKADZ`'s. The generic `serializable_fl4_V15_pmKADZ_C` (any `P : LocPlatCR`) implies `pmKADZ` (`pmKADZ` is its
one-line corollary at `locPlatCR_of P hIoa`).

**Gen 55: `serializable_fl4_localAD3W`** — the VM-epoch A/D top `serializable_fl4_localAD3` (P2/E2EPAD3, kept: the
only P2 top covering `vcpus ≠ ∅`) at the same witness: its re-based form `serializable_fl4_localAD3_C` (`P : LocPlatC`,
`hRun : ChainRun`) at `locPlatC_wit O` and `(locPlatCR_wit O).run`. Premise diff vs `serializable_fl4_localAD3`:
`P : LocPlat` and [P] `hIoa` ↦ `O : OpaqueWK` [P]; the rest (`B`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, the execution with
[P] `MmuAD` and [S] `VmPweU`, the [S] start records `StartAD3`, `hq`) as `serializable_fl4_localAD3`'s.
-/
import Fl4Proofs.P2.LocPlatC
import Fl4Proofs.P2.InsV15Pm
import Fl4Proofs.P2.E2EPAD3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Wit
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.E2E (SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)
open Fl4Proofs.P3 Fl4Proofs.P3.JBoot

/-- **`LocPlatCR` on jboot's witness platform at `ipiMR`, from `OpaqueWK` [P] only** (module docstring). -/
theorem locPlatCR_wit (O : OpaqueWK) : LocPlatCR wst warI wAR ipiMR where
  toC := locPlatC_wit O
  run := fun {_ _ _} hC {_} hσ hct => Fl4Proofs.P2.E2EV.chain_run (wit_locPlatK O) wit_ioapicI hC hσ hct
  act0 := by
    intro σe K Ch hC σ hσ hct
    obtain ⟨Z, H, Cx, nc, -, -, hCh, -, -⟩ := hC
    subst hCh
    obtain ⟨a, τ, hR⟩ := hσ
    have hJ := hR.reach
    have P := wit_locPlatK O
    obtain ⟨Z', H', Cs, Ac, Lst, D, J, hX, -⟩ := Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU29 warI wAR ipiMR P.ari
      P.tot P.nd P.mach P.kd P.io wit_ioapicI P.pa P.ia P.t P.max P.tu P.ref P.pi P.sx P.dr hJ
    exact (J.curFacts (hX.entered (hct a τ hJ)) (cur_thread_ok σ)).2.2.2

variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {Cs Ω Sg Ac : Set U64} {Locks : WSt → U64 → Prop}

/-- **FL4 end to end over V13's slots and PageMap on CoreView with the walker's A/D writes, on jboot's witness
platform at `ipiMR`, without `OpaqueH.ipi`** (module docstring): `serializable_fl4_V15_pmKADZ_C` at
`locPlatCR_wit O`. -/
theorem serializable_fl4_V15_pmKADZW (O : OpaqueWK) (B : PmObl7 wst Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → WSt → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitC (locPlatC_wit O) K0.toKLayoutV (Ch0 e))
    (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem) (hM0 : MapsP K0 s0)
    (h : ExecV15C (ExecCfg.nativePmKAD wst ar hA a0 warI wAR ipiMR B) (locPlatC_wit O) s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_V15_pmKADZ_C wst ar hA a0 (locPlatCR_wit O) B h0 hA0 hB hc0 hM0 h hq

/-- **The A/D top with VM epochs (`serializable_fl4_localAD3`) on jboot's witness platform at `ipiMR`, without
`OpaqueH.ipi`** (gen 55): `serializable_fl4_localAD3_C` at `locPlatC_wit O` and `(locPlatCR_wit O).run`. -/
theorem serializable_fl4_localAD3W (O : OpaqueWK) (B : PmObl7 wst Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : WSt → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitC (locPlatC_wit O) K0.toKLayoutV Ch0)
    (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem) (hM0 : MapsP K0 s0)
    (h : ExecVX4eC (famAD2 wst ar hA a0 B) (StartAD3 wst ar hA a0 B (arI := warI) (AR := wAR) (MR := ipiMR))
      (locPlatC_wit O) s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_localAD3_C wst ar hA a0 (locPlatC_wit O) (locPlatCR_wit O).run B h0 hA0 hB hc0 hM0 h hq

end Fl4Proofs.P2.Wit
