/-
P3 (p3J gen 19): **the interrupt clause with its stable ghosts exposed, at U45nv's premises** — the ghost half of
gen 18's `IrqStab` [J] discharged; `IrqStab` narrowed to `IrqFoot` [J] (footprint and two carry facts only).

* **`irq_stabU45`**: from `RunCK s a σ` (U40's joint reach and the cap-kind invariant) and *any* `JAtZ Z H Cs …`
  at `s` (with `VxE Z`), under U45nv's globals (the subset the interrupt path reads), every
  `handle_interrupt_entry … w` with `IrqHw` ends at an `EvOut false .interrupt` outcome `σ'` that is
  `RunCK` **and** `JStab Z H Cs` (`JAtZ (Z.mv G' V') H Cs …`: H, Cs, the typed heap, TCB and SC sets unchanged).
  Proof: P3JStIrqK's `Fl4ProofsK.P3.SInvR.G5.irq_entryStU41` (StPostIrqEv's stable-ghost run carried through the
  U33 / U42 transports) with `MachPlatF.toT` (as U33), `PPPlatA := ⟨hPAi, TimeAgree.mb⟩` (as U30) and the finish
  record from U43's `kFinEv42_of` and U42's `KFinEv42.toK` (as U43 / U42 discharge it); `JReachU40` at the outcome
  from `JReachU17` there and the spec facts `EvOut.irqCarry` / `EvOut.ioaRel` (as U36I / U40), `CKI` by
  `cki_evOut`.
* **`IrqFoot` [J]** (what is left of `IrqStab`): at every `JAtZ` ghosts of the entry state, for every outcome
  `σ'` and every MDB ghost / VSpace sets `G' V'` with `JAtZ (Z.mv G' V') H Cs …` there, the FL4 run writes only
  `ProjW H Cs s`, no spec object appears where there was none (`KhNoneKeep`) and every RAM untyped cap of `G'`
  was one of `Z.G` at the same slot (`UtKeep`). It no longer asks for the ghosts (`irq_stabU45` gives them).
  Not discharged: P1's `entryXG` footprint `Cur0W` allows every node word but 88 (so other cores' `IDLE_*`) and
  user words outside the projection's objects (`UserW`); a `ProjW`-sharp footprint is a new P1 walk.
* **`kernel_entry_runMcW_irqF`**: gen 18's `kernel_entry_runMcW_irq` with `IrqFoot` in place of `IrqStab`.

Named premises: `IrqFoot` [J] (above); U45nv's globals as in `kernel_entry_runCK` (`hFpu`, `hFW` [P] etc.). No
sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JStIrqK
import Fl4Proofs.P3.P3JMcIrq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **`IrqFoot` [J]** (module docstring): the interrupt run's footprint and carry facts at every `JAtZ` ghosts. -/
def IrqFoot (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∀ (σ' : Fl4Spec.State Unit) (G' : MdbGhost) (V' : XVs)
        (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), EvOut false .interrupt σ σ' →
        JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' r.1 r.2 σ' →
        P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ∧ KhNoneKeep σ σ' ∧ UtKeep (L := L) Z.G G' s r.1 ⦄

variable {arI AR MR}

set_option maxHeartbeats 8000000 in
/-- **The interrupt clause at given ghosts, stable, at U45nv's premises** (module docstring). -/
theorem irq_stabU45 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunCK (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (w : U64) (a1 : A) (hI : IrqHw AR MR a a1 σ w) :
    syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
      RunCK (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  obtain ⟨⟨⟨hJ17, hC⟩, hIoa⟩, hCK⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -⟩ := jreach_invU3 hnd hJ17.1
  have hm := hX.sb.1.1.vim
  have hG := Fl4ProofsK.P3.SInvR.G5.irq_entryStU41 hARI hA hnd (MachPlatF.toT hM hIp) hKD ⟨hPAi, hT.mb⟩ hIA hT
    hmax htu hRef hDR hFpu hJ17 J w a1 hI (KFinEv42.toK (kFinEv42_of hFpu hFW hA) hA)
  refine WP.spec_mono hG ?_
  rintro r ⟨σ', hO, hJ', hSt⟩
  exact ⟨σ', hO, ⟨⟨⟨hJ', EvOut.irqCarry hm hC hO⟩, EvOut.ioaRel hIoa hO⟩, cki_evOut hCK hO⟩, hSt⟩

set_option maxHeartbeats 4000000 in
/-- **The interrupt entry on any core, through `RunMcW`, with `IrqFoot`** (module docstring; `hFt` [J]). -/
theorem kernel_entry_runMcW_irqF [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcW (L := L) arI AR MR s a σ)
    (hFt : IrqFoot (L := L) arI AR MR s a σ) :
    ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
        RunMcW (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro w a1 hw
  obtain ⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (irq_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hDR hFpu hFW hC J
    w a1 hw) (hFt Z H Cs Ac Lst D J hV w a1 hw)) ?_
  rintro r ⟨⟨σ', hO, hC', G', V', Ac', Lst', D', J'⟩, hK⟩
  obtain ⟨hW, hKk, hU⟩ := hK σ' G' V' Ac' Lst' D' hO J'
  exact ⟨σ', hO, hC', jAtMcW_step J hF J' inferInstance hW hKk hU⟩

end

end Fl4Proofs.P3.Mc
