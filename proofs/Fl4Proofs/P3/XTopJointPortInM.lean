/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr10 GOAL 1): **why the port-in
premise `PortInVal` cannot be restated per state through the machine
relation `MR`** (a FINDING, stated formally; `JEntryGlobM.portIn` is kept).

`PortInVal arI` (XTopPortIn, [P]) asks, for every spec state `σ`, an outcome
of the spec's `In` access returning FL4's value. The natural per-state form
is `MachPortIn arI MR` below (the shape of `MachPlat.irqPending`/`take`: at
an `MR`-related machine state the spec's read returns FL4's value, and `MR`
holds after). It buys nothing:

* The spec's read is `machineOpLift (inNImpl port); gets inNVal`
  (Fl4Spec/Machine.lean): `inNImpl` is an opaque nondeterministic operation
  on `machineStateRest` and `inNVal` an opaque function of the whole machine
  state, so the value depends on the parts of the machine state outside the
  four fields `MR` may read.
* `MachPlat.frame` (XTopJointMachRel, not editable here) makes every `MR`
  blind to everything except `irqMasks`, `irqState`, `timeState`,
  `lastMachineTime`; the P line needs it: `MachPlat.mfKeep` carries `MR`
  over every spec step keeping those four fields, including every
  `machineOpLift` (MachFieldFam's `mkf_machineOpLift`: `invalidateASID`,
  `writeCR3`, the FPU operations, `out8`… move `machineStateRest` by opaque
  outcomes FL4's arch state does not see).
* Hence (`MachPortIn.frameAll`): under `MachPlat`, `MachPortIn` at one
  related state is `PortInVal`'s conclusion at EVERY state agreeing with it
  on those four fields, whatever its rest, device state, memory and FPU
  flag: the same ∀-over-states content as `PortInVal`, restricted only in
  four fields the read does not depend on. Neither is provably satisfiable
  by any platform (`inNVal` is opaque; `modelArch.port_in` returns 0).

A genuine per-state form needs a second machine relation that sees
`machineStateRest` (l4v: the whole `machine_state` is shared), carried from
the entry [J] without `frame`, with every spec `machineOpLift` matched by an
FL4 arch operation that reproduces its opaque outcome: not this line.
-/
import Fl4Proofs.P3.XTopJointMachRel
import Fl4Proofs.P3.XTopPortIn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

section
variable {A : Type} (arI : machine.Arch A)

/-- **The per-state port read through `MR`** (module docstring; NOT used as
a premise: `MachPortIn.frameAll` shows it is `PortInVal` in substance). At a
state whose machine state is `MR`-related to `a`, FL4's `port_in` value is
the spec's `In` result at some outcome, the memory kept, `MR` after. -/
def MachPortIn (MR : A → Fl4Spec.MachineState → Prop) : Prop :=
  ∀ (a a' : A) (p z v : U64) (σ : Fl4Spec.State Unit), MR a σ.machineState →
    arI.port_in a p z = ok (v, a') →
    ∃ ms : Fl4Spec.MachineState, ms.underlyingMemory = σ.machineState.underlyingMemory ∧
      (.ok [v.bv], { σ with machineState := ms }) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
        (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 p.val) (inData z.val)))).run σ).1 ∧ MR a' ms

variable {arI} {MR : A → Fl4Spec.MachineState → Prop}

/-- **FINDING (module docstring): under `MachPlat`, `MachPortIn` at one
related machine state `ms` gives `PortInVal`'s conclusion at every spec
state whose machine state agrees with `ms` on the four `MR`-visible fields**
(any `machineStateRest`, `deviceState`, memory, FPU flag, any kernel
state). -/
theorem MachPortIn.frameAll (hM : MachPlat arI MR) (h : MachPortIn arI MR) {a a' : A} {p z v : U64}
    {ms : Fl4Spec.MachineState} (hR : MR a ms) (hv : arI.port_in a p z = ok (v, a')) (σ : Fl4Spec.State Unit)
    (e1 : σ.machineState.irqMasks = ms.irqMasks) (e2 : σ.machineState.irqState = ms.irqState)
    (e3 : σ.machineState.timeState = ms.timeState)
    (e4 : σ.machineState.lastMachineTime = ms.lastMachineTime) :
    ∃ ms' : Fl4Spec.MachineState, ms'.underlyingMemory = σ.machineState.underlyingMemory ∧
      (.ok [v.bv], { σ with machineState := ms' }) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
        (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 p.val) (inData z.val)))).run σ).1 := by
  obtain ⟨ms', hu, hm, -⟩ := h a a' p z v σ (hM.frame a ms _ hR e1 e2 e3 e4) hv
  exact ⟨ms', hu, hm⟩

end

end Fl4Proofs.P3
