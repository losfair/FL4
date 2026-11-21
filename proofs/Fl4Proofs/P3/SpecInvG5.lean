/-
P3 (DESIGN.md §9), invariant line g5a (KENTRY-PLAN g5a; INV-PLAN §2, the
spec-only / joint split): **three entry premises of `JEntryAtR3` as spec-only
invariants** (spec side only; imports only spec-invariant modules, no `JAtZ`
cone).

`JEntryAtR3.handlers` (`HandlersActive`), `.ports` (`IoPortsAlloc`) and `.urz`
(`UtZero`) are statements about FL4's slots read through the CSpace relation:
at a `JAtZ` state each is equivalent to a statement about the spec's caps alone
(`StateRel` relates every slot of the typed heap to the spec's cap there;
`IrqRel` / `IoRel` relate the IRQ states / the IO-port bitmap). So they are
carried on the spec side (where l4v carries them), not as `JExt` fields:
* `SpecIrqH σ` (l4v `valid_irq_handlers` with `valid_cap`'s IRQ bound): every
  IRQ handler cap of the spec's CSpace is for an IRQ up to `maxIRQ` that is not
  inactive;
* `SpecIoP σ` (l4v `valid_ioports`): every IO-port cap's ports are allocated;
* `SpecUtZ σ` (l4v `untyped_ranges_zero`): the spec's memory is zero in the
  free part of every non-device untyped cap.
A fourth one replaces the Thread path's `hFr` (ReadFPU's destination frame,
XTopJointReadFpu's `FpuFrameJHyp`, KENTRY-PLAN g4a P1):
* `SpecFrPg σ` (l4v `valid_cap` of a non-device `PageCap`: `typ_at (AArch
  (AUserData sz)) p`, weakened to "inside" for FL4's DeriveSubframe aliases):
  every non-device page cap's range lies in one non-device spec data page.
`SInvI σ` bundles them. `SInvI.frame`: kept by a step keeping every cap
(`capAt`), the interrupt states, the allocated IO ports and the memory (the
syscall entry's FaultIP write and passing budget check, XTopJointKEntry35E).
Their preservation over a whole syscall / event (a `kentry_sinvI`) is the
remaining spec-only obligation (INV-PLAN §4 G1 shape), not done here.
-/
import Fl4Proofs.P3.SpecInvUtR
import Fl4Proofs.P3.SpecInvVfhR
open Classical

namespace Fl4Proofs.P3.SInvR.G5
open Fl4Spec Fl4Proofs.P3

noncomputable section

/-- **[J] spec** (l4v `valid_irq_handlers`, `valid_cap`): every IRQ handler cap
is for a valid, non-inactive IRQ. -/
def SpecIrqH (σ : State Unit) : Prop :=
  ∀ sl irq, SInvU.capAt σ sl = some (.irqHandlerCap irq) →
    irq ≤ maxIRQ ∧ σ.interruptStates irq ≠ .irqInactive

/-- **[J] spec** (l4v `valid_ioports`): every IO-port cap's ports allocated. -/
def SpecIoP (σ : State Unit) : Prop :=
  ∀ sl f l, SInvU.capAt σ sl = some (.archObjectCap (.ioPortCap f l)) →
    f ≤ l ∧ ∀ p, f ≤ p → p ≤ l → σ.archState.x64AllocatedIoPorts p = true

/-- **[J] spec** (l4v `untyped_ranges_zero`): the memory is zero in the free
part of every non-device untyped cap. -/
def SpecUtZ (σ : State Unit) : Prop :=
  ∀ sl ptr sz fi, SInvU.capAt σ sl = some (.untypedCap false ptr sz fi) →
    ∀ a : Word, ptr.toNat + fi ≤ a.toNat → a.toNat < ptr.toNat + 2 ^ sz → σ.machineState.underlyingMemory a = 0

/-- **[J] spec** (l4v `valid_cap` of a non-device `PageCap`, with FL4's
DeriveSubframe aliases inside their page): every non-device page cap's range
lies in one non-device spec data page. -/
def SpecFrPg (σ : State Unit) : Prop :=
  ∀ sl p rt mt vms mp, SInvU.capAt σ sl = some (.archObjectCap (.pageCap false p rt mt vms mp)) →
    ∃ (o : ObjRef) (vms' : VMPageSize), σ.kheap o = some (.archObj (.dataPage false vms')) ∧
      o.toNat ≤ p.toNat ∧ p.toNat + 2 ^ pageBitsForSize vms ≤ o.toNat + 2 ^ pageBitsForSize vms'

/-- **The four spec-only entry facts** (module docstring). -/
structure SInvI (σ : State Unit) : Prop where
  irqH : SpecIrqH σ
  ioP : SpecIoP σ
  utZ : SpecUtZ σ
  frP : SpecFrPg σ

variable {σ σ' : State Unit}

/-- **`SInvI` across a step keeping the caps, the interrupt states, the
allocated IO ports, the memory and the arch objects.** -/
theorem SInvI.frame (h : SInvI σ) (hcap : ∀ sl, SInvU.capAt σ' sl = SInvU.capAt σ sl)
    (hi : σ'.interruptStates = σ.interruptStates)
    (ha : σ'.archState.x64AllocatedIoPorts = σ.archState.x64AllocatedIoPorts)
    (hm : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory)
    (hao : ∀ o ao, σ.kheap o = some (.archObj ao) → σ'.kheap o = some (.archObj ao)) : SInvI σ' where
  irqH sl irq hc := by rw [hi]; exact h.irqH sl irq (by rw [← hcap]; exact hc)
  ioP sl f l hc := by rw [ha]; exact h.ioP sl f l (by rw [← hcap]; exact hc)
  utZ sl ptr sz fi hc a h1 h2 := by rw [hm]; exact h.utZ sl ptr sz fi (by rw [← hcap]; exact hc) a h1 h2
  frP sl p rt mt vms mp hc := by
    obtain ⟨o, vms', hk, h1, h2⟩ := h.frP sl p rt mt vms mp (by rw [← hcap]; exact hc)
    exact ⟨o, vms', hao o _ hk, h1, h2⟩

/-- `capAt` after replacing one object by a TCB with the same caps (the
`FaultIP` write: `capOpt` of the new TCB is the old one's, `SInv.vfh_capAt`). -/
theorem capAt_updTcb {t : ObjRef} {x x' : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hcm : tcbCnodeMap x' = tcbCnodeMap x) (ek : σ'.kheap = Function.update σ.kheap t (some (.tcb x'))) :
    ∀ sl, SInvU.capAt σ' sl = SInvU.capAt σ sl := by
  intro sl
  rw [SInv.vfh_capAt, SInv.vfh_capAt, ek]
  by_cases hp : sl.1 = t
  · rw [hp, Function.update_self, hk]
    show tcbCnodeMap x' sl.2 = tcbCnodeMap x sl.2
    rw [hcm]
  · rw [Function.update_of_ne hp]

/-- The arch objects after replacing a TCB by a TCB. -/
theorem archObj_updTcb {t : ObjRef} {x : Tcb} {ko : KernelObject} (hk : σ.kheap t = some (.tcb x))
    (ek : σ'.kheap = Function.update σ.kheap t (some ko)) :
    ∀ o ao, σ.kheap o = some (.archObj ao) → σ'.kheap o = some (.archObj ao) := by
  intro o ao ho
  rw [ek, Function.update_of_ne]
  · exact ho
  · rintro rfl; rw [hk] at ho; cases ho

end

end Fl4Proofs.P3.SInvR.G5
