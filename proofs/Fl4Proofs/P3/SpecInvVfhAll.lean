/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §2/§4, invA): **VfhAll: every
TCB's fault handler is valid** (l4v `valid_tcb`'s `valid_fault_handler`
slice; spec side only, outside the JAtZ cone).

* `VfhAll σ := TI vfhQ σ`, `vfhQ x := validFaultHandler x.tcbFaultHandler`
  (Decode_A.valid_fault_handler: an endpoint cap with the handler rights, or
  the null cap).
* Consumers at the top (KENTRY-PLAN fin1, `kernel_entryJ26P`): `JEntryAt.vfh`
  and `KDispHyps*.recv`'s valid fault handler of `ct`, and `JMidVfhHyp` [J]
  (ct's handler after the first phase): `VfhAll.ct` gives the ct form.
* `boot_vfhAll`: the initial state (the idle TCB's handler is null).
* Preservation over the syscall entry is NOT proved here (invA handoff,
  KENTRY-PLAN invA): its writer is `setCap` into a TCB's slot 3, reached by
  every cap write whose slot comes from a lookup (cte_insert/move/swap, retype,
  IPC cap transfer, arch cap updates, deletion's zombies); l4v needs
  `valid_cap`/`cte_wp_at` facts that the written slot is a CNode slot or
  already holds a non-handler cap, plus `checkHandlerEp` at decode for the TCB
  installs.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

/-- A TCB whose fault handler is valid. -/
def vfhQ (x : Tcb) : Prop := validFaultHandler x.tcbFaultHandler

/-- Every TCB's fault handler is valid (l4v `valid_tcb`, `valid_fault_handler`). -/
abbrev VfhAll (σ : State Unit) : Prop := TI vfhQ σ

/-- The current thread's handler (`JEntryAt.vfh`'s form). -/
theorem VfhAll.ct {σ : State Unit} (h : VfhAll σ) :
    ∀ x, σ.kheap σ.curThread = some (.tcb x) → validFaultHandler x.tcbFaultHandler :=
  fun x hx => h _ x hx

/-- **VfhAll at boot** (invA (d)): the initial state `initASt`. -/
theorem boot_vfhAll : VfhAll (initASt (Z := Unit)) := by
  intro p x hp
  simp only [initASt, initKheap, Function.update_apply] at hp
  split_ifs at hp <;> (try cases hp) <;> (try (unfold vfhQ validFaultHandler; exact Or.inr rfl))
  all_goals (split_ifs at hp <;> cases hp)

end

end Fl4Proofs.P3.SInv
