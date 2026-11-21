/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
guest execution and the trusted layer's contract** (proofs/VIRT-PLAN.md
§7, §8, §10).

1. **Guest execution is a nondeterministic oracle**, as l4v's
   `do_user_op` (ADT_A) is for user code. While a thread is
   `runningVM`, one guest step (`GuestStep`) may change exactly: the
   guest-changed fields of that thread's VCPU (`VField.guestChanged`),
   its exit record (any value), and bytes of frames mapped writable under
   the thread's guest root (`GuestWritableByte` of `guestRootOf`). Nothing
   else changes: not the VCPU's binding, I/O bitmap or other fields, not
   another VCPU, not the ported state but those memory bytes (the
   isolation frame). It ends in an exit for the VMM (`pending`) or a host
   exit, possibly with a host interrupt the exit accepted.
   Guest-linear translations and TLBs are not modelled. GPA→HPA is exact:
   the step reads the guest tables of the state it runs in, so once an
   EPT unmap has returned no guest step on any core reaches the frame
   (FL4: `ept::invalidate` is synchronous on every core recorded in the
   root, `kernel/entry.rs` records the core under the serial gate before
   entry).
2. **The trusted hardware layer's contract** (`fl4-arch-x86_64` `vm::run`
   and its assembly) is the named premise shape `VmRunContract` [P]: the
   layer's effect, seen through a refinement relation, is a `GuestStep`;
   and its word-level frame `VmRunFrame` [P]: after a VM exit only the
   VCPU words of guest-changed fields, the exit area, the layer's cache
   words and the writable guest frames differ. No l4v counterpart beyond
   `do_user_op`'s `user_memory_update` frame (l4v trusts the machine).
3. **P3x for virtualization**: `NoVirtObjects`, the states with no VCPU
   and no guest table, and the statement shape `P3xVirt` (VIRT-PLAN.md
   §10).

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtEpt

namespace Fl4Spec

noncomputable section
open Classical

/-- How a guest step ends, for the kernel (FL4 `vm::run`'s return value):
the host interrupt the exit accepted, if any (`none` also for VMM exits). -/
structure GuestOutcome where
  hostIrq : Option Irq

/-- The fields of a VCPU's table a guest step leaves alone: the
non-canonical places (unused) and every canonical field that is not
guest-changed. -/
def VcpuFrame (k : VirtKind) (vs vs' : VcpuState) : Prop :=
  vs'.tcb = vs.tcb ∧ vs'.ioDenied = vs.ioDenied ∧
  ∀ f, (f.canon k ≠ f ∨ f.guestChanged k = false) → vs'.fields f = vs.fields f

/-- **One guest step of thread `t`** (module docstring, 1; l4v ADT_A
`do_user_op` for guests). -/
def GuestStep {Z : Type} (k : VirtKind) (t : ObjRef) (σ σ' : VState Z) (o : GuestOutcome) : Prop :=
  ∃ (tcb : Tcb) (v : ObjRef) (vs vs' : VcpuState) (m' : Word64 → Word8),
    σ.base.kheap t = some (.tcb tcb) ∧ tcb.tcbState = .runningVM ∧
    σ.virt.tcbVcpu t = some v ∧ σ.virt.vcpus v = some vs ∧
    VcpuFrame k vs vs' ∧
    (o.hostIrq ≠ none → vs'.exit.pending = false) ∧
    σ'.virt = { σ.virt with vcpus := Function.update σ.virt.vcpus v (some vs') } ∧
    σ'.base = { σ.base with machineState := { σ.base.machineState with underlyingMemory := m' } } ∧
    ∀ a, m' a ≠ σ.base.machineState.underlyingMemory a →
      GuestWritableByte σ.base (guestRootOf σ.base t) a

/-- **[P] The trusted layer's contract, abstract form** (module
docstring, 2). For any implementation state type `I`, relation `R` and
the layer's effect `run t s s' o` (one `vm::run` of thread `t`): a run
from a related state ends in a related state reached by one `GuestStep`
of the selected backend. -/
def VmRunContract {Z I : Type} (R : I → VState Z → Prop)
    (run : ObjRef → I → I → GuestOutcome → Prop) : Prop :=
  ∀ t s s' o σ, R s σ → run t s s' o → ∃ σ', GuestStep virtKind t σ σ' o ∧ R s' σ'

/-- **[P] The trusted layer's contract, word-level frame** (module
docstring, 2): kernel memory `mem` before and `mem'` after a `vm::run`
differ only in the words of the VCPU's guest-changed fields
(`fieldWords`, the layout of the refinement), the exit area
(`exitWords`: FL4 `vcpu::EXIT`, `VALID`, `PENDING`, `CR2`, `REGS`, `MSRS`),
the layer's cache words (`cacheWords`: `SVM_CPU`, the VMCB ASID, clean
bits and the physical pointers it rewrites) and the writable guest
frames (`writable`). -/
def VmRunFrame (k : VirtKind) (fieldWords : VField → Set Word) (exitWords cacheWords writable : Set Word)
    (mem mem' : Word → Word) : Prop :=
  ∀ a, mem' a ≠ mem a →
    (∃ f, f.canon k = f ∧ f.guestChanged k = true ∧ a ∈ fieldWords f) ∨
    a ∈ exitWords ∨ a ∈ cacheWords ∨ a ∈ writable

/-- No virtualization object exists (module docstring, 3): no VCPU, no
binding, and the heap holds no VCPU and no guest table. -/
def NoVirtObjects {Z : Type} (σ : VState Z) : Prop :=
  (∀ v, σ.virt.vcpus v = none) ∧ (∀ t, σ.virt.tcbVcpu t = none) ∧
  ∀ p ao, σ.base.kheap p = some (.archObj ao) →
    (∀ w, ao ≠ .vcpu w) ∧ (∀ l es, ao ≠ .ept l es)

/-- **The P3x statement shape for virtualization** (DESIGN.md §9, P3x;
VIRT-PLAN.md §10): on a state with no virtualization object, a step of
the extended kernel (`extStep`) is exactly a step of the ported one
(`portStep`) with the extension state unchanged. -/
def P3xVirt {Z : Type} (extStep : VState Z → VState Z → Prop) (portStep : State Z → State Z → Prop) :
    Prop :=
  ∀ σ, NoVirtObjects σ → ∀ σ', extStep σ σ' ↔ (portStep σ.base σ'.base ∧ σ'.virt = σ.virt)

/-- A guest step needs a VCPU: none happens without virtualization
objects. -/
theorem GuestStep.not_noVirt {Z : Type} {k : VirtKind} {t : ObjRef} {σ σ' : VState Z}
    {o : GuestOutcome} (h : GuestStep k t σ σ' o) : ¬ NoVirtObjects σ := by
  obtain ⟨_, v, _, _, _, _, _, _, hv, _⟩ := h
  intro hn
  rw [hn.1 v] at hv
  exact absurd hv (by simp)

/-- The isolation frame: a guest step changes no heap object, no other
VCPU and no binding. -/
theorem GuestStep.frame {Z : Type} {k : VirtKind} {t : ObjRef} {σ σ' : VState Z}
    {o : GuestOutcome} (h : GuestStep k t σ σ' o) :
    σ'.base.kheap = σ.base.kheap ∧ σ'.virt.tcbVcpu = σ.virt.tcbVcpu ∧
    ∃ v, σ.virt.tcbVcpu t = some v ∧ ∀ w, w ≠ v → σ'.virt.vcpus w = σ.virt.vcpus w := by
  obtain ⟨_, v, _, vs', _, _, _, hv, _, _, _, hvirt, hbase, _⟩ := h
  refine ⟨by rw [hbase], by rw [hvirt], v, hv, fun w hw => ?_⟩
  rw [hvirt]
  exact Function.update_of_ne hw _ _

end

end Fl4Spec
