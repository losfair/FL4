/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
the backend constant** (proofs/VIRT-PLAN.md §2).

FL4 selects its virtualization backend once, at boot (README.md "x86
virtualization"): none (no VCPU/EPT objects can be retyped), Intel VT-x
or AMD-V. FL4's `Arch::virtualization()` returns 0, 1 or 2. AArch64 EL2
(upstream `arch/aarch64/vcpu.rs`) is a later backend: `armEl2` is a
constructor so that the shared definitions are written with it in mind,
but nothing here specifies it.

The hardware capability words FL4 reads through `Arch::vcpu_capability`
(the VMX capability MSRs `IA32_VMX_*` 0x480..0x491, the host's XCR0
(field 0) and the host's canonical-address width (field 1)) are
underspecified machine constants, in the style of l4v's `MachineOps`:
one opaque structure `virtPlatform`, constrained only by the facts the
boot code checks (none are needed by the definitions so far). Changing
the backend at run time is not modelled: FL4 never downgrades a selected
backend (README.md).

l4v has no x86 VCPU spec; the structure follows ARM_HYP's `VCPU_A` and
`Arch_Structs_A.vcpu` (l4v master `spec/abstract/ARM_HYP`).

The ported modules are not changed.
-/
import Fl4Spec

namespace Fl4Spec

noncomputable section
open Classical

/-- The virtualization backend (FL4 `Arch::virtualization()`: 0, 1, 2;
`armEl2` is reserved for the AArch64 port and not specified). -/
inductive VirtKind where
  | none
  | vmx
  | svm
  | armEl2
deriving DecidableEq, Repr, Inhabited

/-- FL4's numbering of the backend (`Arch::virtualization()`). -/
def VirtKind.code : VirtKind → Nat
  | .none => 0
  | .vmx => 1
  | .svm => 2
  | .armEl2 => 3

/-- The underspecified platform constants of virtualization: the
backend and `Arch::vcpu_capability`. -/
structure VirtPlatform where
  kind : VirtKind
  /-- `Arch::vcpu_capability f`: for VMX the capability MSR `f`
  (`IA32_VMX_PINBASED_CTLS` 0x481, ..., `IA32_VMX_PROCBASED_CTLS2`
  0x48b; allowed-0 settings in bits 31:0, allowed-1 in 63:32, Intel SDM
  Vol. 3D App. A.3), `IA32_VMX_CR0_FIXED0/1` (0x486/0x487),
  `IA32_VMX_CR4_FIXED0/1` (0x488/0x489), `IA32_VMX_MISC` (0x485); the
  host XCR0 (0); the host's canonical-address width (1). -/
  capability : Word → Word
  /-- FL4 is built for x86-64: the AArch64 backend is never selected. -/
  kind_ne_arm : kind ≠ .armEl2

instance : Inhabited VirtPlatform := ⟨⟨.none, fun _ => 0, by decide⟩⟩

/-- The platform (stands for the boot-time selection and the capability
MSRs; underspecified). -/
opaque virtPlatform : VirtPlatform

/-- The backend FL4 selected at boot. -/
def virtKind : VirtKind := virtPlatform.kind

/-- `Arch::vcpu_capability`. -/
def vcpuCapability (f : Word) : Word := virtPlatform.capability f

/-- The host XCR0 (`vcpu_capability(0)`): the XSAVE features a guest
may enable (Intel SDM Vol. 1 §13.3). -/
def hostXcr0 : Word := vcpuCapability 0

/-- The host's canonical-address width (`vcpu_capability(1)`, 48 for
4-level paging, 57 for LA57). -/
def canonWidth : Word := vcpuCapability 1

/-- Whether VCPU and EPT objects exist at all (FL4 `untyped.rs`: retyping
the VT-x object types returns `InvalidArgument 0` when
`virtualization() == 0`). -/
def virtEnabled : Bool := virtKind ≠ .none

/-- The field operations of a backend (ReadVMCS/WriteVMCS for `vmx`,
ReadVMCB/WriteVMCB for `svm`) return `IllegalOperation` on the other
(README.md "x86 virtualization"). -/
def VirtKind.isVmx (k : VirtKind) : Bool := k = .vmx
/-- See `VirtKind.isVmx`. -/
def VirtKind.isSvm (k : VirtKind) : Bool := k = .svm

end

end Fl4Spec
