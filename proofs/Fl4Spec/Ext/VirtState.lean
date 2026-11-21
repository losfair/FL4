/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
the abstract VCPU state** (proofs/VIRT-PLAN.md §3).

A VCPU is (l4v ARM_HYP `Arch_Structs_A.vcpu` for the shape: `vcpu_tcb`,
`vcpu_regs`):

* `tcb`: the bound thread (FL4 word `vcpu::TCB`; the TCB's `tl::VCPU` word
  is the other half of the binding, `VirtExt.tcbVcpu`);
* `fields`: the backend's field table (`Ext/VirtFields`), indexed by
  canonical fields only;
* `exit`: the pending-exit record, the 30 VMEnter message registers of
  libsel4 `sel4/arch/vmenter.h` (one layout for both backends), with the
  flags `valid` (the last entry reached the guest and exited; FL4 word
  `VALID`) and `pending` (an exit for the VMM not yet reported; `PENDING`);
* `ioDenied`: the VT-x I/O bitmap (FL4 `vcpu::IO`, a set bit traps the
  port; SDM Vol. 3C §25.6.4). SVM uses one shared all-intercepting I/O
  permission map, so the bitmap is VMX-only.

The extension state `VirtExt` holds the VCPUs by object reference and the
TCB → VCPU binding; `VState Z` pairs it with the ported `State Z`. The
kernel heap keeps the ported `.archObj (.vcpu _)` object as the type
marker of the VCPU's memory (retype, detype, `obj_bits`); its words are not
read by the extension (VIRT-PLAN.md §3.3: the shape change that would
put `VcpuState` there instead).

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtSanitize

namespace Fl4Spec

noncomputable section
open Classical

/-- The number of VMEnter message registers (`SEL4_VMENTER_NUM_FAULT_MSGS`). -/
def vmenterNumMrs : Nat := 30

/-- VMEnter MR indices (libsel4 `vmenter.h`, `kernel_fault_context_t`). -/
def vmenterMrIp : Fin 30 := 0
def vmenterMrCtl : Fin 30 := 1
def vmenterMrIntr : Fin 30 := 2
def vmenterMrReason : Fin 30 := 3
def vmenterMrQual : Fin 30 := 4
def vmenterMrInsnLen : Fin 30 := 5
def vmenterMrGpa : Fin 30 := 6
def vmenterMrRflags : Fin 30 := 7
def vmenterMrGuestInt : Fin 30 := 8
def vmenterMrCr3 : Fin 30 := 9
/-- MR 10 + i is GPR i (EAX, EBX, ECX, EDX, ESI, EDI, EBP, R8..R15). -/
def vmenterMrGpr (i : Fin 15) : Fin 30 := ⟨10 + i.val, by omega⟩
def vmenterMrCr2 : Fin 30 := 29

/-- The pending-exit record (module docstring). -/
structure ExitRecord where
  valid : Bool
  pending : Bool
  mrs : Fin 30 → Word

/-- The abstract VCPU (module docstring). -/
structure VcpuState where
  tcb : Option ObjRef
  fields : VField → Word
  exit : ExitRecord
  ioDenied : BitVec 16 → Bool

namespace VcpuState

/-- A field's value (through its canonical place). -/
def get (k : VirtKind) (v : VcpuState) (f : VField) : Word := v.fields (f.canon k)

/-- Set a field (its canonical place). -/
def set (k : VirtKind) (v : VcpuState) (f : VField) (x : Word) : VcpuState :=
  { v with fields := Function.update v.fields (f.canon k) x }

end VcpuState

/-- FL4 `vcpu::reset_svm`'s value of a save-area word (APM Vol. 2
§15.5 / the x86 reset state, Table 14-1 of the APM: real mode at
F000:FFF0, data segments writable, CS executable, LDTR and TR system
segments, EFER.SVME, CR0.ET, DR6/DR7/RFLAGS reset values, the power-on
PAT). Zero elsewhere in the save area (FL4 zeroes `0x400..END`). -/
def svmResetValue (off : Word) : Word :=
  if off = 0x410 then 0xffff_009b_f000
  else if off = 0x418 then 0xffff_0000
  else if off ∈ Svm.segAttrOffsets then
    let attr : Word := if off = 0x470 then 0x82 else if off = 0x490 then 0x8b else 0x93
    0xffff_0000_0000 ||| (attr <<< 16)
  else if off = Svm.efer then 1 <<< 12
  else if off = Svm.cr0 then 0x10
  else if off = Svm.dr6 then 0xffff_0ff0
  else if off = Svm.dr7 then 0x400
  else if off = Svm.rflags then 2
  else if off = Svm.rip then 0xfff0
  else if off = Svm.gPat then 0x0007_0406_0007_0406
  else 0

/-- FL4 `vcpu::reset_svm` on the field table: the save area to the reset
state; RAX (canonically GPR 0) is a save-area word and becomes 0, as
`vm::run` sets FL4's `REGS[0]` after a shutdown exit. -/
def svmReset (fs : VField → Word) : VField → Word
  | .vmcb off => if Svm.save ≤ off ∧ off < Svm.svmEnd then svmResetValue off else fs (.vmcb off)
  | .gpr i => if i = 0 then 0 else fs (.gpr i)
  | f => fs f

/-- FL4 `vcpu::init` on SVM: reset state, FL4's forced intercepts, virtual
interrupt masking (V_INTR_MASKING, APM Vol. 2 §15.21.1), nested paging on. -/
def svmInitFields : VField → Word :=
  let fs := svmReset fun f => if f = .msr msrXcr0 then hostXcr0 else 0
  fun f =>
    if f = .vmcb Svm.interceptCr then 0xffff_ffff_0010_0000
    else if f = .vmcb Svm.interceptExc then vcpuExceptions ||| (Svm.i1Forced <<< 32)
    else if f = .vmcb Svm.interceptMisc2 then Svm.i2Forced
    else if f = .vmcb Svm.intCtl then 1 <<< 24
    else if f = .vmcb Svm.nestedCtl then 1
    else fs f

/-- FL4 `vcpu::init` on VMX: every writable field at its sanitized zero
(`sanitizeVmcs f 0`), the entry controls with "IA-32e mode guest" (bit 9),
RFLAGS's fixed bit 1, the power-on PAT. -/
def vmxInitFields : VField → Word := fun f =>
  if f = .msr msrXcr0 then hostXcr0
  else if f = .vmcs Vmx.controlEntryControls then
    match sanitizeVmcs Vmx.controlEntryControls (1 <<< 9) with
    | .ok x => x
    | .error _ => 0
  else if f = .vmcs Vmx.guestRflags then 2
  else if f = .vmcs Vmx.guestPat then 0x0007_0406_0007_0406
  else match f with
    | .vmcs e => match sanitizeVmcs e 0 with
      | .ok x => x
      | .error _ => 0
    | _ => 0

/-- A new VCPU (FL4 `vcpu::init`; l4v ARM_HYP `default_vcpu`): unbound, no
exit, every I/O port trapped, XCR0 the host's. -/
def initVcpu (k : VirtKind) : VcpuState where
  tcb := none
  fields := if k = .svm then svmInitFields else vmxInitFields
  exit := ⟨false, false, fun _ => 0⟩
  ioDenied := fun _ => true

/-- The extension state (module docstring). -/
structure VirtExt where
  vcpus : ObjRef → Option VcpuState
  /-- The TCB's VCPU (FL4 `tl::VCPU`; l4v ARM_HYP `tcb_vcpu` of
  `arch_tcb`). -/
  tcbVcpu : ObjRef → Option ObjRef

/-- The state with no VCPUs. -/
def VirtExt.empty : VirtExt := ⟨fun _ => none, fun _ => none⟩

/-- The ported state with the virtualization extension. -/
structure VState (Z : Type) where
  base : State Z
  virt : VirtExt

/-- FL4 `vcpu::enter`'s staging of a VMEnter request (MR0..2: guest RIP,
primary controls / SVM vector-3 intercepts, event injection), sanitized,
and the exit record emptied. -/
def VcpuState.enter (k : VirtKind) (v : VcpuState) (ip ctl intr : Word) : VcpuState :=
  let v1 := if k = .svm then
      let v1 := v.set k (.vmcb Svm.rip) ip
      let v1 := v1.set k (.vmcb Svm.interceptExc)
        (svmEnterIntercepts (v1.get k (.vmcb Svm.interceptExc)) ctl)
      v1.set k (.vmcb Svm.eventInj) (intr &&& Svm.eventMask)
    else
      let v1 := v.set k (.vmcs Vmx.guestRip) ip
      let v1 := v1.set k (.vmcs Vmx.controlPrimaryProcessorControls) (vmxEnterPrimary ctl)
      v1.set k (.vmcs Vmx.controlEntryInterruptionInfo) (intr &&& 0xffff_ffff)
  { v1 with exit := { v1.exit with valid := false, pending := false } }

/-- The entry state VMEnter reports when no exit happened (FL4
`vcpu::report`): the staged RIP, controls and injection. -/
def VcpuState.entryIp (k : VirtKind) (v : VcpuState) : Word :=
  if k = .svm then v.get k (.vmcb Svm.rip) else v.get k (.vmcs Vmx.guestRip)
def VcpuState.entryCtl (k : VirtKind) (v : VcpuState) : Word :=
  if k = .svm then v.get k (.vmcb Svm.interceptExc) >>> 32
  else v.get k (.vmcs Vmx.controlPrimaryProcessorControls)
def VcpuState.entryIntr (k : VirtKind) (v : VcpuState) : Word :=
  if k = .svm then v.get k (.vmcb Svm.eventInj)
  else v.get k (.vmcs Vmx.controlEntryInterruptionInfo)

/-- The result of a VMEnter (FL4 `vcpu::report`): the 30 MRs, the
message-info word (`SEL4_VMENTER_RESULT_FAULT` 1 for a VMM exit,
`SEL4_VMENTER_RESULT_NOTIF` 0), and the badge register (the
notification's badge, 0 for an exit). `none` is a thread whose VCPU is
gone (all MRs 0). -/
structure VmenterResult where
  mrs : Fin 30 → Word
  msgInfo : Word
  badge : Word

/-- FL4 `vcpu::report` (module docstring; VIRT-PLAN.md §5.3). A saved exit
is preferred to a notification; without a valid exit the entry state and
current guest registers are reported. -/
def vmenterReport (k : VirtKind) (vo : Option VcpuState) (badge : Word) : VmenterResult :=
  match vo with
  | none => ⟨fun _ => 0, 0, badge⟩
  | some v =>
    let pending := v.exit.pending
    let valid := v.exit.valid
    let mr : Fin 30 → Word := fun i =>
      if ¬ valid ∧ i = vmenterMrIp then v.entryIp k
      else if ¬ valid ∧ i = vmenterMrCtl then v.entryCtl k
      else if ¬ valid ∧ i = vmenterMrIntr then v.entryIntr k
      else if h : ¬ valid ∧ 10 ≤ i.val ∧ i.val < 25 then
        v.get k (.gpr ⟨i.val - 10, by have := h.2.2; omega⟩)
      else if ¬ valid ∧ i = vmenterMrRflags then
        (if k = .svm then v.get k (.vmcb Svm.rflags) else v.get k (.vmcs Vmx.guestRflags))
      else if ¬ valid ∧ i = vmenterMrGuestInt then
        (if k = .svm then v.get k (.vmcb Svm.intState) else v.get k (.vmcs Vmx.guestInterruptability))
      else if ¬ valid ∧ i = vmenterMrCr3 then
        (if k = .svm then v.get k (.vmcb Svm.cr3) else 0)
      else if ¬ valid ∧ i = vmenterMrCr2 then v.get k (.msr msrCr2)
      else if ¬ pending ∧ (i = vmenterMrReason ∨ i = vmenterMrQual) then 0
      else if pending ∨ valid then v.exit.mrs i
      else 0
    ⟨mr, if pending then 1 else 0, if pending then 0 else badge⟩

/-- The VCPU after a report: no pending exit (FL4 clears `PENDING`). -/
def VcpuState.reported (v : VcpuState) : VcpuState :=
  { v with exit := { v.exit with pending := false } }

end

end Fl4Spec
