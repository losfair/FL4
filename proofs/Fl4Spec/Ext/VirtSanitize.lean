/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
the sanitize policy** (proofs/VIRT-PLAN.md §4).

Pure functions, one per backend, giving the value a VMM write stores (or
the error it returns). They transliterate FL4's policy in
`crates/fl4-core/src/vcpu.rs` (`sanitize_vmcs`, `sanitize_vmcb`,
`canonical`, `valid_xcr0`, `valid_pat`, the masks), which is the
reference for FL4's *choices*; the docstrings give the architectural
reason from the vendor manuals (Intel SDM Vol. 3C/3D, AMD APM Vol. 2).
The hardware capability words are `vcpuCapability` (underspecified,
`Ext/VirtBackend`). Where FL4's policy looks inconsistent, VIRT-PLAN.md
lists it as a FINDING and the spec states FL4's behaviour.

Guest-only invalid state that VM entry itself rejects (SDM Vol. 3C §27.3
"Checking and loading guest state", APM Vol. 2 §15.5.1 "VMRUN
consistency checks") is not sanitized: such a write is stored and the
next entry fails (`VMEnter` reports a failed entry).

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtFields

namespace Fl4Spec

noncomputable section
open Classical

/-- FL4 `vcpu::CR4_ALLOWED`: the guest CR4 bits FL4 lets a guest own (VME
.. UMIP (bits 0..11), FSGSBASE, PCIDE, OSXSAVE, SMEP, SMAP). Excluded:
LA57 (12; FL4 uses 4-level paging), VMXE (13; nested VMX), SMXE (14),
PKE (22), CET (23) and the rest (SDM Vol. 3A §2.5). -/
def cr4Allowed : Word :=
  0x0fff ||| (1 <<< 16) ||| (1 <<< 17) ||| (1 <<< 18) ||| (1 <<< 20) ||| (1 <<< 21)

/-- FL4 `vcpu::CR0_OWNED`: NW (29), CD (30) and the reserved bits 6..15,
17, 19..28 of CR0 (SDM Vol. 3A §2.5): the guest never sets them (CD/NW
reach the hardware CR0, SDM Vol. 3C §26.3; under SVM there is no CR0
guest/host mask, APM Vol. 2 §15.9). -/
def cr0Owned : Word := (3 <<< 29) ||| (0x3ff <<< 19) ||| (1 <<< 17) ||| (0x3ff <<< 6)

/-- FL4 `vcpu::DEBUGCTL_ALLOWED`: BTF only (vcpu.rs comment: LBR, the
FREEZE bits, TR, BTS, BTINT drive host state; Xen XSA-269). -/
def debugctlAllowed : Word := 1 <<< 1

/-- FL4 `vcpu::PIN_ALLOWED`: external-interrupt exiting, NMI exiting,
virtual NMIs (SDM Vol. 3C §25.6.1). FL4 forces all three. -/
def pinAllowed : Word := (1 <<< 0) ||| (1 <<< 3) ||| (1 <<< 5)

/-- FL4 `vcpu::PRIMARY_ALLOWED` (SDM Vol. 3C §25.6.2). -/
def primaryAllowed : Word := 0xfbd9_9e8c

/-- FL4 `vcpu::PRIMARY_FORCED`: MWAIT (10), RDPMC (11), CR8-load (19),
CR8-store (20), MOV-DR (23), use I/O bitmaps (25), use MSR bitmaps (28),
MONITOR (29), activate secondary controls (31) exiting. -/
def primaryForced : Word :=
  (1 <<< 10) ||| (1 <<< 11) ||| (1 <<< 19) ||| (1 <<< 20) ||| (1 <<< 23) ||| (1 <<< 25) |||
  (1 <<< 28) ||| (1 <<< 29) ||| (1 <<< 31)

/-- FL4 `vcpu::SECONDARY_ALLOWED`: EPT (1), descriptor-table exiting (2),
RDTSCP (3), VPID (5; removed again by `sanitizeVmcs`), WBINVD exiting (6),
unrestricted guest (7), RDRAND exiting (11), INVPCID (12), RDSEED exiting
(16) (SDM Vol. 3C §25.6.2, Table 25-7). -/
def secondaryAllowed : Word :=
  (1 <<< 1) ||| (1 <<< 2) ||| (1 <<< 3) ||| (1 <<< 5) ||| (1 <<< 6) ||| (1 <<< 7) |||
  (1 <<< 11) ||| (1 <<< 12) ||| (1 <<< 16)

/-- FL4 `vcpu::EXIT_FORCED`: save debug controls (2), host address-space
size (9), save/load IA32_PAT (18/19), save/load IA32_EFER (20/21) (SDM
Vol. 3C §25.7.1). -/
def exitForced : Word :=
  (1 <<< 2) ||| (1 <<< 9) ||| (1 <<< 18) ||| (1 <<< 19) ||| (1 <<< 20) ||| (1 <<< 21)

/-- FL4 `vcpu::canonical`: bits 63..47 (63..56 for a 57-bit host) all
equal (SDM Vol. 1 §3.3.7.1). `width` is `canonWidth`. -/
def canonical (value width : Word) : Bool :=
  let shift : Word := if width = 57 then 56 else 47
  let top := value >>> shift
  top = 0 || top = (~~~(0 : Word)) >>> shift

/-- FL4 `vcpu::valid_xcr0` (SDM Vol. 1 §13.3, XSETBV's #GP conditions):
a subset of the host's XCR0, x87 set, AVX only with SSE, the three
AVX-512 bits together and only with SSE and AVX, MPX's two bits
together, AMX's two bits together. -/
def validXcr0 (x host : Word) : Bool :=
  x &&& ~~~host = 0 && x &&& 1 ≠ 0 && !(x &&& 4 ≠ 0 && x &&& 2 = 0) &&
  (let avx512 := x &&& 0xe0
   (avx512 = 0 || (avx512 = 0xe0 && x &&& 6 = 6)) &&
   (x &&& 0x18 = 0 || x &&& 0x18 = 0x18) &&
   (x &&& 0x60000 = 0 || x &&& 0x60000 = 0x60000))

/-- FL4 `vcpu::valid_pat`: every PAT entry is a defined memory type (0, 1,
4..7; SDM Vol. 3A §13.12.2: writing a reserved type to IA32_PAT is #GP). -/
def validPat (pat : Word) : Bool :=
  (List.range 8).all fun i =>
    let t := (pat >>> (i * 8)) &&& 255
    t ≤ 1 || (4 ≤ t && t ≤ 7)

/-- FL4 `vcpu::controls`: a VMX control word with the capability MSR's
allowed-0 settings (bits 31:0, SDM Vol. 3D App. A.3) and `forced` set,
cleared where the allowed-1 settings (bits 63:32) or `forced ∪ allowed`
do not allow it. -/
def vmxControls (msr value forced allowed : Word) : Word :=
  let cap := vcpuCapability msr
  let ones := (cap &&& 0xffff_ffff) ||| forced
  (value ||| ones) &&& (cap >>> 32) &&& (ones ||| allowed)

/-- The width mask of a VMCS field (SDM Vol. 3D B.1: 16-bit fields keep
bits 15:0, 32-bit fields 31:0). -/
def vmxWidthMask (f v : Word) : Word :=
  if Vmx.fieldWidth f = 0 then v &&& 0xffff
  else if Vmx.fieldWidth f = 2 then v &&& 0xffff_ffff
  else v

/-- FL4 `vcpu::sanitize_vmcs`: the value WriteVMCS stores in field `f`.
`IllegalOperation` for a field outside `vmxWriteFields`;
`InvalidArgument 1` for an activity state other than active (0) or HLT
(1) (shutdown and wait-for-SIPI are host-only, SDM Vol. 3C §25.4.2). -/
def sanitizeVmcs (f value : Word) : Except SyscallError Word :=
  if ¬ Vmx.writable f then .error .illegalOperation
  else if f = Vmx.guestActivity ∧ value > 1 then .error (.invalidArgument 1)
  else
    let v : Word :=
      if f = Vmx.guestActivity then value
      else if f = Vmx.controlExceptionBitmap then value ||| vcpuExceptions
      else if f = Vmx.controlCr0Mask then value ||| cr0Owned
      else if f = Vmx.controlCr4Mask then value ||| ~~~cr4Allowed
      else if f = Vmx.controlPinExecutionControls then vmxControls 0x481 value pinAllowed pinAllowed
      else if f = Vmx.controlPrimaryProcessorControls then
        vmxControls 0x482 value primaryForced primaryAllowed
      -- VPIDs are disabled: every VM entry flushes guest translations.
      else if f = Vmx.controlSecondaryProcessorControls then
        vmxControls 0x48b value (2 ||| ((vcpuCapability 0x48b >>> 32) &&& 64))
          (secondaryAllowed &&& ~~~((1 : Word) <<< 5))
      else if f = Vmx.controlExitControls then
        vmxControls 0x483 value
          (exitForced ||| ((vcpuCapability 0x483 >>> 32) &&& ((1 <<< 12) ||| (1 <<< 15))))
          (exitForced ||| (1 <<< 12) ||| (1 <<< 15))
      else if f = Vmx.controlEntryControls then
        let perf : Word := if (vcpuCapability 0x483 >>> 32) &&& (1 <<< 12) ≠ 0 then 1 <<< 13 else 0
        vmxControls 0x484 value 0 ((1 <<< 2) ||| (1 <<< 9) ||| (1 <<< 14) ||| (1 <<< 15) ||| perf)
      else if f = Vmx.guestCr0 then
        let fixed0 := vcpuCapability 0x486
        let fixed := if (vcpuCapability 0x48b >>> 32) &&& 128 ≠ 0
          then fixed0 &&& ~~~(((1 : Word) <<< 31) ||| 1) else fixed0
        (value ||| fixed) &&& vcpuCapability 0x487 &&& (fixed ||| ~~~cr0Owned)
      else if f = Vmx.guestCr4 then
        let fixed := vcpuCapability 0x488
        (value ||| fixed) &&& vcpuCapability 0x489 &&& (fixed ||| cr4Allowed)
      else if f = Vmx.guestDebugctrl then value &&& debugctlAllowed
      else value
    .ok (vmxWidthMask f v)

/-- FL4 `vcpu::sanitize_vmcb`: the value WriteVMCB stores at offset `f`,
from the old value `old` and the VMM's `value`: the VMM's bits under the
rule's mask, the old ones elsewhere, the forced ones set, and CR0's owned
bits cleared whatever `old` held. `IllegalOperation` outside the table;
`InvalidArgument 1` for a non-canonical address word or an invalid
G_PAT (`validPat`; FL4 checks the PAT types before the value can reach
VMRUN, APM Vol. 2 §15.25.4). -/
def sanitizeVmcb (f old value : Word) : Except SyscallError Word :=
  match Svm.writeRule f with
  | none => .error .illegalOperation
  | some r =>
    if r.addr ∧ ¬ canonical value canonWidth then .error (.invalidArgument 1)
    else if f = Svm.gPat ∧ ¬ validPat value then .error (.invalidArgument 1)
    else
      let v := (old &&& ~~~r.mask) ||| (value &&& r.mask) ||| r.forced
      .ok (if f = Svm.cr0 then v &&& ~~~cr0Owned else v)

/-- FL4 `vcpu::decode` WriteMSR's checks (both backends): LSTAR, CSTAR
and KERNEL_GS_BASE canonical, XCR0 `validXcr0` against the host's
(`InvalidArgument 1`); STAR, FMASK and CR2 any value. A field outside
`vcpuMsrs` is `IllegalOperation`. -/
def checkMsrWrite (m value : Word) : Except SyscallError Unit :=
  if m ∉ vcpuMsrs then .error .illegalOperation
  else if (m = msrLstar ∨ m = msrCstar ∨ m = msrKernelGsBase) ∧ ¬ canonical value canonWidth then
    .error (.invalidArgument 1)
  else if m = msrXcr0 ∧ ¬ validXcr0 value hostXcr0 then .error (.invalidArgument 1)
  else .ok ()

/-- FL4 `vcpu::enter` on VMX: the primary controls of a VMEnter request,
through `sanitizeVmcs` (which cannot fail for that field; the fallback
`primaryForced` is FL4's `unwrap_or`). -/
def vmxEnterPrimary (ctl : Word) : Word :=
  match sanitizeVmcs Vmx.controlPrimaryProcessorControls ctl with
  | .ok v => v
  | .error _ => primaryForced

/-- FL4 `vcpu::enter` on SVM: the intercept word at 0x008 with the
request's vector-3 bits (`SVM_I1_WRITABLE`) and the forced ones. -/
def svmEnterIntercepts (old ctl : Word) : Word :=
  (old &&& 0xffff_ffff) ||| (((ctl &&& Svm.i1Writable) ||| Svm.i1Forced) <<< 32)

end

end Fl4Spec
