# VIRT-PLAN: the x86 virtualization extension spec

Status (2026-11-22, branch `par/v1`): spec design (this file) and the first
batch of Lean modules `Fl4Spec/Ext/Virt*.lean` (§2). Invocation
definitions (§5 as Lean) and every refinement proof are not written yet
(§11, §14). No refinement proof is in this batch.

Sources: the owner's decision of 2026-11-21 (one extension spec for VT-x
and AMD-V, backend as a parameter, per-backend field tables, the full
sanitize policy in the spec); FL4 `crates/fl4-core/src/{vcpu,ept}.rs`,
the VCPU/EPT parts of `syscall.rs`, `tcb.rs`, `objects.rs`,
`notification.rs`, `sched.rs`, `arch/x86_64/{vspace,objects}.rs`;
`crates/fl4-kernel/src/entry.rs` (`exit`); the trusted layer
`crates/fl4-arch-x86_64/src/vm.rs` (`run`) and `vm/vmx_exit.rs`; libsel4
`sel4/arch/vmenter.h`; `interfaces/object-api-arch-x86.xml`,
`object-api-sel4-arch-x86_64.xml`; seL4 C at c98d70ad
(`src/arch/x86/object/vcpu.c`, `objecttype.c`, `tcb.c`, `c_traps.c`) for
compatibility; l4v master `spec/abstract/ARM_HYP/VCPU_A.thy` and
`Arch_Structs_A.vcpu` for structure; Intel SDM Vol. 3C/3D, AMD APM Vol. 2
for the architectural reasons; upstream `main`'s
`arch/aarch64/{vcpu,ept}.rs` (991586ba) to keep room for an EL2 backend.

## 1. Rules this spec follows

- Extensions only (PORTING.md): nothing in a ported module changes. Where
  an existing shape in `Fl4Spec/X64/Structs.lean` should change, §3.3
  says exactly what and why; it is **not** changed in this batch.
- The spec states FL4's behaviour. Where FL4's policy looks wrong or
  inconsistent with its own comments/docs, §12 records a FINDING and the
  spec still says what FL4 does (marked in the docstring).
- Underspecified hardware (capability MSRs, host XCR0, canonical width,
  the backend) is one opaque structure, l4v `MachineOps` style; guest
  execution is a nondeterministic oracle, l4v `do_user_op` style.
- No `sorry`, no `axiom`, no `native_decide`/`bv_decide`.

## 2. Module map

| Module | Defines |
|---|---|
| `Ext/VirtBackend` | `VirtKind` (`none`, `vmx`, `svm`, `armEl2` reserved), `VirtPlatform` and the opaque `virtPlatform`; `virtKind`, `vcpuCapability`, `hostXcr0`, `canonWidth`, `virtEnabled` |
| `Ext/VirtFields` | `VField` (`vmcs enc`, `vmcb off`, `gpr i`, `msr m`), the VMX tables `Vmx.vmxWriteFields` (73) / `Vmx.vmxReadFields` (84) and the 86 field names (`Vmx.*`), the SVM offsets (`Svm.*`), `Svm.writeRule` (50 rows), `Svm.hidden`, `Svm.hostCache`, the MSR list `vcpuMsrs`; `VField.canon` (one place per value), `VField.valid/readable/writable/guestChanged` |
| `Ext/VirtSanitize` | the masks (`cr4Allowed`, `cr0Owned`, `debugctlAllowed`, `pinAllowed`, `primaryAllowed/Forced`, `secondaryAllowed`, `exitForced`, `vcpuExceptions`), `canonical`, `validXcr0`, `validPat`, `vmxControls`, `vmxWidthMask`, `sanitizeVmcs`, `sanitizeVmcb`, `checkMsrWrite`, `vmxEnterPrimary`, `svmEnterIntercepts` |
| `Ext/VirtState` | `ExitRecord`, `VcpuState` (`tcb`, `fields`, `exit`, `ioDenied`), `get`/`set` through `canon`, `svmResetValue`/`svmReset`, `svmInitFields`, `vmxInitFields`, `initVcpu`, `VirtExt` (`vcpus`, `tcbVcpu`), `VState Z`, `VcpuState.enter`, `entryIp/Ctl/Intr`, `VmenterResult`, `vmenterReport`, `reported`, the VMEnter MR indices |
| `Ext/VirtEpt` | `GuestGeom`, `x86GuestGeom`, `guestMemoryType`, `GuestPte` with `encode` (per backend) and `decode`, `guestIndex`, `guestTableAt`, `guestWalk`, `guestRootOf`, `GuestWritableByte`, `GuestReadableByte` |
| `Ext/VirtGuest` | `GuestOutcome`, `VcpuFrame`, `GuestStep` (the oracle), `VmRunContract` [P], `VmRunFrame` [P], `NoVirtObjects`, `P3xVirt` (statement shape), `GuestStep.not_noVirt`, `GuestStep.frame` |
| `Ext/VirtVcpu` (next batch) | `decodeVcpuInvocation`, `VcpuInvocation`, `performVcpuInvocation` (§5.1) |
| `Ext/VirtEptInv` (next batch) | X86PageMapEPT, EPT table map/unmap, guest-root ASID assign, `TCBSetEPTRoot` (§5.2) |
| `Ext/VirtRetype`, `Ext/VirtFinalise` (next batch) | retype of VCPU/EPT objects, finalisation hooks (§5.4, §5.5) |
| `Ext/VirtEntry` (next batch) | `fl4VmEnter`, `vmCheck`, `vmReport` as monadic operations on `VState`, the notification hook, `fl4CallKernelV` (§5.3) |
| `Ext/VirtP3x` (next batch) | the P3x theorem (§10) |

Dependencies: VirtBackend → VirtFields → VirtSanitize → VirtState →
VirtEpt → VirtGuest; all import `Fl4Spec` (the port) only.

## 3. Abstract state

### 3.1 The state

`VState Z = { base : State Z, virt : VirtExt }`, `VirtExt = { vcpus :
ObjRef → Option VcpuState, tcbVcpu : ObjRef → Option ObjRef }`. The
ported heap still holds `.archObj (.vcpu _)` at a VCPU's address (type,
size, detype, `obj_bits`), and guest tables as `.archObj (.ept level
entries)`; `vcpus` holds the abstract VCPU.

`VcpuState`:

| Component | Meaning | FL4 words |
|---|---|---|
| `tcb : Option ObjRef` | bound thread (l4v ARM_HYP `vcpu_tcb`) | `vcpu::TCB` |
| `fields : VField → Word` | the field table, canonical fields only | VMCS image at `SHADOW` (by `vmcs_addr`), VMCB page 0, `REGS`, `MSRS`, `XCR0`, `CR2` |
| `exit : ExitRecord` | `valid`, `pending`, `mrs : Fin 30 → Word` | `VALID`, `PENDING`, `EXIT` (30 words) |
| `ioDenied : BitVec 16 → Bool` | VT-x I/O bitmap, set = trap | `IO` (1024 words) |

Binding invariant (for the proofs, l4v ARM_HYP `sym_refs` of
`vcpu_tcb`/`tcb_vcpu`): `vcpus v = some vs ∧ vs.tcb = some t ↔
tcbVcpu t = some v`.

### 3.2 Field tables

A field is one of `VField.vmcs enc` (VMX), `VField.vmcb off` (SVM),
`VField.gpr i` (both), `VField.msr m` (both). `VField.canon k` gives each
value one place: on SVM the MSRs STAR/LSTAR/CSTAR/FMASK/KERNEL_GS_BASE and
CR2 are VMCB save-area words (0x600, 0x608, 0x610, 0x618, 0x620, 0x640)
and VMCB RAX (0x5f8) is GPR 0; XCR0 is a VCPU word on both backends.
Classes: **R** readable through an invocation, **W** writable (through
the sanitize rule), **G** guest-changed (a guest step may change it).

#### VMX: 86 VMCS fields (73 W, 84 R, 74 G)

By encoding type: 14 control, 13 VM-exit information, 59 guest state
(host-state fields are written only by the trusted layer and are not in
the spec). Sanitize rules: §4.1; a W field not named there gets the width mask only.

| Field | Encoding | Class |
|---|---|---|
| `GUEST_ES_SELECTOR` | 0x00000800 | RWG |
| `GUEST_CS_SELECTOR` | 0x00000802 | RWG |
| `GUEST_SS_SELECTOR` | 0x00000804 | RWG |
| `GUEST_DS_SELECTOR` | 0x00000806 | RWG |
| `GUEST_FS_SELECTOR` | 0x00000808 | RWG |
| `GUEST_GS_SELECTOR` | 0x0000080a | RWG |
| `GUEST_LDTR_SELECTOR` | 0x0000080c | RWG |
| `GUEST_TR_SELECTOR` | 0x0000080e | RWG |
| `CONTROL_TSC_OFFSET` | 0x00002010 | RW- |
| `DATA_GUEST_PHYSICAL` | 0x00002400 | R-G |
| `GUEST_DEBUGCTRL` | 0x00002802 | RWG |
| `GUEST_PAT` | 0x00002804 | RWG |
| `GUEST_EFER` | 0x00002806 | RWG |
| `GUEST_PERF_GLOBAL_CTRL` | 0x00002808 | RWG |
| `GUEST_PDPTE0` | 0x0000280a | RWG |
| `GUEST_PDPTE1` | 0x0000280c | RWG |
| `GUEST_PDPTE2` | 0x0000280e | RWG |
| `GUEST_PDPTE3` | 0x00002810 | RWG |
| `CONTROL_PIN_EXECUTION_CONTROLS` | 0x00004000 | RW- |
| `CONTROL_PRIMARY_PROCESSOR_CONTROLS` | 0x00004002 | RW- |
| `CONTROL_EXCEPTION_BITMAP` | 0x00004004 | RW- |
| `CONTROL_EXIT_CONTROLS` | 0x0000400c | RW- |
| `CONTROL_ENTRY_CONTROLS` | 0x00004012 | RW- |
| `CONTROL_ENTRY_INTERRUPTION_INFO` | 0x00004016 | RWG |
| `CONTROL_ENTRY_EXCEPTION_ERROR_CODE` | 0x00004018 | -WG |
| `CONTROL_ENTRY_INSTRUCTION_LENGTH` | 0x0000401a | -W- |
| `CONTROL_SECONDARY_PROCESSOR_CONTROLS` | 0x0000401e | RW- |
| `DATA_INSTRUCTION_ERROR` | 0x00004400 | R-G |
| `DATA_EXIT_INTERRUPT_INFO` | 0x00004404 | R-G |
| `DATA_EXIT_INTERRUPT_ERROR` | 0x00004406 | R-G |
| `DATA_IDT_VECTOR_INFO` | 0x00004408 | R-G |
| `DATA_IDT_VECTOR_ERROR` | 0x0000440a | R-G |
| `DATA_EXIT_INSTRUCTION_LENGTH` | 0x0000440c | R-G |
| `DATA_EXIT_INSTRUCTION_INFO` | 0x0000440e | R-G |
| `GUEST_ES_LIMIT` | 0x00004800 | RWG |
| `GUEST_CS_LIMIT` | 0x00004802 | RWG |
| `GUEST_SS_LIMIT` | 0x00004804 | RWG |
| `GUEST_DS_LIMIT` | 0x00004806 | RWG |
| `GUEST_FS_LIMIT` | 0x00004808 | RWG |
| `GUEST_GS_LIMIT` | 0x0000480a | RWG |
| `GUEST_LDTR_LIMIT` | 0x0000480c | RWG |
| `GUEST_TR_LIMIT` | 0x0000480e | RWG |
| `GUEST_GDTR_LIMIT` | 0x00004810 | RWG |
| `GUEST_IDTR_LIMIT` | 0x00004812 | RWG |
| `GUEST_ES_ACCESS_RIGHTS` | 0x00004814 | RWG |
| `GUEST_CS_ACCESS_RIGHTS` | 0x00004816 | RWG |
| `GUEST_SS_ACCESS_RIGHTS` | 0x00004818 | RWG |
| `GUEST_DS_ACCESS_RIGHTS` | 0x0000481a | RWG |
| `GUEST_FS_ACCESS_RIGHTS` | 0x0000481c | RWG |
| `GUEST_GS_ACCESS_RIGHTS` | 0x0000481e | RWG |
| `GUEST_LDTR_ACCESS_RIGHTS` | 0x00004820 | RWG |
| `GUEST_TR_ACCESS_RIGHTS` | 0x00004822 | RWG |
| `GUEST_INTERRUPTABILITY` | 0x00004824 | RWG |
| `GUEST_ACTIVITY` | 0x00004826 | RWG |
| `GUEST_SMBASE` | 0x00004828 | RWG |
| `GUEST_SYSENTER_CS` | 0x0000482a | RWG |
| `GUEST_PREEMPTION_TIMER_VALUE` | 0x0000482e | RWG |
| `CONTROL_CR0_MASK` | 0x00006000 | RW- |
| `CONTROL_CR4_MASK` | 0x00006002 | RW- |
| `CONTROL_CR0_READ_SHADOW` | 0x00006004 | RW- |
| `CONTROL_CR4_READ_SHADOW` | 0x00006006 | RW- |
| `DATA_IO_RCX` | 0x00006402 | R-G |
| `DATA_IO_RSI` | 0x00006404 | R-G |
| `DATA_IO_RDI` | 0x00006406 | R-G |
| `DATA_IO_RIP` | 0x00006408 | R-G |
| `DATA_GUEST_LINEAR_ADDRESS` | 0x0000640a | R-G |
| `GUEST_CR0` | 0x00006800 | RWG |
| `GUEST_CR3` | 0x00006802 | RWG |
| `GUEST_CR4` | 0x00006804 | RWG |
| `GUEST_ES_BASE` | 0x00006806 | RWG |
| `GUEST_CS_BASE` | 0x00006808 | RWG |
| `GUEST_SS_BASE` | 0x0000680a | RWG |
| `GUEST_DS_BASE` | 0x0000680c | RWG |
| `GUEST_FS_BASE` | 0x0000680e | RWG |
| `GUEST_GS_BASE` | 0x00006810 | RWG |
| `GUEST_LDTR_BASE` | 0x00006812 | RWG |
| `GUEST_TR_BASE` | 0x00006814 | RWG |
| `GUEST_GDTR_BASE` | 0x00006816 | RWG |
| `GUEST_IDTR_BASE` | 0x00006818 | RWG |
| `GUEST_DR7` | 0x0000681a | RWG |
| `GUEST_RSP` | 0x0000681c | RWG |
| `GUEST_RIP` | 0x0000681e | RWG |
| `GUEST_RFLAGS` | 0x00006820 | RWG |
| `GUEST_PENDING_DEBUG_EXCEPTIONS` | 0x00006822 | RWG |
| `GUEST_SYSENTER_ESP` | 0x00006824 | RWG |
| `GUEST_SYSENTER_EIP` | 0x00006826 | RWG |

R-only (13, all VM-exit information): `DATA_INSTRUCTION_ERROR`,
`DATA_EXIT_INTERRUPT_INFO/ERROR`, `DATA_IDT_VECTOR_INFO/ERROR`,
`DATA_EXIT_INSTRUCTION_LENGTH/INFO`, `DATA_GUEST_PHYSICAL`, `DATA_IO_RCX/RSI/RDI/RIP`,
`DATA_GUEST_LINEAR_ADDRESS`. W-only (2): `CONTROL_ENTRY_EXCEPTION_ERROR_CODE`,
`CONTROL_ENTRY_INSTRUCTION_LENGTH`. Two R fields read 0 when the CPU's VMCS
lacks them (`Vmx.readSupported`: `GUEST_PERF_GLOBAL_CTRL`,
`GUEST_PREEMPTION_TIMER_VALUE`). The exit reason and qualification are not
fields: they reach the VMM only as MR3/MR4 of the exit record.
G = the R fields of type exit-information or guest-state (72) plus the two
event-injection controls (`CONTROL_ENTRY_INTERRUPTION_INFO`, valid bit
cleared on exit or an interrupted event reinjected; `..._EXCEPTION_ERROR_CODE`,
reinjection). Control fields read back by `vm::run` are **not** G: the
[P] contract (§8) says they are unchanged.

#### SVM: 221 VMCB words (50 W, 221 R of which 9 hidden + 2 host-cache, 103 G)

R: every 8-aligned offset below `svm::END` = 0x6e8 (`Svm.readable`);
hidden ones (`vmcb_hidden`: 0x040 IOPM_BASE, 0x048 MSRPM_BASE, 0x098 AVIC
BAR, 0x0a0 GHCB, 0x0b0 N_CR3, 0x0e0/0x0f0/0x0f8 AVIC tables, 0x108 VMSA) read
0; the host-cache words 0x058 (ASID, with FL4's flush request in bits 39:32)
and 0x0c0 (clean bits) read an unspecified value in the spec (FINDING V3).
W (`Svm.writeRule`, FL4 `sanitize_vmcb`; stored = `(old & ~mask) | (value
& mask) | forced`, CR0 then `& ~cr0Owned`):

| Offset | Field | mask | forced | check |
|---|---|---|---|---|
| 0x000 | CR/DR intercepts | 0xffffffff (CR r/w) | DR r/w all, CR4 write (bit 20) | |
| 0x008 | exception + vector 3 | 0xffffffff, vector 3 `i1Writable` | #DB #AC #MC, vector 3 `i1Forced` | |
| 0x010 | vector 4 (+ 5) | 0x182 (VMMCALL, RDTSCP, ICEBP) | `i2Forced` | vector 5 stays 0 |
| 0x038 | PAUSE filter | bits 63:32 | | |
| 0x050 | TSC offset | all | | |
| 0x060 | VINTR | 0xff_001f_01ff (V_TPR, V_IRQ, prio, IGN_TPR, vector) | V_INTR_MASKING | |
| 0x068 | interrupt shadow | bit 0 | | |
| 0x0a8 | EVENTINJ | `eventMask` | | |
| 0x0c8 | NRIP | all | | |
| 0x4c8 | CPL | byte 0x4cb | | |
| 0x4d0 | EFER | all | SVME | |
| 0x548 | CR4 | `cr4Allowed` | | |
| 0x400..0x490 step 16 | segment sel/attr/limit (10) | all | | |
| 0x408..0x498 step 16 | segment bases (10) | all | | canonical |
| 0x550 0x558 0x560 0x568 0x570 0x578 0x5d8 0x5f8 | CR3 CR0 DR7 DR6 RFLAGS RIP RSP RAX(=GPR 0) | all | | CR0 `& ~cr0Owned` |
| 0x600 0x618 0x628 0x640 0x668 | STAR SFMASK SYSENTER_CS CR2 G_PAT | all | | G_PAT `validPat` |
| 0x608 0x610 0x620 0x630 0x638 | LSTAR CSTAR KERNEL_GS_BASE SYSENTER_ESP/EIP | all | | canonical |

G (`Svm.guestChanged`): the save area 0x400..0x6e0 (93 words: the
processor writes it on #VMEXIT, and FL4's shutdown handling resets it) and
the control words 0x060, 0x068, 0x070, 0x078, 0x080, 0x088, 0x0a8, 0x0c8,
0x0d0, 0x0d8 (VINTR, shadow, EXITCODE, EXITINFO1/2, EXITINTINFO, EVENTINJ,
NRIP, instruction bytes). Everything else in the control area is unchanged
by a guest step in the spec; the trusted layer's rewrites of 0x040, 0x048,
0x058, 0x0b0, 0x0c0 are cache/hidden words (§3.4, §8).

#### Both backends

| Field | Class | Notes |
|---|---|---|
| `gpr 0..14` (RAX RBX RCX RDX RSI RDI RBP R8..R15) | W (WriteRegisters, all 15 at once), G, reported as MR10..24 | no read invocation (VMEnter reports them) |
| `msr STAR/LSTAR/CSTAR/FMASK/KERNEL_GS_BASE` | R W, G on VMX (exit MSR-store list); on SVM = VMCB words | LSTAR/CSTAR/KGS canonical |
| `msr CR2` (0xffffffff) | R W G | SVM: VMCB 0x640 |
| `msr XCR0` (0xfffffffe) | R W, **not G** (XSETBV always exits / is intercepted) | `validXcr0` against the host's; init = host XCR0 |
| `IA32_VMX_MISC` (0x485) | R only, not state | VMX: `vcpu_capability(0x485)`, SVM: 0 |

Counts: VMX 86 + 15 + 7 = 108 fields; SVM 221 + 15 + 1 (XCR0; the other six
MSRs are VMCB words) = 237.

### 3.3 Shape changes in `X64/Structs.lean` (listed, not made)

1. `ArchCap.ioPortCap first last` has no owner. FL4's `Cap::IoPort`
   carries `vcpu` (the VCPU its range was granted to, seL4
   `capIOPortVPID`): EnableIOPort writes it, every finalisation of the cap
   (final or not, seL4 `clearVPIDIOPortMappings`) revokes the grant on
   it, and derive keeps it (seL4 `Arch_deriveCap` returns the cap). The
   owner moves with the cap through the ported CNode operations, so it
   cannot live in `VirtExt`. **Change:** `ioPortCap (first last : IoPort)
   (vcpu : Option ObjRef)`. Ported users: `arch_finalise_cap`
   (`.ioPortCap f l, true`), `arch_same_region_as`/`same_object_as`
   (ignore the owner), decode of IOPortControl Issue (`none`). Blocks:
   EnableIOPort's spec and the IO-port finalisation hook.
2. `ArchKernelObj.vcpu (words : Word → Word)` is the raw image. The
   decision makes the abstract VCPU a field table. This batch keeps the
   ported constructor as a type marker and holds `VcpuState` in
   `VirtExt.vcpus` (no change needed). **Optional change**, cleaner and
   what l4v ARM_HYP does (`VCPU vcpu` in `arch_kernel_obj`): `vcpu (st :
   VcpuState)` with `VcpuState` moved below `Structs` (it needs only
   `Word`, `ObjRef`, `VField`). It would remove the `vcpus`/kheap
   agreement invariant from the proofs. Recommended, owner to decide (Q1).
3. `ArchKernelObj.ept level (entries : BitVec 9 → Word)`: raw words. They
   are kept: `GuestPte.decode` is the hardware reading and FL4's tables
   hold exactly these words except FL4's per-core lifetime bitmap in the
   high halves of root entries 510/511 (above the 2^47 limit, never
   present; a refinement detail). No change needed.
4. `ArchCap.eptCap ref level (mapped : Option (Asid × VSpaceRef))`: fits
   (root: `(asid, 0)`; table: `(asid, gpa)`). No change.
5. `tcbEpt` (sixth TCB slot): fits. No change.
6. The TCB → VCPU link: l4v ARM_HYP has `tcb_vcpu` in `arch_tcb`; the
   ported X64 `ArchTcb` has none. Kept in `VirtExt.tcbVcpu` (no change).

### 3.4 Not in the spec (refinement relation only)

VMCS caches and the per-core retained VMCS, `VMRESUME`/launched state;
VMCB clean bits (0x0c0) and ASID word (0x058) and `SVM_CPU` (SVM ASID
retention); the VCPU list `NEXT`/`PREV` and `ks::VCPU_HEAD` (the relation:
list = `dom vcpus`); the physical pointers the trusted layer writes (VMCB
0x040, 0x048, 0x0b0; VMX I/O and MSR bitmap addresses, EPTP, MSR lists,
host state); the EPT root's core bitmap; `vcpu_barrier`, stalls and IPIs;
guest-linear translations and TLBs (FlushTLB has no abstract effect);
the shared SVM IOPM/MSRPM and the VMX MSR bitmap (fixed by the trusted
layer; their passthrough set is part of the [P] contract's trust).

## 4. Sanitize policy (`Ext/VirtSanitize`)

### 4.1 VMX (`sanitizeVmcs f value`)

`IllegalOperation` unless `f ∈ vmxWriteFields`. Then, per field (then the
width mask of the encoding, SDM Vol. 3D B.1):

| Field | Stored value | Reason |
|---|---|---|
| `GUEST_ACTIVITY` | value if ≤ 1, else `InvalidArgument 1` | shutdown / wait-for-SIPI are host states (SDM 3C §25.4.2) |
| `CONTROL_EXCEPTION_BITMAP` | `value ∣ #DB ∣ #AC ∣ #MC` | CVE-2015-5307/8104 loops; #MC is the host's |
| `CONTROL_CR0_MASK` | `value ∣ cr0Owned` | CD/NW/reserved owned by the host |
| `CONTROL_CR4_MASK` | `value ∣ ~cr4Allowed` | VMXE, LA57, SMXE, PKE, CET, reserved owned |
| `CONTROL_PIN_EXECUTION_CONTROLS` | `vmxControls 0x481 v pinAllowed pinAllowed` (= fixed: ext-int, NMI exiting, virtual NMIs) | host interrupts and NMIs exit |
| `CONTROL_PRIMARY_PROCESSOR_CONTROLS` | `vmxControls 0x482 v primaryForced primaryAllowed` | MSR/IO bitmaps, MOV-DR, CR8, MWAIT/MONITOR, RDPMC exits |
| `CONTROL_SECONDARY_PROCESSOR_CONTROLS` | `vmxControls 0x48b v (EPT ∣ WBINVD-exit if supported) (secondaryAllowed ∖ VPID)` | EPT on, no VPID (entries flush), no APIC virtualization, no XSAVES |
| `CONTROL_EXIT_CONTROLS` | fixed: `exitForced` ∣ load PERF_GLOBAL_CTRL / ack-interrupt where supported | host PAT/EFER/debug state restored |
| `CONTROL_ENTRY_CONTROLS` | `vmxControls 0x484 v 0 (load debug ∣ IA-32e ∣ load PAT ∣ load EFER ∣ load PERF_GLOBAL_CTRL if the exit side has it)` | no SMM, no dual-monitor, no CET/PKRS/RTIT/LBR loads |
| `GUEST_CR0` | `(v ∣ fixed0') & fixed1 & (fixed0' ∣ ~cr0Owned)`, fixed0' without PE/PG when unrestricted guest is supported | SDM 3D A.7 |
| `GUEST_CR4` | `(v ∣ fixed0) & fixed1 & (fixed0 ∣ cr4Allowed)` | SDM 3D A.8 |
| `GUEST_DEBUGCTRL` | `v & BTF` | XSA-269 (FL4 comment) |
| every other W field | width mask only; guest-only invalid state is left to VM-entry checks (SDM 3C §27.3) | |

`vmxControls msr v forced allowed = (v ∣ ones) & cap.hi & (ones ∣ allowed)`
with `ones = cap.lo ∣ forced` (SDM 3D A.3). The boot check
(`vm::init_vmx`) requires `PIN_ALLOWED`, `PRIMARY_FORCED`, `EXIT_FORCED`
in the allowed-1 halves; in the spec this is a fact the proofs will need on
`virtPlatform` (to add with the first proof that uses it: `forced ⊆
cap.hi` for 0x481/0x482/0x483 and EPT in 0x48b), as l4v's machine
lemmas do.

VMEnter's MR1 goes through `sanitizeVmcs` of the primary controls
(`vmxEnterPrimary`), MR2 is truncated to 32 bits.

### 4.2 SVM (`sanitizeVmcb f old value`)

The table of §3.2; `InvalidArgument 1` for a non-canonical address word
(`canonical v canonWidth`: 48- or 57-bit) or an invalid G_PAT;
`IllegalOperation` outside the table. VMEnter's MR1 replaces vector 3
(`svmEnterIntercepts`: `(ctl & i1Writable) ∣ i1Forced`), MR2 is masked by
`eventMask`. A WriteVMCB to CR0/CR3/CR4/EFER/G_PAT also requests an ASID
flush (cache state, not in the spec).

### 4.3 MSRs (`checkMsrWrite`)

Both backends; `IllegalOperation` outside `vcpuMsrs`; LSTAR, CSTAR,
KERNEL_GS_BASE canonical; XCR0 `validXcr0 v hostXcr0` (subset of the
host's, x87, AVX ⇒ SSE, AVX-512 all-or-none with SSE+AVX, MPX pair, AMX
pair; SDM Vol. 1 §13.3); `InvalidArgument 1` on failure.

### 4.4 The other backend

ReadVMCS/WriteVMCS on SVM, ReadVMCB/WriteVMCB on VMX, Enable/DisableIOPort
on SVM: `IllegalOperation` (checked before the length checks, as FL4
does). With `virtKind = none` no VCPU/EPT object exists (retype refuses
the types), so no invocation reaches them.

## 5. Invocations (spec for the next batch, from FL4's code)

Notation: `f` = MR0 if `length > 0` else 0, `x` = MR1 if `length > 1` else
0 (`syscall_arg`, FL4 reads them whatever the label); "reply v" = if the
caller used Call: MR0 := v, badge register 0, msginfo (0,0,0,1); then the
caller is `Running` (no restart). "restart" = caller `Restart` (FL4's
`TS_RESTART` after a successful invocation without reply). Errors leave
the state unchanged (every check below precedes the first write). Every
VCPU invocation first stalls the VCPU's thread on another core (no
abstract effect: the thread's guest state is already saved, §8).

### 5.1 VCPU (cap `vcpuCap v`; l4v ARM_HYP `decode_vcpu_invocation` for structure)

| Label | Checks, in FL4's order | Effect |
|---|---|---|
| `X86VCPUSetTCB` | extra cap 0 absent: `TruncatedMessage`; not a thread cap: `IllegalOperation` | `detach target` (its old VCPU; a `runningVM` target first gets `vmReport target 0`), `detach (v.tcb)`, bind `v ↔ target`; restart. l4v `associate_vcpu_tcb` |
| `X86VCPUWriteRegisters` | `length < 15`: `TruncatedMessage` | `gpr i := MR i` (0..14); restart |
| `X86VCPUFlushTLB` | — | no abstract effect (SVM ASID hint); restart |
| `X86VCPUReadVMCS` | SVM: `IllegalOperation`; `length < 1`: `IllegalOperation` (seL4's choice); `f ∉ vmxReadFields`: `IllegalOperation` | reply (`readSupported f` ? field : 0) |
| `X86VCPUWriteVMCS` | SVM: `IllegalOperation`; `length < 2`: `IllegalOperation`; `sanitizeVmcs f x` errors | field := sanitized; reply sanitized |
| `X86VCPUReadVMCB` | VMX: `IllegalOperation`; `length < 2`: `TruncatedMessage`; `f` not 8-aligned, `f ≥ 0x6e8`, `x = 0`, `x > 64`, `x > (0x6e8 - f)/8`: `InvalidArgument 0` | if Call: MR i := word `f + 8i` (hidden: 0; host-cache: unspecified; RAX: GPR 0), msginfo length = last `set_mr` count; caller `Running` |
| `X86VCPUWriteVMCB` | VMX: `IllegalOperation`; `length < 2`: `TruncatedMessage`; `sanitizeVmcb f old x` errors (`old` = the field, 0 if `f` not 8-aligned or ≥ END) | field := sanitized (RAX: GPR 0); reply sanitized |
| `X86VCPUReadMSR` | `length < 1`: `IllegalOperation`; `f = 0x485`: reply (VMX: `vcpu_capability 0x485`, SVM: 0); `f ∉ vcpuMsrs`: `IllegalOperation` | reply the field |
| `X86VCPUWriteMSR` | `length < 2`: `IllegalOperation`; `checkMsrWrite f x` | field := x; reply x |
| `X86VCPUEnableIOPort` | SVM: `IllegalOperation`; `length < 2`: `TruncatedMessage`; `lo = f & 0xffff > hi = x & 0xffff`: `InvalidArgument 0`; extra cap absent: `TruncatedMessage`; not an IO port cap: `IllegalOperation`; `[lo, hi] ⊄ [first, last]`: `InvalidArgument 0` | if the cap's owner is a live VCPU: deny `[first, last]` there; cap owner := v (needs §3.3.1); allow `[lo, hi]` on v; restart |
| `X86VCPUDisableIOPort` | SVM: `IllegalOperation`; `length < 2`: `TruncatedMessage`; `lo > hi`: `InvalidArgument 0` | deny `[lo, hi]` on v (no cap needed, as seL4); restart |
| other | `IllegalOperation` | |

`detach t` (FL4 `vcpu::detach`): if `tcbVcpu t = some w`: if `t` is
`runningVM`, `vmReport t 0`; `w.tcb := none`, `tcbVcpu t := none`.

### 5.2 Guest page tables, guest roots, SetEPTRoot

| Invocation | Checks, in FL4's order | Effect |
|---|---|---|
| `X86PageMapEPT` (frame cap) | `length < 3` or no extra cap: `TruncatedMessage`; `gpa = MR0 & ~0xfff ≥ 2^47`: `InvalidArgument 0`; frame cap mapped: `InvalidCapability 0`; extra cap not a mapped level-0 EPT cap: `InvalidCapability 1`; its ASID: `FailedLookup false lf` (`find_vspace` for a guest entry), entry names another root: `InvalidCapability 1`; `gpa` not aligned to the frame: `AlignmentError`; huge frame: `InvalidCapability 0`; walk to the level (missing or large entry above): `FailedLookup false (MissingCapability shift)`; entry present: `DeleteFirst` | restart; entry := `GuestPte.frame (addrFromPPtr ptr) (2M) (rights has write) (guestMemoryType MR2)` encoded for the backend, rights = `mask_vm_rights capRights (data_to_rights MR1)`; kernel-only rights: entry stays 0 and the cap stays unmapped; else cap := mapped `vmEptMap` at `(asid, gpa)` |
| `X86PageMap` on an EPT-mapped frame | `InvalidCapability 0` | |
| `X86PageUnmap` of an EPT-mapped frame | — | restart; `guestUnmap asid gpa frame` (§6); cap unmapped |
| `X86EPTPDPTMap` / `PDMap` / `PTMap` (levels 39/30/21) | `length < 2` or no extra cap: `TruncatedMessage`; cap mapped: `InvalidCapability 0`; `gpa = MR0 & ~(2^level-1) ≥ 2^47`: `InvalidArgument 0`; root as above; walk: `FailedLookup`; entry present: `DeleteFirst` | restart; entry := `GuestPte.table`; cap mapped `(asid, gpa)` |
| `X86EPT*Unmap` | not the final cap: `RevokeFirst` | restart; if mapped: `guestUnmap` of the table's entry, then the table zeroed (seL4 clears unmapped page tables); cap unmapped |
| any label on a level-0 EPT cap, other labels on tables | `IllegalOperation` | |
| `X86ASIDPoolAssign` with an unmapped level-0 EPT cap | the ported checks (pool, free slot) | pool entry := `root ∣ 1`; cap := `eptCap root 0 (some (asid, 0))`; restart |
| `TCBSetEPTRoot` | (target stalled) no extra cap: `TruncatedMessage`; not a mapped level-0 EPT cap: `IllegalOperation`; `cte_delete` of the target's slot 5 (its errors/preemption) | `cap_insert (derived) src (target, slot 5)`; restart (seL4 `decodeSetEPTRoot`: same errors) |

### 5.3 VMEnter, check, report; notifications and the scheduler

- **`SysVMEnter`** (FL4 `handle_unknown_syscall`): if `virtKind = none` or
  the caller has no VCPU, l4v's unknown-syscall fault (as seL4's
  `c_traps.c`, which falls through). Otherwise, after FL4's MCS budget
  check (`budget_ok`: `update_timestamp`, `check_budget`; if the budget is
  exhausted nothing else happens), **enter**: MR0..2 (in registers, even
  without an IPC buffer) staged by `VcpuState.enter` (sanitized), the exit
  record emptied, state := `runningVM`, then **check**.
- **`vmCheck t`** (FL4 `vcpu::check`, run before every hardware re-entry
  under the serial gate and after every VM exit): nothing unless `t` is
  `runningVM`. A pending exit: `vmReport t 0`. Else, the bound
  notification active: it becomes idle and `vmReport t badge` (l4v
  `complete_signal`). Else, no VCPU: `vmReport t 0`. Else the thread
  stays `runningVM` (the guest runs: §7).
- **`vmReport t badge`**: `vmenterReport` (`Ext/VirtState`): the 30 MRs
  (`set_mr`: registers, then the IPC buffer if any), msginfo 1 for a VMM
  exit / 0 for a notification, badge register; `pending := false`; state
  := `Running`.
- **Notifications** (FL4 `send_signal`, idle notification bound to a
  `runningVM` thread): the notification becomes active (badge OR-ed) and
  the thread's core is stalled; the next `vmCheck` delivers it. (seL4
  completes the VMEnter at once on the same core: FINDING V1.)
- **Scheduler**: `runningVM` is `runnable` (the ported `runnable` already
  says so); `end_timeslice` never raises a timeout fault for a
  `runningVM` thread (FL4 `sched.rs:483`: `valid` requires the state not
  `TS_RUNNING_VM`; seL4's `endTimeslice` has no such exception: FINDING V8) — an Ext hook on the ported
  `end_timeslice`/`handle_timeout` path; `set_priority`, `possible_switch_to`
  treat it as runnable. A remote stall moves a `runningVM` thread back to
  the ready queue with its state unchanged (the guest is re-entered when
  it is scheduled again): `smp::stall` only turns `Running` into
  `Restart`. A guest runs only as the current thread (§7).
- **Exit** (FL4 `handle_vcpu_exit`, after the trusted layer's `vm::run`,
  §8): unless the thread was stalled, `update_timestamp`, `vmCheck ct`,
  `check_budget`; then the accepted host IRQ (`handle_interrupt`), then
  the ported scheduler (`fl4CallKernel`'s tail).

### 5.4 Retype

`UntypedRetype` of `X86_VCPUObject` (15 bits) or the four EPT types (12
bits): `InvalidArgument 0` if `virtKind = none` (FL4 `untyped.rs:42`,
before the other checks). Otherwise the ported `retype_region` creates
`.archObj (.vcpu 0)` / `.archObj (.ept level 0)` (already in `Structs`),
and the extension adds `vcpus v := initVcpu virtKind` (FL4 `vcpu::init`,
which also links the VCPU list) for each VCPU.

### 5.5 Finalisation

- final `vcpuCap v` (FL4 `vcpu::finalise`): `detach (v.tcb)` (with
  `vmReport` of a `runningVM` thread), `vcpus v := none`.
- final `threadCap t`: `detach t` before the ported thread finalisation
  (FL4 `objects.rs:336`).
- `eptCap` mapped level 0: the ported `deleteAsid` (clears the guest
  entry; FL4 invalidates the root on every recorded core first);
  mapped table: `guestUnmap` of its entry in the parent (the ported
  `arch_finalise_cap` does nothing here: Ext hook).
- EPT-mapped frame: `guestUnmap` (the ported `unmapPage` finds no native
  root for the guest-tagged ASID and does nothing: Ext hook).
- `ioPortCap` (final or not): if its owner is a live VCPU, deny its
  `[first, last]` there (needs §3.3.1), then the ported behaviour.
- ASID pool deletion with guest entries: the ported behaviour (the
  invalidations have no abstract effect).

## 6. Guest page tables (`Ext/VirtEpt`)

Four levels (shifts 39, 30, 21, 12), 512 entries, GPAs below 2^47.
`GuestPte`: `invalid`, `table paddr`, `frame paddr large write memType`.
`encode`: EPT `paddr ∣ R ∣ W? ∣ X ∣ PS? ∣ memType<<3`, tables `paddr ∣ 7`;
NPT `paddr ∣ P ∣ W? ∣ U ∣ PS? ∣ PAT bits` (PWT bit 3, PCD bit 4, PAT bit 7 /
12 for 2 MiB), tables `paddr ∣ 7`. `decode`: bit 0 present/readable, bit 1
write, bit 7 large, bits 51:12 address. `guestWalk` follows tables in the
heap; `guestRootOf t` is the root of `t`'s `tcbEpt` cap when its ASID's
pool entry is the guest-tagged root, else none (FL4's empty root).
`guestUnmap asid gpa ptr level` (next batch): find the root by the guest
entry (none: nothing), walk to the level (missing: nothing), clear the
entry iff it is present, of the right kind (large or table) and names
`ptr` (FL4 `ept::unmap`'s check), and the invalidation (no abstract
effect, but the [P] premise of §8 relies on it being synchronous).
Rights: read and execute always, write as the frame's rights; no
kernel-only guest page (the entry stays empty).

## 7. The guest oracle (`Ext/VirtGuest.GuestStep`)

`GuestStep k t σ σ' o`: `t` is a `runningVM` TCB with VCPU `v`; `σ'`
differs from `σ` only in `v`'s guest-changed fields, `v`'s exit record
(any value; `pending = false` when a host IRQ was taken) and bytes of
frames `GuestWritableByte σ (guestRootOf σ t)`. Proved:
`GuestStep.frame` (heap, bindings and other VCPUs unchanged),
`GuestStep.not_noVirt`. The step reads the guest tables of the state it
starts in (no TLB): an unmap that has returned is final for every later
step, on every core.

In the kernel step relation (next batch): when the current thread is
`runningVM` after `vmCheck` at kernel exit, the machine performs a
`GuestStep` and the kernel is re-entered with `handle_vcpu_exit` (§5.3).
One step suffices: FL4's VMX/SVM exit always enters the kernel.

## 8. The trusted layer's contract [P]

`VmRunContract R run` (abstract): from `R s σ`, `run t s s' o` (one
`vm::run` and the hardware between entry and exit) gives `σ'` with
`GuestStep virtKind t σ σ' o ∧ R s' σ'`. `VmRunFrame k fieldWords
exitWords cacheWords writable mem mem'` (word level): only words of
guest-changed fields, the exit area (`EXIT`, `VALID`, `PENDING`, `CR2`,
`REGS`, `MSRS`), cache words (`SVM_CPU`, VMCB 0x040/0x048/0x058/0x0b0/0x0c0;
VMX: none, the hardware VMCS is per core) and writable guest frames change.
What the layer must ensure for it to hold (to be checked against
`vm.rs`/`vm.S`, not proved): guest GPRs saved/restored, host CR2/XCR0/
GDTR/IDTR/DR6/DR7 restored on success and failure, exit metadata
zeroed when undefined (`vmx_exit.rs`), VMCS control fields unchanged
(read back equal), the shared MSR/IO bitmaps intercepting everything but
the passthrough set, IBPB/VERW barriers (outside the functional model),
the EPT root marked on the core under the serial gate before entry, and
`invalidate_ept` synchronous on all marked cores. Used later by the
exit-path refinement (§11 R6) as a [P] premise; no l4v counterpart beyond
`do_user_op`'s `user_memory_update` frame.

## 9. Room for AArch64 EL2

`VirtKind.armEl2` exists; no definition specifies it. What carries over:
the field-table idea (`VField` gets an `el2 reg` case for the VCPU
registers of upstream `arch/aarch64/vcpu.rs`, with its readable/writable
classes and `sanitize_hcr`/`sanitize_vgic_*`), `GuestGeom` (Stage-2 has
3- or 4-level walks with concatenated roots: `shifts`, `gpaLimit` from
`s2_ipa_bits`), the oracle and the [P] contract. What does not: the
VMEnter exit record (AArch64 reports guest exits as VCPU faults, l4v
ARM_HYP style), I/O bitmaps, VMCS/VMCB fields.

## 10. P3x for virtualization

Statement (`Ext/VirtGuest.P3xVirt` shape): for every state with
`NoVirtObjects` (no VCPU, no binding, no `.vcpu`/`.ept` object; then no
VCPU/EPT cap, no EPT-mapped frame and no guest pool entry exist either,
by the cap/object invariants), every kernel step of the extended spec
(`fl4CallKernelV`) is a step of the ported FL4 spec (`fl4CallKernel`)
with `virt` unchanged, and conversely. Plus preservation: the ported
steps keep `NoVirtObjects` except a retype of the five VT-x types, which
is exactly where the extension starts. With `virtKind = none` the
retype is refused, so every reachable state satisfies `NoVirtObjects`
and FL4 is seL4 there (DESIGN.md §2 superset rule). Proof: each Ext hook
is the identity when its object kind is absent (`detach` of a thread
without VCPU, `vmCheck` of a thread not `runningVM` (unreachable without
VMEnter, which faults without a VCPU), the IO-port revoke with no live
owner, the frame unmap of a non-EPT frame).

## 11. Proof plan

### 11.1 Relations (one per backend)

- `VcpuRelVmx mem v vs`: `vs.fields (.vmcs f) = mem (v + SHADOW + 8·idx f)`
  (`vmcs_addr`) for the 86 fields; `gpr i ↔ REGS + 8i`; `msr` STAR..KGS ↔
  `MSRS + 8i`; CR2 ↔ `CR2`; XCR0 ↔ `XCR0`; `exit.mrs i ↔ EXIT + 8i`,
  `valid ↔ VALID ≠ 0`, `pending ↔ PENDING ≠ 0`; `ioDenied p ↔` bit `p` of
  `IO`; `tcb ↔ TCB`.
- `VcpuRelSvm`: VMCB words at their offsets for every canonical
  `.vmcb` field but hidden and host-cache ones; `gpr 0 ↔ REGS` **and**
  the agreement `mem (v + 0x5f8) = mem (v + REGS)` at kernel exit (FL4
  writes both; the trusted layer reads `REGS`); XCR0; exit record; `tcb`.
- `VirtRel`: `dom vcpus` = the VCPU list from `ks::VCPU_HEAD` (P1's
  `VtIoPlace` placement); `tcbVcpu t = some v ↔ mem (t + tl::VCPU) = v ≠ 0`;
  guest tables equal word for word but root entries 510/511's high halves.
- The capability agreement: `Arch::vcpu_capability = vcpuCapability`,
  `Arch::virtualization() = virtKind.code` (a [P] premise of the
  platform, like the time constants).

### 11.2 Order, size, premises retired

| Step | Content | Retires | Size (Lean lines) |
|---|---|---|---|
| R0 | relations, VCPU-list placement, binding invariant (P1 `JState.vcpu`-style) | — | 800 |
| R1 | sanitize functions = FL4's (`sanitize_vmcs`, `sanitize_vmcb`, `canonical`, `valid_xcr0`, `valid_pat`, `controls`, `msr_addr`): bit-level, pure | — | 700 |
| R2 | VCPU invocations (12 labels), `detach` | the dispatcher's VCPU exclusion (ported `archDecodeInvocation` `.vcpuCap → fail`, replaced by the Ext decoder at J); `JVtHyps.vcpu` (VCPU bound to no thread) becomes the binding invariant | 2500 |
| R3 | EPT invocations, `X86PageMapEPT`, guest-root ASID assign, `TCBSetEPTRoot` | `FrameLabel.native` (EPT mapping excluded); "ASID-assignment leaves require a native extra cap"; the dispatcher's SetEPTRoot exclusion; `JVtHyps.eptFr`/`ept` become relation facts | 2200 |
| R4 | retype of VT-x types, finalisation hooks (VCPU, thread detach, EPT tables, EPT frames, IO ports with owners after §3.3.1) | `JVtxHypM`/`JVtxHypMU` (the [scope] VT-x Untyped retype), `JUtPath.vtx`/`JDevPath.vtx` (`JVtxScope`), the FinVt "spec keeps the state" steps (`JFrVtHyp`, `jFinAt_vt` replaced by Ext steps), P1's "thread finalisation requires an unbound VCPU link" | 1800 |
| R5 | VMEnter/check/report, notification hook, `end_timeslice` hook, stall | `NativeSys`'s exclusion of VMEnter (new `VmSys`), the native idle-bound-notification leaf's `runningVM` exclusion, `J.ext.nat` (`JExt.nat`, `Vs.VsNat`: only native VSpace caps) generalised to `VsNat ∨ guest` | 2500 |
| R6 | exit path: `handle_vcpu_exit` from `VmRunContract` [P] + `VmRunFrame` [P] | — (adds the two [P]) | 900 |
| R7 | P3x (§10) | — | 1000 |

Total about 12,000 lines; R1 and R2 are independent of the J layer and can
start first; R3/R4 touch the J-layer frames (`JAtZ`), R5 the kernel entry
(`XTopJointKEntry*`).

## 12. FINDINGS

- **V1 (compatibility, low)** `notification.rs:94-101`, `vcpu.rs`
  `check`/`report`: a signal to an idle notification bound to a
  `runningVM` thread always sets the notification active and stalls the
  thread's core; the VMEnter completes at the next `check`. seL4
  (`sendSignal`, `CONFIG_VTX`) completes it at once with that badge when
  the thread is on the current core (and does FL4's thing only for a
  remote core). Observable: two signals before the check give one report
  with the OR of both badges; seL4 gives two results. The spec states
  FL4's behaviour.
- **V2 (compatibility, low)** `vcpu.rs` `report`: a VMEnter completed by a
  notification without a valid exit reports MR0..2 = the *sanitized*
  staged RIP/controls/injection and the GPRs; seL4 (`c_traps.c`) leaves
  the MRs as the caller sent them. Harmless for VMMs that resend, but it
  is a difference in the MR contents.
- **V3 (information flow, low-medium)** `vcpu.rs` `vmcb_hidden` vs `vm.rs`
  `run` (`vcpu::set(.., svm::ASID, 1 | flush << 32)`, `svm::CLEAN`):
  ReadVMCB returns the ASID word with the kernel's flush decision and the
  clean bits, which the trusted layer rewrites on every entry from
  per-core state. They tell a VMM whether another VCPU/root ran on that
  core since its last entry (a cross-VMM channel), and make the abstract
  state depend on cache policy. Suggest adding 0x058 and 0x0c0 to
  `vmcb_hidden` (the spec leaves them unspecified for now).
- **V4 (consistency, low)** `ept.rs` `memory_type` maps WP (5) to WB, so
  `frame_entry`'s NPT arm `5 => 5` is unreachable and its comment's
  palette "UC, WC, WT, WP, WB" overstates; EPT callers asking for WP get
  WB silently.
- **V5 (consistency, informational)** `sanitize_vmcs` does not check
  `GUEST_PAT` while `sanitize_vmcb` checks `G_PAT` (`valid_pat`). Safe:
  VM entry checks the guest PAT when "load IA32_PAT" is set (SDM 3C
  §27.3.1.1) and ignores it otherwise; the VMM may clear "load IA32_PAT",
  "load IA32_EFER" and "load debug controls" (allowed entry controls), so
  the guest then runs on the host's PAT/EFER.NXE,SCE/DEBUGCTL, which the
  forced exit controls restore. The spec states it; if the owner wants
  the host values never visible, those three entry controls should be
  forced.
- **V6 (WCET, low-medium)** `vcpu.rs` `revoke_ports` and EnableIOPort walk
  the whole VCPU list (`WALK_FUEL = u64::MAX`) under the serial gate on
  every IO-port cap finalisation (final or not) and on EnableIOPort: O(#VCPUs),
  not preemptible. seL4 looks the owner up by VPID in O(1).
- **V7 (correctness, low)** `vcpu.rs` `revoke_ports` ("a stale owner must
  still name a live VCPU before use"): an IO-port cap whose owner VCPU was
  deleted and whose address was retyped as a new VCPU revokes its range on
  the *new* VCPU when it is finalised (or re-enabled), denying ports the
  new VCPU may hold from other caps. Fail-safe (only denies), but a
  spurious revocation; seL4 has the analogous VPID-reuse behaviour only
  after VPID reassignment. Clearing owners at VCPU finalisation is not
  possible without a back-pointer; a per-VCPU generation in the cap would
  fix it.
- **V8 (compatibility, low-medium)** `sched.rs:483` `end_timeslice`: FL4
  never raises a timeout fault for a `runningVM` thread (`valid` requires
  the state not `TS_RUNNING_VM`); seL4's `endTimeslice`
  (`src/kernel/thread.c`) has no such exception, so a VMM thread with a
  timeout handler whose budget expires inside VMEnter gets a timeout
  fault on seL4 and is only postponed or re-queued on FL4. Possibly
  deliberate (a fault would abandon the VMEnter), but undocumented in
  DESIGN.md §4; the spec states FL4's rule (Q7).
- **Reviewed, no finding**: the forced control bits are required at boot
  (`init_vmx` rejects a CPU whose allowed-1 lacks `PIN_ALLOWED`,
  `PRIMARY_FORCED`, `EXIT_FORCED`), so `controls()` never silently drops
  a forced exit; SVM vector 5 (INVLPGB/TLBSYNC) is never intercepted but
  those instructions #UD because `NESTED_CTL` leaves them disabled; short
  ReadVMCS/WriteVMCS/ReadMSR/WriteMSR return `IllegalOperation` as seL4
  does; `TCBSetEPTRoot`'s errors match seL4's `decodeSetEPTRoot`; IO-port
  derive keeps the owner as seL4's `Arch_deriveCap`; guest entry with a
  deleted ASID uses the empty root; the exit path stores every result
  before servicing a remote stall.

## 13. Questions for the owner

- Q1: move `VcpuState` into `ArchKernelObj.vcpu` (§3.3.2) now, or keep it
  in `VirtExt` (this batch)? Keeping it costs one agreement invariant.
- Q2: approve the `ioPortCap` owner field (§3.3.1)? EnableIOPort and the
  IO-port finalisation cannot be specified faithfully without it.
- Q3: V1/V2: keep FL4's notification-to-VM semantics (the spec states
  them) or follow seL4's same-core immediate completion?
- Q4: V3: hide the SVM ASID/clean words from ReadVMCB (kernel change), so
  the spec can make ReadVMCB deterministic?
- Q5: V5: force "load IA32_PAT/EFER/debug controls" on VMX entry?
- Q7: V8: keep the timeout-fault exemption for `runningVM` threads (and
  document it as an FL4 difference), or follow seL4?
- Q6: is the exit-path [P] (`VmRunContract` + `VmRunFrame`) the right
  trust boundary, or should `vm::run`'s Rust part (everything but the
  assembly) be extracted and proved against `VmRunFrame`?

## 14. Handoff

Done in this batch: §1–§4 and §6–§10 as design; Lean modules VirtBackend,
VirtFields, VirtSanitize, VirtState, VirtEpt, VirtGuest (build: `sh v1.sh
Fl4Spec.Ext.Virt...`, 978 jobs, no sorry; axioms of the definitions and
theorems: propext, Classical.choice, Quot.sound at most).

Next: (1) `Ext/VirtVcpu`: `VcpuInvocation`, `decodeVcpuInvocation` and
`performVcpuInvocation` from the table of §5.1, as `SEMonad`/`SMonad` on
`VState Z` (lift the ported `setThreadState`, `setMR`, `lookupIpcBuffer`
through `VState.base`); (2) `Ext/VirtEptInv` (§5.2, `guestUnmap`);
(3) `Ext/VirtEntry` (§5.3); (4) retype/finalise hooks (§5.4/§5.5) and the
extended dispatcher `fl4DecodeInvocationV` (the ported dispatcher's
`.vcpuCap/.eptCap → fail` replaced); (5) P3x (§10). Q1/Q2 decide the
shape of (1) and (4).
