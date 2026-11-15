# FL4: a verified Rust seL4 with fine-grained SMP

*Design, draft 9 (2026-11-13). Draft 8 is published at https://claude.ai/artifact/3zN2Xrz25AFk4ysqA4qfin; draft 9 changes how fine-grained locking is built (§6, §7, §9, §13).*

FL4 re-implements the seL4 17.0 kernel in Rust. Every seL4 program builds and runs on it unchanged from source, and FL4 adds its own APIs on top. Binary compatibility is not a goal. It makes MCS and SMP first-class, detects hardware at boot instead of asking for configuration, and replaces the big kernel lock with short transactions over a striped lock table. The serial kernel is proven correct in Lean through Aeneas. The concurrent kernel is checked by deterministic simulation against that proven serial kernel.

| | |
|---|---|
| Baseline | seL4 17.0.0-dev (c98d70ad) |
| First target | x86_64, tested only inside QEMU/KVM |
| API | MCS only |
| Next target | AArch64 (future work, not part of the current plan) |
| License | GPL-2.0, same as seL4 |

Assurance levels used below: **Verified** (extracted by Aeneas, proven in Lean), **Sim-tested** (checked by deterministic simulation), **Trusted** (small unsafe or hardware code, reviewed and tested).

## 1. Goals and scope

### Goals

- **A superset of the seL4 API.** Every seL4 user program is a valid FL4 program at the source level: unmodified sel4test sources build against FL4's own libsel4 and pass. FL4 is free to renumber its ABI and adds new features and APIs over time, so FL4 programs need not run on seL4.
- **Few configuration options.** Hardware features are detected at boot. The only build inputs left are the build profile and the few seL4 settings that user programs are compiled against.
- **MCS and SMP as the main configuration.** seL4 treats SMP as a big-kernel-lock add-on and has not verified MCS+SMP. FL4 designs for MCS on many cores from the start.
- **Fine-grained locking.** Independent operations on different cores run in parallel. Two threads doing IPC on separate endpoints never share a lock.
- **Machine-checked serial correctness.** The kernel logic is safe Rust that Aeneas translates to Lean 4. We prove it free of panics and overflow, prove it preserves the kernel invariants, and prove it refines an abstract spec.
- **Tested concurrent correctness.** A deterministic simulator runs the real kernel code on simulated cores and checks that every concurrent run is equivalent to some serial run of the proven kernel.
- **Portable.** x86_64 first. The architecture boundary is drawn so AArch64 is a new backend crate, not a rewrite.

### Out of scope

- The non-MCS (master) API. FL4 builds only with `KernelIsMCS` on. Decided.
- In-kernel IOMMU support. FL4 builds with `KernelIOMMU` off and has no IO page table objects. User space programs the IOMMU directly (§11). Decided.
- 32-bit architectures (ia32, aarch32) and RISC-V.
- Fastpaths. seL4's IPC and exception fastpaths are a second, hand-optimized copy of the general path, with their own proofs. FL4 has only the general path, so there is one implementation to verify. A fastpath can be added later if measurements show a need, together with a proof that it matches the general path. Decided.
- Information-flow (confidentiality) proofs and binary-level translation validation. The design leaves room for both.
- seL4's in-kernel benchmark API (`KernelBenchmarks`: utilisation tracking, kernel-entry tracing, the benchmark log buffer). It exists only in profiling builds, and supporting it would mean another kernel configuration to build, test and verify. FL4 forces `KernelBenchmarks none`, so sel4test's BENCHMARK_0001 is not built. Performance is measured from user space instead (sel4bench, §12).

## 2. Compatibility contract

FL4 is compatible with seL4 at the source level, not the binary level:

- **seL4 programs build and run unchanged.** Any program written against the libsel4 17.0 MCS API compiles against FL4's libsel4 without edits and behaves as the seL4 spec allows.
- **seL4 binaries do not carry over.** FL4 generates its own libsel4 and numbers syscalls, invocation labels, object types, BootInfo records and fault types itself. Every program is rebuilt for FL4.
- **FL4 programs may not build on seL4.** They can use FL4's extensions.

### What stays the same

| Surface                                                                                                            | Rule                                                                       |
|--------------------------------------------------------------------------------------------------------------------|----------------------------------------------------------------------------|
| Functions and types: `seL4_Call`, `seL4_TCB_Configure`, `seL4_MessageInfo_t`, the bitfield accessors, …            | Same names, parameters and return types                                    |
| Constants: `seL4_TCBBits`, `seL4_IllegalOperation`, `seL4_CapInitThreadTCB`, object type names, …                  | Same names. Values may change, so programs that use the names keep working |
| Structures user code reads directly: `seL4_BootInfo`, `seL4_IPCBuffer`, `seL4_UserContext`, extra BootInfo records | Same field names and meanings                                              |
| Build interface: sel4test's CMake settings and the `CONFIG_*` macros user code tests                               | Same names (see §3)                                             |
| Behavior: check order in decoders, which error a failing call returns, fault message contents, scheduling          | Follows the seL4 C source and the ported spec (§9)               |

sel4test does not cover all of that behavior, so FL4 adds a differential fuzzer. It generates programs that use only the seL4 API, builds each one twice, against upstream libsel4 for seL4 and against FL4's libsel4 for FL4, runs both under QEMU and compares their syscall traces (§12).

### What FL4 is free to change

- **Numbering.** FL4 keeps one interface definition: seL4's interface XML, imported into the FL4 tree, with FL4's methods added where they belong in each interface. The generator numbers everything from it and emits the kernel decoders and FL4's libsel4 together, so the two always agree.
- **Object sizes.** The `seL4_*Bits` constants are FL4's own. The first change is `seL4_TCBBits` 12 (4 KiB), so a TCB holds the full AVX-512 register state (2,432 bytes with x87, SSE and AVX). The other sizes keep seL4's values for now.
- **Register conventions.** The syscall register layout could change too. FL4 keeps seL4's x86_64 convention for now, and libsel4's hand-written syscall stubs are reused.

### Extensions

- Every new API gets a new name. The meaning of an existing seL4 name never changes. New behavior on an existing object is a new method, and the seL4 method keeps its seL4 meaning.
- Extensions use the `seL4_` prefix, as the l4h ones already do, and live in the same headers. They are not build options: every FL4 libsel4 and kernel has all of them.
- If upstream seL4 later adds an API that FL4 wants, FL4 adopts it under seL4's name, as a normal part of following seL4.
- **More ASIDs.** x86_64 FL4 has 2048 ASID pools of 512, about 1M ASIDs (20 bits), where seL4 has 8 pools (4096). The API is seL4's (`ASIDControl_MakePool`, `ASIDPool_Assign`); only `seL4_NumASIDPoolsBits` changes, from 3 to 11. User space pays 8 bytes per ASID, in the 4 KiB pools it retypes. The kernel's own memory for ASIDs is fixed: a 16 KiB table of pool pointers and the PCID cache (§11, x86_64 backend). Mapping caps keep the 20-bit ASID in spare bits of their two words. fl4test FL4ASID0001 runs a process whose ASID is above 2^16. The spec port uses the same widths (`Fl4Spec/PORTING.md`).

## 3. Configuration

seL4 has over a hundred `Kernel*` build options, and many of them just tell the kernel what hardware it will run on. FL4 adds no options of its own. It sorts seL4's options into four groups. The only inputs that change the kernel image are the profile and the two settings in the last group, and none of them depend on the hardware.

### Detected at boot (option removed)

| seL4 option                                                                                            | FL4 detects it from                                                                                                                                                                                                                                                                              |
|--------------------------------------------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `KernelLAPICMode`, `KernelUseLogicalIDs`                                                               | CPUID.01H:ECX\[21\] and `IA32_APIC_BASE`. x2APIC when the CPU has it, and always when firmware already turned it on. xAPIC otherwise. IPIs use physical destination mode in both                                                                                                                 |
| `KernelIRQController`, `KernelMaxNumIOAPIC`                                                            | ACPI MADT: IOAPICs when listed, legacy PIC otherwise                                                                                                                                                                                                                                             |
| `KernelPC99TSCFrequency`                                                                               | In order: CPUID 15H/16H on Intel, the hypervisor leaf 40000010H under KVM, then the PIT, which some Alder Lake systems gate off. Measured once on the boot core as the median of 5 runs, never again per core. Reported to user space in the existing `SEL4_BOOTINFO_HEADER_X86_TSC_FREQ` record |
| `KernelSupportPCID`                                                                                    | CPUID.01H:ECX\[17\], with INVPCID from CPUID.07H:EBX\[10\]                                                                                                                                                                                                                                       |
| `KernelFSGSBase`                                                                                       | CPUID.07H:EBX\[0\]. FSGSBASE instructions when present, the MSRs otherwise                                                                                                                                                                                                                       |
| `KernelFPU`, `KernelXSave`, `KernelXSaveFeatureSet`, `KernelXSaveSize`                                 | CPUID 0DH. Best save instruction available (XSAVES, XSAVEC, XSAVEOPT, XSAVE, then FXSAVE). XCR0 enables every user state component the CPU has except AMX tile data (8 KiB), which stays off. The 4 KiB TCB (§2) holds the largest remaining area, 2,432 bytes with AVX-512           |
| `KernelX86MicroArch`                                                                                   | CPUID family and model, for errata only                                                                                                                                                                                                                                                          |
| `KernelSkimWindow`, `KernelX86IBRSMode`, `KernelX86IBPBOnContextSwitch`, `KernelX86RSBOnContextSwitch` | CPUID speculation bits and `IA32_ARCH_CAPABILITIES`. Each mitigation is on exactly when the CPU needs it. The skim window is used only when an Intel CPU does not report `RDCL_NO`; one without `IA32_ARCH_CAPABILITIES` counts as vulnerable. User address spaces then map the kernel image with 4 KiB pages and not the physical-memory window, whose mappings are not global; entries switch to the kernel's tables first and exits back last. Enhanced IBRS (Intel `IBRS_ALL`) or automatic IBRS (AMD) is turned on once per core when the CPU has it. IBPB on context switch is not used (§15)   |
| `KernelMaxNumNodes` (as a hardware count)                                                              | Enabled processors in the MADT. See the last group for the upper bound                                                                                                                                                                                                                           |
| `KernelCacheLnSz`                                                                                      | CPUID.01H:EBX for flush loops. Data layout always aligns to 64 bytes                                                                                                                                                                                                                             |
| `KernelMultiboot1Header`, `KernelMultiboot2Header`, `KernelMultibootGFX*`                              | Both headers are always present. The multiboot2 header asks, as an optional request, for a linear framebuffer with no preferred size                                                                                                                                                             |
| EFER.NXE (for `seL4_X86_ExecuteNever`)                                                                 | CPUID 80000001H:EDX\[20\]. Without execute-disable the attribute is ignored                                                                                                                                                                                                                      |
| MCS timer mode                                                                                         | Already a boot-time choice in seL4: TSC-deadline when available, calibrated LAPIC one-shot otherwise                                                                                                                                                                                             |

### Fixed at one value

These are accepted only at the value FL4 supports. The CMake shim fails the build with a clear message for any other value. Values that user programs see are generated into FL4's libsel4, so programs and kernel always agree.

- API shape: `KernelIsMCS` on, `KernelIOMMU` off, `KernelVTX` and 64-bit VCPU guests on, `KernelNumDomains` 1 (one scheduling domain; `KernelNumDomainSchedules` follows at upstream's value for one domain), `KernelHugePage` on, SYSCALL as the entry method, `KernelPTLevels` 4.
- Kernel limits at seL4's defaults: `KernelNumPriorities` 256, `KernelRetypeFanOutLimit` 256, `KernelMaxNumWorkUnitsPerPreemption` 100, `KernelMaxNumBootinfoUntypedCaps` 230, `KernelBootThreadTimeSlice` 5, `KernelWcetScale` 1, `KernelStaticMaxPeriodUs` 0. The kernel builds these in, so the shim refuses any other value rather than let libsel4's generated configuration advertise a limit the kernel does not enforce (GitHub issue #3). `KernelTimeSlice` (non-MCS only) and `KernelStackBits` (FL4 sizes its own kernel stacks) do not apply.
- `KernelResetChunkBits` is 16: untyped resets clear 64 KiB, then check for preemption, as in l4h patch 0030.
- Always off: fastpaths (`KernelFastpath`, `KernelExceptionFastpath`, `KernelSignalFastpath`) and `KernelDangerousCodeInjection`. `KernelX86DangerousMSR` is on only in the bench profile. Fastpaths are left out because a second, hand-optimized copy of IPC is hard to verify (see §1). User programs cannot tell the difference, since the fastpath only changes speed.
- Compiler options (`KernelOptimisation` and similar) do not apply. Cargo profiles replace them.

### Set by the build profile

There are three profiles, **debug**, **release** and **bench**. Debug turns on `KernelDebugBuild`, `KernelPrinting`, the hardware debug API (breakpoints and single-step, which sel4test turns on for debug builds), invocation error reporting and IRQ reporting. Release turns them all off. Bench is release plus what sel4bench needs to read the performance counters: user-mode `rdpmc` (`KernelExportPMCUser`) and the `seL4_X86DangerousRDMSR`/`WRMSR` syscalls (`KernelX86DangerousMSR`), which the kernel's entry glue answers without entering the core. A project that asks for either gets both; every other build gets neither.

### Read from the user-program configuration

Two settings stay, because user programs are compiled against them. FL4 reads them from the same generated configuration as libsel4:

- `KernelRootCNodeSizeBits`, the size of the root task's CNode (seL4's default is 12; sel4test uses 13, l4h 19).
- `KernelMaxNumNodes` as an upper bound. FL4 starts min(cores found, this value) cores, so a program sized for N cores never sees more than N. The per-core arrays use a fixed internal maximum of 64.

### Boot command line

FL4 keeps one of l4h's boot options, with the same name. It says where console output can be seen, which the build cannot know:

| Option       | Effect                                                                                                |
|--------------|-------------------------------------------------------------------------------------------------------|
| `fb_console` | Also draw the console on the multiboot2 framebuffer, for machines whose serial port cannot be reached |

SMP is not an option either. One kernel image runs on one core or many. With one core, lock operations take a predicted branch on a flag set at boot, so uniprocessor IPC does no atomic operations.

AArch64 follows the same rule: GIC version, timer frequency, physical address size and memory map come from ID registers and the device tree at boot, so one image covers every supported board.

## 4. From the l4h patch series

The l4h kernel is seL4 plus 41 patches (`l4h/kernel/patches`). FL4 includes every fix and feature in that series, except multikernel partitioning (0031 to 0036). The virtualization implementation and its current verification limits are described in [README.md](README.md#x86-virtualization). New APIs become FL4 extensions under §2. Fixes become FL4's behavior from the start, each with a regression test in `fl4test` or the simulator.

### l4h user space

l4h's new methods, constants, flags and BootInfo records keep their l4h names and arguments, so l4h user space builds against FL4's libsel4 with no source changes. Their numbers come from FL4's generator, like everything else, so l4h user space is rebuilt like any other program.

### New APIs

| Patch                  | Extension                                                                                                          | FL4 notes                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
|------------------------|--------------------------------------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0003, 0006             | `seL4_TCB_SetTimer`: one-shot deadline timer per TCB that signals a badge to its bound notification                | The in-kernel timer. Armed timers sit in a per-core balanced tree ordered by deadline, held under that core's scheduler lock. Arm and disarm take O(log n). At most 32 timers fire per kernel entry, and the rest fire on an interrupt programmed for right away. The hardware is armed for the deadline itself, so a timer never fires early. The armed deadline is tracked, and the timer is not reprogrammed for a later deadline. Tree invariants join P1 |
| 0001, 0004, 0027, 0007 | `seL4_TCBFlag_trapSyscalls`: every syscall instruction of the thread goes to its fault handler as `UnknownSyscall` | For foreign syscall ABIs such as Linux processes. `int $N` on the gates open to user space is reported as \#GP with the vector. FL4 always saves and restores the user RSP on SYSCALL entry, with or without the skim window. On AArch64 the fault carries x8                                                                                                                                                                                                 |
| 0002                   | `seL4_TCB_ReadFPU`, `seL4_TCB_WriteFPU` through a frame                                                            | The image is always the standard (uncompacted) XSAVE layout, whatever save instruction was chosen at boot. Written images are sanitized: MXCSR is masked with the CPU's MXCSR_MASK, and only components enabled in XCR0 are kept. A live copy on another core is flushed first, and the state is reloaded when the target is the caller                                                                                                                       |
| 0009                   | `seL4_X86_ExecuteNever` VM attribute                                                                               | Sets XD on 4 KiB, 2 MiB and 1 GiB user mappings, so user space can enforce W^X                                                                                                                                                                                                                                                                                                                                                                                |
| 0017                   | `seL4_X86_DeferFlush` attribute and `seL4_X64_PML4_Flush`                                                          | A remap that only lowers rights can skip the TLB shootdown, and the caller flushes a batch at once. FL4 also adopts the flush rules that need no API: mapping into a not-present entry flushes nothing, and a remap that only raises rights flushes the local core only                                                                                                                                                                                       |
| 0023, 0029             | `Page_TestAndClearAccessed` for 4 KiB and 2 MiB mappings                                                           | For page reclaim in user-level OS personalities                                                                                                                                                                                                                                                                                                                                                                                                               |
| 0029                   | `Page_DeriveSubframe`: 4 KiB aliases of a RAM-backed 2 MiB frame                                                   | The aliases are CDT children of the large frame cap when that cap is original (siblings when it is a copy), so revoking the original removes them. The CDT invariants in P1 cover the new parent-child shape                                                                                                                                                                                                                                                                                                                   |
| 0025                   | `IRQControl_GetIOAPICRemapped`                                                                                     | Programs an IOAPIC pin in remappable format with an interrupt-remapping handle the caller owns. This is the piece that lets a user-space IOMMU driver do interrupt remapping (§11)                                                                                                                                                                                                                                                                  |
| 0021                   | BootInfo record for the boot modules after the first                                                               | The modules are copied above the root task's image, below 4 GiB, and handed over as device untypeds so retyping does not clear them                                                                                                                                                                                                                                                                                                                           |
| 0018                   | BootInfo record for the AArch64 feature ID registers                                                               | Part of the AArch64 port                                                                                                                                                                                                                                                                                                                                                                                                                                      |

### Fixes that become FL4 behavior

| Patch      | Behavior in FL4                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
|------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0000       | Remote stalls can fail. A stall IPI is handled only on the interrupt path. When the remote core is busy, the operation gives up and the syscall restarts. In FL4 a stall is an irrevocable effect, so the transaction that needs it aborts and reruns under the serial gate (§7). The operations that need a stall: TCB invocations, finalising a TCB or SC cap, removing a reply whose donated SC belongs to a thread on another core, `SchedContext_YieldTo`, and `SchedControl_ConfigureFlags`. l4h's GenMC harnesses for the lock and IPI code are ported to FL4's lock table and serial gate, next to the simulator's weak-memory mode |
| 0012       | A timer interrupt that finds the timer still armed belongs to a deadline that has since been replaced. FL4 acknowledges it and returns to user space without starting a transaction. The armed deadline is compared with the time first, so a due interrupt does not pay for the MSR read, which traps under a hypervisor. This prevents the livelock l4h saw with vCPUs that the host deschedules                                                                                                                                                                                                             |
| 0013       | `SchedControl_ConfigureFlags` enqueues a thread on another core only when it is schedulable. A postponed thread still gets a remote queue update, so that core reprograms its timer                                                                                                                                                                                                                                                                                                                                                                                                                            |
| 0014       | APIC countdown mode converts deadlines with both rates instead of their truncated ratio, rounds up so the count never runs out early, and re-arms delays longer than the 32-bit count                                                                                                                                                                                                                                                                                                                                                                                                                          |
| 0019       | At boot, only free pages that contain a nonzero word are cleared, which keeps the hypervisor's shared zero pages. Clean boot untypeds start with a free index of 0. Untyped resets at run time still clear everything                                                                                                                                                                                                                                                                                                                                                                                          |
| 0021       | The load-address search skips memory regions that end below the minimum address and rounds region starts up to a page. Modules whose end is below their start are ignored                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| 0028       | User segments use the Linux layout: data at 0x2b, code at 0x33, and STAR\[63:48\] = 0x23, so SYSRET and IRET load the same selectors. The selector values are not part of the libsel4 API, but a program that reads %cs sees a different value than on seL4                                                                                                                                                                                                                                                                                                                                                    |
| 0030       | Untyped resets clear 64 KiB, then check for preemption (§3)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| 0037       | APs load the full GDT base in real mode                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| 0008       | Every invocation starts with an empty error-message buffer, so an error reply never carries a message left by an earlier, possibly more privileged, invocation. The MCP threshold from the same patch is left out (see below)                                                                                                                                                                                                                                                                                                                                                                                  |
| 0011, 0020 | Multiboot2 framebuffer request and the framebuffer console (§3)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| 0022, 0024 | Timer-rate sources and the Meltdown check, now boot-time detection (§3)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| 0015, 0016 | AArch64 port: broadcast inner-shareable TLBI instead of IPIs, 16-bit ASIDs required (`TCR_EL1.AS`), APs that fail init stop, and MCS uses the CNTFRQ rate read at boot (§11)                                                                                                                                                                                                                                                                                                                                                                                                                           |

### Fixes found while building FL4

Behavior where FL4 differs from seL4 17.0 only by closing a race or an overflow. They were found by the simulator (§10) or the P0 proofs (§9).

| Where                  | Behavior in FL4                                                                                                                                                                                                                                       |
|------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `TCB_CopyRegisters`    | The source thread is stalled like the target when it runs on another core. seL4 stalls only the target, so it copies a stale register context and, with `suspendSource`, leaves the other core running a suspended thread until its next kernel entry |
| Domain time accounting | The check that the domain's time has run out saturates, so a very long interval cannot wrap the sum and underflow the remaining time                                                                                                               |

### FL4 bugs the verification work found

Bugs in FL4's own code, not differences from seL4, kept here because each one shows which check catches what:

| Bug | Found by | Fix |
|-----|----------|-----|
| The release queue's tail was read from the word after its head, which was the deadline-timer tree root (l4h 0003), so arming a TCB timer corrupted the release queue | fl4-sim's release-queue oracle (tail and links), once the workload gave SCs partial and sporadic budgets | `RELEASE_TAIL` follows `RELEASE_HEAD` |
| `budget_check`'s overrun loop gave up after `refill_max + 2` rounds; seL4's has no bound. Charging more budgets than that at once (a long vCPU stall) then took the usage off a smaller head refill, which wrapped, so the SC had an effectively unbounded budget | P1: the ordering proof for `budget_check` would not go through; fl4-sim then reproduced it with 2 s stalls (seed 25 in the regressions) | Walk fuel for the loop, and the post-loop charge guarded by seL4's own assertion (`head.amount > usage`) |
| Finalising a CNode recursed once per level, so deep zombie chains could overflow the kernel stack | P0 (recursion has no measure) | Loops |
| Clearing dirty memory divided by the region size, which can be zero | P0 | Guard |
| Unmapping a 4K frame mapped with the PAT attribute (write-combining) left the entry in place, because bit 7 of a 4K entry (PAT) was tested as the large-page bit; the cap became unmapped over a live user mapping | P3 (VSpace, frame Unmap) | Per-size base-address masks, no PS test for 4K; fl4test FL4VM0005 |
| The timer red-black tree followed links without null checks where only the red-black invariant rules out null, so a damaged tree would write page zero | P1 (timer proofs) | Null nodes have no links and are never written |
| The kernel's `USER_TOP` was libsel4's `seL4_UserTop` (`0x7ffffffff000`), not C's `0x7fffffffffff`, so page-table maps and breakpoints in the last user page were refused where seL4 accepts them | P3 (VSpace, l4v `user_vtop`) | C's value |
| With no receive IPC buffer, `set_mr` returned the running index past the message registers, where seL4 returns `n_msgRegisters`, so fault messages reported a length of up to 18 instead of 4 | P3 (fault-message refinement) | Return `N_MSG_REGISTERS` |
| An NMI, #DB or #MC between SYSCALL and the stack switch pushed its frame on the user's RSP in ring 0 | Review while adding the SYSRET exit | IST stacks |
| VMX controls could advertise performance-MSR switching while CPUID exposed no PMU, causing a host MSR-read fault | Intel real-guest regression | Filter the VMX entry/exit performance controls by PMU availability |
| Deleting a non-final IO-port cap left its VCPU grant active; final cleanup revoked unrelated VCPU grants | Proof port and seL4 lifecycle comparison | Revoke only the cap owner's grant on every finalisation; free the allocation during final cleanup |

The VT-x and AMD-V patches (0038–0043) are implemented through a shared VCPU/EPT API with runtime CPU selection. See [README.md](README.md#x86-virtualization) for implementation and verification status.

### Left out

- **Debug syscall MCP threshold** (0008, `KernelDebugSyscallMinMCP`). FL4 does not gate debug syscalls or kernel error messages by MCP. Debug syscalls exist only in the debug profile, which is not for running untrusted code.
- **Multikernel partitioning** (0031 to 0036). FL4 is always the only kernel on its machine. That drops the kernel load-address build option, the `ap_boot_page=`, `no_legacy_irq`, `peers=`, `console_ring=`, `tsc_mhz=` and `apic_khz=` boot options, and `IRQControl_SendPeer`. FL4 loads at the fixed seL4 address, owns the IOAPICs and PIC, and always measures its own timer rates.

## 5. Architecture

The kernel is a stack of layers. Each one has a single assurance level, so the trusted code stays small and easy to find.

| Layer | Crate | Assurance | Contents |
|---|---|---|---|
| User space | sel4test, rootserver | | Unmodified sources, built against FL4's libsel4 |
| Entry and exit | `fl4-arch-x86_64` | Trusted | SYSCALL/SYSRET, interrupt and exception stubs, register save into the TCB, per-core GS state, FPU switching |
| Transaction runtime | `fl4-sync` | Trusted, sim-tested | Runs each kernel entry as a transaction: begin, commit, retry, escalation to the serial gate, IPI servicing while spinning |
| Kernel logic | `fl4-core` | Verified | Syscall dispatch, decode, CSpace, CDT, IPC, notifications, untyped, scheduling, MCS refills, VSpace logic, IRQ objects. Safe Rust only, generic over the store and arch traits |
| Object store | `fl4-store` | Trusted, sim-tested | Implements `Store` over physical memory: directly on one core or under the serial gate, and transactionally otherwise (versioned reads against the lock table, buffered writes, commit) |
| Hardware backends | | Trusted | Page-table writes, TLB and cache maintenance, x2APIC, TSC-deadline timer, IOAPIC/MSI, ACPI parsing, serial |

### Workspace layout

    fl4/
      crates/
        fl4-abi/          # generated from interfaces/ and .bf; no_std, no unsafe
        fl4-bitfield-gen/ # Rust backend for seL4's bitfield_gen.py
        fl4-core/         # #![forbid(unsafe_code)]; the Aeneas input
        fl4-sync/         # serial gate, transaction driver, IPI-aware spinning
        fl4-store/        # PhysStore, the transactional TxStore and its lock table
        fl4-arch/         # Arch + Platform traits, shared by all backends
        fl4-arch-x86_64/  # entry asm, paging, APIC, timer, FPU, VT-d (later)
        fl4-arch-aarch64/ # placeholder that compiles; filled after M5
        fl4-kernel/       # the kernel binary: boot, glue, linker script
        fl4-sim/          # deterministic simulator and oracles (host binary)
      proofs/             # Lean 4 project (Lake)
        Fl4Core/          # Aeneas output, regenerated by the gate, never hand-edited
        Fl4Proofs/P0/     # no-failure theorems (generated, plus hand-written ones)
        Spec/             # abstract spec, ported from seL4's Isabelle ASpec (MCS)
        Invariants/  Refinement/  Runtime/
      cmake/              # drop-in "kernel" for seL4 CMake projects (sel4test)
      interfaces/         # the one interface definition: seL4's XML imported, plus FL4 methods
      libsel4/            # FL4's libsel4: generated headers + seL4's hand-written ones
      vendor/seL4/        # pinned upstream, for CMake config, generators and the fuzzer's seL4 build
      xtask/              # codegen, extract, prove, sim, sel4test runners

## 6. The verified core

`fl4-core` holds every kernel decision. It has to stay inside the Rust subset that Charon and Aeneas translate, so we design for that from the start rather than retrofit it.

### Rules for `fl4-core`

- `#![no_std]`, no `alloc`, `#![forbid(unsafe_code)]`. No raw pointers, `Cell`, `RefCell`, atomics, `dyn` or closures stored in data.
- Objects are named by typed physical-address handles (`TcbRef`, `EpRef`, `SlotRef`, …), never by references held across calls. Intrusive lists (endpoint queues, ready queues, the CDT) link handles, as in seL4.
- Every fallible path returns `Result`. Arithmetic uses explicit checked or wrapping operations. Aeneas models overflow as failure, so "never fails" theorems cover overflow too.
- Loops are bounded by data the kernel controls (queue length, CNode radix, preemption-point counters). Long operations return to the caller at preemption points, exactly as seL4 does.
- Dependency on hardware goes through two traits: `Store` for kernel memory and `Arch` for machine operations. Both are plain generic parameters, which Aeneas turns into Lean structure arguments.
- CI runs Charon and Aeneas on every commit. A construct Aeneas cannot translate fails the build. This "extractability gate" is the main guard against slowly drifting out of the subset.

### Shape of the core API

The core is written as a serial kernel: one entry point per kind of kernel entry (`handle_syscall`, `handle_interrupt_entry`, `handle_vm_fault`, `handle_user_exception`, …), each taking the store and the machine and running the whole entry, scheduling included. seL4's split into a mostly read-only *decode* and a writing *invoke* is kept as it is in seL4, as a matter of structure, not as an interface concurrency depends on.

    // fl4-core: safe Rust, extracted by Aeneas
    pub trait Store {
        fn read(&self, addr: u64) -> u64;           // kernel memory, by kernel virtual address
        fn write(&mut self, addr: u64, v: u64);
        fn zero(&mut self, addr: u64, len: u64);
        fn ks_base(&self) -> u64;                   // the kernel's global state
        fn cur_cpu(&self) -> u64;
    }
    pub trait Arch { /* time, IRQs, TLB, IOAPIC, ports, FPU, remote stall, console */ }

    pub fn handle_syscall<S: Store, A: Arch>(s: &mut S, a: &mut A, number: i64);

Objects are typed handles over this memory (`Tcb`, `Ep`, `Slot`, …) with field accessors, so every kernel decision is a function of what the store returns. That is what makes one core serve every execution mode: on one core the store is plain memory, on several it is a transaction (§7), and the proofs, which are about the serial core, apply to each committed entry.

### Footprints

A kernel entry's footprint is the set of objects it reads and writes. FL4 does not state footprints in the core: the transactional store records them as the entry runs, exactly, and locks what was written. What needs proving is then a property of the runtime, not of each entry point: that a committed transaction saw a consistent snapshot and that commits are serializable (P2 in §9).

## 7. Fine-grained locking

seL4 SMP protects the whole kernel with one CLH lock (`NODE_LOCK_SYS` in `include/smp/lock.h`). FL4 runs every kernel entry as a short transaction over only the memory it touches, in the style of TL2 software transactional memory. The core does not know: the transaction lives in the `Store` and `Arch` it is given.

### The striped seqlock table

Endpoints are 16 bytes and cap slots 32, and a CNode holds thousands of slots. Instead of growing every small object and every slot by a lock word, FL4 keeps locks in a global table indexed by a hash of the cache line a word lives in.

- Each entry is one cache-line-padded 64-bit word: a lock bit and a 63-bit version. Committing writers set the bit and release it with a new version. Readers check an entry without writing to its line. The default is 4096 entries (256 KiB), configurable.
- Two lines that hash to the same entry share it. This costs some false conflicts but never correctness: the protocol only needs every word to be covered by exactly one entry.
- All kernel memory is covered the same way, per-core scheduler state included. Each core's state lies on its own cache lines, so cores conflict on it only when one really touches another's queues.
- A global version clock orders commits.

### Transaction protocol

Each kernel entry, and each chunk of a preemptible operation, runs as follows:

``` mermaid
flowchart LR
  E[Kernel entry] --> B[begin: mark core active, read clock]
  B --> R[run the core entry on the transactional store]
  R -->|read sees a locked or newer entry| A[abort: drop buffers]
  R -->|irrevocable effect| S[serial gate]
  R -->|done| C[lock written entries in table order]
  C --> V[validate the read set]
  V -->|changed| A
  V -->|ok| W[apply writes, bump clock and versions, release]
  W --> F[run queued effects, exit]
  A -->|retries below N| B
  A -->|retries exceed N| S
  S --> D[drain other transactions, run directly, exit]
```

- **Consistent reads.** A read is valid only if its table entry is unlocked and no newer than the clock value the transaction began with. Otherwise the transaction is doomed: from then on reads return zero and nothing it does is kept. Every loop in the core is bounded (P0), so a doomed entry finishes quickly, and until it is doomed the core sees one consistent snapshot of memory. Reads are plain loads through the kernel window, which maps all of kernel memory, so they never fault.
- **Buffered writes, two-phase commit.** Writes go to a per-core buffer, and later reads of the same word see them. At commit the entries covering the write set are locked in table order, which is deadlock free, then the read set is checked against the start clock, the buffer is written out, and the entries are released with the new version.
- **Deferred effects.** Arch operations other cores or the hardware could observe (reschedule IPIs, timer programming, interrupt masking and acknowledgement, address-space switches, console output) are queued and run after commit, never while holding entries. An interrupt accepted during the entry is kept and offered again if the transaction reruns.
- **Irrevocable operations go serial.** Port I/O, remote stalls, FPU state moving between cores, TLB invalidation, and clears of more than 64 KiB cannot run speculatively. An invalidation must follow the page-table change, which a transaction makes only at commit, and its shootdown IPIs need the gate; mapping into an empty entry invalidates nothing, so most maps stay transactions. A core switching address space publishes its ASID before it loads CR3 (or reads the ASID's invalidation generation, with PCIDs), and an invalidation changes the tables before it looks for cores to shoot down, so a switch racing with an unmap cannot keep a stale entry. The transaction aborts and the entry reruns under the serial gate, as does any entry after N failed attempts (default 4).
- **Clearing free memory runs in place.** An untyped reset clears memory that no live object occupies, and so does making an ASID pool from a fresh frame. Such a clear can exceed the write buffer, but it does not need to be buffered: no other core depends on that memory. `Store::clear_free` means `zero` to the proofs. In a transaction it locks the region's stripes in order, validates the read set, zeroes memory in place along with any buffered writes into it, releases the stripes at a new version, and extends the transaction's read version to it. A reader of the region aborts at the new version. A clear larger than 64 KiB (`KernelResetChunkBits`, so never for a reset) still goes serial.
- **The serial gate.** Transactions mark their core active while they run. A core that needs the gate takes it, waits for active transactions to drain, runs the entry directly on memory, and releases it; new transactions wait while it is held. Rare global operations (domain schedule, IRQ control, ASID pool allocation) also use it. With one core there are no transactions and no gate: the store is plain memory.
- **IPI-aware spinning.** seL4 services remote-stall IPIs while spinning on its lock. FL4 does the same in every spin loop: waiting for the gate, for a transaction to drain, or for a remote call to be acknowledged. IPI handlers touch only core-local state, so a core waiting for an acknowledgement cannot deadlock with a core spinning on a lock.

### Footprints of common operations

What a transaction typically touches, and so where cores can conflict:

| Operation                             | Written                                                                | Only read                                    |
|---------------------------------------|------------------------------------------------------------------------|----------------------------------------------|
| Call to a waiting passive server      | caller TCB, endpoint, server TCB, reply object, caller SC, core's scheduler state | endpoint cap slot, reply cap slot   |
| ReplyRecv                             | server TCB, reply, client TCB, endpoint, SC, core's scheduler state    | endpoint and reply cap slots                 |
| Signal, nobody waiting                | notification                                                           | notification cap slot                        |
| Signal wakes a thread on another core | notification, waiter TCB, target core's scheduler state                | notification cap slot; IPI sent after commit |
| CNode_Copy / Mint                     | source slot, destination slot, source's CDT next-neighbor              | CSpace path slots                            |
| Delete (one preemption chunk)         | slot, CDT prev and next, object if final cap                           | CSpace path slots                            |
| Untyped_Retype (one chunk)            | untyped slot, destination slots, CDT neighbors                         | CSpace path slots                            |
| Timer interrupt (MCS)                 | current TCB, current SC, core's scheduler state                        | none                                         |

The CDT stays seL4's doubly linked list in derivation order, so the "is this the final cap" check and inserts only need the slot and its two neighbors. With MCS, IPC uses reply objects instead of reply caps, so the IPC path never touches the CDT. This is one of the main reasons FL4 builds on MCS. Shared CSpaces stay fast because CSpace walks only read slots: sel4test threads share one CSpace, and every invocation reads slots in it.

### Ownership of running threads

A TCB whose thread is running on core C has its register context owned by C. C saves and restores that context outside any transaction. A remote operation that changes it, such as `TCB_WriteRegisters` or suspend, runs under the serial gate and stalls C with an IPI first, like seL4's `remoteTCBStall`, so C is not running the thread when it changes. When the kernel finds only one core, transactions, the serial gate and IPIs are skipped behind a flag set at boot, which keeps uniprocessor IPC free of atomic operations.

## 8. SMP and MCS semantics

FL4 follows seL4 17.0 MCS+SMP behavior exactly. The design points that matter for locking:

- Each core has its own `SchedControl` cap, ready queues with priority bitmap, release queue and timer. A thread runs on the core of its bound scheduling context.
- When a client donates its SC to a passive server on Call, the server runs on the client's core. Migration changes both cores' scheduler state in one transaction.
- Budget accounting reads the per-core TSC and updates only the current SC, which is in the timer path's footprint. The refill algorithm (`src/kernel/sporadic.c`) is ported directly and verified on its own: refill invariants are some of the first Lean proofs.
- Cross-core wakeups update the target core's queues in the transaction and send the reschedule IPI after it commits, never while holding table entries.
- The domain scheduler keeps seL4's global schedule. Changes go through the serial gate.

## 9. Proof plan

The proof is staged so each level is useful by itself and later levels build on earlier ones.

| Level | Statement                                                                                                                                                                                                                                       | Scope                                                                                           |
|-------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------------------------------------------------------------------------------------------|
| P0    | Every extracted function terminates without failure (no panic, overflow or out-of-bounds) when the invariants hold. Complete: all 1,041 functions, 14 proved by hand; CI fails if any is left (`FL4_P0_STRICT`)                                                                                                                              | All of `fl4-core`                                                                               |
| P1    | Each kernel entry preserves the invariants: well-typed heap, object alignment and non-overlap, CDT well-formed (including subframe aliases), queues consistent with thread states, refill invariants, deadline-timer trees, untyped bookkeeping | All of `fl4-core`                                                                               |
| P2    | Transaction soundness: over an abstract model of `fl4-store` and `fl4-sync`, a committed transaction observed one consistent snapshot, its writes are applied atomically, and any history of committed transactions is equivalent to running them one after another: writers and serial entries in commit order, each read-only transaction on the memory at its start. Proved in `proofs/Fl4Proofs/P2/Runtime.lean` (`sound`, `snapshot`) | Once, for the runtime; required before fine-grained locking ships |
| P3    | Functional refinement: every kernel entry refines the abstract spec                                                                                                                                                                             | One subsystem at a time: CSpace, then IPC and notifications, scheduler and MCS, untyped, VSpace |
| P3x   | Conservative extension: on any state reachable by seL4 calls alone, every seL4 call behaves exactly as in the ported seL4 spec                                                                                                                  | Proven once for the spec, then again for each extension that touches shared state               |
| P4    | Integrity, then confidentiality                                                                                                                                                                                                                 | After P3                                                                                        |

### Status

- **P0**: complete (1,041 functions, 14 by hand), enforced in CI.
- **P1**, in `proofs/Fl4Proofs/P1`, over a `LawfulStore` (a total store with read-after-write laws and a model instance):
  - The invariants: refill rings (structure, ordering, no-overflow, window); thread queues refining list operations, with priority and time ordering; the combined scheduler-queue invariant (exact queued flags, located membership, ready and release queues exclusive); endpoint and notification queues consistent with thread states; bound SCs (BoundInv, SCsOK); reply, SC and notification-binding objects; the deadline-timer trees. Together they form `BlkOK`/`EntryInv`.
  - `kernel_entry.entry`: native syscalls (excluding VMEnter) and interrupt entries preserve `EntryInv`, under `EntryHyps`. Still assumed there: IPC transfer, the composite `handle_invocation` (its per-family pieces are proved), `handle_fault`, `debug_syscall`, `activate_thread`, and three placement facts P3 supplies.
  - Write footprints and frames for the native operations used by P3: cap-slot writes, installs, delete and finalisation, and VSpace operations. The native thread-finalisation leaf requires an unbound VCPU link. None of them breaks the invariant, and finalisation writes no cap slot.
  - The two conditions seL4's C code relies on without checking are P1 invariants, kept by every kernel entry: the current thread has an SC when `switch_sched_context` runs (`BoundInv.resume`, l4v `active_sc_tcb_at`), and a thread blocked on reply has a reply object (`ReplyInv0.reply`).
  - Typed-heap layout, object alignment and non-overlap appear as hypotheses (the sets P1 is parameterised by). CDT and untyped invariants are proved in P3 (`MdbOK`), not yet as P1 invariants.
- **P2**: complete.
- **P3**, in `proofs/Fl4Proofs/P3`, against `Fl4Spec` (the l4v rt abstract spec ported to Lean, up to `call_kernel`; KernelInit_A is dead in l4v and left out). The top-level theorem `handle_invocation_refinesM` relates the decode and invocation of each capability to the spec, from per-capability results and named hypotheses, and carries the CDT invariant `MdbOK` (frame invariant, untyped bookkeeping, no overlap) through a per-step relation `MdbStep`:
  - CSpace: lookups, every CNode invocation, delete and revoke (zombies, preemption), untyped retype and reset, the IRQ and IO port caps.
  - TCBs: native TCB invocations, including cap installs. The dispatcher excludes the new SetEPTRoot label.
  - Scheduling contexts (MCS): SchedContext and SchedControl, budget checks, `set_priority`, and binding and unbinding SCs.
  - VSpace: native frames and page tables, native-root ASID assignment, ASID pools and control, DeriveSubframe, with the VSpace cap-placement invariant (`VsMdbInv`). Guest-tagged pool entries stay occupied during allocation and are rejected by native lookup. `FrameLabel.native` excludes EPT mapping, and ASID-assignment leaves require a native extra cap.
  - Endpoints and notifications: the IPC and signal paths are in progress. The native idle-bound notification leaf excludes a thread running a VM.
  - Hypotheses still to discharge are named in each file. The main ones: the state facts after the TCB fault-handler install, finalisation of a final Endpoint, Notification, Reply, Thread or SchedContext cap on the spec side (`FinWorkHyp`; FL4's side and the VSpace cases are proved), the reply and fault paths, and the placement link between P3's typed heap and P1's object sets.
  - The proofs so far found no disagreement between FL4 and the spec.

### The abstract spec

Decided: we port seL4's Isabelle abstract specification (the MCS version, from `l4v/spec/abstract`) to Lean 4 as a nondeterministic state monad. It is long but close to a transliteration, and it keeps FL4 tied to the meaning the seL4 proofs have already validated. The semantic port covers the MCS native paths; non-MCS paths and IO page tables remain excluded. The cap and object representations include VCPU/EPT objects, and ASID pools retain guest tags as occupied entries while native lookup rejects them. VMEnter, SetEPTRoot, EPT mapping, guest-root ASID assignment, and the VCPU/EPT invocation families still need their own functional refinement; their extracted core functions are covered by P0. Where FL4 must differ, such as per-core state, the difference is written down in the spec and listed in one place.

- The port goes subsystem by subsystem in P3 order. Each Lean definition carries a comment naming the Isabelle definition it comes from, so reviewers can compare them side by side.
- The Lean spec is executable where the Isabelle spec is deterministic. Those parts double as a reference model in the simulator and the differential fuzzer.
- Extensions go in separate Lean modules on top of the ported spec, never as edits to it. Theorem P3x states that they leave seL4 behavior unchanged, which is the formal form of the superset rule in §2.

### From serial to concurrent

The argument

\(1\) A committed transaction ran the serial core on one consistent snapshot of memory and its writes take effect at once, so it behaves like one serial kernel entry, which P0 to P3 are about. (2) Commits are serializable: two-phase locking of the write set with reads validated against the start clock makes any execution equivalent to running the transactions one after another in commit order. A transaction that wrote nothing commits without revalidating, so it serializes at its start rather than at its commit. Together these are P2, a textbook argument proved once in Lean over an abstract model of the runtime, not once per entry point. The model takes each read as one step (the seqlock read in `tx.rs` rechecks the stripe around the load) and the part of a commit that runs with its write stripes locked as one step; lock acquisition, aborts and serial-gate entries interleave freely. (3) Aborted transactions have no effect: their writes stay in the buffer and their Arch effects in the queue. (4) What is left unproven is that `fl4-store`, `fl4-sync` and the IPI paths implement that model correctly on real memory. The simulator tests exactly that.

### Trusted base

The proof assumes: Rust, LLVM and the linker; Charon, Aeneas and the Lean kernel; the abstract spec; entry assembly and boot code; `fl4-store` and `fl4-sync`; hardware backends; and the processor's memory model. Everything trusted is listed in one file in the repo, with its size tracked in CI.

## 10. Deterministic simulation

`fl4-sim` is a host program that links the real `fl4-core`, `fl4-sync` and the transactional store over simulated memory, with a simulated arch backend. Nothing is mocked above the hardware line.

### Execution model

- Each simulated CPU is a coroutine, and all of them run on one host thread, so switching CPUs is a stack switch, not a host context switch. A seeded scheduler decides which CPU runs at every scheduling point: each atomic operation, lock attempt, IPI send and store access. The same seed always replays the same run.
- Time is virtual. Each CPU has its own TSC and TSC-deadline timer, so MCS budget overruns, timeouts and refill edge cases can be hit on purpose.
- Atomics run on a store-buffer model of x86-TSO (`fl4-sim --tso`). `fl4-store` and `fl4-sync` do every atomic operation of the runtime (version table, clock, serial gate) and every commit store through the `Mem` trait. On hardware these are the operations themselves, inlined. In the simulator each core has a FIFO store buffer:
  - Commit stores, the kernel's direct stores, and the runtime's release and relaxed atomic stores go into the buffer.
  - Loads read the core's own newest buffered store first.
  - Locked operations (CAS, fetch-add, SeqCst stores) and SeqCst fences drain the buffer, as does leaving the kernel. Otherwise buffered stores become visible at random points.
  - A mutant that weakens the gate's SeqCst store of a core's "transaction active" flag to Release breaks the Dekker handshake between that store and the gate holder's. It passes 100 seeds under sequentially consistent scheduling and fails 5 under TSO.
  - A weak-memory model for AArch64 is future work.
- User programs are Rust closures that issue seL4 syscalls through the simulated register ABI. Workloads include generated random syscall programs, ports of the SMP-sensitive sel4test cases, and targeted races: revoke during IPC, deleting an endpoint with queued threads on several cores, SC exhaustion during migration, signal racing with a thread being bound to another core.

### Oracles

| Oracle                                                                                                                                                                        | Catches                                                                                           |
|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------|
| **Snapshot checker.** Simulated memory keeps every version of every word. Each value a transaction read must be the value at its start clock, and each write must land only at commit.  | Validation and buffering bugs, found on the first run that executes the path, with no unlucky interleaving needed |
| **Serializability.** Record the commit order, replay the same transactions on a single-core FL4 (the proven configuration), compare every syscall result and the final state. | Lost updates, stale reads, validation bugs                                                        |
| **Invariants.** Executable Rust versions of the P1 invariants, checked after every commit: CDT links, endpoint, notification and release queues (links, tails, owning core), and refills (ring bounds; for periodic SCs, time order without overlap and a total within the period). The workload gives SCs partial and sporadic budgets so the refill paths run. The release-queue checks found a layout bug: the release queue's tail word was the deadline-timer tree root | Corruption, close to where it starts                                                              |
| **Liveness.** Wait-for graph with cycle detection, bounded retry counts, IPI acknowledgement deadlines. As implemented: every wait (for the serial gate, a stripe lock, or a remote stall to be acknowledged) is a counted spin, and a core that spins 2,000,000 times without finishing a kernel entry fails the run. The only blocking waits are on the gate, the stripes and stall acknowledgements, so a deadlock shows up as such a spin. A run that hangs anyway fails on the per-seed timeout | Deadlock, livelock, missed IPIs                                                                   |

### Exploration

- Random walks and PCT (probabilistic concurrency testing) at scale, millions of seeds per night. In PCT (`fl4-sim --pct D`), the live core with the highest priority runs. Priorities start in random order, and at D−1 random scheduling points the running core drops below the others. A spinning core also drops below the others, because it is waiting for another core. Each step of a run has about 50 scheduling points. PCT preempts rarely, so a transaction it preempts usually reads what the other core wrote meanwhile and aborts. As a result PCT catches the runtime mutants below in only 1–2 seeds in 100, and the random scheduler remains the main campaign.
- Bounded exhaustive search with partial-order reduction for small scenarios of 2 to 3 CPUs and a few syscalls each. These cover the hand-picked races completely.
  - As built (`fl4-sim --explore B`), the search runs every schedule of a seed's scenario with up to B preemptions. The schedule is a list of scheduling points at which the running core is preempted; otherwise a core runs until it spins or runs out of steps.
  - The reduction: scheduling points are only the runtime's atomic operations (version table, clock, serial gate). Data accesses are bracketed by version checks, so their order against another core's matters only at those operations.
  - A two-core, six-entry scenario has 550 to 980 such points, and a schedule takes about 2 ms of CPU, so a bound of 1 runs in under a second over all CPUs. `cargo xtask sim` runs four seeds this way.
  - Results so far: it finds the skip-validation mutant with one preemption (43 of 582 schedules fail). It does not find the gate mutants: these scenarios have a single serial entry, which never overlaps a transaction that reads what it writes. Hand-picked scenarios that force that overlap are still to do.
- An eighth of transactions are doomed to the serial path at random, so serial entries overlap running transactions often enough to test the gate.
- Mutation testing checks that the simulator can fail: each known-broken runtime must fail seeds in a 100-seed concurrent campaign. The mutants are test-only Cargo features of `fl4-store` and `fl4-sync` (`mutant-skip-validation`, `mutant-no-publish`, `mutant-gate-no-wait`, `mutant-gate-release`). `cargo xtask mutants` runs each one under the random, PCT and TSO schedulers in CI, and each must be caught by at least one of them. Current catch rates out of 100 seeds (random/PCT/TSO): 36/1/43, 51/1/48, 10/0/15, and 0/0/3 for the last, which only the store-buffer model can see. Measured so far: commit skips read validation (57/100 seeds fail before the snapshot checker; with it 50/100, every one at the faulty commit), the gate does not wait for running transactions (14/100), commit does not publish new stripe versions (53/100; with the checker 52/100, every one at the commit).
- The snapshot checker is implemented as: each word's history tagged with the commit version that wrote it (serial entries take the current clock); a committed writer's reads must match memory just before its commit version, a read-only transaction's its start version. Words a core writes directly outside the gate (its own thread's context, §7) carry no version and are left unchecked; about a tenth of reads fall there.
- Failing seeds shrink automatically and become regression tests. A failing run is cut to the shortest prefix of the same seed that still fails, found by bisecting the step count; one mutant's 4000-step failure shrank to 12 steps. `--record` appends shrunk runs to `crates/fl4-sim/regressions`, which every campaign replays first.
- `cargo xtask sim` runs every campaign above (100 seeds each of random, PCT and TSO, 25 each of the endpoint and notification races under random and TSO, the four bounded searches, and 100 seeds with every entry under the serial gate) in about 5 seconds on 16 host CPUs. Where the time went before, when it took over 25 minutes:
  - Simulated CPUs were host threads handing a baton through a condition variable, about 10 million host context switches for one endpoint-race run.
  - Each run booted again: boot reads all of free memory (l4h 0019), 36 ms. Boot now uses a fixed seed. A campaign boots once and forks a child per run from the booted state, with one child per host CPU at a time, and the seed's RNG starts after boot.
  - The capability and refill oracles scanned the whole 8,192-slot root CNode after every entry. They now check only slots written since the last check, slots that were not empty and unlinked then, and every slot of a CNode or TCB that is new to them. Any other slot is unchanged since a check found it empty and unlinked.
  - Store forwarding searched the whole store buffer, which an untyped reset fills with a thousand stores.
- For bugs seen only in QEMU, QEMU record and replay reproduces the full-system run. The simulator remains the main tool.

## 11. x86_64 now, AArch64 later (future work)

### x86_64 backend

- Multiboot 1 and 2 entry, so QEMU `-kernel` with the rootserver as a module works the way the seL4 x86 build does. APs start with INIT-SIPI-SIPI.
- SYSCALL/SYSRET, per-core GS-based kernel state, SMEP and SMAP, PCID, and the optional kernel skim window (seL4's KPTI-style mitigation). A thread whose context SYSCALL saved leaves by SYSRET (Error = −1, as in seL4), and only when its return address is in the canonical lower half, so SYSRET never faults in ring 0 with the user's RSP loaded. Every other exit uses IRET. NMI, #DB, #MC and #DF run on per-core IST stacks, because the instructions just after SYSCALL and just before SYSRET run in ring 0 on the user's stack pointer.
- PCIDs, when the CPU has them, are a per-core cache of ASIDs: ASIDs have 20 bits and PCIDs 12. Each core has a direct-mapped table of 512 PCIDs, indexed by a hash of the ASID that gives the ASIDs of one pool distinct entries. An entry holds the ASID it last ran and that ASID's invalidation generation. Invalidating an ASID bumps a generation in a global table of 4096 words, which ASIDs share by hash, and shoots down the cores running it. A core flushes a PCID when it takes it for another ASID, or when the generation moved. Sharing a generation costs only extra flushes. Memory is 32 KiB global plus 8 KiB per core, whatever the number of ASIDs; seL4 instead uses the ASID as the PCID. The test host has no PCIDs (§12), so this path is covered by host unit tests of the table, not by sel4test.
- x2APIC or xAPIC, chosen at boot (§3). In xAPIC mode IPIs use physical destination mode, so more than 8 cores can be addressed.
- MCS timer: TSC-deadline mode when CPUID reports it, otherwise the LAPIC one-shot timer with a TSC-to-APIC ratio calibrated at boot. seL4 has the same fallback in `apic.c`. Both are first-class paths, and the test setups in §12 exercise each one.
- IOAPIC and MSI routing, ACPI MADT parsing, IO port caps.
- The PIT is used only for calibration, on channel 2. Channel 0 is put in one-shot mode at boot, because firmware leaves it interrupting at 18.2 Hz on ISA IRQ 0, which is IOAPIC pin 2, where user space may route an HPET timer.
- XSAVE-family FPU switching, chosen at boot like the other mitigations (§3). On Intel CPUs it is eager: the incoming thread's state is loaded on every switch, because lazy switching is what LazyFP (CVE-2018-3665) exploits. On CPUs LazyFP does not affect (AMD) it is lazy, as in seL4. A thread that doesn't own the FPU registers runs with CR0.TS set. Its first FPU instruction raises #NM, and the entry glue swaps the state and returns to the thread without entering the core. fl4test FL4FPU0003 checks that two threads keep their own registers across IPC; it fails on a mutant that leaves TS clear. A thread that keeps using the FPU would pay a trap and two CR0 writes per switch, more than the eager switch costs (CR0 writes are slow under KVM). So each thread counts its #NM traps in a byte after its FPU image. From the third trap on it is switched eagerly; the byte keeps counting and wraps, so after 256 switches the thread is tried lazily again (Linux once did the same with `fpu_counter`). Guest execution uses the bound TCB's FPU image and switches a validated guest XCR0 around each VM entry.

### IOMMU left to user space

FL4 has no IO page table objects and no `IOSpace` caps. The kernel never programs the IOMMU.

- The kernel parses the ACPI DMAR (Intel) or IVRS (AMD) table only to find the IOMMU's MMIO registers. It does not reserve them, so they show up in BootInfo as ordinary device untypeds, and the root task can hand them to an IOMMU driver.
- User space finds the DMAR or IVRS table through the ACPI RSDP that seL4 already passes in BootInfo, so no new interface is needed.
- The kernel leaves the IOMMU in whatever state firmware set. A driver that enables translation has to map anything devices need, which is its job.
- The consequence is that DMA isolation now depends on the user-space driver, and devices can reach kernel memory until that driver turns translation on. This is a deliberate trade, and the trusted-base list records it.
- sel4test's IO page table tests are compiled only when `CONFIG_IOMMU` is set, so the suite runs unchanged without them.

### Keeping AArch64 cheap

- `Arch` covers register context, fault decoding, page-table formats as associated types, TLB and cache maintenance, and IRQ controller access. `fl4-core` never names an x86 type.
- Arch-specific kernel objects (page tables, ASID pools, IO ports) are an enum in `fl4-core` selected by `cfg`, with verified logic per architecture. Their invariants are written against the `Arch` trait.
- `fl4-sync` uses only acquire/release orderings plus explicit fences. Nothing relies on x86-TSO, and the simulator's weak-memory mode checks that.
- The AArch64 fixes from l4h are requirements of the port: broadcast TLB invalidation, 16-bit ASIDs, CNTFRQ for MCS accounting, the ID-register BootInfo record, and x8 in trapped-syscall faults (§4).
- The AArch64 placeholder crate compiles in CI from M0, so the trait boundary cannot quietly pick up x86 assumptions.

## 12. sel4test and CI

sel4test finds the kernel through `find_package(seL4)` in its `kernel/` directory and builds libsel4 and the kernel image from there. FL4 ships a drop-in replacement in `cmake/`:

- It reuses upstream seL4's CMake configuration from `vendor/seL4`, so sel4test's settings work unchanged, but builds libsel4 from FL4's `libsel4/` and generators instead of upstream's.
- It replaces only the `kernel.elf` target with a `cargo build` that reads the generated configuration and checks it against §3.
- sel4test runs with `SIMULATION=OFF`, because its `SIMULATION` mode turns on `KernelIOMMU` for x86. With `SIMULATION` off, a debug build also turns on the hardware debug API, so FL4 implements breakpoints and single-step in the debug profile. KVM passes debug registers through to the guest.
- FL4's extensions get their own suite, `fl4test`, built on the same test framework and run in the same QEMU setups. It covers every extension and fix taken from l4h. sel4test itself stays unmodified: `fl4test/fl4test.c` is linked into sel4test's test application, its tests are named `FL4…`, sel4test runs filter them out and `cargo xtask fl4test` runs only them.
- l4h user space, rebuilt against FL4's libsel4, runs under QEMU/KVM as a second compatibility check. Parts that depend on multikernel boot are skipped.
- `xtask sel4test` links the checkout at `~/Projects/sel4test` with this kernel directory, builds, runs under QEMU and parses the test summary. sel4test has 228 test definitions. Each one is tracked separately so progress is visible.

### Test machine

FL4 is never booted on the development machine's hardware. Every kernel run happens inside a QEMU/KVM guest on that machine, driven locally by `xtask`. Hosted CI can come later with the same commands.

|                   |                                                                                                                                                                            |
|-------------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| CPU               | AMD Ryzen 7 7700 (Zen 4), 8 cores, 16 threads                                                                                                                              |
| Memory            | 61 GiB                                                                                                                                                                     |
| Virtualisation    | KVM (AMD-V), `/dev/kvm` usable by the build user                                                                                                                           |
| QEMU              | 10.0.13                                                                                                                                                                    |
| Relevant features | Has `invpcid`, `smep`, `smap`, `xsaves`, `fsgsbase`, automatic IBRS, 1 GiB pages, invariant TSC. No PCIDs (neither has TCG), so FL4's PCID paths are not exercised here; no TSC-deadline timer. x2APIC is not exposed to the host. AMD-Vi IOMMU present. |

KVM emulates both x2APIC and the TSC-deadline timer for guests, even though this host CPU lacks both. Masking them in the guest CPU model covers the fallback paths that real CPUs without those features would take. So sel4test runs in three QEMU setups:

| Setup                 | QEMU options                                        | Purpose                                                                         |
|-----------------------|-----------------------------------------------------|---------------------------------------------------------------------------------|
| KVM, full features    | `-enable-kvm -machine kernel-irqchip=split -cpu host`                       | Fast main loop; x2APIC and TSC-deadline paths. Same kernel image in every setup |
| KVM, reduced features | `-enable-kvm -machine kernel-irqchip=split -cpu host,-x2apic,-tsc-deadline,-pcid,-invpcid,-fsgsbase,-xsaves,-xsavec` | xAPIC, the calibrated one-shot timer, no PCIDs, the FS/GS MSRs and XSAVEOPT     |
| TCG                   | `-accel tcg`, record and replay when needed                                 | An independent CPU and device model, for failures seen under KVM               |
| TCG, Intel model      | `-accel tcg -cpu Skylake-Client-v1`                                          | A Meltdown-affected CPU: the skim window paths                                   |

The KVM setups keep the IOAPIC in QEMU (`kernel-irqchip=split`). With KVM's in-kernel IOAPIC, QEMU routes GSI 0 (the PIT) to pin 2 and gives GSI 2 no route. sel4test's timer driver puts the HPET on pin 2, so its interrupts never arrive. That was the cause of SCHED0000 failing ("flaky") and INTERRUPT0005 hanging under KVM: the driver ran only on stray PIT interrupts every 55 ms instead of its own 10 ms ones. Since the change no sel4test test is skipped. Three tests measure wall-clock scheduling and depend on the host: SCHED0011, SCHED0014 and TIMEOUTFAULT0001. With 4 cores in kvm-reduced, SCHED0014 failed 20 runs out of 20 on upstream seL4 (`FL4_KERNEL=sel4`, the same tests on vendor/seL4) and 5 out of 20 on FL4, on a host with load 5 to 7. Upstream already disables the test under simulation. When a run's only failures are among these three, xtask reruns them alone up to three times and says so in the log. Any other failure fails the run. Under `-icount`, QEMU 10.0 currently stops with "Bad icount read" during boot, so the TCG setup runs without it until that is resolved.

`cargo xtask uefi` boots the same kernel and sel4test's driver through GRUB's Multiboot 2 loader on OVMF (UEFI) under KVM, and checks that the kernel finds ACPI from the RSDP the bootloader passes, starts every core and starts the root task. UEFI firmware keeps its ACPI tables outside the BIOS areas the legacy search covers (GitHub issue #8). sel4test's driver stops there on any kernel: its timer set-up looks for the RSDP in the BIOS areas from user space, not in BootInfo.

Performance numbers come from KVM with pinned vCPUs and are labelled that way. They are compared with upstream seL4 measured in the same setup, never with bare-metal figures.

### Test matrix

| Job                               | Configurations                                                                                             | When                       |
|-----------------------------------|------------------------------------------------------------------------------------------------------------|----------------------------|
| sel4test on QEMU                  | x86_64 MCS × {1, 2, 4 cores} × {debug, release} × the first two setups above                               | Every PR                   |
| Extract and check proofs          | Charon → Aeneas → `lake build`                                                                             | Every PR                   |
| Simulation, short                 | 10⁴ seeds plus all regression seeds                                                             | Every PR                   |
| Simulation, long                  | Millions of seeds, PCT, exhaustive small scenarios, TSO and weak modes                                     | Nightly                    |
| Differential fuzzing against seL4 | Same generated programs on seL4 and FL4, compare traces (`cargo xtask fuzz`, fl4test/fuzz.c)               | Nightly                    |
| Performance                       | sel4bench IPC and signal latency; multi-core scaling on independent endpoints; FL4 and seL4 both under KVM | Nightly, tracked over time |

Performance targets: uniprocessor IPC within 1.2× of seL4 built with `KernelFastpath` off (seL4 with its fastpath is also measured and reported, for reference), and near-linear throughput scaling for independent IPC pairs where seL4's big lock stays flat. The machine has 8 physical cores, so scaling is measured up to 8 vCPUs pinned one per physical core.

The baseline seL4 must have the same mitigations as FL4 on the test CPU. seL4's x86_64 default turns on `KernelSkimWindow`, which switches CR3 on every entry and exit. FL4 turns the skim window on only where the CPU needs it (§3). The development machine (AMD Zen 4) doesn't, so `cargo xtask bench sel4` builds seL4 with `KernelSkimWindow=OFF` (and `KernelSupportPCID=OFF`, `KernelFSGSBase=msr`). Measured on that machine (cycles, medians, `cargo xtask bench`, one pinned vCPU):

| IPC                        | seL4, skim on (default) | seL4, skim off | FL4 before | FL4, SYSRET exit and LTO | FL4, also lazy FPU |
|----------------------------|-------------------------|----------------|------------|--------------------------|--------------------|
| Call, same address space   | 1026                    | 494            | 950–988    | 836                      | 684–722            |
| ReplyRecv, same            | 1064–1102               | 494–513        | 1102       | 1026                     | 874                |
| Call, cross address space  | 1026                    | 798–817        | 1216–1254  | 1064                     | 912–950            |
| ReplyRecv, cross           | 1064–1102               | 798–836        | 1349–1368  | 1254                     | 1102               |

Against the like-for-like baseline FL4 is now at 1.14–1.7×. Cross-address-space Call is the closest; same-address-space Call and ReplyRecv are the furthest. That is not yet 1.2×. Instrumentation (TSC and retired-instruction counts at stage boundaries) shows where the rest goes:
- About 1800 kernel instructions per Call or ReplyRecv. The capability lookup takes about 200 and the extra-caps lookup about 200 even with no extra caps; budget charging takes about 85, scheduling 90–210, and the exit path about 150.
- Eager FPU switching cost about 130 cycles per switch between threads, for XSAVES and XRSTORS, because the owner changes on every IPC round trip. Lazy switching on CPUs without LazyFP (§11) removed it: on this machine, Call went from 836 to 722 cycles (same address space) and from 1064 to 950 (cross).
- One CR3 write plus the TLB refill after it costs about 280 cycles. That is the whole cross-address-space difference; this CPU has no PCIDs.

sel4bench's signal benchmark (`-DSIGNAL=ON`) currently fails in the same way on both kernels: its child thread dies with an invalid instruction. It is a setup problem in the benchmark build, so `cargo xtask bench` runs the IPC benchmarks only. Counting retired kernel instructions per Call or ReplyRecv the same way in both kernels (PMC0 in kernel mode, read at entry and exit; a temporary patch) gives about 580–990 for seL4 and 1550–1990 for FL4, so FL4's path is 2–2.7× longer in instructions. Closing the gap is M5 work on the general path in `fl4-core`: fewer capability decodes and encodes, repeated loads of the current thread and its fields, and the many small helper calls of a direct transliteration.

The differential fuzzer (`cargo xtask fuzz`) builds `fl4test/fuzz.c` against upstream seL4 and against FL4 and runs both in the KVM setup.
- Each of 40 seeds generates a program of 400 calls. It runs in a thread whose CSpace is a fresh 256-slot CNode holding only that CNode and a private 64 KiB untyped. Capability pointers are therefore slot numbers, and nothing depends on the root task's memory layout.
- The calls are retypes of endpoints, notifications, replies, CNodes, untypeds and scheduling contexts; CNode Copy, Mint, Move, Mutate, Delete, Revoke, Rotate and CancelBadgedSends; and non-blocking sends.
- The trace records each call's arguments, its error, the message registers a failure returns, and the types of the capabilities in the slots it touched (`seL4_DebugCapIdentify`).
- The first run gave 16,000 identical trace lines. Every call kind both succeeded and failed in several ways: success, InvalidCapability, FailedLookup, DeleteFirst, IllegalOperation, RangeError, NotEnoughMemory.
- Left out for now:
  - Receives. A receive through a capability without the Read right is a capability fault, which the program would need a fault handler to survive.
  - TCB and frame objects, whose sizes differ between the kernels.

Multi-core scaling is measured by fl4test's FL4PERF0002 (`fl4test/perf.c`). It uses only the seL4 API, so it also runs on upstream seL4 with `FL4_KERNEL=sel4`. It runs k independent client/server pairs, pair i on core i, for k = 1 to the number of cores, and prints round trips per million TSC ticks. These are debug builds with 8 unpinned vCPUs on a host shared with other VMs, so expect noise:

| Pairs | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|-------|---|---|---|---|---|---|---|---|
| seL4  | 96 | 112 | 109 | 109 | 108 | 83 | 65 | 78 |
| FL4   | 186 | 325 | 347 | 318 | 742 | 861 | 706 | 279 |

seL4 stays flat behind its kernel lock. FL4 reaches 4.6× at 6 pairs, but not smoothly. The transaction log (`fl4_store::tx::conflicts`, printed with the debug statistics) shows why: most aborts come from small objects of *different* pairs sharing a 64-byte stripe. Endpoints are 16 bytes and reply objects 32, both fixed by the seL4 API, and allocators place them next to each other.

Two experiments with 16-byte stripes failed:
- A hashed table of 16384 entries made the curve smooth (159 to 757, 4.8×) but raised the abort rate to about 15%, through hash collisions.
- An adjacency-preserving table raised serial entries tenfold.

`FL4_PIN=c0,c1,...` pins each vCPU thread to a host CPU; xtask gets the thread IDs from QEMU over QMP. Until the kbench work it also pinned a bogus "thread 0" (the SMT thread number in each CPU's QMP `props`), which shifted the list so that two vCPUs shared one host CPU. That, not the host, explains an earlier pinned run in which both kernels slowed down more than 20× from 5 pairs on.

**Kernel-intensive SMP throughput** (`cargo xtask kbench`, fl4test FL4PERF0003). k workers on k cores, k = 1, 2, 4, 6, each repeat one kernel operation on objects of their own for a fixed window of 10⁸ TSC ticks:
- `yield`: `seL4_Yield`.
- `signal`: Signal plus Wait on the worker's own notification.
- `ipc`: Call to a server on the same core.
- `xipc`: Call to a server on the next core.
- `cap`: CNode Copy plus Delete.
- `retype`: Untyped Retype of an endpoint plus Delete, which resets the untyped.
- `map`: Page Unmap plus Map of a 4 KiB frame in the one shared address space.

Both kernels are release builds, seL4 with the skim window off as in the uniprocessor comparison. There are 6 vCPUs under KVM, pinned to host cores 2–7, on a host shared with another project's 8-vCPU VM. The table gives the median of 3 alternating rounds, in operations per million TSC ticks summed over all cores; a whole kbench takes about 15 s. The spread between rounds is mostly within ±10%, and 2-core runs vary more (up to ±30%).

| Workload | Kernel | 1 core | 2 | 4 | 6 |
|----------|--------|--------|---|---|---|
| yield    | FL4    | 643  | 1151 | 2009 | 3020 |
|          | seL4   | 274  | 238  | 236  | 221  |
| signal   | FL4    | 622  | 1021 | 1731 | 2467 |
|          | seL4   | 1962 | 1550 | 1341 | 1301 |
| ipc      | FL4    | 182  | 341  | 577  | 854  |
|          | seL4   | 113  | 105  | 104  | 101  |
| xipc     | FL4    | –    | 69   | 122  | 159  |
|          | seL4   | –    | 30   | 30   | 26   |
| cap      | FL4    | 360  | 626  | 994  | 1322 |
|          | seL4   | 1340 | 1094 | 1023 | 1015 |
| retype   | FL4    | 208  | 366  | 735  | 706  |
|          | seL4   | 946  | 684  | 669  | 665  |
| map      | FL4    | 346  | 171  | 76   | 55   |
|          | seL4   | 7    | 7    | 7    | 7    |

What the table shows:
- **seL4 does not scale.** Its throughput is flat or falls with cores, as its big kernel lock predicts.
- **FL4 scales on independent objects.** From 1 to 6 cores: yield 4.7×, ipc 4.7×, signal 4.0×, cap 3.7×.
- **retype scales 3.4×.** The untyped reset clears free memory in place inside the transaction (§7). Before that, the 4 KiB clear overflowed the write buffer, and every reset reran under the serial gate. Retype then measured 268, 352, 425 and 430, levelling off at 1.6×. Locking and validating the region costs a single core about a fifth of its throughput (268 to 208).
- **map gets slower with more workers.** All workers share one address space, so every unmap shoots down every other worker's core.
- **FL4 costs more per operation on the multi-core build.** On one core it is about 3.5× slower than seL4 for signal, cap and retype. Not yet measured: whether that is transaction bookkeeping or the gate. The crossover is at about 4 cores for signal and cap, and at about 6 for retype.
- **seL4 is slow on yield and ipc, likely because of timer writes under KVM.** seL4's yield and same-core IPC take 3,600 and 8,800 ticks. A likely cause, not yet confirmed, is MCS reprogramming the timer on each scheduling-context switch, which is a VM exit under KVM.
- **seL4's map is about 50× FL4's on one core.** seL4 shoots down every core that has run the address space, even idle ones, which KVM must wake. FL4 interrupts only the cores currently running the ASID (§3).


## 13. Milestones

Ordered by dependency. Each milestone ends with a check that can be run.

- **M0 Scaffolding** — ABI and bitfield generators, workspace, CMake drop-in, Aeneas pipeline on a stub core, boot to a serial banner on QEMU. *Exit: sel4test builds against FL4; extraction runs in CI.*
- **M1 Uniprocessor MCS kernel** — CSpace, CDT, untyped, TCB, endpoints, notifications, reply and SC objects, VSpace, IRQs, faults, debug syscalls, both MCS timer modes. The l4h fixes, and the l4h extensions that do not depend on SMP. *Exit: sel4test passes with 1 core, debug and release, in both KVM setups.*
- **M2 P0 and first P1 proofs** — No-failure proofs for all of `fl4-core`, CDT and refill invariants. *Exit: P0 complete; extraction gate enforced.*
- **M3 SMP in serial-gate mode** — APs, per-core scheduling, IPIs, migration, and the remaining l4h extensions. Every transaction takes the serial gate, which behaves like a big lock. Simulator with oracles running. *Exit: sel4test passes with 2 and 4 cores.*
- **M4 Fine-grained locking** — The transactional store over the lock table, deferred Arch effects, escalation of irrevocable entries to the serial gate, and the simulator interleaving transactions inside kernel entries. P2 for the runtime. Serial-gate mode stays as a test-only Cargo feature for differential runs. It is not a user-facing option. *Exit: P2 complete; nightly simulation clean for two weeks; sel4test passes; scaling target met.*
- **M5 P1 completion and performance** — Full invariant set. Speed up the general IPC path in `fl4-core` without adding a second copy of it. *Exit: P1 complete; uniprocessor IPC within target.*
- **M6 Refinement** — P3 per subsystem against the ported spec. *Exit: each subsystem's refinement proof lands separately.*

AArch64 is future work, outside M1–M6. The boundary rules in §11 still apply, so the port stays a new backend crate when it happens.

## 14. Risks

| Risk                                                                                      | Mitigation                                                                                                                                                                             |
|-------------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Aeneas cannot express some kernel patterns, or proof terms grow too large at kernel scale | Extractability gate from M0. Keep functions small. Prove against the `Store` trait instead of a concrete heap. Budget time to contribute upstream fixes to Charon and Aeneas.          |
| Porting the abstract spec to Lean is a large job                                          | Port incrementally per subsystem, in the same order as P3. P0 to P2 do not need the abstract spec.                                                                                     |
| Behavior differs from seL4 in cases sel4test does not cover                               | Differential fuzzing against seL4 on QEMU. Decoders follow the C source check by check.                                                                                                |
| Retries make worst-case execution time hard to bound                                      | Serial-gate escalation after N retries gives a bound comparable to the big lock. Measure retry rates in simulation and on hardware.                                                    |
| False sharing in the lock table under load                                                | Table size is configurable. The hash includes high address bits. Monitor collision counters in benchmark builds.                                                                       |
| The simulator misses a bug that only real hardware shows                                  | Keep the trusted runtime tiny, test both KVM CPU models and TCG, and use QEMU record and replay to reproduce.                                                                          |
| KVM hides timing and ordering behavior of real hardware, and one AMD host runs every test | The reduced-feature KVM setup covers the fallback hardware paths. The simulator's memory model does not depend on the host. Add an Intel KVM host once FL4 is ready for wider testing. |

## 15. Decisions

Settled on 2026-11-12.

| Question                    | Decision                                                                                                                                  | Where it applies                             |
|-----------------------------|-------------------------------------------------------------------------------------------------------------------------------------------|----------------------------------------------|
| Support the non-MCS API?    | No. MCS only.                                                                                                                             | §1, §2, §12 |
| Source of the abstract spec | Port seL4's Isabelle abstract spec to Lean.                                                                                               | §9                                 |
| IOMMU                       | No in-kernel support. User space programs the IOMMU directly.                                                                             | §11                                |
| Configuration               | As few options as possible. Hardware is detected at boot, not configured.                                                                 | §3                                |
| API evolution               | FL4 is a superset of the seL4 API. Every seL4 program builds and runs on FL4 from source, but FL4 programs may use extensions seL4 lacks. | §2, §9                  |
| l4h patch series            | Include every fix and feature except multikernel partitioning and the debug syscall MCP threshold.                           | §4                                   |
| Binary compatibility        | Not a goal. FL4 is compatible with the seL4 API at the source level and numbers its own ABI.                                              | §2                                |
| Debug syscall MCP threshold | Not supported.                                                                                                                            | §4                                   |
| Multikernel                 | Not supported. FL4 is the only kernel on its machine.                                                                                     | §4                                   |
| Fastpaths                   | None for now. Only the general, verified IPC path.                                                                                        | §1, §3                  |
| Test hardware               | Only inside QEMU/KVM guests on the development machine. FL4 never boots on that machine's hardware.                                       | §12                              |
| Fine-grained locking        | A transactional store (TL2 style) under the unchanged serial core, not a prepare/perform split of every operation. Decided 2026-11-13. | §6, §7, §9, §13 |
| IBPB on context switch      | Not used. It protects user programs from each other through the branch predictor at thousands of cycles per switch between address spaces; as in seL4's default configuration, that threat is outside FL4's model for now. Decided 2026-11-13. | §3 |

VT-x and AMD-V support precede the AArch64 port. P0 covers the virtualization policy; P1/P3 use the expanded capability and TCB layouts, with native semantic scope as described in §9.
