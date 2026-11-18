# FL4

FL4 is a Rust re-implementation of the seL4 17.0 microkernel (MCS API) with
first-class SMP and fine-grained locking. See [DESIGN.md](DESIGN.md).

## Layout

| Path | Contents |
|---|---|
| `crates/fl4-core` | Kernel logic, safe Rust, extracted to Lean by Charon/Aeneas |
| `crates/fl4-abi` | ABI numbering generated from `interfaces/` and the build configuration |
| `crates/fl4-kernel` | The x86_64 kernel image (boot, glue) |
| `crates/fl4-arch-x86_64` | x86_64 hardware backend |
| `crates/fl4-sync`, `fl4-store` | Transaction runtime and object store |
| `crates/fl4-sim` | Deterministic simulator |
| `interfaces/` | The one interface definition (seL4's XML, pruned to FL4's configuration, plus FL4 methods) |
| `libsel4/` | FL4's libsel4 |
| `cmake/` | Drop-in `kernel` directory for seL4 CMake projects such as sel4test |
| `proofs/` | Lean 4 project: `Fl4Core/` is extracted, `Fl4Proofs/` holds the proofs |
| `vendor/seL4` | Pinned upstream seL4 (submodule) |

## Tasks

Development runs use QEMU. The AMD SEV guest test runs on a confidential VM.

```
cargo xtask run [--setup kvm|kvm-reduced|tcg]   # boot the standalone kernel
cargo xtask sel4test [--release] [--smp N] [--setup ...]
cargo xtask extract                              # Charon + Aeneas -> proofs/Fl4Core
(cd proofs && lake build)                        # check the proofs
```

Host dependencies live in `$FL4_DEPS` (default `~/Projects/fl4-deps`):
`venv/` with `sel4-deps`, and an `aeneas/` checkout with Charon built.

## AMD SEV guests

The x86_64 image detects base AMD Secure Encrypted Virtualization (SEV) at
boot. Kernel and userspace RAM, page tables, boot modules and firmware ACPI
data start private. Device MMIO uses shared mappings. The serial banner shows
the active C-bit. SEV-ES, SEV-SNP and nested virtualization inside an SEV
guest are outside the supported configuration.

The extra BootInfo record `SEL4_BOOTINFO_HEADER_SHARED_DMA` tells drivers
that DMA requires shared RAM. Drivers allocate buffers with
`seL4_Untyped_RetypeShared(source, size_bits, root, node_index, node_depth, node_offset, num_objects)`.
The call takes ordinary RAM from the same allocation watermark as
`seL4_Untyped_Retype`. It creates up to 256 contiguous 4 KiB frames or one
2 MiB frame per call and installs one cap per consecutive empty destination
slot. Zero index and depth address the supplied root CNode directly.

The frames start zeroed, including for uncached access. Copies of a frame cap
share its visibility. `seL4_X86_Page_GetAddress` returns the GPA to program
into the device. [Userspace NVMe example](xtask/tests/sev_guest.c)

Shared frames have device-frame restrictions, including exclusion from IPC
buffers and subframe derivation. Stop DMA before revoking the source or
deleting the last frame cap. Final deletion unmaps the frame, flushes the
shared alias, and zeros the private memory before reuse. On native hardware
drivers use ordinary RAM and the invocation returns `seL4_IllegalOperation`.
In an SEV guest a device untyped returns `seL4_InvalidCapability` and an
unsupported frame size returns `seL4_InvalidArgument`. [AMD memory encryption](https://docs.kernel.org/arch/x86/amd-memory-encryption.html)

`xtask/scripts/sev-smoke-image.sh` builds `build/sev-smoke/fl4-sev.tar.gz`
with a GRUB EFI loader and a test root task. The script requires the sel4test
build dependencies, GRUB's x86_64 EFI tools, sgdisk and mtools. Import the
archive as a GCE image with `UEFI_COMPATIBLE,SEV_CAPABLE,GVNIC`. Boot it on
an `n2d-standard-2` AMD Milan VM with `--confidential-compute-type=SEV`,
`--maintenance-policy=TERMINATE` and an NVMe boot disk. The serial log should
report both `NVMe Identify DMA passed` and `shared and private frame lifecycle
passed`. [GCE confidential VM configuration](https://docs.cloud.google.com/confidential-computing/confidential-vm/docs/create-a-confidential-vm-instance)

## x86 virtualization

FL4 exposes the seL4 VCPU/EPT API and the l4h extensions from patches
0038–0043. One image selects Intel VT-x or AMD-V at boot. On unsupported
CPUs, firmware-disabled virtualization, missing mitigation microcode or
capabilities, or the SKIM path on the boot processor, native boot continues
and retyping VCPU/EPT objects returns `seL4_InvalidArgument` for the type.
Incompatible enabled application processors or their startup timeouts halt boot
before userspace starts; an already-selected backend is not downgraded during
AP startup. Disabled CPU hotplug slots are not started.
`KernelVTX` and `KernelX86_64VTX64BitGuests` are always enabled in the ABI.

Use `seL4_X86_ASIDPool_Assign` for an EPT root and
`seL4_TCB_SetEPTRoot`/`seL4_X86_VCPU_SetTCB` to bind it to a thread.
`seL4_VMEnter` and the MR layout in `sel4/arch/vmenter.h` are shared by
both backends. Intel uses `ReadVMCS`/`WriteVMCS`; AMD uses
`ReadVMCB`/`WriteVMCB`, with byte offsets from the AMD VMCB layout.
The other backend's field operations return `seL4_IllegalOperation`.
VCPU objects occupy 32 KiB (`seL4_VCPUBits = 15`).

Each core retains a VMCS and uses `VMRESUME` after its first successful
launch. A field cache follows both software writes and guest changes read
on exit, so entries write only changed VMCS fields. The VCPU's software
image remains complete before remote operations or migration; the hardware
VMCS stays on its core. EPT translations survive entries. Nested unmaps and
root/ASID-pool deletion synchronously invalidate every core recorded in
the root before memory can be reused. Recording a core already present in
the root's lifetime bitmap does not write the hardware page table again.
VMX uses no VPID. SVM retains ASID 1 only for the last VCPU/root on each
core. VCPU switches, migration, retype, failed entry, nested invalidation,
explicit TLB flushes and software paging writes force a flush before reuse.
Guest-linear translations can survive SVM entries. A VMM that edits guest
page tables or emulates translation-invalidating operations (such as INVLPG,
INVPCID or a task switch) must call `seL4_X86_VCPU_FlushTLB` before reentry,
unless a software paging-register write already requested the flush.
VMCB clean bits track both software writes and hardware's exit state.
The host VMLOAD image is refreshed when FS/GS selectors or bases change
(on every entry with the dangerous-MSR API); AMD entry avoids VMX-only
MSR and descriptor-table work. Guest FPU state is the bound TCB's;
XCR0, CR2, syscall MSRs, descriptor-table limits, and host state are
restored on successful and failed entries.

VT-x supports Intel CPUs reporting `RDCL_NO` (hardware Meltdown immunity);
AMD-V supports Zen 2 and newer. Required security microcode must be installed
by firmware. Enhanced/Automatic IBRS are used when present; older supported
CPUs use software return-stack protection. IBPB runs on kernel entry and VM
exit, including the return to the userspace VMM. Intel additionally uses
legacy IBRS, PBRSB, and BHI protection where needed. Memory-form VERW clears
CPU buffers before guest/user entry and idle on affected CPUs. SMT siblings
are parked on SRSO-affected AMD and MDS/MMIO-affected Intel CPUs; STIBP is
enabled when supported. Missing required protections disable virtualization
on the boot processor with a diagnostic. Nested hosts must expose mitigation
capabilities accurately. See [the security policy](docs/virtualization-security.md) for
firmware checks, SMT restrictions, and validation limits.

The requirements are checked on each core. VMX event and instruction metadata
is copied only where architecturally defined; invalid vector/error fields
and undefined instruction bits are zeroed before reaching the VMM.

Virtualization regression tests run real guests and cover field restrictions,
CPUID/HLT exits, repeated entry, failed entry, GPRs, notifications,
replacement of cached nested mappings, explicit guest TLB invalidation,
same-value CR3 writes, cross-core rebinding, migration,
revocation, and deletion of a running VCPU:

```
cargo test -p fl4-core -p fl4-arch-x86_64
FL4_EXPECT_VM=present FL4_TESTS='^FL4VCPU' cargo xtask fl4test --smp 4 --setup kvm
FL4_EXPECT_VM=absent FL4_TESTS='^FL4VCPU' cargo xtask fl4test --smp 2 --setup kvm-no-vm
FL4_EXPECT_VM=present FL4_TESTS='^FL4VCPU' cargo xtask fl4test --smp 2 --setup kvm-no-ibrs
FL4_EXPECT_VM=absent FL4_TESTS='^FL4VCPU' cargo xtask fl4test --smp 2 --setup kvm-no-ibpb
FL4_EXPECT_VM=absent FL4_TESTS='^FL4VCPU' cargo xtask fl4test --smp 2 --setup kvm-no-rdcl
FL4_EXPECT_VM=present FL4_TESTS='^FL4VCPU' cargo xtask fl4test --smp 1 --setup kvm-no-pmu
FL4_P0_STRICT=1 cargo xtask gate
```

P0 checks totality for every extracted core function. For guest memory,
`guest_pte_roundtrip` proves that constructing a 4 KiB, 2 MiB or 1 GiB
leaf, extracting its address and removing the visibility bits recovers the
frame's aligned GPA. The store laws admit private and shared address masks.
The native l4v page and untyped refinements assume plain frame addresses.
The l4v semantic scope excludes SEV memory sharing, VMEnter, SetEPTRoot, EPT
mapping, guest-root ASID assignment, and VCPU/EPT refinement. The entry/exit
assembly and architecture backend are trusted. See [DESIGN.md §9](DESIGN.md#9-proof-plan) for the exact claims.

Real-guest execution passes on AMD-V under QEMU/KVM, including SMP,
release, reduced-feature and no-PMU configurations. The retained Intel
VMCS path has stateful host tests and a two-core Bochs 3.0 VMX run covering
repeated and failed entry, mapping replacement, migration, revocation and
deletion. That emulator run enabled guest IF for the timer and loop tests:
the IF-clear timer test also hangs with the original backend in Bochs.
The RSB/PBRSB/BHB sequences have a host assembly regression checking register
and stack restoration and a linked-kernel instruction-order check. The Bochs
run predates the current mitigation policy. The available AMD runner lacks
TSA microcode: positive guest tests use an explicitly labelled QEMU
`VERW_CLEAR` capability fixture, while the unmodified capability set correctly
disables virtualization. These runs validate control flow, not hardware TSA
protection. See the security policy for reproduction commands.
Intel hardware validation of the retained VMCS path remains outstanding.
VMX performance-MSR switching is enabled only when CPUID exposes a suitable
PMU; a PMU-present Intel hardware runtime has not been tested.
