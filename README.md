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

All kernel runs happen inside QEMU; FL4 is never booted on the host.

```
cargo xtask run [--setup kvm|kvm-reduced|tcg]   # boot the standalone kernel
cargo xtask sel4test [--release] [--smp N] [--setup ...]
cargo xtask extract                              # Charon + Aeneas -> proofs/Fl4Core
(cd proofs && lake build)                        # check the proofs
```

Host dependencies live in `$FL4_DEPS` (default `~/Projects/fl4-deps`):
`venv/` with `sel4-deps`, and an `aeneas/` checkout with Charon built.

## x86 virtualization

FL4 exposes the seL4 VCPU/EPT API and the l4h extensions from patches
0038–0043. One image selects Intel VT-x or AMD-V at boot. On unsupported
CPUs, firmware-disabled virtualization, or the SKIM path, boot continues
and retyping VCPU/EPT objects returns `seL4_InvalidArgument` for the type.
`KernelVTX` and `KernelX86_64VTX64BitGuests` are always enabled in the ABI.

Use `seL4_X86_ASIDPool_Assign` for an EPT root and
`seL4_TCB_SetEPTRoot`/`seL4_X86_VCPU_SetTCB` to bind it to a thread.
`seL4_VMEnter` and the MR layout in `sel4/arch/vmenter.h` are shared by
both backends. Intel uses `ReadVMCS`/`WriteVMCS`; AMD uses
`ReadVMCB`/`WriteVMCB`, with byte offsets from the AMD VMCB layout.
The other backend's field operations return `seL4_IllegalOperation`.
VCPU objects occupy 32 KiB (`seL4_VCPUBits = 15`).

The first implementation rebuilds a per-core VMCS on each entry, uses no
VMX VPID, and flushes SVM's ASID on every entry. This favors simple
ownership and migration over entry/exit performance. Nested unmaps and
root/ASID-pool deletion synchronously invalidate every core recorded in
the root before memory can be reused. Guest FPU state is the bound TCB's;
XCR0, CR2, syscall MSRs, descriptor-table limits, and host state are
restored on successful and failed entries.

Virtualization regression tests run real guests and cover field restrictions,
CPUID/HLT exits, GPRs, notifications, cross-core rebinding, migration,
revocation, and deletion of a running VCPU:

```
cargo test -p fl4-core
FL4_TESTS='^FL4VCPU' cargo xtask fl4test --smp 4 --setup kvm
FL4_TESTS='^FL4VCPU' cargo xtask fl4test --smp 2 --setup kvm-no-vm
FL4_TESTS='^FL4VCPU' cargo xtask fl4test --smp 1 --setup kvm-no-pmu
FL4_P0_STRICT=1 cargo xtask gate
```

The strict extraction/proof gate passes. The proof project builds with the
expanded capability and TCB layouts,
VM thread state, and mixed native/nested ASID pools. All 1,041 extracted
core functions have checked totality proofs with zero `sorry`s. Existing
P1/P3 native proofs are ported; VMEnter, SetEPTRoot, EPT mapping, guest-root
ASID assignment, and VCPU/EPT functional refinement remain outside their
semantic scope. The entry/exit assembly and architecture backend remain
trusted. See [DESIGN.md §9](DESIGN.md#9-proof-plan) for the exact claims.

Real-guest execution passes on AMD-V under QEMU/KVM and on Intel VT-x
through Hyper-V/KVM, including SMP, release, reduced-feature and no-PMU
configurations. VMX performance-MSR switching is enabled only when CPUID
exposes a suitable PMU; a PMU-present Intel runtime has not been tested.
