# Virtualization CPU and mitigation policy

The supported baseline is Intel CPUs reporting `IA32_ARCH_CAPABILITIES.RDCL_NO`
(hardware Meltdown immunity) and AMD Zen 2 or newer, with VT-x/EPT or SVM/NPT
enabled and the required firmware security updates installed. Marketing
generation names are insufficient: some CPUs released after Skylake still
need Meltdown mitigation. The existing SKIM exclusion remains in place.

The selector in `spec/policy.rs` is pure and tested against capability and
firmware combinations. Every logical CPU is probed before VM initialization.
Missing requirements on the boot processor leave VCPU/EPT allocation unavailable
and produce a boot diagnostic. Native-only boot still applies available
mitigations (the native entry barriers, STIBP, BHI controls and TSX disabling
`select` would choose, as far as the CPU provides them) and reports the
incomplete protection. Incompatible AP capabilities
or an enabled AP's startup timeout halt boot before userspace; see the SMP policy
below. FL4 does not install firmware/microcode updates.

## Predictor boundaries

* Native syscall, interrupt, exception and NMI entry run the selected assembly
  barriers before calling Rust. There is no GS/per-CPU lookup before protection.
* Every VM exit, including failed entry, issues IBPB before the first host return
  or interrupt enable. This also protects the userspace VMM without requiring
  a context switch. The guest cannot write the host's speculation-control MSRs.
* Intel eIBRS stays enabled. Without eIBRS, legacy IBRS is reasserted with a
  fresh WRMSR at each boundary, even if already set, and VM exit fills the RSB.
  Affected eIBRS CPUs use the PBRSB CALL/stack-adjust/LFENCE sequence.
  Intel also requires SMEP for native return protection; nested hosts must
  expose it as well. With eIBRS and SMEP, native entries skip IBPB, as Linux
  does: eIBRS keeps user-mode training out of supervisor indirect and
  alternate return predictions, and SMEP keeps supervisor returns off the
  user-mode targets of user RSB entries. ITS-affected parts keep it: ITS_NO
  or BHI_CTRL (which no affected part has) rule ITS out, and otherwise the
  model, on bare metal only, since a hypervisor may report a compatibility
  model of an affected host (as Linux's `vulnerable_to_its`). VM exits keep IBPB. On GCE N4 the entry IBPB was half of a guest
  syscall round trip (1.97 to 1.00 us).
* On AMD family 19h CPUs (Zen 3/4) with SMEP and STIBP, native entries use
  the Zen 3/4 Safe RET thunk for returns, and AutoIBRS (Zen 4) or, without
  it (Zen 3), retpolines for indirect calls and jumps: Linux's choice on
  Zen 3 (Spectre v2: Retpolines; SRSO: Safe RET). On GCE N2D (Milan) the
  IBPB it replaces cost about 2.4 us per guest syscall round trip, most of
  it in the cold predictors it leaves. Bare metal makes LFENCE
  dispatch-serializing itself; a guest relies on its hypervisor for it, as
  its native-only entry guards already do. Native-only boots rejected for
  VM support alone (buffer-clearing capability, nested LFENCE, SRSO
  microcode) still use Safe RET, and keep SMT siblings with STIBP, as
  Linux does there (under SEV-SNP the STIBP write goes through the GHCB, so
  it is the hypervisor's to honour). Otherwise, AMD CPUs with AutoIBRS and
  SMEP that report SRSO_NO or SRSO_USER_KERNEL_NO (no SRSO across the
  user/kernel boundary) skip the native entry IBPB.
  Other native AMD entries retain IBPB
  plus 32 nonzero-displacement CALLs where IBPB leaves return predictions
  live. Every AMD VM exit retains IBPB and omits the CALLs when AutoIBRS
  provides return protection. An AMD bare-metal boot explicitly makes
  LFENCE dispatch-serializing. Nested AMD requires the corresponding CPUID
  capability.
* Intel BHI protection uses BHI_DIS_S when available, otherwise the vendor's
  long BHB-clearing sequence. IBHF follows the sequence for virtualized hosts
  and is also used with BHI_DIS_S. Return protection precedes the BHB routine's
  balanced CALL/RET sequence.

Mitigation flags are selected by trusted code. Conditional assembly guards end
at LFENCE so a mispredicted guard cannot bypass protection and reach a host
return. Guest GPRs are saved before scratch-register use and cleared before
restoring the host. SVM keeps GIF clear through host VMLOAD and the barriers.

For Safe RET, native entry untrains the single return thunk before calling
Rust. The linker checks the Zen 3/4 BTB alias addresses. If an interrupt
lands between the thunk's CALL and RET, entry completes the interrupted
return in the hardware frame before resuming it. This follows the
[Linux Safe RET design](https://docs.kernel.org/admin-guide/hw-vuln/srso.html)
and its [interrupt recovery](https://www.amd.com/en/resources/product-security/bulletin/amd-sb-7061.html).

The x86 kernel builds its Rust libraries from source with external return
thunks and external retpoline thunks (`-Zretpoline-external-thunk`: every
indirect call and jump goes through `__x86_indirect_thunk_r11`, and no
jump tables are emitted), using the Rust toolchain's `rust-src` component.
The indirect thunk starts as `JMP *%r11`; boots that use Safe RET without
AutoIBRS change it into a short jump to the retpoline with the return
thunk patch. The linked-image check rejects any other indirect branch
outside the identity-mapped boot code.
The linked-image check rejects unexpected plain returns. The image starts
with a plain RET followed by INT3 in the thunk. On eligible boots the
boot core changes the RET opcode into a short jump, using the INT3 byte
as its displacement. Each core serializes instruction fetch before the
Safe RET native entry policy is published and APs are released. Fallback
boots keep the plain return and the boot-selected native entry barriers.

Under Safe RET every Rust return mispredicts: the thunk's CALL leaves the
return-stack prediction pointing at its own UD2. A syscall fault and its
reply used to execute about 65 returns, a quarter of the round trip. The
functions on that path (entry and exit, the serial gate, syscall dispatch,
IPC, fault delivery and reply, scheduling and the address-space switch) are
therefore `#[inline(always)]`. The larger ones with many callers
(`schedule`, `handle_fault`, `decode_invocation`) stay out of line: inlining
them grows the image more than it saves.

## Firmware and data sampling

* Bare-metal Intel parts affected by ITS need a verified model/stepping-specific
  revision from Intel's IPU 2025.1 release or newer. An unknown affected patch
  stream is rejected; a revision from another stepping is never substituted.
  This requirement matters to the documented IBPB semantics even when eIBRS
  guest/host isolation is unaffected. Nested Intel relies on L0 implementing
  the advertised IBPB contract: a guest BIOS-signature MSR is not a physical
  host firmware revision.
* Outside SEV/SEV-SNP the hypervisor is trusted: on Intel, MMIO stale data
  and RFDS are judged by the reported model, as on bare metal, when the
  immunity bits are missing (GCE N4 reports no RFDS_NO although RFDS affects
  Atom cores only). RFDS_CLEAR without RFDS_NO still selects VERW on any
  model: it is how a VMM asks for it. The MMIO list includes the
  pre-RDCL_NO models a compatibility CPUID could present.
* Zen 2's IBPB intrinsically has the branch-type behavior needed for SRSO.
  The bare-metal Zen 2 path also applies the Zenbleed software workaround
  unless the model/stepping has a known fixed microcode revision.
* Bare-metal family 19h uses AMD's published model/stepping revision table for
  TSA. These revisions also include the SRSO branch-type fixes. Newer AMD CPUs
  use the explicit capability bits. Nested AMD must expose IBPB_BRTYPE or
  SRSO_NO and VERW_CLEAR or all applicable TSA immunity bits; masked family
  names and synthetic guest patch revisions cannot establish protection.
  AMD's November 2026 revision adds affected family 1Ah products and defines
  ECX[7] as TSA_FILL_NO. Updated affected Zen 5 CPUs enumerate VERW_CLEAR in
  hardware; a family-wide Zen 5 exemption would admit vulnerable machines.
  TSA_SQ_NO and TSA_L1_NO alone do not establish TSA-FILL immunity.
* Memory-form VERW with a writable host data selector runs immediately before
  VMLAUNCH/VMRESUME/VMRUN, IRET/SYSRET and idle on affected processors. This
  covers Intel MDS/MMIO/RFDS and AMD TSA when the required microcode is present.
  Intel TAA is handled by disabling TSX where its control MSR is available.
  Enumerated FB_CLEAR_DIS/GDS_MITG_DIS controls are cleared, preserving other
  firmware bits. The support contract still requires current vendor security
  firmware for hardware issues outside these enumerated software mechanisms.
  Intel's implicit fill-buffer-clearing rule requires MDS_NO=0 along with
  MD_CLEAR and FLUSH_L1D; MDS_NO CPUs need explicit FB_CLEAR for MMIO mitigation.

## SMT and heterogeneous systems

Only MADT processors with the Enabled flag set are candidates for startup, for
both local APIC and x2APIC records. Online Capable alone describes a CPU that
can be enabled during OS runtime, not one ready for boot ([ACPI local APIC
flags](https://uefi.org/specs/ACPI/6.6/05_ACPI_Software_Programming_Model.html#processor-local-apic-structure)).
FL4 does not support CPU hotplug; these disabled slots are ignored and do not
consume the boot CPU limit or trigger startup timeouts.

With a VM-capable plan, SRSO-affected AMD and MDS/MMIO-affected Intel use
one logical processor per physical core; native-only boots, Safe RET
included, keep SMT siblings with STIBP (Predictor boundaries above). STIBP is enabled when available; an otherwise eligible CPU
without adequate cross-thread branch protection also uses one thread per core.
Unknown topology under this restriction uses only the boot processor. The BSP
is retained even if firmware started it on a secondary thread.
The SRSO_NO requirement for retaining AMD SMT is deliberately conservative,
including on newer CPUs; model-specific relaxations need separate validation.

Skipped siblings remain in firmware's wait-for-SIPI state. FL4 currently does
not enable CR4.MCE. Future machine-check support must initialize every sibling
at least once before parking it, so a broadcast machine check does not encounter
a sibling with CR4.MCE=0 and shut down the machine (as documented in
[Linux's CPU bring-up code](https://github.com/torvalds/linux/blob/master/kernel/cpu.c)).

Native entry uses Safe RET only if every admitted CPU supports it. Otherwise
it uses the union of admitted CPUs' entry barriers. The native policy is frozen
before userspace starts. VM exits use the local CPU's plan. All admitted CPUs must
support the common vendor/IBPB operations. An AP requiring stricter SMT
isolation than the BSP, failing the local mitigation policy, or lacking the
selected VM backend reports rejection to the BSP and halts. The BSP then halts
with a diagnostic; other started APs remain behind the boot barrier. Startup
timeouts for enabled APs also halt the BSP, preventing a late AP from racing
userspace or reuse of its per-core storage. This deliberately stops boot while
VMX/SVM may already be active on other cores. Existing VMX capability
compatibility checks also apply to VCPU migration.

Nested FL4 cannot police the physical host's SMT scheduling or install L0's
firmware. L0 must supply the hardware isolation and truthful mitigation
capabilities. General native user-to-user side-channel isolation remains
outside FL4's contract; guest-to-kernel and guest-to-VMM prediction boundaries
are explicitly covered by this change.

## Validation

Host tests execute the kernel's ACPI parser against LAPIC/x2APIC tables with
disabled and online-capable slots, including enough slots to fill the CPU array
if mistakenly admitted. Enabled CPU IDs and IOAPIC discovery must be preserved.

The unit matrix covers RDCL_NO independently of eIBRS, Zen 2/3/4/newer paths,
microcode revision boundaries, nested feature masking, buffer clearing, and
SMT admission. Host assembly tests execute the actual VMX software exit
sequences and verify guest GPR/host-stack preservation. Safe RET tests check
that interruption at either instruction produces the correct saved RIP and
RSP. The linked-image check verifies return thunk coverage, BTB aliasing,
barriers, fenced conditional skips, CALL traps, return ordering, memory-form
VERW and SVM GIF ordering:

```sh
cargo test -p fl4-arch-x86_64 -p fl4-core -p xtask
cargo xtask kernel
python3 xtask/scripts/check_vm_asm.py build/kernel.elf
FL4_EXPECT_VM=present FL4_TESTS='^FL4VCPU' cargo xtask fl4test --setup kvm-no-ibrs --smp 4
FL4_EXPECT_VM=absent FL4_TESTS='^FL4VCPU' cargo xtask fl4test --setup kvm-no-ibpb --smp 2
FL4_EXPECT_VM=absent FL4_TESTS='^FL4VCPU' cargo xtask fl4test --setup kvm-no-rdcl --smp 2
```

`FL4_EXPECT_VM=present` makes an unavailable backend or skipped guest execution
a failure, rather than counting a runtime-probe skip as successful execution.

The development runner is a Ryzen 7 7700 with microcode `0x0a601209`, below
AMD's TSA minimum `0x0a60120a`; Linux reports TSA protection incomplete. FL4
correctly rejects its unmodified nested capability set. For functional CI
only, an opt-in QEMU ioctl fixture advertises VERW_CLEAR:

```sh
FL4_TEST_VERW_FIXTURE=1 FL4_EXPECT_VM=present FL4_TESTS='^FL4VCPU' \
  cargo xtask fl4test --setup kvm-no-ibrs --smp 4
```

The fixture is outside the kernel, changes only test QEMU's CPUID, and emits
an explicit warning. Its temporary library is removed after QEMU exits, including
test failures and timeouts. It does not update firmware or establish that VERW
clears the physical buffers. Never use it with untrusted guests or sensitive data.
Passing these tests validates instruction/control flow, including repeated
and failed entries, protected-MSR interception, notifications, invalidations
and migration. It is not
hardware proof of speculative-execution isolation. Real Intel, Zen 2/3, and
updated-firmware TSA hardware validation remain necessary for that claim.

The same fixture can exercise SMT admission with
`FL4_QEMU_ARGS='-smp 4,sockets=1,cores=2,threads=2'`: an affected AMD CPU must
report two cores running. The repeated-CPUID guest loop reports TSC ticks per
entry over 512 iterations, including VMM checks, for comparing mitigation paths.

The AMD fixture can also remove IBPB or LFENCE serialization on AP 1, or make
that AP require stricter SMT isolation than the BSP. Each run must observe the
BSP's rejection diagnostic and stop before the root task starts:

```sh
for fault in ibpb lfence smt; do
  FL4_TEST_VERW_FIXTURE=1 FL4_TEST_AP_REJECT=$fault \
    FL4_EXPECT_VM=ap-rejected FL4_TESTS='^FL4VCPU' \
    cargo xtask fl4test --setup kvm --smp 4
done
```

## Primary references

* [Intel architectural speculation capabilities](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/technical-documentation/cpuid-enumeration-and-architectural-msrs.html)
* [Intel legacy and enhanced IBRS](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/technical-documentation/indirect-branch-restricted-speculation.html)
* [Intel PBRSB](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/advisory-guidance/post-barrier-return-stack-buffer-predictions.html)
* [Intel BHI and IBHF](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/technical-documentation/branch-history-injection.html)
* [Intel ITS guidance](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/advisory-guidance/indirect-target-selection.html) and [IPU 2025.1 revisions](https://github.com/intel/Intel-Linux-Processor-Microcode-Data-Files/blob/microcode-20250512/releasenote.md)
* [Intel MMIO stale-data mitigation selection](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/technical-documentation/processor-mmio-stale-data-vulnerabilities.html)
* [AMD SRSO capabilities and IBPB behavior](https://www.amd.com/content/dam/amd/en/documents/corporate/cr/speculative-return-stack-overflow-whitepaper.pdf)
* [AMD TSA guidance and microcode table, rev. 3.0](https://www.amd.com/content/dam/amd/en/documents/resources/bulletin/technical-guidance-for-mitigating-transient-scheduler-attacks.pdf)
* [Linux RSB mitigation rationale](https://docs.kernel.org/admin-guide/hw-vuln/rsb.html) and [VMSCAPE boundary/SMT requirements](https://docs.kernel.org/admin-guide/hw-vuln/vmscape.html)
