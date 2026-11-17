# Virtualization CPU and mitigation policy

The supported baseline is Intel CPUs reporting `IA32_ARCH_CAPABILITIES.RDCL_NO`
(hardware Meltdown immunity) and AMD Zen 2 or newer, with VT-x/EPT or SVM/NPT
enabled and the required firmware security updates installed. Marketing
generation names are insufficient: some CPUs released after Skylake still
need Meltdown mitigation. The existing SKIM exclusion remains in place.

The selector in `spec/policy.rs` is pure and tested against capability and
firmware combinations. Every logical CPU is probed before VM initialization.
Missing requirements leave VCPU/EPT allocation unavailable and produce a boot
diagnostic. Native-only boot still applies available mitigations and reports
the incomplete protection. FL4 does not install firmware/microcode updates.

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
  expose it as well.
* AMD uses IBPB plus 32 nonzero-displacement CALLs where IBPB does not clear
  return predictions; VM exit omits the CALLs when AutoIBRS provides return
  protection. AutoIBRS remains enabled when available, but does not
  replace the IBPB needed for SRSO/VMSCAPE. An AMD bare-metal boot explicitly
  makes LFENCE dispatch-serializing; nested AMD requires the corresponding
  CPUID capability.
* Intel BHI protection uses BHI_DIS_S when available, otherwise the vendor's
  long BHB-clearing sequence. IBHF follows the sequence for virtualized hosts
  and is also used with BHI_DIS_S. Return protection precedes the BHB routine's
  balanced CALL/RET sequence.

Mitigation flags are selected by trusted code. Conditional assembly guards end
at LFENCE so a mispredicted guard cannot bypass protection and reach a host
return. Guest GPRs are saved before scratch-register use and cleared before
restoring the host. SVM keeps GIF clear through host VMLOAD and the barriers.

The initial implementation deliberately issues IBPB on every native entry and
VM exit. This has a measurable cost, including on newer CPUs. Avoiding redundant
barriers or introducing compiler-wide return thunks is a separate optimization;
the existing VMCS/VMCB field and translation caches remain in use.

## Firmware and data sampling

* Bare-metal Intel parts affected by ITS need a verified model/stepping-specific
  revision from Intel's IPU 2025.1 release or newer. An unknown affected patch
  stream is rejected; a revision from another stepping is never substituted.
  This requirement matters to the documented IBPB semantics even when eIBRS
  guest/host isolation is unaffected. Nested Intel relies on L0 implementing
  the advertised IBPB contract: a guest BIOS-signature MSR is not a physical
  host firmware revision.
* Zen 2's IBPB intrinsically has the branch-type behavior needed for SRSO.
  The bare-metal Zen 2 path also applies the Zenbleed software workaround
  unless the model/stepping has a known fixed microcode revision.
* Bare-metal family 19h uses AMD's published model/stepping revision table for
  TSA. These revisions also include the SRSO branch-type fixes. Newer AMD CPUs
  use the explicit capability bits. Nested AMD must expose IBPB_BRTYPE or
  SRSO_NO and VERW_CLEAR or all applicable TSA immunity bits; masked family
  names and synthetic guest patch revisions cannot establish protection.
* Memory-form VERW with a writable host data selector runs immediately before
  VMLAUNCH/VMRESUME/VMRUN, IRET/SYSRET and idle on affected processors. This
  covers Intel MDS/MMIO/RFDS and AMD TSA when the required microcode is present.
  Intel TAA is handled by disabling TSX where its control MSR is available.
  Enumerated FB_CLEAR_DIS/GDS_MITG_DIS controls are cleared, preserving other
  firmware bits. The support contract still requires current vendor security
  firmware for hardware issues outside these enumerated software mechanisms.

## SMT and heterogeneous systems

SRSO-affected AMD and MDS/MMIO-affected Intel use one logical processor per
physical core. STIBP is enabled when available; an otherwise eligible CPU
without adequate cross-thread branch protection also uses one thread per core.
Unknown topology under this restriction uses only the boot processor. The BSP
is retained even if firmware started it on a secondary thread.

Native entry barriers use the union of admitted CPUs' actions, frozen before
userspace starts; VM exits use the local CPU's plan. All admitted CPUs must
support the common vendor/IBPB operations. An AP requiring stricter SMT
isolation than the BSP is rejected before userspace can run. Existing VMX
capability compatibility checks also apply to VCPU migration.

Nested FL4 cannot police the physical host's SMT scheduling or install L0's
firmware. L0 must supply the hardware isolation and truthful mitigation
capabilities. General native user-to-user side-channel isolation remains
outside FL4's contract; guest-to-kernel and guest-to-VMM prediction boundaries
are explicitly covered by this change.

## Validation

The unit matrix covers RDCL_NO independently of eIBRS, Zen 2/3/4/newer paths,
microcode revision boundaries, nested feature masking, buffer clearing, and
SMT admission. Host assembly tests execute the actual VMX software exit
sequences and verify guest GPR/host-stack preservation. The linked-image check
verifies barriers, fenced conditional skips, CALL traps, return ordering,
memory-form VERW and SVM GIF ordering:

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
an explicit warning. It does not update firmware or establish that VERW clears
the physical buffers. Never use it with untrusted guests or sensitive data.
Passing these tests validates instruction/control flow, including repeated
and failed entries, protected-MSR interception, notifications, invalidations
and migration. It is not
hardware proof of speculative-execution isolation. Real Intel, Zen 2/3, and
updated-firmware TSA hardware validation remain necessary for that claim.

The same fixture can exercise SMT admission with
`FL4_QEMU_ARGS='-smp 4,sockets=1,cores=2,threads=2'`: an affected AMD CPU must
report two cores running. The repeated-CPUID guest loop reports TSC ticks per
entry over 512 iterations, including VMM checks, for comparing mitigation paths.

## Primary references

* [Intel architectural speculation capabilities](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/technical-documentation/cpuid-enumeration-and-architectural-msrs.html)
* [Intel legacy and enhanced IBRS](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/technical-documentation/indirect-branch-restricted-speculation.html)
* [Intel PBRSB](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/advisory-guidance/post-barrier-return-stack-buffer-predictions.html)
* [Intel BHI and IBHF](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/technical-documentation/branch-history-injection.html)
* [Intel ITS guidance](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/advisory-guidance/indirect-target-selection.html) and [IPU 2025.1 revisions](https://github.com/intel/Intel-Linux-Processor-Microcode-Data-Files/blob/microcode-20250512/releasenote.md)
* [AMD SRSO capabilities and IBPB behavior](https://www.amd.com/content/dam/amd/en/documents/corporate/cr/speculative-return-stack-overflow-whitepaper.pdf)
* [AMD TSA guidance and microcode table, rev. 3.0](https://www.amd.com/content/dam/amd/en/documents/resources/bulletin/technical-guidance-for-mitigating-transient-scheduler-attacks.pdf)
* [Linux RSB mitigation rationale](https://docs.kernel.org/admin-guide/hw-vuln/rsb.html) and [VMSCAPE boundary/SMT requirements](https://docs.kernel.org/admin-guide/hw-vuln/vmscape.html)
