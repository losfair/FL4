//! Kernel side of the SEV-SNP UEFI handoff and #VC handling.
use crate::entry::Frame;
use fl4_arch_x86_64::{
    cpu,
    sev::{self, mmio, snp},
};
use fl4_core::layout::pptr;

pub fn init(cpuid: u64) {
    // The loader places a dedicated GHCB page after the CPUID copy.
    unsafe { snp::init(pptr(cpuid), cpuid + 4096) };
}

/// Only emulate kernel instructions that access virtual hardware, after
/// verifying the opcode. Never disclose operands of unrelated instructions
/// in response to a hypervisor-injected #VC.
pub fn vc(f: &mut Frame) {
    let (start, end) = crate::paging::text_bounds();
    if f.rip < start || f.rip >= end.saturating_sub(2) {
        snp::terminate(0);
    }
    let op = unsafe { (f.rip as *const [u8; 2]).read() };
    let msr = f.rcx as u32;
    if f.error == 0x37 && op == [0x0f, 0x23] && unsafe { ((f.rip + 2) as *const u8).read() } == 0xf8
    {
        snp::write_dr7(f.rax);
        f.rip += 3;
        return;
    }
    match (f.error, op) {
        (0x7c, [0x0f, 0x32]) if virtual_msr(msr) => {
            let value = snp::read_msr(msr);
            f.rax = value as u32 as u64;
            f.rdx = value >> 32;
        }
        (0x7c, [0x0f, 0x30]) if virtual_msr(msr) => {
            snp::write_msr(msr, (f.rdx << 32) | f.rax as u32 as u64);
        }
        (0x6e, [0x0f, 0x31]) => {
            let value = snp::rdtsc();
            f.rax = value as u32 as u64;
            f.rdx = value >> 32;
        }
        _ => {
            crate::kprintln!(
                "FL4: unsupported SNP #VC {:#x} at text offset {:#x}",
                f.error,
                f.rip - start
            );
            snp::terminate(0);
        }
    }
    f.rip += 2;
}

/// MSRs a #VC forwards to the hypervisor through the GHCB. SPEC_CTRL
/// (0x48): native-only boots set STIBP whenever it is advertised
/// (`spec::init_core`), and GCE's SEV-SNP hypervisor intercepts the MSR;
/// a hypervisor that ignores the write leaves STIBP to it, as it already
/// controls the sibling thread's scheduling.
fn virtual_msr(msr: u32) -> bool {
    matches!(
        msr,
        cpu::msr::APIC_BASE | cpu::msr::TSC_DEADLINE | 0x48 | 0x800..=0x83f
    )
}

use crate::snp_walk::Access;

/// Walk the active user tables through their private kernel aliases.
/// SNP's AMD CPUs run with the full kernel window in each user CR3.
fn translate(va: u64, access: Access) -> Option<u64> {
    crate::snp_walk::translate(
        va,
        access,
        cpu::read_cr3(),
        sev::mask(),
        fl4_abi::consts::USER_TOP,
        crate::paging::window_top(),
        |pa| unsafe { (pptr(pa) as *const u64).read_volatile() },
    )
}

fn user_next_rip(rip: u64, length: u64) -> Option<u64> {
    rip.checked_add(length)
        .filter(|&next| next <= fl4_abi::consts::USER_TOP)
}

pub fn user_vc(f: &mut Frame) -> bool {
    let fetch = |off| {
        let pa = translate(f.rip.checked_add(off)?, Access::Execute)?;
        Some(unsafe { (pptr(pa) as *const u8).read_volatile() })
    };
    if f.error == 0x72 && fetch(0) == Some(0x0f) && fetch(1) == Some(0xa2) {
        let Some(next) = user_next_rip(f.rip, 2) else {
            return false;
        };
        let result = cpu::cpuid(f.rax as u32, f.rcx as u32);
        f.rax = result.eax as u64;
        f.rbx = result.ebx as u64;
        f.rcx = result.ecx as u64;
        f.rdx = result.edx as u64;
        f.rip = next;
        return true;
    }
    if f.error == 0x6e
        && fetch(0) == Some(0x0f)
        && fetch(1) == Some(0x31)
        && cpu::read_cr4() & 4 == 0
    {
        let Some(next) = user_next_rip(f.rip, 2) else {
            return false;
        };
        let tsc = snp::rdtsc();
        f.rax = tsc as u32 as u64;
        f.rdx = tsc >> 32;
        f.rip = next;
        return true;
    }
    if f.error != 0x400 {
        return false;
    }

    let gprs = [
        &mut f.rax, &mut f.rcx, &mut f.rdx, &mut f.rbx, &mut f.rsp, &mut f.rbp, &mut f.rsi,
        &mut f.rdi, &mut f.r8, &mut f.r9, &mut f.r10, &mut f.r11, &mut f.r12, &mut f.r13,
        &mut f.r14, &mut f.r15,
    ];
    let values = core::array::from_fn(|i| *gprs[i]);
    let Some(access) = mmio::decode(f.rip, &values, fetch) else {
        return false;
    };
    let Some(next) = user_next_rip(f.rip, access.length) else {
        return false;
    };
    // Never let a single GHCB operation cross a page boundary. Consult
    // the guest's own mappings instead of any address supplied by the VMM.
    if (access.address & 4095) + access.bytes > 4096 {
        return false;
    }
    let mode = match access.op {
        mmio::Operation::Write(_) => Access::Write,
        mmio::Operation::Read { .. } => Access::Read,
    };
    let Some(pa) = translate(access.address, mode) else {
        return false;
    };
    let mask = u64::MAX >> (64 - 8 * access.bytes);
    match access.op {
        mmio::Operation::Write(value) => {
            snp::mmio(pa, access.bytes, Some(value & mask));
        }
        mmio::Operation::Read {
            register,
            shift,
            dest_bytes,
        } => {
            let value = snp::mmio(pa, access.bytes, None) & mask;
            *gprs[register] = if dest_bytes >= 4 {
                value
            } else {
                let dest_mask = u64::MAX >> (64 - 8 * dest_bytes);
                (values[register] & !(dest_mask << shift)) | (value << shift)
            };
        }
    }
    f.rip = next;
    true
}

#[repr(C, align(4096))]
struct Page([u8; 4096]);

// Place the VMSA in the second 4 KiB page of an 8 KiB slot. The RMP
// erratum for a large translation overlapping a VMSA requires the
// VMSA GPA to be off a 2 MiB or 1 GiB boundary.
#[repr(C, align(8192))]
struct ApMemory {
    ghcb: Page,
    vmsa: Page,
}

static mut APS: [ApMemory; fl4_arch_x86_64::percpu::MAX_CPUS - 1] = [const {
    ApMemory {
        ghcb: Page([0; 4096]),
        vmsa: Page([0; 4096]),
    }
};
    fl4_arch_x86_64::percpu::MAX_CPUS - 1];

fn ap_memory(cpu_index: usize) -> *mut ApMemory {
    assert!((1..fl4_arch_x86_64::percpu::MAX_CPUS).contains(&cpu_index));
    unsafe { core::ptr::addr_of_mut!(APS).cast::<ApMemory>().add(cpu_index - 1) }
}

/// Make an AP's GHCB page shared and build its VMPL0 VMSA directly in long
/// mode: the guest controls its initial entry point, stack and descriptor
/// tables without a SIPI. Every AP's page-state changes run before the
/// first AP starts (ap_order::bring_up), while only the boot core can hold
/// TLB entries for these pages; this core drops each alias it may hold.
pub fn prepare_ap(cpu_index: usize, stack: u64, entry: u64) {
    extern "C" {
        static fl4_efi_gdt: u8;
    }
    let ap = ap_memory(cpu_index);
    let ghcb = unsafe { core::ptr::addr_of_mut!((*ap).ghcb) as u64 };
    let vmsa = unsafe { &mut (*ap).vmsa.0 };
    let gpa = crate::paging::image_paddr(vmsa.as_ptr() as u64);
    // prepare_cpu invalidates the physical windows' aliases before and
    // after the state change; do the same for the image alias (private,
    // 4 KiB, global), which is never used for this page again.
    cpu::invlpg(ghcb);
    unsafe { snp::prepare_cpu(cpu_index, crate::paging::image_paddr(ghcb)) };
    cpu::invlpg(ghcb);

    let features = cpu::rdmsr(0xc001_0131) >> 2;
    let mut put = |off: usize, value: u64| vmsa[off..off + 8].copy_from_slice(&value.to_le_bytes());
    // Segment entries contain selector, attributes, limit and base.
    let segment = |selector, attrib: u64, limit: u64| selector | (attrib << 16) | (limit << 32);
    put(0x00, segment(0x18, 0xc93, u32::MAX as u64)); // ES
    put(0x10, segment(0x10, 0xa9b, u32::MAX as u64)); // CS
    put(0x20, segment(0x18, 0xc93, u32::MAX as u64)); // SS
    put(0x30, segment(0x18, 0xc93, u32::MAX as u64)); // DS
    put(0x60, segment(0, 0, 31)); // GDTR
    put(0x68, unsafe { &fl4_efi_gdt as *const u8 as u64 });
    put(0x70, segment(0, 0x82, 0xffff)); // LDTR
    put(0x80, segment(0, 0, crate::gdt::BOOT_IDT_LIMIT as u64)); // IDTR
    put(0x88, crate::gdt::boot_idt_base());
    put(0x90, segment(0, 0x8b, 0xffff)); // TR
    put(0xd0, cpu::rdmsr(cpu::msr::EFER) | (1 << 12));
    put(0x148, cpu::read_cr4() & !(1 << 18)); // AP enables OSXSAVE itself
    put(0x150, crate::paging::root_paddr());
    put(0x158, cpu::read_cr0() & !(1 << 3));
    put(0x160, 0x400); // DR7
    put(0x168, 0xffff_0ff0); // DR6
    put(0x170, 2); // RFLAGS, IF clear
    put(0x178, entry);
    put(0x1d8, stack - 8); // RSP, SysV call alignment
    put(0x268, cpu::rdmsr(cpu::msr::PAT));
    put(0x338, cpu_index as u64); // RDI
    put(0x3b0, features);
    put(0x3e8, 1); // XCR0
    put(0x408, 0x1f80); // MXCSR
    put(0x410, 0x037f); // FCW

    let addr = vmsa.as_ptr() as u64;
    let result: u64;
    unsafe {
        core::arch::asm!("rmpadjust", inlateout("rax") addr => result, in("rcx") 0u64,
            in("rdx") (1u64 | 1 << 16), options(nostack));
    }
    if result != 0 {
        crate::fail("SNP AP VMSA setup failed");
    }
    // Nothing writes the VMSA from here on; drop this core's writable
    // translations of it (the image and the private window).
    cpu::invlpg(addr);
    cpu::invlpg(pptr(gpa));
}

/// Start an AP whose memory `prepare_ap` set up. Changes no page state.
pub fn start_ap(cpu_index: usize, apic: u32) {
    let ap = ap_memory(cpu_index);
    let vmsa = unsafe { core::ptr::addr_of!((*ap).vmsa) as u64 };
    let features = cpu::rdmsr(0xc001_0131) >> 2;
    snp::start_cpu(apic, crate::paging::image_paddr(vmsa), features);
}
