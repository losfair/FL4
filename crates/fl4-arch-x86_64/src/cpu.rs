//! Instruction wrappers.
use core::arch::asm;

#[inline]
pub fn outb(port: u16, v: u8) {
    if crate::sev::snp::active() {
        crate::sev::snp::port(port, 1, false, u32::from(v));
        return;
    }
    unsafe { asm!("out dx, al", in("dx") port, in("al") v, options(nomem, nostack, preserves_flags)) }
}

#[inline]
pub fn inb(port: u16) -> u8 {
    if crate::sev::snp::active() {
        return crate::sev::snp::port(port, 1, true, 0) as u8;
    }
    let v: u8;
    unsafe { asm!("in al, dx", in("dx") port, out("al") v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn outw(port: u16, v: u16) {
    if crate::sev::snp::active() {
        crate::sev::snp::port(port, 2, false, u32::from(v));
        return;
    }
    unsafe { asm!("out dx, ax", in("dx") port, in("ax") v, options(nomem, nostack, preserves_flags)) }
}

#[inline]
pub fn inw(port: u16) -> u16 {
    if crate::sev::snp::active() {
        return crate::sev::snp::port(port, 2, true, 0) as u16;
    }
    let v: u16;
    unsafe { asm!("in ax, dx", in("dx") port, out("ax") v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn outl(port: u16, v: u32) {
    if crate::sev::snp::active() {
        crate::sev::snp::port(port, 4, false, u32::from(v));
        return;
    }
    unsafe { asm!("out dx, eax", in("dx") port, in("eax") v, options(nomem, nostack, preserves_flags)) }
}

#[inline]
pub fn inl(port: u16) -> u32 {
    if crate::sev::snp::active() {
        return crate::sev::snp::port(port, 4, true, 0) as u32;
    }
    let v: u32;
    unsafe { asm!("in eax, dx", in("dx") port, out("eax") v, options(nomem, nostack, preserves_flags)) }
    v
}

#[derive(Clone, Copy, Debug)]
pub struct Cpuid {
    pub eax: u32,
    pub ebx: u32,
    pub ecx: u32,
    pub edx: u32,
}

#[inline]
pub fn cpuid(leaf: u32, sub: u32) -> Cpuid {
    if let Some(r) = crate::sev::snp::cpuid(leaf, sub) { return r; }
    let r = core::arch::x86_64::__cpuid_count(leaf, sub);
    Cpuid { eax: r.eax, ebx: r.ebx, ecx: r.ecx, edx: r.edx }
}

/// Serialize instruction fetch after a code patch on a non-SNP CPU.
#[inline]
pub fn serialize_instructions() {
    // The assembly also acts as a compiler memory barrier. LLVM reserves
    // RBX, so save and restore it here.
    unsafe {
        asm!("push rbx", "cpuid", "pop rbx",
            inout("eax") 0u32 => _, inout("ecx") 0u32 => _, lateout("edx") _,
            options(preserves_flags));
    }
}

#[inline]
pub fn rdmsr(msr: u32) -> u64 {
    let (lo, hi): (u32, u32);
    unsafe { asm!("rdmsr", in("ecx") msr, out("eax") lo, out("edx") hi, options(nomem, nostack, preserves_flags)) }
    ((hi as u64) << 32) | lo as u64
}

/// Where the kernel image is linked: its first byte is at this virtual
/// address (fl4-kernel's linker script, fl4-efi's `KERNEL_OFFSET`).
pub const KERNEL_OFFSET: u64 = 0xffff_ffff_8000_0000;

/// How far above its linked physical address the loader put the image:
/// 0 for Multiboot, fl4-efi's 2 MiB aligned allocation otherwise. Set once, by the boot core, first.
static IMAGE_DELTA: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);

pub fn set_image_delta(delta: u64) {
    IMAGE_DELTA.store(delta, core::sync::atomic::Ordering::Relaxed);
}

pub fn image_delta() -> u64 {
    IMAGE_DELTA.load(core::sync::atomic::Ordering::Relaxed)
}

/// The physical address of `v`, an address in the kernel image's mapping
/// at `KERNEL_OFFSET`, for an image moved up by `delta`.
pub const fn image_paddr_at(v: u64, delta: u64) -> u64 {
    v.wrapping_sub(KERNEL_OFFSET).wrapping_add(delta)
}

/// The physical address of `v`, an address in the kernel image (its
/// code, statics and stacks). Hardware that is given one (VMXON, VMCS,
/// host-save and bitmap pages, paravirtual clock buffers, page tables)
/// must get it from here: the image is not at `v - KERNEL_OFFSET` when
/// a loader moved it.
pub fn image_paddr(v: u64) -> u64 {
    image_paddr_at(v, image_delta())
}

/// CR4.FSGSBASE is set: user code may change its FS and GS bases itself.
static FSGSBASE: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(false);

/// The processor's physical-address width (MAXPHYADDR) from the largest
/// extended CPUID leaf (`max_ext`, CPUID 80000000H:EAX) and, if leaf
/// 80000008H exists, its EAX: bits 7:0, held to 36..=52 (SDM Vol. 3
/// §4.1.4; a CPU without the leaf has 36). Paging entries with address
/// bits at or above it are reserved.
pub fn phys_addr_bits(max_ext: u32, leaf_8000_0008_eax: u32) -> u64 {
    if max_ext >= 0x8000_0008 {
        ((leaf_8000_0008_eax & 0xff) as u64).clamp(36, 52)
    } else {
        36
    }
}

/// The first physical address past MAXPHYADDR.
pub fn max_paddr() -> u64 {
    let max_ext = cpuid(0x8000_0000, 0).eax;
    let eax = if max_ext >= 0x8000_0008 { cpuid(0x8000_0008, 0).eax } else { 0 };
    1 << phys_addr_bits(max_ext, eax)
}

const CR4_VMXE: u64 = 1 << 13;
const CR4_FSGSBASE: u64 = 1 << 16;
const CR4_OSXSAVE: u64 = 1 << 18;
const CR4_SMEP: u64 = 1 << 20;
const CR4_SMAP: u64 = 1 << 21;

/// The boot core's CR4 as the other cores load it, before their own IDT
/// is in: without OSXSAVE and VMXE, which `fpu::init` and `vm::init` set
/// on each core once they have checked its XSAVE and VMX.
pub const fn ap_boot_cr4(cr4: u64) -> u64 {
    cr4 & !(CR4_OSXSAVE | CR4_VMXE)
}

/// Whether a core whose CPUID.(EAX=7,ECX=0):EBX is `leaf7_ebx` can load
/// `cr4`: setting FSGSBASE, SMEP or SMAP without its feature is #GP.
/// PCIDE is `tlb::core_supported`'s.
pub fn cr4_supported(cr4: u64, leaf7_ebx: u32) -> bool {
    [(CR4_FSGSBASE, 0), (CR4_SMEP, 7), (CR4_SMAP, 20)]
        .iter()
        .all(|&(bit, feature)| cr4 & bit == 0 || leaf7_ebx & (1 << feature) != 0)
}

/// The calling core can load `cr4` (`cr4_supported`).
pub fn core_cr4_supported(cr4: u64) -> bool {
    cr4_supported(cr4, if cpuid(0, 0).eax >= 7 { cpuid(7, 0).ebx } else { 0 })
}

pub fn has_fsgsbase() -> bool {
    cpuid(7, 0).ebx & 1 != 0
}

pub fn set_fsgsbase(on: bool) {
    FSGSBASE.store(on, core::sync::atomic::Ordering::Relaxed);
}

pub fn fsgsbase() -> bool {
    FSGSBASE.load(core::sync::atomic::Ordering::Relaxed)
}

/// The current FS base (RDFSBASE when enabled, else the MSR).
pub fn fs_base() -> u64 {
    if fsgsbase() {
        let v: u64;
        unsafe { asm!("rdfsbase {}", out(reg) v, options(nomem, nostack, preserves_flags)) }
        v
    } else {
        rdmsr(msr::FS_BASE)
    }
}

/// The current GS base. The kernel runs with the user's GS live.
pub fn gs_base() -> u64 {
    if fsgsbase() {
        let v: u64;
        unsafe { asm!("rdgsbase {}", out(reg) v, options(nomem, nostack, preserves_flags)) }
        v
    } else {
        rdmsr(msr::GS_BASE)
    }
}

pub fn set_fs_base(v: u64) {
    if fsgsbase() {
        unsafe { asm!("wrfsbase {}", in(reg) v, options(nomem, nostack, preserves_flags)) }
    } else {
        wrmsr(msr::FS_BASE, v)
    }
}

pub fn set_gs_base(v: u64) {
    if fsgsbase() {
        unsafe { asm!("wrgsbase {}", in(reg) v, options(nomem, nostack, preserves_flags)) }
    } else {
        wrmsr(msr::GS_BASE, v)
    }
}

#[inline]
pub fn wrmsr(msr: u32, v: u64) {
    unsafe {
        asm!("wrmsr", in("ecx") msr, in("eax") v as u32, in("edx") (v >> 32) as u32, options(nostack, preserves_flags))
    }
}

#[inline]
pub fn rdtsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

#[inline]
pub fn halt() {
    unsafe { asm!("hlt", options(nomem, nostack)) }
}

pub fn halt_forever() -> ! {
    loop {
        unsafe { asm!("cli; hlt", options(nomem, nostack)) }
    }
}

#[inline]
pub fn read_cr0() -> u64 {
    let v: u64;
    unsafe { asm!("mov {}, cr0", out(reg) v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn write_cr0(v: u64) {
    unsafe { asm!("mov cr0, {}", in(reg) v, options(nostack, preserves_flags)) }
}

#[inline]
pub fn read_cr2() -> u64 {
    let v: u64;
    unsafe { asm!("mov {}, cr2", out(reg) v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn read_cr3() -> u64 {
    let v: u64;
    unsafe { asm!("mov {}, cr3", out(reg) v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn write_cr3(v: u64) {
    unsafe { asm!("mov cr3, {}", in(reg) v, options(nostack, preserves_flags)) }
}

#[inline]
pub fn read_cr4() -> u64 {
    let v: u64;
    unsafe { asm!("mov {}, cr4", out(reg) v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn write_cr4(v: u64) {
    unsafe { asm!("mov cr4, {}", in(reg) v, options(nostack, preserves_flags)) }
}

#[inline]
pub fn invlpg(addr: u64) {
    unsafe { asm!("invlpg [{}]", in(reg) addr, options(nostack, preserves_flags)) }
}

#[inline]
pub fn xgetbv(reg: u32) -> u64 {
    let (lo, hi): (u32, u32);
    unsafe { asm!("xgetbv", in("ecx") reg, out("eax") lo, out("edx") hi, options(nomem, nostack, preserves_flags)) }
    ((hi as u64) << 32) | lo as u64
}

#[inline]
pub fn xsetbv(reg: u32, v: u64) {
    unsafe { asm!("xsetbv", in("ecx") reg, in("eax") v as u32, in("edx") (v >> 32) as u32, options(nostack, preserves_flags)) }
}

pub fn read_dr6() -> u64 {
    let v: u64;
    unsafe { asm!("mov {}, dr6", out(reg) v, options(nomem, nostack, preserves_flags)) }
    v
}

pub fn write_dr6(v: u64) {
    unsafe { asm!("mov dr6, {}", in(reg) v, options(nostack, preserves_flags)) }
}

pub fn write_dr7(v: u64) {
    unsafe { asm!("mov dr7, rax", in("rax") v, options(nostack, preserves_flags)) }
}

pub fn write_dr(i: u64, v: u64) {
    unsafe {
        match i {
            0 => asm!("mov dr0, {}", in(reg) v, options(nostack, preserves_flags)),
            1 => asm!("mov dr1, {}", in(reg) v, options(nostack, preserves_flags)),
            2 => asm!("mov dr2, {}", in(reg) v, options(nostack, preserves_flags)),
            _ => asm!("mov dr3, {}", in(reg) v, options(nostack, preserves_flags)),
        }
    }
}

/// IRET to the next instruction, at the same privilege level and stack:
/// ends NMI blocking without taking an interrupt.
#[inline]
pub fn iret_to_self() {
    unsafe {
        asm!(
            "mov {t:e}, ss",
            "push {t}",
            "lea {t}, [rsp + 8]",
            "push {t}",
            "pushfq",
            "mov {t:e}, cs",
            "push {t}",
            "lea {t}, [rip + 2f]",
            "push {t}",
            "iretq",
            "2:",
            t = out(reg) _,
        )
    }
}

#[inline]
pub fn enable_interrupts_briefly() {
    // Not `nomem`: interrupt handlers run here and touch kernel state.
    unsafe { asm!("sti", "nop", "nop", "cli", options(nostack)) }
}

pub mod msr {
    pub const APIC_BASE: u32 = 0x1b;
    pub const SYSENTER_CS: u32 = 0x174;
    pub const TSC_DEADLINE: u32 = 0x6e0;
    pub const PAT: u32 = 0x277;
    pub const EFER: u32 = 0xc000_0080;
    pub const STAR: u32 = 0xc000_0081;
    pub const LSTAR: u32 = 0xc000_0082;
    pub const CSTAR: u32 = 0xc000_0083;
    pub const FMASK: u32 = 0xc000_0084;
    pub const FS_BASE: u32 = 0xc000_0100;
    pub const GS_BASE: u32 = 0xc000_0101;
    pub const KERNEL_GS_BASE: u32 = 0xc000_0102;
    pub const XSS: u32 = 0xda0;
}

/// seL4's PAT palette, also used by AMD nested page-table entries:
/// WB, WT, UC-, UC, WC in indices 0..4. Configure before user mappings.
pub fn init_pat() {
    if cpuid(1, 0).edx & (1 << 16) != 0 {
        wrmsr(msr::PAT, (rdmsr(msr::PAT) & !0x0000_00ff_ffff_ffff) | 0x0000_0001_0007_0406);
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;

    #[test]
    fn physical_address_width_comes_from_leaf_8000_0008() {
        assert_eq!(phys_addr_bits(0x8000_0004, 0x3027), 36);
        assert_eq!(phys_addr_bits(0x8000_0008, 0x3027), 39);
        assert_eq!(phys_addr_bits(0x8000_0020, 0x3030), 48);
        assert_eq!(phys_addr_bits(0x8000_0008, 0x3020), 36);
        assert_eq!(phys_addr_bits(0x8000_0008, 0x00ff), 52);
        assert_eq!(phys_addr_bits(0x8000_0008, 0), 36);
    }

    #[test]
    fn image_addresses_follow_the_loader_delta() {
        assert_eq!(image_paddr_at(0xffff_ffff_8012_3000, 0), 0x12_3000);
        assert_eq!(image_paddr_at(0xffff_ffff_8012_3000, 0x3fe0_0000), 0x3ff2_3000);
    }

    #[test]
    fn iret_to_self_preserves_stack_and_flags() {
        let (rsp_before, flags_before, rsp_after, flags_after): (u64, u64, u64, u64);
        unsafe {
            asm!("mov {}, rsp", "pushfq", "pop {}", out(reg) rsp_before, out(reg) flags_before);
        }
        iret_to_self();
        unsafe {
            asm!("mov {}, rsp", "pushfq", "pop {}", out(reg) rsp_after, out(reg) flags_after);
        }
        assert_eq!(rsp_before, rsp_after);
        assert_eq!(flags_before & 0xcd5, flags_after & 0xcd5);
    }
}
