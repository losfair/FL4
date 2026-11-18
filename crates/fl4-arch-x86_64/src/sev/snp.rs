//! SNP's validated CPUID table, RMP transitions and GHCB v2 (AMD 56421).
use crate::cpu::{self, Cpuid};
use crate::percpu::{self, MAX_CPUS};
use core::arch::asm;
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

const GHCB_MSR: u32 = 0xc001_0130;
const PAGE: u64 = 4096;
const RAX: usize = 0x1f8;
const RCX: usize = 0x308;
const RDX: usize = 0x310;
const EXIT_CODE: usize = 0x390;
const EXIT_INFO1: usize = 0x398;
const EXIT_INFO2: usize = 0x3a0;
const SCRATCH: usize = 0x3a8;
const SHARED_BUFFER: u64 = 0x800;
const VALID: usize = 0x3f0;
const VERSION: usize = 0xffa;

// Also read by the assembly entry path to identify an SNP guest.
#[no_mangle]
#[cfg_attr(target_os = "none", link_section = ".bss.skim")]
static FL4_SNP_CPUID_PAGE: AtomicU64 = AtomicU64::new(0);
static FEATURES: AtomicU64 = AtomicU64::new(0);
// Read by the entry and return stubs, including on skim page tables.
#[no_mangle]
#[cfg_attr(target_os = "none", link_section = ".bss.skim")]
static FL4_SNP_POISONED: AtomicBool = AtomicBool::new(false);

#[inline]
pub fn halt_if_poisoned() {
    if FL4_SNP_POISONED.load(Ordering::Acquire) {
        cpu::halt_forever();
    }
}

struct Channel {
    gpa: AtomicU64,
    in_use: AtomicBool,
}

static CHANNELS: [Channel; MAX_CPUS] = [const {
    Channel {
        gpa: AtomicU64::new(0),
        in_use: AtomicBool::new(false),
    }
}; MAX_CPUS];

#[repr(C)]
struct Leaf {
    function: u32,
    subfunction: u32,
    xcr0: u64,
    xss: u64,
    eax: u32,
    ebx: u32,
    ecx: u32,
    edx: u32,
    reserved: u64,
}

#[repr(C)]
struct CpuidPage {
    count: u32,
    reserved: [u32; 3],
    leaves: [Leaf; 64],
}

pub fn active() -> bool {
    FL4_SNP_CPUID_PAGE.load(Ordering::Relaxed) != 0
}

fn vmgexit() {
    unsafe { asm!("rep vmmcall", options(nostack, preserves_flags)) };
}

fn msr_request(request: u64) -> u64 {
    cpu::wrmsr(GHCB_MSR, request);
    vmgexit();
    cpu::rdmsr(GHCB_MSR)
}

pub fn terminate(reason: u8) -> ! {
    // Standard delivery allows a hostile host to ignore the exit. Every
    // CPU checks this flag at kernel entry and before leaving the kernel.
    if FL4_SNP_POISONED.swap(true, Ordering::AcqRel) {
        cpu::halt_forever();
    }
    cpu::wrmsr(GHCB_MSR, 0x100 | ((reason as u64) << 16));
    vmgexit();
    cpu::halt_forever()
}

/// # Safety
/// The supplied CPUID page is an immutable, private copy of the SNP launch
/// table. The second page is a zeroed, private, exclusively owned GHCB page.
/// Only the BSP is running and both physical windows cover the pages.
pub unsafe fn init(cpuid: u64, ghcb: u64) {
    let pa = cpuid as *const CpuidPage;
    let count = unsafe { (*pa).count };
    if count == 0 || count > 64 {
        terminate(0);
    }
    FL4_SNP_CPUID_PAGE.store(cpuid, Ordering::Relaxed);
    let info = msr_request(0x002);
    if info & 0xfff != 0x001 || (info >> 48) < 2 || ((info >> 32) & 0xffff) > 2 {
        terminate(1);
    }
    let features = msr_request(0x080);
    if features & 0x1fff != 0x1081 {
        terminate(2);
    }
    FEATURES.store(features >> 12, Ordering::Relaxed);
    unsafe { prepare_cpu(0, ghcb) };
    register_cpu();
}

pub fn ap_creation() -> bool {
    FEATURES.load(Ordering::Relaxed) & 2 != 0
}

/// # Safety
/// ghcb is a private, zeroed and exclusively owned page for the given CPU.
/// That CPU has not started, and no other CPU has used the page.
pub unsafe fn prepare_cpu(cpu: usize, ghcb: u64) {
    super::transition_inner(fl4_core::layout::pptr(ghcb), PAGE, true, false);
    CHANNELS[cpu].gpa.store(ghcb, Ordering::Release);
}

pub fn register_cpu() {
    let ghcb = CHANNELS[percpu::cpu_index()].gpa.load(Ordering::Acquire);
    if ghcb == 0 || msr_request(ghcb | 0x012) != (ghcb | 0x013) {
        terminate(0);
    }
}

pub fn start_cpu(apic: u32, vmsa: u64, features: u64) {
    exchange(
        0x8000_0013,
        ((apic as u64) << 32) | 1,
        vmsa,
        |g| g.set(RAX, features),
        |_| (),
    );
}

/// Read launch-validated feature bits. The hypervisor-present bit and
/// XCR0-dependent XSAVE sizes are synthesized from local state.
pub fn cpuid(function: u32, sub: u32) -> Option<Cpuid> {
    let ptr = FL4_SNP_CPUID_PAGE.load(Ordering::Relaxed);
    if ptr == 0 {
        return None;
    }
    let table = unsafe { &*(ptr as *const CpuidPage) };
    let leaves = &table.leaves[..table.count as usize];
    let find = |function, sub| {
        leaves.iter().find(|l| {
            l.function == function
                && l.subfunction == sub
                && (function != 0xd || sub > 1 || (l.xcr0 <= 1 && l.xss == 0))
        })
    };
    // These architectural feature leaves ignore ECX on hardware. In
    // particular, libc issues CPUID(0) and CPUID(1) with ECX unspecified.
    let sub = match function {
        0 | 1 | 0x8000_0000..=0x8000_0008 => 0,
        _ => sub,
    };
    let entry = find(function, sub);
    let mut r = entry.map_or(
        Cpuid {
            eax: 0,
            ebx: 0,
            ecx: 0,
            edx: 0,
        },
        |l| Cpuid {
            eax: l.eax,
            ebx: l.ebx,
            ecx: l.ecx,
            edx: l.edx,
        },
    );
    if entry.is_some() {
        let apic_id = percpu::apic_id(percpu::cpu_index());
        match function {
            1 => r.ebx = (r.ebx & 0x00ff_ffff) | ((apic_id & 0xff) << 24),
            0xb | 0x1f => r.edx = apic_id,
            0x8000_001e => {
                r.eax = apic_id;
                let threads = ((r.ebx >> 8) & 0xff) + 1;
                let core_id = apic_id >> (32 - (threads - 1).leading_zeros());
                r.ebx = (r.ebx & !0xff) | (core_id & 0xff);
            }
            _ => {}
        }
    }
    let osxsave = cpu::read_cr4() & (1 << 18) != 0;
    if function == 1 {
        r.ecx = (r.ecx & !(1 << 27)) | ((osxsave as u32) << 27) | (1 << 31);
    }
    if function == 0xd && sub <= 1 && entry.is_some() {
        let xcr0 = if osxsave { cpu::xgetbv(0) } else { 1 };
        let mut size = 576;
        for i in 2..64 {
            if xcr0 & (1 << i) == 0 {
                continue;
            }
            let Some(l) = find(0xd, i) else { terminate(0) };
            if sub == 0 {
                size = size.max(l.ebx + l.eax);
            } else {
                if l.ecx & 2 != 0 {
                    size = (size + 63) & !63;
                }
                size += l.eax;
            }
        }
        r.ebx = size;
    }
    Some(r)
}

/// Change RMP ownership one 4 KiB page at a time. On a partial failure
/// stop before returning memory to the allocator in an unknown state.
pub(super) fn change_state(base: u64, pa: u64, bytes: u64, shared: bool) {
    for off in (0..bytes).step_by(PAGE as usize) {
        if shared {
            pvalidate(base + off, false);
        }
        let op = if shared { 2 } else { 1 };
        if msr_request((pa + off) | (op << 52) | 0x014) != 0x015 {
            terminate(0);
        }
        if !shared {
            pvalidate(base + off, true);
        }
    }
}

fn pvalidate(va: u64, valid: bool) {
    let result: u64;
    let carry: u8;
    unsafe {
        asm!(
            "pvalidate",
            "setc {carry}",
            inlateout("rax") va => result,
            in("rcx") 0u64,
            in("rdx") valid as u64,
            carry = lateout(reg_byte) carry,
            options(nostack),
        );
    }
    if result as u32 != 0 || carry != 0 {
        terminate(0);
    }
}

struct Ghcb {
    pa: u64,
    base: u64,
    valid: u128,
}

impl Ghcb {
    fn set(&mut self, off: usize, value: u64) {
        unsafe { ((self.base + off as u64) as *mut u64).write_volatile(value) };
        self.valid |= 1 << (off / 8);
    }

    fn read(&self, off: usize) -> u64 {
        let bit = off / 8;
        let v = unsafe { ((self.base + (VALID + bit / 8) as u64) as *const u8).read_volatile() };
        if v & (1 << (bit % 8)) == 0 {
            terminate(0);
        }
        unsafe { ((self.base + off as u64) as *const u64).read_volatile() }
    }
}

fn exchange<T>(
    code: u64,
    info1: u64,
    info2: u64,
    prepare: impl FnOnce(&mut Ghcb),
    read: impl FnOnce(&Ghcb) -> T,
) -> T {
    let flags: u64;
    unsafe { asm!("pushfq", "pop {}", "cli", out(reg) flags) };
    let channel = &CHANNELS[percpu::cpu_index()];
    let pa = channel.gpa.load(Ordering::Acquire);
    if pa == 0 || channel.in_use.swap(true, Ordering::Relaxed) {
        terminate(0);
    }
    let base = super::shared_ptr(pa);
    let mut ghcb = Ghcb { pa, base, valid: 0 };
    prepare(&mut ghcb);
    ghcb.set(EXIT_CODE, code);
    ghcb.set(EXIT_INFO1, info1);
    ghcb.set(EXIT_INFO2, info2);
    unsafe {
        ((base + VALID as u64) as *mut u64).write_volatile(ghcb.valid as u64);
        ((base + VALID as u64 + 8) as *mut u64).write_volatile((ghcb.valid >> 64) as u64);
        ((base + VERSION as u64) as *mut u16).write_volatile(2);
        ((base + VERSION as u64 + 2) as *mut u32).write_volatile(0);
    }
    cpu::wrmsr(GHCB_MSR, pa);
    vmgexit();
    if ghcb.read(EXIT_INFO1) as u32 != 0 {
        terminate(0);
    }
    let value = read(&ghcb);
    channel.in_use.store(false, Ordering::Relaxed);
    if flags & (1 << 9) != 0 {
        unsafe { asm!("sti", options(nostack)) };
    }
    value
}

pub fn port(port: u16, width: u64, input: bool, value: u32) -> u32 {
    let info = ((port as u64) << 16) | (1 << 9) | (width << 4) | input as u64;
    exchange(
        0x7b,
        info,
        0,
        |g| {
            if !input {
                g.set(RAX, value as u64);
            }
        },
        |g| if input { g.read(RAX) as u32 } else { 0 },
    )
}

pub fn read_msr(msr: u32) -> u64 {
    exchange(
        0x7c,
        0,
        0,
        |g| g.set(RCX, msr as u64),
        |g| ((g.read(RDX) as u32 as u64) << 32) | g.read(RAX) as u32 as u64,
    )
}

pub fn write_msr(msr: u32, value: u64) {
    exchange(
        0x7c,
        1,
        0,
        |g| {
            g.set(RCX, msr as u64);
            g.set(RAX, value as u32 as u64);
            g.set(RDX, value >> 32);
        },
        |_| (),
    );
}

pub fn rdtsc() -> u64 {
    exchange(
        0x6e,
        0,
        0,
        |_| (),
        |g| ((g.read(RDX) as u32 as u64) << 32) | g.read(RAX) as u32 as u64,
    )
}

pub fn write_dr7(value: u64) {
    exchange(0x37, 0, 0, |g| g.set(RAX, value), |_| ());
}

pub fn mmio(pa: u64, bytes: u64, write: Option<u64>) -> u64 {
    let code = if write.is_some() {
        0x8000_0002
    } else {
        0x8000_0001
    };
    exchange(
        code,
        pa,
        bytes,
        |g| {
            g.set(SCRATCH, g.pa + SHARED_BUFFER);
            unsafe { ((g.base + SHARED_BUFFER) as *mut u64).write_volatile(write.unwrap_or(0)) };
        },
        |g| unsafe { ((g.base + SHARED_BUFFER) as *const u64).read_volatile() },
    )
}
