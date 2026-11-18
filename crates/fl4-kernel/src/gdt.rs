//! GDT, TSS, IDT and the SYSCALL MSRs.
//!
//! Selectors follow Linux (l4h 0028): kernel code 0x10, kernel data 0x18,
//! user data 0x2b, user 64-bit code 0x33, TSS 0x40. Linux's 32-bit user
//! code 0x23 stays a null descriptor: FL4 runs user code in 64-bit mode
//! only (every exit loads 0x33), and with no compatibility-mode code
//! segment (nor an LDT) user code cannot leave it by a far return. SYSRET to
//! 64-bit mode takes 0x33 and 0x2b from STAR without reading the GDT.
use core::arch::asm;
use core::cell::UnsafeCell;
use fl4_arch_x86_64::cpu::{self, rdmsr, wrmsr, msr};
use fl4_arch_x86_64::percpu::{self, MAX_CPUS};

pub const KERNEL_CS: u16 = 0x10;
pub const KERNEL_DS: u16 = 0x18;
pub const TSS_SEL: u16 = 0x40;

const GDT_ENTRIES: usize = 10;

#[repr(C, align(16))]
struct Gdt([u64; GDT_ENTRIES]);

#[repr(C, align(16))]
struct Tss([u32; 26]);

#[repr(C, align(4096))]
struct Idt([u64; 512]);

/// NMI, #DB, #MC and #DF run on stacks of their own (IST1..IST4), as they
/// can arrive while the kernel still (or again) runs on the user's stack
/// pointer: between SYSCALL and the switch to the entry stack, and between
/// loading the user's RSP and SYSRET. Without them the CPU would push its
/// frame wherever user code pointed RSP. One stack per vector, so an NMI
/// during #DB (or the reverse) does not overwrite the other's frame.
const IST_VECTORS: [usize; 4] = [2, 1, 18, 8]; // NMI, #DB, #MC, #DF
const STACK_BYTES: usize = 4096;
const SNP_STACK_BYTES: usize = 8192;

#[repr(C, align(4096))]
struct SnpStack([u8; SNP_STACK_BYTES]);

#[repr(C, align(4096))]
struct Stack([u8; STACK_BYTES]);

/// One core's entry area, in the skim window (paging.rs): everything the
/// CPU and entry.S touch before an entry from user mode has switched to the
/// kernel's tables, and after an exit has switched to the user's.
///
/// Entries from user mode arrive on `entry_stack` (TSS.RSP0, and SYSCALL's
/// stack through `gs_block`) or an IST stack; entry.S then moves the frame
/// to the core's kernel stack in KSTACKS (`gs_block[2]`), which the user's
/// tables do not map. entry.S finds the area from the stack pointer: areas
/// are `size_of::<SkimCpu>()`-aligned, a power of two.
#[repr(C, align(65536))]
struct SkimCpu {
    /// KERNEL_GS_BASE points here: entry stack top, a scratch word for
    /// SYSCALL, kernel stack top, core index.
    gs_block: [u64; 4],
    gdt: Gdt,
    tss: Tss,
    entry_stack: Stack,
    ist: [Stack; 4],
    snp_ist: [SnpStack; 3],
}

pub const SKIM_CPU_SIZE: usize = core::mem::size_of::<SkimCpu>();
const _: () = assert!(SKIM_CPU_SIZE.is_power_of_two() && core::mem::align_of::<SkimCpu>() == SKIM_CPU_SIZE);
// entry.S reads the kernel stack top at offset 16.
const _: () = assert!(core::mem::offset_of!(SkimCpu, gs_block) == 0);

struct SkimTables {
    idt: Idt,
    cpus: [SkimCpu; MAX_CPUS],
}

struct Cell(UnsafeCell<SkimTables>);
unsafe impl Sync for Cell {}

#[link_section = ".bss.skim"]
static TABLES: Cell = Cell(UnsafeCell::new(SkimTables {
    idt: Idt([0; 512]),
    cpus: [const {
        SkimCpu {
            gs_block: [0; 4],
            gdt: Gdt([0; GDT_ENTRIES]),
            tss: Tss([0; 26]),
            entry_stack: Stack([0; STACK_BYTES]),
            ist: [const { Stack([0; STACK_BYTES]) }; 4],
            snp_ist: [const { SnpStack([0; SNP_STACK_BYTES]) }; 3],
        }
    }; MAX_CPUS],
}));

extern "C" {
    static fl4_vectors: u8;
    fn fl4_syscall_entry();
}

/// Top of core `cpu`'s entry stack, where exits to user mode build the
/// frame they return through.
pub fn entry_top(cpu: usize) -> u64 {
    let t = unsafe { &*TABLES.0.get() };
    t.cpus[cpu].entry_stack.0.as_ptr() as u64 + STACK_BYTES as u64
}

#[repr(C, packed)]
struct Pointer {
    limit: u16,
    base: u64,
}

/// Vectors user code may raise with `int n`: #BP and the trap range.
fn user_gate(v: usize) -> bool {
    v == 3 || (0xa0..0xff).contains(&v)
}

/// SNP standard injection permits the VMM to deliver an exception during
/// the SYSCALL/SYSRET windows with a user-controlled RSP. Every vector
/// needs a hardware stack switch, including vectors normally masked by
/// IF. Use separate stacks for #VC, other exceptions, and IRQ/trap gates:
/// an interrupt or an exception handler may itself access GHCB devices.
fn ist_index(vector: usize, snp: bool) -> u64 {
    if let Some(i) = IST_VECTORS.iter().position(|&v| v == vector) { return i as u64 + 1; }
    if !snp { return 0; }
    match vector {
        29 => 5,
        0..32 => 6,
        _ => 7,
    }
}

/// Bounds of the trusted runtime IST the given frame arrived on. The
/// boot IDT can deliver #VC before any runtime IST has been installed.
pub fn snp_ist(frame: u64, vector: usize) -> Option<core::ops::Range<u64>> {
    let base = unsafe { core::ptr::addr_of!((*TABLES.0.get()).cpus) as u64 };
    if frame.wrapping_sub(base) >= (MAX_CPUS * SKIM_CPU_SIZE) as u64 {
        return None;
    }
    let core = frame & !(SKIM_CPU_SIZE as u64 - 1);
    let index = ist_index(vector, true) as usize - 1;
    let (offset, bytes) = if index < IST_VECTORS.len() {
        (core::mem::offset_of!(SkimCpu, ist) + index * STACK_BYTES, STACK_BYTES)
    } else {
        (core::mem::offset_of!(SkimCpu, snp_ist) + (index - IST_VECTORS.len()) * SNP_STACK_BYTES, SNP_STACK_BYTES)
    };
    let start = core + offset as u64;
    let bounds = start..start + bytes as u64;
    bounds.contains(&frame).then_some(bounds)
}

/// Fill the IDT (shared by all cores).
pub fn init_idt() {
    let t = unsafe { &mut *TABLES.0.get() };
    let base = unsafe { &fl4_vectors as *const u8 as u64 };
    let snp = fl4_arch_x86_64::sev::snp::active();
    for v in 0..256 {
        let h = base + 16 * v as u64;
        let dpl: u64 = if user_gate(v) { 3 } else { 0 };
        let ist = ist_index(v, snp);
        let lo = (h & 0xffff) | ((KERNEL_CS as u64) << 16) | (ist << 32) | ((0x8e | (dpl << 5)) << 40) | (((h >> 16) & 0xffff) << 48);
        t.idt.0[2 * v] = lo;
        t.idt.0[2 * v + 1] = h >> 32;
    }
}

/// The SNP handoff needs #VC before setting up the per-core state. Only
/// expose that gate until the full IDT and its IST stacks are ready.
static mut BOOT_IDT: Idt = Idt([0; 512]);
pub const BOOT_IDT_LIMIT: u16 = 30 * 16 - 1;

pub fn boot_idt_base() -> u64 {
    core::ptr::addr_of!(BOOT_IDT) as u64
}

pub fn load_boot_vc() {
    let a = core::ptr::addr_of_mut!(BOOT_IDT).cast::<u64>();
    let h = unsafe { &fl4_vectors as *const u8 as u64 + 16 * 29 };
    let lo = (h & 0xffff) | ((KERNEL_CS as u64) << 16) | (0x8e << 40) | (((h >> 16) & 0xffff) << 48);
    let ip = Pointer { limit: BOOT_IDT_LIMIT, base: a as u64 };
    unsafe {
        a.add(58).write(lo);
        a.add(59).write(h >> 32);
        asm!("lidt [{}]", in(reg) &ip, options(readonly, nostack, preserves_flags));
    }
}

/// Load the GDT, TSS and IDT on core `cpu`, with `stack_top` as the
/// kernel stack entries from user mode move to, and set up SYSCALL.
pub fn init_core(cpu: usize, stack_top: u64) {
    let t = unsafe { &mut *TABLES.0.get() };
    percpu::register_entry_areas(t.cpus.as_ptr() as u64, SKIM_CPU_SIZE as u64);
    let c = &mut t.cpus[cpu];
    let entry = c.entry_stack.0.as_ptr() as u64 + STACK_BYTES as u64;
    c.gs_block = [entry, 0, stack_top, cpu as u64];
    let g = &mut c.gdt.0;
    g[0] = 0;
    g[1] = 0;
    g[2] = 0x00af_9a00_0000_ffff; // 0x10 kernel code
    g[3] = 0x00cf_9200_0000_ffff; // 0x18 kernel data
    g[4] = 0; // 0x20: no 32-bit user code
    g[5] = 0x00cf_f200_0000_ffff; // 0x28 user data
    g[6] = 0x00af_fa00_0000_ffff; // 0x30 user code (64-bit)
    g[7] = 0;
    let tss = &mut c.tss;
    tss.0 = [0; 26];
    tss.0[1] = entry as u32;
    tss.0[2] = (entry >> 32) as u32;
    // IST1..IST4 (TSS bytes 36..68).
    for i in 0..IST_VECTORS.len() {
        let top = c.ist[i].0.as_ptr() as u64 + STACK_BYTES as u64;
        tss.0[9 + 2 * i] = top as u32;
        tss.0[10 + 2 * i] = (top >> 32) as u32;
    }
    if fl4_arch_x86_64::sev::snp::active() {
        for (i, stack) in c.snp_ist.iter().enumerate() {
            let top = stack.0.as_ptr() as u64 + SNP_STACK_BYTES as u64;
            tss.0[17 + 2 * i] = top as u32;
            tss.0[18 + 2 * i] = (top >> 32) as u32;
        }
    }
    // No I/O permission bitmap: the base is past the limit.
    tss.0[25] = 104 << 16;
    let tb = tss as *const Tss as u64;
    let limit = 103u64;
    g[8] = (limit & 0xffff) | ((tb & 0xff_ffff) << 16) | (0x89 << 40) | (((tb >> 24) & 0xff) << 56);
    g[9] = tb >> 32;

    let gp = Pointer { limit: (GDT_ENTRIES * 8 - 1) as u16, base: g.as_ptr() as u64 };
    let ip = Pointer { limit: (512 * 8 - 1) as u16, base: t.idt.0.as_ptr() as u64 };
    unsafe {
        asm!(
            "lgdt [{gp}]",
            "push {cs}",
            "lea {tmp}, [rip + 2f]",
            "push {tmp}",
            "retfq",
            "2:",
            "mov ds, {ds:e}",
            "mov es, {ds:e}",
            "mov ss, {ds:e}",
            "mov fs, {zero:e}",
            "mov gs, {zero:e}",
            "ltr {tss:x}",
            "lldt {zero:x}",
            "lidt [{ip}]",
            gp = in(reg) &gp,
            ip = in(reg) &ip,
            cs = in(reg) KERNEL_CS as u64,
            ds = in(reg) KERNEL_DS as u64,
            zero = in(reg) 0u64,
            tss = in(reg) TSS_SEL as u64,
            tmp = out(reg) _,
        );
    }

    // SYSCALL: CS from STAR[47:32], SYSRET selectors from STAR[63:48].
    wrmsr(msr::EFER, rdmsr(msr::EFER) | 1);
    wrmsr(msr::STAR, (0x23u64 << 48) | ((KERNEL_CS as u64) << 32));
    wrmsr(msr::LSTAR, fl4_syscall_entry as *const () as u64);
    // Compatibility-mode SYSCALL (AMD) cannot happen without a 32-bit
    // code segment; CSTAR still names an entry rather than address 0.
    wrmsr(msr::CSTAR, fl4_syscall_entry as *const () as u64);
    // No SYSENTER (valid in 64-bit mode on Intel): with SYSENTER_CS 0 it
    // raises #GP, whatever the boot loader left here. VM exits set it to 0
    // too (vm.rs HOST_SYSENTER_CS).
    wrmsr(msr::SYSENTER_CS, 0);
    // Clear TF, IF, DF, IOPL, NT and AC on entry.
    wrmsr(msr::FMASK, 0x4_7700);
    wrmsr(msr::FS_BASE, 0);
    wrmsr(msr::GS_BASE, 0);
    wrmsr(msr::KERNEL_GS_BASE, c.gs_block.as_ptr() as u64);
    // No breakpoint the boot loader left: the debug registers are reloaded
    // only for threads that use them (HARDWARE_DEBUG_API) and, on Intel,
    // around VM entries; AMD guests run with the host's DR0..DR3.
    cpu::write_dr7(0x400);
    for i in 0..4 {
        cpu::write_dr(i, 0);
    }
    cpu::write_dr6(0xffff_0ff0);
}
