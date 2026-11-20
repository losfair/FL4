//! FPU state switching. Each TCB holds an XSAVE image at
//! `layout::tcb::FPU`. The registers keep the state of the last thread
//! that ran with the FPU (the owner) until another such thread runs, so a
//! switch to and from the idle thread or an FPU-less thread costs nothing.
//! Threads with seL4_TCBFlag_fpuDisabled run with CR0.TS set and get #NM.
//!
//! On CPUs that LazyFP (CVE-2018-3665) does not affect, the switch is lazy
//! (DESIGN.md §3): a thread that does not own the registers runs with
//! CR0.TS set, and its first FPU instruction traps (#NM) to `lazy_load`,
//! which saves the owner's state and loads the thread's. A thread that
//! never touches the FPU between IPCs then costs no FPU work at all. On
//! Intel CPUs, where #NM-deferred state can leak through speculation, the
//! switch stays eager: the incoming thread's state is loaded on the way
//! out of the kernel, whether it uses the FPU or not, and a thread that
//! runs with CR0.TS set (seL4_TCBFlag_fpuDisabled) finds the registers in
//! their initial state, the last owner's saved (`scrub_local`).
//!
//! A thread that uses the FPU every time it runs would pay a trap and two
//! CR0.TS writes on top of the swap, which costs more than the eager
//! switch (CR0 writes are slow under a hypervisor). So, like Linux's old
//! `fpu_counter`, each thread counts its traps; from `EAGER_AFTER` on it is
//! switched eagerly. The counter is a byte that keeps counting and wraps,
//! so every 256 switches the thread is tried lazily again.
//!
//! The save instruction is the best the CPU has (DESIGN.md §3): XSAVES,
//! XSAVEC, XSAVEOPT, XSAVE, then FXSAVE. The first two write the compacted
//! format; an image leaves the FPU code (`flush`, for TCB_ReadFPU and
//! migration) in the standard format, and restore takes either.
use crate::cpu::{cpuid, msr, read_cr0, read_cr4, wrmsr, write_cr0, write_cr4, xsetbv};
use crate::percpu;
use core::arch::asm;
use core::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicU8, Ordering};
use fl4_core::layout::tcb;

static XSAVE: AtomicBool = AtomicBool::new(false);
static LAZY: AtomicBool = AtomicBool::new(false);
static XCR0: AtomicU64 = AtomicU64::new(0);
static MXCSR_MASK: AtomicU64 = AtomicU64::new(0xffbf);
static INSN: AtomicU8 = AtomicU8::new(Insn::Fxsave as u8);
/// Per state component: standard-format offset and size, and whether the
/// compacted format aligns it to 64 bytes (CPUID 0DH sub-leaf i).
static STD_OFF: [AtomicU32; 64] = [const { AtomicU32::new(0) }; 64];
static SIZE: [AtomicU32; 64] = [const { AtomicU32::new(0) }; 64];
static ALIGN: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum Insn {
    Fxsave = 0,
    Xsave = 1,
    Xsaveopt = 2,
    Xsavec = 3,
    Xsaves = 4,
}

fn insn() -> Insn {
    match INSN.load(Ordering::Relaxed) {
        1 => Insn::Xsave,
        2 => Insn::Xsaveopt,
        3 => Insn::Xsavec,
        4 => Insn::Xsaves,
        _ => Insn::Fxsave,
    }
}

/// AVX-512 (opmask, ZMM_Hi256, Hi16_ZMM): together, and only with AVX.
const AVX512: u64 = 0xe0;
const AVX: u64 = 1 << 2;
/// MPX (BNDREGS, BNDCSR): together.
const MPX: u64 = 0x18;

const CR0_MP: u64 = 1 << 1;
const CR0_EM: u64 = 1 << 2;
const CR0_TS: u64 = 1 << 3;
const CR0_NE: u64 = 1 << 5;
const CR4_OSFXSR: u64 = 1 << 9;
const CR4_OSXMMEXCPT: u64 = 1 << 10;
const CR4_OSXSAVE: u64 = 1 << 18;

/// XSAVE header: XSTATE_BV, XCOMP_BV (bit 63: compacted).
const HDR: u64 = 512;
const COMPACTED: u64 = 1 << 63;

#[repr(C, align(64))]
struct Scratch([u8; 512]);

/// An image of the initial FPU state, for every restore instruction:
/// FCW 0x37f and MXCSR 0x1f80 in the legacy area (FXRSTOR loads all of
/// it: empty x87 stack, XMM registers 0), XSTATE_BV 0 (XRSTOR and XRSTORS
/// put every requested component in its initial state, reading no
/// component data) and XCOMP_BV `compacted` (XRSTORS needs bit 63, XRSTOR
/// takes the standard format, 0); the other header bytes are 0, as both
/// require. The 1 KiB covers the legacy area and the header with room.
#[repr(C, align(64))]
struct InitImage([u8; 1024]);

const fn init_image(compacted: bool) -> InitImage {
    let mut b = [0u8; 1024];
    b[0] = 0x7f;
    b[1] = 0x03;
    b[24] = 0x80;
    b[25] = 0x1f;
    if compacted {
        b[HDR as usize + 15] = 0x80;
    }
    InitImage(b)
}

static INIT_STANDARD: InitImage = init_image(false);
static INIT_COMPACTED: InitImage = init_image(true);

/// PKRU.
const PKRU: u64 = 1 << 9;
/// The user state components FL4 knows the standard-format layout of (x87,
/// SSE, AVX, MPX, AVX-512, PKRU). Anything else (AMX, whose tile data alone
/// is 8 KiB, APX, components future CPUs add) stays off: its offset could
/// lie past the TCB's image.
const ALLOWED: u64 = 0x3 | AVX | MPX | AVX512 | PKRU;

/// The user state components to enable, given the ones the CPU supports
/// (CPUID 0DH.0 EDX:EAX) and `size`, the XSAVE image size with a given XCR0
/// (which `size` sets). Only `ALLOWED` components; AVX and AVX-512 only
/// with SSE; the largest groups dropped until the image fits the TCB, and
/// x87 and SSE alone if it still does not.
fn choose_components(supported: u64, mut size: impl FnMut(u64) -> u64) -> u64 {
    let mut x = (supported & ALLOWED) | 1;
    if x & 2 == 0 {
        x &= !(AVX | AVX512);
    }
    if x & AVX512 != AVX512 || x & AVX == 0 {
        x &= !AVX512;
    }
    if x & MPX != MPX {
        x &= !MPX;
    }
    for drop in [AVX512, MPX] {
        if size(x) <= tcb::FPU_SIZE {
            return x;
        }
        x &= !drop;
    }
    if size(x) > tcb::FPU_SIZE {
        x = 0x3;
        size(x);
    }
    x
}

fn components() -> u64 {
    let sup = cpuid(0xd, 0);
    choose_components(sup.eax as u64 | ((sup.edx as u64) << 32), |x| {
        xsetbv(0, x);
        cpuid(0xd, 0).ebx as u64
    })
}

/// What `init` picks on a core: state components, their standard-format
/// layout and compacted alignment, the save instruction, lazy switching
/// and the MXCSR mask. Images and the globals below are shared by every
/// core, so another core must come to the boot core's choice exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Config {
    pub xsave: bool,
    pub xcr0: u64,
    pub insn: u8,
    pub align: u64,
    pub size: [u32; 64],
    pub std_off: [u32; 64],
    pub lazy: bool,
    pub mxcsr_mask: u64,
}

/// Whether a core that picked `ap` can share the boot core's (`bsp`)
/// images and globals: only with the same choice on every axis. A core
/// with other state components or layouts would make XRSTOR(S) of an
/// image fault in the kernel (#GP), or lose state.
pub fn symmetric(bsp: &Config, ap: &Config) -> bool {
    bsp == ap
}

/// Enable the FPU on this core (CR0, CR4, XCR0, XSS: this core's own
/// registers) and work out its `Config`, changing no global.
fn probe() -> Config {
    write_cr0((read_cr0() & !(CR0_EM | CR0_TS)) | CR0_MP | CR0_NE);
    let mut cr4 = read_cr4() | CR4_OSFXSR | CR4_OSXMMEXCPT;
    let has_xsave = cpuid(1, 0).ecx & (1 << 26) != 0;
    if has_xsave {
        cr4 |= CR4_OSXSAVE;
    }
    write_cr4(cr4);
    let mut c = Config {
        xsave: has_xsave,
        xcr0: 0,
        insn: Insn::Fxsave as u8,
        align: 0,
        size: [0; 64],
        std_off: [0; 64],
        lazy: false,
        mxcsr_mask: 0,
    };
    if has_xsave {
        let x = components();
        xsetbv(0, x);
        c.xcr0 = x;
        for i in 2..63 {
            if x & (1 << i) != 0 {
                let l = cpuid(0xd, i);
                c.size[i as usize] = l.eax;
                c.std_off[i as usize] = l.ebx;
                if l.ecx & 2 != 0 {
                    c.align |= 1 << i;
                }
            }
        }
        let ext = cpuid(0xd, 1).eax;
        let i = if ext & (1 << 3) != 0 {
            // XSAVES saves supervisor state too; FL4 enables none.
            wrmsr(msr::XSS, 0);
            Insn::Xsaves
        } else if ext & (1 << 1) != 0 {
            Insn::Xsavec
        } else if ext & 1 != 0 {
            Insn::Xsaveopt
        } else {
            Insn::Xsave
        };
        c.insn = i as u8;
    }
    // LazyFP is an Intel erratum; AMD (and Hygon) are not affected.
    let v = cpuid(0, 0);
    let intel = v.ebx == 0x756e_6547 && v.edx == 0x4965_6e69 && v.ecx == 0x6c65_746e;
    c.lazy = !intel;
    unsafe { asm!("fninit", options(nomem, nostack)) };
    let mut f = Scratch([0; 512]);
    unsafe { asm!("fxsave64 [{}]", in(reg) f.0.as_mut_ptr(), options(nostack)) };
    let m = u32::from_le_bytes([f.0[28], f.0[29], f.0[30], f.0[31]]) as u64;
    c.mxcsr_mask = if m == 0 { 0xffbf } else { m };
    c
}

/// The boot core's `Config`, as `init(true)` recorded it.
fn recorded() -> Config {
    Config {
        xsave: XSAVE.load(Ordering::Relaxed),
        xcr0: XCR0.load(Ordering::Relaxed),
        insn: INSN.load(Ordering::Relaxed),
        align: ALIGN.load(Ordering::Relaxed),
        size: core::array::from_fn(|i| SIZE[i].load(Ordering::Relaxed)),
        std_off: core::array::from_fn(|i| STD_OFF[i].load(Ordering::Relaxed)),
        lazy: LAZY.load(Ordering::Relaxed),
        mxcsr_mask: MXCSR_MASK.load(Ordering::Relaxed),
    }
}

/// Enable the FPU on this core and pick the state components and the save
/// instruction. The boot core (`bsp`) records its choice for every core;
/// another core returns whether it came to the same (`symmetric`), and
/// changes no global either way.
pub fn init(bsp: bool) -> bool {
    let c = probe();
    if !bsp {
        return symmetric(&recorded(), &c);
    }
    XSAVE.store(c.xsave, Ordering::Relaxed);
    XCR0.store(c.xcr0, Ordering::Relaxed);
    INSN.store(c.insn, Ordering::Relaxed);
    ALIGN.store(c.align, Ordering::Relaxed);
    for i in 0..64 {
        SIZE[i].store(c.size[i], Ordering::Relaxed);
        STD_OFF[i].store(c.std_off[i], Ordering::Relaxed);
    }
    LAZY.store(c.lazy, Ordering::Relaxed);
    MXCSR_MASK.store(c.mxcsr_mask, Ordering::Relaxed);
    true
}

pub fn xcr0() -> u64 {
    XCR0.load(Ordering::Relaxed)
}

/// The save instruction, for the boot banner.
pub fn save_insn() -> &'static str {
    match insn() {
        Insn::Fxsave => "fxsave",
        Insn::Xsave => "xsave",
        Insn::Xsaveopt => "xsaveopt",
        Insn::Xsavec => "xsavec",
        Insn::Xsaves => "xsaves",
    }
}

/// Traps after which a thread's FPU state is loaded eagerly.
const EAGER_AFTER: u8 = 3;

fn use_count(t: u64) -> *mut u8 {
    (t + tcb::FPU_USE) as *mut u8
}

/// FPU switching is lazy on this CPU.
pub fn lazy() -> bool {
    LAZY.load(Ordering::Relaxed)
}

/// `flush` may rewrite a TCB's image even when its state is not live:
/// saves write the compacted format, or skip components in their initial
/// state (the init optimization of XSAVEOPT, XSAVEC and XSAVES), leaving
/// older bytes in place that `flush` clears.
pub fn flush_writes() -> bool {
    matches!(insn(), Insn::Xsaveopt | Insn::Xsavec | Insn::Xsaves)
}

fn image(t: u64) -> *mut u8 {
    (t + tcb::FPU) as *mut u8
}

fn rd(p: *mut u8, off: u64) -> u64 {
    unsafe { core::ptr::read_volatile(p.add(off as usize) as *const u64) }
}

fn wr(p: *mut u8, off: u64, v: u64) {
    unsafe { core::ptr::write_volatile(p.add(off as usize) as *mut u64, v) }
}

/// Offsets of the components `comp` names in the compacted format.
fn compacted_offsets(comp: u64, out: &mut [u64; 64]) {
    let align = ALIGN.load(Ordering::Relaxed);
    let mut off = HDR + 64;
    for i in 2..63 {
        if comp & (1 << i) == 0 {
            continue;
        }
        if align & (1 << i) != 0 {
            off = (off + 63) & !63;
        }
        out[i] = off;
        off += SIZE[i].load(Ordering::Relaxed) as u64;
    }
}

/// Rewrite `t`'s compacted image in the standard format. Standard
/// offsets are never below compacted ones, so components move up, the
/// last first. Components in their initial state are zeroed.
fn to_standard(t: u64) {
    let p = image(t);
    let comp = rd(p, HDR + 8);
    if comp & COMPACTED == 0 {
        return;
    }
    let bv = rd(p, HDR);
    let mut coff = [0u64; 64];
    compacted_offsets(comp, &mut coff);
    for i in (2..63).rev() {
        if comp & (1 << i) == 0 {
            continue;
        }
        let size = SIZE[i].load(Ordering::Relaxed) as usize;
        let dst = STD_OFF[i].load(Ordering::Relaxed) as usize;
        unsafe {
            if bv & (1 << i) != 0 {
                core::ptr::copy(p.add(coff[i] as usize), p.add(dst), size);
            } else {
                core::ptr::write_bytes(p.add(dst), 0, size);
            }
        }
    }
    wr(p, HDR + 8, 0);
}

/// In the standard-format image `img`, give each enabled (`xcr0`) state
/// component that XSTATE_BV marks as in its initial state its initial
/// value: x87 (FCW 0x37f, every other field and register 0), XMM0..15 0,
/// and the components from 2 on (`std(i)`: offset and size) 0. A save with
/// the init optimization does not write such components, so the image
/// would otherwise show values the thread had before. (MXCSR is not part
/// of either component's initial state: saves always write it.)
fn clear_init(img: &mut [u8], xcr0: u64, std: impl Fn(usize) -> (usize, usize)) {
    let mut bv = [0u8; 8];
    bv.copy_from_slice(&img[HDR as usize..HDR as usize + 8]);
    let init = xcr0 & !u64::from_le_bytes(bv);
    if init & 1 != 0 {
        img[..24].fill(0);
        img[..2].copy_from_slice(&0x037fu16.to_le_bytes());
        img[32..160].fill(0);
    }
    if init & 2 != 0 {
        img[160..416].fill(0);
    }
    for i in 2..63 {
        if init & (1 << i) != 0 {
            let (off, size) = std(i);
            if let Some(c) = img.get_mut(off..off + size) {
                c.fill(0);
            }
        }
    }
}

/// Rewrite `t`'s standard image in the compacted format XRSTORS needs:
/// components move down, the first first.
fn to_compacted(t: u64) {
    let p = image(t);
    if rd(p, HDR + 8) & COMPACTED != 0 {
        return;
    }
    let comp = XCR0.load(Ordering::Relaxed) & !COMPACTED;
    let mut coff = [0u64; 64];
    compacted_offsets(comp, &mut coff);
    for i in 2..63 {
        if comp & (1 << i) == 0 {
            continue;
        }
        let size = SIZE[i].load(Ordering::Relaxed) as usize;
        let src = STD_OFF[i].load(Ordering::Relaxed) as usize;
        unsafe { core::ptr::copy(p.add(src), p.add(coff[i] as usize), size) };
    }
    wr(p, HDR + 8, comp | COMPACTED);
}

fn save(t: u64) {
    let p = image(t);
    unsafe {
        match insn() {
            Insn::Xsaves => asm!("xsaves64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
            Insn::Xsavec => asm!("xsavec64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
            Insn::Xsaveopt => asm!("xsaveopt64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
            Insn::Xsave => asm!("xsave64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
            Insn::Fxsave => asm!("fxsave64 [{}]", in(reg) p, options(nostack)),
        }
    }
}

fn restore(t: u64) {
    let p = image(t);
    unsafe {
        match insn() {
            Insn::Xsaves => {
                to_compacted(t);
                asm!("xrstors64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack))
            }
            Insn::Fxsave => asm!("fxrstor64 [{}]", in(reg) p, options(nostack)),
            // XRSTOR takes both formats.
            _ => asm!("xrstor64 [{}]", in(reg) p, in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
        }
    }
}

#[inline(always)]
fn set_ts(on: bool) {
    let pc = percpu::get();
    if pc.ts_set.get() != on {
        if on {
            write_cr0(read_cr0() | CR0_TS);
        } else {
            // Cheaper than a read and write of CR0. Every switch between
            // a thread with the FPU disabled and one with it does one or
            // the other.
            unsafe { asm!("clts", options(nomem, nostack, preserves_flags)) }
        }
        pc.ts_set.set(on);
    }
}

/// Put every enabled FPU component in its initial state. CR0.TS is clear.
fn load_init() {
    unsafe {
        match insn() {
            Insn::Xsaves => asm!("xrstors64 [{}]", in(reg) INIT_COMPACTED.0.as_ptr(), in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
            Insn::Fxsave => asm!("fxrstor64 [{}]", in(reg) INIT_STANDARD.0.as_ptr(), options(nostack)),
            _ => asm!("xrstor64 [{}]", in(reg) INIT_STANDARD.0.as_ptr(), in("eax") u32::MAX, in("edx") u32::MAX, options(nostack)),
        }
    }
    percpu::get().fpu_clean.set(true);
}

/// Where switching is eager (LazyFP-affected Intel), a thread that runs
/// with CR0.TS set must find no other thread's state in the registers:
/// its FPU instructions trap (#NM), but they can read the registers
/// speculatively before they do. Save the owner's state, if any, and
/// leave the initial state there.
fn scrub_local() {
    let owner = percpu::fpu_owner(percpu::cpu_index());
    if owner == 0 && percpu::get().fpu_clean.get() {
        return;
    }
    set_ts(false);
    if owner != 0 {
        save(owner);
        percpu::set_fpu_owner(0);
    }
    load_init();
}

/// Exit path: make the FPU right for thread `t`.
#[inline(always)]
pub fn switch_to(t: u64, fpu_disabled: bool) {
    if fpu_disabled {
        if !lazy() {
            scrub_local();
        }
        set_ts(true);
        return;
    }
    if percpu::fpu_owner(percpu::cpu_index()) == t {
        set_ts(false);
        return;
    }
    if lazy() {
        let n = unsafe { core::ptr::read_volatile(use_count(t)) };
        if n < EAGER_AFTER {
            // The swap waits for the thread's first FPU instruction.
            set_ts(true);
            return;
        }
        unsafe { core::ptr::write_volatile(use_count(t), n.wrapping_add(1)) };
    }
    set_ts(false);
    load(t);
}

/// Save the owner's state, if any, and load `t`'s.
fn load(t: u64) {
    let owner = percpu::fpu_owner(percpu::cpu_index());
    if owner != 0 {
        save(owner);
    }
    restore(t);
    percpu::get().fpu_clean.set(false);
    percpu::set_fpu_owner(t);
}

/// #NM from thread `t` on the lazy path: give it the FPU. Runs in the
/// entry glue with interrupts off, so no remote FPU call (`flush`,
/// `forget`) for this core can run in between.
pub fn lazy_load(t: u64) {
    unsafe {
        let n = core::ptr::read_volatile(use_count(t));
        core::ptr::write_volatile(use_count(t), n.saturating_add(1).max(1));
    }
    set_ts(false);
    if percpu::fpu_owner(percpu::cpu_index()) != t {
        load(t);
    }
}

/// Write `t`'s state back to its TCB if it is live on this core. CR0.TS
/// goes back to what it was: the current thread may be one that must still
/// trap on its first FPU instruction.
fn flush_local(t: u64) {
    if percpu::fpu_owner(percpu::cpu_index()) == t {
        let ts = percpu::get().ts_set.get();
        set_ts(false);
        save(t);
        set_ts(ts);
    }
}

/// Forget `t`'s state if it is live on this core. The registers keep it
/// (`fpu_clean` stays clear) until a load or `scrub_local` replaces it.
pub fn forget_local(t: u64) {
    if percpu::fpu_owner(percpu::cpu_index()) == t {
        percpu::set_fpu_owner(0);
    }
}

/// Save `t`'s state to its TCB and forget it if it is live on this core
/// (seL4 `switchLocalFpuOwner(NULL)`). CR0.TS ends up set: a thread that
/// was running with the registers (one whose FPU was just disabled) traps
/// on its next FPU instruction; any other thread on this core had them
/// set already, as a thread that does not own the registers runs so.
pub fn release_local(t: u64) {
    if percpu::fpu_owner(percpu::cpu_index()) == t {
        set_ts(false);
        save(t);
        percpu::set_fpu_owner(0);
        if !lazy() {
            load_init();
        }
        set_ts(true);
    }
}

/// The core whose registers hold `t`'s FPU state, if any.
fn owner_core(t: u64) -> Option<usize> {
    (0..percpu::MAX_CPUS).find(|&c| percpu::fpu_owner(c) == t)
}

/// Whether some core's registers hold `t`'s FPU state.
pub fn is_live(t: u64) -> bool {
    owner_core(t).is_some()
}

/// The remote call `flush` makes for state live on core `owner`, if any,
/// when it runs on core `me`.
///
/// Another core gives the state up, not just saves it: it still owns the
/// registers otherwise, and its next load for another thread (`lazy_load`
/// on #NM, which runs without the serial gate, or an exit's `switch_to`)
/// saves them over `t`'s image while this core converts or rewrites that
/// image (`to_standard`, `clear_init`, TCB_WriteFPU's copy and
/// `sanitise`): a torn image whose XRSTORS faults in the kernel. `t` does
/// not run there (callers stall or migrate it first), so the release takes
/// nothing from the thread that does.
fn flush_call(owner: Option<usize>, me: usize) -> Option<(u64, usize)> {
    match owner {
        Some(c) if c != me => Some((crate::smp::CALL_FPU_RELEASE, c)),
        _ => None,
    }
}

/// Write `t`'s live state, wherever it is, back to its TCB, in the
/// standard format. The caller holds the serial gate when another core may
/// hold the state; it is no longer live there afterwards (`flush_call`).
pub fn flush(t: u64) {
    let owner = owner_core(t);
    let me = percpu::cpu_index();
    match flush_call(owner, me) {
        Some((call, c)) => crate::smp::remote_call(call, t, 0, 1 << c),
        None if owner == Some(me) => flush_local(t),
        None => {}
    }
    if XSAVE.load(Ordering::Relaxed) {
        to_standard(t);
        if flush_writes() {
            let img = unsafe { core::slice::from_raw_parts_mut(image(t), tcb::FPU_SIZE as usize) };
            clear_init(img, XCR0.load(Ordering::Relaxed), |i| {
                (STD_OFF[i].load(Ordering::Relaxed) as usize, SIZE[i].load(Ordering::Relaxed) as usize)
            });
        }
    }
}

/// `t`'s state is no longer (or no longer only) in some core's registers.
pub fn forget(t: u64) {
    match owner_core(t) {
        Some(c) if c == percpu::cpu_index() => forget_local(t),
        Some(c) => crate::smp::remote_call(crate::smp::CALL_FPU_DROP, t, 0, 1 << c),
        None => {}
    }
}

/// `t` is being deleted, moved away or loses the FPU: save its live state,
/// wherever it is, to its TCB and forget it there (seL4 `fpuRelease`). The
/// caller holds the serial gate when another core may hold the state.
pub fn release(t: u64) {
    match owner_core(t) {
        Some(c) if c == percpu::cpu_index() => release_local(t),
        Some(c) => crate::smp::remote_call(crate::smp::CALL_FPU_RELEASE, t, 0, 1 << c),
        None => {}
    }
}

/// Make a user-written image safe for XRSTOR/FXRSTOR (l4h 0002).
pub fn sanitise(t: u64) {
    let f = t + tcb::FPU;
    unsafe {
        // MXCSR at byte 24 (low half of the word).
        let w = (f + 24) as *mut u64;
        let v = core::ptr::read_volatile(w);
        let mx = (v as u32 as u64) & MXCSR_MASK.load(Ordering::Relaxed);
        core::ptr::write_volatile(w, (v & !0xffff_ffff) | mx);
        if XSAVE.load(Ordering::Relaxed) {
            // XSAVE header at 512: XSTATE_BV, XCOMP_BV, then reserved.
            let h = (f + 512) as *mut u64;
            let bv = core::ptr::read_volatile(h) & XCR0.load(Ordering::Relaxed);
            core::ptr::write_volatile(h, bv);
            let mut i = 1;
            while i < 8 {
                core::ptr::write_volatile(h.add(i), 0);
                i += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Standard-format image size for XCR0 `x` (CPUID 0DH.0 EBX), on a CPU
    /// with every component below and an unknown one at a high offset.
    fn size(x: u64) -> u64 {
        let mut end = 576;
        for (bits, e) in [(AVX, 832), (MPX, 1088), (AVX512, 2688), (PKRU, 2696), (1 << 19, 1216), (1 << 40, 8192)] {
            if x & bits != 0 {
                end = end.max(e);
            }
        }
        end
    }

    #[test]
    fn the_initial_images_hold_the_initial_state_and_valid_headers() {
        for (img, xcomp) in [(&INIT_STANDARD, 0u64), (&INIT_COMPACTED, COMPACTED)] {
            assert_eq!(img.0.as_ptr() as usize % 64, 0);
            let b = &img.0;
            let word = |o: usize| u64::from_le_bytes(b[o..o + 8].try_into().unwrap());
            assert_eq!(u16::from_le_bytes([b[0], b[1]]), 0x037f);
            assert_eq!(u32::from_le_bytes([b[24], b[25], b[26], b[27]]), 0x1f80);
            // Everything else in the legacy area is 0: FSW, FTW (all
            // empty), FOP, pointers, ST0..7, XMM0..15.
            assert!(b[2..24].iter().chain(&b[28..512]).all(|&x| x == 0));
            assert_eq!(word(HDR as usize), 0);
            assert_eq!(word(HDR as usize + 8), xcomp);
            assert!(b[HDR as usize + 16..].iter().all(|&x| x == 0));
        }
    }

    /// FXRSTOR and (with XSAVE) XRSTOR of the image leave no register
    /// value behind; XRSTORS needs ring 0.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn restoring_the_initial_image_clears_the_registers() {
        let read = || {
            let mut x = [0u64; 2];
            let mut mxcsr = 0u32;
            let mut fcw = 0u16;
            let mut fsw = 0u16;
            unsafe {
                asm!("movdqu [{x}], xmm7", "stmxcsr dword ptr [{m}]", "fnstcw word ptr [{c}]", "fnstsw word ptr [{w}]",
                     x = in(reg) x.as_mut_ptr(), m = in(reg) &mut mxcsr, c = in(reg) &mut fcw, w = in(reg) &mut fsw,
                     options(nostack));
            }
            (x, mxcsr, fcw, fsw)
        };
        let dirty = || unsafe {
            let m = 0x1f80u32 | (3 << 13);
            asm!("pcmpeqd xmm7, xmm7", "fld1", "fld1", "ldmxcsr dword ptr [{}]", in(reg) &m,
                 clobber_abi("C"), options(nostack));
        };
        dirty();
        unsafe { asm!("fxrstor64 [{}]", in(reg) INIT_STANDARD.0.as_ptr(), clobber_abi("C"), options(nostack)) };
        assert_eq!(read(), ([0, 0], 0x1f80, 0x037f, 0));
        if cpuid(1, 0).ecx & (1 << 27) != 0 {
            dirty();
            // x87, SSE and AVX only: the host may keep others (AMX) armed.
            unsafe {
                asm!("xrstor64 [{}]", in(reg) INIT_STANDARD.0.as_ptr(), in("eax") 7u32, in("edx") 0u32,
                     clobber_abi("C"), options(nostack))
            };
            assert_eq!(read(), ([0, 0], 0x1f80, 0x037f, 0));
        }
    }

    /// State live on another core is released there, so that core never
    /// saves over the image `flush` hands back; on this core it is saved
    /// and stays live.
    #[test]
    fn a_remote_flush_releases_the_state() {
        assert_eq!(flush_call(Some(1), 0), Some((crate::smp::CALL_FPU_RELEASE, 1)));
        assert_eq!(flush_call(Some(0), 1), Some((crate::smp::CALL_FPU_RELEASE, 0)));
        assert_eq!(flush_call(Some(2), 2), None);
        assert_eq!(flush_call(None, 0), None);
    }

    #[test]
    fn known_components_that_fit_are_kept() {
        let all = 0x3 | AVX | MPX | AVX512 | PKRU;
        assert_eq!(choose_components(all, size), all);
    }

    /// A component FL4 has no layout for (here one past the TCB's image)
    /// is never enabled, so XSAVE cannot write beyond the image.
    #[test]
    fn unknown_components_stay_off() {
        let amx = (1 << 17) | (1 << 18);
        let all = 0x3 | AVX | MPX | AVX512 | PKRU | amx | (1 << 19) | (1 << 40);
        let x = choose_components(all, size);
        assert_eq!(x, 0x3 | AVX | MPX | AVX512 | PKRU);
        assert!(size(x) <= tcb::FPU_SIZE);
    }

    /// If even the allowed groups do not fit after dropping AVX-512 and
    /// MPX, only x87 and SSE stay on.
    #[test]
    fn an_image_that_never_fits_falls_back_to_x87_and_sse() {
        let mut last = 0;
        let x = choose_components(0x3 | AVX | MPX | AVX512, |x| {
            last = x;
            if x == 0x3 { 576 } else { tcb::FPU_SIZE + 1 }
        });
        assert_eq!(x, 0x3);
        // The last XCR0 written is the one returned.
        assert_eq!(last, 0x3);
    }

    /// A standard-format image whose every byte is stale (0xaa), with
    /// XSTATE_BV `bv`; AVX (component 2) at 576, 256 bytes.
    fn stale(bv: u64) -> [u8; 1024] {
        let mut img = [0xaa; 1024];
        img[HDR as usize..HDR as usize + 8].copy_from_slice(&bv.to_le_bytes());
        img
    }

    fn std_off(i: usize) -> (usize, usize) {
        assert_eq!(i, 2);
        (576, 256)
    }

    /// XSAVEOPT, XSAVEC and XSAVES leave components in their initial state
    /// unwritten: TCB_ReadFPU must not see the older bytes, for x87 and SSE
    /// as for the others.
    #[test]
    fn init_components_read_as_initial_values() {
        let mut img = stale(0);
        clear_init(&mut img, 0x7, std_off);
        assert_eq!(&img[..2], &[0x7f, 0x03]);
        assert!(img[2..24].iter().all(|&b| b == 0));
        // MXCSR and its mask are written by every save.
        assert!(img[24..32].iter().all(|&b| b == 0xaa));
        assert!(img[32..416].iter().all(|&b| b == 0));
        assert!(img[416..512].iter().all(|&b| b == 0xaa));
        assert!(img[576..832].iter().all(|&b| b == 0));
        assert!(img[832..].iter().all(|&b| b == 0xaa));
    }

    #[test]
    fn live_and_disabled_components_are_kept() {
        // x87 and AVX in use: only SSE is cleared.
        let mut img = stale(0x5);
        clear_init(&mut img, 0x7, std_off);
        assert!(img[..160].iter().all(|&b| b == 0xaa));
        assert!(img[160..416].iter().all(|&b| b == 0));
        assert!(img[576..832].iter().all(|&b| b == 0xaa));
        // A component XCR0 leaves off is not touched (nor looked up).
        let mut img = stale(0x3);
        clear_init(&mut img, 0x3, |_| unreachable!());
        assert!(img.iter().enumerate().all(|(i, &b)| b == 0xaa || (HDR as usize..HDR as usize + 8).contains(&i)));
    }

    #[test]
    fn avx_needs_sse() {
        assert_eq!(choose_components(0x1 | AVX | AVX512, size), 0x1);
        assert_eq!(choose_components(0x3 | AVX512, size), 0x3);
        assert_eq!(choose_components(0x3 | (MPX & 0x8), size), 0x3);
    }

    fn boot() -> Config {
        let mut size = [0; 64];
        let mut std_off = [0; 64];
        size[2] = 256;
        std_off[2] = 576;
        size[9] = 8;
        std_off[9] = 2688;
        Config {
            xsave: true,
            xcr0: 0x207,
            insn: Insn::Xsavec as u8,
            align: 0,
            size,
            std_off,
            lazy: true,
            mxcsr_mask: 0xffff,
        }
    }

    /// Audit F4: a core whose FPU set-up differs from the boot core's in
    /// any respect is refused, never allowed to replace the boot core's.
    #[test]
    fn an_application_processor_must_match_the_boot_cores_fpu_choice() {
        let b = boot();
        assert!(symmetric(&b, &b));
        let axes: [fn(&mut Config); 9] = [
            |c| c.xsave = false,
            |c| c.xcr0 |= AVX512,
            |c| c.xcr0 &= !PKRU,
            |c| c.insn = Insn::Xsaves as u8,
            |c| c.align |= 1 << 9,
            |c| c.size[2] = 512,
            |c| c.std_off[9] = 2432,
            |c| c.lazy = false,
            |c| c.mxcsr_mask = 0xffbf,
        ];
        for (i, change) in axes.iter().enumerate() {
            let mut ap = b;
            change(&mut ap);
            assert!(!symmetric(&b, &ap), "axis {i}");
        }
    }
}
