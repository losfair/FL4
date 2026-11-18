//! The FL4 kernel image for AArch64 (DESIGN.md §11): boot from FL4's UEFI
//! loader (fl4-efi), and the glue between fl4-core and the AArch64
//! backend. One image for every UEFI platform: the hardware comes from
//! ACPI or the device tree at boot.
#![no_std]

mod entry;
mod hw;
mod paging;
mod smp;

use core::cell::UnsafeCell;
use core::fmt::Write;
use fl4_arch_aarch64::arch::PhysArch;
use fl4_arch_aarch64::{cpu, fpu, gic, percpu, serial, timer};
use fl4_bootinfo::{mem, BootInfo, KERNEL_VBASE, MAGIC};
use fl4_core::boot::{BootParams, Region, MAX_REGIONS, PADDR_USER_DEVICE_TOP};
use fl4_core::layout::{ks, pptr, PADDR_TOP};
use fl4_core::machine::Store;
use fl4_core::obj::ks_set;
use fl4_core::sched;

core::arch::global_asm!(".equ FL4_MAIR, {mair}", include_str!("boot.S"), mair = const fl4_core::vspace::MAIR);

pub struct Console;

impl Write for Console {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for b in s.bytes() {
            if b == b'\n' {
                serial::putc(b'\r');
            }
            serial::putc(b);
        }
        Ok(())
    }
}

#[macro_export]
macro_rules! kprintln {
    ($($arg:tt)*) => {{
        let _ = core::fmt::Write::write_fmt(&mut $crate::Console, format_args!($($arg)*));
        let _ = core::fmt::Write::write_str(&mut $crate::Console, "\n");
    }};
}

const PAGE: u64 = 4096;
// The loader's bounds (fl4-bootinfo) are the kernel's window and user space.
const _: () = assert!(fl4_bootinfo::LOAD_TOP == PADDR_TOP && fl4_bootinfo::USER_END == fl4_abi::consts::USER_TOP + 1);
const IDLE_STRIDE: usize = 8192;
/// Extra BootInfo beyond the device tree.
const EXTRA_FIXED: u64 = 4096;

#[repr(C, align(64))]
struct KsArea([u8; ks::SIZE as usize]);

#[repr(C, align(4096))]
struct IdleArea([[u8; IDLE_STRIDE]; percpu::MAX_CPUS]);

struct Statics {
    ks: KsArea,
    idle: IdleArea,
}

struct Cell(UnsafeCell<Statics>);
unsafe impl Sync for Cell {}

static STATICS: Cell = Cell(UnsafeCell::new(Statics { ks: KsArea([0; ks::SIZE as usize]), idle: IdleArea([[0; IDLE_STRIDE]; percpu::MAX_CPUS]) }));

pub fn fail(msg: &str) -> ! {
    kprintln!("FL4 boot failed: {}", msg);
    cpu::halt_forever()
}

/// A small sorted list of half-open physical ranges.
#[derive(Clone, Copy)]
struct Ranges {
    r: [Region; 128],
    n: usize,
}

impl Ranges {
    const fn new() -> Ranges {
        Ranges { r: [Region::EMPTY; 128], n: 0 }
    }

    fn add(&mut self, start: u64, end: u64) {
        if start >= end || self.n == self.r.len() {
            return;
        }
        let mut i = self.n;
        while i > 0 && self.r[i - 1].start > start {
            self.r[i] = self.r[i - 1];
            i -= 1;
        }
        self.r[i] = Region { start, end };
        self.n += 1;
        let mut out = 0;
        for j in 0..self.n {
            let cur = self.r[j];
            if out > 0 && cur.start <= self.r[out - 1].end {
                if cur.end > self.r[out - 1].end {
                    self.r[out - 1].end = cur.end;
                }
            } else {
                self.r[out] = cur;
                out += 1;
            }
        }
        self.n = out;
    }

    fn remove(&mut self, start: u64, end: u64) {
        let mut res = Ranges::new();
        for j in 0..self.n {
            let c = self.r[j];
            if c.end <= start || c.start >= end {
                res.add(c.start, c.end);
            } else {
                if c.start < start {
                    res.add(c.start, start);
                }
                if c.end > end {
                    res.add(end, c.end);
                }
            }
        }
        *self = res;
    }

    /// Take `len` bytes, page aligned, from the top of the highest range
    /// that has them.
    fn take(&mut self, len: u64) -> Option<u64> {
        let len = (len + PAGE - 1) & !(PAGE - 1);
        for j in (0..self.n).rev() {
            let c = self.r[j];
            if c.end - c.start >= len {
                let start = c.end - len;
                self.remove(start, c.end);
                return Some(start);
            }
        }
        None
    }
}

fn put(buf: &mut [u8], off: &mut usize, b: &[u8]) {
    buf[*off..*off + b.len()].copy_from_slice(b);
    *off += b.len();
}

fn hdr(buf: &mut [u8], off: &mut usize, id: u64, len: u64) {
    put(buf, off, &id.to_le_bytes());
    put(buf, off, &len.to_le_bytes());
}

/// The extra BootInfo records: the ACPI RSDP, the device tree, the boot
/// core's ID registers (l4h 0018) and the boot modules (l4h 0021).
fn build_extra_bi(buf: &mut [u8], h: &hw::Hw, dtb: u64, dtb_len: u64, bi: &BootInfo, mods: &[(u64, u64)]) -> usize {
    use fl4_abi::consts::bootinfo_header as id;
    let mut off = 0;
    if h.has_rsdp {
        hdr(buf, &mut off, id::X86_ACPI_RSDP, 16 + hw::RSDP_LEN as u64);
        put(buf, &mut off, &h.rsdp);
    }
    let regs = [
        fl4_arch_aarch64::mrs!("id_aa64isar0_el1"),
        fl4_arch_aarch64::mrs!("id_aa64isar1_el1"),
        fl4_arch_aarch64::mrs!("s3_0_c0_c6_2"), // ID_AA64ISAR2_EL1
        fl4_arch_aarch64::mrs!("id_aa64pfr0_el1"),
        fl4_arch_aarch64::mrs!("id_aa64pfr1_el1"),
    ];
    hdr(buf, &mut off, id::AARCH64_ID_REGS, 16 + 8 * regs.len() as u64);
    for r in regs {
        put(buf, &mut off, &r.to_le_bytes());
    }
    if !mods.is_empty() {
        hdr(buf, &mut off, id::X86_BOOT_MODULES, 16 + 8 + 80 * mods.len() as u64);
        put(buf, &mut off, &(mods.len() as u64).to_le_bytes());
        for (i, &(paddr, size)) in mods.iter().enumerate() {
            put(buf, &mut off, &paddr.to_le_bytes());
            put(buf, &mut off, &size.to_le_bytes());
            put(buf, &mut off, &bi.modules[i].name);
        }
    }
    if dtb_len != 0 {
        let len = (dtb_len + 7) & !7;
        hdr(buf, &mut off, id::FDT, 16 + len);
        let src = unsafe { core::slice::from_raw_parts(pptr(dtb) as *const u8, dtb_len as usize) };
        let at = off;
        put(buf, &mut off, src);
        // The copy's total size is what was copied.
        buf[at + 4..at + 8].copy_from_slice(&(dtb_len as u32).to_be_bytes());
        off = (off + 7) & !7;
    }
    off
}

fn has_option(bi: &BootInfo, opt: &[u8]) -> bool {
    let n = bi.cmdline.iter().position(|&c| c == 0).unwrap_or(bi.cmdline.len());
    bi.cmdline[..n].split(|&c| c == b' ').any(|w| w == opt)
}

#[no_mangle]
pub extern "C" fn fl4_boot(off: u64) -> ! {
    let bi = unsafe { &*((KERNEL_VBASE + off) as *const BootInfo) };
    if bi.magic != MAGIC || bi.version != fl4_bootinfo::VERSION {
        cpu::halt_forever();
    }
    let pa_top = (1u64 << cpu::pa_bits()).min(PADDR_USER_DEVICE_TOP);

    // RAM in the window: everything the memory map calls write-back memory.
    let mut ram = Ranges::new();
    let mut usable = Ranges::new();
    for e in &bi.mmap[..(bi.n_mmap as usize).min(fl4_bootinfo::MAX_MMAP)] {
        let start = (e.base + PAGE - 1) & !(PAGE - 1);
        let end = (e.base + e.len) & !(PAGE - 1);
        let end = end.min(PADDR_TOP).min(pa_top);
        if e.cacheable != 0 && (e.kind == mem::FREE || e.kind == mem::FIRMWARE) {
            ram.add(start, end);
        }
        if e.cacheable != 0 && e.kind == mem::FREE {
            usable.add(start, end);
        }
    }
    let mut window = [(0u64, 0u64); 128];
    for i in 0..ram.n {
        window[i] = (ram.r[i].start, ram.r[i].end);
    }
    let ttbr1 = paging::init(bi.region_paddr, bi.region_len, &window[..ram.n]);
    paging::activate(ttbr1);
    percpu::init(0);
    smp::init_core_regs();

    // The hardware and the console.
    let h = match hw::discover(bi.rsdp, bi.dtb) {
        Some(h) => h,
        None => cpu::halt_forever(),
    };
    if h.uart_kind != serial::KIND_NONE {
        let base = paging::map_device(h.uart_base, 0x1000);
        serial::init(h.uart_kind, base, h.uart_shift, h.uart_wide);
    }
    kprintln!("FL4: seL4 17.0 (MCS) API kernel, AArch64");
    kprintln!("FL4: hardware from the {}: GICv{}, {} core(s), console {}", h.source, h.gic_version, h.n_cpus,
        match h.uart_kind { serial::KIND_PL011 => "PL011", serial::KIND_16550 => "16550", _ => "none" });
    if !cpu::has_asid16() {
        fail("16-bit ASIDs are required (l4h 0016)");
    }
    if h.vtimer != 0 && h.vtimer != fl4_core::layout::irq::TIMER_ID {
        fail("the EL1 virtual timer is not PPI 27");
    }
    if h.gicd == 0 {
        fail("no GIC distributor");
    }

    // Interrupt controller, timer, FP/SIMD.
    let gicd = paging::map_device(h.gicd, 0x1_0000);
    let mut gicr_va = [(0u64, 0u64); hw::MAX_GICR];
    let mut dev_used = Ranges::new();
    dev_used.add(h.gicd, h.gicd + 0x1_0000);
    if fl4_abi::config::PRINTING && h.uart_kind != serial::KIND_NONE {
        dev_used.add(h.uart_base & !(PAGE - 1), (h.uart_base & !(PAGE - 1)) + PAGE);
    }
    let gicc = if h.gic_version == 3 {
        for i in 0..h.n_gicr {
            let (base, len) = h.gicr[i];
            // An unsized range (MADT GICC entries): one frame per core.
            let len = if len == 0 { 0x4_0000 * h.n_cpus as u64 } else { len };
            gicr_va[i] = (paging::map_device(base, len), len);
            dev_used.add(base, base + len);
        }
        smp::set_gicr(&gicr_va[..h.n_gicr]);
        0
    } else {
        if h.gicc == 0 {
            fail("no GICv2 CPU interface");
        }
        dev_used.add(h.gicc, h.gicc + 0x2000);
        paging::map_device(h.gicc, 0x2000)
    };
    gic::init_dist(h.gic_version, gicd, gicc);
    gic::init_cpu(smp::find_gicr());
    if !timer::init() {
        fail("CNTFRQ_EL0 is zero");
    }
    fpu::init();
    fl4_arch_aarch64::smp::set_psci(h.psci);
    kprintln!("FL4: timer at {} Hz, {} SPIs, PSCI {}", timer::freq(), gic::max_spi() - 31,
        match h.psci { 1 => "SMC", 2 => "HVC", _ => "absent" });

    // The other cores.
    let ncpus = smp::start_aps(&h.cpus[..h.n_cpus], ttbr1);
    kprintln!("FL4: {} core(s) running", ncpus);

    // Memory. The kernel region, the root task image and the boot modules
    // are taken; everything else of the free memory goes to user space.
    // Everything that is neither RAM nor the kernel's own devices goes to
    // user space as device memory (firmware tables included).
    let root = bi.root;
    if root.p_end <= root.p_start {
        fail("no root task");
    }
    let mut free = usable;
    free.remove(bi.region_paddr, bi.region_paddr + bi.region_len);
    free.remove(root.p_start, root.p_end);
    let mut mods = [(0u64, 0u64); fl4_bootinfo::MAX_MODULES];
    let n_mods = (bi.n_modules as usize).min(fl4_bootinfo::MAX_MODULES);
    for i in 0..n_mods {
        let m = bi.modules[i];
        free.remove(m.paddr & !(PAGE - 1), (m.paddr + m.size + PAGE - 1) & !(PAGE - 1));
    }
    let mut dev = Ranges::new();
    dev.add(0, pa_top);
    for i in 0..usable.n {
        dev.remove(usable.r[i].start, usable.r[i].end);
    }
    for i in 0..dev_used.n {
        dev.remove(dev_used.r[i].start, dev_used.r[i].end);
    }
    // The kernel's own memory and the root task's image are never device
    // memory, whatever the memory map said about them.
    dev.remove(bi.region_paddr, bi.region_paddr + bi.region_len);
    dev.remove(root.p_start, root.p_end);
    // The other boot modules (l4h 0021): handed over as device untypeds,
    // which retype without clearing.
    let mut extra_mods = 0;
    for i in 0..n_mods {
        let m = bi.modules[i];
        let start = m.paddr & !(PAGE - 1);
        let end = (m.paddr + m.size + PAGE - 1) & !(PAGE - 1);
        dev.add(start, end);
        mods[extra_mods] = (m.paddr, m.size);
        extra_mods += 1;
        kprintln!("FL4: boot module {}: {:#x} bytes at {:#x}", i, m.size, m.paddr);
    }

    // The extra BootInfo, in memory taken from the free RAM.
    let dtb_len = if bi.dtb != 0 { hw::dtb_size(bi.dtb) } else { 0 };
    let extra_size = EXTRA_FIXED + ((dtb_len + 16 + PAGE) & !(PAGE - 1));
    // Not over the device tree it copies (which may be in free memory).
    let mut pool = free;
    if dtb_len != 0 {
        pool.remove(bi.dtb & !(PAGE - 1), (bi.dtb + dtb_len + PAGE - 1) & !(PAGE - 1));
    }
    let extra_pa = match pool.take(extra_size) {
        Some(p) => p,
        None => fail("no memory for the extra BootInfo"),
    };
    free.remove(extra_pa, extra_pa + extra_size);
    let extra = unsafe { core::slice::from_raw_parts_mut(pptr(extra_pa) as *mut u8, extra_size as usize) };
    let extra_len = build_extra_bi(extra, &h, bi.dtb, dtb_len, bi, &mods[..extra_mods]);
    if has_option(bi, b"fb_console") {
        kprintln!("FL4: fb_console is not supported on AArch64");
    }

    let st = unsafe { &mut *STATICS.0.get() };
    let mut p = BootParams {
        free: [Region::EMPTY; MAX_REGIONS],
        n_free: 0,
        device: [Region::EMPTY; MAX_REGIONS],
        n_device: 0,
        ui_p_start: root.p_start,
        ui_p_end: root.p_end,
        pv_offset: root.p_start.wrapping_sub(root.v_start),
        v_entry: root.entry,
        extra_bi: extra.as_ptr() as u64,
        extra_bi_len: extra_len as u64,
        num_nodes: ncpus as u64,
        idle_base: st.idle.0.as_ptr() as u64,
        idle_stride: IDLE_STRIDE as u64,
    };
    // The largest free ranges, if there are more than BootParams holds.
    while free.n > MAX_REGIONS {
        let (mut k, mut best) = (0, u64::MAX);
        for j in 0..free.n {
            let l = free.r[j].end - free.r[j].start;
            if l < best {
                best = l;
                k = j;
            }
        }
        let r = free.r[k];
        free.remove(r.start, r.end);
    }
    for i in 0..free.n {
        p.free[i] = Region { start: pptr(free.r[i].start), end: pptr(free.r[i].end) };
        p.n_free += 1;
    }
    for i in 0..dev.n.min(MAX_REGIONS) {
        p.device[i] = dev.r[i];
        p.n_device += 1;
    }

    // The root task's image came from the loader through the data cache;
    // its instructions must reach instruction fetch.
    cpu::sync_icache(pptr(root.p_start), root.p_end - root.p_start);

    let ks_base = st.ks.0.as_ptr() as u64;
    entry::set_ks_base(ks_base);
    let mut s = entry::store();
    s.zero(ks_base, ks::SIZE);
    ks_set(&mut s, ks::KERNEL_ROOT, paging::empty_root());
    // Where a core goes when another retires the ASID it runs (mmu.rs).
    fl4_arch_aarch64::mmu::set_empty_root(paging::empty_root());
    let mut a = PhysArch;
    if let Err(e) = fl4_core::boot::create_root_task(&mut s, &mut a, &mut p) {
        let why = match e {
            fl4_core::boot::BootError::NoMemory => "not enough memory",
            fl4_core::boot::BootError::TooManyCaps => "root CNode too small",
        };
        kprintln!("FL4: creating the root task failed: {}", why);
        fail("root task");
    }
    kprintln!("FL4: starting the root task at {:#x}", root.entry);
    // With kernel printing disabled, the root task owns the UART page.
    if !fl4_abi::config::PRINTING {
        serial::release();
    }
    entry::lock();
    smp::release_aps();
    sched::schedule(&mut s, &mut a);
    sched::activate_thread(&mut s, &mut a);
    entry::exit()
}

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    kprintln!("FL4 panic: {}", info);
    entry::dump_trace();
    cpu::halt_forever()
}
