//! The FL4 kernel image for x86_64: boot (seL4 arch/x86/kernel/boot_sys.c
//! and boot.c) and the glue between fl4-core and the x86_64 backend.
#![no_std]

mod acpi;
mod entry;
mod gdt;
mod mb2;
mod mboot;
mod paging;
mod smp;
mod trace;

use core::cell::UnsafeCell;
use core::fmt::Write;
use fl4_arch_x86_64::arch::{PhysArch, TIMER_VECTOR};
use fl4_arch_x86_64::{apic, cpu, fbcon, fpu, ioapic, percpu, pic, serial, spec, timer, tlb};
use fl4_core::boot::{BootParams, Region, MAX_REGIONS, PADDR_USER_DEVICE_TOP};
use fl4_core::layout::{ks, pptr, PADDR_TOP};
use fl4_core::machine::Store;
use fl4_core::obj::ks_set;
use fl4_core::sched;

core::arch::global_asm!(include_str!("boot.S"), options(att_syntax));

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

extern "C" {
    static __kernel_end: u8;
}

const KERNEL_PHYS_START: u64 = 0x10_0000;
const HIGHMEM_PADDR: u64 = 0x10_0000;
const PAGE: u64 = 4096;

#[repr(C, align(64))]
struct KsArea([u8; ks::SIZE as usize]);

#[repr(C, align(4096))]
struct IdleArea([[u8; 8192]; percpu::MAX_CPUS]);

#[repr(C, align(8))]
struct ExtraBi([u8; 4096]);

struct Statics {
    ks: KsArea,
    idle: IdleArea,
    extra: ExtraBi,
    mods: KeptModules,
}

struct Cell(UnsafeCell<Statics>);
unsafe impl Sync for Cell {}

static STATICS: Cell = Cell(UnsafeCell::new(Statics {
    ks: KsArea([0; ks::SIZE as usize]),
    idle: IdleArea([[0; 8192]; percpu::MAX_CPUS]),
    extra: ExtraBi([0; 4096]),
    mods: KeptModules { n: 0, paddr: [0; mboot::MAX_MODULES], size: [0; mboot::MAX_MODULES] },
}));

fn fail(msg: &str) -> ! {
    kprintln!("FL4 boot failed: {}", msg);
    cpu::halt_forever()
}

/// A small sorted list of half-open physical ranges.
struct Ranges {
    r: [Region; 64],
    n: usize,
}

impl Ranges {
    const fn new() -> Ranges {
        Ranges { r: [Region::EMPTY; 64], n: 0 }
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
        // Merge overlapping or touching neighbours.
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
}

fn put_bytes(buf: &mut [u8], off: &mut usize, b: &[u8]) {
    buf[*off..*off + b.len()].copy_from_slice(b);
    *off += b.len();
}

/// Where the extra boot modules went, for BootInfo.
pub struct KeptModules {
    n: usize,
    paddr: [u64; mboot::MAX_MODULES],
    size: [u64; mboot::MAX_MODULES],
}

/// Copy modules 1.. to page-aligned memory from `start`, which lies above
/// every module; returns the end of the copies.
fn keep_modules(mb: &mboot::BootInfo, start: u64, ram: &Ranges, k: &mut KeptModules) -> u64 {
    let mut dst = start;
    k.n = 0;
    for i in 1..mb.n_modules {
        let m = mb.modules[i];
        let size = m.end - m.start;
        let end = dst + ((size + PAGE - 1) & !(PAGE - 1));
        if !(0..ram.n).any(|j| ram.r[j].start <= dst && end <= ram.r[j].end) {
            fail("no memory for the extra boot modules");
        }
        unsafe { core::ptr::copy_nonoverlapping(pptr(m.start) as *const u8, pptr(dst) as *mut u8, size as usize) };
        k.paddr[k.n] = dst;
        k.size[k.n] = size;
        k.n += 1;
        kprintln!("FL4: boot module {}: {:#x} bytes at {:#x}", i, size, dst);
        dst = end;
    }
    dst
}

/// Extra BootInfo records in the order seL4 writes them: ACPI RSDP,
/// Multiboot memory map, TSC frequency; then l4h's boot modules record.
fn build_extra_bi(buf: &mut [u8], a: &acpi::Info, mb: &mboot::BootInfo, k: &KeptModules) -> usize {
    let mut off = 0;
    let hdr = |buf: &mut [u8], off: &mut usize, id: u64, len: u64| {
        put_bytes(buf, off, &id.to_le_bytes());
        put_bytes(buf, off, &len.to_le_bytes());
    };
    hdr(buf, &mut off, 3, 16 + acpi::RSDP_LEN as u64);
    put_bytes(buf, &mut off, &a.rsdp);
    if let Some(f) = mb.fb {
        if f.addr != 0 {
            hdr(buf, &mut off, fl4_abi::consts::bootinfo_header::X86_FRAMEBUFFER, 16 + 22);
            put_bytes(buf, &mut off, &f.addr.to_le_bytes());
            put_bytes(buf, &mut off, &f.pitch.to_le_bytes());
            put_bytes(buf, &mut off, &f.width.to_le_bytes());
            put_bytes(buf, &mut off, &f.height.to_le_bytes());
            put_bytes(buf, &mut off, &[f.bpp, f.ty]);
        }
    }
    let mmap_size = 16 + 4 + 24 * mboot::MAX_MMAP;
    hdr(buf, &mut off, 2, mmap_size as u64);
    put_bytes(buf, &mut off, &((mb.n_mmap * 24) as u32).to_le_bytes());
    for i in 0..mboot::MAX_MMAP {
        let e = if i < mb.n_mmap { mb.mmap[i] } else { mboot::MemRegion::default() };
        put_bytes(buf, &mut off, &(if i < mb.n_mmap { 20u32 } else { 0 }).to_le_bytes());
        put_bytes(buf, &mut off, &e.base.to_le_bytes());
        put_bytes(buf, &mut off, &e.len.to_le_bytes());
        put_bytes(buf, &mut off, &e.ty.to_le_bytes());
    }
    hdr(buf, &mut off, 5, 20);
    put_bytes(buf, &mut off, &(timer::tsc_mhz() as u32).to_le_bytes());
    if k.n > 0 {
        // seL4_X86_BootModules_t: count, then (paddr, size, name[64]).
        hdr(buf, &mut off, fl4_abi::consts::bootinfo_header::X86_BOOT_MODULES, 16 + 8 + 80 * k.n as u64);
        put_bytes(buf, &mut off, &(k.n as u64).to_le_bytes());
        for i in 0..k.n {
            put_bytes(buf, &mut off, &k.paddr[i].to_le_bytes());
            put_bytes(buf, &mut off, &k.size[i].to_le_bytes());
            put_bytes(buf, &mut off, &mb.modules[i + 1].name);
        }
    }
    off
}

fn cpu_features() -> (bool, bool, bool) {
    let ext = cpu::cpuid(0x8000_0001, 0);
    let nx = ext.edx & (1 << 20) != 0;
    let l7 = cpu::cpuid(7, 0);
    let smep = l7.ebx & (1 << 7) != 0;
    let smap = l7.ebx & (1 << 20) != 0;
    (nx, smep, smap)
}

#[no_mangle]
pub extern "C" fn fl4_boot(magic: u32, info: u32) -> ! {
    serial::init();
    kprintln!("FL4: seL4 17.0 (MCS) API kernel, x86_64");
    let mb = match mboot::parse(magic, info as u64) {
        Some(b) => b,
        None => fail("no usable multiboot information"),
    };

    // CPU: paging features, our own page tables, descriptor tables, FPU.
    let (nx, smep, smap) = cpu_features();
    if nx {
        cpu::wrmsr(cpu::msr::EFER, cpu::rdmsr(cpu::msr::EFER) | (1 << 11));
    }
    let mut cr4 = cpu::read_cr4() | (1 << 7);
    if smep {
        cr4 |= 1 << 20;
    }
    if smap {
        cr4 |= 1 << 21;
    }
    if cpu::has_fsgsbase() {
        cr4 |= 1 << 16;
        cpu::set_fsgsbase(true);
    }
    spec::detect();
    cr4 |= tlb::init(spec::skim());
    // The bench profile lets user code read the performance counters.
    if fl4_abi::config::EXPORT_PMC_USER {
        cr4 |= 1 << 8;
    }
    cpu::write_cr4(cr4);
    let (kernel_root, window_top) = paging::init(nx, spec::skim());
    let stack_top = percpu::stack_top(0);
    gdt::init_idt();
    gdt::init_core(0, stack_top);
    cpu::init_pat();
    fpu::init();
    assert!(spec::init_core(true));
    assert!(fl4_arch_x86_64::vm::init(true));
    kprintln!("FL4: virtualization {}", match fl4_arch_x86_64::vm::backend() { 1 => "VT-x", 2 => "AMD-V", _ => "unavailable" });
    percpu::get().cr3.set(paging::root_paddr());
    if spec::skim() {
        entry::set_kernel_cr3(tlb::kernel_cr3(paging::root_paddr()));
    }

    // Interrupt controllers and the timer.
    let acpi = match acpi::init(mb.rsdp) {
        Some(a) => a,
        None => fail("no ACPI tables"),
    };
    pic::disable();
    let apic_base = apic::base_paddr();
    apic::enable(pptr(apic_base));
    apic::write(apic::REG_SVR, (1 << 8) | 0xff);
    apic::write(apic::REG_LVT_LINT0, 1 << 16);
    apic::write(apic::REG_LVT_LINT1, 1 << 16);
    apic::write(apic::REG_LVT_ERROR, 1 << 16);
    percpu::set_apic_id(apic::id());
    for i in 0..acpi.n_ioapics {
        ioapic::add(pptr(acpi.ioapics[i]));
    }
    timer::init(TIMER_VECTOR);
    kprintln!(
        "FL4: {} core(s), {} IOAPIC(s), {}, timer {} at {} MHz (from the {}), xcr0 {:#x} ({})",
        acpi.n_cpus,
        acpi.n_ioapics,
        if apic::is_x2apic() { "x2APIC" } else { "xAPIC" },
        if timer::deadline_mode() { "TSC-deadline" } else { "APIC one-shot" },
        timer::tsc_mhz(),
        timer::source(),
        fpu::xcr0(),
        fpu::save_insn()
    );
    kprintln!("FL4: speculation mitigations: {}; PCIDs {}", spec::describe(), if tlb::pcid() { "on" } else { "off" });

    // Read the boot loader's command line before the AP trampoline can
    // overwrite it.
    let fb_console = mboot::has_option(&mb, b"fb_console");

    // The other cores, if any (each sets itself up and waits).
    let ncpus = smp::start_aps(&acpi.cpus[..acpi.n_cpus], smp::Features { cr4: cpu::read_cr4(), efer_nx: nx });
    if ncpus > 1 {
        kprintln!("FL4: {} cores running", ncpus);
    }

    // The root task: the first module, loaded after everything else.
    if mb.n_modules == 0 {
        fail("no boot module (root task)");
    }
    let kernel_end = paging::image_paddr(unsafe { &__kernel_end as *const u8 as u64 });
    let mut mods_end = kernel_end;
    for i in 0..mb.n_modules {
        mods_end = mods_end.max(mb.modules[i].end);
    }
    let load = (mods_end + PAGE - 1) & !(PAGE - 1);
    let image = match mboot::load_elf(mb.modules[0].start, load) {
        Some(i) => i,
        None => fail("root task is not an x86_64 ELF image"),
    };

    // Memory: RAM above 1 MiB minus the kernel, modules and image is free;
    // everything that is not RAM goes to user space as device memory.
    let mut ram = Ranges::new();
    for i in 0..mb.n_mmap {
        let e = mb.mmap[i];
        if e.ty == 1 && e.base >= HIGHMEM_PADDR && e.len >= PAGE {
            let start = (e.base + PAGE - 1) & !(PAGE - 1);
            let end = (e.base + e.len) & !(PAGE - 1);
            ram.add(start, end.min(PADDR_TOP).min(window_top));
        }
    }
    let mut dev = Ranges::new();
    dev.add(0, PADDR_USER_DEVICE_TOP);
    for i in 0..ram.n {
        dev.remove(ram.r[i].start, ram.r[i].end);
    }
    dev.remove(apic_base, apic_base + PAGE);
    for i in 0..acpi.n_ioapics {
        dev.remove(acpi.ioapics[i], acpi.ioapics[i] + PAGE);
    }
    // The other modules (l4h 0021): copied above the image, out of the way
    // of everything, and handed over as device untypeds, which retype
    // without clearing.
    let st = unsafe { &mut *STATICS.0.get() };
    let mods = keep_modules(&mb, image.p_end, &ram, &mut st.mods);
    dev.add(image.p_end, mods);
    // The framebuffer console (l4h 0020), if asked for: never on RAM or low
    // memory (which holds the APs' boot code).
    if fb_console {
        let ok = match mb.fb {
            Some(f) => {
                let end = f.addr.saturating_add(f.pitch as u64 * f.height as u64);
                let on_ram = (0..ram.n).any(|j| f.addr < ram.r[j].end && ram.r[j].start < end);
                f.addr >= HIGHMEM_PADDR && !on_ram && fbcon::init(f.addr, f.pitch, f.width, f.height, f.bpp, f.ty)
            }
            None => false,
        };
        match mb.fb {
            Some(f) if !ok => kprintln!(
                "FL4: framebuffer not usable as a console ({}x{}, {} bpp, type {}, at {:#x})",
                f.width, f.height, f.bpp, f.ty, f.addr
            ),
            _ => kprintln!("FL4: {}", if ok { "console copied to the framebuffer" } else { "no framebuffer for the console" }),
        }
    }
    let mut free = ram;
    free.remove(KERNEL_PHYS_START, mods);

    let extra_len = build_extra_bi(&mut st.extra.0, &acpi, &mb, &st.mods);
    let mut p = BootParams {
        free: [Region::EMPTY; MAX_REGIONS],
        n_free: 0,
        device: [Region::EMPTY; MAX_REGIONS],
        n_device: 0,
        ui_p_start: image.p_start,
        ui_p_end: image.p_end,
        pv_offset: image.p_start.wrapping_sub(image.v_start),
        v_entry: image.entry,
        extra_bi: st.extra.0.as_ptr() as u64,
        extra_bi_len: extra_len as u64,
        num_nodes: ncpus as u64,
        idle_base: st.idle.0.as_ptr() as u64,
        idle_stride: 8192,
    };
    for i in 0..free.n.min(MAX_REGIONS) {
        p.free[i] = Region { start: pptr(free.r[i].start), end: pptr(free.r[i].end) };
        p.n_free += 1;
    }
    for i in 0..dev.n.min(MAX_REGIONS) {
        p.device[i] = dev.r[i];
        p.n_device += 1;
    }

    // Kernel state, then the root task.
    let ks_base = st.ks.0.as_ptr() as u64;
    entry::set_ks_base(ks_base);
    let mut s = entry::store();
    s.zero(ks_base, ks::SIZE);
    // The kernel half user address spaces copy: everything, or with the
    // skim window only the entry code and data (paging::init_skim).
    let template = if spec::skim() {
        paging::init_skim(nx)
    } else {
        kernel_root
    };
    ks_set(&mut s, ks::KERNEL_ROOT, template);
    ks_set(&mut s, ks::FEATURES, if nx { ks::FEATURE_NX } else { 0 });
    let mut a = PhysArch;
    if let Err(e) = fl4_core::boot::create_root_task(&mut s, &mut a, &mut p) {
        let why = match e {
            fl4_core::boot::BootError::NoMemory => "not enough memory",
            fl4_core::boot::BootError::TooManyCaps => "root CNode too small",
        };
        kprintln!("FL4: creating the root task failed: {}", why);
        fail("root task");
    }
    kprintln!("FL4: starting the root task at {:#x}", image.entry);
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
