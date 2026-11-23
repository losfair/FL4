//! The FL4 kernel image for x86_64: boot (seL4 arch/x86/kernel/boot_sys.c
//! and boot.c) and the glue between fl4-core and the x86_64 backend.
#![no_std]

mod acpi;
mod ap_order;
mod bootmem;
mod cvm_mmio;
mod cvm_walk;
mod dangerous_msr;
mod elf;
mod entry;
mod gdt;
mod mb2;
mod mboot;
mod paging;
mod smp;
mod snp;
mod tdx;
mod trace;
mod user_trap;

use core::cell::UnsafeCell;
use core::fmt::Write;
use fl4_arch_x86_64::arch::{PhysArch, TIMER_VECTOR};
use fl4_arch_x86_64::{apic, cpu, cvm, fbcon, fpu, ioapic, percpu, pic, serial, sev, spec, timer, tlb};
use bootmem::Ranges;
use fl4_core::boot::{BootParams, Region, MAX_REGIONS, PADDR_USER_DEVICE_TOP};
use fl4_core::layout::{ks, pptr};
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
/// An IOAPIC's registers: IOREGSEL and IOWIN.
const IOAPIC_WINDOW: u64 = 0x20;
/// The user address space the boot frames after the root task's image
/// take (boot.rs `root_layout`): the IPC buffer, the BootInfo frame, then
/// the extra BootInfo, which fl4-core rounds up to a power of two over
/// `ExtraBi`'s 4 KiB plus the l4h 0047 reservation (16 + 256 * 16 bytes),
/// so at most 16 KiB.
const IT_TAIL: u64 = 6 * PAGE;
/// Memory map entries the BootInfo record holds (libsel4
/// `SEL4_MULTIBOOT_MAX_MMAP_ENTRIES`).
const BI_MMAP: usize = 50;

/// Where the root task's image went.
struct Image {
    p_start: u64,
    p_end: u64,
    v_start: u64,
    entry: u64,
}

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
    dma_ram: Ranges,
    private_devices: Ranges,
    cvm_memory: cvm::Memory,
    /// RAM accepted at boot in a TDX guest, which the APs read while they
    /// help (`smp::accept_memory`).
    accepted: Ranges,
}

struct Cell(UnsafeCell<Statics>);
unsafe impl Sync for Cell {}

static STATICS: Cell = Cell(UnsafeCell::new(Statics {
    ks: KsArea([0; ks::SIZE as usize]),
    idle: IdleArea([[0; 8192]; percpu::MAX_CPUS]),
    extra: ExtraBi([0; 4096]),
    dma_ram: Ranges::new(),
    private_devices: Ranges::new(),
    cvm_memory: cvm::Memory { ram: &[], private_devices: &[] },
    accepted: Ranges::new(),
    mods: KeptModules { n: 0, paddr: [0; mboot::MAX_MODULES], size: [0; mboot::MAX_MODULES] },
}));

fn fail(msg: &str) -> ! {
    kprintln!("FL4 boot failed: {}", msg);
    cpu::halt_forever()
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
        if !ram.contains(dst, end) {
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
/// Multiboot memory map, TSC frequency; then l4h's boot modules record,
/// the TPM and confidential-computing event logs, and the TDX guest's facts.
fn build_extra_bi(buf: &mut [u8], a: &acpi::Info, mb: &mboot::BootInfo, k: &KeptModules, tpm: Option<mboot::EventLog>, cc: Option<mboot::EventLog>) -> usize {
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
    // The record has libsel4's fixed size: the first `BI_MMAP` entries.
    let n_mmap = mb.n_mmap.min(BI_MMAP);
    let mmap_size = 16 + 4 + 24 * BI_MMAP;
    hdr(buf, &mut off, 2, mmap_size as u64);
    put_bytes(buf, &mut off, &((n_mmap * 24) as u32).to_le_bytes());
    for i in 0..BI_MMAP {
        let e = if i < n_mmap { mb.mmap[i] } else { mboot::MemRegion::default() };
        put_bytes(buf, &mut off, &(if i < n_mmap { 20u32 } else { 0 }).to_le_bytes());
        put_bytes(buf, &mut off, &e.base.to_le_bytes());
        put_bytes(buf, &mut off, &e.len.to_le_bytes());
        put_bytes(buf, &mut off, &e.ty.to_le_bytes());
    }
    hdr(buf, &mut off, 5, 20);
    put_bytes(buf, &mut off, &(timer::tsc_mhz() as u32).to_le_bytes());
    if cvm::active() {
        hdr(buf, &mut off, fl4_abi::consts::bootinfo_header::SHARED_DMA, 16);
    }
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
    if let Some(t) = tpm {
        // seL4_TpmEventLog: paddr, size, flags.
        hdr(buf, &mut off, fl4_abi::consts::bootinfo_header::TPM_EVENT_LOG, 16 + 24);
        put_bytes(buf, &mut off, &t.paddr.to_le_bytes());
        put_bytes(buf, &mut off, &t.size.to_le_bytes());
        put_bytes(buf, &mut off, &t.flags.to_le_bytes());
    }
    if let Some(t) = cc {
        // seL4_CcEventLog: paddr, size, flags.
        hdr(buf, &mut off, fl4_abi::consts::bootinfo_header::CC_EVENT_LOG, 16 + 24);
        put_bytes(buf, &mut off, &t.paddr.to_le_bytes());
        put_bytes(buf, &mut off, &t.size.to_le_bytes());
        put_bytes(buf, &mut off, &t.flags.to_le_bytes());
    }
    if fl4_arch_x86_64::tdx::active() {
        // seL4_X86_TdxInfo: gpaw, attributes, td_ctls, num_vcpus, max_vcpus.
        hdr(buf, &mut off, fl4_abi::consts::bootinfo_header::TDX_INFO, 16 + 40);
        for v in fl4_arch_x86_64::tdx::boot_info() {
            put_bytes(buf, &mut off, &v.to_le_bytes());
        }
    }
    // l4h 0047: the kernel appends the extra untyped chunk with word
    // writes, so end on a word boundary. The records above come to at most
    // 2146 bytes, so these at most 23 fit in `ExtraBi` too.
    if off % 8 != 0 {
        let pad = 8 - off % 8;
        hdr(buf, &mut off, fl4_abi::consts::bootinfo_header::PADDING, (16 + pad) as u64);
        put_bytes(buf, &mut off, &[0u8; 8][..pad]);
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
pub extern "C" fn fl4_boot(magic: u32, info: u32, private_mask: u64, cpuid_page: u64, delta: u64) -> ! {
    paging::set_image_delta(delta);
    // An SNP guest's CPUID takes #VC, which has no handler yet; SEV and SNP
    // are never TDX.
    let td = if private_mask == 0 && cpuid_page == 0 { fl4_arch_x86_64::tdx::probe() } else { None };
    cvm::init(private_mask, td.map_or(0, |t| t.shared_mask));
    if let Some(t) = td {
        gdt::load_boot_ve();
        fl4_arch_x86_64::tdx::init(t);
    }
    if cpuid_page != 0 {
        gdt::load_boot_vc();
        snp::init(cpuid_page);
    }
    serial::init();
    kprintln!("FL4: seL4 17.0 (MCS) API kernel, x86_64");
    if private_mask != 0 {
        let technology = if sev::snp::active() { "SEV-SNP" } else { "SEV" };
        kprintln!("FL4: AMD {} guest, C-bit {}", technology, private_mask.trailing_zeros());
    }
    if let Some(t) = td {
        kprintln!("FL4: Intel TDX guest, GPAW {}, {} of {} vCPUs", t.gpaw, t.num_vcpus, t.max_vcpus);
    }
    let mb = match mboot::parse(magic, info as u64) {
        Some(b) => b,
        None => fail("no usable multiboot information"),
    };
    // What a cut-short map left out could be RAM or firmware memory, which
    // would become user space's device memory.
    if mb.mmap_lost {
        fail("more memory map entries than the kernel keeps");
    }

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
    // In a TD only with the PERFMON attribute.
    if fl4_abi::config::EXPORT_PMC_USER && td.is_none_or(|t| fl4_arch_x86_64::tdx::user_pmc_allowed(t.attributes)) {
        cr4 |= 1 << 8;
    }
    cpu::write_cr4(cr4);
    let gpa_top = cvm::gpa_top(cpu::max_paddr(), cvm::private_mask() | cvm::shared_mask());
    // 1 GiB pages, read once: the window, the other cores and user
    // mappings all go by this (paging::init).
    let huge = cpu::has_1g_pages();
    let (kernel_root, window_top) = paging::init(nx, spec::skim(), gpa_top, huge);
    let stack_top = percpu::stack_top(0);
    gdt::init_idt();
    gdt::init_core(0, stack_top);
    cpu::init_pat();
    assert!(fpu::init(true));
    assert!(spec::init_core(true));
    assert!(fl4_arch_x86_64::vm::init(true));
    // VM-only SMT parking, before `describe` and AP startup.
    spec::commit_vm(fl4_arch_x86_64::vm::backend() != 0);
    kprintln!("FL4: virtualization {}", match fl4_arch_x86_64::vm::backend() { 1 => "VT-x", 2 => "AMD-V", _ => "unavailable" });
    percpu::get().cr3.set(paging::root_paddr());
    if spec::skim() {
        entry::set_kernel_cr3(tlb::kernel_cr3(paging::root_paddr()));
    }

    // Interrupt controllers and the timer.
    let acpi = match acpi::init(mb.rsdp, window_top) {
        Some(a) => a,
        None => fail("no ACPI tables"),
    };
    // A TD has no PIC: its ports are the VMM's.
    if td.is_none() {
        pic::disable();
    }
    let apic_base = apic::enable(true, window_top).unwrap_or_else(|| fail("local APIC outside the physical window"));
    apic::write(apic::REG_SVR, (1 << 8) | 0xff);
    apic::write(apic::REG_LVT_LINT0, 1 << 16);
    apic::write(apic::REG_LVT_LINT1, 1 << 16);
    apic::write(apic::REG_LVT_ERROR, 1 << 16);
    percpu::set_apic_id(apic::id());
    // Every IOAPIC's registers stay out of user space's device memory, so
    // the kernel must know them all, even those past what it drives.
    if acpi.ioapics_lost {
        fail("more IOAPICs than the kernel can keep from user space");
    }
    if acpi.n_ioapics > ioapic::MAX_IOAPICS {
        kprintln!("FL4: {} IOAPICs: only the first {} are used", acpi.n_ioapics, ioapic::MAX_IOAPICS);
    }
    for i in 0..acpi.n_ioapics.min(ioapic::MAX_IOAPICS) {
        let addr = cvm::mmio_ptr(acpi.ioapics[i], IOAPIC_WINDOW, window_top)
            .unwrap_or_else(|| fail("IOAPIC outside the physical window"));
        ioapic::add(addr);
    }
    timer::init(TIMER_VECTOR);
    kprintln!(
        "FL4: {} core(s), {} IOAPIC(s), {}, timer {} at {} MHz (from the {}), xcr0 {:#x} ({})",
        acpi.n_cpus,
        ioapic::count(),
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

    // The top of the physical memory user space can map (device memory,
    // below) and of the kernel window: every core must address it.
    let device_top = bootmem::top(&[PADDR_USER_DEVICE_TOP, gpa_top]);
    // The MADT names the mailbox, and the VMM writes the MADT: use it only
    // if the memory map says it is firmware's.
    let mailbox = acpi.mp_wakeup_mailbox.filter(|&m| {
        bootmem::mailbox_ok(m, window_top, mb.mmap[..mb.n_mmap].iter().map(|e| (e.base, e.len, e.ty)))
    });
    let tdx_wakeup = if td.is_some() {
        mb.tdx_ap_page.zip(mailbox).map(|(page, mailbox)| tdx::Wakeup { page, mailbox })
    } else {
        None
    };
    if td.is_some() && tdx_wakeup.is_none() {
        let mmap_ty = acpi.mp_wakeup_raw.and_then(|(_, _, m)| {
            bootmem::mmap_type_of(m, mb.mmap[..mb.n_mmap].iter().map(|e| (e.base, e.len, e.ty)))
        });
        kprintln!(
            "FL4: no usable TDX AP wakeup mailbox (ap_page {:x?}, madt (ver, len, mailbox) {:x?}, mmap_ty {:x?}); using one core",
            mb.tdx_ap_page, acpi.mp_wakeup_raw, mmap_ty
        );
    }
    // The other cores, if any (each sets itself up and waits). Each walks
    // the boot core's tables, and the 1 GiB pages and addresses in them.
    let ncpus = smp::start_aps(&acpi.cpus[..acpi.n_cpus], smp::Features { cr4: cpu::ap_boot_cr4(cpu::read_cr4()), efer_nx: nx, window_top, huge, paddr_top: device_top, tdx_wakeup });
    if ncpus > 1 {
        kprintln!("FL4: {} cores running", ncpus);
    }

    // Memory: RAM above 1 MiB minus the kernel, modules and image is free;
    // everything that is not RAM goes to user space as device memory.
    // RAM stops at the kernel window's mapped top: the kernel reaches it
    // through the window. Device memory goes on to PADDR_USER_DEVICE_TOP,
    // as in seL4 (firmware places 64-bit BARs far above the 510 GiB
    // window): the kernel never touches it, and a device untyped's
    // pointer is only its physical address plus PPTR_BASE, wrapping to
    // the lower half from 512 GiB on. Over [510 GiB, 512 GiB) it has the
    // values of the kernel image's addresses, the names of the kernel's
    // statics: fl4-core's `create_device_untypeds` leaves out the image's
    // part (BootParams::kernel_image).
    // Nothing goes past what the CPU can address either (MAXPHYADDR): a
    // mapping of it would set reserved bits in a paging, EPT or NPT entry
    // (`device_top`, above, which every core must reach).
    let mut ram = bootmem::ram(mb.mmap[..mb.n_mmap].iter().map(|e| (e.base, e.len, e.ty)), HIGHMEM_PADDR, window_top);
    // A TDX guest's unaccepted RAM joins it, accepted on all cores. Past
    // the window it stays unaccepted, and out of device memory below.
    if td.is_some() {
        let accepted = bootmem::unaccepted(mb.mmap[..mb.n_mmap].iter().map(|e| (e.base, e.len, e.ty)), HIGHMEM_PADDR, window_top);
        if accepted.lost {
            fail("more unaccepted memory ranges than the kernel keeps");
        }
        let st = unsafe { &mut *STATICS.0.get() };
        st.accepted = accepted;
        let list: &'static [Region] = &st.accepted.r[..st.accepted.n];
        smp::accept_memory(list);
        for r in list {
            ram.add(r.start, r.end);
        }
    }
    if ram.lost {
        fail("more RAM ranges than the kernel keeps");
    }

    // The root task: the first module, loaded into RAM above everything
    // else (seL4 `load_boot_module`).
    if mb.n_modules == 0 {
        fail("no boot module (root task)");
    }
    let kernel_end = paging::image_paddr(unsafe { &__kernel_end as *const u8 as u64 });
    let mut mods_end = kernel_end;
    for i in 0..mb.n_modules {
        mods_end = mods_end.max(mb.modules[i].end);
    }
    // The event logs stay where the loader put them until they are copied:
    // the root task does not load over them.
    for t in [mb.tpm_log, mb.cc_log].into_iter().flatten() {
        mods_end = mods_end.max(t.paddr + t.size);
    }
    let mods_end = (mods_end + PAGE - 1) & !(PAGE - 1);
    let m0 = mb.modules[0];
    let layout = match elf::check(m0.start, m0.end - m0.start, fl4_abi::consts::USER_TOP + 1 - IT_TAIL) {
        Some(l) => l,
        None => fail("root task is not a loadable x86_64 ELF image"),
    };
    let log_bytes = |l: Option<mboot::EventLog>| l.map_or(0, |t| t.size.div_ceil(PAGE) * PAGE);
    let image_bytes = layout.size() + mb.modules[1..mb.n_modules].iter()
        .map(|m| (m.end - m.start).div_ceil(PAGE) * PAGE).sum::<u64>() + log_bytes(mb.tpm_log) + log_bytes(mb.cc_log);
    let load = match ram.find(mods_end, image_bytes).or_else(|| {
        // EFI allocates the handoff as a unit and may put it at the top
        // of the last usable range. Search below it as well.
        if delta == 0 { return None; }
        ram.find_below(HIGHMEM_PADDR, image_bytes, KERNEL_PHYS_START + delta)
    }) {
        Some(p) => p,
        None => fail("no memory for the root task"),
    };
    elf::load(m0.start, &layout, load);
    let image = Image { p_start: load, p_end: load + layout.size(), v_start: layout.v_start, entry: layout.entry };

    // Device memory never covers the kernel's image and statics, the boot
    // modules or the root task, whatever the memory map says about them
    // (a loader may report its own allocations as reserved).
    let reserved = [(KERNEL_PHYS_START + delta, mods_end), (image.p_start, image.p_end), (apic_base, apic_base + PAGE)];
    let ioapics = acpi.ioapics[..acpi.n_ioapics].iter().map(|&b| (b, b + IOAPIC_WINDOW));
    let mut dev = bootmem::device(&ram, device_top, reserved.into_iter().chain(ioapics));
    // RAM not accepted (a TDX guest's past the window, or any other guest's)
    // is no device: an access through a device cap would fault in the guest.
    for e in &mb.mmap[..mb.n_mmap] {
        if e.ty == bootmem::UNACCEPTED {
            dev.remove(e.base & !(PAGE - 1), e.base.saturating_add(e.len).saturating_add(PAGE - 1) & !(PAGE - 1));
        }
    }
    // The wakeup mailbox stays the firmware's and the kernel's.
    if let Some(w) = tdx_wakeup {
        dev.remove(w.mailbox, w.mailbox + PAGE);
    }
    // The framebuffer console (l4h 0020), if asked for: only on device
    // memory as it is before the modules join it, so never on RAM, the
    // kernel's image and statics, the boot modules, the root task or the
    // APIC and IOAPIC registers (a loader may report any of them as
    // reserved), nor in low memory (which holds the APs' boot code).
    let fb_ok = |f: &mboot::Framebuffer| {
        f.addr >= HIGHMEM_PADDR
            && f.addr.checked_add(f.pitch as u64 * f.height as u64).is_some_and(|end| dev.contains(f.addr, end))
    };
    let fb = mb.fb.filter(|f| fb_console && fb_ok(f));
    // The other modules (l4h 0021): copied above the image, out of the way
    // of everything, and handed over as device untypeds, which retype
    // without clearing.
    let st = unsafe { &mut *STATICS.0.get() };
    let mods = keep_modules(&mb, image.p_end, &ram, &mut st.mods);
    // The event logs after them, the same way (the root task reads them
    // from device untypeds, which keep their bytes).
    let keep_log = |log: Option<mboot::EventLog>, dst: u64, what: &str| {
        let t = log?;
        let end = dst + t.size.div_ceil(PAGE) * PAGE;
        if !ram.contains(dst, end) {
            kprintln!("FL4: no memory for the {} event log: not passed on", what);
            return None;
        }
        unsafe { core::ptr::copy_nonoverlapping(pptr(t.paddr) as *const u8, pptr(dst) as *mut u8, t.size as usize) };
        // The rest of the last page goes to user space too: no old RAM.
        unsafe { core::ptr::write_bytes(pptr(dst + t.size) as *mut u8, 0, (end - dst - t.size) as usize) };
        kprintln!("FL4: {} event log: {:#x} bytes at {:#x}", what, t.size, dst);
        Some(mboot::EventLog { paddr: dst, ..t })
    };
    let tpm_log = keep_log(mb.tpm_log, mods, "TPM");
    let cc_start = tpm_log.map_or(mods, |t| mods + t.size.div_ceil(PAGE) * PAGE);
    let cc_log = keep_log(mb.cc_log, cc_start, "CC");
    let log_end = cc_log.map_or(cc_start, |t| cc_start + t.size.div_ceil(PAGE) * PAGE);
    if cvm::hardened() {
        // Keep usable RAM and ACPI NVS (including the SNP secrets)
        // out of device caps. Root reads ACPI tables in reclaim memory
        // through private device frames, which retain the encryption bit.
        for e in &mb.mmap[..mb.n_mmap] {
            if matches!(e.ty, 1 | 4) {
                dev.remove(e.base & !(PAGE - 1), e.base.saturating_add(e.len).saturating_add(PAGE - 1) & !(PAGE - 1));
            }
        }
    }
    dev.add(image.p_end, log_end);
    if fb_console {
        let ok = match fb {
            Some(f) => fbcon::init(f.addr, window_top, f.pitch, f.width, f.height, f.bpp, f.ty),
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
    free.remove(KERNEL_PHYS_START + delta, mods_end);
    free.remove(image.p_start, log_end);

    let extra_len = build_extra_bi(&mut st.extra.0, &acpi, &mb, &st.mods, tpm_log, cc_log);
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
        kernel_image: Region { start: paging::KERNEL_OFFSET, end: unsafe { &__kernel_end as *const u8 as u64 } },
    };
    for i in 0..free.n.min(MAX_REGIONS) {
        p.free[i] = Region { start: pptr(free.r[i].start), end: pptr(free.r[i].end) };
        p.n_free += 1;
    }
    // BootParams holds MAX_REGIONS free ranges: say what the rest held.
    if free.n > MAX_REGIONS {
        let lost = &free.r[MAX_REGIONS..free.n];
        let bytes: u64 = lost.iter().map(|r| r.end - r.start).sum();
        kprintln!("FL4: {} free RAM region(s) ({:#x} bytes) exceed the boot range limit", lost.len(), bytes);
    }
    // At most one interval per firmware entry and one for the kept modules.
    // Keep every private boundary even if BootParams can export fewer ranges.
    let mut firmware = bootmem::RangeList::<{ mboot::MAX_MMAP + 1 }>::new();
    if cvm::active() {
        firmware.add(image.p_end, log_end);
        for e in &mb.mmap[..mb.n_mmap] {
            if e.len != 0 && matches!(e.ty, 1 | 3 | 4) {
                let start = e.base & !(PAGE - 1);
                let end = e.base.saturating_add(e.len).saturating_add(PAGE - 1) & !(PAGE - 1);
                firmware.add(start, end);
            }
        }
    }
    let mut omitted = 0;
    let mut omitted_boot_data = false;
    bootmem::device_regions(&dev.r[..dev.n], &firmware.r[..firmware.n], |r, private| {
        if let Some(slot) = p.device.get_mut(p.n_device as usize) {
            *slot = r;
            p.n_device += 1;
            if private { st.private_devices.add(r.start, r.end); }
        } else {
            omitted += 1;
            // The boot modules and event logs reach the root task only as
            // these device untypeds.
            if r.start < log_end && image.p_end < r.end {
                omitted_boot_data = true;
            }
        }
    });
    if omitted != 0 { kprintln!("FL4: {} device memory regions exceed the boot range limit", omitted); }
    if omitted_boot_data {
        fail("boot modules or event logs exceed the boot device range limit");
    }
    if let Some(w) = tdx_wakeup {
        st.private_devices.add(w.mailbox, w.mailbox + PAGE);
    }
    // A private boundary left out would hand private memory over as shared.
    if firmware.lost || st.private_devices.lost {
        fail("more firmware memory ranges than the kernel keeps");
    }
    if cvm::active() {
        st.dma_ram = free;
        st.cvm_memory = cvm::Memory {
            ram: &st.dma_ram.r[..st.dma_ram.n],
            private_devices: &st.private_devices.r[..st.private_devices.n],
        };
        cvm::install(&st.cvm_memory);
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
    // Where a core goes when another deletes the ASID it runs (tlb.rs).
    tlb::set_kernel_root(template.wrapping_sub(fl4_core::layout::PPTR_BASE));
    ks_set(&mut s, ks::FEATURES, if nx { ks::FEATURE_NX } else { 0 } | if huge { ks::FEATURE_HUGE_PAGES } else { 0 });
    let mut a = PhysArch;
    if let Err(e) = fl4_core::boot::create_root_task(&mut s, &mut a, &mut p) {
        let why = match e {
            fl4_core::boot::BootError::NoMemory => "not enough memory",
            fl4_core::boot::BootError::TooManyCaps => "root CNode too small",
            fl4_core::boot::BootError::TooManyUntypeds => "too many untyped regions",
        };
        kprintln!("FL4: creating the root task failed: {}", why);
        fail("root task");
    }
    match spec::finish_native_entry_policy(entry::patch_return_thunk) {
        Some(false) => kprintln!("FL4: native entry uses AutoIBRS and Safe RET"),
        Some(true) => kprintln!("FL4: native entry uses retpolines and Safe RET"),
        None => {}
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
    if cvm::hardened() {
        cvm::terminate(0);
    }
    cpu::halt_forever()
}
