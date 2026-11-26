//! The FL4 kernel image for AArch64 (DESIGN.md §11): boot from FL4's UEFI
//! loader (fl4-efi), and the glue between fl4-core and the AArch64
//! backend. One image for every UEFI platform: the hardware comes from
//! ACPI or the device tree at boot.
#![no_std]

mod bootmem;
mod entry;
mod extra_bi;
mod hw;
mod paging;
mod smp;

use core::cell::UnsafeCell;
use core::fmt::Write;
use fl4_arch_aarch64::arch::PhysArch;
use bootmem::Ranges;
use fl4_arch_aarch64::{cpu, fpu, gic, kconfig, percpu, serial, timer};
use fl4_bootinfo::{BootInfo, KERNEL_VBASE, MAGIC};
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
/// Bytes of the console UART the kernel maps from the base the tables give.
const UART_MAP: u64 = 0x1000;
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

/// The extra BootInfo records (`extra_bi::build`): the ACPI RSDP, the
/// boot core's ID registers, virtualization info, the boot modules, the
/// TPM event log and the device tree.
fn build_extra_bi(buf: &mut [u8], h: &hw::Hw, dtb: u64, dtb_len: u64, mods: &[fl4_bootinfo::Module], tpm: Option<&extra_bi::TpmEventLog>, msi: Option<&fl4_arch_aarch64::its::Info>) -> usize {
    let regs = [
        fl4_arch_aarch64::mrs!("id_aa64isar0_el1"),
        fl4_arch_aarch64::mrs!("id_aa64isar1_el1"),
        fl4_arch_aarch64::mrs!("s3_0_c0_c6_2"), // ID_AA64ISAR2_EL1
        fl4_arch_aarch64::mrs!("id_aa64pfr0_el1"),
        fl4_arch_aarch64::mrs!("id_aa64pfr1_el1"),
    ];
    let mut flags = 0u64;
    if fl4_arch_aarch64::arch::virt_ready() {
        flags |= fl4_abi::consts::virt_info_flag::VIRT_READY;
    }
    if cpu::is_el2_vhe() {
        flags |= fl4_abi::consts::virt_info_flag::EL2_VHE;
    }
    if cpu::has_el2() && cpu::vmid16() {
        flags |= fl4_abi::consts::virt_info_flag::VMID16;
    }
    if cpu::is_el2_nvhe() {
        flags |= fl4_abi::consts::virt_info_flag::EL2_NVHE;
    }
    let gicv_size = if h.gicv != 0 {
        if h.gicv_len != 0 { h.gicv_len } else { 0x2000 }
    } else {
        0
    };
    let virt_info = extra_bi::VirtInfo {
        flags,
        ipa_bits: fl4_arch_aarch64::mmu::s2_ipa_bits(),
        gic_version: h.gic_version,
        vgic_vtr: gic::vgic_vtr(),
        gicv_paddr: h.gicv,
        gicv_size,
        midr_el1: fl4_arch_aarch64::mrs!("midr_el1"),
        ctr_el0: fl4_arch_aarch64::mrs!("ctr_el0"),
        id_aa64mmfr0_el1: fl4_arch_aarch64::mrs!("id_aa64mmfr0_el1"),
        id_aa64mmfr1_el1: fl4_arch_aarch64::mrs!("id_aa64mmfr1_el1"),
        id_aa64mmfr2_el1: fl4_arch_aarch64::mrs!("s3_0_c0_c7_2"),
        id_aa64dfr0_el1: fl4_arch_aarch64::mrs!("id_aa64dfr0_el1"),
        id_aa64dfr1_el1: fl4_arch_aarch64::mrs!("id_aa64dfr1_el1"),
    };
    let src: &[u8] = if dtb_len != 0 { unsafe { core::slice::from_raw_parts(pptr(dtb) as *const u8, dtb_len as usize) } } else { &[] };
    let rsdp = if h.has_rsdp { Some(&h.rsdp[..]) } else { None };
    let msi = msi.map(|m| [m.doorbell, m.num_lpis, m.num_events, m.num_devices]);
    match extra_bi::build(buf, rsdp, &regs, Some(&virt_info), mods, tpm, msi.as_ref(), src) {
        Some(len) => len,
        None => fail("extra BootInfo too large"),
    }
}

/// The loader's TPM event log, if it is one the kernel can hand over: page
/// aligned, at most `MAX_TPM_LOG` bytes, inside free RAM (`usable`) and
/// clear of the kernel region, the root task image and the boot modules.
/// Anything else is ignored: a missing log never stops the boot.
fn tpm_log(bi: &BootInfo, usable: &Ranges, n_mods: usize) -> Option<extra_bi::TpmEventLog> {
    if bi.tpm_log_paddr == 0 {
        return None;
    }
    let (start, size) = (bi.tpm_log_paddr, bi.tpm_log_size);
    // The size is checked before it is rounded (no overflow).
    let end = if size == 0 || size > fl4_bootinfo::MAX_TPM_LOG || start % PAGE != 0 {
        None
    } else {
        start.checked_add(size.div_ceil(PAGE) * PAGE)
    };
    let Some(end) = end else {
        kprintln!("FL4: TPM event log at {:#x} ({:#x} bytes) out of range: ignored", start, size);
        return None;
    };
    let apart = |s: u64, e: u64| end <= s || e <= start;
    let root = bi.root;
    let clear = apart(bi.region_paddr, bi.region_paddr + bi.region_len)
        && apart(root.p_start, root.p_end)
        && bi.modules[..n_mods].iter().all(|m| apart(m.paddr & !(PAGE - 1), (m.paddr + m.size + PAGE - 1) & !(PAGE - 1)));
    let in_ram = usable.r[..usable.n].iter().any(|r| r.start <= start && end <= r.end);
    if !clear || !in_ram {
        kprintln!("FL4: TPM event log at {:#x} overlaps boot memory or is not free RAM: ignored", start);
        return None;
    }
    Some(extra_bi::TpmEventLog { paddr: start, size, flags: bi.tpm_log_flags })
}

/// Whether `[start, end)` meets any range of `r`.
fn overlaps(r: &Ranges, start: u64, end: u64) -> bool {
    r.r[..r.n].iter().any(|x| x.start < end && start < x.end)
}

fn has_option(bi: &BootInfo, opt: &[u8]) -> bool {
    fl4_bootinfo::has_option(&bi.cmdline, opt)
}

extern "C" {
    static __kernel_end: u8;
}

#[no_mangle]
pub extern "C" fn fl4_boot(off: u64, el_mode: u64) -> ! {
    let bi = unsafe { &*((KERNEL_VBASE + off) as *const BootInfo) };
    if bi.magic != MAGIC || bi.version != fl4_bootinfo::VERSION {
        cpu::halt_forever();
    }
    cpu::init_el_mode(el_mode);
    let pa_top = (1u64 << cpu::pa_bits()).min(PADDR_USER_DEVICE_TOP);

    // RAM in the window: everything the memory map calls write-back memory.
    // Free RAM past the window (all_usable) is neither handed out as
    // free memory nor as device memory (`dev` below).
    let bootmem::MemLists { ram, usable, mut zeroed, all_usable } =
        bootmem::classify(&bi.mmap[..(bi.n_mmap as usize).min(fl4_bootinfo::MAX_MMAP)], PADDR_TOP, pa_top);
    if zeroed.lost {
        zeroed = Ranges::new();
    }
    // RAM a full list left out would go to user space as device memory,
    // or be handed out as free memory the window does not map.
    if ram.lost || usable.lost || all_usable.lost {
        fail("too many memory map ranges");
    }
    let mib = |r: &Ranges| r.r[..r.n].iter().map(|x| x.end - x.start).sum::<u64>() >> 20;
    // Printed once there is a console.
    let ram_report = (mib(&usable), usable.n, mib(&all_usable) - mib(&usable), bi.n_mmap);
    let mut window = [(0u64, 0u64); bootmem::MAX_RANGES];
    for i in 0..ram.n {
        window[i] = (ram.r[i].start, ram.r[i].end);
    }
    let ttbr1 = paging::init(bi.region_paddr, bi.region_len, &window[..ram.n], pa_top);
    paging::activate(ttbr1);
    // What a new ArmHighVSpace copies: the tables themselves, read when it
    // is made, so the device mappings made below are in them too.
    let (kl0, kl1) = paging::kernel_tables();
    fl4_arch_aarch64::mmu::set_kernel_ttbr1(ttbr1, kl0, kl1);
    cpu::init_pauth();
    if cpu::is_el2_nvhe() {
        fl4_arch_aarch64::hyp_nvhe::init_core(
            0,
            paging::hyp_ttbr0(),
            paging::image_pa(fl4_arch_aarch64::hyp_nvhe::hyp_vectors_va()),
            paging::image_pa(fl4_arch_aarch64::hyp_nvhe::hyp_cpu_va(0)),
        );
    }
    fl4_arch_aarch64::mmu::set_empty_s2_root(paging::empty_s2_root_pa());
    percpu::init(0);
    smp::init_core_regs();

    // The hardware and the console.
    let h = match hw::discover(bi.rsdp, bi.dtb) {
        Some(h) => h,
        None => cpu::halt_forever(),
    };
    // A UART the tables put where the kernel cannot map it as a device
    // (past the physical address size, or in RAM), misaligned for its
    // registers, or in a range too small for them, is no console.
    let pa_limit = 1u64 << cpu::pa_bits();
    let uart_ok = match h.uart_kind {
        serial::KIND_NONE => false,
        k => {
            let pl011 = k == serial::KIND_PL011;
            let min_len = if pl011 { 0x40 } else { 8 << h.uart_shift };
            let aligned = !(pl011 || h.uart_wide) || h.uart_base & 3 == 0;
            aligned
                && (h.uart_len == 0 || h.uart_len >= min_len)
                && h.uart_base.checked_add(h.uart_len.max(0x1000)).is_some_and(|e| e <= pa_limit)
        }
    };
    let uart = if uart_ok { paging::map_device(h.uart_base, UART_MAP) } else { None };
    if let Some(base) = uart {
        serial::init(h.uart_kind, base, h.uart_shift, h.uart_wide);
    }
    kprintln!("FL4: seL4 17.0 (MCS) API kernel, AArch64");
    kprintln!("FL4: hardware from the {}: GICv{}, {} core(s), console {} at {:#x}", h.source, h.gic_version, h.n_cpus,
        match h.uart_kind { serial::KIND_PL011 => "PL011", serial::KIND_16550 => "16550", _ => "none" }, h.uart_base);
    kprintln!("FL4: {} MiB of free RAM in {} range(s) ({} MiB past the window), {} map entries",
        ram_report.0, ram_report.1, ram_report.2, ram_report.3);
    if !cpu::has_asid16() {
        fail("16-bit ASIDs are required (l4h 0016)");
    }
    match cpu::el_mode() {
        cpu::ElMode::El2Vhe => {
            if h.hyptimer != 0 && h.hyptimer != fl4_core::layout::irq::HYP_TIMER_ID {
                fail("the EL2 physical timer is not PPI 26");
            }
        }
        cpu::ElMode::El2Nvhe => {
            if h.ptimer != 0 && h.ptimer != fl4_core::layout::irq::PHYS_TIMER_ID {
                fail("the EL1 physical timer is not PPI 30");
            }
        }
        cpu::ElMode::El1 => {
            if h.vtimer != 0 && h.vtimer != fl4_core::layout::irq::TIMER_ID {
                fail("the EL1 virtual timer is not PPI 27");
            }
        }
    }
    if h.gicd == 0 {
        fail("no GIC distributor");
    }
    let (gicd_map, gicd_len) = match fl4_arch_aarch64::gic_layout::gicd_extent(h.gic_version, h.gicd, h.gicd_len, pa_limit) {
        Some(e) => e,
        None => fail("bad GIC distributor range"),
    };
    // A redistributor left out of the tables' count would go to user
    // space as device memory.
    if h.gicr_lost {
        fail("more GIC redistributors than the kernel records");
    }
    // As would an ITS left out.
    if h.its_lost {
        fail("more GIC ITS blocks than the kernel records");
    }

    // Interrupt controller, timer, FP/SIMD.
    let device = |pa: u64, len: u64, what: &str| match paging::map_device(pa, len) {
        Some(va) => va,
        None => fail(what),
    };
    let gicd = device(h.gicd, gicd_map, "GIC distributor not mappable");
    let mut gicr_va = [(0u64, 0u64); hw::MAX_GICR];
    let mut dev_used = Ranges::new();
    // Device memory goes to user space in pages: every page a kernel
    // device range touches is kept.
    let keep = |r: &mut Ranges, start: u64, end: u64| {
        let (s, e) = bootmem::pages_covering(start, end);
        r.add(s, e);
    };
    keep(&mut dev_used, h.gicd, h.gicd + gicd_len);
    // Every page of the console's mapping: two when the tables give a
    // base inside a page (SPCR and device trees may).
    if fl4_abi::config::PRINTING && uart.is_some() {
        keep(&mut dev_used, h.uart_base, h.uart_base.saturating_add(UART_MAP));
    }
    // Ranges apart from each other, from the kernel's devices so far and
    // from RAM.
    let apart = |used: &Ranges, r: &[(u64, u64)]| {
        r.iter().enumerate().all(|(i, a)| {
            !overlaps(used, a.0, a.1) && !overlaps(&ram, a.0, a.1) && r[..i].iter().all(|b| a.1 <= b.0 || b.1 <= a.0)
        })
    };
    let gicc = if h.gic_version == 3 {
        gic::set_gicr_stride(h.gicr_stride);
        // Every range checked and read (no register written) before any is
        // kept, and before anything is written to a redistributor or ITS.
        let mut gicr_ranges = [(0u64, 0u64); hw::MAX_GICR];
        for i in 0..h.n_gicr {
            let (base, raw_len) = h.gicr[i];
            if base & 0xffff != 0 || (raw_len != 0 && raw_len < fl4_arch_aarch64::gic_layout::GICR_FRAME) {
                fail("bad GIC redistributor range");
            }
            // An unsized range: up to one GICv4 redistributor per core.
            let len = if raw_len == 0 { fl4_arch_aarch64::gic_layout::GICR_FRAME_VLPI * h.n_cpus.max(1) as u64 } else { raw_len };
            let va = device(base, len, "GIC redistributors not mappable");
            gicr_va[i] = (va, len);
            // A MADT GICC entry sizes a core's RD and SGI frames only;
            // GICv4 adds two VLPI frames, which are not user space's
            // either (they hold tables the GIC writes to memory). An
            // unsized range must end with its last frame inside the
            // mapping (disabled cores' redistributors, more than
            // `MAX_CPUS` of them): what follows would be user space's.
            let span = match gic::redistributor_reserve(va, raw_len, len) {
                Some(s) => s,
                None => fail("GIC redistributor range ends past what the kernel maps"),
            };
            match base.checked_add(span).and_then(|e| e.checked_next_multiple_of(PAGE)) {
                Some(e) if e <= pa_limit => gicr_ranges[i] = (base, e),
                _ => fail("GIC redistributor range past physical address space"),
            }
        }
        if !apart(&dev_used, &gicr_ranges[..h.n_gicr]) {
            fail("overlapping GIC redistributor MMIO");
        }
        for &(s, e) in &gicr_ranges[..h.n_gicr] {
            keep(&mut dev_used, s, e);
        }
        smp::set_gicr(&gicr_va[..h.n_gicr]);
        0
    } else {
        if h.gicc == 0 {
            fail("no GICv2 CPU interface");
        }
        let fits = |b: u64, l: u64| b.checked_add(l.max(0x2000)).is_some_and(|e| e <= pa_limit);
        if h.gicc & 0xfff != 0 || (h.gicc_len != 0 && h.gicc_len < 0x2000) || !fits(h.gicc, h.gicc_len) {
            fail("bad GICv2 CPU interface range");
        }
        if h.gich != 0 && (h.gich & 0xfff != 0 || (h.gich_len != 0 && h.gich_len < 0x2000) || !fits(h.gich, h.gich_len)) {
            fail("bad GICv2 hypervisor interface range");
        }
        // The tables may give more than the two pages the kernel maps
        // (64 KiB-spaced aliases of the CPU interface).
        keep(&mut dev_used, h.gicc, h.gicc.saturating_add(h.gicc_len.max(0x2000)));
        if cpu::has_el2() && h.gich != 0 {
            let gich_len = h.gich_len.max(0x2000);
            let gich_va = device(h.gich, gich_len, "GIC hypervisor interface not mappable");
            keep(&mut dev_used, h.gich, h.gich.saturating_add(gich_len));
            gic::set_gich(gich_va);
        }
        device(h.gicc, 0x2000, "GIC CPU interface not mappable")
    };
    // Every ITS is the kernel's, whether or not it can drive it (its.rs
    // drives the first): all of its frames, GICv4.1's vSGI frame too
    // (`its::span`). Before any is read, the range the tables give each
    // (at least its two frames) must be apart from the others', the
    // kernel's devices (the redistributors included) and RAM; then each is
    // read (not written) for its whole range, checked the same way.
    let mut its_va = None;
    let mut its_pa = 0;
    let mut its_was_enabled = false;
    let mut its_ranges = [(0u64, 0u64); hw::MAX_ITS];
    let mut its_vas = [0u64; hw::MAX_ITS];
    if h.n_its != 0 {
        use fl4_arch_aarch64::its;
        if h.gic_version != 3 {
            fail("GICv2 firmware tables describe a GICv3 ITS");
        }
        let its = &h.its[..h.n_its];
        for (i, b) in its.iter().enumerate() {
            if b.raw_len != 0 && b.raw_len < its::ITS_SIZE {
                fail("GIC ITS size contradicts hardware");
            }
            match b.base.checked_add(b.raw_len.max(its::ITS_SIZE)).and_then(|e| e.checked_next_multiple_of(PAGE)) {
                Some(e) if e <= pa_limit => its_ranges[i] = (b.base, e),
                _ => fail("GIC ITS past physical address space"),
            }
        }
        if !apart(&dev_used, &its_ranges[..its.len()]) {
            fail("overlapping GIC ITS MMIO");
        }
        for (i, b) in its.iter().enumerate() {
            let va = device(b.base, its::ITS_SIZE, "GIC ITS not mappable");
            its_vas[i] = va;
            let span = match its::span(va, b.raw_len) {
                Some(s) => s,
                None => fail("GIC ITS size contradicts hardware"),
            };
            // A device tree's buses do not reach its last frame: what is
            // there is unknown.
            if span > b.max_len {
                fail("GIC ITS exceeds bus range");
            }
            match b.base.checked_add(span).and_then(|e| e.checked_next_multiple_of(PAGE)) {
                Some(e) if e <= pa_limit => its_ranges[i] = (b.base, e),
                Some(_) => fail("GIC ITS past physical address space"),
                None => fail("GIC ITS address overflows"),
            }
        }
        if !apart(&dev_used, &its_ranges[..its.len()]) {
            fail("overlapping GIC ITS MMIO");
        }
    }
    // Every GIC range is known good and apart: now take the redistributors
    // and the ITSs over. LPIs the firmware left on read and write its
    // tables, in memory the kernel hands out: off on every redistributor,
    // whether or not the kernel drives an ITS; and every ITS quiescent
    // (the firmware may have left one translating).
    if h.gic_version == 3 {
        if let Err(e) = fl4_arch_aarch64::its::quiesce_redistributors(&gicr_va[..h.n_gicr], h.gicr_stride) {
            fail(e);
        }
    }
    for i in 0..h.n_its {
        match fl4_arch_aarch64::its::quiesce(its_vas[i]) {
            Some(was) if i == 0 => its_was_enabled = was,
            Some(_) => {}
            None => fail("GIC ITS did not quiesce"),
        }
        keep(&mut dev_used, its_ranges[i].0, its_ranges[i].1);
    }
    if h.n_its != 0 {
        its_va = Some(its_vas[0]);
        its_pa = h.its[0].base;
    }
    if !gic::init_dist(h.gic_version, gicd, gicc) {
        fail("GIC distributor RWP stuck");
    }
    gic::init_cpu(smp::find_gicr());
    if cpu::is_el2_nvhe() {
        fl4_arch_aarch64::hyp_nvhe::init_gic_core(
            0,
            h.gic_version == 3,
            gic::vgic_num_lrs(),
            if h.gic_version == 3 { fl4_arch_aarch64::vcpu::gicv3_n_apr() } else { 0 },
        );
    }
    if !timer::init() {
        fail("CNTFRQ_EL0 is zero");
    }
    if cpu::is_el2_nvhe() {
        fl4_arch_aarch64::hyp_nvhe::save_host_regs();
    }
    fpu::init();
    fl4_arch_aarch64::smp::set_psci(h.psci);
    let vgic_lrs = gic::vgic_num_lrs();
    let virt_reject = kconfig::virt_reject_of(&kconfig::Virt {
        has_el2: cpu::has_el2(),
        novirt: has_option(bi, b"novirt"),
        vgic: (h.gic_version == 3 && gic::has_sysregs())
            || (h.gic_version == 2 && gic::gich() != 0 && h.gicv != 0),
        lrs: vgic_lrs as u64,
        ppis_ok: (h.vgic_maint == 0 || h.vgic_maint == fl4_core::layout::irq::VGIC_MAINT_ID)
            && (h.vtimer == 0 || h.vtimer == fl4_core::layout::irq::TIMER_ID),
        psci_ok: h.n_cpus <= 1 || h.psci != fl4_arch_aarch64::smp::PSCI_HVC,
    });
    let virt_ready = virt_reject == fl4_abi::consts::kernel_config::virt_reject::NONE;
    fl4_arch_aarch64::arch::set_virt_ready(virt_ready);
    match cpu::el_mode() {
        cpu::ElMode::El2Vhe => {
            kprintln!(
                "FL4: EL2 (VHE), virt {}, GICv{} VGIC ({} LRs)",
                if virt_ready { "ready" } else { "disabled" },
                h.gic_version,
                gic::vgic_num_lrs(),
            );
        }
        cpu::ElMode::El2Nvhe => {
            kprintln!(
                "FL4: EL2 (nVHE), virt {}, GICv{} VGIC ({} LRs)",
                if virt_ready { "ready" } else { "disabled" },
                h.gic_version,
                gic::vgic_num_lrs(),
            );
        }
        cpu::ElMode::El1 => {
            kprintln!("FL4: EL1 (native)");
        }
    }
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
    zeroed.remove(bi.region_paddr, bi.region_paddr + bi.region_len);
    zeroed.remove(root.p_start, root.p_end);
    let mut mods = [fl4_bootinfo::Module::default(); fl4_bootinfo::MAX_MODULES];
    let n_mods = (bi.n_modules as usize).min(fl4_bootinfo::MAX_MODULES);
    for i in 0..n_mods {
        let m = bi.modules[i];
        let m_start = m.paddr & !(PAGE - 1);
        let m_end = (m.paddr + m.size + PAGE - 1) & !(PAGE - 1);
        free.remove(m_start, m_end);
        zeroed.remove(m_start, m_end);
    }
    // The TPM event log the loader copied: whole pages of free RAM clear
    // of the kernel region, the root task and the modules, or none.
    let mut tpm = tpm_log(bi, &usable, n_mods);
    if let Some(t) = tpm {
        if overlaps(&dev_used, t.paddr, t.paddr + t.size.div_ceil(PAGE) * PAGE) {
            kprintln!("FL4: TPM event log at {:#x} overlaps a kernel device: ignored", t.paddr);
            tpm = None;
        }
    }
    if let Some(t) = &tpm {
        let t_end = t.paddr + t.size.div_ceil(PAGE) * PAGE;
        free.remove(t.paddr, t_end);
        zeroed.remove(t.paddr, t_end);
    }
    let mut dev = Ranges::new();
    dev.add(0, pa_top);
    for i in 0..all_usable.n {
        dev.remove(all_usable.r[i].start, all_usable.r[i].end);
    }
    // A kernel device range the list lost would be user space's.
    if dev_used.lost {
        fail("too many kernel device ranges");
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
        // It would hand user space the kernel's device.
        if overlaps(&dev_used, start, end) {
            fail("boot module overlaps kernel device");
        }
        dev.add(start, end);
        mods[extra_mods] = m;
        extra_mods += 1;
        kprintln!("FL4: boot module {}: {:#x} bytes at {:#x}", i, m.size, m.paddr);
    }
    // Handed over the same way.
    if let Some(t) = &tpm {
        dev.add(t.paddr, t.paddr + t.size.div_ceil(PAGE) * PAGE);
        kprintln!("FL4: TPM event log: {:#x} bytes at {:#x}", t.size, t.paddr);
    }

    // The ITS's tables, from the free RAM, 64 KiB aligned.
    let mut msi = None;
    if let Some(va) = its_va {
        use fl4_arch_aarch64::its;
        let size = its::memory_size(ncpus);
        let mut pool = free;
        if bi.dtb != 0 {
            let dl = hw::dtb_size(bi.dtb);
            pool.remove(bi.dtb & !(PAGE - 1), (bi.dtb + dl + PAGE - 1) & !(PAGE - 1));
        }
        match pool.take(size + 0x1_0000) {
            Some(p) => {
                free.remove(p, p + size + 0x1_0000);
                zeroed.remove(p, p + size + 0x1_0000);
                let mem = (p + 0xffff) & !0xffff;
                let gicr_pa = |c: usize| {
                    let va = percpu::gicr(c);
                    (0..h.n_gicr).find(|&i| va >= gicr_va[i].0 && va < gicr_va[i].0 + gicr_va[i].1)
                        .map(|i| h.gicr[i].0 + (va - gicr_va[i].0))
                };
                // fl4-efi boots from UEFI, after ExitBootServices: an ITS comes
                // to the kernel from reset, unused. A loader that cannot
                // promise that (a warm reboot, kexec) passes `warm_its`, and
                // an ITS without GITS_TYPER.INV then stays off.
                let trusted_cold_handoff = !has_option(bi, b"warm_its");
                match its::init(va, its_pa, mem, ncpus, gicr_pa, &gicr_va[..h.n_gicr], its_was_enabled, trusted_cold_handoff) {
                    Ok(info) => {
                        kprintln!("FL4: ITS at {:#x}: {} LPIs, {} device IDs, MSI doorbell {:#x}", its_pa, info.num_lpis, info.num_devices, info.doorbell);
                        msi = Some(info);
                    }
                    Err(its::InitError::Unsupported(e)) => kprintln!("FL4: ITS at {:#x} unused: {}", its_pa, e),
                    Err(its::InitError::Unsafe(e)) => fail(e),
                }
            }
            // Quiesced at discovery, it stays off.
            None => kprintln!("FL4: no memory for the ITS tables"),
        }
    }

    // The extra BootInfo, in memory taken from the free RAM.
    let dtb_len = if bi.dtb != 0 { hw::dtb_size(bi.dtb) } else { 0 };
    let extra_size = EXTRA_FIXED + ((dtb_len + 16 + PAGE) & !(PAGE - 1));
    // Not over the device tree it copies (which may be in free memory).
    let mut pool = free;
    if dtb_len != 0 {
        let dtb_start = bi.dtb & !(PAGE - 1);
        let dtb_end = (bi.dtb + dtb_len + PAGE - 1) & !(PAGE - 1);
        pool.remove(dtb_start, dtb_end);
        zeroed.remove(dtb_start, dtb_end);
    }
    let extra_pa = match pool.take(extra_size) {
        Some(p) => p,
        None => fail("no memory for the extra BootInfo"),
    };
    free.remove(extra_pa, extra_pa + extra_size);
    zeroed.remove(extra_pa, extra_pa + extra_size);
    if zeroed.lost {
        zeroed = Ranges::new();
    }
    let extra = unsafe { core::slice::from_raw_parts_mut(pptr(extra_pa) as *mut u8, extra_size as usize) };
    let extra_len = build_extra_bi(extra, &h, bi.dtb, dtb_len, &mods[..extra_mods], tpm.as_ref(), msi.as_ref());
    // The boot frames go after the image in user space (fl4-core
    // `root_layout`): all of them below its end, the extra BootInfo with
    // fl4-core's room for the extra untypeds.
    let root_v_end = root.v_start.checked_add(root.p_end - root.p_start);
    let tail_len = (extra_len as u64).checked_add(fl4_core::boot::extra_ut_reserve());
    if !root_v_end.zip(tail_len).is_some_and(|(end, len)| fl4_bootinfo::root_tail_fits(end, len)) {
        fail("root task image too close to the end of user space");
    }
    if has_option(bi, b"fb_console") {
        kprintln!("FL4: fb_console is not supported on AArch64");
    }

    let st = unsafe { &mut *STATICS.0.get() };
    let mut p = BootParams {
        free: [Region::EMPTY; MAX_REGIONS],
        n_free: 0,
        zeroed: [Region::EMPTY; MAX_REGIONS],
        n_zeroed: 0,
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
        // Its pointers' physical addresses, just below 128 TiB, can be
        // device memory: fl4-core's `create_device_untypeds` leaves them out.
        kernel_image: Region { start: KERNEL_VBASE, end: unsafe { &__kernel_end as *const u8 as u64 } },
    };
    // The largest free ranges, if there are more than BootParams holds.
    let (mut omitted_free, mut omitted_bytes) = (0usize, 0u64);
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
        omitted_free += 1;
        omitted_bytes += r.end - r.start;
    }
    if omitted_free != 0 {
        kprintln!("FL4: {} free RAM region(s) ({:#x} bytes) exceed the boot range limit", omitted_free, omitted_bytes);
    }
    for i in 0..free.n {
        p.free[i] = Region { start: pptr(free.r[i].start), end: pptr(free.r[i].end) };
        p.n_free += 1;
    }
    if zeroed.n <= MAX_REGIONS {
        for i in 0..zeroed.n {
            p.zeroed[i] = Region { start: pptr(zeroed.r[i].start), end: pptr(zeroed.r[i].end) };
            p.n_zeroed += 1;
        }
    }
    for i in 0..dev.n.min(MAX_REGIONS) {
        p.device[i] = dev.r[i];
        p.n_device += 1;
    }
    if dev.n > MAX_REGIONS {
        kprintln!("FL4: {} device memory regions exceed the boot range limit", dev.n - MAX_REGIONS);
        // The boot modules and the TPM log reach the root task only as
        // these device untypeds.
        let boot_data = mods[..extra_mods]
            .iter()
            .map(|m| (m.paddr, m.paddr + m.size))
            .chain(tpm.as_ref().map(|t| (t.paddr, t.paddr + t.size)));
        let lost = &dev.r[MAX_REGIONS..dev.n];
        for (start, end) in boot_data {
            let (start, end) = (start & !(PAGE - 1), (end + PAGE - 1) & !(PAGE - 1));
            if lost.iter().any(|r| r.start < end && start < r.end) {
                fail("boot modules or event logs exceed the boot device range limit");
            }
        }
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
            fl4_core::boot::BootError::TooManyUntypeds => "too many untyped regions",
        };
        kprintln!("FL4: creating the root task failed: {}", why);
        fail("root task");
    }
    if cpu::has_el2() {
        use fl4_core::interrupt::{IRQ_RESERVED, IRQ_TIMER};
        use fl4_core::layout::irq;
        let ktimer_id = timer::timer_irq_id();
        for c in 0..irq::BANKED_CORES {
            let kt = irq::of(ktimer_id, c);
            let vtm = irq::of(irq::TIMER_ID, c);
            let vgic = irq::of(irq::VGIC_MAINT_ID, c);
            ks_set(&mut s, ks::IRQ_STATE + kt * 8, IRQ_TIMER);
            ks_set(&mut s, ks::IRQ_STATE + vtm * 8, IRQ_RESERVED);
            ks_set(&mut s, ks::IRQ_STATE + vgic * 8, IRQ_RESERVED);
        }
    }
    // Everything SysKernelConfig answers is decided now.
    kconfig::freeze(&kconfig::Facts {
        online: fl4_arch_aarch64::smp::num_online(),
        el2_vhe: cpu::is_el2_vhe(),
        el2_nvhe: cpu::is_el2_nvhe(),
        virt_reject,
        vmid16: cpu::has_el2() && cpu::vmid16(),
        s2_ipa_bits: fl4_arch_aarch64::mmu::s2_ipa_bits(),
        vgic_lrs: vgic_lrs as u64,
        pan: cpu::has_pan(),
        pauth: cpu::has_pauth(),
        clrbhb: cpu::has_clrbhb(),
        asid16: cpu::has_asid16(),
        hw_af: cpu::has_hw_af(),
        gicv3_sre: gic::sre(),
        its: msi.is_some(),
        timer_local_ack: gic::can_ack_timer_only(),
        pa_bits: cpu::pa_bits(),
        gic_version: gic::version(),
        max_spi: gic::max_spi(),
        psci: fl4_arch_aarch64::smp::psci(),
        timer_hz: timer::freq(),
    });
    kprintln!("FL4: starting the root task at {:#x}", root.entry);
    // With kernel printing disabled, the root task owns the UART page.
    if !fl4_abi::config::PRINTING {
        serial::release();
    }
    // Every kernel mapping is made: ArmHighVSpaces copy the tables from now.
    paging::freeze_kernel_tables();
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
