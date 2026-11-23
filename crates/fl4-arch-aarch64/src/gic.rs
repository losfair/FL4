//! The GIC, version 2 or 3 as found at boot (ACPI MADT or the device
//! tree). All interrupts are group 1 at one priority; the kernel takes
//! them one at a time with interrupts masked except in the idle loop.
use crate::{cpu, gic_layout, percpu};
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

pub const SPURIOUS: u64 = 1023;
const PRIO: u32 = 0xa0;

static VERSION: AtomicU64 = AtomicU64::new(0);
static GICD: AtomicU64 = AtomicU64::new(0);
static GICC: AtomicU64 = AtomicU64::new(0);
static GICH: AtomicU64 = AtomicU64::new(0);
static LINES: AtomicU64 = AtomicU64::new(32);
/// GICv3: some core started has Aff0 16 or more, so every core must be
/// able to send SGIs with the range selector.
static NEED_RSS: AtomicBool = AtomicBool::new(false);
/// ICC_SRE_EL1.SRE reads back as set: the GICv3 system register interface
/// works even where ID_AA64PFR0_EL1.GIC says 0 (QEMU HVF on Apple silicon),
/// as Linux's gic_enable_sre() finds it.
static GICV3_SRE: AtomicBool = AtomicBool::new(false);

const GICD_CTLR: u64 = 0x0;
const GICD_TYPER: u64 = 0x4;
const GICD_IGROUPR: u64 = 0x80;
const GICD_ISENABLER: u64 = 0x100;
const GICD_ICENABLER: u64 = 0x180;
const GICD_ICPENDR: u64 = 0x280;
const GICD_ICACTIVER: u64 = 0x380;
const GICD_IPRIORITYR: u64 = 0x400;
const GICD_ITARGETSR: u64 = 0x800;
const GICD_ICFGR: u64 = 0xc00;
const GICD_SGIR: u64 = 0xf00;
const GICD_IROUTER: u64 = 0x6000;

const GICC_CTLR: u64 = 0x0;
const GICC_PMR: u64 = 0x4;
const GICC_BPR: u64 = 0x8;
const GICC_IAR: u64 = 0xc;
const GICC_EOIR: u64 = 0x10;

const GICR_WAKER: u64 = 0x14;
const GICR_SGI: u64 = 0x1_0000;

fn rd(a: u64) -> u32 {
    unsafe { core::ptr::read_volatile(a as *const u32) }
}

fn wr(a: u64, v: u32) {
    unsafe { core::ptr::write_volatile(a as *mut u32, v) }
}

fn wr8(a: u64, v: u8) {
    unsafe { core::ptr::write_volatile(a as *mut u8, v) }
}

fn wr64(a: u64, v: u64) {
    unsafe { core::ptr::write_volatile(a as *mut u64, v) }
}

pub fn version() -> u64 {
    VERSION.load(Ordering::Relaxed)
}

fn gicd() -> u64 {
    GICD.load(Ordering::Relaxed)
}

/// GICD_TYPER.
pub fn dist_typer() -> u32 {
    rd(gicd() + GICD_TYPER)
}

/// Interrupt lines the distributor implements (SPIs end below this).
pub fn lines() -> u64 {
    LINES.load(Ordering::Relaxed)
}

pub fn max_spi() -> u64 {
    (lines() - 1).min(1019)
}

/// Record the GICv2 hypervisor control interface (GICH) kernel virtual address.
pub fn set_gich(va: u64) {
    GICH.store(va, Ordering::Relaxed);
}

/// The GICv2 GICH kernel virtual address (0 if none / GICv3).
pub fn gich() -> u64 {
    GICH.load(Ordering::Relaxed)
}

/// The GICv3 system register interface: ID_AA64PFR0_EL1.GIC, or SRE set.
pub fn has_sysregs() -> bool {
    cpu::has_gic_sysregs() || GICV3_SRE.load(Ordering::Relaxed)
}

fn raw_vgic_vtr() -> u64 {
    if !cpu::has_el2() {
        return 0;
    }
    if version() == 3 {
        if !has_sysregs() {
            return 0;
        }
        if cpu::is_el2_nvhe() {
            return crate::hyp_nvhe::vgic_vtr();
        }
        let v: u64;
        unsafe { core::arch::asm!("mrs {}, s3_4_c12_c11_1", out(reg) v, options(nomem, nostack, preserves_flags)) };
        v
    } else {
        let h = GICH.load(Ordering::Relaxed);
        if h == 0 {
            0
        } else {
            rd(h + 0x4) as u64
        }
    }
}

/// Physical number of VGIC list registers implemented by hardware
/// (GICv3: 5-bit ListRegs, GICv2: 6-bit ListRegs).
pub fn vgic_hw_num_lrs() -> u8 {
    let raw = raw_vgic_vtr();
    if raw == 0 {
        0
    } else if version() == 3 {
        ((raw & 0x1f) + 1) as u8
    } else {
        ((raw & 0x3f) + 1) as u8
    }
}

/// ABI-capped VGIC type register (`ICH_VTR_EL2` on GICv3, `GICH_VTR` on GICv2).
/// Caps `ListRegs` to <= 15 (16 LRs) so BootInfo, VCPU init and ReadState agree
/// with the 16-slot `VGIC_LR0..15` ABI. Returns 0 when VGIC is unavailable.
pub fn vgic_vtr() -> u64 {
    let raw = raw_vgic_vtr();
    if raw == 0 {
        0
    } else if version() == 2 && (raw & 0x3f) >= 16 {
        (raw & !0x3f) | 15
    } else if version() == 3 && (raw & 0x1f) >= 16 {
        (raw & !0x1f) | 15
    } else {
        raw
    }
}

/// Number of VGIC list registers exposed by the FL4 ABI (capped at 16; 0 when unavailable).
pub fn vgic_num_lrs() -> u8 {
    vgic_hw_num_lrs().min(16)
}

fn v3_wait_rwp(base: u64) {
    let mut n = 0u64;
    while rd(base) & (1 << 31) != 0 && n < 10_000_000 {
        core::hint::spin_loop();
        n += 1;
    }
}

/// The distributor, once, on the boot core. `gicd` and `gicc` are kernel
/// virtual addresses (`gicc` 0 on GICv3).
pub fn init_dist(version: u64, gicd: u64, gicc: u64) {
    VERSION.store(version, Ordering::Relaxed);
    GICD.store(gicd, Ordering::Relaxed);
    GICC.store(gicc, Ordering::Relaxed);
    let lines = gic_layout::dist_lines(rd(gicd + GICD_TYPER));
    LINES.store(lines, Ordering::Relaxed);
    wr(gicd + GICD_CTLR, 0);
    if version == 3 {
        v3_wait_rwp(gicd + GICD_CTLR);
    }
    // Only the registers of implemented interrupts below 1020: the last
    // word of a 1024-line distributor also has bits for the special
    // INTIDs, and the registers past them are reserved.
    let mut i = 32;
    while i < lines {
        let bits = gic_layout::bank_bits(i, lines);
        wr(gicd + GICD_ICENABLER + i / 8, bits);
        wr(gicd + GICD_ICPENDR + i / 8, bits);
        wr(gicd + GICD_ICACTIVER + i / 8, bits);
        wr(gicd + GICD_IGROUPR + i / 8, bits);
        i += 32;
    }
    let mut i = 32;
    while i < lines {
        wr(gicd + GICD_IPRIORITYR + i, PRIO * 0x0101_0101);
        i += 4;
    }
    // Level triggered, until user space asks for an edge.
    let mut i = 32;
    while i < lines {
        wr(gicd + GICD_ICFGR + i / 4, 0);
        i += 16;
    }
    if version == 3 {
        // Affinity routing; group 1 for both security views.
        wr(gicd + GICD_CTLR, 1 << 4);
        v3_wait_rwp(gicd + GICD_CTLR);
        wr(gicd + GICD_CTLR, (1 << 4) | (1 << 1) | 1);
        v3_wait_rwp(gicd + GICD_CTLR);
        let me = cpu::mpidr();
        let mut i = 32;
        while i < lines {
            wr64(gicd + GICD_IROUTER + i * 8, me);
            i += 1;
        }
    } else {
        // To the boot core's interface, which need not be interface 0.
        let targets = gic_layout::v2_targets(rd(gicd + GICD_ITARGETSR));
        let mut i = 32;
        while i < lines {
            wr(gicd + GICD_ITARGETSR + i, targets);
            i += 4;
        }
        wr(gicd + GICD_CTLR, 3);
    }
}

/// GICv3: find this core's redistributor in the `len` mapped bytes from
/// `base`: only a frame wholly inside them, up to the frame marked last.
pub fn find_redistributor(base: u64, len: u64) -> Option<u64> {
    gic_layout::find_frame(base, len, affinity(), typer)
}

/// How many bytes from `base` the redistributors in its `len` mapped bytes
/// take, VLPI frames included (`gic_layout::span`): none of it is for user
/// space.
pub fn redistributor_span(base: u64, len: u64) -> u64 {
    gic_layout::span(base, len, typer)
}

/// What boot keeps from user space of the redistributor range mapped at
/// `base` for `len` bytes, which the tables gave `raw_len` bytes
/// (`gic_layout::reserve`): None if it cannot tell.
pub fn redistributor_reserve(base: u64, raw_len: u64, len: u64) -> Option<u64> {
    gic_layout::reserve(base, raw_len, len, typer)
}

/// The calling core's affinity as GICR_TYPER[63:32] gives it.
fn affinity() -> u64 {
    let me = cpu::mpidr();
    ((me >> 32) & 0xff) << 24 | (me & 0xff_ffff)
}

/// GICR_TYPER of the redistributor at `frame`.
fn typer(frame: u64) -> u64 {
    unsafe { core::ptr::read_volatile((frame + 8) as *const u64) }
}

/// The calling core's interface. GICv3: `gicr` is its redistributor.
pub fn init_cpu(gicr: u64) {
    if version() == 3 {
        percpu::set_gicr(gicr);
        // Wake the redistributor.
        let w = rd(gicr + GICR_WAKER) & !(1 << 1);
        wr(gicr + GICR_WAKER, w);
        let mut n = 0u64;
        while rd(gicr + GICR_WAKER) & (1 << 2) != 0 && n < 10_000_000 {
            core::hint::spin_loop();
            n += 1;
        }
        let sgi = gicr + GICR_SGI;
        wr(sgi + GICD_ICENABLER, u32::MAX);
        wr(sgi + GICD_ICPENDR, u32::MAX);
        wr(sgi + GICD_ICACTIVER, u32::MAX);
        wr(sgi + GICD_IGROUPR, u32::MAX);
        let mut i = 0;
        while i < 32 {
            wr(sgi + GICD_IPRIORITYR + i, PRIO * 0x0101_0101);
            i += 4;
        }
        v3_wait_rwp(gicr);
        // System registers: SRE, priority mask, group 1 enable.
        msr_s("s3_0_c12_c12_5", 0x7);
        cpu::isb();
        let sre: u64;
        unsafe { core::arch::asm!("mrs {}, s3_0_c12_c12_5", out(reg) sre) };
        if sre & 1 != 0 {
            GICV3_SRE.store(true, Ordering::Relaxed);
        }
        msr_s("s3_0_c4_c6_0", 0xff);
        msr_s("s3_0_c12_c12_3", 0);
        msr_s("s3_0_c12_c12_4", 0);
        msr_s("s3_0_c12_c12_7", 1);
        cpu::isb();
    } else {
        let d = gicd();
        wr(d + GICD_ICENABLER, u32::MAX);
        wr(d + GICD_ICPENDR, u32::MAX);
        wr(d + GICD_ICACTIVER, u32::MAX);
        let mut i = 0;
        while i < 32 {
            wr(d + GICD_IPRIORITYR + i, PRIO * 0x0101_0101);
            i += 4;
        }
        // This interface's number: the banked targets of an SGI.
        percpu::set_gic_cpu(gic_layout::v2_interface(rd(d + GICD_ITARGETSR)));
        let c = GICC.load(Ordering::Relaxed);
        wr(c + GICC_PMR, 0xff);
        wr(c + GICC_BPR, 0);
        wr(c + GICC_CTLR, 3);
        if cpu::has_el2() {
            let h = GICH.load(Ordering::Relaxed);
            if h != 0 {
                // Zero GICH_HCR and every physical GICH_LR so slots above the
                // 16-LR ABI cap remain permanently invalid.
                wr(h + 0x0, 0);
                let hw_lrs = vgic_hw_num_lrs() as u64;
                for i in 0..hw_lrs {
                    wr(h + 0x100 + i * 4, 0);
                }
            }
        }
    }
    // The kernel owns these banked interrupts on every online core.
    use fl4_core::layout::irq;
    let bank = if version() == 3 { gicr + GICR_SGI } else { gicd() };
    let timer_id = crate::timer::timer_irq_id();
    wr(bank + GICD_ISENABLER,
       (1 << timer_id) | (1 << irq::REMOTE_CALL_ID) | (1 << irq::RESCHEDULE_ID));
    cpu::dsb_sy();
}

/// GICv3: whether the calling core can send SGIs to Aff0 16 and more
/// (`gic_layout::v3_rss`); after `init_cpu`, which enables the system
/// register interface.
pub fn rss() -> bool {
    if version() != 3 {
        return false;
    }
    let ctlr: u64;
    unsafe { core::arch::asm!("mrs {}, s3_0_c12_c12_4", out(reg) ctlr) };
    gic_layout::v3_rss(rd(gicd() + GICD_TYPER), ctlr)
}

/// Before the APs start: whether a core with Aff0 16 or more will run.
pub fn set_need_rss(v: bool) {
    NEED_RSS.store(v, Ordering::Relaxed);
}

/// Whether the calling core, index `c`, after `init_cpu`, can exchange
/// SGIs with the cores before it: GICv2, one CPU interface of its own;
/// GICv3, the range selector if a core needs it (`start_aps` starts no
/// core an SGI cannot name).
pub fn sgi_ok(c: usize) -> bool {
    if version() == 3 {
        !NEED_RSS.load(Ordering::Relaxed) || rss()
    } else {
        gic_layout::v2_interface_ok(percpu::gic_cpu(c), (0..c).map(percpu::gic_cpu))
    }
}

fn msr_s(reg: &str, v: u64) {
    // The GIC registers by encoding, for assemblers without the names.
    unsafe {
        match reg {
            "s3_0_c12_c12_5" => core::arch::asm!("msr s3_0_c12_c12_5, {}", in(reg) v),
            "s3_0_c4_c6_0" => core::arch::asm!("msr s3_0_c4_c6_0, {}", in(reg) v),
            "s3_0_c12_c12_3" => core::arch::asm!("msr s3_0_c12_c12_3, {}", in(reg) v),
            "s3_0_c12_c12_4" => core::arch::asm!("msr s3_0_c12_c12_4, {}", in(reg) v),
            "s3_0_c12_c12_7" => core::arch::asm!("msr s3_0_c12_c12_7, {}", in(reg) v),
            "s3_0_c12_c12_1" => core::arch::asm!("msr s3_0_c12_c12_1, {}", in(reg) v),
            "s3_0_c12_c11_5" => core::arch::asm!("msr s3_0_c12_c11_5, {}", in(reg) v),
            _ => {}
        }
    }
}

/// Acknowledge the highest pending interrupt: its ID, or `SPURIOUS`.
pub fn ack() -> u64 {
    if version() == 3 {
        let v: u64;
        unsafe { core::arch::asm!("mrs {}, s3_0_c12_c12_0", out(reg) v) };
        cpu::dsb_sy();
        v & 0xff_ffff
    } else {
        let v = rd(GICC.load(Ordering::Relaxed) + GICC_IAR) as u64;
        let id = v & 0x3ff;
        if id >= 1020 {
            SPURIOUS
        } else {
            // SGIs keep the source core in bits 10-12, which EOI needs.
            v & 0x1fff
        }
    }
}

/// The highest pending interrupt's ID without acknowledging it.
pub fn highest_pending() -> u64 {
    if version() == 3 {
        let v: u64;
        unsafe { core::arch::asm!("mrs {}, s3_0_c12_c12_2", out(reg) v) };
        v & 0xff_ffff
    } else {
        (rd(GICC.load(Ordering::Relaxed) + 0x18) & 0x3ff) as u64
    }
}

/// The interrupt ID in an acknowledge value: an LPI's whole, else the low
/// ten bits (GICv2 puts an SGI's source core above them).
pub fn raw_id(raw: u64) -> u64 {
    if raw >= fl4_core::layout::irq::LPI_ID_BASE { raw } else { raw & 0x3ff }
}

/// Whether an acknowledge value names no interrupt.
pub fn is_spurious(raw: u64) -> bool {
    raw == SPURIOUS || (1020..fl4_core::layout::irq::LPI_ID_BASE).contains(&raw_id(raw))
}

/// End interrupt `id` (as `ack` returned it).
pub fn eoi(id: u64) {
    if version() == 3 {
        msr_s("s3_0_c12_c12_1", id);
        cpu::isb();
    } else {
        wr(GICC.load(Ordering::Relaxed) + GICC_EOIR, id as u32);
    }
}

/// Whether an interrupt is pending for this core.
pub fn pending() -> bool {
    crate::mrs!("isr_el1") & (1 << 7) != 0
}

/// Whether `id`'s bits for `core` can only be changed on that core
/// (`gic_layout::banked_remote`): `mask` and `configure` would reach
/// nothing from here, so the caller makes a remote call (`smp::CALL_GIC_*`).
pub fn remote(id: u64, core: u64) -> bool {
    gic_layout::banked_remote(version() == 3, id, core, percpu::cpu_index() as u64)
}

/// The registers that hold banked interrupt `id`'s bits for `core`, or
/// None when they cannot be reached from here (GICv2, another core:
/// `remote`).
fn banked_base(core: u64) -> Option<u64> {
    if version() == 3 {
        let r = percpu::gicr(core as usize);
        if r == 0 {
            None
        } else {
            Some(r + GICR_SGI)
        }
    } else if core == percpu::cpu_index() as u64 {
        Some(gicd())
    } else {
        None
    }
}

/// Mask or unmask `id` (banked interrupts: on `core`).
pub fn mask(id: u64, core: u64, masked: bool) {
    // LPIs are never masked (its.rs).
    if id >= 1020 {
        return;
    }
    let base = if id < 32 {
        match banked_base(core) {
            Some(b) => b,
            None => return,
        }
    } else {
        gicd()
    };
    let reg = if masked { GICD_ICENABLER } else { GICD_ISENABLER };
    wr(base + reg + (id / 32) * 4, 1 << (id % 32));
}

/// Edge (true) or level triggering for `id`; for an SPI also the target.
pub fn configure(id: u64, core: u64, edge: bool) {
    if id >= 1020 {
        return;
    }
    let base = if id < 32 {
        match banked_base(core) {
            Some(b) => b,
            None => return,
        }
    } else {
        gicd()
    };
    if id >= 16 {
        let a = base + GICD_ICFGR + (id / 16) * 4;
        let bit = 1u32 << ((id % 16) * 2 + 1);
        let v = rd(a);
        wr(a, if edge { v | bit } else { v & !bit });
    }
    if id >= 32 {
        route(id, core);
    }
}

/// Deliver SPI `id` to `core`.
pub fn route(id: u64, core: u64) {
    if !(32..1020).contains(&id) {
        return;
    }
    if version() == 3 {
        wr64(gicd() + GICD_IROUTER + id * 8, percpu::mpidr(core as usize));
    } else {
        wr8(gicd() + GICD_ITARGETSR + id, percpu::gic_cpu(core as usize) as u8);
    }
}

/// Send SGI `id` to `core`.
pub fn send_sgi(id: u64, core: u64) {
    let c = core as usize;
    // Everything this core wrote (a remote call's arguments, a woken
    // thread's state, page tables) before the SGI can reach the target.
    cpu::dsb_ish();
    if version() == 3 {
        let m = percpu::mpidr(c);
        let aff0 = m & 0xff;
        let v = (id << 24)
            | (((m >> 8) & 0xff) << 16)
            | (((m >> 16) & 0xff) << 32)
            | (((m >> 32) & 0xff) << 48)
            | ((aff0 / 16) << 44)
            | (1 << (aff0 % 16));
        msr_s("s3_0_c12_c11_5", v);
        cpu::isb();
    } else {
        wr(gicd() + GICD_SGIR, ((percpu::gic_cpu(c) as u32) << 16) | id as u32);
    }
}
