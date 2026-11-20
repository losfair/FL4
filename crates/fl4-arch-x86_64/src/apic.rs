//! Local APIC, in x2APIC mode when the CPU has it and xAPIC otherwise
//! (detected at boot, DESIGN.md §3). IPIs use physical destinations.
use crate::cpu::{cpuid, rdmsr, wrmsr, msr};
use core::sync::atomic::{AtomicU64, AtomicBool, Ordering};

static X2APIC: AtomicBool = AtomicBool::new(false);
/// Kernel virtual address of the xAPIC MMIO page.
static MMIO: AtomicU64 = AtomicU64::new(0);

pub const REG_ID: u32 = 0x20;
pub const REG_EOI: u32 = 0xb0;
pub const REG_SVR: u32 = 0xf0;
pub const REG_ISR: u32 = 0x100;
pub const REG_IRR: u32 = 0x200;
pub const REG_ICR_LO: u32 = 0x300;
pub const REG_ICR_HI: u32 = 0x310;
pub const REG_LVT_TIMER: u32 = 0x320;
pub const REG_LVT_LINT0: u32 = 0x350;
pub const REG_LVT_LINT1: u32 = 0x360;
pub const REG_LVT_ERROR: u32 = 0x370;
pub const REG_TIMER_INIT: u32 = 0x380;
pub const REG_TIMER_CUR: u32 = 0x390;
pub const REG_TIMER_DIV: u32 = 0x3e0;

pub fn has_x2apic() -> bool {
    cpuid(1, 0).ecx & (1 << 21) != 0
}

pub fn is_x2apic() -> bool {
    X2APIC.load(Ordering::Relaxed)
}

const BASE_ADDR_MASK: u64 = 0x000f_ffff_ffff_f000;
const X2_ENABLE: u64 = 1 << 10;

#[derive(Debug, PartialEq, Eq)]
enum Registers {
    Msr,
    Mmio(u64),
}

fn registers(base: u64, cpu_x2: bool, window_top: u64) -> Option<Registers> {
    if cpu_x2 || base & X2_ENABLE != 0 {
        Some(Registers::Msr)
    } else {
        crate::sev::mmio_ptr(base & BASE_ADDR_MASK, 4096, window_top).map(Registers::Mmio)
    }
}

/// The boot core's xAPIC register page (physical), the one page boot
/// keeps from user space's device memory.
static BSP_BASE: AtomicU64 = AtomicU64::new(0);

/// An application processor's registers, given the boot core's mode
/// (`bsp_x2`) and xAPIC page (`bsp_base`): None unless it can work the
/// same way. The mode and the page are global (`is_x2apic`, `MMIO`) and
/// boot reserves only the boot core's page, so an AP in the other mode
/// would fault on its first register access (or switch every core's
/// accesses to its mode), and one with its own xAPIC page would leave an
/// active APIC in user space's device memory.
fn ap_registers(base: u64, cpu_x2: bool, bsp_x2: bool, bsp_base: u64, window_top: u64) -> Option<Registers> {
    if bsp_x2 {
        (cpu_x2 || base & X2_ENABLE != 0).then_some(Registers::Msr)
    } else if base & X2_ENABLE != 0 || base & BASE_ADDR_MASK != bsp_base {
        // x2APIC cannot go back to xAPIC without disabling the APIC.
        None
    } else {
        crate::sev::mmio_ptr(base & BASE_ADDR_MASK, 4096, window_top).map(Registers::Mmio)
    }
}

/// Enable this core's APIC and return its physical base for boot memory
/// reservation. Only xAPIC requires a mapped register page. The boot core
/// (`bsp`) sets the mode and page every core uses; an application
/// processor that cannot use them gets None and changes nothing.
pub fn enable(bsp: bool, window_top: u64) -> Option<u64> {
    let base = rdmsr(msr::APIC_BASE);
    let regs = if bsp {
        registers(base, has_x2apic(), window_top)?
    } else {
        // After the boot core's Release stores (it enabled its APIC before
        // starting any AP).
        ap_registers(base, has_x2apic(), X2APIC.load(Ordering::Acquire), BSP_BASE.load(Ordering::Acquire), window_top)?
    };
    // An AP's mode and page are the boot core's: the globals stay.
    match regs {
        Registers::Msr => {
            wrmsr(msr::APIC_BASE, base | (1 << 11) | X2_ENABLE);
            if bsp {
                X2APIC.store(true, Ordering::Release);
            }
        }
        Registers::Mmio(mmio) => {
            wrmsr(msr::APIC_BASE, base | (1 << 11));
            if bsp {
                MMIO.store(mmio, Ordering::Release);
            }
        }
    }
    if bsp {
        BSP_BASE.store(base & BASE_ADDR_MASK, Ordering::Release);
    }
    Some(base & BASE_ADDR_MASK)
}

#[cfg(not(test))]
pub fn read(reg: u32) -> u32 {
    if is_x2apic() {
        rdmsr(0x800 + (reg >> 4)) as u32
    } else {
        unsafe { crate::sev::read_mmio32(MMIO.load(Ordering::Relaxed) + reg as u64) }
    }
}

#[cfg(not(test))]
pub fn write(reg: u32, v: u32) {
    if is_x2apic() {
        wrmsr(0x800 + (reg >> 4), v as u64)
    } else {
        unsafe { crate::sev::write_mmio32(MMIO.load(Ordering::Relaxed) + reg as u64, v) }
    }
}

/// Host tests: a register file whose EOI clears the highest ISR bit, as
/// the local APIC's does.
#[cfg(test)]
static FAKE: [core::sync::atomic::AtomicU32; 64] = [const { core::sync::atomic::AtomicU32::new(0) }; 64];

#[cfg(test)]
pub fn read(reg: u32) -> u32 {
    FAKE[(reg >> 4) as usize].load(Ordering::Relaxed)
}

#[cfg(test)]
pub fn write(reg: u32, v: u32) {
    if reg == REG_EOI {
        let mut i = 8;
        while i > 0 {
            i -= 1;
            let w = read(REG_ISR + i * 0x10);
            if w != 0 {
                FAKE[((REG_ISR >> 4) + i) as usize].store(w & !(1 << (31 - w.leading_zeros())), Ordering::Relaxed);
                return;
            }
        }
        return;
    }
    FAKE[(reg >> 4) as usize].store(v, Ordering::Relaxed)
}

pub fn id() -> u32 {
    if is_x2apic() {
        read(REG_ID)
    } else {
        read(REG_ID) >> 24
    }
}

pub fn eoi() {
    write(REG_EOI, 0);
}

/// Whether the local APIC has `v` in service (ISR): it delivered `v` as
/// an interrupt that has had no EOI yet. An `int n` from user code never
/// sets the bit.
pub fn in_service(v: u32) -> bool {
    read(REG_ISR + (v / 32) * 0x10) & (1 << (v % 32)) != 0
}

/// First vector above the kernel's IRQ range (the `int n` trap range).
const STRAY_MIN: u64 = fl4_core::layout::irq::INT_OFFSET + fl4_core::layout::irq::MAX + 1;
/// The spurious vector (SVR): its delivery sets no ISR bit and takes no EOI.
pub const SPURIOUS_VECTOR: u64 = 0xff;

/// An interrupt on `v` above the IRQ range, which no kernel IRQ uses but a
/// device's MSI or an IPI can name: if the APIC delivered it (rather than
/// user code raising `int n`), acknowledge it, so that it does not mask
/// every lower-priority vector (timer, IPIs and all IRQs) on this core
/// for good. Returns whether it was one, to be otherwise ignored.
#[inline(always)]
pub fn ack_stray(v: u64) -> bool {
    if v < STRAY_MIN || v >= SPURIOUS_VECTOR || !in_service(v as u32) {
        return false;
    }
    eoi();
    true
}

/// Whether any vector in [lo, hi] is requested (IRR).
pub fn irr_pending(lo: u32, hi: u32) -> bool {
    let mut v = lo;
    while v <= hi {
        let w = read(REG_IRR + (v / 32) * 0x10);
        if w & (1 << (v % 32)) != 0 {
            return true;
        }
        v += 1;
    }
    false
}

/// Whether `dest` names one core as a physical destination: xAPIC has 8
/// bits (a larger ID would be truncated to another core's) and 0xff is
/// the broadcast ID; x2APIC's broadcast ID is 0xffff_ffff (Intel SDM
/// vol. 3A §11.6.1, §11.12.9).
pub fn valid_physical_dest(dest: u32, x2apic: bool) -> bool {
    if x2apic { dest != u32::MAX } else { dest < 0xff }
}

/// Send an IPI with physical destination mode to one core. A destination
/// that does not name exactly one core sends nothing.
pub fn send_ipi(dest: u32, icr_lo: u32) {
    if !valid_physical_dest(dest, is_x2apic()) {
        return;
    }
    if is_x2apic() {
        wrmsr(0x830, ((dest as u64) << 32) | icr_lo as u64);
    } else {
        write(REG_ICR_HI, dest << 24);
        write(REG_ICR_LO, icr_lo);
        while read(REG_ICR_LO) & (1 << 12) != 0 {
            core::hint::spin_loop();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_xapic_needs_a_mapped_register_page() {
        let top = 16 << 30;
        assert_eq!(registers(top, true, top), Some(Registers::Msr));
        assert_eq!(registers(top | X2_ENABLE, false, top), Some(Registers::Msr));
        assert_eq!(registers(top, false, top), None);
        let last_page = top - 4096;
        assert_eq!(
            registers(last_page | (1 << 11), false, top),
            Some(Registers::Mmio(fl4_core::layout::pptr(last_page)))
        );
    }

    /// Audit round 5 F2: an MADT x2APIC entry's ID above 0xfe cannot be
    /// sent an xAPIC IPI (0x100 would become 0x00, the boot core), and
    /// neither mode's broadcast ID names one core.
    #[test]
    fn physical_destinations_name_exactly_one_core() {
        assert!(valid_physical_dest(0, false));
        assert!(valid_physical_dest(0xfe, false));
        assert!(!valid_physical_dest(0xff, false));
        assert!(!valid_physical_dest(0x100, false));
        assert!(!valid_physical_dest(0x101, false));
        assert!(!valid_physical_dest(u32::MAX, false));
        assert!(valid_physical_dest(0xff, true));
        assert!(valid_physical_dest(0x100, true));
        assert!(valid_physical_dest(u32::MAX - 1, true));
        assert!(!valid_physical_dest(u32::MAX, true));
    }

    /// Audit F6: an AP works only in the boot core's mode and, in xAPIC
    /// mode, at the boot core's register page.
    #[test]
    fn application_processors_use_the_boot_cores_apic_mode_and_page() {
        let top = 16 << 30;
        let page = 0xfee0_0000u64;
        let en = 1 << 11;
        let mmio = Some(Registers::Mmio(fl4_core::layout::pptr(page)));
        // Both x2APIC: the CPU has it, or the firmware enabled it.
        assert_eq!(ap_registers(page | en, true, true, page, top), Some(Registers::Msr));
        assert_eq!(ap_registers(page | en | X2_ENABLE, false, true, page, top), Some(Registers::Msr));
        // x2APIC boot core, xAPIC-only AP: rejected, nothing written.
        assert_eq!(ap_registers(page | en, false, true, page, top), None);
        // Both xAPIC at the boot core's page; an x2APIC-capable AP stays
        // in xAPIC mode with the boot core.
        assert_eq!(ap_registers(page | en, false, false, page, top), mmio);
        assert_eq!(ap_registers(page | en, true, false, page, top), mmio);
        assert_eq!(ap_registers(page, false, false, page, top), mmio);
        // xAPIC boot core, AP the firmware left in x2APIC mode: rejected
        // (it would switch every core to MSR access).
        assert_eq!(ap_registers(page | en | X2_ENABLE, true, false, page, top), None);
        assert_eq!(ap_registers(page | en | X2_ENABLE, false, false, page, top), None);
        // xAPIC at another page than the boot core's: rejected, mappable
        // or not.
        assert_eq!(ap_registers((page + 0x1000) | en, false, false, page, top), None);
        assert_eq!(ap_registers(0x1000 | en, true, false, page, top), None);
        assert_eq!(ap_registers(top | en, false, false, page, top), None);
        // The boot core's own page past the window: rejected as before.
        assert_eq!(ap_registers(top | en, false, false, top, top), None);
    }

    fn set_in_service(v: u32) {
        let r = REG_ISR + (v / 32) * 0x10;
        FAKE[(r >> 4) as usize].fetch_or(1 << (v % 32), Ordering::Relaxed);
    }

    /// Audit F2: an interrupt the APIC delivers on a vector of the trap
    /// range (0xa0..=0xfe) is acknowledged; an `int n` on one is not, nor
    /// is the spurious vector or a vector of the IRQ range (the core
    /// acknowledges those itself).
    #[test]
    fn stray_vectors_are_acknowledged_only_when_in_service() {
        assert_eq!(STRAY_MIN, 0xa0);
        for v in [0xa0u32, 0xb3, 0xfe] {
            // `int n` from user code: nothing in service.
            assert!(!ack_stray(v as u64));
            set_in_service(v);
            // The timer, in service below it, keeps its own ISR bit.
            set_in_service(0x9d);
            assert!(ack_stray(v as u64));
            assert!(!in_service(v) && in_service(0x9d));
            assert!(!ack_stray(v as u64));
            eoi();
            assert!(!in_service(0x9d));
        }
        for v in [0x9du32, 0x9f, 0xff] {
            set_in_service(v);
            assert!(!ack_stray(v as u64));
            assert!(in_service(v));
            eoi();
        }
    }
}
