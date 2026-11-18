//! IOAPICs found in the ACPI MADT. All pins start masked; user space
//! routes pins to vectors through IRQControl.
//!
//! Every IOAPIC register access is two MMIO accesses (select, then the
//! window), and `ROUTE` must match what the pins hold: both happen under
//! `LOCK`, with interrupts off, since several cores may program or mask
//! pins at once (a committed transaction's `Effect::Mask` runs outside the
//! serial gate).
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

pub const MAX_IOAPICS: usize = 8;
const REG_VER: u32 = 1;
const MASKED: u32 = 1 << 16;
const VALID: u64 = 1 << 63;

static BASE: [AtomicU64; MAX_IOAPICS] = [const { AtomicU64::new(0) }; MAX_IOAPICS];
static PINS: [AtomicU64; MAX_IOAPICS] = [const { AtomicU64::new(0) }; MAX_IOAPICS];
static COUNT: AtomicU64 = AtomicU64::new(0);
/// Low word of each redirection entry as last programmed, per IRQ: bit 63
/// valid, bits 32..39 ioapic, 40..47 pin, 0..31 the entry. At most one
/// valid entry names any pin.
static ROUTE: [AtomicU64; 256] = [const { AtomicU64::new(0) }; 256];
static LOCK: AtomicBool = AtomicBool::new(false);

/// `LOCK`, held with interrupts off; dropping it restores IF.
struct Guard {
    interrupts: bool,
}

fn lock() -> Guard {
    let interrupts = disable_interrupts();
    while LOCK.compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed).is_err() {
        core::hint::spin_loop();
    }
    Guard { interrupts }
}

impl Drop for Guard {
    fn drop(&mut self) {
        LOCK.store(false, Ordering::Release);
        if self.interrupts {
            unsafe { core::arch::asm!("sti", options(nomem, nostack)) };
        }
    }
}

/// Clear IF; returns whether it was set. (Host tests run in user mode,
/// where IF stays as it is.)
#[cfg(not(test))]
fn disable_interrupts() -> bool {
    let flags: u64;
    unsafe { core::arch::asm!("pushfq", "pop {}", "cli", out(reg) flags, options(nomem)) };
    flags & (1 << 9) != 0
}

#[cfg(test)]
fn disable_interrupts() -> bool {
    false
}

#[cfg(not(test))]
fn read(i: usize, reg: u32) -> u32 {
    let b = BASE[i].load(Ordering::Relaxed);
    unsafe {
        crate::sev::write_mmio32(b, reg);
        crate::sev::read_mmio32(b + 0x10)
    }
}

#[cfg(not(test))]
fn write(i: usize, reg: u32, v: u32) {
    let b = BASE[i].load(Ordering::Relaxed);
    unsafe {
        crate::sev::write_mmio32(b, reg);
        crate::sev::write_mmio32(b + 0x10, v);
    }
}

/// Host tests: each IOAPIC is a plain register file.
#[cfg(test)]
static FAKE: [[core::sync::atomic::AtomicU32; 256]; MAX_IOAPICS] =
    [const { [const { core::sync::atomic::AtomicU32::new(0) }; 256] }; MAX_IOAPICS];

#[cfg(test)]
fn read(i: usize, reg: u32) -> u32 {
    FAKE[i][reg as usize].load(Ordering::Relaxed)
}

#[cfg(test)]
fn write(i: usize, reg: u32, v: u32) {
    FAKE[i][reg as usize].store(v, Ordering::Relaxed)
}

fn lo_reg(pin: u64) -> u32 {
    0x10 + 2 * pin as u32
}

fn route_pin(r: u64) -> (usize, u64) {
    (((r >> 32) & 0xff) as usize, (r >> 40) & 0xff)
}

/// Register an IOAPIC mapped at kernel address `mmio`; masks every pin.
pub fn add(mmio: u64) {
    let _g = lock();
    let i = COUNT.load(Ordering::Relaxed) as usize;
    if i >= MAX_IOAPICS {
        return;
    }
    BASE[i].store(mmio, Ordering::Relaxed);
    let n = ((read(i, REG_VER) >> 16) & 0xff) + 1;
    PINS[i].store(n as u64, Ordering::Relaxed);
    for p in 0..n {
        write(i, 0x10 + 2 * p, MASKED);
        write(i, 0x11 + 2 * p, 0);
    }
    COUNT.store(i as u64 + 1, Ordering::Relaxed);
}

pub fn count() -> u64 {
    COUNT.load(Ordering::Relaxed)
}

pub fn pins(i: u64) -> u64 {
    if i < count() {
        PINS[i as usize].load(Ordering::Relaxed)
    } else {
        0
    }
}

/// Route `pin` of `ioapic` to `vector` on the boot CPU (`dest`), masked.
/// A nonzero `high` replaces the destination word and `lo_extra` is ORed
/// into the low word (remappable-format entries, l4h 0025).
///
/// Whatever routed this pin before loses it, so masking or unmasking the
/// old IRQ no longer reaches the pin; and the pin the IRQ came from before,
/// if another, is masked, so it no longer raises this vector.
///
/// A compatibility-format entry has an 8-bit destination (bits 56..63):
/// an x2APIC ID above 255 cannot be named there, and its low byte would
/// name some other core, or none. Such a request changes nothing and
/// returns false; only a remappable entry can reach that core.
#[allow(clippy::too_many_arguments)]
pub fn map(ioapic: u64, pin: u64, level: u64, polarity: u64, vector: u64, dest: u32, high: u32, lo_extra: u32) -> bool {
    if high == 0 && dest > 0xff {
        return false;
    }
    let i = ioapic as usize;
    let lo = MASKED | ((level as u32) << 15) | ((polarity as u32) << 13) | lo_extra | vector as u32;
    let irq = vector.wrapping_sub(0x20) as usize;
    let _g = lock();
    for (j, slot) in ROUTE.iter().enumerate() {
        let r = slot.load(Ordering::Relaxed);
        if r & VALID == 0 {
            continue;
        }
        let (ri, rpin) = route_pin(r);
        if (ri, rpin) == (i, pin) {
            slot.store(0, Ordering::Relaxed);
        } else if j == irq {
            write(ri, lo_reg(rpin), r as u32 | MASKED);
            slot.store(0, Ordering::Relaxed);
        }
    }
    write(i, lo_reg(pin), MASKED);
    write(i, lo_reg(pin) + 1, if high != 0 { high } else { dest << 24 });
    write(i, lo_reg(pin), lo);
    if irq < 256 {
        ROUTE[irq].store(VALID | (ioapic << 32) | (pin << 40) | lo as u64, Ordering::Relaxed);
    }
    true
}

/// Mask or unmask whatever pin `irq` is routed from.
pub fn mask(irq: u64, masked: bool) {
    if irq >= 256 {
        return;
    }
    let _g = lock();
    let r = ROUTE[irq as usize].load(Ordering::Relaxed);
    if r & VALID == 0 {
        return;
    }
    let (i, pin) = route_pin(r);
    let mut lo = r as u32;
    if masked {
        lo |= MASKED;
    } else {
        lo &= !MASKED;
    }
    write(i, lo_reg(pin), lo);
    ROUTE[irq as usize].store((r & !0xffff_ffff) | lo as u64, Ordering::Relaxed);
}

/// `irq` is free again: mask the pin it is routed from, if any, and forget
/// the route.
pub fn forget(irq: u64) {
    if irq >= 256 {
        return;
    }
    let _g = lock();
    let r = ROUTE[irq as usize].load(Ordering::Relaxed);
    if r & VALID != 0 {
        let (i, pin) = route_pin(r);
        write(i, lo_reg(pin), r as u32 | MASKED);
    }
    ROUTE[irq as usize].store(0, Ordering::Relaxed);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lo(i: usize, pin: u64) -> u32 {
        read(i, lo_reg(pin))
    }

    fn masked(i: usize, pin: u64) -> bool {
        lo(i, pin) & MASKED != 0
    }

    /// One test: the IOAPIC state is global.
    #[test]
    fn routes_follow_rebinds_and_forget() {
        FAKE[0][REG_VER as usize].store(23 << 16, Ordering::Relaxed);
        FAKE[1][REG_VER as usize].store(23 << 16, Ordering::Relaxed);
        add(0x1000);
        add(0x2000);
        assert_eq!((count(), pins(0), pins(1)), (2, 24, 24));
        assert!((0..24).all(|p| masked(0, p) && masked(1, p)));

        // IRQ 5 on pin 3, unmasked.
        map(0, 3, 0, 0, 0x25, 0, 0, 0);
        mask(5, false);
        assert_eq!(lo(0, 3), 0x25);

        // Pin 3 rebound to IRQ 9: IRQ 5's route no longer reaches it.
        map(0, 3, 1, 0, 0x29, 0, 0, 0);
        mask(9, false);
        assert_eq!(lo(0, 3), 0x29 | 1 << 15);
        mask(5, true);
        mask(5, false);
        assert_eq!(lo(0, 3), 0x29 | 1 << 15, "a stale route reprogrammed the pin");
        mask(9, true);
        assert!(masked(0, 3));
        mask(5, false);
        assert!(masked(0, 3), "a stale route unmasked the pin");

        // IRQ 9 moved to pin 7 of the second IOAPIC: pin 3 is masked and
        // left alone after.
        mask(9, false);
        map(1, 7, 0, 0, 0x29, 0, 0, 0);
        assert!(masked(0, 3));
        mask(9, false);
        assert_eq!(lo(1, 7), 0x29);
        assert!(masked(0, 3));

        // Freeing IRQ 9 masks its pin, and its route is gone.
        forget(9);
        assert!(masked(1, 7));
        mask(9, false);
        assert!(masked(1, 7));
        assert_eq!(ROUTE[9].load(Ordering::Relaxed), 0);

        // At most one route names any pin.
        map(0, 4, 0, 0, 0x30, 0, 0, 0);
        map(0, 4, 0, 0, 0x31, 0, 0, 0);
        map(0, 4, 0, 0, 0x32, 0, 0, 0);
        let named = ROUTE.iter().filter(|r| {
            let r = r.load(Ordering::Relaxed);
            r & VALID != 0 && route_pin(r) == (0, 4)
        });
        assert_eq!(named.count(), 1);

        // An x2APIC ID above 255 does not fit a compatibility entry's
        // destination: the request leaves the pin and its route alone
        // instead of sending the IRQ to the core named by the low byte.
        assert!(map(0, 5, 0, 0, 0x33, 0x12, 0, 0));
        assert_eq!(read(0, lo_reg(5) + 1), 0x12 << 24);
        assert!(!map(0, 5, 0, 0, 0x34, 0x101, 0, 0));
        assert_eq!(read(0, lo_reg(5) + 1), 0x12 << 24, "destination truncated to its low byte");
        assert_eq!(lo(0, 5), 0x33 | MASKED);
        assert_ne!(ROUTE[0x13].load(Ordering::Relaxed) & VALID, 0);
        assert_eq!(ROUTE[0x14].load(Ordering::Relaxed), 0);
        // A remappable entry carries its own destination word.
        assert!(map(0, 5, 0, 0, 0x34, 0x101, (7 << 17) | (1 << 16), 0));
        assert_eq!(read(0, lo_reg(5) + 1), (7 << 17) | (1 << 16));
        assert!(!LOCK.load(Ordering::Relaxed));
    }
}
