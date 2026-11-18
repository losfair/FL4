//! AMD SEV guest memory. Physical addresses in capabilities, BootInfo
//! and device descriptors are always GPAs without the page-table C-bit.
use core::arch::asm;
use core::ptr;
use core::sync::atomic::{AtomicPtr, AtomicU64, Ordering};
use fl4_core::boot::Region;
use fl4_core::layout::{paddr, pptr};

pub mod mmio;
pub mod snp;

static MASK: AtomicU64 = AtomicU64::new(0);

/// Adjacent to the private physical window in PML4 slot 511.
pub const SHARED_SLOT: usize = 510;
const SHARED_BASE: u64 = 0xffff_ff00_0000_0000;

/// The BSP detected this mask before enabling paging.
pub fn init(mask: u64) { MASK.store(mask, Ordering::Relaxed); }

pub fn mask() -> u64 { MASK.load(Ordering::Relaxed) }

/// End of the contiguous GPA range below both MAXPHYADDR and the C-bit.
/// AMD APM vol. 2 §15.34.6 applies PhysAddrReduction to the system physical
/// address after nested translation. The guest uses its advertised width.
pub fn gpa_top(max_paddr: u64, private_mask: u64) -> u64 {
    if private_mask == 0 { max_paddr } else { max_paddr.min(private_mask) }
}

fn shared_ptr(pa: u64) -> u64 {
    if mask() == 0 { pptr(pa) } else { SHARED_BASE + pa }
}

/// Only form a direct-window pointer after the complete MMIO span fits.
pub fn mmio_ptr(pa: u64, bytes: u64, window_top: u64) -> Option<u64> {
    (bytes != 0 && pa < window_top && bytes <= window_top - pa).then(|| shared_ptr(pa))
}

/// # Safety
/// The caller owns the MMIO register at a validated device-window address.
pub unsafe fn read_mmio32(addr: u64) -> u32 {
    if snp::active() {
        snp::mmio(addr - SHARED_BASE, 4, None) as u32
    } else {
        unsafe { ptr::read_volatile(addr as *const u32) }
    }
}

/// # Safety
/// The caller owns the MMIO register at a validated device-window address.
pub unsafe fn write_mmio32(addr: u64, value: u32) {
    if snp::active() {
        snp::mmio(addr - SHARED_BASE, 4, Some(value as u64));
    } else {
        unsafe { ptr::write_volatile(addr as *mut u32, value) }
    }
}

/// Installed once before the BSP releases the APs. RAM handed to userspace
/// as ordinary untypeds is disjoint from all the initial device untypeds.
pub struct Memory {
    pub ram: &'static [Region],
    pub private_devices: &'static [Region],
}

static MEMORY: AtomicPtr<Memory> = AtomicPtr::new(ptr::null_mut());

pub fn install(memory: &'static Memory) {
    MEMORY.store(ptr::from_ref(memory).cast_mut(), Ordering::Release);
}

fn memory() -> Option<&'static Memory> {
    // install publishes a static snapshot before the APs start.
    unsafe { MEMORY.load(Ordering::Acquire).as_ref() }
}

pub fn private_device(pa: u64) -> bool {
    memory().is_some_and(|m| m.private_devices.iter().any(|r| r.start <= pa && pa < r.end))
}

/// A shared device frame in allocatable RAM can only come from RetypeShared.
/// Device caps cannot be used as IPC buffers, kernel objects or subframe
/// sources. Thus no core uses the private alias during this frame's lifetime.
pub fn is_dma_ram(base: u64, bytes: u64) -> bool {
    let pa = paddr(base);
    mask() != 0 && bytes > 0 && bytes <= 1 << 21 && (pa | bytes) & 4095 == 0
        && memory().is_some_and(|m| m.ram.iter().any(|r| r.start <= pa && pa < r.end && bytes <= r.end - pa))
}

/// Evict the entire representation, waiting for writeback before an alias
/// can be touched or the frame published. Base SEV CPUs use 64-byte lines.
fn flush(base: u64, bytes: u64, optimized: bool) {
    unsafe {
        if optimized {
            for offset in (0..bytes).step_by(64) {
                asm!("clflushopt [{}]", in(reg) base + offset, options(nostack, preserves_flags));
            }
        } else {
            for offset in (0..bytes).step_by(64) {
                asm!("clflush [{}]", in(reg) base + offset, options(nostack, preserves_flags));
            }
        }
        asm!("mfence", options(nostack, preserves_flags));
    }
}

/// Called under the serial gate after exclusive ownership or the last unmap
/// and its synchronous shootdown. A new shared range must reach memory even
/// when its first consumer uses uncached loads or non-snooping DMA.
pub fn transition(base: u64, bytes: u64, shared: bool) {
    transition_inner(base, bytes, shared, true);
}

fn transition_inner(base: u64, bytes: u64, shared: bool, shootdown: bool) {
    let alias = shared_ptr(paddr(base));
    let (old, new) = if shared { (base, alias) } else { (alias, base) };
    let optimized = crate::cpu::cpuid(7, 0).ebx & (1 << 23) != 0;
    unsafe { asm!("mfence", options(nostack, preserves_flags)); }
    flush(old, bytes, optimized);
    if snp::active() {
        invalidate_aliases(base, bytes);
        if shootdown {
            crate::smp::remote_call(crate::smp::CALL_SNP_INVLPG, base, bytes, crate::smp::online_mask());
        }
        snp::change_state(base, paddr(base), bytes, shared);
    }
    unsafe {
        ptr::write_bytes(new as *mut u8, 0, bytes as usize);
        asm!("mfence", options(nostack, preserves_flags));
    }
    if shared { flush(new, bytes, optimized); }
}

/// Used by both ends of a synchronous shootdown before an RMP change.
pub(crate) fn invalidate_aliases(base: u64, bytes: u64) {
    let alias = shared_ptr(paddr(base));
    for offset in (0..bytes).step_by(4096) {
        crate::cpu::invlpg(base + offset);
        crate::cpu::invlpg(alias + offset);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contiguous_gpas_stop_at_the_guest_width_or_the_visibility_bit() {
        assert_eq!(gpa_top(1 << 52, 0), 1 << 52);
        assert_eq!(gpa_top(1 << 52, 1 << 51), 1 << 51);
        assert_eq!(gpa_top(1 << 48, 1 << 39), 1 << 39);
        assert_eq!(gpa_top(1 << 36, 1 << 51), 1 << 36);
    }

    #[test]
    fn uninstalled_memory_and_mmio_bounds() {
        assert!(!private_device(0));
        assert!(!is_dma_ram(pptr(0x200000), 4096));
        let top = 16 << 30;
        assert_eq!(mmio_ptr(top - 4096, 4096, top), Some(pptr(top - 4096)));
        assert_eq!(mmio_ptr(top - 1, 2, top), None);
        assert_eq!(mmio_ptr(u64::MAX, 4096, top), None);
        assert_eq!(mmio_ptr(0, 0, top), None);
    }
}
