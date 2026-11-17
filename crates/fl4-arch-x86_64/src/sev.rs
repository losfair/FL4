//! Base AMD SEV guest memory. Physical addresses in capabilities, BootInfo
//! and device descriptors are always GPAs without the page-table C-bit.
use core::arch::asm;
use core::ptr;
use core::sync::atomic::{AtomicPtr, AtomicU64, Ordering};
use fl4_core::boot::Region;
use fl4_core::layout::{paddr, pptr};

static MASK: AtomicU64 = AtomicU64::new(0);

/// Adjacent to the private physical window in PML4 slot 511.
pub const SHARED_SLOT: usize = 510;
const SHARED_BASE: u64 = 0xffff_ff00_0000_0000;

/// The BSP detected this mask before enabling paging.
pub fn init(mask: u64) { MASK.store(mask, Ordering::Relaxed); }

pub fn mask() -> u64 { MASK.load(Ordering::Relaxed) }

pub fn shared_ptr(pa: u64) -> u64 {
    if mask() == 0 { pptr(pa) } else { SHARED_BASE + pa }
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

fn memory() -> &'static Memory {
    let p = MEMORY.load(Ordering::Acquire);
    assert!(!p.is_null());
    unsafe { &*p }
}

pub fn private_device(pa: u64) -> bool {
    memory().private_devices.iter().any(|r| r.start <= pa && pa < r.end)
}

/// A shared device frame in allocatable RAM can only come from RetypeShared.
/// Device caps cannot be used as IPC buffers, kernel objects or subframe
/// sources. Thus no core uses the private alias during this frame's lifetime.
pub fn is_dma_ram(base: u64, size_bits: u64) -> bool {
    let pa = paddr(base);
    mask() != 0 && matches!(size_bits, 12 | 21)
        && memory().ram.iter().any(|r| r.start <= pa && pa < r.end && r.end - pa >= 1 << size_bits)
}

/// Called under the serial gate after exclusive ownership or the last
/// unmap and its synchronous shootdown. CLFLUSH evicts the old representation
/// from the coherence domain before any store through the new alias.
/// Zero both transitions: sharing never publishes previous private contents,
/// and retiring a DMA buffer never imports host-controlled bytes.
pub fn transition(base: u64, size_bits: u64, shared: bool) {
    let alias = shared_ptr(paddr(base));
    let (old, new) = if shared { (base, alias) } else { (alias, base) };
    let len = 1usize << size_bits;
    // All SEV-capable AMD processors use 64-byte cache lines.
    unsafe {
        asm!("mfence", options(nostack, preserves_flags));
        for offset in (0..len).step_by(64) {
            asm!("clflush [{}]", in(reg) old + offset as u64, options(nostack, preserves_flags));
        }
        asm!("mfence", options(nostack, preserves_flags));
        ptr::write_bytes(new as *mut u8, 0, len);
        asm!("mfence", options(nostack, preserves_flags));
    }
}
