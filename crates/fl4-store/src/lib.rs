//! FL4's object store over physical memory (trusted, DESIGN.md §5).
//!
//! `PhysStore` implements `fl4_core::machine::Store` by reading and writing
//! kernel virtual addresses. Every address the core uses is in the kernel
//! window or the kernel image, both always mapped. The caller has the
//! access it needs: one core, the serial gate, or a local path's footprint
//! (fl4-sync, DESIGN.md §7).
#![no_std]

pub mod lock;

use fl4_core::machine::Store;

/// Physical memory through the kernel window.
pub struct Phys;

impl lock::Mem for Phys {}

pub struct PhysStore {
    pub ks_base: u64,
    pub frame_masks: (u64, u64),
    pub cpu: u64,
}

impl Store for PhysStore {
    #[inline(always)]
    fn frame_masks(&self) -> (u64, u64) { self.frame_masks }

    #[inline(always)]
    fn read(&self, addr: u64) -> u64 {
        debug_assert!(addr & 7 == 0);
        unsafe { core::ptr::read_volatile(addr as *const u64) }
    }

    #[inline(always)]
    fn read_pair(&self, addr: u64) -> (u64, u64) {
        (self.read(addr), self.read(addr.wrapping_add(8)))
    }

    #[inline(always)]
    fn write(&mut self, addr: u64, v: u64) {
        debug_assert!(addr & 7 == 0);
        unsafe { core::ptr::write_volatile(addr as *mut u64, v) }
    }

    #[inline(always)]
    fn zero(&mut self, addr: u64, len: u64) {
        unsafe { core::ptr::write_bytes(addr as *mut u8, 0, len as usize) }
    }

    #[inline(always)]
    fn clear_free(&mut self, addr: u64, len: u64) {
        self.zero(addr, len)
    }

    #[inline(always)]
    fn ks_base(&self) -> u64 {
        self.ks_base
    }

    #[inline(always)]
    fn cur_cpu(&self) -> u64 {
        self.cpu
    }
}
