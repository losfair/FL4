//! FL4's object store over physical memory (trusted, DESIGN.md §5).
//!
//! `PhysStore` implements `fl4_core::machine::Store` by reading and writing
//! kernel virtual addresses. Every address the core uses is in the kernel
//! window or the kernel image, both always mapped. With `tx` set, accesses
//! go through the calling core's transaction (`tx`, DESIGN.md §7).
#![no_std]

pub mod tx;

use fl4_core::machine::Store;

/// Physical memory through the kernel window.
pub struct Phys;

impl tx::Mem for Phys {
    #[inline(always)]
    fn load(&self, addr: u64) -> u64 {
        unsafe { core::ptr::read_volatile(addr as *const u64) }
    }
    #[inline(always)]
    fn store(&self, addr: u64, v: u64) {
        unsafe { core::ptr::write_volatile(addr as *mut u64, v) }
    }
    #[inline(always)]
    fn clear(&self, addr: u64, len: u64) {
        // The caller has exclusive access: a single core, the serial
        // gate, or every covering stripe held until publication.
        unsafe { core::ptr::write_bytes(addr as *mut u8, 0, len as usize) }
    }
}

pub struct PhysStore {
    pub ks_base: u64,
    pub frame_masks: (u64, u64),
    pub cpu: u64,
    /// Run inside this core's transaction.
    pub tx: bool,
}

impl Store for PhysStore {
    #[inline(always)]
    fn frame_masks(&self) -> (u64, u64) { self.frame_masks }

    #[inline(always)]
    fn read(&self, addr: u64) -> u64 {
        debug_assert!(addr & 7 == 0);
        if self.tx {
            tx::read(self.cpu, &Phys, addr)
        } else {
            unsafe { core::ptr::read_volatile(addr as *const u64) }
        }
    }

    #[inline(always)]
    fn read_pair(&self, addr: u64) -> (u64, u64) {
        debug_assert!(addr & 7 == 0);
        if self.tx {
            tx::read_pair(self.cpu, &Phys, addr)
        } else {
            (self.read(addr), self.read(addr.wrapping_add(8)))
        }
    }

    #[inline(always)]
    fn write(&mut self, addr: u64, v: u64) {
        debug_assert!(addr & 7 == 0);
        if self.tx {
            tx::write(self.cpu, addr, v)
        } else {
            unsafe { core::ptr::write_volatile(addr as *mut u64, v) }
        }
    }

    #[inline(always)]
    fn zero(&mut self, addr: u64, len: u64) {
        if self.tx {
            tx::zero(self.cpu, addr, len)
        } else {
            unsafe { core::ptr::write_bytes(addr as *mut u8, 0, len as usize) }
        }
    }

    #[inline(always)]
    fn clear_free(&mut self, addr: u64, len: u64) {
        if self.tx {
            tx::clear_free(self.cpu, &Phys, addr, len)
        } else {
            unsafe { core::ptr::write_bytes(addr as *mut u8, 0, len as usize) }
        }
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

/// A store whose mode is fixed for one kernel entry. Both specializations
/// use the same primitives as PhysStore; LLVM removes the per-word mode
/// branch. The runtime chooses the mode and provides the synchronization.
pub struct EntryStore<const TX: bool> {
    ks_base: u64,
    frame_masks: (u64, u64),
    cpu: u64,
}

impl PhysStore {
    pub fn specialize<const TX: bool>(&self) -> EntryStore<TX> {
        debug_assert_eq!(self.tx, TX);
        EntryStore {
            ks_base: self.ks_base,
            frame_masks: self.frame_masks,
            cpu: self.cpu,
        }
    }
}

impl<const TX: bool> EntryStore<TX> {
    #[inline(always)]
    fn phys(&self) -> PhysStore {
        PhysStore { ks_base: self.ks_base, frame_masks: self.frame_masks, cpu: self.cpu, tx: TX }
    }
}

impl<const TX: bool> Store for EntryStore<TX> {
    #[inline(always)]
    fn frame_masks(&self) -> (u64, u64) { self.frame_masks }
    #[inline(always)]
    fn read(&self, addr: u64) -> u64 { self.phys().read(addr) }
    #[inline(always)]
    fn read_pair(&self, addr: u64) -> (u64, u64) { self.phys().read_pair(addr) }
    #[inline(always)]
    fn write(&mut self, addr: u64, v: u64) { self.phys().write(addr, v); }
    #[inline(always)]
    fn zero(&mut self, addr: u64, len: u64) { self.phys().zero(addr, len); }
    #[inline(always)]
    fn clear_free(&mut self, addr: u64, len: u64) { self.phys().clear_free(addr, len); }
    #[inline(always)]
    fn ks_base(&self) -> u64 { self.ks_base }
    #[inline(always)]
    fn cur_cpu(&self) -> u64 { self.cpu }
}
