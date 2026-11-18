//! Address-space switches, broadcast TLB maintenance (l4h 0015: no IPIs)
//! and user cache maintenance.
use crate::{cpu, percpu};
use core::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use fl4_core::layout;

/// Physical ranges the kernel window maps (for cache maintenance through
/// it), set at boot.
/// As many as the kernel's window can have (fl4-kernel-aarch64 `fl4_boot`).
const MAX_RANGES: usize = 128;
static RANGES: [(AtomicU64, AtomicU64); MAX_RANGES] = [const { (AtomicU64::new(0), AtomicU64::new(0)) }; MAX_RANGES];
static NRANGES: AtomicUsize = AtomicUsize::new(0);

pub fn add_window_range(start: u64, end: u64) {
    let n = NRANGES.load(Ordering::Relaxed);
    if n < MAX_RANGES {
        RANGES[n].0.store(start, Ordering::Relaxed);
        RANGES[n].1.store(end, Ordering::Relaxed);
        NRANGES.store(n + 1, Ordering::Release);
    }
}

/// `[start, start + len)` (physical) lies in one range the kernel window
/// maps.
pub fn in_window(start: u64, len: u64) -> bool {
    let n = NRANGES.load(Ordering::Acquire);
    (0..n).any(|i| {
        let s = RANGES[i].0.load(Ordering::Relaxed);
        let e = RANGES[i].1.load(Ordering::Relaxed);
        s <= start && start.wrapping_add(len) <= e && start.wrapping_add(len) >= start
    })
}

/// Whole-address-space invalidations so far (`invalidate_asid`).
///
/// ASIDs are the hardware ASIDs, so an ASID deleted while another core
/// still runs its old address space can be refilled there with the old
/// translations after the broadcast invalidation; once the ASID names a
/// new address space, that core would use them. So a core that switches
/// address space after any such invalidation first flushes its own TLB.
/// An invalidation counts itself before it broadcasts; a switch that
/// installs an ASID's new root follows the reassignment under the serial
/// gate, so it sees the count of the invalidation that retired the ASID.
///
/// As on x86_64 (tlb.rs), a switch publishes the core's new TTBR0 value,
/// then reads the count; an invalidation bumps the count, then reads which
/// cores run the ASID (`cores_on`). Both are sequentially consistent, so
/// either the invalidating core sees the switching one and calls it, or
/// the switching core sees the new count and flushes.
static ASID_GEN: AtomicU64 = AtomicU64::new(0);

/// The empty user table (fl4-core's `ks::KERNEL_ROOT`, kernel virtual),
/// which a core runs with ASID 0 once the ASID it ran is retired.
static EMPTY_ROOT: AtomicU64 = AtomicU64::new(0);

/// Set once at boot, before any core runs user code.
pub fn set_empty_root(root: u64) {
    EMPTY_ROOT.store(root, Ordering::Relaxed);
}

/// Run on the address space `root` (kernel virtual) with `asid`.
pub fn switch(root: u64, asid: u64) {
    let v = layout::paddr(root) | (asid << 48);
    let me = percpu::cpu_index();
    if percpu::ttbr0(me) != v {
        crate::msr!("ttbr0_el1", v);
        cpu::isb();
    }
    // Publish before reading the count (module comment); also when the
    // value is unchanged, which costs one store.
    percpu::set_ttbr0(v);
    let g = ASID_GEN.load(Ordering::SeqCst);
    // Also when the value is unchanged: a root freed and made again at
    // the same address can take back the same ASID.
    let pc = percpu::get();
    if pc.asid_gen.get() != g {
        // After the switch, so the old tables cannot refill it.
        unsafe { core::arch::asm!("tlbi vmalle1", "dsb nsh", "isb", options(nostack)) };
        pc.asid_gen.set(g);
    }
}

/// Make page-table writes visible to the table walkers before user code
/// runs (exit path).
#[inline(always)]
pub fn publish_tables() {
    cpu::dsb_ishst();
}

pub fn invalidate_page(asid: u64, vaddr: u64) {
    let arg = (asid << 48) | ((vaddr >> 12) & 0xfff_ffff_ffff);
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vae1is, {}", "dsb ish", "isb", in(reg) arg, options(nostack));
    }
}

pub fn invalidate_asid(asid: u64) {
    ASID_GEN.fetch_add(1, Ordering::SeqCst);
    let arg = asid << 48;
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi aside1is, {}", "dsb ish", "isb", in(reg) arg, options(nostack));
    }
}

/// The cores other than this one whose current ASID is `asid`.
pub fn cores_on(asid: u64) -> u64 {
    let me = percpu::cpu_index();
    let online = crate::smp::online_mask();
    let mut m = 0;
    for c in 0..percpu::MAX_CPUS {
        if c != me && online & (1 << c) != 0 && percpu::ttbr0(c) >> 48 == asid {
            m |= 1 << c;
        }
    }
    m
}

/// Remote side of `invalidate_asid` (`smp::CALL_ASID`): the broadcast
/// invalidation has run, but if the ASID was deleted its tables can be
/// freed and reused as soon as the call returns, while this core goes on
/// in the kernel with TTBR0 on them: its table walker may still walk them
/// (speculatively too), refilling the TLB from whatever they have become
/// and, with hardware access flags, setting bit 10 of words in them. So
/// it leaves them now for the empty table with ASID 0 (whose switch, the
/// count having moved, also flushes this core's TLB), and the exit sets
/// the address space again from the current thread's VSpace cap.
pub fn retired(asid: u64) {
    if percpu::ttbr0(percpu::cpu_index()) >> 48 == asid {
        switch(EMPTY_ROOT.load(Ordering::Relaxed), 0);
        percpu::get().vspace_stale.set(true);
    }
}

/// Everything, on every core (boot).
pub fn invalidate_all() {
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vmalle1is", "dsb ish", "isb", options(nostack));
    }
}

/// seL4 `doFlush` for `len` bytes at user address `vaddr` of (`root`,
/// `asid`), physically `paddr`: through the kernel window when it maps
/// the range, otherwise through the user mapping itself.
pub fn cache_op(op: u64, root: u64, asid: u64, vaddr: u64, len: u64, paddr: u64) {
    use fl4_core::vspace::{CACHE_CLEAN, CACHE_CLEAN_INVALIDATE, CACHE_INVALIDATE};
    let (va, switched) = if in_window(paddr, len) {
        (layout::pptr(paddr), None)
    } else {
        let old = percpu::ttbr0(percpu::cpu_index());
        switch(root, asid);
        (vaddr, Some(old))
    };
    if op == CACHE_CLEAN {
        cpu::clean_dcache_poc(va, len);
    } else if op == CACHE_INVALIDATE {
        cpu::inval_dcache_poc(va, len);
    } else if op == CACHE_CLEAN_INVALIDATE {
        cpu::clean_inval_dcache_poc(va, len);
    } else {
        cpu::sync_icache(va, len);
    }
    if let Some(old) = switched {
        crate::msr!("ttbr0_el1", old);
        cpu::isb();
        percpu::set_ttbr0(old);
    }
}
