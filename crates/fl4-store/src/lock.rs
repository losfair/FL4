//! The runtime's atomics, and the object locks of the local paths beside
//! the serial gate (fl4-sync `run_syscall`, DESIGN.md §7).
use core::sync::atomic::{AtomicU64, Ordering};

/// Cores the runtime supports: the serial gate's active flags.
pub const MAX_CPUS: usize = 128;

/// The runtime's atomics (serial gate, object locks) go through this, so
/// that the simulator can run them on a store-buffer model of x86-TSO
/// (DESIGN.md §10). On hardware they are the operations themselves.
pub trait Mem {
    #[inline(always)]
    fn a_load(&self, a: &AtomicU64, o: Ordering) -> u64 {
        a.load(o)
    }
    #[inline(always)]
    fn a_store(&self, a: &AtomicU64, v: u64, o: Ordering) {
        a.store(v, o)
    }
    /// A strong compare-and-swap: a lock attempt that fails spuriously
    /// (LL/SC without LSE) would send a local path to the gate.
    #[inline(always)]
    fn a_cas(&self, a: &AtomicU64, old: u64, new: u64, ok: Ordering, err: Ordering) -> Result<u64, u64> {
        a.compare_exchange(old, new, ok, err)
    }
    #[inline(always)]
    fn a_add(&self, a: &AtomicU64, v: u64, o: Ordering) -> u64 {
        a.fetch_add(v, o)
    }
    #[inline(always)]
    fn fence(&self, o: Ordering) {
        core::sync::atomic::fence(o)
    }
}

const LOCK_BITS: u32 = 12;
const LOCKS: usize = 1 << LOCK_BITS;

/// One lock word per cache line: locks of different cores' objects never
/// share a line.
#[repr(align(64))]
struct Lock(AtomicU64);

static TABLE: [Lock; LOCKS] = [const { Lock(AtomicU64::new(0)) }; LOCKS];

/// The lock covering the object at `addr`: a hash, so that neighbouring
/// objects (a guest's per-vCPU endpoints) use different locks. Two objects
/// sharing one only make the second attempt fail.
#[inline(always)]
fn index(addr: u64) -> usize {
    // 16-byte granularity: endpoints (16) and slots and replies (32) use
    // different locks; a pair of neighbouring page-table entries (8
    // bytes) shares one. 8-byte granularity separates those too, but cost
    // an l4h guest's page faults 9% at 4 workers (8 vCPUs), against the
    // spurious contention it removes.
    ((addr >> 4).wrapping_mul(0x9e37_79b9_7f4a_7c15) >> (64 - LOCK_BITS)) as usize
}

/// Take the lock of the object at `addr` without waiting. True if it was
/// free, which `held` then records.
pub fn try_lock_object<M: Mem>(m: &M, addr: u64, held: &mut Held) -> bool {
    let e = index(addr);
    // Two objects of one path on one lock word: this core holds it
    // already (recorded once, so released once). Otherwise the path
    // would decline whenever they collide, every time for the same pair
    // (a vCPU's notification and a slot of its CSpace).
    if held.e[..held.n].contains(&e) {
        return true;
    }
    if held.n == MAX_HELD
        || m.a_load(&TABLE[e].0, Ordering::Relaxed) != 0
        || m.a_cas(&TABLE[e].0, 0, 1, Ordering::Acquire, Ordering::Relaxed).is_err()
    {
        return false;
    }
    held.e[held.n] = e;
    held.n += 1;
    true
}

/// Release what `try_lock_object` took.
pub fn unlock_held<M: Mem>(m: &M, held: &mut Held) {
    while held.n > 0 {
        held.n -= 1;
        m.a_store(&TABLE[held.e[held.n]].0, 0, Ordering::Release);
    }
}

pub const MAX_HELD: usize = 6;

/// Locks `try_lock_object` holds.
pub struct Held {
    e: [usize; MAX_HELD],
    n: usize,
}

impl Held {
    pub const fn new() -> Held {
        Held { e: [0; MAX_HELD], n: 0 }
    }
}

impl Default for Held {
    fn default() -> Held {
        Held::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Atomics;
    impl Mem for Atomics {}

    /// Two objects of one path on one lock word (here the same object
    /// twice, and its neighbour in the same 16 bytes): the second is this
    /// core's already, recorded once and released once.
    #[test]
    fn a_lock_word_this_core_holds_is_taken_again() {
        let (a, b) = (0x50_0000, 0x50_0008);
        assert_eq!(index(a), index(b));
        let mut h = Held::new();
        let mut other = Held::new();
        assert!(try_lock_object(&Atomics, a, &mut h));
        assert!(try_lock_object(&Atomics, b, &mut h));
        assert!(try_lock_object(&Atomics, a, &mut h));
        assert_eq!(h.n, 1);
        assert!(!try_lock_object(&Atomics, b, &mut other));
        unlock_held(&Atomics, &mut h);
        assert!(try_lock_object(&Atomics, b, &mut other));
        unlock_held(&Atomics, &mut other);
    }

    #[test]
    fn a_held_lock_refuses_others_until_released() {
        let (a, b) = (0x40_0000, 0x40_1000);
        assert_ne!(index(a), index(b));
        let mut h1 = Held::new();
        let mut h2 = Held::new();
        assert!(try_lock_object(&Atomics, a, &mut h1));
        assert!(!try_lock_object(&Atomics, a, &mut h2));
        assert!(try_lock_object(&Atomics, b, &mut h2));
        unlock_held(&Atomics, &mut h1);
        unlock_held(&Atomics, &mut h2);
        assert!(try_lock_object(&Atomics, a, &mut h1));
        unlock_held(&Atomics, &mut h1);
    }

    #[test]
    fn neighbouring_objects_use_different_locks() {
        // A guest's per-vCPU endpoints, 16 bytes apart.
        let mut seen = [false; LOCKS];
        for i in 0..64u64 {
            let e = index(0x80_0000 + 16 * i);
            assert!(!seen[e]);
            seen[e] = true;
        }
    }

    #[test]
    fn at_most_max_held() {
        let mut h = Held::new();
        for i in 0..MAX_HELD as u64 {
            assert!(try_lock_object(&Atomics, 0x90_0000 + 0x1000 * i, &mut h));
        }
        assert!(!try_lock_object(&Atomics, 0xa0_0000, &mut h));
        unlock_held(&Atomics, &mut h);
    }
}
