//! CSpace addressing (seL4 kernel/cspace.c).

use crate::capability::Cap;
use crate::error::{Exc, KResult, LookupFault, SysError};
use crate::layout::tcb as t;
use crate::machine::Store;
use crate::obj::{Slot, Tcb};

pub const WORD_BITS: u64 = 64;

/// Result of `resolveAddressBits`: the slot reached and the bits left.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Resolved {
    pub slot: Slot,
    pub bits_left: u64,
}

fn mask(bits: u64) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << (bits & 63)).wrapping_sub(1)
    }
}

/// seL4 `resolveAddressBits`. Errors are lookup faults.
#[inline(always)]
pub fn resolve_address_bits<S: Store>(s: &S, node_cap: Cap, cptr: u64, n_bits: u64) -> Result<Resolved, LookupFault> {
    let mut cap = node_cap;
    let mut n = n_bits;
    // Each level consumes at least one bit, so this ends within 64 rounds.
    let mut fuel: u64 = 65;
    loop {
        let (ptr, radix, guard_size, guard) = match cap {
            Cap::CNode { ptr, radix, guard_size, guard } => (ptr, radix, guard_size, guard),
            _ => return Err(LookupFault::InvalidRoot),
        };
        let level = radix.wrapping_add(guard_size);
        if level == 0 || fuel == 0 {
            // "All CNodes must resolve bits": unreachable for well-formed caps.
            return Err(LookupFault::InvalidRoot);
        }
        fuel -= 1;
        let shift = n.wrapping_sub(guard_size) & 63;
        let g = (cptr >> shift) & mask(guard_size);
        if guard_size > n || g != guard {
            return Err(LookupFault::GuardMismatch { guard_found: guard, bits_left: n, guard_size });
        }
        if level > n {
            return Err(LookupFault::DepthMismatch { bits_found: level, bits_left: n });
        }
        let offset = (cptr >> ((n - level) & 63)) & mask(radix);
        let slot = Slot::index(ptr, offset);
        if n == level {
            return Ok(Resolved { slot, bits_left: 0 });
        }
        n -= level;
        let next = slot.cap(s);
        match next {
            Cap::CNode { .. } => cap = next,
            _ => return Ok(Resolved { slot, bits_left: n }),
        }
    }
}

/// seL4 `lookupSlot`: resolve a CPtr in the thread's CSpace.
#[inline(always)]
pub fn lookup_slot<S: Store>(s: &S, thread: Tcb, cptr: u64) -> Result<Resolved, LookupFault> {
    let root = thread.slot(t::SLOT_CTABLE).cap(s);
    resolve_address_bits(s, root, cptr, WORD_BITS)
}

/// seL4 `lookupCap`, with lookup faults as kernel exceptions.
#[inline(always)]
pub fn lookup_cap<S: Store>(s: &S, thread: Tcb, cptr: u64) -> KResult<Cap> {
    match lookup_slot(s, thread, cptr) {
        Ok(r) => Ok(r.slot.cap(s)),
        Err(lf) => Err(Exc::Lookup(lf)),
    }
}

/// seL4 `lookupCapAndSlot`.
pub fn lookup_cap_and_slot<S: Store>(s: &S, thread: Tcb, cptr: u64) -> KResult<(Cap, Slot)> {
    match lookup_slot(s, thread, cptr) {
        Ok(r) => Ok((r.slot.cap(s), r.slot)),
        Err(lf) => Err(Exc::Lookup(lf)),
    }
}

/// seL4 `lookupSlotForCNodeOp`; errors are syscall errors.
pub fn lookup_slot_for_cnode_op<S: Store>(s: &S, is_source: bool, root: Cap, cptr: u64, depth: u64) -> KResult<Slot> {
    if !matches!(root, Cap::CNode { .. }) {
        return Err(Exc::Sys(SysError::FailedLookup { source: is_source, lf: LookupFault::InvalidRoot }));
    }
    if depth < 1 || depth > WORD_BITS {
        return Err(Exc::Sys(SysError::RangeError { min: 1, max: WORD_BITS }));
    }
    match resolve_address_bits(s, root, cptr, depth) {
        Err(lf) => Err(Exc::Sys(SysError::FailedLookup { source: is_source, lf })),
        Ok(r) => {
            if r.bits_left != 0 {
                Err(Exc::Sys(SysError::FailedLookup {
                    source: is_source,
                    lf: LookupFault::DepthMismatch { bits_found: 0, bits_left: r.bits_left },
                }))
            } else {
                Ok(r.slot)
            }
        }
    }
}

pub fn lookup_source_slot<S: Store>(s: &S, root: Cap, cptr: u64, depth: u64) -> KResult<Slot> {
    lookup_slot_for_cnode_op(s, true, root, cptr, depth)
}

pub fn lookup_target_slot<S: Store>(s: &S, root: Cap, cptr: u64, depth: u64) -> KResult<Slot> {
    lookup_slot_for_cnode_op(s, false, root, cptr, depth)
}

pub fn lookup_pivot_slot<S: Store>(s: &S, root: Cap, cptr: u64, depth: u64) -> KResult<Slot> {
    lookup_slot_for_cnode_op(s, true, root, cptr, depth)
}
