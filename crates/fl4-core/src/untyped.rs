//! Untyped_Retype (seL4 object/untyped.c). Free indices are byte offsets.

use crate::capability::Cap;
use crate::cdt;
use crate::cspace;
use crate::error::{illegal, invalid_arg, invalid_cap, range, truncated, Exc, KResult, LookupFault, SysError};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::obj::Slot;
use crate::objects;
use crate::sched;
use fl4_abi::consts::{bits, object as ot};
use fl4_abi::label;

pub const RETYPE_FAN_OUT_LIMIT: u64 = 256;
/// KernelResetChunkBits, fixed at 16 (l4h 0030).
pub const RESET_CHUNK_BITS: u64 = 16;

fn align_up(v: u64, align: u64) -> u64 {
    let m = (1u64 << (align & 63)).wrapping_sub(1);
    v.wrapping_add(m) & !m
}

/// seL4 `decodeUntypedInvocation`.
pub fn decode<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, slot: Slot, cap: Cap, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    if lbl != label::UntypedRetype {
        if lbl == label::UntypedRetypeShared && crate::machine::sharing_enabled(s) {
            return retype_shared(s, a, length, slot, cap, buf, extra);
        }
        return illegal();
    }
    if length < 6 || extra[0].is_null() {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let new_type = msg::syscall_arg(s, ct, buf, 0);
    let user_size = msg::syscall_arg(s, ct, buf, 1);
    let node_index = msg::syscall_arg(s, ct, buf, 2);
    let node_depth = msg::syscall_arg(s, ct, buf, 3);
    let node_offset = msg::syscall_arg(s, ct, buf, 4);
    let node_window = msg::syscall_arg(s, ct, buf, 5);
    if new_type >= ot::X86Vcpu && new_type < ot::Count && a.virtualization() == 0 { return invalid_arg(0); }
    let obj_size = retype_size(new_type, user_size)?;
    let dest = retype_dest(s, extra[0], node_index, node_depth, node_offset, node_window)?;
    ensure_empty_slots(s, dest, node_offset, node_offset.wrapping_add(node_window))?;
    let u = match as_untyped(cap) {
        Some(u) => u,
        None => return illegal(),
    };
    let ptr = u.ptr;
    let block = u.size_bits;
    let free_index = u.free_index;
    let device = u.is_device;
    let (free_index, reset) = match cdt::ensure_no_children(s, slot) {
        Err(_) => (free_index, false),
        Ok(()) => (0, true),
    };
    let free_ref = ptr.wrapping_add(free_index);
    let free_bytes = (1u64 << (block & 63)).wrapping_sub(free_index);
    if (free_bytes >> (obj_size & 63)) < node_window || obj_size >= 64 {
        return Err(Exc::Sys(SysError::NotEnoughMemory { bytes: free_bytes }));
    }
    if device && !objects::is_frame_type(new_type) && new_type != ot::Untyped {
        return invalid_arg(1);
    }
    let aligned = align_up(free_ref, obj_size);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    retype(s, a, slot, reset, aligned, new_type, user_size, dest, node_offset, node_window, device)
}

/// Frame object type and maximum batch count. Limit each serial cache
/// transition to 2 MiB as well as the ordinary capability fan-out limit.
fn shared_frame_spec(bits: u64) -> KResult<(u64, u64)> {
    match bits {
        12 => Ok((ot::X86Page4K, RETYPE_FAN_OUT_LIMIT)),
        21 => Ok((ot::X86LargePage, 1)),
        _ => invalid_arg(0),
    }
}

/// Aligned base, byte length and resulting free index for a checked batch.
fn shared_extent(u: UntypedCap, used: u64, bits: u64, count: u64) -> KResult<(u64, u64, u64)> {
    let base = align_up(u.ptr.wrapping_add(used), bits);
    let block = 1u64 << (u.size_bits & 63);
    let bytes = count << (bits & 63);
    let start = base.wrapping_sub(u.ptr);
    if start > block || bytes > block.wrapping_sub(start) {
        return Err(Exc::Sys(SysError::NotEnoughMemory { bytes: block.saturating_sub(used) }));
    }
    Ok((base, bytes, start.wrapping_add(bytes)))
}

/// Allocate zeroed device frames from ordinary RAM. Use the same watermark,
/// derivation tree and destination-slot checks as Retype. Validate the entire
/// batch before resetting the untyped or changing any page's representation.
fn retype_shared<S: Store, A: Arch>(s: &mut S, a: &mut A, length: u64, slot: Slot, cap: Cap, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    if length < 5 || extra[0].is_null() { return truncated(); }
    let u = match as_untyped(cap) {
        Some(u) if !u.is_device => u,
        _ => return invalid_cap(0),
    };
    let ct = sched::cur_thread(s);
    let bits = msg::syscall_arg(s, ct, buf, 0);
    let (kind, limit) = shared_frame_spec(bits)?;
    let index = msg::syscall_arg(s, ct, buf, 1);
    let depth = msg::syscall_arg(s, ct, buf, 2);
    let offset = msg::syscall_arg(s, ct, buf, 3);
    let count = msg::syscall_arg(s, ct, buf, 4);
    if count == 0 || count > limit { return range(1, limit); }
    let dest = retype_dest(s, extra[0], index, depth, offset, count)?;
    ensure_empty_slots(s, dest, offset, offset.wrapping_add(count))?;

    let reset = cdt::ensure_no_children(s, slot).is_ok();
    let used = if reset { 0 } else { u.free_index };
    let (base, bytes, free_index) = shared_extent(u, used, bits, count)?;
    if !a.dma_ram(base, bytes) { return invalid_cap(0); }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    if reset { reset_untyped(s, a, slot)?; }
    a.dma_frame(base, bytes, true);
    slot.set_cap(s, Cap::Untyped { ptr: u.ptr, size_bits: u.size_bits, free_index, is_device: false });
    objects::create_new_objects(s, a, kind, slot, dest, offset, count, base, 0, true);
    Ok(())
}

/// The size in bits of each new object, with seL4's checks on the type
/// and size arguments.
fn retype_size(new_type: u64, user_size: u64) -> KResult<u64> {
    if new_type >= ot::Count {
        return invalid_arg(0);
    }
    let obj_size = match objects::object_size(new_type, user_size) {
        Some(z) => z,
        None => return invalid_arg(0),
    };
    if user_size >= 64 || obj_size > bits::MAX_UNTYPED {
        return range(0, bits::MAX_UNTYPED);
    }
    if new_type == ot::CapTable && user_size == 0 {
        return invalid_arg(1);
    }
    if new_type == ot::Untyped && user_size < bits::MIN_UNTYPED {
        return invalid_arg(1);
    }
    if new_type == ot::SchedContext && user_size < bits::MIN_SCHED_CONTEXT {
        return invalid_arg(1);
    }
    Ok(obj_size)
}

/// The CNode the new caps go in, checked to have room for the window.
fn retype_dest<S: Store>(s: &S, root_slot: Slot, node_index: u64, node_depth: u64, node_offset: u64, node_window: u64) -> KResult<u64> {
    let node_cap = if node_depth == 0 {
        root_slot.cap(s)
    } else {
        let root = root_slot.cap(s);
        cspace::lookup_target_slot(s, root, node_index, node_depth)?.cap(s)
    };
    let (dest, radix) = match cnode_of(node_cap) {
        Some(x) => x,
        None => {
            return Err(Exc::Sys(SysError::FailedLookup {
                source: false,
                lf: LookupFault::MissingCapability { bits_left: node_depth },
            }))
        }
    };
    let node_size = 1u64 << (radix & 63);
    if node_offset > node_size.wrapping_sub(1) {
        return range(0, node_size.wrapping_sub(1));
    }
    if node_window < 1 || node_window > RETYPE_FAN_OUT_LIMIT {
        return range(1, RETYPE_FAN_OUT_LIMIT);
    }
    if node_window > node_size.wrapping_sub(node_offset) {
        return range(1, node_size.wrapping_sub(node_offset));
    }
    Ok(dest)
}

fn cnode_of(c: Cap) -> Option<(u64, u64)> {
    match c {
        Cap::CNode { ptr, radix, .. } => Some((ptr, radix)),
        _ => None,
    }
}

/// An untyped cap's fields.
#[derive(Clone, Copy)]
struct UntypedCap {
    ptr: u64,
    size_bits: u64,
    free_index: u64,
    is_device: bool,
}

fn as_untyped(c: Cap) -> Option<UntypedCap> {
    match c {
        Cap::Untyped { ptr, size_bits, free_index, is_device } => Some(UntypedCap { ptr, size_bits, free_index, is_device }),
        _ => None,
    }
}

/// Every slot of `cnode` in [from, to) is empty. (The loop has no early
/// exit, which Aeneas cannot translate yet.)
fn ensure_empty_slots<S: Store>(s: &S, cnode: u64, from: u64, to: u64) -> KResult<()> {
    let mut r = Ok(());
    let mut i = from;
    while i < to && r.is_ok() {
        r = cdt::ensure_empty_slot(s, Slot::index(cnode, i));
        i += 1;
    }
    r
}

/// seL4 `resetUntypedCap`: clear the used part, top down, in chunks.
/// Bytes cleared between preemption points, `1 << RESET_CHUNK_BITS`. A
/// literal, so the extracted loop uses the value itself rather than taking
/// it as an argument (which could be 0).
const RESET_CHUNK: u64 = 65536;
const _: () = assert!(RESET_CHUNK == 1 << RESET_CHUNK_BITS);

fn reset_untyped<S: Store, A: Arch>(s: &mut S, a: &mut A, slot: Slot) -> KResult<()> {
    let u = match as_untyped(slot.cap(s)) {
        Some(u) => u,
        None => return Ok(()),
    };
    let ptr = u.ptr;
    let block = u.size_bits;
    let free_index = u.free_index;
    let device = u.is_device;
    if free_index == 0 {
        return Ok(());
    }
    if device || block < RESET_CHUNK_BITS {
        if !device {
            s.clear_free(ptr, 1u64 << (block & 63));
        }
        slot.set_cap(s, Cap::Untyped { ptr, size_bits: block, free_index: 0, is_device: device });
        return Ok(());
    }
    let mut offset = (free_index - 1) & !(RESET_CHUNK - 1);
    loop {
        s.clear_free(ptr.wrapping_add(offset), RESET_CHUNK);
        slot.set_cap(s, Cap::Untyped { ptr, size_bits: block, free_index: offset, is_device: device });
        if offset == 0 {
            return Ok(());
        }
        // The cap just written reads back. (It did not in a doomed
        // transaction, which read 0, before the transactional runtime
        // went: its preemption point never counted up, so this gave up
        // the rest and the entry reran. Removing the check changes the
        // extracted code, so it waits for the proofs.)
        if as_untyped(slot.cap(s)).is_none() {
            return Err(Exc::Preempted);
        }
        sched::preemption_point(s, a)?;
        // `offset` is a nonzero multiple of the chunk here.
        offset = offset.saturating_sub(RESET_CHUNK);
    }
}

#[allow(clippy::too_many_arguments)]
fn retype<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    slot: Slot,
    reset: bool,
    base: u64,
    new_type: u64,
    user_size: u64,
    dest: u64,
    offset: u64,
    length: u64,
    device: bool,
) -> KResult<()> {
    if reset {
        reset_untyped(s, a, slot)?;
    }
    let size = objects::object_size(new_type, user_size).unwrap_or(0);
    let total = length << (size & 63);
    if let Cap::Untyped { ptr, size_bits, is_device, .. } = slot.cap(s) {
        let free_ref = base.wrapping_add(total);
        slot.set_cap(s, Cap::Untyped { ptr, size_bits, free_index: free_ref.wrapping_sub(ptr), is_device });
    }
    objects::create_new_objects(s, a, new_type, slot, dest, offset, length, base, user_size, device);
    Ok(())
}

#[cfg(all(test, not(feature = "aarch64")))]
mod tests {
    //! `reset_untyped` on a store whose reads return 0 and whose writes
    //! are dropped, as a doomed transaction's were before the
    //! transactional runtime went: the preemption point never counts up
    //! and cannot end the loop, and the read-back check must.
    extern crate std;
    use super::*;
    use std::collections::BTreeMap;

    /// A store that behaves as a transaction did: a `clear_free` larger
    /// than `limit` dooms it (fl4-store's former `MAX_TX_CLEAR`), after
    /// which every read is 0 and every write is lost.
    struct TxMem {
        words: BTreeMap<u64, u64>,
        limit: u64,
        doomed: bool,
        clears: u64,
    }
    impl Store for TxMem {
        fn read(&self, a: u64) -> u64 {
            if self.doomed { 0 } else { *self.words.get(&a).unwrap_or(&0) }
        }
        fn write(&mut self, a: u64, v: u64) {
            if !self.doomed {
                self.words.insert(a, v);
            }
        }
        fn zero(&mut self, a: u64, len: u64) {
            for i in (0..len).step_by(8) {
                self.write(a + i, 0);
            }
        }
        fn clear_free(&mut self, a: u64, len: u64) {
            self.clears += 1;
            if self.doomed {
                return;
            }
            if len > self.limit {
                self.doomed = true;
                return;
            }
            self.zero(a, len);
        }
        fn ks_base(&self) -> u64 {
            0x10_0000
        }
        fn cur_cpu(&self) -> u64 {
            0
        }
    }

    struct NoIrq;
    impl Arch for NoIrq {
        fn now(&mut self) -> u64 { 0 }
        fn set_deadline(&mut self, _: u64) {}
        fn us_to_ticks(&self, x: u64) -> u64 { x }
        fn ticks_to_us(&self, x: u64) -> u64 { x }
        fn max_us(&self) -> u64 { u64::MAX }
        fn kernel_wcet_ticks(&self) -> u64 { 1 }
        fn irq_pending(&mut self) -> bool { false }
        fn take_pending_irq(&mut self) -> u64 { u64::MAX }
        fn mask_irq(&mut self, _: u64, _: bool) {}
        fn ack_irq(&mut self, _: u64) {}
        fn set_vspace(&mut self, _: u64, _: u64) {}
        fn invalidate_page(&mut self, _: u64, _: u64) {}
        fn invalidate_asid(&mut self, _: u64) {}
        fn invalidate_page_structures(&mut self, _: u64) {}
        fn ioapic_map(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool { false }
        fn ioapic_map_remapped(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool { false }
        fn num_ioapics(&self) -> u64 { 0 }
        fn ioapic_pins(&self, _: u64) -> u64 { 0 }
        fn port_in(&mut self, _: u64, _: u64) -> u64 { 0 }
        fn port_out(&mut self, _: u64, _: u64, _: u64) {}
        fn fpu_flush(&mut self, _: u64) {}
        fn fpu_sanitise(&mut self, _: u64) {}
        fn fpu_reload(&mut self, _: u64) {}
        fn fpu_release(&mut self, _: u64) {}
        fn remote_stall(&mut self, _: u64) {}
        fn send_reschedule(&mut self, _: u64) {}
        fn putc(&mut self, _: u64) {}
        fn get_char(&mut self) -> u64 { 0 }
        fn halt(&mut self) {}
    }

    const SLOT: Slot = Slot(0x20_0000);
    const UT: u64 = 0x1_0000_0000;

    fn untyped(free_index: u64, limit: u64) -> TxMem {
        let mut s = TxMem { words: BTreeMap::new(), limit, doomed: false, clears: 0 };
        SLOT.set_cap(&mut s, Cap::Untyped { ptr: UT, size_bits: 36, free_index, is_device: false });
        s
    }

    /// Audit r11 F2: the first 64 KiB chunk dooms the store; the reset
    /// must give up at once rather than walk the remaining chunks (a
    /// 64 GiB untyped: about a million rounds with interrupts off).
    #[test]
    fn doomed_reset_stops_after_the_first_chunk() {
        let mut s = untyped(64 << 20, 8192);
        let r = reset_untyped(&mut s, &mut NoIrq, SLOT);
        assert!(s.doomed);
        assert_eq!(s.clears, 1, "doomed reset kept clearing chunks");
        assert!(r.is_err());
    }

    /// On a plain store the reset clears every chunk, top down, and the
    /// cap ends with a free index of 0.
    #[test]
    fn serial_reset_clears_every_chunk() {
        let chunks = 64;
        let mut s = untyped(chunks * RESET_CHUNK, u64::MAX);
        s.words.insert(UT + 8, 0xdead);
        assert!(reset_untyped(&mut s, &mut NoIrq, SLOT).is_ok());
        assert_eq!(s.clears, chunks);
        assert_eq!(s.read(UT + 8), 0);
        assert!(SLOT.cap(&s) == Cap::Untyped { ptr: UT, size_bits: 36, free_index: 0, is_device: false });
    }
}
