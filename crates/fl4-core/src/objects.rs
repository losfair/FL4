//! Object rules shared by all capability types (seL4 object/objecttype.c
//! and the x86/x86_64 Arch_ and Mode_ variants).

use crate::capability::{Cap, FrameSize, Rights, VM_READ_WRITE, ZOMBIE_TCB};
use crate::cdt;
use crate::error::{Exc, KResult, SysError};
use crate::interrupt;
use crate::layout::{self, tcb as tl};
use crate::machine::{Arch, Store};
use crate::notification;
use crate::obj::{Reply, Sc, Slot, Tcb};
use crate::sched;
use crate::schedcontext;
use crate::vspace;
use fl4_abi::consts::{bits, object as ot};

/// seL4 `getObjectSize`, or None for an invalid type.
pub fn object_size(t: u64, user_size: u64) -> Option<u64> {
    if t == ot::X86Vcpu {
        Some(bits::VCPU)
    } else if t >= ot::X86EptPml4 && t <= ot::X86EptPt {
        Some(12)
    } else if t == ot::Tcb {
        Some(bits::TCB)
    } else if t == ot::Endpoint {
        Some(bits::ENDPOINT)
    } else if t == ot::Notification {
        Some(bits::NOTIFICATION)
    } else if t == ot::CapTable {
        Some(bits::SLOT.wrapping_add(user_size))
    } else if t == ot::Untyped || t == ot::SchedContext {
        Some(user_size)
    } else if t == ot::Reply {
        Some(bits::REPLY)
    } else if t == ot::X86Page4K {
        Some(12)
    } else if t == ot::X86LargePage {
        Some(21)
    } else if t == ot::X64HugePage {
        Some(30)
    } else if t == ot::X86PageTable || t == ot::X86PageDirectory || t == ot::X86Pdpt || t == ot::X64Pml4 {
        Some(12)
    } else {
        None
    }
}

pub fn is_frame_type(t: u64) -> bool {
    t == ot::X86Page4K || t == ot::X86LargePage || t == ot::X64HugePage
}

/// seL4 `cap_get_capSizeBits`.
pub fn cap_size_bits(c: Cap) -> u64 {
    match c {
        Cap::Untyped { size_bits, .. } => size_bits,
        Cap::Endpoint { .. } => bits::ENDPOINT,
        Cap::Notification { .. } => bits::NOTIFICATION,
        Cap::CNode { radix, .. } => radix.wrapping_add(bits::SLOT),
        Cap::Thread { .. } => bits::TCB,
        Cap::Zombie { ztype, .. } => {
            if ztype == ZOMBIE_TCB {
                bits::TCB
            } else {
                ztype.wrapping_add(bits::SLOT)
            }
        }
        Cap::Reply { .. } => bits::REPLY,
        Cap::SchedContext { size_bits, .. } => size_bits,
        Cap::Frame { size, .. } => size.bits(),
        Cap::PageTable { .. } | Cap::PageDirectory { .. } | Cap::Pdpt { .. } | Cap::Pml4 { .. } => 12,
        Cap::Vcpu { .. } => bits::VCPU,
        Cap::Ept { .. } => 12,
        Cap::AsidPool { .. } => bits::ASID_POOL,
        _ => 0,
    }
}

/// seL4 `cap_get_capIsPhysical`.
pub fn cap_is_physical(c: Cap) -> bool {
    match c {
        Cap::Untyped { .. }
        | Cap::Endpoint { .. }
        | Cap::Notification { .. }
        | Cap::CNode { .. }
        | Cap::Thread { .. }
        | Cap::SchedContext { .. }
        | Cap::Zombie { .. }
        | Cap::Reply { .. }
        | Cap::Frame { .. }
        | Cap::PageTable { .. }
        | Cap::PageDirectory { .. }
        | Cap::Pdpt { .. }
        | Cap::Pml4 { .. }
        | Cap::Vcpu { .. }
        | Cap::Ept { .. }
        | Cap::AsidPool { .. } => true,
        _ => false,
    }
}

fn mask(b: u64) -> u64 {
    if b >= 64 {
        u64::MAX
    } else {
        (1u64 << (b & 63)).wrapping_sub(1)
    }
}

/// seL4 `sameRegionAs`.
pub fn same_region_as(a: Cap, b: Cap) -> bool {
    match a {
        Cap::Untyped { ptr, size_bits, .. } => {
            if cap_is_physical(b) {
                let a_base = ptr;
                let b_base = b.ptr();
                let a_top = a_base.wrapping_add(mask(size_bits));
                let b_top = b_base.wrapping_add(mask(cap_size_bits(b)));
                a_base <= b_base && b_top <= a_top && b_base <= b_top
            } else {
                false
            }
        }
        Cap::Endpoint { ptr, .. } => matches!(b, Cap::Endpoint { ptr: p, .. } if p == ptr),
        Cap::Notification { ptr, .. } => matches!(b, Cap::Notification { ptr: p, .. } if p == ptr),
        Cap::CNode { ptr, radix, .. } => matches!(b, Cap::CNode { ptr: p, radix: r, .. } if p == ptr && r == radix),
        Cap::Thread { ptr } => matches!(b, Cap::Thread { ptr: p } if p == ptr),
        Cap::Reply { ptr, .. } => matches!(b, Cap::Reply { ptr: p, .. } if p == ptr),
        Cap::Domain => matches!(b, Cap::Domain),
        Cap::IrqControl => matches!(b, Cap::IrqControl | Cap::IrqHandler { .. }),
        Cap::IrqHandler { irq } => matches!(b, Cap::IrqHandler { irq: i } if i == irq),
        Cap::SchedContext { ptr, size_bits } => {
            matches!(b, Cap::SchedContext { ptr: p, size_bits: z } if p == ptr && z == size_bits)
        }
        Cap::SchedControl { .. } => matches!(b, Cap::SchedControl { .. }),
        Cap::Frame { ptr, size, .. } => match b {
            Cap::Frame { ptr: pb, size: sb, .. } => {
                let bot_a = ptr;
                let bot_b = pb;
                let top_a = bot_a.wrapping_add(mask(size.bits()));
                let top_b = bot_b.wrapping_add(mask(sb.bits()));
                bot_a <= bot_b && top_a >= top_b && bot_b <= top_b
            }
            _ => false,
        },
        Cap::PageTable { ptr, .. } => matches!(b, Cap::PageTable { ptr: p, .. } if p == ptr),
        Cap::PageDirectory { ptr, .. } => matches!(b, Cap::PageDirectory { ptr: p, .. } if p == ptr),
        Cap::Pdpt { ptr, .. } => matches!(b, Cap::Pdpt { ptr: p, .. } if p == ptr),
        Cap::Pml4 { ptr, .. } => matches!(b, Cap::Pml4 { ptr: p, .. } if p == ptr),
        Cap::Vcpu { ptr } => matches!(b, Cap::Vcpu { ptr: p } if p == ptr),
        Cap::Ept { ptr, level, .. } => matches!(b, Cap::Ept { ptr: p, level: l, .. } if p == ptr && l == level),
        Cap::AsidControl => matches!(b, Cap::AsidControl),
        Cap::AsidPool { ptr, .. } => matches!(b, Cap::AsidPool { ptr: p, .. } if p == ptr),
        Cap::IoPortControl => matches!(b, Cap::IoPortControl | Cap::IoPort { .. }),
        Cap::IoPort { first, last, .. } => matches!(b, Cap::IoPort { first: f, last: l, .. } if f == first && l == last),
        _ => false,
    }
}

/// seL4 `sameObjectAs`.
pub fn same_object_as(a: Cap, b: Cap) -> bool {
    match a {
        Cap::Untyped { .. } | Cap::IrqControl => false,
        Cap::IoPortControl => {
            if matches!(b, Cap::IoPort { .. }) {
                false
            } else {
                same_region_as(a, b)
            }
        }
        Cap::Frame { ptr, size, is_device, .. } => match b {
            Cap::Frame { ptr: pb, size: sb, is_device: db, .. } => ptr == pb && size == sb && is_device == db,
            _ => same_region_as(a, b),
        },
        _ => same_region_as(a, b),
    }
}

/// seL4 `updateCapData`.
pub fn update_cap_data(preserve: bool, data: u64, c: Cap) -> Cap {
    match c {
        Cap::Endpoint { ptr, badge, send, recv, grant, grant_reply } => {
            if !preserve && badge == 0 {
                Cap::Endpoint { ptr, badge: data, send, recv, grant, grant_reply }
            } else {
                Cap::Null
            }
        }
        Cap::Notification { ptr, badge, send, recv } => {
            if !preserve && badge == 0 {
                Cap::Notification { ptr, badge: data, send, recv }
            } else {
                Cap::Null
            }
        }
        Cap::CNode { ptr, radix, .. } => {
            let guard_size = data & 0x3f;
            if guard_size.wrapping_add(radix) > 64 {
                Cap::Null
            } else {
                let guard = (data >> 6) & mask(guard_size);
                Cap::CNode { ptr, radix, guard_size, guard }
            }
        }
        other => other,
    }
}

/// seL4 `isCapRevocable`.
pub fn is_cap_revocable(derived: Cap, src: Cap) -> bool {
    match derived {
        Cap::Endpoint { badge, .. } => match src {
            Cap::Endpoint { badge: b, .. } => badge != b,
            _ => true,
        },
        Cap::Notification { badge, .. } => match src {
            Cap::Notification { badge: b, .. } => badge != b,
            _ => true,
        },
        Cap::IrqHandler { .. } => matches!(src, Cap::IrqControl),
        Cap::Untyped { .. } => true,
        Cap::IoPort { .. } => matches!(src, Cap::IoPortControl),
        _ => false,
    }
}

pub fn mask_rights(r: Rights, c: Cap) -> Cap {
    crate::capability::mask_cap_rights(r, c)
}

/// seL4 `deriveCap`.
pub fn derive_cap<S: Store>(s: &S, slot: Slot, c: Cap) -> KResult<Cap> {
    match c {
        Cap::Zombie { .. } | Cap::IrqControl | Cap::IoPortControl => Ok(Cap::Null),
        Cap::Untyped { .. } => {
            cdt::ensure_no_children(s, slot)?;
            Ok(c)
        }
        Cap::PageTable { mapped, .. }
        | Cap::PageDirectory { mapped, .. }
        | Cap::Pdpt { mapped, .. }
        | Cap::Pml4 { mapped, .. }
        | Cap::Ept { mapped, .. } => {
            if mapped {
                Ok(c)
            } else {
                Err(Exc::Sys(SysError::IllegalOperation))
            }
        }
        Cap::Frame { ptr, size, rights, is_device, .. } => {
            Ok(Cap::Frame { ptr, size, rights, is_device, mapped: false, is_ept: false, asid: 0, vaddr: 0 })
        }
        other => Ok(other),
    }
}

/// Firmware and MMIO frames also carry the device flag. Only a frame in
/// allocatable RAM can have been created by RetypeShared.
fn retire_dma_frame<S: Store, A: Arch>(s: &S, a: &mut A, ptr: u64, size: FrameSize) {
    if crate::machine::sharing_enabled(s) {
        let bytes = 1u64 << (size.bits() & 63);
        if a.dma_ram(ptr, bytes) { a.dma_frame(ptr, bytes, false); }
    }
}

/// seL4 `finaliseCap`: returns (remainder, cleanup info).
pub fn finalise_cap<S: Store, A: Arch>(s: &mut S, a: &mut A, c: Cap, fin: bool, exposed: bool) -> (Cap, Cap) {
    let _ = exposed;
    if let Cap::IrqHandler { irq } = c {
        if fin {
            interrupt::deleting_irq_handler(s, a, irq);
        }
    }
    finalise_cap_object(s, a, c, fin)
}

/// `finalise_cap` without the IRQ handler's deletion of the IRQ slot, so
/// that deleting the slot's cap (always a notification cap) cannot recurse.
pub fn finalise_cap_object<S: Store, A: Arch>(s: &mut S, a: &mut A, c: Cap, fin: bool) -> (Cap, Cap) {
    match c {
        Cap::Vcpu { ptr } => { if fin { crate::vcpu::finalise(s, a, ptr); } (Cap::Null, Cap::Null) }
        Cap::Ept { .. } => { if fin { crate::ept::finalise(s, a, c); } (Cap::Null, Cap::Null) }
        Cap::Frame { ptr, size, is_device, mapped, is_ept, asid, vaddr, .. } => {
            if mapped && asid != 0 {
                if is_ept { crate::ept::unmap(s, a, asid, vaddr, ptr, size.bits(), false); } else { vspace::unmap_page(s, a, size, asid, vaddr, ptr); }
            }
            if fin && is_device { retire_dma_frame(s, a, ptr, size); }
            (Cap::Null, Cap::Null)
        }
        Cap::PageTable { ptr, mapped, asid, vaddr } => {
            if fin && mapped {
                vspace::unmap_page_table(s, a, asid, vaddr, ptr);
            }
            (Cap::Null, Cap::Null)
        }
        Cap::PageDirectory { ptr, mapped, asid, vaddr } => {
            if fin && mapped {
                vspace::unmap_page_directory(s, a, asid, vaddr, ptr);
            }
            (Cap::Null, Cap::Null)
        }
        Cap::Pdpt { ptr, mapped, asid, vaddr } => {
            if fin && mapped {
                vspace::unmap_pdpt(s, a, asid, vaddr, ptr);
            }
            (Cap::Null, Cap::Null)
        }
        Cap::Pml4 { ptr, mapped, asid } => {
            if fin && mapped {
                vspace::delete_asid(s, a, asid, ptr);
            }
            (Cap::Null, Cap::Null)
        }
        Cap::AsidPool { ptr, asid_base } => {
            if fin {
                vspace::delete_asid_pool(s, a, asid_base, ptr);
            }
            (Cap::Null, Cap::Null)
        }
        Cap::IoPort { first, last, vcpu: owner } => {
            crate::vcpu::revoke_ports(s, a, owner, first, last);
            if fin {
                (Cap::Null, c)
            } else {
                (Cap::Null, Cap::Null)
            }
        }
        Cap::AsidControl | Cap::IoPortControl => (Cap::Null, Cap::Null),
        Cap::Endpoint { ptr, .. } => {
            if fin {
                crate::endpoint::cancel_all_ipc(s, ptr);
            }
            (Cap::Null, Cap::Null)
        }
        Cap::Notification { ptr, .. } => {
            if fin {
                schedcontext::maybe_unbind_ntfn(s, crate::obj::Ntfn(ptr));
                notification::unbind_maybe_notification(s, ptr);
                notification::cancel_all_signals(s, ptr);
            }
            (Cap::Null, Cap::Null)
        }
        Cap::Reply { ptr, .. } => {
            if fin {
                let r = Reply(ptr);
                let t = Tcb(r.tcb(s));
                if !t.is_null() {
                    let st = t.state(s);
                    if st == sched::TS_BLOCKED_ON_REPLY {
                        crate::ipc::reply_remove(s, a, r, t);
                    } else if st == sched::TS_BLOCKED_ON_RECV {
                        crate::ipc::cancel_ipc(s, a, t);
                    }
                }
            }
            (Cap::Null, Cap::Null)
        }
        Cap::Null | Cap::Domain => (Cap::Null, Cap::Null),
        Cap::CNode { ptr, radix, .. } => {
            if fin {
                (Cap::Zombie { ptr, ztype: radix, number: 1u64 << (radix & 63) }, Cap::Null)
            } else {
                (Cap::Null, Cap::Null)
            }
        }
        Cap::Thread { ptr } => {
            if fin {
                let t = Tcb(ptr);
                crate::smp::remote_tcb_stall(s, a, t);
                crate::vcpu::detach(s, a, t);
                notification::unbind_notification(s, t);
                crate::timer::remove(s, t);
                let sc = Sc(t.sc(s));
                if !sc.is_null() {
                    schedcontext::unbind_tcb(s, sc);
                    let yf = Tcb(sc.yield_from(s));
                    if !yf.is_null() {
                        schedcontext::complete_yield_to(s, a, yf);
                    }
                }
                sched::suspend(s, a, t);
                debug_remove(s, t);
                a.fpu_release(t.0);
                (Cap::Zombie { ptr: t.slot(tl::SLOT_CTABLE).0, ztype: ZOMBIE_TCB, number: tl::NUM_SLOTS }, Cap::Null)
            } else {
                (Cap::Null, Cap::Null)
            }
        }
        Cap::SchedContext { ptr, .. } => {
            if fin {
                let sc = Sc(ptr);
                schedcontext::unbind_all_tcbs(s, a, sc);
                schedcontext::unbind_ntfn(s, sc);
                schedcontext::unbind_reply(s, sc);
                let yf = Tcb(sc.yield_from(s));
                if !yf.is_null() {
                    schedcontext::complete_yield_to(s, a, yf);
                }
                sc.set_refill_max(s, 0);
                sc.set_sporadic(s, 0);
            }
            (Cap::Null, Cap::Null)
        }
        Cap::Zombie { .. } => (c, Cap::Null),
        Cap::IrqHandler { .. } => {
            if fin {
                (Cap::Null, c)
            } else {
                (Cap::Null, Cap::Null)
            }
        }
        Cap::IrqControl | Cap::SchedControl { .. } | Cap::Untyped { .. } => (Cap::Null, Cap::Null),
    }
}

/// seL4 `postCapDeletion`.
pub fn post_cap_deletion<S: Store, A: Arch>(s: &mut S, a: &mut A, cleanup: Cap) {
    match cleanup {
        Cap::IrqHandler { irq } => interrupt::deleted_irq_handler(s, a, irq),
        Cap::IoPort { first, last, .. } => crate::ioport::free_ioports(s, first, last),
        _ => {}
    }
}

// ---- debug list of TCBs ----------------------------------------------------

pub fn debug_append<S: Store>(s: &mut S, t: Tcb) {
    let cpu = t.affinity(s);
    let head = crate::obj::node_get(s, cpu, layout::node::DEBUG_TCBS);
    t.set_debug_prev(s, 0);
    t.set_debug_next(s, head);
    if head != 0 {
        Tcb(head).set_debug_prev(s, t.0);
    }
    crate::obj::node_set(s, cpu, layout::node::DEBUG_TCBS, t.0);
}

pub fn debug_remove<S: Store>(s: &mut S, t: Tcb) {
    let cpu = t.affinity(s);
    let head = crate::obj::node_get(s, cpu, layout::node::DEBUG_TCBS);
    let next = t.debug_next(s);
    let prev = t.debug_prev(s);
    if head == t.0 {
        crate::obj::node_set(s, cpu, layout::node::DEBUG_TCBS, next);
    } else if prev != 0 {
        Tcb(prev).set_debug_next(s, next);
    }
    if next != 0 {
        Tcb(next).set_debug_prev(s, prev);
    }
    t.set_debug_prev(s, 0);
    t.set_debug_next(s, 0);
}

/// Initial FPU image of a new thread: x87 control word 0x37f and MXCSR
/// 0x1f80, everything else in its initial state (XSTATE_BV = 0).
fn init_fpu<S: Store>(s: &mut S, t: Tcb) {
    let f = t.fpu_addr();
    s.write(f, 0x037f);
    s.write(f.wrapping_add(24), 0x0000_ffff_0000_1f80);
}

/// seL4 `createObject`. The memory is already zero.
pub fn create_object<S: Store, A: Arch>(s: &mut S, a: &mut A, t: u64, base: u64, user_size: u64, device: bool) -> Cap {
    let _ = a;
    if t == ot::X86Vcpu {
        crate::vcpu::init(s, a, base);
        Cap::Vcpu { ptr: base }
    } else if t >= ot::X86EptPml4 && t <= ot::X86EptPt {
        let level = if t == ot::X86EptPml4 { 0 } else if t == ot::X86EptPdpt { 39 } else if t == ot::X86EptPd { 30 } else { 21 };
        Cap::Ept { ptr: base, level, mapped: false, asid: 0, vaddr: 0 }
    } else if t == ot::Tcb {
        let tcb = Tcb(base);
        crate::regs::init_context(s, tcb);
        init_fpu(s, tcb);
        crate::debug::init_context(s, tcb);
        let d = sched::cur_domain(s);
        tcb.set_domain(s, d);
        let ct = sched::cur_thread(s);
        set_child_name(s, tcb, ct);
        debug_append(s, tcb);
        Cap::Thread { ptr: base }
    } else if t == ot::Endpoint {
        Cap::Endpoint { ptr: base, badge: 0, send: true, recv: true, grant: true, grant_reply: true }
    } else if t == ot::Notification {
        Cap::Notification { ptr: base, badge: 0, send: true, recv: true }
    } else if t == ot::CapTable {
        Cap::CNode { ptr: base, radix: user_size, guard_size: 0, guard: 0 }
    } else if t == ot::Untyped {
        Cap::Untyped { ptr: base, size_bits: user_size, free_index: 0, is_device: device }
    } else if t == ot::SchedContext {
        Cap::SchedContext { ptr: base, size_bits: user_size }
    } else if t == ot::Reply {
        Cap::Reply { ptr: base, grant: true }
    } else if t == ot::X86Page4K || t == ot::X86LargePage || t == ot::X64HugePage {
        let size = if t == ot::X86Page4K {
            FrameSize::Small
        } else if t == ot::X86LargePage {
            FrameSize::Large
        } else {
            FrameSize::Huge
        };
        Cap::Frame { ptr: base, size, rights: VM_READ_WRITE, is_device: device, mapped: false, is_ept: false, asid: 0, vaddr: 0 }
    } else if t == ot::X86PageTable {
        Cap::PageTable { ptr: base, mapped: false, asid: 0, vaddr: 0 }
    } else if t == ot::X86PageDirectory {
        Cap::PageDirectory { ptr: base, mapped: false, asid: 0, vaddr: 0 }
    } else if t == ot::X86Pdpt {
        Cap::Pdpt { ptr: base, mapped: false, asid: 0, vaddr: 0 }
    } else {
        // X64Pml4
        vspace::copy_global_mappings(s, base);
        Cap::Pml4 { ptr: base, mapped: false, asid: 0 }
    }
}

/// "child of" and ": '", little-endian.
const CHILD_PREFIX0: u64 = 0x666f_2064_6c69_6863;
const CHILD_PREFIX1: u64 = 0x0027_203a;
const CHILD_PREFIX_LEN: u64 = 11;
/// Room for the parent's name: the prefix, the closing quote and the NUL
/// take the rest of the 64 bytes.
const CHILD_NAME_MAX: u64 = 51;

fn name_byte<S: Store>(s: &S, t: Tcb, i: u64) -> u64 {
    (s.read(t.name_addr().wrapping_add(i & !7)) >> ((i & 7).wrapping_mul(8) & 63)) & 0xff
}

/// Byte `i` of "child of: '<first len bytes of parent's name>'".
fn child_name_byte<S: Store>(s: &S, parent: Tcb, len: u64, i: u64) -> u64 {
    if i < 8 {
        (CHILD_PREFIX0 >> (i * 8)) & 0xff
    } else if i < CHILD_PREFIX_LEN {
        (CHILD_PREFIX1 >> ((i - 8) * 8)) & 0xff
    } else if i - CHILD_PREFIX_LEN < len {
        name_byte(s, parent, i - CHILD_PREFIX_LEN)
    } else if i - CHILD_PREFIX_LEN == len {
        0x27
    } else {
        0
    }
}

/// "child of: '<parent name>'", as seL4 names new TCBs in debug builds.
/// Built a byte at a time (no local arrays, so it translates to Lean).
fn set_child_name<S: Store>(s: &mut S, child: Tcb, parent: Tcb) {
    if !fl4_abi::config::DEBUG_BUILD || parent.is_null() {
        return;
    }
    let mut len: u64 = 0;
    while len < CHILD_NAME_MAX && name_byte(s, parent, len) != 0 {
        len += 1;
    }
    let mut w: u64 = 0;
    while w < 8 {
        let mut v: u64 = 0;
        let mut k: u64 = 0;
        while k < 8 {
            v |= child_name_byte(s, parent, len, w.wrapping_mul(8).wrapping_add(k)) << (k.wrapping_mul(8) & 63);
            k += 1;
        }
        s.write(child.name_addr().wrapping_add(w.wrapping_mul(8)), v);
        w += 1;
    }
}

/// seL4 `createNewObjects`.
#[allow(clippy::too_many_arguments)]
pub fn create_new_objects<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    t: u64,
    parent: Slot,
    dest_cnode: u64,
    dest_offset: u64,
    dest_length: u64,
    base: u64,
    user_size: u64,
    device: bool,
) {
    let size = match object_size(t, user_size) {
        Some(z) => z,
        None => return,
    };
    let mut i = 0;
    while i < dest_length {
        let cap = create_object(s, a, t, base.wrapping_add(i << (size & 63)), user_size, device);
        cdt::insert_new_cap(s, parent, Slot::index(dest_cnode, dest_offset.wrapping_add(i)), cap);
        i += 1;
    }
}
