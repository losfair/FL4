//! I/O port capabilities (seL4 arch/x86/object/ioport.c).

use crate::capability::Cap;
use crate::cdt;
use crate::cspace;
use crate::error::{illegal, invalid_arg, truncated, Exc, KResult, SysError};
use crate::layout::ks;
use crate::machine::{Arch, Store};
use crate::msg;
use crate::obj::{ks_get, ks_set, Slot};
use crate::sched;
use fl4_abi::label;

fn pattern(start: u64, end: u64) -> u64 {
    // start <= 63 and end <= 64 (both come from `& 63`).
    let n = end.wrapping_sub(start);
    if n >= 64 {
        u64::MAX
    } else {
        ((1u64 << (n & 63)).wrapping_sub(1)) << (start & 63)
    }
}

fn word_off(w: u64) -> u64 {
    ks::IOPORT_BITMAP.wrapping_add(w.wrapping_mul(8))
}

fn apply<S: Store>(s: &mut S, w: u64, p: u64, set: bool) {
    let v = ks_get(s, word_off(w));
    ks_set(s, word_off(w), if set { v | p } else { v & !p });
}

/// seL4 `setIOPortMask`.
pub fn set_mask<S: Store>(s: &mut S, low: u64, high: u64, set: bool) {
    let lw = low >> 6;
    let hw = high >> 6;
    let li = low & 63;
    let hi = high & 63;
    if lw == hw {
        apply(s, lw, pattern(li, hi.wrapping_add(1)), set);
    } else {
        apply(s, lw, pattern(li, 64), set);
        let mut w = lw + 1;
        while w < hw {
            apply(s, w, u64::MAX, set);
            w += 1;
        }
        apply(s, hw, pattern(0, hi.wrapping_add(1)), set);
    }
}

fn range_free<S: Store>(s: &S, low: u64, high: u64) -> bool {
    let lw = low >> 6;
    let hw = high >> 6;
    let li = low & 63;
    let hi = high & 63;
    if lw == hw {
        return ks_get(s, word_off(lw)) & pattern(li, hi.wrapping_add(1)) == 0;
    }
    if ks_get(s, word_off(lw)) & pattern(li, 64) != 0 {
        return false;
    }
    let mut w = lw + 1;
    while w < hw {
        if ks_get(s, word_off(w)) != 0 {
            return false;
        }
        w += 1;
    }
    ks_get(s, word_off(hw)) & pattern(0, hi.wrapping_add(1)) == 0
}

pub fn free_ioports<S: Store>(s: &mut S, first: u64, last: u64) {
    set_mask(s, first, last, false);
}

/// seL4 `decodeX86PortControlInvocation`.
pub fn decode_control<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, slot: Slot, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    let _ = a;
    if lbl != label::X86IOPortControlIssue {
        return illegal();
    }
    if length < 4 || extra[0].is_null() {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let first = msg::syscall_arg(s, ct, buf, 0) & 0xffff;
    let last = msg::syscall_arg(s, ct, buf, 1) & 0xffff;
    let index = msg::syscall_arg(s, ct, buf, 2);
    let depth = msg::syscall_arg(s, ct, buf, 3);
    let cnode = extra[0].cap(s);
    if last < first {
        return invalid_arg(1);
    }
    if !range_free(s, first, last) {
        return Err(Exc::Sys(SysError::RevokeFirst));
    }
    let dest = cspace::lookup_target_slot(s, cnode, index, depth)?;
    cdt::ensure_empty_slot(s, dest)?;
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    set_mask(s, first, last, true);
    cdt::insert(s, Cap::IoPort { first, last, vcpu: 0 }, slot, dest);
    Ok(())
}

fn allowed(first: u64, last: u64, port: u64, size: u64) -> KResult<()> {
    let end = port.wrapping_add(size).wrapping_sub(1);
    if port < first || end > last {
        return illegal();
    }
    Ok(())
}

/// seL4 `decodeX86PortInvocation`.
/// The access size of an IO port invocation, or 0 if `lbl` is not one.
fn port_size(lbl: u64) -> u64 {
    if lbl == label::X86IOPortIn8 || lbl == label::X86IOPortOut8 {
        1
    } else if lbl == label::X86IOPortIn16 || lbl == label::X86IOPortOut16 {
        2
    } else if lbl == label::X86IOPortIn32 || lbl == label::X86IOPortOut32 {
        4
    } else {
        0
    }
}

/// Whether `lbl` names an I/O port access.
pub fn is_port_label(lbl: u64) -> bool {
    port_size(lbl) != 0
}

// Literal results rather than `a || b == c`: Aeneas types a boolean whose
// last operand is a comparison as a Lean Prop.
fn is_port_in(lbl: u64) -> bool {
    if lbl == label::X86IOPortIn8 || lbl == label::X86IOPortIn16 || lbl == label::X86IOPortIn32 {
        true
    } else {
        false
    }
}

/// Whether thread `t`'s invocation of `cptr` with `info` is an I/O port
/// access that `decode` would carry out: the cap is an IoPort, there are
/// arguments enough and the port is in its range. Reads only.
pub fn invocation_ok<S: Store>(s: &S, t: crate::obj::Tcb, cptr: u64, info: crate::msginfo::MessageInfo) -> bool {
    let size = port_size(info.label);
    if size == 0 {
        return false;
    }
    let (first, last) = match cspace::lookup_slot(s, t, cptr) {
        Ok(r) => match r.slot.cap(s) {
            Cap::IoPort { first, last, .. } => (first, last),
            _ => return false,
        },
        Err(_) => return false,
    };
    let buf = msg::lookup_ipc_buffer(s, false, t);
    let mut length = info.length;
    if length > msg::N_MSG_REGISTERS && buf == 0 {
        length = msg::N_MSG_REGISTERS;
    }
    if length < if is_port_in(info.label) { 1 } else { 2 } {
        return false;
    }
    let port = msg::syscall_arg(s, t, buf, 0) & 0xffff;
    allowed(first, last, port, size).is_ok()
}

pub fn decode<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, cap: Cap, call: bool, buf: u64) -> KResult<()> {
    let (first, last) = match cap {
        Cap::IoPort { first, last, .. } => (first, last),
        _ => return illegal(),
    };
    let ct = sched::cur_thread(s);
    let size = port_size(lbl);
    if size == 0 {
        return illegal();
    }
    let is_in = is_port_in(lbl);
    if is_in {
        if length < 1 {
            return truncated();
        }
        let port = msg::syscall_arg(s, ct, buf, 0) & 0xffff;
        allowed(first, last, port, size)?;
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        let v = a.port_in(port, size);
        if call {
            let b = msg::lookup_ipc_buffer(s, true, ct);
            ct.set_reg(s, crate::layout::reg::BADGE, 0);
            let n = msg::set_mr(s, ct, b, 0, v);
            msg::set_msg_info(s, ct, crate::msginfo::MessageInfo::new(0, 0, 0, n));
        }
        sched::set_thread_state(s, ct, sched::TS_RUNNING);
    } else {
        if length < 2 {
            return truncated();
        }
        let port = msg::syscall_arg(s, ct, buf, 0) & 0xffff;
        let raw = msg::syscall_arg(s, ct, buf, 1);
        allowed(first, last, port, size)?;
        let data = if size == 1 {
            raw & 0xff
        } else if size == 2 {
            raw & 0xffff
        } else {
            raw & 0xffff_ffff
        };
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        a.port_out(port, size, data);
    }
    Ok(())
}
