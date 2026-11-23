//! Faults: storing them in TCBs, delivering them to handlers, encoding the
//! fault messages and applying fault replies (seL4 api/faults.c,
//! kernel/faulthandler.c).

use crate::capability::Cap;
use crate::endpoint;
use crate::error::{Fault, LookupFault};
use crate::layout::{reg, tcb as tl};
use crate::machine::{Arch, Store};
use crate::msg::{self, N_MSG_REGISTERS};
use crate::obj::{Sc, Tcb};
use crate::sched;
use crate::schedcontext;
use fl4_abi::consts::fault as ft;

arch_items!("faults.rs");

pub fn clear_fault<S: Store>(s: &mut S, t: Tcb) {
    t.set_fault_type(s, ft::NullFault);
}

/// Store `f` as the thread's fault (and the lookup failure of a cap fault).
#[inline(always)]
pub fn set_fault<S: Store>(s: &mut S, t: Tcb, f: Fault) {
    let (ty, w0, w1, w2) = match f {
        Fault::Null => (ft::NullFault, 0, 0, 0),
        Fault::Cap { addr, in_recv, lf } => {
            let (lt, l0, l1) = lf.encode();
            t.set_lf_type(s, lt);
            t.set_lf_w0(s, l0);
            t.set_lf_w1(s, l1);
            (ft::CapFault, addr, if in_recv { 1 } else { 0 }, 0)
        }
        Fault::UnknownSyscall { number } => (ft::UnknownSyscall, number, 0, 0),
        Fault::UserException { number, code } => (ft::UserException, number, code, 0),
        Fault::Debug { reason, addr, bp } => (ft::DebugException, reason, addr, bp),
        Fault::Timeout { badge } => (ft::Timeout, badge, 0, 0),
        Fault::VmFault { addr, fsr, instruction } => (ft::VMFault, addr, fsr, if instruction { 1 } else { 0 }),
        #[cfg(feature = "aarch64")]
        Fault::VcpuFault { hsr } => (ft::VCPUFault, hsr, 0, 0),
        #[cfg(feature = "aarch64")]
        Fault::VgicMaintenance { idx, idx_valid } => (ft::VGICMaintenance, idx, if idx_valid { 1 } else { 0 }, 0),
        #[cfg(feature = "aarch64")]
        Fault::VppiEvent { irq } => (ft::VPPIEvent, irq, 0, 0),
    };
    t.set_fault_type(s, ty);
    t.set_fault_w0(s, w0);
    t.set_fault_w1(s, w1);
    t.set_fault_w2(s, w2);
}

fn lookup_failure<S: Store>(s: &S, t: Tcb) -> LookupFault {
    LookupFault::decode(t.lf_type(s), t.lf_w0(s), t.lf_w1(s))
}

/// seL4 `validFaultHandler`.
pub fn valid_fault_handler(cap: Cap) -> bool {
    match cap {
        Cap::Endpoint { send, grant, grant_reply, .. } => send && (grant || grant_reply),
        Cap::Null => true,
        _ => false,
    }
}

/// seL4 `validTimeoutHandler`.
pub fn valid_timeout_handler<S: Store>(s: &S, t: Tcb) -> bool {
    matches!(t.slot(tl::SLOT_TIMEOUT_HANDLER).cap(s), Cap::Endpoint { .. })
}

/// seL4 `sendFaultIPC`.
#[inline(always)]
fn send_fault_ipc<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, handler: Cap, can_donate: bool, f: Fault) -> bool {
    match handler {
        Cap::Endpoint { ptr, badge, grant, grant_reply, .. } => {
            set_fault(s, t, f);
            endpoint::send_ipc(s, a, true, false, badge, grant, grant_reply, can_donate, t, ptr);
            true
        }
        _ => false,
    }
}

/// seL4 `handleFault`.
pub fn handle_fault<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, f: Fault) {
    let handler = t.slot(tl::SLOT_FAULT_HANDLER).cap(s);
    let can_donate = t.sc(s) != 0;
    if !send_fault_ipc(s, a, t, handler, can_donate, f) {
        // handleNoFaultHandler: the thread stops (no fault is stored).
        sched::set_thread_state(s, t, sched::TS_INACTIVE);
    }
}

/// seL4 `handleTimeout`.
pub fn handle_timeout<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, f: Fault) {
    let handler = t.slot(tl::SLOT_TIMEOUT_HANDLER).cap(s);
    let _ = send_fault_ipc(s, a, t, handler, false, f);
}

fn set_mrs_lookup_failure<S: Store>(s: &mut S, receiver: Tcb, buf: u64, lf: LookupFault, offset: u64) -> u64 {
    let i = msg::set_mr(s, receiver, buf, offset, lf.type_code());
    match lf {
        LookupFault::InvalidRoot => i,
        LookupFault::MissingCapability { bits_left } => msg::set_mr(s, receiver, buf, offset.wrapping_add(1), bits_left),
        LookupFault::DepthMismatch { bits_found, bits_left } => {
            msg::set_mr(s, receiver, buf, offset.wrapping_add(1), bits_left);
            msg::set_mr(s, receiver, buf, offset.wrapping_add(2), bits_found)
        }
        LookupFault::GuardMismatch { guard_found, bits_left, guard_size } => {
            msg::set_mr(s, receiver, buf, offset.wrapping_add(1), bits_left);
            msg::set_mr(s, receiver, buf, offset.wrapping_add(2), guard_found);
            msg::set_mr(s, receiver, buf, offset.wrapping_add(3), guard_size)
        }
    }
}

/// seL4 `setMRs_lookup_failure` for syscall errors (offset 1).
pub fn set_mrs_lookup_failure_at<S: Store>(s: &mut S, receiver: Tcb, buf: u64, lf: LookupFault, offset: u64) -> u64 {
    set_mrs_lookup_failure(s, receiver, buf, lf, offset)
}

#[inline(always)]

fn copy_mrs_fault<S: Store>(s: &mut S, sender: Tcb, receiver: Tcb, regs_list: &[u64], buf: u64) {
    let mut i: usize = 0;
    while i < regs_list.len() && (i as u64) < N_MSG_REGISTERS {
        let v = sender.reg(s, regs_list[i]);
        receiver.set_reg(s, msg::msg_register(i as u64), v);
        i += 1;
    }
    if buf != 0 {
        while i < regs_list.len() {
            let v = sender.reg(s, regs_list[i]);
            msg::buf_set(s, buf, (i as u64).wrapping_add(1), v);
            i += 1;
        }
    }
}

/// seL4 `setMRs_fault`: encode the sender's fault into the receiver's
/// message registers. Returns the message length.
#[inline(always)]
pub fn set_mrs_fault<S: Store, A: Arch>(s: &mut S, a: &A, sender: Tcb, receiver: Tcb, buf: u64) -> u64 {
    let ty = sender.fault_type(s);
    let w0 = sender.fault_w0(s);
    let w1 = sender.fault_w1(s);
    let w2 = sender.fault_w2(s);
    let restart_pc = sender.reg(s, reg::FAULT_IP);
    if ty == ft::CapFault {
        msg::set_mr(s, receiver, buf, 0, restart_pc);
        msg::set_mr(s, receiver, buf, 1, w0);
        msg::set_mr(s, receiver, buf, 2, w1);
        let lf = lookup_failure(s, sender);
        set_mrs_lookup_failure(s, receiver, buf, lf, 3)
    } else if ty == ft::UnknownSyscall {
        copy_mrs_fault(s, sender, receiver, &SYSCALL_MESSAGE, buf);
        trap_syscall_message!(s, sender, buf, msg::set_mr(s, receiver, buf, unknown_syscall_number_mr!(), w0))
    } else if ty == ft::UserException {
        copy_mrs_fault(s, sender, receiver, &EXCEPTION_MESSAGE, buf);
        msg::set_mr(s, receiver, buf, 3, w0);
        msg::set_mr(s, receiver, buf, 4, w1)
    } else if ty == ft::Timeout {
        let sc = Sc(sender.sc(s));
        if !sc.is_null() {
            let consumed = schedcontext::update_consumed(s, a, sc);
            let len = msg::set_mr(s, receiver, buf, 0, w0);
            msg::set_mr(s, receiver, buf, len, consumed)
        } else {
            msg::set_mr(s, receiver, buf, 0, w0)
        }
    } else if ty == ft::DebugException {
        msg::set_mr(s, receiver, buf, 0, restart_pc);
        let mut ret = msg::set_mr(s, receiver, buf, 1, w0);
        if w0 != crate::debug::SINGLE_STEP && w0 != crate::debug::SOFTWARE_BREAK_REQUEST {
            msg::set_mr(s, receiver, buf, 2, w1);
            ret = msg::set_mr(s, receiver, buf, 3, w2);
        }
        ret
    } else if ty == ft::VMFault {
        msg::set_mr(s, receiver, buf, 0, restart_pc);
        msg::set_mr(s, receiver, buf, 1, w0);
        msg::set_mr(s, receiver, buf, 2, w2);
        msg::set_mr(s, receiver, buf, 3, w1)
    } else {
        #[cfg(feature = "aarch64")]
        {
            if ty == ft::VCPUFault {
                return msg::set_mr(s, receiver, buf, 0, w0);
            } else if ty == ft::VGICMaintenance {
                return if w1 != 0 { msg::set_mr(s, receiver, buf, 0, w0) } else { 0 };
            } else if ty == ft::VPPIEvent {
                return msg::set_mr(s, receiver, buf, 0, w0);
            }
        }
        0
    }
}

#[inline(always)]
fn copy_mrs_fault_reply<S: Store>(s: &mut S, sender: Tcb, receiver: Tcb, regs_list: &[u64], length: u64) {
    let n = if length < regs_list.len() as u64 { length as usize } else { regs_list.len() };
    let mut i: usize = 0;
    while i < n && i < regs_list.len() && (i as u64) < N_MSG_REGISTERS {
        let r = regs_list[i];
        let v = sender.reg(s, msg::msg_register(i as u64));
        receiver.set_reg(s, r, sanitise_reg!(s, receiver, r, v));
        i += 1;
    }
    if i < n {
        let buf = msg::lookup_ipc_buffer(s, false, sender);
        if buf != 0 {
            while i < n && i < regs_list.len() {
                let r = regs_list[i];
                let v = msg::buf_get(s, buf, (i as u64).wrapping_add(1));
                receiver.set_reg(s, r, sanitise_reg!(s, receiver, r, v));
                i += 1;
            }
        }
    }
}

/// seL4 `handleFaultReply`: apply the handler's reply. Returns whether the
/// faulting thread restarts.
#[inline(always)]
pub fn handle_fault_reply<S: Store, A: Arch>(s: &mut S, a: &mut A, receiver: Tcb, sender: Tcb) -> bool {
    let tag = msg::msg_info(s, sender);
    let lbl = tag.label;
    let len = tag.length;
    let ty = receiver.fault_type(s);
    if ty == ft::CapFault {
        true
    } else if ty == ft::UnknownSyscall {
        copy_mrs_fault_reply(s, sender, receiver, &SYSCALL_MESSAGE, len);
        trap_syscall_reply!(s, sender, receiver, len);
        lbl == 0
    } else if ty == ft::UserException {
        copy_mrs_fault_reply(s, sender, receiver, &EXCEPTION_MESSAGE, len);
        lbl == 0
    } else if ty == ft::Timeout {
        copy_mrs_fault_reply(s, sender, receiver, &TIMEOUT_REPLY_MESSAGE, len);
        lbl == 0
    } else if ty == ft::DebugException {
        if receiver.fault_w0(s) != crate::debug::SINGLE_STEP {
            return lbl == 0;
        }
        let n_instrs = if len < 1 { 1 } else { sender.reg(s, msg::msg_register(0)) };
        crate::debug::configure_single_stepping(s, a, receiver, 0, n_instrs, true);
        lbl == 0
    } else {
        // VM faults always restart the thread.
        true
    }
}
