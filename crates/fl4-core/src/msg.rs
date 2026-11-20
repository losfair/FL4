//! Message registers, IPC buffers and syscall arguments.
//!
//! The IPC buffer layout (seL4_IPCBuffer): tag, msg[120], userData,
//! caps_or_badges[3], receiveCNode, receiveIndex, receiveDepth.

use crate::capability::{Cap, VM_READ_ONLY, VM_READ_WRITE};
use crate::layout::{reg, tcb as tl};
use crate::machine::Store;
use crate::msginfo::MessageInfo;
use crate::obj::Tcb;

arch_items!("msg.rs");

pub const N_MSG_REGISTERS: u64 = 4;
pub const MSG_MAX_LENGTH: u64 = 120;
pub const MSG_MAX_EXTRA_CAPS: u64 = 3;

/// Word offsets in the IPC buffer.
pub const BUF_MSG: u64 = 1;
pub const BUF_USER_DATA: u64 = 1 + MSG_MAX_LENGTH;
pub const BUF_CAPS: u64 = BUF_USER_DATA + 1;
pub const BUF_RECV_CNODE: u64 = BUF_CAPS + MSG_MAX_EXTRA_CAPS;
pub const BUF_RECV_INDEX: u64 = BUF_RECV_CNODE + 1;
pub const BUF_RECV_DEPTH: u64 = BUF_RECV_INDEX + 1;

/// A thread's IPC buffer as a kernel address, or 0 (seL4 `lookupIPCBuffer`).
#[inline(always)]
pub fn lookup_ipc_buffer<S: Store>(s: &S, is_receiver: bool, t: Tcb) -> u64 {
    let w = t.ipc_buffer(s);
    match t.slot(tl::SLOT_BUFFER).cap(s) {
        Cap::Frame { ptr, size, rights, is_device, .. } => {
            if is_device {
                return 0;
            }
            if rights == VM_READ_WRITE || (!is_receiver && rights == VM_READ_ONLY) {
                let bits = size.bits();
                ptr.wrapping_add(w & (1u64 << (bits & 63)).wrapping_sub(1))
            } else {
                0
            }
        }
        _ => 0,
    }
}

pub fn buf_get<S: Store>(s: &S, buf: u64, i: u64) -> u64 {
    s.read(buf.wrapping_add(i.wrapping_mul(8)))
}

pub fn buf_set<S: Store>(s: &mut S, buf: u64, i: u64, v: u64) {
    s.write(buf.wrapping_add(i.wrapping_mul(8)), v)
}

/// `getSyscallArg`: argument `i` of the current invocation.
pub fn syscall_arg<S: Store>(s: &S, t: Tcb, buf: u64, i: u64) -> u64 {
    if i < N_MSG_REGISTERS {
        t.reg(s, msg_register(i))
    } else if buf != 0 {
        buf_get(s, buf, i.wrapping_add(1))
    } else {
        0
    }
}

/// `getMR`.
pub fn get_mr<S: Store>(s: &S, t: Tcb, buf: u64, i: u64) -> u64 {
    syscall_arg(s, t, buf, i)
}

/// `setMR`: returns the number of registers written so far (i + 1), or
/// `N_MSG_REGISTERS` when the value had nowhere to go, as seL4 does.
pub fn set_mr<S: Store>(s: &mut S, t: Tcb, buf: u64, i: u64, v: u64) -> u64 {
    if i < N_MSG_REGISTERS {
        t.set_reg(s, msg_register(i), v);
        i.wrapping_add(1)
    } else if buf != 0 {
        buf_set(s, buf, i.wrapping_add(1), v);
        i.wrapping_add(1)
    } else {
        N_MSG_REGISTERS
    }
}

/// `copyMRs`.
pub fn copy_mrs<S: Store>(s: &mut S, sender: Tcb, send_buf: u64, receiver: Tcb, recv_buf: u64, n: u64) -> u64 {
    let mut i = 0;
    while i < n && i < N_MSG_REGISTERS {
        let v = sender.reg(s, msg_register(i));
        receiver.set_reg(s, msg_register(i), v);
        i += 1;
    }
    if recv_buf == 0 || send_buf == 0 {
        return i;
    }
    while i < n && i < MSG_MAX_LENGTH {
        let v = buf_get(s, send_buf, i + 1);
        buf_set(s, recv_buf, i + 1, v);
        i += 1;
    }
    i
}

pub fn msg_info<S: Store>(s: &S, t: Tcb) -> MessageInfo {
    MessageInfo::from_word_clamped(t.reg(s, reg::MSG_INFO))
}

pub fn set_msg_info<S: Store>(s: &mut S, t: Tcb, m: MessageInfo) {
    t.set_reg(s, reg::MSG_INFO, m.to_word())
}

/// `replyFromKernel_success_empty`.
pub fn reply_success_empty<S: Store>(s: &mut S, t: Tcb) {
    t.set_reg(s, reg::BADGE, 0);
    set_msg_info(s, t, MessageInfo::new(0, 0, 0, 0));
}
