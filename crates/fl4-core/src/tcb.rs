//! TCB invocations (seL4 object/tcb.c, MCS), plus the l4h extensions
//! TCB_SetTimer, TCB_ReadFPU, TCB_WriteFPU and the trapSyscalls flag.

use crate::capability::{Cap, VM_KERNEL_ONLY, VM_READ_WRITE};
use crate::cdt;
use crate::debug;
use crate::error::{illegal, invalid_arg, invalid_cap, range, sys, truncated, Exc, KResult, SysError};
use crate::faults;
use crate::layout::{reg, tcb as tl};
use crate::machine::{Arch, Store};
use crate::msg::{self, N_MSG_REGISTERS};
use crate::msginfo::MessageInfo;
use crate::notification;
use crate::obj::{Ntfn, Sc, Slot, Tcb};
use crate::objects;
use crate::regs::{self, FRAME_REGISTERS, GP_REGISTERS};
use crate::sched;
use crate::schedcontext;
use crate::sporadic;
use crate::timer;
use crate::vspace;
use fl4_abi::consts::tcb_flag;
use fl4_abi::label;

const N_FRAME: u64 = 18;
const N_GP: u64 = 2;

/// Arguments common to every TCB invocation.
pub struct Ctx<'a> {
    pub length: u64,
    pub buf: u64,
    pub call: bool,
    pub slot: Slot,
    pub extra: &'a [Slot; 3],
}

fn arg<S: Store>(s: &S, c: &Ctx, i: u64) -> u64 {
    msg::syscall_arg(s, sched::cur_thread(s), c.buf, i)
}

fn extra(c: &Ctx, i: usize) -> Option<Slot> {
    if i >= 3 || c.extra[i].is_null() {
        None
    } else {
        Some(c.extra[i])
    }
}

fn restart_caller<S: Store>(s: &mut S) {
    let ct = sched::cur_thread(s);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
}

fn check_prio<S: Store>(s: &S, prio: u64, auth: Tcb) -> KResult<()> {
    let mcp = auth.mcp(s);
    if prio > mcp {
        return range(0, mcp);
    }
    Ok(())
}

/// Reply to a Call with `n` message registers already set.
fn reply_words<S: Store>(s: &mut S, t: Tcb, n: u64) {
    t.set_reg(s, reg::BADGE, 0);
    msg::set_msg_info(s, t, MessageInfo::new(0, 0, 0, n));
}

/// seL4 `installTCBCap`.
fn install_tcb_cap<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, slot: Slot, index: u64, new_cap: Cap, src: Slot) -> KResult<()> {
    let root = target.slot(index);
    cdt::delete(s, a, root, true)?;
    if !new_cap.is_null() && still_valid(s, target, slot, new_cap, src) {
        cdt::insert(s, new_cap, src, root);
    }
    Ok(())
}

/// seL4 `checkCapAt` for a cap about to be installed in a TCB slot: its
/// source still holds it, and the invoked TCB cap is still in place (both
/// may have been deleted while the old cap was).
fn still_valid<S: Store>(s: &S, target: Tcb, slot: Slot, new_cap: Cap, src: Slot) -> bool {
    if src.is_null() || !objects::same_object_as(new_cap, src.cap(s)) {
        return false;
    }
    objects::same_object_as(Cap::Thread { ptr: target.0 }, slot.cap(s))
}

/// The IPC buffer part of `TCB_Configure`/`SetIPCBuffer`.
fn install_buffer<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, slot: Slot, buffer_addr: u64, buffer: (Cap, Slot)) -> KResult<()> {
    let bslot = target.slot(tl::SLOT_BUFFER);
    cdt::delete(s, a, bslot, true)?;
    target.set_ipc_buffer(s, buffer_addr);
    if still_valid(s, target, slot, buffer.0, buffer.1) {
        cdt::insert(s, buffer.0, buffer.1, bslot);
    }
    if target == sched::cur_thread(s) {
        sched::reschedule_required(s);
    }
    Ok(())
}

const UPDATE_FAULT: u64 = 1;
const UPDATE_TIMEOUT: u64 = 2;
const UPDATE_SPACE: u64 = 4;
const UPDATE_IPC_BUFFER: u64 = 8;

#[allow(clippy::too_many_arguments)]
fn thread_control_caps<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    target: Tcb,
    slot: Slot,
    fh: (Cap, Slot),
    th: (Cap, Slot),
    croot: (Cap, Slot),
    vroot: (Cap, Slot),
    buffer_addr: u64,
    buffer: (Cap, Slot),
    flags: u64,
) -> KResult<()> {
    if flags & UPDATE_FAULT != 0 {
        install_tcb_cap(s, a, target, slot, tl::SLOT_FAULT_HANDLER, fh.0, fh.1)?;
    }
    if flags & UPDATE_TIMEOUT != 0 {
        install_tcb_cap(s, a, target, slot, tl::SLOT_TIMEOUT_HANDLER, th.0, th.1)?;
    }
    if flags & UPDATE_SPACE != 0 {
        install_tcb_cap(s, a, target, slot, tl::SLOT_CTABLE, croot.0, croot.1)?;
        install_tcb_cap(s, a, target, slot, tl::SLOT_VTABLE, vroot.0, vroot.1)?;
    }
    if flags & UPDATE_IPC_BUFFER != 0 {
        install_buffer(s, a, target, slot, buffer_addr, buffer)?;
    }
    Ok(())
}

const SCHED_UPDATE_SC: u64 = 1;
const SCHED_UPDATE_FAULT: u64 = 2;
const SCHED_UPDATE_MCP: u64 = 4;
const SCHED_UPDATE_PRIO: u64 = 8;

#[allow(clippy::too_many_arguments)]
fn thread_control_sched<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    target: Tcb,
    slot: Slot,
    fh: (Cap, Slot),
    mcp: u64,
    prio: u64,
    sc: Sc,
    flags: u64,
) -> KResult<()> {
    if flags & SCHED_UPDATE_FAULT != 0 {
        install_tcb_cap(s, a, target, slot, tl::SLOT_FAULT_HANDLER, fh.0, fh.1)?;
    }
    if flags & SCHED_UPDATE_MCP != 0 {
        target.set_mcp(s, mcp);
    }
    if flags & SCHED_UPDATE_PRIO != 0 {
        sched::set_priority(s, target, prio);
    }
    if flags & SCHED_UPDATE_SC != 0 {
        if !sc.is_null() {
            schedcontext::bind_tcb(s, a, sc, target);
        } else {
            let old = Sc(target.sc(s));
            if !old.is_null() {
                schedcontext::unbind_tcb(s, old);
            }
        }
    }
    Ok(())
}

fn derive_for_buffer<S: Store>(s: &S, buffer_addr: u64, bslot: Slot) -> KResult<(Cap, Slot)> {
    if buffer_addr == 0 {
        return Ok((bslot.cap(s), Slot(0)));
    }
    let c = objects::derive_cap(s, bslot, bslot.cap(s))?;
    vspace::check_valid_ipc_buffer(buffer_addr, c)?;
    Ok((c, bslot))
}

fn derive_roots<S: Store>(s: &S, target: Tcb, cdata: u64, vdata: u64, cslot: Slot, vslot: Slot) -> KResult<(Cap, Cap)> {
    if cdt::slot_cap_long_running_delete(s, target.slot(tl::SLOT_CTABLE))
        || cdt::slot_cap_long_running_delete(s, target.slot(tl::SLOT_VTABLE))
    {
        return illegal();
    }
    let ccap = derive_with_data(s, cslot, cdata)?;
    if !is_cnode(ccap) {
        return illegal();
    }
    let vcap = derive_with_data(s, vslot, vdata)?;
    if !vspace::is_valid_vtable_root(vcap) {
        return illegal();
    }
    Ok((ccap, vcap))
}

/// The cap in `slot`, with `data` applied if nonzero, derived.
fn derive_with_data<S: Store>(s: &S, slot: Slot, data: u64) -> KResult<Cap> {
    let mut c = slot.cap(s);
    if data != 0 {
        c = objects::update_cap_data(false, data, c);
    }
    objects::derive_cap(s, slot, c)
}

fn is_cnode(c: Cap) -> bool {
    matches!(c, Cap::CNode { .. })
}

fn copy_registers<S: Store, A: Arch>(s: &mut S, a: &mut A, dest: Tcb, src: Tcb, flags: u64) -> KResult<()> {
    if flags & 1 != 0 {
        sched::suspend(s, a, src);
    }
    if flags & 2 != 0 {
        sched::restart(s, a, dest);
    }
    if flags & 4 != 0 {
        let mut i = 0;
        while i < N_FRAME {
            let r = FRAME_REGISTERS[i as usize];
            let v = src.reg(s, r);
            dest.set_reg(s, r, regs::sanitise(r, v));
            i += 1;
        }
        let pc = dest.reg(s, reg::FAULT_IP);
        dest.set_reg(s, reg::NEXT_IP, pc);
    }
    if flags & 8 != 0 {
        let mut i = 0;
        while i < N_GP {
            let r = GP_REGISTERS[i as usize];
            let v = src.reg(s, r);
            dest.set_reg(s, r, regs::sanitise(r, v));
            i += 1;
        }
    }
    post_modify_registers(s, dest);
    if dest == sched::cur_thread(s) {
        sched::reschedule_required(s);
    }
    Ok(())
}

/// seL4 x86_64 `Mode_postModifyRegisters`: force a full (iret) restore.
fn post_modify_registers<S: Store>(s: &mut S, t: Tcb) {
    if t != sched::cur_thread(s) {
        t.set_reg(s, reg::ERROR, 0);
    }
}

fn read_registers<S: Store, A: Arch>(s: &mut S, a: &mut A, src: Tcb, suspend: bool, n: u64, call: bool) {
    let ct = sched::cur_thread(s);
    if suspend {
        sched::suspend(s, a, src);
    }
    if call {
        let buf = msg::lookup_ipc_buffer(s, true, ct);
        ct.set_reg(s, reg::BADGE, 0);
        let mut i: u64 = 0;
        while i < n && i < N_FRAME && i < N_MSG_REGISTERS {
            let v = src.reg(s, FRAME_REGISTERS[i as usize]);
            ct.set_reg(s, msg::msg_register(i), v);
            i += 1;
        }
        if buf != 0 && i < n && i < N_FRAME {
            while i < n && i < N_FRAME {
                let v = src.reg(s, FRAME_REGISTERS[i as usize]);
                msg::buf_set(s, buf, i + 1, v);
                i += 1;
            }
        }
        let j = i;
        let mut k: u64 = 0;
        while k < N_GP && k + N_FRAME < n && k + N_FRAME < N_MSG_REGISTERS {
            let v = src.reg(s, GP_REGISTERS[k as usize]);
            ct.set_reg(s, msg::msg_register(k + N_FRAME), v);
            k += 1;
        }
        if buf != 0 && k < N_GP && k + N_FRAME < n {
            while k < N_GP && k + N_FRAME < n {
                let v = src.reg(s, GP_REGISTERS[k as usize]);
                msg::buf_set(s, buf, k + N_FRAME + 1, v);
                k += 1;
            }
        }
        msg::set_msg_info(s, ct, MessageInfo::new(0, 0, 0, k.wrapping_add(j)));
    }
    sched::set_thread_state(s, ct, sched::TS_RUNNING);
}

fn write_registers<S: Store, A: Arch>(s: &mut S, a: &mut A, dest: Tcb, resume: bool, n_in: u64, buf: u64) {
    let ct = sched::cur_thread(s);
    let n = if n_in > N_FRAME + N_GP { N_FRAME + N_GP } else { n_in };
    let mut i = 0;
    while i < N_FRAME && i < n {
        let r = FRAME_REGISTERS[i as usize];
        let v = msg::syscall_arg(s, ct, buf, i + 2);
        dest.set_reg(s, r, regs::sanitise(r, v));
        i += 1;
    }
    let mut k = 0;
    while k < N_GP && k + N_FRAME < n {
        let r = GP_REGISTERS[k as usize];
        let v = msg::syscall_arg(s, ct, buf, k + N_FRAME + 2);
        dest.set_reg(s, r, regs::sanitise(r, v));
        k += 1;
    }
    let pc = dest.reg(s, reg::FAULT_IP);
    dest.set_reg(s, reg::NEXT_IP, pc);
    post_modify_registers(s, dest);
    if resume {
        sched::restart(s, a, dest);
    }
    if dest == sched::cur_thread(s) {
        sched::reschedule_required(s);
    }
}

/// Copy `n` words from `src` to `dst`.
fn copy_words<S: Store>(s: &mut S, src: u64, dst: u64, n: u64) {
    let mut i = 0;
    while i < n {
        let v = s.read(src.wrapping_add(i.wrapping_mul(8)));
        s.write(dst.wrapping_add(i.wrapping_mul(8)), v);
        i += 1;
    }
}

/// l4h 0002: copy the FPU image between the TCB and a frame.
fn fpu_transfer<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx, to_frame: bool) -> KResult<()> {
    let fslot = match extra(c, 0) {
        Some(x) if c.length >= 1 => x,
        _ => return truncated(),
    };
    let offset = arg(s, c, 0);
    let (base, size) = match fslot.cap(s) {
        Cap::Frame { ptr, size, rights, is_device, .. } => {
            if is_device || rights == VM_KERNEL_ONLY || (to_frame && rights != VM_READ_WRITE) {
                return invalid_cap(1);
            }
            (ptr, 1u64 << (size.bits() & 63))
        }
        _ => return invalid_cap(1),
    };
    let n = fl4_abi::consts::FPU_STATE_SIZE;
    if offset % 64 != 0 || offset >= size || size - offset < n {
        return invalid_arg(0);
    }
    restart_caller(s);
    a.fpu_flush(target.0);
    let words = (n + 7) / 8;
    let frame = base.wrapping_add(offset);
    if to_frame {
        copy_words(s, target.fpu_addr(), frame, words);
    } else {
        copy_words(s, frame, target.fpu_addr(), words);
    }
    if !to_frame {
        a.fpu_sanitise(target.0);
        a.fpu_reload(target.0);
    }
    Ok(())
}

fn set_breakpoint_checked<S: Store>(s: &mut S, t: Tcb, c: &Ctx) -> KResult<()> {
    let bp = arg(s, c, 0);
    let vaddr = arg(s, c, 1);
    let ty = arg(s, c, 2);
    let size = arg(s, c, 3);
    let rw = arg(s, c, 4);
    if vaddr >= fl4_abi::consts::USER_TOP {
        return invalid_arg(1);
    }
    if ty != debug::INSTRUCTION_BREAKPOINT && ty != debug::DATA_BREAKPOINT {
        return invalid_arg(2);
    }
    if ty == debug::INSTRUCTION_BREAKPOINT {
        if size != 0 {
            return invalid_arg(3);
        }
        if rw != debug::BREAK_ON_READ {
            return invalid_arg(4);
        }
    } else if size == 0 {
        return invalid_arg(3);
    }
    if rw != debug::BREAK_ON_READ && rw != debug::BREAK_ON_WRITE && rw != debug::BREAK_ON_READ_WRITE {
        return invalid_arg(3);
    }
    if size != 0 && size != 1 && size != 2 && size != 4 && size != 8 {
        return invalid_arg(3);
    }
    if size > 0 && vaddr & (size - 1) != 0 {
        return sys(SysError::AlignmentError);
    }
    debug::check_bp_num(bp)?;
    if size == 8 {
        // No CPU FL4 supports has 8-byte breakpoints in the legacy encoding.
        return invalid_arg(3);
    }
    restart_caller(s);
    debug::set_breakpoint(s, t, bp, vaddr, ty, size, rw);
    Ok(())
}

/// seL4 `decodeTCBInvocation`: one decoder per invocation, as in seL4.
pub fn decode<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, target: Tcb, c: &Ctx) -> KResult<()> {
    crate::smp::remote_tcb_stall(s, a, target);
    if lbl == label::TCBSetEPTRoot {
        if c.extra[0].is_null() { return truncated(); }
        let src = c.extra[0];
        let cap = src.cap(s);
        if !matches!(cap, Cap::Ept { level: 0, mapped: true, .. }) { return illegal(); }
        let derived = crate::objects::derive_cap(s, src, cap)?;
        crate::cdt::delete(s, a, target.slot(tl::SLOT_EPT), true)?;
        crate::cdt::insert(s, derived, src, target.slot(tl::SLOT_EPT));
        let ct = sched::cur_thread(s);
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        return Ok(());
    }
    if lbl == label::TCBReadRegisters {
        decode_read_registers(s, a, target, c)
    } else if lbl == label::TCBWriteRegisters {
        decode_write_registers(s, a, target, c)
    } else if lbl == label::TCBCopyRegisters {
        decode_copy_registers(s, a, target, c)
    } else if lbl == label::TCBSuspend {
        restart_caller(s);
        sched::suspend(s, a, target);
        Ok(())
    } else if lbl == label::TCBResume {
        restart_caller(s);
        sched::restart(s, a, target);
        Ok(())
    } else if lbl == label::TCBConfigure {
        decode_configure(s, a, target, c)
    } else if lbl == label::TCBSetPriority || lbl == label::TCBSetMCPriority {
        decode_set_priority(s, a, target, c, lbl == label::TCBSetPriority)
    } else if lbl == label::TCBSetSchedParams {
        decode_set_sched_params(s, a, target, c)
    } else if lbl == label::TCBSetIPCBuffer {
        decode_set_ipc_buffer(s, a, target, c)
    } else if lbl == label::TCBSetSpace {
        decode_set_space(s, a, target, c)
    } else if lbl == label::TCBSetTimeoutEndpoint {
        decode_set_timeout_endpoint(s, a, target, c)
    } else if lbl == label::TCBBindNotification {
        decode_bind_notification(s, target, c)
    } else if lbl == label::TCBUnbindNotification {
        if target.bound_ntfn(s) == 0 {
            return illegal();
        }
        restart_caller(s);
        notification::unbind_notification(s, target);
        Ok(())
    } else if lbl == label::TCBConfigureSingleStepping {
        decode_configure_single_stepping(s, a, target, c)
    } else if lbl == label::TCBSetBreakpoint {
        set_breakpoint_checked(s, target, c)
    } else if lbl == label::TCBGetBreakpoint {
        decode_get_breakpoint(s, target, c)
    } else if lbl == label::TCBUnsetBreakpoint {
        let bp = arg(s, c, 0);
        debug::check_bp_num(bp)?;
        restart_caller(s);
        debug::unset_breakpoint(s, target, bp);
        Ok(())
    } else if lbl == label::TCBSetTLSBase {
        decode_set_tls_base(s, target, c)
    } else if lbl == label::TCBSetFlags {
        decode_set_flags(s, a, target, c)
    } else if lbl == label::TCBSetTimer {
        if c.length < 2 {
            return truncated();
        }
        let deadline = arg(s, c, 0);
        let badge = arg(s, c, 1);
        restart_caller(s);
        timer::insert(s, target, deadline, badge);
        Ok(())
    } else if lbl == label::TCBReadFPU {
        fpu_transfer(s, a, target, c, true)
    } else if lbl == label::TCBWriteFPU {
        fpu_transfer(s, a, target, c, false)
    } else {
        Err(Exc::Sys(SysError::IllegalOperation))
    }
}

/// The thread cap in `slot`, for invocations that take another TCB.
fn thread_arg<S: Store>(s: &S, slot: Slot, pos: u64) -> KResult<Tcb> {
    match slot.cap(s) {
        Cap::Thread { ptr } => Ok(Tcb(ptr)),
        _ => invalid_cap(pos),
    }
}

/// `extra(c, i)` for an invocation that needs at least `min_length` words.
fn extra_with_length(c: &Ctx, i: usize, min_length: u64) -> KResult<Slot> {
    match extra(c, i) {
        Some(x) if c.length >= min_length => Ok(x),
        _ => truncated(),
    }
}

fn decode_read_registers<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    if c.length < 2 {
        return truncated();
    }
    let flags = arg(s, c, 0);
    let n = arg(s, c, 1);
    if n < 1 || n > N_FRAME + N_GP {
        return range(1, N_FRAME + N_GP);
    }
    if target == sched::cur_thread(s) {
        return illegal();
    }
    restart_caller(s);
    read_registers(s, a, target, flags & 1 != 0, n, c.call);
    Ok(())
}

fn decode_write_registers<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    if c.length < 2 {
        return truncated();
    }
    let flags = arg(s, c, 0);
    let w = arg(s, c, 1);
    if c.length - 2 < w {
        return truncated();
    }
    if target == sched::cur_thread(s) {
        return illegal();
    }
    restart_caller(s);
    write_registers(s, a, target, flags & 1 != 0, w, c.buf);
    Ok(())
}

fn decode_copy_registers<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    let src_slot = extra_with_length(c, 0, 1)?;
    let flags = arg(s, c, 0);
    let src = thread_arg(s, src_slot, 1)?;
    // The source may be running on another core too: stop it before
    // reading (and maybe suspending) it. seL4 stalls only the target;
    // a running source's registers would be stale and a suspended one
    // would keep running until that core next entered the kernel.
    crate::smp::remote_tcb_stall(s, a, src);
    restart_caller(s);
    copy_registers(s, a, target, src, flags)
}

fn decode_configure<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    let cs = extra_with_length(c, 0, 3)?;
    let vs = extra_with_length(c, 1, 3)?;
    let bs = extra_with_length(c, 2, 3)?;
    let cdata = arg(s, c, 0);
    let vdata = arg(s, c, 1);
    let baddr = arg(s, c, 2);
    let buffer = derive_for_buffer(s, baddr, bs)?;
    let (ccap, vcap) = derive_roots(s, target, cdata, vdata, cs, vs)?;
    restart_caller(s);
    let none = (Cap::Null, Slot(0));
    thread_control_caps(s, a, target, c.slot, none, none, (ccap, cs), (vcap, vs), baddr, buffer, UPDATE_SPACE | UPDATE_IPC_BUFFER)
}

fn decode_set_priority<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx, prio: bool) -> KResult<()> {
    let auth_slot = extra_with_length(c, 0, 1)?;
    let p = arg(s, c, 0);
    let auth = thread_arg(s, auth_slot, 1)?;
    check_prio(s, p, auth)?;
    restart_caller(s);
    let none = (Cap::Null, Slot(0));
    if prio {
        thread_control_sched(s, a, target, Slot(0), none, 0, p, Sc(0), SCHED_UPDATE_PRIO)
    } else {
        thread_control_sched(s, a, target, Slot(0), none, p, 0, Sc(0), SCHED_UPDATE_MCP)
    }
}

/// The scheduling context a `SetSchedParams` binds, as seL4 checks it.
fn sched_params_sc<S: Store>(s: &S, target: Tcb, sc_slot: Slot) -> KResult<Sc> {
    match sc_slot.cap(s) {
        Cap::SchedContext { ptr, .. } => {
            let sc = Sc(ptr);
            if target.sc(s) != sc.0 && (target.sc(s) != 0 || sc.tcb(s) != 0) {
                return illegal();
            }
            if sched::is_blocked(s, target) && !sporadic::sc_released(s, sc) {
                return illegal();
            }
            Ok(sc)
        }
        Cap::Null => {
            if target == sched::cur_thread(s) {
                return illegal();
            }
            Ok(Sc(0))
        }
        _ => invalid_cap(2),
    }
}

fn decode_set_sched_params<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    let auth_slot = extra_with_length(c, 0, 2)?;
    let sc_slot = extra_with_length(c, 1, 2)?;
    let fh_slot = extra_with_length(c, 2, 2)?;
    let mcp = arg(s, c, 0);
    let prio = arg(s, c, 1);
    let auth = thread_arg(s, auth_slot, 1)?;
    check_prio(s, mcp, auth)?;
    check_prio(s, prio, auth)?;
    let sc = sched_params_sc(s, target, sc_slot)?;
    let mut flags = SCHED_UPDATE_MCP | SCHED_UPDATE_PRIO | SCHED_UPDATE_FAULT;
    if target.sc(s) != sc.0 {
        flags |= SCHED_UPDATE_SC;
    }
    let fh = fh_slot.cap(s);
    if !faults::valid_fault_handler(fh) {
        return invalid_cap(3);
    }
    restart_caller(s);
    thread_control_sched(s, a, target, c.slot, (fh, fh_slot), mcp, prio, sc, flags)
}

fn decode_set_ipc_buffer<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    let bs = extra_with_length(c, 0, 1)?;
    let baddr = arg(s, c, 0);
    let buffer = derive_for_buffer(s, baddr, bs)?;
    restart_caller(s);
    let none = (Cap::Null, Slot(0));
    thread_control_caps(s, a, target, c.slot, none, none, none, none, baddr, buffer, UPDATE_IPC_BUFFER)
}

fn decode_set_space<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    let fs = extra_with_length(c, 0, 2)?;
    let cs = extra_with_length(c, 1, 2)?;
    let vs = extra_with_length(c, 2, 2)?;
    let cdata = arg(s, c, 0);
    let vdata = arg(s, c, 1);
    let (ccap, vcap) = derive_roots(s, target, cdata, vdata, cs, vs)?;
    let fh = fs.cap(s);
    if !faults::valid_fault_handler(fh) {
        return invalid_cap(1);
    }
    restart_caller(s);
    let none = (Cap::Null, Slot(0));
    thread_control_caps(s, a, target, c.slot, (fh, fs), none, (ccap, cs), (vcap, vs), 0, none, UPDATE_SPACE | UPDATE_FAULT)
}

fn decode_set_timeout_endpoint<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    let ts = extra_with_length(c, 0, 0)?;
    let th = ts.cap(s);
    if !faults::valid_fault_handler(th) {
        return invalid_cap(1);
    }
    restart_caller(s);
    let none = (Cap::Null, Slot(0));
    thread_control_caps(s, a, target, c.slot, none, (th, ts), none, none, 0, none, UPDATE_TIMEOUT)
}

/// The notification a `BindNotification` binds, as seL4 checks it.
fn bindable_ntfn<S: Store>(s: &S, ns: Slot) -> KResult<Ntfn> {
    match ns.cap(s) {
        Cap::Notification { ptr, recv, .. } => {
            if !recv {
                return illegal();
            }
            let n = Ntfn(ptr);
            if n.head(s) != 0 || n.bound_tcb(s) != 0 {
                return illegal();
            }
            Ok(n)
        }
        _ => illegal(),
    }
}

fn decode_bind_notification<S: Store>(s: &mut S, target: Tcb, c: &Ctx) -> KResult<()> {
    let ns = extra_with_length(c, 0, 0)?;
    if target.bound_ntfn(s) != 0 {
        return illegal();
    }
    let n = bindable_ntfn(s, ns)?;
    restart_caller(s);
    notification::bind_notification(s, target, n.0);
    Ok(())
}

fn decode_configure_single_stepping<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let bp = arg(s, c, 0);
    let n = arg(s, c, 1);
    restart_caller(s);
    let consumed = debug::configure_single_stepping(s, a, target, bp, n, false);
    if c.call {
        let buf = msg::lookup_ipc_buffer(s, true, ct);
        let len = msg::set_mr(s, ct, buf, 0, if n != 0 && consumed { 1 } else { 0 });
        reply_words(s, ct, len);
    }
    sched::set_thread_state(s, ct, sched::TS_RUNNING);
    Ok(())
}

fn decode_get_breakpoint<S: Store>(s: &mut S, target: Tcb, c: &Ctx) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let bp = arg(s, c, 0);
    debug::check_bp_num(bp)?;
    restart_caller(s);
    let r = debug::get_breakpoint(s, target, bp);
    if c.call {
        let buf = msg::lookup_ipc_buffer(s, true, ct);
        msg::set_mr(s, ct, buf, 0, r.vaddr);
        msg::set_mr(s, ct, buf, 1, r.ty);
        msg::set_mr(s, ct, buf, 2, r.size);
        msg::set_mr(s, ct, buf, 3, r.rw);
        let len = msg::set_mr(s, ct, buf, 4, if r.enabled { 1 } else { 0 });
        reply_words(s, ct, len);
    }
    sched::set_thread_state(s, ct, sched::TS_RUNNING);
    Ok(())
}

fn decode_set_tls_base<S: Store>(s: &mut S, target: Tcb, c: &Ctx) -> KResult<()> {
    if c.length < 1 {
        return truncated();
    }
    let base = arg(s, c, 0);
    restart_caller(s);
    target.set_reg(s, reg::TLS_BASE, regs::sanitise(reg::TLS_BASE, base));
    if target == sched::cur_thread(s) {
        sched::reschedule_required(s);
    }
    Ok(())
}

fn decode_set_flags<S: Store, A: Arch>(s: &mut S, a: &mut A, target: Tcb, c: &Ctx) -> KResult<()> {
    if c.length < 2 {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let clear = arg(s, c, 0);
    let set = arg(s, c, 1);
    restart_caller(s);
    let mut f = target.flags(s);
    f &= !clear;
    f |= set & tcb_flag::MASK;
    target.set_flags(s, f);
    if f & tcb_flag::FPU_DISABLED != 0 {
        a.fpu_release(target.0);
    }
    if c.call {
        let buf = msg::lookup_ipc_buffer(s, true, ct);
        let len = msg::set_mr(s, ct, buf, 0, f);
        reply_words(s, ct, len);
    }
    sched::set_thread_state(s, ct, sched::TS_RUNNING);
    Ok(())
}

