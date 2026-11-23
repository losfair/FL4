/// seL4 `decodeIRQControlInvocation` with the ARM arch part (GetTrigger,
/// and GetTriggerCore for a banked interrupt of another core or to route
/// an SPI). The plain `IRQIssueIRQHandler` leaves the trigger as it is.
pub fn decode_irq_control<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, src: Slot, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    if lbl == label::ARMIRQIssueIRQHandlerMSI {
        return decode_irq_control_msi(s, a, length, src, buf, extra);
    }
    let ct = sched::cur_thread(s);
    let plain = lbl == label::IRQIssueIRQHandler;
    let with_core = lbl == label::ARMIRQIssueIRQHandlerTriggerCore;
    if !plain && !with_core && lbl != label::ARMIRQIssueIRQHandlerTrigger {
        return illegal();
    }
    let min_len = if plain { 3 } else if with_core { 5 } else { 4 };
    let cnode = match extra0(s, extra) {
        Some(c) if length >= min_len => c,
        _ => return truncated(),
    };
    let irq_w = msg::syscall_arg(s, ct, buf, 0);
    let (edge, index, depth) = if plain {
        (false, msg::syscall_arg(s, ct, buf, 1), msg::syscall_arg(s, ct, buf, 2))
    } else {
        let d = msg::syscall_arg(s, ct, buf, 3);
        (msg::syscall_arg(s, ct, buf, 1) != 0, msg::syscall_arg(s, ct, buf, 2), if with_core { d & 0xff } else { d })
    };
    let cpu = if with_core { msg::syscall_arg(s, ct, buf, 4) } else { 0 };
    let max = a.max_spi();
    if irq_w > max {
        return range(0, max);
    }
    if with_core && cpu >= ks_get(s, ks::NUM_NODES) {
        return Err(Exc::Sys(SysError::InvalidArgument { arg: 4 }));
    }
    if !plain && !with_core && irq_w < irqn::SPI_MIN && fl4_abi::config::ENABLE_SMP_SUPPORT {
        return illegal();
    }
    let irq = irqn::of(irq_w, cpu);
    if is_irq_active(s, irq) {
        return Err(Exc::Sys(SysError::RevokeFirst));
    }
    let dest = cspace::lookup_target_slot(s, cnode, index, depth)?;
    cdt::ensure_empty_slot(s, dest)?;
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    if !plain {
        a.configure_irq(irq, edge, cpu);
    }
    invoke_irq_control(s, a, irq, dest, src);
    Ok(())
}

/// FL4 `GetMSI` (interfaces/object-api-extensions.xml): a handler for LPI
/// `irq`, which the ITS raises for event `event` of device `device` on
/// core `target`. The mapping is made last, once nothing else can fail;
/// the backend refuses (and changes nothing) without an ITS, for a device
/// or event it cannot map, or an event mapped already.
pub fn decode_irq_control_msi<S: Store, A: Arch>(s: &mut S, a: &mut A, length: u64, src: Slot, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let cnode = match extra0(s, extra) {
        Some(c) if length >= 6 => c,
        _ => return truncated(),
    };
    let n = msg::syscall_arg(s, ct, buf, 0);
    let device = msg::syscall_arg(s, ct, buf, 1);
    let event = msg::syscall_arg(s, ct, buf, 2);
    let index = msg::syscall_arg(s, ct, buf, 3);
    let depth = msg::syscall_arg(s, ct, buf, 4) & 0xff;
    let cpu = msg::syscall_arg(s, ct, buf, 5);
    if n >= irqn::NUM_LPIS {
        return range(0, irqn::NUM_LPIS - 1);
    }
    if cpu >= ks_get(s, ks::NUM_NODES) {
        return Err(Exc::Sys(SysError::InvalidArgument { arg: 5 }));
    }
    let irq = irqn::LPI_BASE + n;
    if is_irq_active(s, irq) {
        return Err(Exc::Sys(SysError::RevokeFirst));
    }
    let dest = cspace::lookup_target_slot(s, cnode, index, depth)?;
    cdt::ensure_empty_slot(s, dest)?;
    use crate::machine::msi;
    match a.msi_map(irq, device, event, cpu) {
        msi::OK => {}
        msi::BAD_DEVICE => return Err(Exc::Sys(SysError::InvalidArgument { arg: 1 })),
        msi::BAD_EVENT => return Err(Exc::Sys(SysError::InvalidArgument { arg: 2 })),
        _ => return illegal(),
    }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    invoke_irq_control(s, a, irq, dest, src);
    Ok(())
}
