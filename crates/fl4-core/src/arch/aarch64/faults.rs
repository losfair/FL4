/// AArch64 `syscallMessage`.
pub const SYSCALL_MESSAGE: [u64; 12] = [
    reg::X0,
    reg::X1,
    reg::X2,
    reg::X3,
    reg::X4,
    reg::X5,
    reg::X6,
    reg::X7,
    reg::FAULT_IP,
    reg::SP_EL0,
    reg::ELR_EL1,
    reg::SPSR_EL1,
];

/// AArch64 `exceptionMessage`.
pub const EXCEPTION_MESSAGE: [u64; 3] = [reg::FAULT_IP, reg::SP_EL0, reg::SPSR_EL1];

/// AArch64 `timeoutReplyMessage`.
pub const TIMEOUT_REPLY_MESSAGE: [u64; 34] = [
    reg::FAULT_IP,
    reg::SP_EL0,
    reg::SPSR_EL1,
    reg::X0,
    reg::X1,
    reg::X2,
    reg::X3,
    reg::X4,
    reg::X5,
    reg::X6,
    reg::X7,
    reg::X8,
    reg::X16,
    reg::X17,
    reg::X18,
    reg::X29,
    reg::X30,
    reg::X9,
    reg::X10,
    reg::X11,
    reg::X12,
    reg::X13,
    reg::X14,
    reg::X15,
    reg::X19,
    reg::X20,
    reg::X21,
    reg::X22,
    reg::X23,
    reg::X24,
    reg::X25,
    reg::X26,
    reg::X27,
    reg::X28,
];

macro_rules! unknown_syscall_number_mr {
    () => {
        12
    };
}

/// FL4 (l4h): an UnknownSyscall fault of a thread that traps its syscalls
/// (`tcb_flag::TRAP_SYSCALLS`) carries the rest of its user registers after
/// the standard message: x8-x30, then TPIDR_EL0, from message register
/// `TRAP_EXTRA_FIRST`, as x86_64's carries every general register. A reply
/// at least `TRAP_FULL_LENGTH` long writes them back too. A handler then
/// needs no TCB_ReadRegisters or TCB_WriteRegisters around a syscall, which
/// would run under the serial gate.
pub const TRAP_EXTRA_MESSAGE: [u64; 24] = [
    reg::X8, reg::X9, reg::X10, reg::X11, reg::X12, reg::X13, reg::X14, reg::X15,
    reg::X16, reg::X17, reg::X18, reg::X19, reg::X20, reg::X21, reg::X22, reg::X23,
    reg::X24, reg::X25, reg::X26, reg::X27, reg::X28, reg::X29, reg::X30,
    reg::TPIDR_EL0,
];
/// After the standard message's 13 words (the syscall number last).
pub const TRAP_EXTRA_FIRST: u64 = 13;
pub const TRAP_FULL_LENGTH: u64 = TRAP_EXTRA_FIRST + TRAP_EXTRA_MESSAGE.len() as u64;

/// `set_mrs_fault` for an UnknownSyscall whose standard message is `n`
/// words: a trapping sender's extra registers, when the receiver has an
/// IPC buffer (they are past the message registers). Returns the length.
#[inline(always)]
fn trap_extra_mrs<S: Store>(s: &mut S, sender: Tcb, buf: u64, n: u64) -> u64 {
    if buf == 0 || n != TRAP_EXTRA_FIRST || sender.flags(s) & fl4_abi::consts::tcb_flag::TRAP_SYSCALLS == 0 {
        return n;
    }
    let mut i: usize = 0;
    while i < TRAP_EXTRA_MESSAGE.len() {
        let v = sender.reg(s, TRAP_EXTRA_MESSAGE[i]);
        msg::buf_set(s, buf, TRAP_EXTRA_FIRST.wrapping_add(i as u64).wrapping_add(1), v);
        i += 1;
    }
    TRAP_FULL_LENGTH
}

/// `handle_fault_reply` for an UnknownSyscall: a full-length reply to a
/// trapping thread also sets its extra registers.
#[inline(always)]
fn trap_extra_reply<S: Store>(s: &mut S, sender: Tcb, receiver: Tcb, length: u64) {
    if length < TRAP_FULL_LENGTH || receiver.flags(s) & fl4_abi::consts::tcb_flag::TRAP_SYSCALLS == 0 {
        return;
    }
    let buf = msg::lookup_ipc_buffer(s, false, sender);
    if buf == 0 {
        return;
    }
    let mut i: usize = 0;
    while i < TRAP_EXTRA_MESSAGE.len() {
        let r = TRAP_EXTRA_MESSAGE[i];
        let v = msg::buf_get(s, buf, TRAP_EXTRA_FIRST.wrapping_add(i as u64).wrapping_add(1));
        receiver.set_reg(s, r, sanitise_reg!(s, receiver, r, v));
        i += 1;
    }
}

macro_rules! trap_syscall_message {
    ($s:expr, $sender:expr, $buf:expr, $n:expr) => {{
        let n = $n;
        trap_extra_mrs($s, $sender, $buf, n)
    }};
}

macro_rules! trap_syscall_reply {
    ($s:expr, $sender:expr, $receiver:expr, $len:expr) => {
        trap_extra_reply($s, $sender, $receiver, $len)
    };
}
