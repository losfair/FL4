/// The length of the syscall instruction (SYSCALL, SVC). A macro, so the
/// x86_64 code the proofs are about keeps its literal.
macro_rules! syscall_insn_len {
    () => {
        2
    };
}

/// The number a trapped syscall reports: the seL4 number register on
/// x86_64, x8 (the Linux syscall number) on AArch64 (l4h 0015).
macro_rules! trapped_syscall_number {
    ($s:expr, $t:expr, $number:expr) => {
        $number as u64
    };
}

/// Whether a fault's code says it was an instruction fetch: bit 4 of the
/// x86 page-fault error code; on AArch64 the ESR's class (instruction
/// abort from EL0).
macro_rules! instruction_fault {
    ($code:expr) => {
        ($code >> 4) & 1 != 0
    };
}

/// `int $N` from user space on a gate it may use: seL4 reports this as an
/// unknown syscall whose number combines the vector and EAX.
/// The fault address is the `int $N` itself (two bytes long), from
/// NextIP as for a syscall: FaultIP may already name it (the entry saves
/// it so for a stall that cancels the entry before this runs).
pub fn handle_trap_syscall<S: Store, A: Arch>(s: &mut S, a: &mut A, vector: u64) {
    let t = sched::cur_thread(s);
    let next = t.reg(s, reg::NEXT_IP);
    t.set_reg(s, reg::FAULT_IP, next.wrapping_sub(2));
    // l4h 0001: a thread with trapSyscalls set has only its syscall
    // instructions as system calls. `int $N` gets the #GP it raises where
    // the gate is closed, with the IDT vector in the error code.
    if t.flags(s) & tcb_flag::TRAP_SYSCALLS != 0 {
        handle_user_exception(s, a, 13, (vector << 3) | 2);
        return;
    }
    let eax = t.reg(s, reg::RAX);
    let num = (vector << 24) | (eax & 0x00ff_ffff);
    let _ = handle_unknown_syscall(s, a, num as i64, false);
}
