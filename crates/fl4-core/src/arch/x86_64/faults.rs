/// x86_64 `syscallMessage`.
pub const SYSCALL_MESSAGE: [u64; 18] = [
    reg::RAX,
    reg::RBX,
    reg::RCX,
    reg::RDX,
    reg::RSI,
    reg::RDI,
    reg::RBP,
    reg::R8,
    reg::R9,
    reg::R10,
    reg::R11,
    reg::R12,
    reg::R13,
    reg::R14,
    reg::R15,
    reg::FAULT_IP,
    reg::RSP,
    reg::FLAGS,
];

/// x86_64 `exceptionMessage`.
pub const EXCEPTION_MESSAGE: [u64; 3] = [reg::FAULT_IP, reg::RSP, reg::FLAGS];

/// x86_64 `timeoutReplyMessage`.
pub const TIMEOUT_REPLY_MESSAGE: [u64; 19] = [
    reg::FAULT_IP,
    reg::RSP,
    reg::FLAGS,
    reg::RAX,
    reg::RBX,
    reg::RCX,
    reg::RDX,
    reg::RSI,
    reg::RDI,
    reg::RBP,
    reg::R8,
    reg::R9,
    reg::R10,
    reg::R11,
    reg::R12,
    reg::R13,
    reg::R14,
    reg::R15,
    reg::TLS_BASE,
];

/// Where the syscall number goes in an UnknownSyscall message. (A macro,
/// so the x86_64 code the proofs are about keeps its literal.)
macro_rules! unknown_syscall_number_mr {
    () => {
        18
    };
}

/// AArch64 appends a trapping thread's other registers to its UnknownSyscall
/// message; x86_64's message has every general register already.
macro_rules! trap_syscall_message {
    ($s:expr, $sender:expr, $buf:expr, $n:expr) => {
        $n
    };
}

macro_rules! trap_syscall_reply {
    ($s:expr, $sender:expr, $receiver:expr, $len:expr) => {};
}
