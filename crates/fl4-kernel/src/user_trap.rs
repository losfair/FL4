//! A #BP or #DB a thread took in user mode and the kernel has not yet
//! delivered (entry.rs `exit`). Kept in the thread's DR6 debug slot,
//! which the exit path never loads: DR6 is read and cleared at the entry.
//! `exit` reads the slot only after an entry that may have left one or
//! made its thread current (percpu `check_user_trap`, or the gate held).
//! No hardware access, so the backend's host tests run it
//! (fl4-arch-x86_64 tests/kernel_user_trap.rs).

/// The debug slot (`Tcb::debug_reg`) that holds the word.
pub const SLOT: u64 = 4;
/// The debug slot holding the thread's DR7.
pub const DR7_SLOT: u64 = 5;
/// The slot's value with nothing pending (`debug::init_context`'s DR6).
pub const NONE: u64 = 0xffff_0ff0;
/// A #BP (`int3`) is pending.
const BP: u64 = 1 << 63;
/// A #DB is pending.
const DB: u64 = 1 << 62;
/// Bits 16..=61: the low 46 bits of the address the thread resumes at.
const IP_SHIFT: u64 = 16;
const IP_MASK: u64 = (1 << 46) - 1;
/// Bits 0..=15: DR6's status bits (B0-B3, BD, BS, BT), all that
/// `debug::debug_exception` reads.
const DR6_MASK: u64 = 0xffff;

/// A pending trap: its vector, the DR6 its entry read (16 bits, 0 when
/// it read none), and the low 46 bits of the address it resumes at.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Trap {
    pub vector: u64,
    pub dr6: u64,
    pub ip: u64,
}

/// The word for user-mode vector `v` (1 or 3) taken with the thread to
/// resume at `ip`, and `dr6` as its entry read it (0 when it did not).
pub fn encode(v: u64, dr6: u64, ip: u64) -> u64 {
    let kind = if v == 3 { BP } else { DB };
    kind | (ip & IP_MASK) << IP_SHIFT | if v == 3 { 0 } else { dr6 & DR6_MASK }
}

/// The pending trap `w` holds, if any.
pub fn decode(w: u64) -> Option<Trap> {
    let ip = (w >> IP_SHIFT) & IP_MASK;
    if w & BP != 0 {
        Some(Trap { vector: 3, dr6: 0, ip })
    } else if w & DB != 0 {
        Some(Trap { vector: 1, dr6: w & DR6_MASK, ip })
    } else {
        None
    }
}

impl Trap {
    /// Whether the thread is still where it trapped: it resumes at
    /// `fault_ip`, and a breakpoint the #DB names (the lowest of B0-B3,
    /// as `debug_exception` picks it) is still enabled in `dr7`.
    pub fn current(&self, fault_ip: u64, dr7: u64) -> bool {
        if self.ip != fault_ip & IP_MASK {
            return false;
        }
        if self.vector != 1 || self.dr6 & 0xf == 0 {
            return true;
        }
        let bp = (self.dr6 & 0xf).trailing_zeros() as u64;
        dr7 & 1 << (2 * bp + 1) != 0
    }
}
