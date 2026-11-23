// The kernel is a freestanding staticlib; exercise how it keeps a user
// #BP or #DB a stall would cancel in the backend's host-test harness.
#[allow(dead_code)]
#[path = "../../fl4-kernel/src/user_trap.rs"]
mod user_trap;

use user_trap::{decode, encode, Trap, NONE};

const IP: u64 = 0x40_1234;
/// DR6 with B1 set, and with BS (single step) set.
const DR6_B1: u64 = 0xffff_0ff2;
const DR6_BS: u64 = 0xffff_4ff0;
/// DR7 with breakpoint 1 enabled (L1, bit 3), and with it disabled.
const DR7_B1: u64 = 0x400 | 1 << 3;
const DR7_NONE: u64 = 0x400;

#[test]
fn nothing_is_pending_in_a_fresh_or_cleared_slot() {
    // debug::init_context's DR6, and what exit() writes after delivery.
    assert_eq!(decode(NONE), None);
    assert_eq!(decode(0), None);
}

#[test]
fn a_breakpoint_comes_back_as_vector_3() {
    assert_eq!(decode(encode(3, 0, IP)), Some(Trap { vector: 3, dr6: 0, ip: IP }));
}

#[test]
fn a_debug_trap_keeps_its_dr6_status_bits() {
    // Single-step (BS), a breakpoint hit (B0, B3), and none read (the
    // hardware debug API off).
    for dr6 in [DR6_BS, 0xffff_0ff1, 0xffff_0ff8, 0] {
        assert_eq!(decode(encode(1, dr6, IP)), Some(Trap { vector: 1, dr6: dr6 & 0xffff, ip: IP }), "{dr6:#x}");
    }
}

#[test]
fn the_address_keeps_its_low_46_bits() {
    // The top of the user half has bit 46 set; kernel-half bits are dropped.
    let top = 0x7fff_ffff_f000;
    let t = decode(encode(3, 0, top)).unwrap();
    assert_eq!(t.ip, top & ((1 << 46) - 1));
    assert!(t.current(top, DR7_NONE));
    assert_eq!(decode(encode(1, DR6_BS, 0xffff_8000_0000_0000 | IP)).unwrap().ip, IP);
}

#[test]
fn a_trap_is_current_only_where_the_thread_trapped() {
    for (v, dr6) in [(3, 0), (1, DR6_BS), (1, 0)] {
        let t = decode(encode(v, dr6, IP)).unwrap();
        assert!(t.current(IP, DR7_NONE), "{v} {dr6:#x}");
        assert!(!t.current(IP + 1, DR7_NONE), "{v} {dr6:#x}");
    }
}

#[test]
fn a_breakpoint_hit_is_current_only_while_the_breakpoint_is_enabled() {
    let t = decode(encode(1, DR6_B1, IP)).unwrap();
    assert!(t.current(IP, DR7_B1));
    assert!(!t.current(IP, DR7_NONE));
    // A single step needs no breakpoint.
    assert!(decode(encode(1, DR6_BS, IP)).unwrap().current(IP, DR7_NONE));
}
