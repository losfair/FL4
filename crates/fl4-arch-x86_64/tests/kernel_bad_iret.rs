//! The kernel's recovery from a faulting IRET to user mode (fl4-kernel
//! bad_iret.S, used by entry.S `fl4_common_entry`), run on the host on
//! frames in entry.S order: 15 GPRs, vector, error, then the hardware's
//! rip, cs, rflags, rsp, ss.
#![cfg(target_arch = "x86_64")]

core::arch::global_asm!(
    include_str!("../../fl4-kernel/src/bad_iret.S"),
    ".text
    .global fl4_test_bad_iret
fl4_test_bad_iret:
    pushq %rbp
    movq %rdi, %rbp
    fl4_bad_iret fl4_test_iret_a, fl4_test_iret_b, 1f
    xorl %eax, %eax
    popq %rbp
    ret
1:
    movl $1, %eax
    popq %rbp
    ret
    .global fl4_test_iret_a
fl4_test_iret_a:
    iretq
    .global fl4_test_iret_b
fl4_test_iret_b:
    iretq",
    options(att_syntax)
);

extern "C" {
    fn fl4_test_bad_iret(frame: *mut u64) -> u64;
    fn fl4_test_iret_a();
    fn fl4_test_iret_b();
}

const VECTOR: usize = 15;
const ERROR: usize = 16;
const RIP: usize = 17;
const CS: usize = 18;
const RSP: usize = 20;
const USER: [u64; 5] = [0x0000_8000_0000_0000, 0x33, 0x246, 0x7fff_ffff_e000, 0x2b];

/// A kernel-mode fault's frame at the start of `stack`, with the IRET
/// frame it interrupted at word `at` (22, or 23 when the CPU aligned its
/// push below it). Words not set are a marker, to see what moved.
fn stack(vector: u64, rip: u64, at: usize, outer: [u64; 5]) -> [u64; 28] {
    let mut s = [0x5a5a_5a5a; 28];
    for (i, w) in s.iter_mut().enumerate().take(VECTOR) {
        *w = 0x1000 + i as u64;
    }
    s[VECTOR] = vector;
    s[ERROR] = 0;
    s[RIP] = rip;
    s[CS] = 0x10;
    s[19] = 0x2;
    s[RSP] = 0;
    s[21] = 0x18;
    s[at..at + 5].copy_from_slice(&outer);
    s
}

fn run(s: &mut [u64; 28], at: usize) -> bool {
    s[RSP] = &s[at] as *const u64 as u64;
    unsafe { fl4_test_bad_iret(s.as_mut_ptr()) == 1 }
}

#[test]
fn a_fault_of_an_iret_to_user_mode_becomes_the_users() {
    let a = fl4_test_iret_a as usize as u64;
    let b = fl4_test_iret_b as usize as u64;
    for (vector, rip, at) in [(13, a, 22), (13, b, 23), (12, a, 23), (12, b, 22)] {
        let mut s = stack(vector, rip, at, USER);
        assert!(run(&mut s, at), "vector {vector} at {rip:#x}");
        // The user's registers stay, the vector too; the error code is 0
        // and the hardware part is the IRET frame's.
        for (i, w) in s.iter().enumerate().take(VECTOR) {
            assert_eq!(*w, 0x1000 + i as u64);
        }
        assert_eq!(s[VECTOR], vector);
        assert_eq!(s[ERROR], 0);
        assert_eq!(s[RIP..RIP + 5], USER);
        // Nothing of it is left where it was; the alignment word is
        // untouched.
        assert_eq!(s[at..at + 5], [0; 5]);
        if at == 23 {
            assert_eq!(s[22], 0x5a5a_5a5a);
        }
    }
}

#[test]
fn other_kernel_faults_are_left_alone() {
    let a = fl4_test_iret_a as usize as u64;
    let b = fl4_test_iret_b as usize as u64;
    let elsewhere = fl4_test_bad_iret as usize as u64;
    let mut kernel = USER;
    kernel[1] = 0x10;
    kernel[4] = 0x18;
    for (vector, rip, outer) in [
        // Another vector at the IRET (a #PF, an NMI's frame).
        (14, a, USER),
        (2, b, USER),
        // A #GP anywhere else.
        (13, elsewhere, USER),
        (13, a + 1, USER),
        // An IRET back to kernel mode.
        (13, a, kernel),
        (12, b, kernel),
    ] {
        let mut s = stack(vector, rip, 22, outer);
        let before = s;
        assert!(!run(&mut s, 22), "vector {vector} at {rip:#x}");
        let mut want = before;
        want[RSP] = s[RSP];
        assert_eq!(s, want);
    }
}
