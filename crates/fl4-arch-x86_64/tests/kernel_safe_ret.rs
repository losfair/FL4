//! Host test of the Safe RET interrupt recovery used by the kernel entry.
#![cfg(target_arch = "x86_64")]

core::arch::global_asm!(
    include_str!("../../fl4-kernel/src/safe_ret.S"),
    ".text
    .global fl4_test_finish_safe_ret
fl4_test_finish_safe_ret:
    fl4_finish_interrupted_safe_ret %rdi
    ret",
    options(att_syntax)
);

extern "C" {
    fn fl4_test_finish_safe_ret(frame: *mut u64);
    fn fl4_safe_ret();
    fn fl4_safe_ret_insn();
}

const RIP: usize = 17;
const CS: usize = 18;
const RSP: usize = 20;

#[test]
fn completes_a_kernel_return_interrupted_at_either_instruction() {
    let stack = [0x1111, 0x2222, 0x3333];
    for (ip, sp) in [
        (fl4_safe_ret as *const (), &stack[0]),
        (fl4_safe_ret_insn as *const (), &stack[1]),
    ] {
        let mut frame = [0xabab; 22];
        frame[RIP] = ip as u64;
        frame[CS] = 0x10;
        frame[RSP] = sp as *const u64 as u64;
        let mut expected = frame;
        expected[RIP] = stack[1];
        expected[RSP] = &stack[2] as *const u64 as u64;
        unsafe { fl4_test_finish_safe_ret(frame.as_mut_ptr()) };
        assert_eq!(frame, expected);
    }
}

#[test]
fn ignores_user_frames_and_other_kernel_instructions() {
    for (cs, ip) in [
        (0x33, fl4_safe_ret as *const ()),
        (0x33, fl4_safe_ret_insn as *const ()),
        (0x10, fl4_test_finish_safe_ret as *const ()),
    ] {
        let mut frame = [0xabab; 22];
        frame[RIP] = ip as u64;
        frame[CS] = cs;
        frame[RSP] = 0;
        let expected = frame;
        unsafe { fl4_test_finish_safe_ret(frame.as_mut_ptr()) };
        assert_eq!(frame, expected);
    }
}
