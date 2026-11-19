/* SPDX-License-Identifier: GPL-2.0-only */
/*
 * Zen 3/4 Safe RET. The two addresses below alias in the BTB. A direct
 * jump from the untraining address evicts a prediction at the safe RET
 * address. CALL then gives RET a speculative target that traps rather
 * than following the architectural return address.
 *
 * Adapted from Linux arch/x86/lib/retpoline.S (the Zen 3/4 alias thunks).
 */
.section .text.safe_ret.untrain, "ax", @progbits
.global fl4_untrain_ret
fl4_untrain_ret:
    .byte 0x66, 0x90
    lfence
    jmp fl4_safe_ret_thunk

.section .text.safe_ret.return, "ax", @progbits
.global fl4_safe_ret
fl4_safe_ret:
    leaq 8(%rsp), %rsp
.global fl4_safe_ret_insn
fl4_safe_ret_insn:
    ret
    int3

/* The byte after RET is both an INT3 and the displacement for JMP rel8
 * (-52). Boot changes only the opcode, from RET to JMP, on Safe RET CPUs.
 * Either value decodes correctly if an NMI arrives while APs are parked. */
fl4_safe_ret_thunk:
    call fl4_safe_ret
    ud2
    .fill 50 - (. - fl4_safe_ret_thunk), 1, 0xcc

.global __x86_return_thunk
.type __x86_return_thunk, @function
__x86_return_thunk:
    ret
    int3
.size __x86_return_thunk, . - __x86_return_thunk

/* Complete an interrupted CALL/LEA/RET using the architectural stack.
 * Linux's handle_interrupted_saferet does the same repair. Once an
 * interrupt has run, returning to the RET could use a poisoned predictor.
 * The caller has saved the GPRs. Only a kernel CS can have been executing
 * the thunk.
 */
.macro fl4_finish_interrupted_safe_ret frame=%rsp
    cmpw $0x10, 18*8(\frame)
    jne .Lsrso_done_\@
    movq 17*8(\frame), %rax
    leaq fl4_safe_ret(%rip), %rdx
    cmpq %rdx, %rax
    je .Lsrso_before_lea_\@
    leaq fl4_safe_ret_insn(%rip), %rdx
    cmpq %rdx, %rax
    jne .Lsrso_done_\@
    movq 20*8(\frame), %rax
    jmp .Lsrso_finish_\@
.Lsrso_before_lea_\@:
    movq 20*8(\frame), %rax
    addq $8, %rax
.Lsrso_finish_\@:
    lfence
    movq (%rax), %rdx
    movq %rdx, 17*8(\frame)
    addq $8, %rax
    movq %rax, 20*8(\frame)
.Lsrso_done_\@:
.endm
