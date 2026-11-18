/* fl4_bad_iret iret_a, iret_b, user: for an entry from kernel mode whose
 * frame (entry.S order) is at %rbp, jump to \user if it is a #GP or #SS
 * that one of the IRETs to user mode at \iret_a or \iret_b raised, after
 * turning the frame into the user-mode entry that IRET would have led to
 * had it faulted in user mode; else fall through. Clobbers rax, rcx, rdx,
 * rsi and the flags.
 *
 * IRET checks the return state in ring 0: a thread whose next instruction
 * is at a non-canonical address (an INT3, INT n or SYSCALL in the last
 * bytes below the sign-extension hole, or an interrupt after the last
 * instruction there) makes it raise #GP(0) in the kernel, which would
 * otherwise panic. The fault leaves the IRET frame, as IRET found it, at
 * the stack pointer the fault's frame saved (the CPU aligns its own push
 * below it), and the user's registers in the frame's GPRs. Its five words
 * replace the kernel-mode part of the frame (error code 0) and are cleared
 * where they were, so fl4_entry sees the fault as the user's own, at the
 * return address, and handles it as any other (handle_user_exception).
 * Host-tested by fl4-arch-x86_64/tests/kernel_bad_iret.rs. */
.macro fl4_bad_iret iret_a, iret_b, user
    movq 15*8(%rbp), %rax
    cmpq $13, %rax
    je .Lbad_iret_vector\@
    cmpq $12, %rax
    jne .Lbad_iret_no\@
.Lbad_iret_vector\@:
    leaq \iret_a(%rip), %rax
    cmpq %rax, 17*8(%rbp)
    je .Lbad_iret_at\@
    leaq \iret_b(%rip), %rax
    cmpq %rax, 17*8(%rbp)
    jne .Lbad_iret_no\@
.Lbad_iret_at\@:
    movq 20*8(%rbp), %rsi
    testb $3, 8(%rsi)
    jz .Lbad_iret_no\@
    xorl %ecx, %ecx
.Lbad_iret_copy\@:
    movq (%rsi,%rcx,8), %rdx
    movq %rdx, 17*8(%rbp,%rcx,8)
    movq $0, (%rsi,%rcx,8)
    incl %ecx
    cmpl $5, %ecx
    jne .Lbad_iret_copy\@
    movq $0, 16*8(%rbp)
    jmp \user
.Lbad_iret_no\@:
.endm
