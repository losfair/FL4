/* FL4 x86_64 kernel entry and exit.
 *
 * Every entry builds the same frame on the per-core kernel stack and calls
 * fl4_entry (entry.rs). From low to high addresses:
 *   r15 r14 r13 r12 r11 r10 r9 r8 rbp rdi rsi rdx rcx rbx rax
 *   vector error rip cs rflags rsp ss
 * Exceptions and interrupts get the hardware part from the CPU (with a
 * zero error code pushed for vectors without one); SYSCALL builds it by
 * hand, with vector 0x100. fl4_entry returns only for an interrupt taken
 * in kernel mode while the kernel polls for pending interrupts; every
 * other entry leaves through fl4_restore_user or fl4_idle.
 *
 * The kernel never uses GS: the user GS base stays live in GS_BASE, and
 * KERNEL_GS_BASE points at the per-core block whose first word is the
 * kernel stack top and second a scratch word. SYSCALL swaps GS only long
 * enough to find the stack. */

    .text
    .align 16
    .global fl4_vectors
fl4_vectors:
    .set vecnum, 0
    .rept 256
    .align 16
    .if (vecnum == 8) || ((vecnum >= 10) && (vecnum <= 14)) || (vecnum == 17) || (vecnum == 21) || (vecnum == 29) || (vecnum == 30)
    .else
    pushq $0
    .endif
    pushq $vecnum
    jmp fl4_common_entry
    .set vecnum, vecnum + 1
    .endr

    .align 16
    .global fl4_syscall_entry
fl4_syscall_entry:
    swapgs
    lfence
    movq %rsp, %gs:8
    movq %gs:0, %rsp
    pushq $0x2b
    pushq %gs:8
    swapgs
    pushq %r11
    pushq $0x33
    pushq %rcx
    pushq $0
    pushq $0x100

fl4_common_entry:
    pushq %rax
    pushq %rbx
    pushq %rcx
    pushq %rdx
    pushq %rsi
    pushq %rdi
    pushq %rbp
    pushq %r8
    pushq %r9
    pushq %r10
    pushq %r11
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    cld
    movl FL4_SPEC_ENTRY(%rip), %r11d
    fl4_spec_barrier %r11d
    fl4_clear_guest_gprs
    movq %rsp, %rdi
    call fl4_entry
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %r11
    popq %r10
    popq %r9
    popq %r8
    popq %rbp
    popq %rdi
    popq %rsi
    popq %rdx
    popq %rcx
    popq %rbx
    popq %rax
    addq $16, %rsp
    fl4_clear_buffers
    iretq

/* fl4_restore_user(regs: *const u64, stack_top: u64, cr3: u64) -> !
 * regs is a TCB's register array (fl4_core::layout::reg order). A nonzero
 * cr3 (the skim window, spec.rs) is loaded after the last read of the TCB,
 * which the user's tables do not map; the kernel stack is in the image,
 * which they do.
 *
 * A thread whose context SYSCALL saved (Error = -1, as in seL4; changing
 * its registers through the API clears it) leaves by SYSRET, which loads
 * RIP from rcx and RFLAGS from r11, both of which SYSCALL clobbered. Only
 * if the return address is in the canonical lower half: SYSRET to a
 * non-canonical address faults in ring 0 on Intel, after the user's RSP
 * is loaded. Everything else leaves by IRET. */
    .align 16
    .global fl4_restore_user
fl4_restore_user:
    movq %rsi, %rsp
    movq 14*8(%rdi), %rcx
    shrq $47, %rcx
    jnz 1f
    cmpq $-1, 15*8(%rdi)
    je 3f
1:
    pushq $0x2b
    pushq 16*8(%rdi)
    pushq 13*8(%rdi)
    pushq $0x33
    pushq 14*8(%rdi)
    pushq %rdx
    pushq 0*8(%rdi)
    movq 1*8(%rdi), %rsi
    movq 2*8(%rdi), %rax
    movq 3*8(%rdi), %rbx
    movq 4*8(%rdi), %rbp
    movq 5*8(%rdi), %r12
    movq 6*8(%rdi), %r13
    movq 7*8(%rdi), %r14
    movq 8*8(%rdi), %rdx
    movq 9*8(%rdi), %r10
    movq 10*8(%rdi), %r8
    movq 11*8(%rdi), %r9
    movq 12*8(%rdi), %r15
    movq 18*8(%rdi), %r11
    movq 19*8(%rdi), %rcx
    movq 8(%rsp), %rdi
    testq %rdi, %rdi
    jz 2f
    movq %rdi, %cr3
2:
    popq %rdi
    addq $8, %rsp
    fl4_clear_buffers
    iretq

3:  /* SYSRET path. The frame on the kernel stack: user rsp, cr3, rdi. */
    pushq 16*8(%rdi)
    pushq %rdx
    pushq 0*8(%rdi)
    movq 1*8(%rdi), %rsi
    movq 2*8(%rdi), %rax
    movq 3*8(%rdi), %rbx
    movq 4*8(%rdi), %rbp
    movq 5*8(%rdi), %r12
    movq 6*8(%rdi), %r13
    movq 7*8(%rdi), %r14
    movq 8*8(%rdi), %rdx
    movq 9*8(%rdi), %r10
    movq 10*8(%rdi), %r8
    movq 11*8(%rdi), %r9
    movq 12*8(%rdi), %r15
    movq 13*8(%rdi), %r11
    movq 14*8(%rdi), %rcx
    movq 8(%rsp), %rdi
    testq %rdi, %rdi
    jz 4f
    movq %rdi, %cr3
4:
    /* AMD's SYSRET loads the SS selector but keeps the hidden attributes,
     * which are unusable after an interrupt from user mode (SS = 0): give
     * SS a valid descriptor first, as Linux does. */
    movl $0x18, %edi
    movl %edi, %ss
    popq %rdi
    addq $8, %rsp
    popq %rsp
    fl4_clear_buffers
    sysretq

/* fl4_idle(stack_top: u64) -> !: the idle thread. Interrupts arrive in
 * kernel mode on this stack and never return here. */
    .align 16
    .global fl4_idle
fl4_idle:
    movq %rdi, %rsp
1:
    fl4_clear_buffers
    sti
    hlt
    cli
    jmp 1b
