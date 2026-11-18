/* FL4 x86_64 kernel entry and exit.
 *
 * Every entry builds the same frame and calls fl4_entry (entry.rs). From
 * low to high addresses:
 *   r15 r14 r13 r12 r11 r10 r9 r8 rbp rdi rsi rdx rcx rbx rax
 *   vector error rip cs rflags rsp ss
 * Exceptions and interrupts get the hardware part from the CPU (with a
 * zero error code pushed for vectors without one); SYSCALL builds it by
 * hand, with vector 0x100.
 *
 * Entries from user mode arrive on the core's entry stack (TSS.RSP0, and
 * SYSCALL's through KERNEL_GS_BASE) or, for NMI, #DB, #MC and #DF, on an
 * IST stack, all in the core's entry area (gdt.rs SkimCpu), which the skim
 * window maps into user address spaces. fl4_common_entry switches to the
 * kernel's tables, moves the frame to the core's kernel stack (KSTACKS,
 * which user address spaces never map), clearing it where it was, and runs
 * fl4_entry there. Entries from kernel mode run fl4_entry where they
 * arrived. fl4_entry returns (with the CR3 value to leave on, or 0) only
 * for an entry it answers without a kernel entry proper; every other entry
 * leaves through fl4_restore_user or fl4_idle.
 *
 * Any entry may arrive on the user's tables, even from kernel mode (an NMI
 * or #DB in the trampolines here), so every entry switches CR3 itself and
 * restores the interrupted CR3 when it returns to kernel mode.
 *
 * The kernel never uses GS: the user GS base stays live in GS_BASE, and
 * KERNEL_GS_BASE points at the core's gs_block (gdt.rs): entry stack top,
 * a scratch word, kernel stack top. SYSCALL swaps GS only long enough to
 * find the stack. */

    .section .skim.text, "ax", @progbits
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
    jmp fl4_vector_entry
    .set vecnum, vecnum + 1
    .endr

    /* Interrupt and trap gates leave RFLAGS.AC as the interrupted code had
     * it, and user code may set it (POPFQ): with AC set SMAP stops nothing
     * for the whole entry, nor in the idle loop or around VMRUN, which
     * keeps the host's RFLAGS. Start from RFLAGS = 2 (AC, DF, TF, NT and
     * IF clear; IF is clear already). An entry from kernel mode gets its
     * RFLAGS back from the frame. SYSCALL clears them through FMASK. */
    .align 16
    .global fl4_vector_entry
fl4_vector_entry:
    pushq $2
    popfq
    jmp fl4_common_entry

    .align 16
    .global fl4_syscall_entry
fl4_syscall_entry:
    swapgs
    lfence
    movq %rsp, %gs:8
    movq %gs:0, %rsp
    pushq $0x2b
    pushq %gs:8
    movq $0, %gs:8
    swapgs
    pushq %r11
    pushq $0x33
    pushq %rcx
    pushq $0
    pushq $0x100

    .global fl4_common_entry
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
    /* A wrong injection type can give an error-code vector a frame
     * without an error code. Reject an invalid CS before the common path
     * can mistake that malformed frame for a user entry and relocate it. */
    cmpw $0x10, 18*8(%rsp)
    je .Lframe_cs_ok
    cmpw $0x33, 18*8(%rsp)
    je .Lframe_cs_ok
    andq $-16, %rsp
    call fl4_bad_entry_frame
    ud2
.Lframe_cs_ok:
    cmpb $0, FL4_SNP_POISONED(%rip)
    jne .Lpoisoned
    movl FL4_SPEC_ENTRY(%rip), %r11d
    fl4_spec_barrier %r11d
    fl4_clear_guest_gprs
    movq %rsp, %rbp
    /* The kernel's tables, if not on them already. rbx keeps the CR3 to
     * go back to on a return to kernel mode: 0 for none; the user's, with
     * the no-flush bit if PCIDs are on (it names a nonzero PCID then). */
    movq FL4_KERNEL_CR3(%rip), %rax
    testq %rax, %rax
    jz .Lcr3_done
    movq %cr3, %rbx
    movq %rbx, %rcx
    xorq %rax, %rcx
    movabsq $0x000ffffffffff000, %rdx
    testq %rdx, %rcx
    jnz .Lcr3_user
    xorl %ebx, %ebx
    jmp .Lcr3_done
.Lcr3_user:
    testl $0xfff, %ebx
    jz .Lcr3_load
    btsq $63, %rbx
.Lcr3_load:
    movq %rax, %cr3
.Lcr3_done:
    /* From user mode: move the frame to the kernel stack. The entry area
     * holding this stack is size-aligned; its third word is the top of
     * the core's kernel stack. A fault of an IRET to user mode belongs to
     * the user (bad_iret.S) and goes the same way. */
    /* Validate the original hardware frame before bad-IRET fixup can
     * replace its saved RSP, or Rust can enter a returning IRQ path. */
    cmpq $0, FL4_SNP_CPUID_PAGE(%rip)
    je .Lcheck_user
    testb $3, 18*8(%rbp)
    jnz .Lfrom_user
    movq %rbp, %rdi
    call fl4_snp_kernel_entry_stack
    testq %rax, %rax
    jnz .Lmove_frame
.Lcheck_user:
    testb $3, 18*8(%rbp)
    jnz .Lfrom_user
    fl4_bad_iret .Lcommon_iret, .Lrestore_iret, .Lfrom_user
    jmp .Lon_stack
.Lfrom_user:
    movq %rbp, %rax
    andq $-{skim_cpu_size}, %rax
    movq 16(%rax), %rax
.Lmove_frame:
    leaq -22*8(%rax), %rdi
    xorl %ecx, %ecx
.Lcopy_in:
    movq (%rbp,%rcx,8), %rdx
    movq %rdx, (%rdi,%rcx,8)
    movq $0, (%rbp,%rcx,8)
    incl %ecx
    cmpl $22, %ecx
    jne .Lcopy_in
    movq %rdi, %rsp
.Lon_stack:
    lfence
    movq %rsp, %rdi
    call fl4_entry
    /* Back to the interrupted code. A frame that moved goes back where it
     * came from (the kernel stack copy is never mapped for user code). */
    cmpq %rsp, %rbp
    je .Lframe_back
    /* SNP's full kernel mapping lets IRET use the kernel-stack copy.
     * Returning from IST6 to userspace on IST6 would let a bad IRET
     * overwrite its own frame when #GP or #SS also lands there. */
    cmpq $0, FL4_SNP_CPUID_PAGE(%rip)
    je .Lcopy_back
    cmpq $0, FL4_KERNEL_CR3(%rip)
    je .Lframe_back
.Lcopy_back:
    xorl %ecx, %ecx
.Lcopy_out:
    movq (%rsp,%rcx,8), %rdx
    movq %rdx, (%rbp,%rcx,8)
    incl %ecx
    cmpl $22, %ecx
    jne .Lcopy_out
    movq %rbp, %rsp
.Lframe_back:
    testq %rax, %rax
    jnz .Lcr3_back
    movq %rbx, %rax
    testq %rax, %rax
    jz .Lcr3_kept
.Lcr3_back:
    movq %rax, %cr3
.Lcr3_kept:
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
    /* Leave none of the registers just restored in the entry area. */
    movq $0, -8(%rsp)
    movq $0, -16(%rsp)
    movq $0, -24(%rsp)
    movq $0, -32(%rsp)
    movq $0, -40(%rsp)
    movq $0, -48(%rsp)
    movq $0, -56(%rsp)
    movq $0, -64(%rsp)
    movq $0, -72(%rsp)
    movq $0, -80(%rsp)
    movq $0, -88(%rsp)
    movq $0, -96(%rsp)
    movq $0, -104(%rsp)
    movq $0, -112(%rsp)
    movq $0, -120(%rsp)
    movq $0, -128(%rsp)
    movq $0, -136(%rsp)
    fl4_clear_buffers
    cmpb $0, FL4_SNP_POISONED(%rip)
    jne .Lpoisoned
.Lcommon_iret:
    iretq

/* Once another SNP vCPU reports a fatal error, do not resume guests or
 * enter the normal kernel path. This code and flag are mapped everywhere. */
.Lpoisoned:
    cli
    hlt
    jmp .Lpoisoned

/* fl4_restore_user(regs: *const u64, stack_top: u64, cr3: u64) -> !
 * regs is a TCB's register array (fl4_core::layout::reg order); stack_top
 * is the core's entry stack top (gdt.rs). A nonzero cr3 (the skim window,
 * spec.rs) is loaded after the last read of the TCB, which the user's
 * tables do not map; the entry stack is in the skim window, which they
 * do. What earlier entries and exits left on the entry stack is cleared
 * first, so no other thread's registers stay there, and the CR3 value
 * kept there is cleared before the exit.
 *
 * A thread whose registers are still as SYSCALL left them leaves by
 * SYSRET (fl4_sysret_check, sysret.S); everything else by IRET. */
    .align 16
    .global fl4_restore_user
fl4_restore_user:
    movq %rsi, %rsp
    movq $-22, %rcx
.Lclear_entry:
    movq $0, (%rsi,%rcx,8)
    incq %rcx
    jnz .Lclear_entry
    fl4_sysret_check %rdi, %rcx, 1f
    jmp 3f
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
    movq $0, (%rsp)
    addq $8, %rsp
    fl4_clear_buffers
    cmpb $0, FL4_SNP_POISONED(%rip)
    jne .Lpoisoned
.Lrestore_iret:
    iretq

3:  /* SYSRET path. The frame on the entry stack: user rsp, cr3, rdi. */
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
    movq $0, (%rsp)
    addq $8, %rsp
    popq %rsp
    fl4_clear_buffers
    cmpb $0, FL4_SNP_POISONED(%rip)
    jne .Lpoisoned
    sysretq

/* fl4_idle(stack_top: u64) -> !: the idle thread, on the kernel stack and
 * the kernel's tables. SNP interrupts land on an IST and move here before
 * running the handler. A timer acknowledged early can resume this loop. */
    .align 16
    .global fl4_idle
fl4_idle:
    movq %rdi, %rsp
    .global fl4_idle_loop
fl4_idle_loop:
1:
    cmpb $0, FL4_SNP_POISONED(%rip)
    jne .Lpoisoned
    fl4_clear_buffers
    sti
    hlt
    cli
    jmp 1b
    .global fl4_idle_end
fl4_idle_end:

    .text
