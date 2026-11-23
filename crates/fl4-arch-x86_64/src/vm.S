/* VM entry/exit on the kernel stack. Run's layout is asserted in vm.rs. */
.text
.macro save_host
    pushq %rbp
    pushq %rbx
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    pushq %rdi
.endm
.macro load_guest
    movq %rdi, %rax
    movq 8(%rax), %rbx
    movq 16(%rax), %rcx
    movq 24(%rax), %rdx
    movq 32(%rax), %rsi
    movq 48(%rax), %rbp
    movq 56(%rax), %r8
    movq 64(%rax), %r9
    movq 72(%rax), %r10
    movq 80(%rax), %r11
    movq 88(%rax), %r12
    movq 96(%rax), %r13
    movq 104(%rax), %r14
    movq 112(%rax), %r15
    movq 40(%rax), %rdi
.endm
.macro save_guest pointer_offset
    pushq %rax
    movq \pointer_offset(%rsp), %rax
    movq %rbx, 8(%rax)
    movq %rcx, 16(%rax)
    movq %rdx, 24(%rax)
    movq %rsi, 32(%rax)
    movq %rdi, 40(%rax)
    movq %rbp, 48(%rax)
    movq %r8, 56(%rax)
    movq %r9, 64(%rax)
    movq %r10, 72(%rax)
    movq %r11, 80(%rax)
    movq %r12, 88(%rax)
    movq %r13, 96(%rax)
    movq %r14, 104(%rax)
    movq %r15, 112(%rax)
.endm
.macro restore_host
    popq %rdi
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbx
    popq %rbp
    ret
.endm
/* restore_host, returning through the return thunk: Safe RET's when it is
 * on, which a return after a VM exit without IBPB needs (SRSO). */
.macro restore_host_thunk
    popq %rdi
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbx
    popq %rbp
    jmp __x86_return_thunk
.endm
.global fl4_vmx_run
fl4_vmx_run:
    save_host
    cmpq %rsp, 192(%rdi)
    je .Lhost_rsp_ready
    movq $0x6c14, %rcx
    vmwrite %rsp, %rcx
    movq %rsp, 192(%rdi)
.Lhost_rsp_ready:
    cmpq $0, 184(%rdi)
    /* MOV preserves the resume decision while loading the guest. */
    load_guest
    movq (%rax), %rax
    jne .Lvmresume
    fl4_clear_buffers
    vmlaunch
    jmp .Lentry_failed
.Lvmresume:
    fl4_clear_buffers
    vmresume
.Lentry_failed:
    pushq $1
    jmp 1f
.global fl4_vmx_exit
fl4_vmx_exit:
    pushq $0
1:
    save_guest 16
    popq %rcx
    movq %rcx, (%rax)
    popq %rcx
    movq %rcx, 176(%rax)
    movl 200(%rax), %r11d
    fl4_spec_barrier %r11d
    cld
    fl4_clear_guest_gprs
    restore_host

.global fl4_svm_run
fl4_svm_run:
    save_host
    clgi
    sti
    load_guest
    movq 128(%rax), %rax
    vmload %rax
    fl4_clear_buffers
    vmrun %rax
    cli
    vmsave %rax
    save_guest 8
    addq $8, %rsp
    movl 200(%rax), %r11d
    movq 136(%rax), %rax
    vmload %rax
    /* Restore host segment/MSR state first, then invalidate guest branch
     * predictions and, on Zen 2/3, overwrite the RAP. GIF stays clear
     * until after the barrier; no RET or indirect branch precedes it. */
    fl4_spec_barrier %r11d
    cld
    fl4_clear_guest_gprs
    /* Safe RET (SRSO): returns trained as at a native entry before the
     * first one, as Linux's UNTRAIN_RET_VM; the exit's IBPB, which also
     * covered them, may be deferred (spec::vm_ibpb_deferred). GIF is
     * clear: nothing interrupts the sequence. */
    cmpb $0, FL4_SAFE_RET(%rip)
    je 2f
    lfence
    call fl4_untrain_ret
2:
    lfence
    stgi
    restore_host_thunk
