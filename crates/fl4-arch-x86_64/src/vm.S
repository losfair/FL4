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
.global fl4_vmx_run
fl4_vmx_run:
    save_host
    movq $0x6c14, %rcx
    vmwrite %rsp, %rcx
    leaq fl4_vmx_exit(%rip), %rdx
    movq $0x6c16, %rcx
    vmwrite %rdx, %rcx
    load_guest
    movq (%rax), %rax
    vmlaunch
    pushq $1
    jmp 1f
fl4_vmx_exit:
    pushq $0
1:
    save_guest 16
    popq %rcx
    movq %rcx, (%rax)
    popq %rcx
    movq %rcx, 176(%rax)
    cld
    restore_host

.global fl4_svm_run
fl4_svm_run:
    save_host
    clgi
    sti
    load_guest
    movq 128(%rax), %rax
    vmload %rax
    vmrun %rax
    cli
    vmsave %rax
    save_guest 8
    addq $8, %rsp
    movq 136(%rax), %rax
    vmload %rax
    cld
    stgi
    restore_host
