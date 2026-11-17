/* Shared entry/exit primitives. The caller has saved all untrusted GPRs.
 * Each conditional mitigation ends at LFENCE before any RET/indirect
 * branch, including when the branch predicting whether to run it misses.
 * AMD boot code ensures LFENCE is dispatch-serializing.
 */
.ifndef FL4_SPEC_ASM
.set FL4_SPEC_ASM, 1
.macro fl4_spec_barrier flags:req
    testl ${spec_legacy}, \flags
    jz .Lno_legacy_\@
    movl $0x48, %ecx
    rdmsr
    orl $1, %eax
    /* Legacy IBRS requires a new write even if IBRS was already set. */
    wrmsr
.Lno_legacy_\@:
    lfence
    testl ${spec_ibpb}, \flags
    jz .Lno_ibpb_\@
    movl $0x49, %ecx
    movl $1, %eax
    xorl %edx, %edx
    wrmsr
.Lno_ibpb_\@:
    lfence
    /* Zen 2/3 IBPB does not clear the RAP. AMD APM vol. 2, 3.2.9:
     * 32 nonzero-displacement CALLs overwrite the untrusted entries.
     * All predicted destinations are traps; no architectural RET here. */
    testl ${spec_rsb}, \flags
    jz .Lno_rsb_\@
    movl $32, %ecx
.Lfill_rsb_\@:
    call .Lrsb_slot_\@
    int3
.Lrsb_slot_\@:
    leaq 8(%rsp), %rsp
    decl %ecx
    jnz .Lfill_rsb_\@
.Lno_rsb_\@:
    lfence
    /* PBRSB: force a CALL to retire before the first unbalanced RET. */
    testl ${spec_pbrsb}, \flags
    jz .Lno_pbrsb_\@
    call .Lpbrsb_slot_\@
    int3
.Lpbrsb_slot_\@:
    leaq 8(%rsp), %rsp
.Lno_pbrsb_\@:
    lfence
    /* Intel INTEL-SA-00598, long BHB-clearing sequence. This follows
     * return protection because it contains balanced CALL/RET pairs.
     * The long sequence covers newer physical hosts under nested VMMs. */
    testl ${spec_bhb}, \flags
    jz .Lbhb_done_\@
    movl $12, %ecx
    call .Lbhb_outer_\@
    jmp .Lbhb_done_\@
    .balign 64
.Lbhb_outer_\@:
    call .Lbhb_inner_\@
    ret
    .balign 64
.Lbhb_inner_\@:
    movl $7, %eax
.Lbhb_branch_\@:
    jmp .Lbhb_next_\@
    nop
.Lbhb_next_\@:
    decl %eax
    jnz .Lbhb_branch_\@
    decl %ecx
    jnz .Lbhb_outer_\@
    ret
.Lbhb_done_\@:
    lfence
    testl ${spec_ibhf}, \flags
    jz .Libhf_done_\@
    /* IBHF, a hint NOP without BHI_DIS_S support (Intel encoding). */
    .byte 0xf3, 0x48, 0x0f, 0x1e, 0xf8
.Libhf_done_\@:
    lfence
.endm

/* Memory-form VERW with a valid writable data selector; no GPR clobber.
 * Invoke after the last sensitive memory access and before guest/user
 * entry or idle. Only flags change (VM entry/IRET/SYSRET load new flags). */
.macro fl4_clear_buffers
    cmpl $0, FL4_SPEC_BUFFERS(%rip)
    je .Lbuffers_done_\@
    verw .Lfl4_clear_selector(%rip)
.Lbuffers_done_\@:
    lfence
.endm

.macro fl4_clear_guest_gprs
    xorl %eax, %eax
    xorl %ebx, %ebx
    xorl %ecx, %ecx
    xorl %edx, %edx
    xorl %esi, %esi
    xorl %edi, %edi
    xorl %ebp, %ebp
    xorl %r8d, %r8d
    xorl %r9d, %r9d
    xorl %r10d, %r10d
    xorl %r11d, %r11d
    xorl %r12d, %r12d
    xorl %r13d, %r13d
    xorl %r14d, %r14d
    xorl %r15d, %r15d
.endm

.pushsection .rodata
.balign 2
.Lfl4_clear_selector:
    .word 0x18
.popsection
.endif
