/* FL4 x86_64 boot entry. Multiboot 1 (QEMU -kernel) and Multiboot 2 (GRUB)
 * both enter here in 32-bit protected mode with paging off, EAX holding the
 * loader's magic and EBX the physical address of its info structure. We map
 * the first 4 GiB three times (identity, the kernel window at
 * 0xffffff8000000000 and the image at 0xffffffff80000000) with 2 MiB pages,
 * enter long mode, and call fl4_boot in the high half. The Rust boot code
 * replaces these tables with the real kernel address space. */


    .section .multiboot, "a"
    .align 4
mb1_header:
    .long 0x1BADB002
    .long 0x00000003          /* page-align modules, want memory info */
    .long -(0x1BADB002 + 0x00000003)

    .align 8
mb2_header:
    .long 0xE85250D6
    .long 0
    .long mb2_header_end - mb2_header
    .long -(0xE85250D6 + (mb2_header_end - mb2_header))
    /* Framebuffer request, optional, no preferred size (l4h 0011). */
    .align 8
    .short 5
    .short 1
    .long 20
    .long 0
    .long 0
    .long 0
    .align 8
    .short 0
    .short 0
    .long 8
mb2_header_end:

    .section .boot.text, "ax"
    .code32
    .global _start
_start:
    cli
    cld
    movl %eax, %edi
    movl %ebx, %esi
    movl $boot_stack32_top, %esp

    /* SEV encrypts memory accesses with paging off. Keep that view of
     * RAM when paging comes on. A CPU advertising SEV can also be running
     * an ordinary guest: only SEV_STATUS[0] enables the C-bit. */
    xorl %ebp, %ebp
    movl $0x80000000, %eax
    cpuid
    cmpl $0x8000001f, %eax
    jb .Lboot_tables
    movl $0x8000001f, %eax
    cpuid
    testl $2, %eax
    jz .Lboot_tables
    movl $0xc0010131, %ecx
    rdmsr
    testl $1, %eax
    jz .Lboot_tables
    testl $6, %eax             /* ES/SNP require a different entry protocol */
    jnz .Lunsupported
    andl $63, %ebx
    cmpl $32, %ebx             /* high doubleword of a 52-bit PTE address */
    jb .Lunsupported
    cmpl $51, %ebx
    ja .Lunsupported
    movb %bl, %cl
    btsl %ecx, %ebp            /* register bit index is modulo 32 */
.Lboot_tables:
    /* 2048 2 MiB pages covering 0..4 GiB in four page directories. */
    movl $boot_pd, %ebx
    xorl %ecx, %ecx
.Lpd_loop:
    movl %ecx, %eax
    shll $21, %eax
    orl $0x83, %eax
    movl %eax, (%ebx, %ecx, 8)
    movl %ebp, 4(%ebx, %ecx, 8)
    incl %ecx
    cmpl $2048, %ecx
    jne .Lpd_loop

    xorl %ecx, %ecx
.Lpdpt_loop:
    movl %ecx, %eax
    shll $12, %eax
    addl $boot_pd, %eax
    orl $0x3, %eax
    movl %eax, boot_pdpt_low(, %ecx, 8)
    movl %eax, boot_pdpt_high(, %ecx, 8)
    incl %ecx
    cmpl $4, %ecx
    jne .Lpdpt_loop
    movl $(boot_pd + 0x3), %eax
    movl %eax, boot_pdpt_high + 510 * 8
    movl $(boot_pd + 0x1000 + 0x3), %eax
    movl %eax, boot_pdpt_high + 511 * 8
    movl $(boot_pdpt_low + 0x3), %eax
    movl %eax, boot_pml4
    movl $(boot_pdpt_high + 0x3), %eax
    movl %eax, boot_pml4 + 511 * 8

    movl %cr4, %eax
    orl $(1 << 5), %eax       /* PAE */
    movl %eax, %cr4
    movl $boot_pml4, %eax
    movl %eax, %cr3
    movl $0xC0000080, %ecx    /* EFER.LME */
    rdmsr
    orl $(1 << 8), %eax
    wrmsr
    movl %cr0, %eax
    orl $((1 << 31) | (1 << 16) | 1), %eax   /* PG, WP, PE */
    movl %eax, %cr0
    lgdt boot_gdt_ptr
    ljmp $0x08, $long_entry

.Lunsupported:
    hlt
    jmp .Lunsupported

    .code64
long_entry:
    movw $0x10, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %ss
    xorw %ax, %ax
    movw %ax, %fs
    movw %ax, %gs
    movl %edi, %edi
    movl %esi, %esi
    movabsq $boot_stack_top, %rsp
    movl %ebp, %edx
    shlq $32, %rdx
    xorl %ebp, %ebp
    movabsq $fl4_boot, %rax
    call *%rax
.Lhalt:
    hlt
    jmp .Lhalt

    .section .boot.data, "aw"
    .align 16
boot_gdt:
    .quad 0
    .quad 0x00af9a000000ffff
    .quad 0x00cf92000000ffff
boot_gdt_end:
boot_gdt_ptr:
    .short boot_gdt_end - boot_gdt - 1
    .long boot_gdt

    .section .boot.bss, "aw", @nobits
    .align 4096
boot_pml4:      .skip 4096
boot_pdpt_low:  .skip 4096
boot_pdpt_high: .skip 4096
boot_pd:        .skip 4 * 4096
    .skip 4096
boot_stack32_top:

    .section .bss
    .align 4096
    .global boot_stack_top
boot_stack: .skip 65536
boot_stack_top:
