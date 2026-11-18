/* FL4 x86_64 kernel image. The boot section is linked and loaded at its
 * physical address so the 32-bit multiboot entry can run before paging;
 * everything else is linked in the top 2 GiB and loaded right after it. */
OUTPUT_FORMAT(elf64-x86-64)
ENTRY(_start)

KERNEL_PHYS = 0x100000;
KERNEL_OFFSET = 0xffffffff80000000;

PHDRS {
    boot PT_LOAD FLAGS(7);
    text PT_LOAD FLAGS(5);
    rodata PT_LOAD FLAGS(4);
    data PT_LOAD FLAGS(6);
}

SECTIONS
{
    . = KERNEL_PHYS;
    .boot : {
        KEEP(*(.multiboot))
        *(.boot.text)
        *(.boot.data)
        . = ALIGN(4096);
        *(.boot.bss)
    } :boot

    . = ALIGN(4096);
    . += KERNEL_OFFSET;
    /* The skim window (spec.rs) maps only the skim parts into user
     * address spaces: the entry and exit code, the data it touches before
     * switching to the kernel's tables, and the per-core entry stacks and
     * descriptor tables. Each part starts and ends on a page boundary so
     * that nothing else shares its pages. (The skim part of .bss is
     * .bss.skim: LLVM leaves only sections named .bss* without contents.)
     * The boundary symbols are hidden, so that disassemblers name the
     * functions that start at them rather than the boundaries. */
    .text : AT(ADDR(.text) - KERNEL_OFFSET) {
        HIDDEN(__text_start = .);
        HIDDEN(__skim_text_start = .);
        *(.skim.text .skim.text.*)
        . = ALIGN(4096);
        HIDDEN(__skim_text_end = .);
        *(.text .text.*)
    } :text
    .efi.entry : AT(ADDR(.efi.entry) - KERNEL_OFFSET) {
        KEEP(*(.efi.entry))
        HIDDEN(__text_end = .);
    } :text
    . = ALIGN(4096);
    .rodata : AT(ADDR(.rodata) - KERNEL_OFFSET) {
        HIDDEN(__rodata_start = .);
        HIDDEN(__skim_rodata_start = .);
        *(.skim.rodata .skim.rodata.*)
        . = ALIGN(4096);
        HIDDEN(__skim_rodata_end = .);
        *(.rodata .rodata.*)
        HIDDEN(__rodata_end = .);
    } :rodata
    . = ALIGN(4096);
    .data : AT(ADDR(.data) - KERNEL_OFFSET) {
        HIDDEN(__data_start = .);
        *(.data .data.*)
    } :data
    .bss : AT(ADDR(.bss) - KERNEL_OFFSET) {
        __bss_start = .;
        . = ALIGN(4096);
        HIDDEN(__skim_bss_start = .);
        *(.bss.skim .bss.skim.*)
        . = ALIGN(4096);
        HIDDEN(__skim_bss_end = .);
        *(.bss .bss.*)
        *(COMMON)
        . = ALIGN(4096);
        __bss_end = .;
    } :data
    . = ALIGN(4096);
    __kernel_end = .;
    /DISCARD/ : { *(.eh_frame*) *(.note*) *(.comment) }
}
