//! The AArch64 boot protocol between FL4's UEFI loader (`fl4-efi`) and the
//! kernel. The loader puts the kernel image, its boot page tables and this
//! record in one physically contiguous "kernel region", 2 MiB aligned,
//! which the boot tables map both at its physical address and at
//! `KERNEL_VBASE`. It enters the kernel's `_start` at its physical address
//! with the MMU and caches off, at EL2 or EL1, with x0 the record's offset
//! in the region.
#![no_std]

pub mod elf;

/// Where the kernel region is mapped (in TTBR1 L0[510], leaving L0[511]
/// exclusively for `ArmHighVSpace` so KERNEL_TTBR1.L0[511] stays invalid).
pub const KERNEL_VBASE: u64 = 0xffff_ff7f_8000_0000;
/// The kernel region ends at or below this address, the start of TTBR1
/// level-0 entry 511 (`ArmHighVSpace`s'): 2 GiB from `KERNEL_VBASE`.
pub const KERNEL_REGION_TOP: u64 = 0xffff_ff80_0000_0000;
const _: () = assert!(KERNEL_VBASE < KERNEL_REGION_TOP && (KERNEL_VBASE >> 39) & 511 == 510 && (KERNEL_REGION_TOP >> 39) & 511 == 511);

/// Whether a kernel region of `len` bytes at `KERNEL_VBASE` is not empty and
/// ends at or below `KERNEL_REGION_TOP`.
pub fn kernel_region_fits(len: u64) -> bool {
    len > 0 && KERNEL_VBASE.checked_add(len).is_some_and(|end| end <= KERNEL_REGION_TOP)
}

/// Where the loader puts things in the kernel region for an image of
/// `image_len` bytes, then `tables_len` bytes of boot tables, then a boot
/// record of `bi_size` bytes (rounded up to `page`), the whole rounded up
/// to `align` (powers of two): the tables' and the record's offsets and the
/// region's length; None if any of it wraps or the region does not fit
/// (`kernel_region_fits`).
pub fn kernel_region_layout(image_len: u64, tables_len: u64, bi_size: u64, page: u64, align: u64) -> Option<(u64, u64, u64)> {
    let tables_off = image_len;
    let bi_off = tables_off.checked_add(tables_len)?;
    let bi_len = bi_size.checked_add(page - 1)? & !(page - 1);
    let region_len = bi_off.checked_add(bi_len)?.checked_add(align - 1)? & !(align - 1);
    kernel_region_fits(region_len).then_some((tables_off, bi_off, region_len))
}
pub const MAGIC: u64 = 0x464c_345f_424f_4f54; // "FL4_BOOT"
pub const VERSION: u64 = 2;

/// Everything the loader allocates (the kernel region, the root task, the
/// boot modules) lies below this physical address: the reach of the
/// kernel's window over RAM (`fl4_core::layout::PADDR_TOP` on AArch64).
pub const LOAD_TOP: u64 = 0x0000_7f00_0000_0000;
/// The end of user space (`fl4_abi::consts::USER_TOP` + 1): the root task's
/// segments end at or below it.
pub const USER_END: u64 = 0x0000_8000_0000_0000;

/// The boot frames fl4-core maps right after the root task's image
/// (`boot::root_layout`): its IPC buffer and BootInfo frame, then the
/// extra BootInfo. That is never empty on AArch64 (the ID registers), so
/// the image ends at least this far below `USER_END`.
pub const ROOT_TAIL_MIN: u64 = 3 * 4096;

/// Whether the boot frames after a root task image ending at virtual
/// `v_end` fit below `USER_END`, with `extra_len` bytes of extra BootInfo,
/// fl4-core's extra-untyped room (`boot::extra_ut_reserve`) included
/// (mapped as fl4-core does: rounded up to a power of two of at least a
/// page, `boot::extra_bi_size_bits`). Past it they would be mapped, and
/// given out as caps, at addresses user space must not have.
pub fn root_tail_fits(v_end: u64, extra_len: u64) -> bool {
    let extra = if extra_len == 0 {
        Some(0)
    } else {
        extra_len.checked_add(4095).map(|l| l & !4095).and_then(u64::checked_next_power_of_two)
    };
    extra
        .and_then(|e| v_end.checked_add(2 * 4096)?.checked_add(e))
        .is_some_and(|end| end <= USER_END)
}

pub const MAX_MMAP: usize = 256;
pub const MAX_MODULES: usize = 8;
pub const CMDLINE_LEN: usize = 256;
pub const NAME_LEN: usize = 64;

/// Where a word of `word_len` bytes goes on a kernel command line now
/// `len` bytes long (after a space separating it from the words before),
/// leaving room for the closing NUL; None when it does not fit. The loader
/// fails rather than drop a word (`warm_its`, `novirt` would silently not
/// apply).
pub fn cmdline_room(len: usize, word_len: usize) -> Option<usize> {
    let at = len + usize::from(len > 0);
    (word_len < CMDLINE_LEN && at.checked_add(word_len)? < CMDLINE_LEN).then_some(at)
}

/// Whether the kernel command line `cmdline` (NUL-terminated, or full) has
/// the word `opt`.
pub fn has_option(cmdline: &[u8; CMDLINE_LEN], opt: &[u8]) -> bool {
    let n = cmdline.iter().position(|&c| c == 0).unwrap_or(CMDLINE_LEN);
    cmdline[..n].split(|&c| c == b' ').any(|w| w == opt)
}

/// Memory map entry kinds (from the UEFI memory types).
pub mod mem {
    /// Free after ExitBootServices: conventional, loader and boot
    /// services memory (minus what the record names).
    pub const FREE: u32 = 1;
    /// Firmware memory with RAM behind it that must stay: runtime
    /// services, ACPI tables and NVS, persistent memory.
    pub const FIRMWARE: u32 = 2;
    /// Anything else: reserved, unusable, MMIO.
    pub const OTHER: u32 = 3;
    /// Bit in `MemRegion::cacheable` (alongside bit 0 = write-back RAM):
    /// every byte of this `FREE` region outside the kernel region, root
    /// task, boot modules, device tree and TPM event log is already zero
    /// (for example, freshly mapped anonymous VMM memory the loader never
    /// wrote to), so boot need not read every page before creating untypeds.
    pub const ZEROED: u32 = 1 << 1;
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct MemRegion {
    pub base: u64,
    pub len: u64,
    pub kind: u32,
    /// Bit 0 (`1`): ordinary write-back cacheable RAM (`EFI_MEMORY_WB`).
    /// Bit 1 (`mem::ZEROED`): untouched bytes of this `FREE` region are
    /// already zero.
    pub cacheable: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Module {
    pub paddr: u64,
    pub size: u64,
    pub name: [u8; NAME_LEN],
}

impl Default for Module {
    fn default() -> Self {
        Module { paddr: 0, size: 0, name: [0; NAME_LEN] }
    }
}

/// The root task, loaded by the loader: its segments occupy
/// [p_start, p_end), mapped at p - pv_offset.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct RootTask {
    pub p_start: u64,
    pub p_end: u64,
    pub v_start: u64,
    pub entry: u64,
}

#[repr(C)]
pub struct BootInfo {
    pub magic: u64,
    pub version: u64,
    /// The kernel region: physical base and length.
    pub region_paddr: u64,
    pub region_len: u64,
    /// Boot page tables (in the region): TTBR0 identity, TTBR1 high.
    pub ttbr0: u64,
    pub ttbr1: u64,
    /// ACPI RSDP and device tree blob (physical; 0 if none).
    pub rsdp: u64,
    pub dtb: u64,
    pub dtb_len: u64,
    pub root: RootTask,
    /// Further boot modules (l4h 0021), as the loader read them.
    pub n_modules: u64,
    pub modules: [Module; MAX_MODULES],
    pub n_mmap: u64,
    pub mmap: [MemRegion; MAX_MMAP],
    /// NUL-terminated kernel command line.
    pub cmdline: [u8; CMDLINE_LEN],
    /// The UEFI TPM event log the loader copied (version 2): its physical
    /// address (page aligned, 0 if none), exact length (at most
    /// `MAX_TPM_LOG`) and flags (fl4_abi `tpm_event_log_flag`).
    pub tpm_log_paddr: u64,
    pub tpm_log_size: u64,
    pub tpm_log_flags: u64,
}

/// The longest TPM event log the loader passes on (fl4-efi tcg2.rs
/// `MAX_EVENT_LOG`).
pub const MAX_TPM_LOG: u64 = 1 << 20;

/// Where a flattened device tree's blocks are, from its 40-byte header
/// (offsets from the blob's start, all inside its total size).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fdt {
    pub total: u64,
    pub structs: (u64, u64),
    pub strings: (u64, u64),
    pub rsv: u64,
}

/// The device tree header `h` (big-endian), if it is one whose blocks lie
/// inside the blob: firmware's word, but the kernel walks it before
/// anything else can check it.
pub fn fdt_header(h: &[u8; 40]) -> Option<Fdt> {
    let be = |o: usize| u32::from_be_bytes([h[o], h[o + 1], h[o + 2], h[o + 3]]) as u64;
    if be(0) != 0xd00d_feed {
        return None;
    }
    let total = be(4);
    let block = |off: u64, size: u64| (off >= 40 && size <= total && off <= total - size).then_some((off, off + size));
    let structs = block(be(8), be(36))?;
    let strings = block(be(12), be(32))?;
    let rsv = be(16);
    if rsv < 40 || rsv > total {
        return None;
    }
    Some(Fdt { total, structs, strings, rsv })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_kernel_region_stays_below_the_high_window() {
        const MB2: u64 = 2 << 20;
        let room = KERNEL_REGION_TOP - KERNEL_VBASE;
        assert_eq!(room, 2 << 30);
        assert!(kernel_region_fits(room));
        assert!(kernel_region_fits(0x1000));
        assert!(!kernel_region_fits(room + 1));
        assert!(!kernel_region_fits(room + 0x1000));
        assert!(!kernel_region_fits(0));
        assert!(!kernel_region_fits(u64::MAX));
        assert!(!kernel_region_fits(u64::MAX - KERNEL_VBASE + 1));
        // An ordinary image: tables and the record after it, 2 MiB rounded.
        assert_eq!(kernel_region_layout(0x30_0000, 0xa000, 0x1800, 0x1000, MB2), Some((0x30_0000, 0x30_a000, 0x40_0000)));
        // Exactly to the boundary, and a tail one page past it.
        let image = room - 0xa000 - 0x1000;
        assert_eq!(kernel_region_layout(image, 0xa000, 0x1000, 0x1000, MB2), Some((image, image + 0xa000, room)));
        assert_eq!(kernel_region_layout(image + 0x1000, 0xa000, 0x1000, 0x1000, MB2), None);
        // The record's page rounding takes it past.
        assert_eq!(kernel_region_layout(image, 0xa000, 0x1001, 0x1000, MB2), None);
        // Additions that wrap.
        assert_eq!(kernel_region_layout(u64::MAX - 0x1000, 0xa000, 0x1000, 0x1000, MB2), None);
        assert_eq!(kernel_region_layout(0, u64::MAX, 0x1000, 0x1000, MB2), None);
        assert_eq!(kernel_region_layout(0, 0, u64::MAX, 0x1000, MB2), None);
        assert_eq!(kernel_region_layout(u64::MAX - MB2 - 0x2000, 0x1000, 0x1000, 0x1000, MB2), None);
    }

    #[test]
    fn root_task_boot_frames_stay_in_user_space() {
        // IPC buffer, BootInfo, one page of extra BootInfo: exactly up to
        // the end, and not a page further.
        assert!(root_tail_fits(USER_END - 3 * 4096, 1));
        assert!(root_tail_fits(USER_END - 3 * 4096, 4096));
        assert!(!root_tail_fits(USER_END - 2 * 4096, 4096));
        // fl4-core maps 5 pages of extra BootInfo as 8.
        assert!(!root_tail_fits(USER_END - 7 * 4096, 5 * 4096));
        assert!(root_tail_fits(USER_END - 10 * 4096, 5 * 4096));
        assert!(root_tail_fits(USER_END - 2 * 4096, 0));
        // No wrapping past 2^64.
        assert!(!root_tail_fits(u64::MAX - 4096, 4096));
        assert!(!root_tail_fits(0x1000, u64::MAX));
    }

    fn header(total: u32, off_struct: u32, size_struct: u32, off_strings: u32, size_strings: u32) -> [u8; 40] {
        let mut h = [0u8; 40];
        for (o, v) in [(0, 0xd00d_feed), (4, total), (8, off_struct), (12, off_strings), (16, 40), (32, size_strings), (36, size_struct)] {
            h[o..o + 4].copy_from_slice(&u32::to_be_bytes(v));
        }
        h
    }

    #[test]
    fn device_tree_blocks_must_lie_inside_the_blob() {
        assert_eq!(
            fdt_header(&header(0x1000, 0x100, 0x800, 0x900, 0x100)),
            Some(Fdt { total: 0x1000, structs: (0x100, 0x900), strings: (0x900, 0xa00), rsv: 40 })
        );
        // Blocks past the end, overlapping the header, or wrapping.
        assert_eq!(fdt_header(&header(0x1000, 0x100, 0xf01, 0x900, 0x100)), None);
        assert_eq!(fdt_header(&header(0x1000, 0x100, 0x800, 0xf80, 0x100)), None);
        assert_eq!(fdt_header(&header(0x1000, 0x10, 0x800, 0x900, 0x100)), None);
        assert_eq!(fdt_header(&header(0x1000, u32::MAX, 2, 0x900, 0x100)), None);
        assert_eq!(fdt_header(&header(0x20, 0x28, 0, 0x28, 0)), None);
        let mut h = header(0x1000, 0x100, 0x800, 0x900, 0x100);
        h[0] = 0;
        assert_eq!(fdt_header(&h), None);
    }
}
