//! The AArch64 boot protocol between FL4's UEFI loader (`fl4-efi`) and the
//! kernel. The loader puts the kernel image, its boot page tables and this
//! record in one physically contiguous "kernel region", 2 MiB aligned,
//! which the boot tables map both at its physical address and at
//! `KERNEL_VBASE`. It enters the kernel's `_start` at its physical address
//! with the MMU and caches off, at EL2 or EL1, with x0 the record's offset
//! in the region.
#![no_std]

pub mod elf;

/// Where the kernel region is mapped.
pub const KERNEL_VBASE: u64 = 0xffff_ffff_8000_0000;
pub const MAGIC: u64 = 0x464c_345f_424f_4f54; // "FL4_BOOT"
pub const VERSION: u64 = 1;

/// Everything the loader allocates (the kernel region, the root task, the
/// boot modules) lies below this physical address: the reach of the
/// kernel's window over RAM (`fl4_core::layout::PADDR_TOP` on AArch64).
pub const LOAD_TOP: u64 = 0x0000_7f80_0000_0000;
/// The end of user space (`fl4_abi::consts::USER_TOP` + 1): the root task's
/// segments end at or below it.
pub const USER_END: u64 = 0x0000_8000_0000_0000;

pub const MAX_MMAP: usize = 256;
pub const MAX_MODULES: usize = 8;
pub const CMDLINE_LEN: usize = 256;
pub const NAME_LEN: usize = 64;

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
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct MemRegion {
    pub base: u64,
    pub len: u64,
    pub kind: u32,
    /// The region is ordinary write-back cacheable RAM (EFI_MEMORY_WB).
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
}

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
