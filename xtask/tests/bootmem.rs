//! The kernel's boot-time RAM and device memory carving (fl4-kernel
//! bootmem.rs), with fl4-core's `Region` replaced by an identical type.
extern crate self as fl4_core;

pub mod boot {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Region {
        pub start: u64,
        pub end: u64,
    }
    impl Region {
        pub const EMPTY: Region = Region { start: 0, end: 0 };
    }
}

#[path = "../../crates/fl4-kernel/src/bootmem.rs"]
mod bootmem;

use bootmem::Ranges;
use boot::Region;

const MIB: u64 = 1 << 20;
const TOP: u64 = 1 << 47;
const KERNEL: u64 = MIB;

fn list(r: &Ranges) -> Vec<(u64, u64)> {
    r.r[..r.n].iter().map(|x| (x.start, x.end)).collect()
}

fn overlaps(r: &Ranges, start: u64, end: u64) -> bool {
    r.r[..r.n].iter().any(|x: &Region| x.start < end && start < x.end)
}

#[test]
fn ram_that_starts_in_low_memory_counts_from_1_mib() {
    // One available entry from 0 used to be dropped whole.
    let ram = bootmem::ram([(0, 0x8000_0000, 1)], MIB, 1 << 40);
    assert_eq!(list(&ram), [(MIB, 0x8000_0000)]);
}

#[test]
fn ram_takes_whole_pages_below_the_top_and_never_wraps() {
    let ram = bootmem::ram(
        [(0x20_0001, 0x2000, 1), (0x40_0000, 0x10_0000, 2), (u64::MAX - 0x800, 0x1000, 1), (0x1_0000_0000, u64::MAX, 1)],
        MIB,
        0x2_0000_0000,
    );
    assert_eq!(list(&ram), [(0x20_1000, 0x20_2000), (0x1_0000_0000, 0x2_0000_0000)]);
}

#[test]
fn the_kernel_and_root_task_are_never_device_memory() {
    // The loader reports its own allocations (kernel, modules) as reserved
    // (UEFI GRUB), so the RAM list misses them.
    let image_end = 0x80_0000;
    let ram = bootmem::ram([(image_end, 0x1000_0000, 1)], MIB, 1 << 40);
    let dev = bootmem::device(&ram, TOP, [(KERNEL, image_end), (0xfee0_0000, 0xfee0_1000)]);
    assert!(!overlaps(&dev, KERNEL, image_end));
    assert!(!overlaps(&dev, image_end, image_end + 0x1000_0000));
    assert!(!overlaps(&dev, 0xfee0_0000, 0xfee0_1000));
    // Low memory and everything else stays device memory.
    assert!(overlaps(&dev, 0, KERNEL));
    assert!(overlaps(&dev, 0xfec0_0000, 0xfec0_1000));
}

#[test]
fn reserved_ranges_widen_to_whole_pages() {
    // An IOAPIC whose registers are not page aligned, or cross a page.
    let ram = Ranges::new();
    let dev = bootmem::device(&ram, TOP, [(0xfec0_0400, 0xfec0_0420), (0xfec0_1ff0, 0xfec0_2010)]);
    assert!(!overlaps(&dev, 0xfec0_0000, 0xfec0_3000));
    assert!(overlaps(&dev, 0xfebf_f000, 0xfec0_0000));
    assert!(overlaps(&dev, 0xfec0_3000, 0xfec0_4000));
}

#[test]
fn the_root_task_goes_to_ram_that_holds_it() {
    let mut ram = Ranges::new();
    ram.add(MIB, 0x9f_0000);
    ram.add(0x100_0000, 0x200_0000);
    // Above the modules, page aligned.
    assert_eq!(ram.find(0x80_0001, 0x1000), Some(0x80_1000));
    // Not across the hole: the next region that fits.
    assert_eq!(ram.find(0x90_0000, 0x10_0000), Some(0x100_0000));
    assert_eq!(ram.find(0x90_0000, 0x200_0000), None);
    assert_eq!(ram.find(u64::MAX - 10, 1), None);
    assert!(ram.contains(0x100_0000, 0x200_0000));
    assert!(!ram.contains(0x9f_0000, 0xa0_0000));
}

/// fl4-core `layout`: the kernel window is [PPTR_BASE, PPTR_TOP), and
/// physical address `p` is at `PPTR_BASE + p` (wrapping).
const PPTR_BASE: u64 = 0xffff_ff80_0000_0000;
const PPTR_TOP: u64 = 0xffff_ffff_8000_0000;
const PADDR_TOP: u64 = PPTR_TOP - PPTR_BASE;
const MAX_UNTYPED: u64 = 47;
const MIN_UNTYPED: u64 = 4;

/// The device untypeds fl4-core `boot::create_untypeds_for_region` makes
/// of `[start, end)` (same split: the largest block at `start` aligned as
/// its pointer): `(ptr, size_bits)`.
fn device_untypeds(start: u64, end: u64) -> Vec<(u64, u64)> {
    let mut out = Vec::new();
    let mut start = start;
    let mut fuel = 128;
    while start < end && fuel > 0 {
        fuel -= 1;
        let mut size_bits = 63u64.wrapping_sub((end - start).leading_zeros() as u64) & 63;
        size_bits = size_bits.min(MAX_UNTYPED);
        let at = start.wrapping_add(PPTR_BASE);
        if at != 0 {
            size_bits = size_bits.min(at.trailing_zeros() as u64);
        }
        if size_bits >= MIN_UNTYPED {
            out.push((at, size_bits));
        }
        start = start.wrapping_add(1 << size_bits);
    }
    out
}

/// What fl4_boot gives user space as device memory, with memory below
/// 4 GiB and at 64 GiB..72 GiB as RAM, for a CPU of `max_paddr`.
fn boot_devices(max_paddr: u64) -> Ranges {
    let ram = bootmem::ram([(MIB, 0x7ff0_0000, 1), (0x10_0000_0000, 0x2_0000_0000, 1)], MIB, bootmem::top(&[PADDR_TOP, PADDR_TOP, max_paddr]));
    bootmem::device(&ram, bootmem::top(&[PADDR_TOP, TOP, max_paddr]), [(KERNEL, 4 * MIB)])
}

#[test]
fn boot_memory_stops_at_the_lowest_limit() {
    assert_eq!(bootmem::top(&[PADDR_TOP, TOP, 1 << 39]), PADDR_TOP);
    assert_eq!(bootmem::top(&[PADDR_TOP, TOP, 1 << 36]), 1 << 36);
    assert_eq!(bootmem::top(&[PADDR_TOP, 16 << 30, 1 << 46]), 16 << 30);
}

/// With 2^47 as the device top (seL4's CONFIG_PADDR_USER_DEVICE_TOP for a
/// 128 TiB window) FL4's 510 GiB window gave out untypeds over the kernel
/// image's mapping and, from 512 GiB on, pointers that wrapped to the
/// lower half. Every device untyped must lie in the window and below
/// MAXPHYADDR.
#[test]
fn device_untypeds_stay_in_the_kernel_window_and_below_maxphyaddr() {
    let old = device_untypeds(1 << 39, TOP);
    assert!(old.iter().any(|&(ptr, _)| ptr < PPTR_BASE), "the old top wrapped");
    for bits in [36u64, 39, 40, 46, 48, 52] {
        let max_paddr = 1u64 << bits;
        let dev = boot_devices(max_paddr);
        assert!(dev.n > 0);
        for r in &dev.r[..dev.n] {
            assert!(r.end <= PADDR_TOP.min(max_paddr), "{bits}: {:#x}..{:#x}", r.start, r.end);
            for (ptr, size_bits) in device_untypeds(r.start, r.end) {
                let end = ptr as u128 + (1u128 << size_bits);
                assert!(PPTR_BASE <= ptr && end <= PPTR_TOP as u128, "{bits}: {ptr:#x}/{size_bits}");
                assert!(ptr - PPTR_BASE + (1 << size_bits) <= max_paddr);
                assert_eq!(ptr % (1 << size_bits), 0);
            }
        }
    }
}

#[test]
fn fragmented_firmware_keeps_visibility_boundaries_in_gpa_order() {
    let mut firmware = bootmem::RangeList::<129>::new();
    for i in (0..65).rev() { firmware.add((2*i+1)*4096, (2*i+2)*4096); }
    let dev = [Region { start: 0, end: 130*4096 }];
    let mut parts = Vec::new();
    bootmem::device_regions(&dev, &firmware.r[..firmware.n], |r, private| parts.push((r, private)));
    assert_eq!(parts.len(), 130);
    for (i, (r, private)) in parts.into_iter().enumerate() {
        assert_eq!(r, Region { start: i as u64*4096, end: (i as u64+1)*4096 });
        assert_eq!(private, i % 2 == 1);
    }
}
