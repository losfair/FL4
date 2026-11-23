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
    bootmem::device(&ram, bootmem::top(&[TOP, max_paddr]), [(KERNEL, 4 * MIB)])
}

#[test]
fn boot_memory_stops_at_the_lowest_limit() {
    assert_eq!(bootmem::top(&[PADDR_TOP, TOP, 1 << 39]), PADDR_TOP);
    assert_eq!(bootmem::top(&[PADDR_TOP, TOP, 1 << 36]), 1 << 36);
    assert_eq!(bootmem::top(&[PADDR_TOP, 16 << 30, 1 << 46]), 16 << 30);
    assert_eq!(bootmem::top(&[TOP, 1 << 46]), 1 << 46);
    assert_eq!(bootmem::top(&[TOP, 1 << 52]), TOP);
}

/// Device memory reaches past FL4's 510 GiB window, up to seL4's
/// CONFIG_PADDR_USER_DEVICE_TOP (2^47) and MAXPHYADDR: firmware places
/// 64-bit BARs there (0x3800_0000_0000 with 46 address bits). A device
/// untyped's pointer is its physical address plus PPTR_BASE, wrapping:
/// in the window below 510 GiB, in the lower half from 512 GiB on. No
/// block wraps: one ends where the pointers do (512 GiB).
#[test]
fn device_untypeds_reach_high_bars() {
    for bits in [36u64, 39, 40, 46, 48, 52] {
        let max_paddr = 1u64 << bits;
        let top = TOP.min(max_paddr);
        let dev = boot_devices(max_paddr);
        assert!(dev.n > 0);
        // All of it up to the top, but for the image's alias.
        assert!(dev.contains(0x1_0000_0000, 0x10_0000_0000.min(top)), "{bits}");
        if top > 0x12_0000_0000 {
            assert!(dev.contains(0x12_0000_0000, top), "{bits}");
        }
        if bits >= 46 {
            assert!(dev.contains(0x3800_0000_0000, 0x3800_0000_8000), "{bits}: QEMU's 64-bit BARs");
        }
        let mut blocks = 0;
        for r in &dev.r[..dev.n] {
            assert!(r.end <= top, "{bits}: {:#x}..{:#x}", r.start, r.end);
            let mut at = r.start;
            for (ptr, size_bits) in device_untypeds(r.start, r.end) {
                blocks += 1;
                let size = 1u64 << size_bits;
                // The pointer is the block's physical address in the
                // window numbering, aligned, and the block does not wrap.
                assert_eq!(ptr.wrapping_sub(PPTR_BASE), at, "{bits}: {ptr:#x}/{size_bits}");
                assert_eq!(ptr % size, 0);
                let end = ptr as u128 + size as u128;
                if at < 1 << 39 {
                    assert!(PPTR_BASE <= ptr && end <= 1 << 64, "{bits}: {ptr:#x}/{size_bits}");
                } else {
                    // Lower half: canonical, as a capability stores 48 bits.
                    assert!(at >= 1 << 39 && end <= 1 << 47, "{bits}: {ptr:#x}/{size_bits}");
                }
                at += size;
            }
            // Whole pages: the blocks cover the range exactly.
            assert_eq!(at, r.end, "{bits}");
        }
        // Within the BootInfo's untyped list (230), with room for RAM.
        assert!(blocks < 100, "{bits}: {blocks} device untypeds");
    }
}

/// Audit F4: RAM that does not fit the list is reported (the kernel then
/// refuses to boot), not left out to become device memory.
#[test]
fn ram_past_the_list_is_reported_lost() {
    let entries: Vec<(u64, u64, u32)> = (0..256u64).map(|i| (MIB + i * 2 * MIB, MIB, 1)).collect();
    let ram = bootmem::ram(entries.iter().copied(), MIB, TOP);
    assert_eq!(ram.n, 256);
    assert!(!ram.lost);
    let mut full = Ranges::new();
    for i in 0..full.r.len() as u64 {
        full.add(i * 2 * MIB, i * 2 * MIB + MIB);
    }
    assert!(!full.lost);
    full.add(1 << 40, (1 << 40) + MIB);
    assert!(full.lost);
    assert!(!overlaps(&full, 1 << 40, (1 << 40) + MIB));
    // A split of a full list by `remove` too.
    let mut full = Ranges::new();
    for i in 0..full.r.len() as u64 {
        full.add(i * 4 * MIB, i * 4 * MIB + 3 * MIB);
    }
    full.remove(MIB, 2 * MIB);
    assert!(full.lost);
}

const UNACCEPTED: u32 = bootmem::UNACCEPTED;

/// Only unaccepted entries count, in whole pages, clipped to the window.
#[test]
fn unaccepted_ranges_are_whole_pages_inside_the_window() {
    let top = 4 << 30;
    let r = bootmem::unaccepted(
        [
            (0, 2 * MIB, UNACCEPTED),
            (16 * MIB, 16 * MIB, 1),
            (64 * MIB + 1, 8 * MIB, UNACCEPTED),
            (top - MIB, 4 * MIB, UNACCEPTED),
            (top + MIB, MIB, UNACCEPTED),
            (128 * MIB, MIB, 2),
        ],
        MIB,
        top,
    );
    assert_eq!(list(&r), [(MIB, 2 * MIB), (64 * MIB + 4096, 72 * MIB), (top - MIB, top)]);
    assert!(!r.lost);
}

/// Unaccepted memory the kernel did not accept stays out of RAM, and its
/// removal keeps it out of device memory, up to the device top.
#[test]
fn unaccepted_memory_past_the_window_is_no_device_memory() {
    let window = 4 << 30;
    let entries = [(0x10_0000, 16 * MIB, 1), (window - MIB, 8 * MIB, UNACCEPTED)];
    let ram = bootmem::ram(entries, MIB, window);
    assert_eq!(list(&ram), [(MIB, 17 * MIB)]);
    let mut dev = bootmem::device(&ram, TOP, []);
    assert!(overlaps(&dev, window - MIB, window + 7 * MIB), "the map alone leaves it in device memory");
    dev.remove(window - MIB, window + 7 * MIB);
    assert!(!overlaps(&dev, window - MIB, window + 7 * MIB));
}

fn region(start: u64, end: u64) -> Region {
    Region { start, end }
}

fn chunks(ranges: &[Region], chunk: u64) -> Vec<(u64, u64)> {
    (0..).map_while(|i| bootmem::chunk_of(ranges, i, chunk)).collect()
}

/// The pieces cores take are exactly the ranges, cut at chunk multiples.
#[test]
fn accept_chunks_partition_the_ranges() {
    let c = 64 * MIB;
    let ranges = [region(MIB, 3 * MIB), region(60 * MIB, 200 * MIB), region(256 * MIB, 320 * MIB)];
    assert_eq!(
        chunks(&ranges, c),
        [
            (MIB, 3 * MIB),
            (60 * MIB, 64 * MIB),
            (64 * MIB, 128 * MIB),
            (128 * MIB, 192 * MIB),
            (192 * MIB, 200 * MIB),
            (256 * MIB, 320 * MIB),
        ]
    );
    let total: u64 = chunks(&ranges, c).iter().map(|(s, e)| e - s).sum();
    assert_eq!(total, ranges.iter().map(|r| r.end - r.start).sum::<u64>());
    assert_eq!(bootmem::chunk_of(&ranges, 6, c), None);
    assert_eq!(bootmem::chunk_of(&ranges, u64::MAX, c), None);
    assert_eq!(bootmem::chunk_of(&[], 0, c), None);
    assert_eq!(chunks(&[region(5 * MIB, 5 * MIB), region(c, c + 1)], c), [(c, c + 1)]);
}

/// The MADT's mailbox address comes from the VMM: only a whole page of
/// firmware's reserved, ACPI reclaim or NVS memory, inside the window, is
/// used.
#[test]
fn the_wakeup_mailbox_must_be_a_firmware_page() {
    let top = 4 << 30;
    let map = [(0x10_0000, 16 * MIB, 1), (0x7f00_0000, 0x4000, 4), (0x7f80_0000, 0x1000, 2), (0x8000_0000, 0x1000, 3), (0x9000_0000, 0x4000, UNACCEPTED)];
    assert!(bootmem::mailbox_ok(0x7f00_0000, top, map));
    assert!(bootmem::mailbox_ok(0x7f00_3000, top, map));
    assert!(bootmem::mailbox_ok(0x7f80_0000, top, map));
    assert!(bootmem::mailbox_ok(0x8000_0000, top, map));
    for bad in [
        0,
        0x7f00_0800,                // off a page
        0x20_0000,                  // RAM
        0x9000_1000,                // unaccepted RAM
        0x7f00_4000,                // just past the entry
        0x7f7f_f000,                // in a hole
        u64::MAX & !0xfff,
    ] {
        assert!(!bootmem::mailbox_ok(bad, top, map), "{bad:#x}");
    }
    // Past the window the kernel cannot reach it.
    assert!(!bootmem::mailbox_ok(0x7f00_0000, 0x7f00_0000, map));
    assert!(bootmem::mailbox_ok(0x7f00_0000, 0x7f00_1000, map));
}

/// The count that lets idle cores stop taking pieces is exactly how many
/// there are.
#[test]
fn the_chunk_count_is_the_number_of_pieces() {
    let c = 64 * MIB;
    for ranges in [
        vec![],
        vec![region(5 * MIB, 5 * MIB)],
        vec![region(MIB, 3 * MIB)],
        vec![region(0, c)],
        vec![region(c - 1, c + 1)],
        vec![region(MIB, 3 * MIB), region(60 * MIB, 200 * MIB), region(256 * MIB, 320 * MIB)],
    ] {
        let n = bootmem::chunk_count(&ranges, c);
        assert_eq!(n, chunks(&ranges, c).len() as u64, "{ranges:?}");
        assert_eq!(bootmem::chunk_of(&ranges, n, c), None);
    }
}

#[test]
fn the_memory_type_of_a_page_needs_one_entry_to_hold_it() {
    let map = [(0x10_0000, 0x2000, 1), (0x10_2000, 0x1000, 4), (0x20_0000, 0x1800, 3)];
    assert_eq!(bootmem::mmap_type_of(0x10_0000, map), Some(1));
    assert_eq!(bootmem::mmap_type_of(0x10_1000, map), Some(1));
    assert_eq!(bootmem::mmap_type_of(0x10_2000, map), Some(4));
    assert_eq!(bootmem::mmap_type_of(0x20_0000, map), Some(3));
    // Across two entries, past an entry's end, in a hole, at the top.
    assert_eq!(bootmem::mmap_type_of(0x10_1800, map), None);
    assert_eq!(bootmem::mmap_type_of(0x20_1000, map), None);
    assert_eq!(bootmem::mmap_type_of(0x30_0000, map), None);
    assert_eq!(bootmem::mmap_type_of(u64::MAX & !0xfff, map), None);
    assert_eq!(bootmem::mmap_type_of(0x10_0000, []), None);
}

/// Audit r13 T2-02: free RAM past BootParams' `MAX_REGIONS` ranges is not
/// dropped silently: the boot says how many ranges and bytes it left out,
/// as it does for device memory.
#[test]
fn free_ram_past_the_boot_range_limit_is_reported() {
    let lib = include_str!("../../crates/fl4-kernel/src/lib.rs");
    let copy = lib.find("for i in 0..free.n.min(MAX_REGIONS) {").expect("free RAM copied");
    let warn = lib.find("if free.n > MAX_REGIONS {").expect("free RAM past the limit");
    assert!(copy < warn);
    let block = &lib[warn..];
    let block = &block[..block.find("\n    }\n").unwrap()];
    assert!(block.contains("let lost = &free.r[MAX_REGIONS..free.n];"));
    assert!(block.contains("kprintln!(\"FL4: {} free RAM region(s) ({:#x} bytes) exceed the boot range limit\", lost.len(), bytes);"));
    assert!(lib.contains("kprintln!(\"FL4: {} device memory regions exceed the boot range limit\", omitted);"));
}

/// BootParams' range limit, as fl4-core states it.
fn max_regions() -> usize {
    let core = include_str!("../../crates/fl4-core/src/boot.rs");
    let at = core.find("pub const MAX_REGIONS: usize = ").expect("MAX_REGIONS") + "pub const MAX_REGIONS: usize = ".len();
    core[at..at + core[at..].find(';').unwrap()].parse().unwrap()
}

/// A CVM's device memory split at 40 fragmented firmware ranges (ACPI
/// reclaim and the like), each with a shared gap after it, yields more
/// ranges than the old limit of 32 and all of them fit in BootParams now.
#[test]
fn fragmented_firmware_boundaries_fit_the_boot_device_ranges() {
    assert_eq!(max_regions(), 128);
    let base = 0x1_0000_0000;
    let dev = [region(base, base + 1024 * MIB)];
    let firmware: Vec<Region> = (0..40).map(|i| region(base + i * 2 * MIB, base + i * 2 * MIB + MIB)).collect();
    let mut out = Vec::new();
    bootmem::device_regions(&dev, &firmware, |r, private| out.push((r, private)));
    // A private range per firmware entry, a shared gap after each.
    assert_eq!(out.len(), 80);
    assert!(out.len() > 32 && out.len() <= max_regions());
    assert_eq!(out.iter().filter(|(_, private)| *private).count(), 40);
    // Ordered, contiguous and covering the device range exactly.
    assert_eq!(out[0].0.start, base);
    assert_eq!(out.last().unwrap().0.end, base + 1024 * MIB);
    for w in out.windows(2) {
        assert_eq!(w[0].0.end, w[1].0.start);
        assert_ne!(w[0].1, w[1].1, "visibility alternates");
    }
}

/// The boot modules and event logs, [image.p_end, log_end), reach the root
/// task only as device untypeds: if a range meeting them does not fit in
/// BootParams the boot stops rather than lose them silently.
#[test]
fn boot_modules_and_event_logs_past_the_device_range_limit_stop_the_boot() {
    let lib = include_str!("../../crates/fl4-kernel/src/lib.rs");
    let call = &lib[lib.find("bootmem::device_regions(&dev.r[..dev.n], &firmware.r[..firmware.n], |r, private| {").expect("device ranges")..];
    let call = &call[..call.find("\n    });\n").unwrap()];
    let full = call.find("} else {\n            omitted += 1;").expect("omitted when full");
    let meets = call.find("if r.start < log_end && image.p_end < r.end {\n                omitted_boot_data = true;\n            }").expect("boot data check");
    assert!(full < meets);
    let after = &lib[lib.find("let mut omitted_boot_data = false;").expect("flag")..];
    let warn = after.find("kprintln!(\"FL4: {} device memory regions exceed the boot range limit\", omitted);").unwrap();
    let stop = after
        .find("if omitted_boot_data {\n        fail(\"boot modules or event logs exceed the boot device range limit\");\n    }")
        .expect("fail-fast");
    assert!(warn < stop);
    assert!(stop < after.find("fl4_core::boot::create_root_task(").unwrap());
    // The ranges handed over hold the modules and logs: added before.
    assert!(lib.find("dev.add(image.p_end, log_end);").unwrap() < lib.find("let mut omitted_boot_data = false;").unwrap());
    // AArch64 the same, for its modules and TPM log.
    let a64 = include_str!("../../crates/fl4-kernel-aarch64/src/lib.rs");
    let blk = &a64[a64.find("if dev.n > MAX_REGIONS {").expect("aarch64 limit")..];
    let blk = &blk[..blk.find("\n    }\n").unwrap()];
    assert!(blk.contains("let lost = &dev.r[MAX_REGIONS..dev.n];"));
    assert!(blk.contains("fail(\"boot modules or event logs exceed the boot device range limit\");"));
}
