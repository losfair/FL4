//! The kernel address space: the physical-memory window at PPTR_BASE and
//! the kernel image at KERNEL_OFFSET, both in the top PML4 slot (so every
//! user address space shares them through copyGlobalMappings). The window
//! uses 1 GiB pages when the CPU has them, 2 MiB pages otherwise, and is
//! never executable; the image is mapped with 4 KiB pages, its code
//! read-only, its read-only data read-only and not executable, and its
//! data not executable.
use fl4_arch_x86_64::sev;
use core::cell::UnsafeCell;
use fl4_arch_x86_64::cpu::{cpuid, write_cr3};
use fl4_core::layout::{PADDR_TOP, PPTR_BASE};

pub const KERNEL_OFFSET: u64 = 0xffff_ffff_8000_0000;
/// With 2 MiB pages the window covers at most this much physical memory.
pub const SMALL_WINDOW_GIB: usize = 16;

const P: u64 = 1;
const RW: u64 = 2;
const PS: u64 = 1 << 7;
const G: u64 = 1 << 8;
const NX: u64 = 1 << 63;

#[repr(C, align(4096))]
struct Table([u64; 512]);

struct Tables {
    pml4: Table,
    pdpt: Table,
    pds: [Table; SMALL_WINDOW_GIB],
    shared_pdpt: Table,
    shared_pds: [Table; SMALL_WINDOW_GIB],
    /// The kernel image, in 4 KiB pages: one page table per 2 MiB of
    /// physical memory from 0.
    image_pd: Table,
    image_pts: [Table; IMAGE_PTS],
    /// Application processors start on this: the kernel's mappings plus
    /// an identity map of the first GiB, for the trampoline.
    ap_pml4: Table,
    ap_pdpt: Table,
    ap_pd: Table,
    /// The skim window (spec.rs): the kernel half of every user address
    /// space when the CPU needs it, mapping the image's .skim parts only.
    skim_pml4: Table,
    skim_pdpt: Table,
    skim_pd: Table,
    skim_pts: [Table; IMAGE_PTS],
}

/// Page tables for the image: room for an image ending below 32 MiB.
const IMAGE_PTS: usize = 16;

struct Cell(UnsafeCell<Tables>);
unsafe impl Sync for Cell {}

static TABLES: Cell = Cell(UnsafeCell::new(Tables {
    pml4: Table([0; 512]),
    pdpt: Table([0; 512]),
    pds: [const { Table([0; 512]) }; SMALL_WINDOW_GIB],
    shared_pdpt: Table([0; 512]),
    shared_pds: [const { Table([0; 512]) }; SMALL_WINDOW_GIB],
    image_pd: Table([0; 512]),
    image_pts: [const { Table([0; 512]) }; IMAGE_PTS],
    ap_pml4: Table([0; 512]),
    ap_pdpt: Table([0; 512]),
    ap_pd: Table([0; 512]),
    skim_pml4: Table([0; 512]),
    skim_pdpt: Table([0; 512]),
    skim_pd: Table([0; 512]),
    skim_pts: [const { Table([0; 512]) }; IMAGE_PTS],
}));

// Section boundaries (linker.ld), all page-aligned.
extern "C" {
    static __text_start: u8;
    static __text_end: u8;
    static __rodata_start: u8;
    static __rodata_end: u8;
    static __data_start: u8;
    static __kernel_end: u8;
    static __skim_text_start: u8;
    static __skim_text_end: u8;
    static __skim_rodata_start: u8;
    static __skim_rodata_end: u8;
    static __skim_bss_start: u8;
    static __skim_bss_end: u8;
}

fn sym(s: &u8) -> u64 {
    s as *const u8 as u64
}

/// Physical address of something in the kernel image.
pub fn image_paddr(v: u64) -> u64 {
    v - KERNEL_OFFSET
}

pub fn has_huge_pages() -> bool {
    cpuid(0x8000_0001, 0).edx & (1 << 26) != 0
}

/// Map the image's pages from virtual `start` to `end` with `flags` into
/// `pd`, with page tables from `pts`.
fn map_image(pd: &mut Table, pts: &mut [Table; IMAGE_PTS], start: u64, end: u64, flags: u64) {
    let mut pa = image_paddr(start) & !0xfff;
    let end = image_paddr(end + 0xfff) & !0xfff;
    while pa < end {
        let pd_i = (pa >> 21) as usize;
        assert!(pd_i < IMAGE_PTS, "FL4: kernel image too large for its page tables");
        pts[pd_i].0[((pa >> 12) & 511) as usize] = pa | flags | sev::mask();
        pd.0[pd_i] = image_paddr(&pts[pd_i] as *const Table as u64) | P | RW;
        pa += 4096;
    }
}

/// Build the tables and switch to them. Returns the PML4's address in the
/// window (what fl4-core uses as the kernel root) and the top of the
/// physical memory the window maps. With the skim window the window's
/// mappings are not global, so none survives a switch to user tables.
pub fn init(nx: bool, skim: bool, gpa_top: u64) -> (u64, u64) {
    let t = unsafe { &mut *TABLES.0.get() };
    let nx_bit = if nx { NX } else { 0 };
    let wg = if skim { 0 } else { G };
    let huge = has_huge_pages();
    let max = if huge { PADDR_TOP } else { (SMALL_WINDOW_GIB as u64) << 30 };
    let mask = sev::mask();
    let window_top = max.min(gpa_top);
    let flags = P | RW | PS | wg | nx_bit;
    // SEV always encrypts page-table walks (including CR3). The C-bit on
    // a leaf selects the data view. Keep the kernel window private and use
    // a second supervisor-only, NX window for MMIO and DMA transitions.
    // These permanent superpage aliases rely on base SEV. SNP and TDX would
    // need accepted-RAM tracking, page-state changes and split mappings.
    let n = (window_top >> 30) as usize;
    for g in 0..n {
        let base = (g as u64) << 30;
        if huge {
            t.pdpt.0[g] = base | flags | mask;
            if mask != 0 { t.shared_pdpt.0[g] = base | flags; }
        } else {
            for j in 0..512 {
                let e = base | ((j as u64) << 21) | flags;
                t.pds[g].0[j] = e | mask;
                if mask != 0 { t.shared_pds[g].0[j] = e; }
            }
            t.pdpt.0[g] = image_paddr(&t.pds[g] as *const Table as u64) | P | RW;
            if mask != 0 {
                t.shared_pdpt.0[g] = image_paddr(&t.shared_pds[g] as *const Table as u64) | P | RW;
            }
        }
    }
    if mask != 0 {
        t.pml4.0[sev::SHARED_SLOT] = image_paddr(&t.shared_pdpt as *const Table as u64) | P | RW;
    }
    // The image, and nothing else, at KERNEL_OFFSET. (Its alias of all of
    // the low 2 GiB was writable and executable.)
    unsafe {
        map_image(&mut t.image_pd, &mut t.image_pts, sym(&__text_start), sym(&__text_end), P | wg);
        map_image(&mut t.image_pd, &mut t.image_pts, sym(&__rodata_start), sym(&__rodata_end), P | wg | nx_bit);
        map_image(&mut t.image_pd, &mut t.image_pts, sym(&__data_start), sym(&__kernel_end), P | RW | wg | nx_bit);
    }
    t.pdpt.0[510] = image_paddr(&t.image_pd as *const Table as u64) | P | RW;
    t.pml4.0[511] = image_paddr(&t.pdpt as *const Table as u64) | P | RW;
    let root = image_paddr(&t.pml4 as *const Table as u64);
    write_cr3(root);
    (root + PPTR_BASE, window_top)
}

/// The skim window's kernel half: only the image's .skim parts (the entry
/// and exit code, the data it reads, and the per-core entry areas), so the
/// kernel stacks, kernel state and everything else stay unmapped while
/// user code runs. Returns the template PML4's address in the window, which
/// user address spaces copy their kernel half from.
pub fn init_skim(nx: bool) -> u64 {
    let t = unsafe { &mut *TABLES.0.get() };
    let nx_bit = if nx { NX } else { 0 };
    unsafe {
        map_image(&mut t.skim_pd, &mut t.skim_pts, sym(&__skim_text_start), sym(&__skim_text_end), P);
        map_image(&mut t.skim_pd, &mut t.skim_pts, sym(&__skim_rodata_start), sym(&__skim_rodata_end), P | nx_bit);
        map_image(&mut t.skim_pd, &mut t.skim_pts, sym(&__skim_bss_start), sym(&__skim_bss_end), P | RW | nx_bit);
    }
    t.skim_pdpt.0[510] = image_paddr(&t.skim_pd as *const Table as u64) | P | RW;
    t.skim_pml4.0[511] = image_paddr(&t.skim_pdpt as *const Table as u64) | P | RW;
    image_paddr(&t.skim_pml4 as *const Table as u64) + PPTR_BASE
}

pub fn root_paddr() -> u64 {
    let t = unsafe { &*TABLES.0.get() };
    image_paddr(&t.pml4 as *const Table as u64)
}

/// Physical address of the page table application processors start on.
pub fn ap_boot_root() -> u64 {
    let t = unsafe { &mut *TABLES.0.get() };
    for (j, e) in t.ap_pd.0.iter_mut().enumerate() {
        *e = ((j as u64) << 21) | P | RW | PS | sev::mask();
    }
    t.ap_pdpt.0[0] = image_paddr(&t.ap_pd as *const Table as u64) | P | RW;
    t.ap_pml4.0[0] = image_paddr(&t.ap_pdpt as *const Table as u64) | P | RW;
    t.ap_pml4.0[511] = t.pml4.0[511];
    image_paddr(&t.ap_pml4 as *const Table as u64)
}
