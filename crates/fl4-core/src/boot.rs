//! Creating the initial user-level state (seL4 kernel/boot.c and
//! arch/x86/kernel/boot.c `init_sys_state`). The x86 backend finds memory,
//! loads the root task's image and builds the extra BootInfo records; this
//! module turns that into the root task's capabilities.

use crate::capability::{Cap, FrameSize, VM_READ_WRITE};
use crate::cdt;
use crate::interrupt;
use crate::layout::{self, irq, ks, node, tcb as tl};
use crate::machine::{Arch, Store};
use crate::obj::{ks_set, node_get, node_set, Sc, Slot, Tcb};
use crate::objects;
use crate::regs;
use crate::sched;
use crate::sporadic;
use crate::vspace;
use fl4_abi::consts::{bits, root_slot as rs};

pub const MAX_REGIONS: usize = 128;
pub const ROOT_CNODE_BITS: u64 = fl4_abi::config::ROOT_CNODE_SIZE_BITS;
pub const MAX_BOOTINFO_UNTYPEDS: u64 = 230;
pub const BOOT_THREAD_TIME_SLICE_US: u64 = 5 * 1000;
/// The root task's ASID.
pub const IT_ASID: u64 = 1;
arch_items!("boot.rs");

/// A half-open range of kernel virtual (or, for devices, physical)
/// addresses.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Region {
    pub start: u64,
    pub end: u64,
}

impl Region {
    pub const EMPTY: Region = Region { start: 0, end: 0 };
    pub fn is_empty(self) -> bool {
        self.start >= self.end
    }
}

/// What the backend hands to `create_root_task`.
pub struct BootParams {
    /// Free RAM (kernel virtual addresses), sorted, page aligned, not
    /// overlapping the kernel, the boot modules or the root task image.
    pub free: [Region; MAX_REGIONS],
    pub n_free: u64,
    /// Sub-ranges of free RAM (kernel virtual addresses), sorted, page
    /// aligned, that the loader guarantees are already zeroed.
    pub zeroed: [Region; MAX_REGIONS],
    pub n_zeroed: u64,
    /// Physical ranges given out as device untypeds, sorted.
    pub device: [Region; MAX_REGIONS],
    pub n_device: u64,
    /// The root task image: physical range, physical minus virtual
    /// offset, and entry point.
    pub ui_p_start: u64,
    pub ui_p_end: u64,
    pub pv_offset: u64,
    pub v_entry: u64,
    /// Extra BootInfo records, prepared by the backend (kernel address).
    pub extra_bi: u64,
    pub extra_bi_len: u64,
    pub num_nodes: u64,
    /// Per-core idle thread memory: a 4 KiB TCB followed by a 256-byte SC,
    /// `idle_stride` bytes apart, starting at `idle_base`.
    pub idle_base: u64,
    pub idle_stride: u64,
    /// The kernel image's addresses as linked, [first, end) (seL4
    /// [KERNEL_ELF_BASE, ki_end)): the names of the kernel's statics,
    /// which hold kernel objects (the global state, the IRQ node, the idle
    /// threads). `PPTR_BASE <= start`; no device untyped's pointer range
    /// meets it (`create_device_untypeds`).
    pub kernel_image: Region,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BootError {
    NoMemory,
    TooManyCaps,
    /// More untypeds than the BootInfo and the l4h 0047 chunk describe.
    TooManyUntypeds,
}

/// Word offsets in seL4_BootInfo.
mod bi {
    pub const EXTRA_LEN: u64 = 0;
    pub const NODE_ID: u64 = 1;
    pub const NUM_NODES: u64 = 2;
    pub const NUM_IOPT_LEVELS: u64 = 3;
    pub const IPC_BUFFER: u64 = 4;
    pub const EMPTY: u64 = 5;
    pub const USER_IMAGE_FRAMES: u64 = 9;
    pub const USER_IMAGE_PAGING: u64 = 11;
    pub const EXTRA_BI_PAGES: u64 = 15;
    pub const CNODE_SIZE_BITS: u64 = 17;
    pub const DOMAIN: u64 = 18;
    pub const SCHED_CONTROL: u64 = 19;
    pub const UNTYPED: u64 = 21;
    pub const UNTYPED_LIST: u64 = 23;
}

struct Boot {
    root_cnode: u64,
    slot_pos: u64,
    bi_frame: u64,
    /// Bump allocator over the root server's memory.
    next: u64,
    end: u64,
    /// The root CNode overflowed.
    full: bool,
    /// l4h 0047: kernel address of the extra untyped chunk's header, after
    /// the backend's chunks; 0 when there is no room for it.
    extra_ut: u64,
    /// l4h 0047: the extra BootInfo's mapped size, set with `extra_ut`;
    /// what it does not use is a padding record.
    extra_bytes: u64,
    /// An untyped was dropped because neither list had room for it.
    ut_lost: bool,
}

fn bi_set<S: Store>(s: &mut S, b: &Boot, word: u64, v: u64) {
    s.write(b.bi_frame.wrapping_add(word.wrapping_mul(8)), v)
}

/// seL4 `write_slot`.
fn write_slot<S: Store>(s: &mut S, slot: Slot, c: Cap) {
    slot.clear(s);
    slot.set_cap(s, c);
    slot.set_revocable(s, true);
    slot.set_first_badged(s, true);
}

fn root_slot(b: &Boot, i: u64) -> Slot {
    Slot::index(b.root_cnode, i)
}

/// Put `c` in the next free root CNode slot. When the CNode is full the
/// cap is dropped and `b.full` set; `create_root_task` then fails. (No
/// early exit, so the loops that call this translate to Lean.)
fn provide_cap<S: Store>(s: &mut S, b: &mut Boot, c: Cap) {
    if b.slot_pos >= (1u64 << ROOT_CNODE_BITS) {
        b.full = true;
    } else {
        write_slot(s, root_slot(b, b.slot_pos), c);
        b.slot_pos += 1;
    }
}

fn alloc<S: Store>(s: &mut S, b: &mut Boot, size_bits: u64, n: u64) -> u64 {
    let p = b.next;
    let len = n << (size_bits & 63);
    b.next = b.next.wrapping_add(len);
    s.zero(p, len);
    p
}

/// Number of tables of the level covering 2^bits needed for `r`.
fn n_paging(r: Region, bits: u64) -> u64 {
    let b = bits & 63;
    let start = r.start >> b;
    let end = (r.end.wrapping_add((1u64 << (b & 63)).wrapping_sub(1))) >> b;
    end.wrapping_sub(start)
}

fn arch_n_paging(r: Region) -> u64 {
    n_paging(r, 21).wrapping_add(n_paging(r, 30)).wrapping_add(n_paging(r, 39))
}

/// Bytes the extra BootInfo reserves for the l4h 0047 chunk: a header and
/// `EXTRA_UNTYPEDS` 16-byte descriptors.
/// The bytes `root_layout` adds to the extra BootInfo for the extra
/// untyped chunk (l4h 0047), which the loader's tail check must count too.
pub fn extra_ut_reserve() -> u64 {
    if EXTRA_UNTYPEDS > 0 {
        16 + 16 * EXTRA_UNTYPEDS
    } else {
        0
    }
}

fn extra_bi_size_bits(len: u64) -> u64 {
    if len == 0 {
        return 0;
    }
    let rounded = len.wrapping_add(4095) & !4095;
    let mut msb = 63u64.wrapping_sub(rounded.leading_zeros() as u64) & 63;
    if rounded > (1u64 << (msb & 63)) {
        msb += 1;
    }
    msb
}

/// Address of the entry for `vaddr` in the table at `table` whose entries
/// each cover 2^shift bytes.
fn entry_addr(table: u64, vaddr: u64, shift: u64) -> u64 {
    table.wrapping_add(((vaddr >> (shift & 63)) & 511).wrapping_mul(8))
}

/// The table the entry for `vaddr` points to.
fn next_table<S: Store>(s: &S, table: u64, vaddr: u64, shift: u64) -> u64 {
    layout::pptr(s.read(entry_addr(table, vaddr, shift)) & 0x000f_ffff_ffff_f000)
}

fn it_frame_cap(pptr: u64, vaddr: u64, mapped: bool) -> Cap {
    Cap::Frame {
        ptr: pptr,
        size: FrameSize::Small,
        rights: VM_READ_WRITE,
        is_device: false,
        mapped,
        is_ept: false,
        asid: if mapped { IT_ASID } else { 0 },
        vaddr: if mapped { vaddr } else { 0 },
    }
}

fn create_frames<S: Store>(s: &mut S, b: &mut Boot, reg: Region, pml4: u64, pv_offset: u64) -> (u64, u64) {
    let before = b.slot_pos;
    // `reg` is page aligned; count pages so the loop cannot wrap.
    let n = if reg.end > reg.start { (reg.end - reg.start) / 4096 } else { 0 };
    let mut i: u64 = 0;
    while i < n {
        let f = reg.start.wrapping_add(i.wrapping_mul(4096));
        let paddr = layout::paddr(f);
        let vaddr = paddr.wrapping_sub(pv_offset);
        map_it_frame(s, pml4, vaddr, paddr);
        provide_cap(s, b, it_frame_cap(f, vaddr, true));
        i += 1;
    }
    (before, b.slot_pos)
}

fn create_untypeds_for_region<S: Store>(
    s: &mut S,
    b: &mut Boot,
    device: bool,
    reg: Region,
    first: u64,
    zeroed: &[Region; MAX_REGIONS],
    n_zeroed: u64,
) {
    let mut start = reg.start;
    // Each round takes the largest aligned block at `start`, so a region
    // splits into at most 128 blocks; the fuel makes that bound explicit.
    let mut fuel: u64 = 128;
    while start < reg.end && fuel > 0 {
        fuel -= 1;
        let mut size_bits = 63u64.wrapping_sub((reg.end - start).leading_zeros() as u64) & 63;
        if size_bits > bits::MAX_UNTYPED {
            size_bits = bits::MAX_UNTYPED;
        }
        // Aligned as the cap's pointer, as in seL4, which works on the
        // region in kernel-pointer space: retype aligns pointers, and the
        // window's base is only 2^39-aligned, so a device block aligned
        // only physically would have its children shifted (GitHub
        // issue #2).
        let at = if device { layout::pptr(start) } else { start };
        if at != 0 {
            let align = at.trailing_zeros() as u64;
            if size_bits > align {
                size_bits = align;
            }
        }
        if size_bits >= bits::MIN_UNTYPED {
            let i = b.slot_pos.wrapping_sub(first);
            let paddr = if device { start } else { layout::paddr(start) };
            let desc = size_bits | (if device { 1 << 8 } else { 0 });
            if i < MAX_BOOTINFO_UNTYPEDS {
                bi_set(s, b, bi::UNTYPED_LIST + 2 * i, paddr);
                bi_set(s, b, bi::UNTYPED_LIST + 2 * i + 1, desc);
                provide_untyped(s, b, device, start, size_bits, zeroed, n_zeroed);
            } else if b.extra_ut != 0 && i - MAX_BOOTINFO_UNTYPEDS < EXTRA_UNTYPEDS {
                // l4h 0047: the descriptor goes in the extra chunk, after
                // its 16-byte header.
                let e = b.extra_ut.wrapping_add(16).wrapping_add((i - MAX_BOOTINFO_UNTYPEDS).wrapping_mul(16));
                s.write(e, paddr);
                s.write(e.wrapping_add(8), desc);
                provide_untyped(s, b, device, start, size_bits, zeroed, n_zeroed);
            } else if EXTRA_UNTYPEDS > 0 {
                b.ut_lost = true;
            }
        }
        start = start.wrapping_add(1u64 << (size_bits & 63));
    }
}

/// Device untypeds for the physical region `reg`, minus the physical page
/// whose pointer is 0 and the physical addresses whose pointers are the
/// kernel image's addresses `kernel` (`create_device_untypeds_image`).
///
/// The pointer-0 page is physical `2^64 - PPTR_BASE` (x86_64 512 GiB,
/// AArch64 128 TiB), where device pointers wrap to the lower half: a
/// device untyped starting there would have pointer 0, the null name
/// (seL4's null capability pointer), and so would the first frame
/// retyped from it. The cut is the whole page [paddr(0), paddr(0) +
/// 4 KiB) rather than the smallest untyped (2^MIN_UNTYPED bytes): device
/// memory is page granular and a device untyped makes only frames (at
/// least a page, page aligned) and smaller untypeds, so the rest of that
/// page could never hold a frame and would only spend bootinfo slots on
/// up to eight tiny untypeds; with the page cut every device untyped
/// stays page aligned in pointer space, as without it. The untypeds
/// below the cut end at pointer 2^64 (as before), those above start at
/// pointer 4 KiB, so no device untyped's range contains pointer 0.
fn create_device_untypeds<S: Store>(s: &mut S, b: &mut Boot, reg: Region, kernel: Region, first: u64) {
    // paddr(0) = 2^64 - PPTR_BASE < 2^64 - 4096: no overflow.
    let null_start = layout::paddr(0);
    let null_end = null_start.wrapping_add(4096);
    let below_end = if reg.end < null_start { reg.end } else { null_start };
    create_device_untypeds_image(s, b, Region { start: reg.start, end: below_end }, kernel, first);
    let above_start = if reg.start > null_end { reg.start } else { null_end };
    create_device_untypeds_image(s, b, Region { start: above_start, end: reg.end }, kernel, first);
}

/// Device untypeds for the physical region `reg`, minus the physical
/// addresses whose pointers are the kernel image's addresses `kernel`.
///
/// An untyped's objects are named by pointers, and a device untyped's
/// pointer is its physical address plus PPTR_BASE whatever is there, so
/// device memory at physical `kernel - PPTR_BASE` (on x86_64
/// [510 GiB, 510 GiB + image size), just above the window; on AArch64
/// just below 128 TiB) would get the names of the kernel's statics: a
/// retype or reset of it would create or delete objects (in the
/// specification, `deleteObjects` over its range) under the names of the
/// global state, the IRQ node's CNodes and the idle threads. seL4 hands
/// that memory out (boot.c `create_untypeds`); l4v assumes it does not
/// (`valid_global_refs`: no untyped covers a kernel object). So the
/// kernel leaves it out. Pointers above it wrap to the lower half, which
/// holds no kernel object, and an untyped never wraps (it is aligned in
/// pointer space), so every device untyped's range misses `kernel`.
fn create_device_untypeds_image<S: Store>(s: &mut S, b: &mut Boot, reg: Region, kernel: Region, first: u64) {
    let cut_start = layout::paddr(kernel.start);
    let cut_end = layout::paddr(kernel.end);
    let no_zeroed = [Region::EMPTY; MAX_REGIONS];
    if cut_start >= cut_end {
        create_untypeds_for_region(s, b, true, reg, first, &no_zeroed, 0);
        return;
    }
    let below_end = if reg.end < cut_start { reg.end } else { cut_start };
    create_untypeds_for_region(s, b, true, Region { start: reg.start, end: below_end }, first, &no_zeroed, 0);
    let above_start = if reg.start > cut_end { reg.start } else { cut_end };
    create_untypeds_for_region(s, b, true, Region { start: above_start, end: reg.end }, first, &no_zeroed, 0);
}

/// The cap for the untyped at `start` (a kernel address for RAM, physical
/// for devices).
fn provide_untyped<S: Store>(
    s: &mut S,
    b: &mut Boot,
    device: bool,
    start: u64,
    size_bits: u64,
    zeroed: &[Region; MAX_REGIONS],
    n_zeroed: u64,
) {
    let ptr = if device { layout::pptr(start) } else { start };
    // Boot untypeds are clean (l4h 0019): RAM is cleared here so the free
    // index can start at 0.
    if !device {
        clear_dirty(s, start, 1u64 << (size_bits & 63), zeroed, n_zeroed);
    }
    provide_cap(s, b, Cap::Untyped { ptr, size_bits, free_index: 0, is_device: device });
}

fn is_prezeroed(zeroed: &[Region; MAX_REGIONS], n_zeroed: u64, start: u64, len: u64) -> bool {
    let end = match start.checked_add(len) {
        Some(e) => e,
        None => return false,
    };
    let mut i: u64 = 0;
    let mut found = false;
    while i < n_zeroed && i < MAX_REGIONS as u64 {
        let z = zeroed[i as usize];
        if z.start <= start && end <= z.end {
            found = true;
        }
        i += 1;
    }
    found
}

/// l4h 0019: clear the pages of [start, start + len) that hold a nonzero
/// word and leave the others alone, so a hypervisor's shared zero pages
/// stay shared. `len` is a power of two of at least 16 bytes.
fn clear_dirty<S: Store>(
    s: &mut S,
    start: u64,
    len: u64,
    zeroed: &[Region; MAX_REGIONS],
    n_zeroed: u64,
) {
    if is_prezeroed(zeroed, n_zeroed, start, len) {
        return;
    }
    let chunk = if len < 4096 { len } else { 4096 };
    if chunk == 0 {
        return;
    }
    let n = len / chunk;
    let mut i: u64 = 0;
    while i < n {
        let base = start.wrapping_add(i.wrapping_mul(chunk));
        if !is_prezeroed(zeroed, n_zeroed, base, chunk) && !all_zero(s, base, chunk / 8) {
            s.zero(base, chunk);
        }
        i += 1;
    }
}

/// The `words` words from `base` are all zero.
fn all_zero<S: Store>(s: &S, base: u64, words: u64) -> bool {
    let mut k: u64 = 0;
    while k < words && s.read(base.wrapping_add(k.wrapping_mul(8))) == 0 {
        k += 1;
    }
    k == words
}

fn configure_sched_context<S: Store>(s: &mut S, t: Tcb, sc: Sc, budget: u64) {
    t.set_sc(s, sc.0);
    sporadic::refill_new(s, sc, sporadic::MIN_REFILLS, budget, 0);
    sc.set_tcb(s, t.0);
}

fn set_name<S: Store>(s: &mut S, t: Tcb, name: &[u8]) {
    let mut w: u64 = 0;
    while w < 8 {
        let mut v: u64 = 0;
        let mut k = 0;
        while k < 8 {
            let i = w.wrapping_mul(8).wrapping_add(k) as usize;
            if i < name.len() {
                v |= (name[i] as u64) << (k.wrapping_mul(8) & 63);
            }
            k += 1;
        }
        s.write(t.name_addr().wrapping_add(w.wrapping_mul(8)), v);
        w += 1;
    }
}

/// Pick the root server's memory: the top of the highest free region that
/// fits `size` bytes aligned to `align_bits`.
fn take_rootserver_mem(p: &mut BootParams, size: u64, align_bits: u64) -> Option<u64> {
    let pick = match find_rootserver_mem(p, size, align_bits) {
        Some(x) => x,
        None => return None,
    };
    if pick.k >= MAX_REGIONS {
        return None;
    }
    let r = p.free[pick.k];
    // Split the region around the allocation.
    let tail = Region { start: pick.start.wrapping_add(size), end: r.end };
    p.free[pick.k] = Region { start: r.start, end: pick.start };
    if !tail.is_empty() && p.n_free < MAX_REGIONS as u64 {
        let n = p.n_free as usize;
        p.free[n] = tail;
        p.n_free += 1;
    }
    Some(pick.start)
}

/// Where `take_rootserver_mem` takes from: region `k`, at `start`.
struct Pick {
    k: usize,
    start: u64,
}

fn find_rootserver_mem(p: &BootParams, size: u64, align_bits: u64) -> Option<Pick> {
    let mut i = p.n_free;
    while i > 0 {
        i -= 1;
        let k = i as usize;
        if k < MAX_REGIONS {
            let r = p.free[k];
            if r.end > r.start && r.end - r.start >= size {
                let start = (r.end - size) & !((1u64 << (align_bits & 63)).wrapping_sub(1));
                if start >= r.start {
                    return Some(Pick { k, start });
                }
            }
        }
    }
    None
}

/// Build the root task, the idle threads and the scheduler state, and
/// make the root task the scheduler's next choice.
pub fn create_root_task<S: Store, A: Arch>(s: &mut S, a: &mut A, p: &mut BootParams) -> Result<Tcb, BootError> {
    let mut r = rootserver_objects(s, p)?;
    let root_cap = init_root_cnode(s, &r.b);
    init_tdx_control(s, a, &r.b);
    init_bootinfo(s, &mut r, p);
    let (vcap, ipc_cap) = init_address_space(s, &mut r, p);
    // The paging structures came from the allocator above; the SC is last
    // because it is the only object smaller than a page.
    let sc = Sc(alloc(s, &mut r.b, bits::MIN_SCHED_CONTEXT, 1));
    if r.b.next > r.b.end {
        return Err(BootError::NoMemory);
    }
    init_asid_pool(s, &r);
    create_idle_threads(s, a, p);
    init_root_thread(s, a, &r, p, sc, root_cap, vcap, ipc_cap);
    init_core_state(s, r.tcb, p.num_nodes);
    create_untypeds(s, &mut r.b, p);
    if r.b.full {
        return Err(BootError::TooManyCaps);
    }
    if r.b.ut_lost {
        return Err(BootError::TooManyUntypeds);
    }
    Ok(r.tcb)
}

/// The root task's objects and where its frames go in its address space.
struct Root {
    b: Boot,
    extra_bi: u64,
    pml4: u64,
    asid_pool: u64,
    ipc_buf: u64,
    tcb: Tcb,
    ipcbuf_vptr: u64,
    bi_frame_vptr: u64,
    extra_bi_vptr: u64,
    ebytes: u64,
    it: Region,
}

/// Where the root task's frames go in its address space, and how much
/// memory its objects take (seL4 `calculate_rootserver_size`).
#[derive(Clone, Copy)]
struct RootLayout {
    ipcbuf_vptr: u64,
    bi_frame_vptr: u64,
    extra_bi_vptr: u64,
    ebits: u64,
    ebytes: u64,
    it: Region,
    cnode_bits: u64,
    max_bits: u64,
    total: u64,
}

fn root_layout(p: &BootParams) -> RootLayout {
    let ui_v_start = p.ui_p_start.wrapping_sub(p.pv_offset);
    let ui_v_end = p.ui_p_end.wrapping_sub(p.pv_offset);
    let ipcbuf_vptr = ui_v_end;
    let bi_frame_vptr = ipcbuf_vptr.wrapping_add(4096);
    let extra_bi_vptr = bi_frame_vptr.wrapping_add(4096);
    // l4h 0047: room for the extra untyped chunk after the backend's.
    let ebits = extra_bi_size_bits(p.extra_bi_len.wrapping_add(extra_ut_reserve()));
    let ebytes = if ebits > 0 { 1u64 << (ebits & 63) } else { 0 };
    let it = Region { start: ui_v_start, end: extra_bi_vptr.wrapping_add(ebytes).wrapping_add(4095) & !4095 };
    let cnode_bits = ROOT_CNODE_BITS + bits::SLOT;
    let n_paging = arch_n_paging(it);
    let fixed = (1u64 << (cnode_bits & 63)) + (1u64 << bits::TCB) + 4096 * 3 + 4096 + (1u64 << bits::MIN_SCHED_CONTEXT);
    let size = fixed.wrapping_add(ebytes).wrapping_add(n_paging.wrapping_mul(4096));
    let max_bits = if cnode_bits > ebits { cnode_bits } else { ebits };
    let total = size.wrapping_add(1u64 << (max_bits & 63));
    RootLayout { ipcbuf_vptr, bi_frame_vptr, extra_bi_vptr, ebits, ebytes, it, cnode_bits, max_bits, total }
}

/// seL4 `create_rootserver_objects`.
fn rootserver_objects<S: Store>(s: &mut S, p: &mut BootParams) -> Result<Root, BootError> {
    let l = root_layout(p);
    let start = match take_rootserver_mem(p, l.total, l.max_bits) {
        Some(x) => x,
        None => return Err(BootError::NoMemory),
    };
    let mut b = Boot {
        root_cnode: 0,
        slot_pos: 0,
        bi_frame: 0,
        next: start,
        end: start.wrapping_add(l.total),
        full: false,
        extra_ut: 0,
        extra_bytes: 0,
        ut_lost: false,
    };
    let extra_bi = alloc_root_objects(s, &mut b, l.ebits, l.cnode_bits);
    // `Store::write` takes aligned words; `alloc` zeroed the chunk.
    if EXTRA_UNTYPEDS > 0 && p.extra_bi_len & 7 == 0 {
        b.extra_ut = extra_bi.wrapping_add(p.extra_bi_len);
        b.extra_bytes = l.ebytes;
    }
    let pml4 = alloc(s, &mut b, 12, 1);
    let asid_pool = alloc(s, &mut b, 12, 1);
    let ipc_buf = alloc(s, &mut b, 12, 1);
    b.bi_frame = alloc(s, &mut b, 12, 1);
    let tcb = Tcb(alloc(s, &mut b, bits::TCB, 1));
    Ok(Root {
        b,
        extra_bi,
        pml4,
        asid_pool,
        ipc_buf,
        tcb,
        ipcbuf_vptr: l.ipcbuf_vptr,
        bi_frame_vptr: l.bi_frame_vptr,
        extra_bi_vptr: l.extra_bi_vptr,
        ebytes: l.ebytes,
        it: l.it,
    })
}

/// The root CNode and the extra BootInfo, the larger first for
/// alignment; returns the extra BootInfo's address (0 if none).
fn alloc_root_objects<S: Store>(s: &mut S, b: &mut Boot, ebits: u64, cnode_bits: u64) -> u64 {
    let extra_bi = if ebits >= cnode_bits && ebits > 0 { alloc(s, b, ebits, 1) } else { 0 };
    b.root_cnode = alloc(s, b, cnode_bits, 1);
    if extra_bi == 0 && ebits > 0 {
        alloc(s, b, ebits, 1)
    } else {
        extra_bi
    }
}

/// BootInfo's fields, the extra BootInfo, and the SchedControl caps.
fn init_bootinfo<S: Store>(s: &mut S, r: &mut Root, p: &BootParams) {
    let b = &mut r.b;
    bi_set(s, b, bi::NODE_ID, 0);
    bi_set(s, b, bi::NUM_NODES, p.num_nodes);
    bi_set(s, b, bi::NUM_IOPT_LEVELS, u64::MAX);
    bi_set(s, b, bi::IPC_BUFFER, r.ipcbuf_vptr);
    bi_set(s, b, bi::CNODE_SIZE_BITS, ROOT_CNODE_BITS);
    bi_set(s, b, bi::DOMAIN, 0);
    bi_set(s, b, bi::EXTRA_LEN, p.extra_bi_len);
    b.slot_pos = rs::NumInitialCaps;
    let mut w = 0;
    while w < p.extra_bi_len.wrapping_add(7) / 8 {
        let v = s.read(p.extra_bi.wrapping_add(w.wrapping_mul(8)));
        s.write(r.extra_bi.wrapping_add(w.wrapping_mul(8)), v);
        w += 1;
    }
    let first = b.slot_pos;
    let mut n = 0;
    while n < p.num_nodes {
        provide_cap(s, b, Cap::SchedControl { cpu: n });
        n += 1;
    }
    bi_set(s, b, bi::SCHED_CONTROL, first);
    bi_set(s, b, bi::SCHED_CONTROL + 1, b.slot_pos);
}

/// The address space with the BootInfo frame, the extra BootInfo, the IPC
/// buffer and the image; returns the VSpace and IPC buffer caps.
fn init_address_space<S: Store>(s: &mut S, r: &mut Root, p: &BootParams) -> (Cap, Cap) {
    let vcap = create_it_address_space(s, &mut r.b, r.it, r.pml4);
    map_it_frame(s, r.pml4, r.bi_frame_vptr, layout::paddr(r.b.bi_frame));
    write_slot(s, root_slot(&r.b, rs::BootInfoFrame), it_frame_cap(r.b.bi_frame, r.bi_frame_vptr, true));
    let extra_off = layout::paddr(r.extra_bi).wrapping_sub(r.extra_bi_vptr);
    let (ef, el) = create_frames(s, &mut r.b, Region { start: r.extra_bi, end: r.extra_bi.wrapping_add(r.ebytes) }, r.pml4, extra_off);
    bi_set(s, &r.b, bi::EXTRA_BI_PAGES, ef);
    bi_set(s, &r.b, bi::EXTRA_BI_PAGES + 1, el);
    map_it_frame(s, r.pml4, r.ipcbuf_vptr, layout::paddr(r.ipc_buf));
    let ipc_cap = it_frame_cap(r.ipc_buf, r.ipcbuf_vptr, true);
    write_slot(s, root_slot(&r.b, rs::InitThreadIPCBuffer), ipc_cap);
    let ui = Region { start: layout::pptr(p.ui_p_start), end: layout::pptr(p.ui_p_end) };
    let (uf, ul) = create_frames(s, &mut r.b, ui, r.pml4, p.pv_offset);
    bi_set(s, &r.b, bi::USER_IMAGE_FRAMES, uf);
    bi_set(s, &r.b, bi::USER_IMAGE_FRAMES + 1, ul);
    (vcap, ipc_cap)
}

fn init_asid_pool<S: Store>(s: &mut S, r: &Root) {
    let base = (IT_ASID >> vspace::ASID_LOW_BITS) << vspace::ASID_LOW_BITS;
    write_slot(s, root_slot(&r.b, rs::InitThreadASIDPool), Cap::AsidPool { ptr: r.asid_pool, asid_base: base });
    write_slot(s, root_slot(&r.b, rs::ASIDControl), Cap::AsidControl);
    ks_set(s, ks::ASID_TABLE + (IT_ASID >> vspace::ASID_LOW_BITS) * 8, r.asid_pool);
    s.write(r.asid_pool.wrapping_add((IT_ASID & 511) * 8), r.pml4);
}

/// Idle threads, one per core.
fn create_idle_threads<S: Store, A: Arch>(s: &mut S, a: &mut A, p: &BootParams) {
    let now = a.now();
    let mut c = 0;
    while c < p.num_nodes {
        node_set(s, c, node::CUR_TIME, now);
        let base = p.idle_base.wrapping_add(c.wrapping_mul(p.idle_stride));
        create_idle_thread(s, a, c, Tcb(base), Sc(base.wrapping_add(4096)));
        c += 1;
    }
}

fn create_idle_thread<S: Store, A: Arch>(s: &mut S, a: &mut A, c: u64, idle: Tcb, isc: Sc) {
    s.zero(idle.0, 4096 + 256);
    regs::init_context(s, idle);
    idle.set_flags(s, fl4_abi::consts::tcb_flag::FPU_DISABLED);
    idle.set_state(s, sched::TS_IDLE);
    idle.set_affinity(s, c);
    set_name(s, idle, b"idle_thread");
    node_set(s, c, node::IDLE_THREAD, idle.0);
    let max_ticks = a.us_to_ticks(sporadic::max_period_us(a));
    configure_sched_context(s, idle, isc, max_ticks);
    isc.set_cpu(s, c);
    node_set(s, c, node::IDLE_SC, isc.0);
    node_set(s, c, node::CUR_THREAD, idle.0);
    node_set(s, c, node::CUR_SC, isc.0);
    node_set(s, c, node::REPROGRAM, 1);
    node_set(s, c, node::SCHED_ACTION, sched::ACTION_RESUME_CURRENT);
}

/// The initial thread.
#[allow(clippy::too_many_arguments)]
fn init_root_thread<S: Store, A: Arch>(s: &mut S, a: &mut A, r: &Root, p: &BootParams, sc: Sc, root_cap: Cap, vcap: Cap, ipc_cap: Cap) {
    let tcb = r.tcb;
    regs::init_context(s, tcb);
    objects_init_fpu(s, tcb);
    crate::debug::init_context(s, tcb);
    let derived = objects::derive_cap(s, root_slot(&r.b, rs::InitThreadIPCBuffer), ipc_cap).unwrap_or(Cap::Null);
    cdt::insert(s, root_cap, root_slot(&r.b, rs::InitThreadCNode), tcb.slot(tl::SLOT_CTABLE));
    cdt::insert(s, vcap, root_slot(&r.b, rs::InitThreadVSpace), tcb.slot(tl::SLOT_VTABLE));
    cdt::insert(s, derived, root_slot(&r.b, rs::InitThreadIPCBuffer), tcb.slot(tl::SLOT_BUFFER));
    tcb.set_ipc_buffer(s, r.ipcbuf_vptr);
    tcb.set_reg(s, layout::reg::CAP, r.bi_frame_vptr);
    tcb.set_reg(s, layout::reg::NEXT_IP, p.v_entry);
    tcb.set_reg(s, layout::reg::FAULT_IP, p.v_entry);
    let slice = a.us_to_ticks(BOOT_THREAD_TIME_SLICE_US);
    configure_sched_context(s, tcb, sc, slice);
    tcb.set_prio(s, fl4_abi::consts::MAX_PRIO);
    tcb.set_mcp(s, fl4_abi::consts::MAX_PRIO);
    tcb.set_domain(s, 0);
    tcb.set_state(s, sched::TS_RUNNING);
    write_slot(s, root_slot(&r.b, rs::InitThreadTCB), Cap::Thread { ptr: tcb.0 });
    write_slot(s, root_slot(&r.b, rs::InitThreadSC), Cap::SchedContext { ptr: sc.0, size_bits: bits::MIN_SCHED_CONTEXT });
    set_name(s, tcb, b"rootserver");
}

/// seL4 `init_core_state`: the root task runs first.
fn init_core_state<S: Store>(s: &mut S, tcb: Tcb, num_nodes: u64) {
    // Every TCB that can be migrated or deleted is on its core's debug
    // list, as `objects::create_object` keeps for the others.
    objects::debug_append(s, tcb);
    if fl4_abi::config::DEBUG_BUILD {
        let mut c = 0;
        while c < num_nodes {
            let idle = Tcb(node_get(s, c, node::IDLE_THREAD));
            objects::debug_append(s, idle);
            c += 1;
        }
    }
    node_set(s, 0, node::SCHED_ACTION, tcb.0);
    ks_set(s, ks::CUR_DOMAIN, 0);
    ks_set(s, ks::DOMAIN_TIME, (1 << 56) - 1);
    sched::set_dom_sched(s, 0, 0, (1 << 56) - 1);
    ks_set(s, ks::NUM_NODES, num_nodes);
}

/// Untypeds: device memory first, then free RAM (seL4 `create_untypeds`).
fn create_untypeds<S: Store>(s: &mut S, b: &mut Boot, p: &BootParams) {
    let first = b.slot_pos;
    let mut i = 0;
    while i < p.n_device && i < MAX_REGIONS as u64 {
        let r = p.device[i as usize];
        create_device_untypeds(s, b, r, p.kernel_image, first);
        i += 1;
    }
    let mut i = 0;
    while i < p.n_free && i < MAX_REGIONS as u64 {
        let r = p.free[i as usize];
        create_untypeds_for_region(s, b, false, r, first, &p.zeroed, p.n_zeroed);
        i += 1;
    }
    // l4h 0047: `untyped` covers the BootInfo's list; the caps described
    // in the extra chunk follow it, before `empty`.
    let base_end = first.wrapping_add(MAX_BOOTINFO_UNTYPEDS);
    let end = if b.slot_pos < base_end { b.slot_pos } else { base_end };
    let n = if b.slot_pos > base_end { b.slot_pos - base_end } else { 0 };
    let mut used = p.extra_bi_len;
    if n > 0 {
        let len = 16u64.wrapping_add(n.wrapping_mul(16));
        s.write(b.extra_ut, fl4_abi::consts::bootinfo_header::X86_EXTRA_UNTYPEDS);
        s.write(b.extra_ut.wrapping_add(8), len);
        used = used.wrapping_add(len);
        bi_set(s, b, bi::EXTRA_LEN, used);
    }
    // With the reservation the extra BootInfo is mapped whole, so, as in
    // seL4, a padding record covers the rest and `extraLen` all of it: a
    // root that reserves `extraLen` rounded up to pages then reserves
    // every mapped page.
    if b.extra_ut != 0 && b.extra_bytes > used && b.extra_bytes - used >= 16 {
        let pad = b.extra_ut.wrapping_add(used.wrapping_sub(p.extra_bi_len));
        s.write(pad, fl4_abi::consts::bootinfo_header::PADDING);
        s.write(pad.wrapping_add(8), b.extra_bytes - used);
        bi_set(s, b, bi::EXTRA_LEN, b.extra_bytes);
    }
    bi_set(s, b, bi::UNTYPED, first);
    bi_set(s, b, bi::UNTYPED + 1, end);
    bi_set(s, b, bi::EMPTY, b.slot_pos);
    bi_set(s, b, bi::EMPTY + 1, 1u64 << ROOT_CNODE_BITS);
}

#[cfg(test)]
mod tests {
    //! Device untypeds never take the kernel image's names
    //! (`create_device_untypeds`).
    extern crate std;
    use super::*;
    use std::collections::BTreeMap;
    use std::vec::Vec;

    struct Mem(BTreeMap<u64, u64>);
    impl Store for Mem {
        fn read(&self, a: u64) -> u64 {
            *self.0.get(&a).unwrap_or(&0)
        }
        fn write(&mut self, a: u64, v: u64) {
            self.0.insert(a, v);
        }
        fn zero(&mut self, a: u64, len: u64) {
            for i in (0..len).step_by(8) {
                self.write(a + i, 0);
            }
        }
        fn clear_free(&mut self, a: u64, len: u64) {
            self.zero(a, len)
        }
        fn ks_base(&self) -> u64 {
            0x10_0000
        }
        fn cur_cpu(&self) -> u64 {
            0
        }
    }

    const GIB: u64 = 1 << 30;
    /// Where both kernels link their image (x86_64 KERNEL_OFFSET, AArch64
    /// KERNEL_VBASE).
    const IMAGE: u64 = 0xffff_ffff_8000_0000;

    /// The device untypeds made for `reg` with the image at `kernel`, as
    /// (pointer, size bits).
    fn device_untypeds(reg: Region, kernel: Region) -> Vec<(u64, u64)> {
        made(|s, b| create_device_untypeds(s, b, reg, kernel, 0))
    }

    /// The device untypeds `create_untypeds_for_region` makes for `reg`,
    /// with no cut at all.
    fn uncut_untypeds(reg: Region) -> Vec<(u64, u64)> {
        let no_zeroed = [Region::EMPTY; MAX_REGIONS];
        made(|s, b| create_untypeds_for_region(s, b, true, reg, 0, &no_zeroed, 0))
    }

    fn made(f: impl FnOnce(&mut Mem, &mut Boot)) -> Vec<(u64, u64)> {
        let mut s = Mem(BTreeMap::new());
        let mut b = Boot {
            root_cnode: 0x100_0000,
            slot_pos: 0,
            bi_frame: 0x200_0000,
            next: 0,
            end: 0,
            full: false,
            extra_ut: 0,
            extra_bytes: 0,
            ut_lost: false,
        };
        f(&mut s, &mut b);
        assert!(!b.full && !b.ut_lost);
        (0..b.slot_pos)
            .map(|i| match root_slot(&b, i).cap(&s) {
                Cap::Untyped { ptr, size_bits, free_index: 0, is_device: true } => (ptr, size_bits),
                _ => panic!("slot {i} is not a fresh device untyped"),
            })
            .collect()
    }

    fn meets(ptr: u64, size_bits: u64, r: Region) -> bool {
        let (a, e) = (ptr as u128, ptr as u128 + (1u128 << size_bits));
        a < (r.end as u128) && (r.start as u128) < e
    }

    fn total(uts: &[(u64, u64)]) -> u64 {
        uts.iter().map(|&(_, sb)| 1u64 << sb).sum()
    }

    /// Device memory around the image's physical addresses (on x86_64
    /// [510 GiB, 510 GiB + 4 MiB), the window's top): everything but the
    /// image's part and the pointer-0 page becomes untypeds, none of them
    /// meeting the image's names, including those past 512 GiB whose
    /// pointers wrap.
    #[test]
    fn device_untypeds_skip_kernel_image() {
        let kernel = Region { start: IMAGE, end: IMAGE + (4 << 20) };
        let p = layout::paddr(IMAGE);
        let reg = Region { start: p - GIB, end: p + 3 * GIB };
        let uts = device_untypeds(reg, kernel);
        for &(ptr, sb) in &uts {
            assert!(!meets(ptr, sb, kernel), "untyped {ptr:#x}/{sb} meets the image");
            let pa = layout::paddr(ptr);
            assert!(reg.start <= pa && pa + (1 << sb) <= reg.end);
            assert_eq!(ptr & ((1 << sb) - 1), 0, "pointer alignment");
        }
        assert!(uts.iter().all(|&(ptr, sb)| !meets(ptr, sb, NULL_PAGE)));
        assert_eq!(total(&uts), 4 * GIB - (4 << 20) - 4096);
        // Both sides of the image are there.
        assert!(uts.iter().any(|&(ptr, _)| layout::paddr(ptr) < p));
        assert!(uts.iter().any(|&(ptr, _)| layout::paddr(ptr) >= p + (4 << 20)));
    }

    /// The pointers [0, 4 KiB): the page `create_device_untypeds` cuts.
    const NULL_PAGE: Region = Region { start: 0, end: 4096 };

    /// Device memory across physical 2^64 - PPTR_BASE (x86_64 512 GiB,
    /// AArch64 128 TiB), where pointers wrap to 0: exactly the pointer-0
    /// page is cut, no untyped has pointer 0 or covers it, the rest is
    /// what the two sides give uncut, and every untyped stays page aligned.
    #[test]
    fn device_untypeds_skip_null_page() {
        let z = layout::paddr(0);
        for (lo, hi) in [(GIB, GIB), (4096, 1 << 20), (3 * GIB + 8192, 7 * GIB), (1 << 39, 1 << 39)] {
            let reg = Region { start: z - lo, end: z + hi };
            for kernel in [Region::EMPTY, Region { start: IMAGE, end: IMAGE + (4 << 20) }] {
                let uts = device_untypeds(reg, kernel);
                let cut_image = kernel.start < kernel.end && reg.start <= layout::paddr(kernel.start);
                for &(ptr, sb) in &uts {
                    assert_ne!(ptr, 0, "untyped at pointer 0");
                    assert!(!meets(ptr, sb, NULL_PAGE), "untyped {ptr:#x}/{sb} covers pointer 0");
                    assert!(!meets(ptr, sb, kernel));
                    assert_eq!(ptr & ((1 << sb) - 1), 0, "pointer alignment");
                    assert!(sb >= 12, "page aligned");
                    let pa = layout::paddr(ptr);
                    assert!(reg.start <= pa && pa + (1 << sb) <= reg.end);
                }
                let image = if cut_image { kernel.end - kernel.start } else { 0 };
                assert_eq!(total(&uts), lo + hi - 4096 - image);
                if !cut_image {
                    let mut want = uncut_untypeds(Region { start: reg.start, end: z });
                    want.extend(uncut_untypeds(Region { start: z + 4096, end: reg.end }));
                    assert_eq!(uts, want);
                }
                // Both sides of the page are there.
                assert!(uts.iter().any(|&(ptr, sb)| ptr.wrapping_add(1 << sb) == 0));
                assert!(uts.iter().any(|&(ptr, _)| ptr == 4096));
            }
        }
        // A region ending at, or starting just past, the page is untouched.
        for reg in [Region { start: z - GIB, end: z }, Region { start: z + 4096, end: z + GIB }] {
            assert_eq!(device_untypeds(reg, Region::EMPTY), uncut_untypeds(reg));
        }
    }

    /// Regions away from the image and the pointer-0 page, or no image
    /// given: nothing is cut.
    #[test]
    fn device_untypeds_elsewhere_unchanged() {
        let kernel = Region { start: IMAGE, end: IMAGE + (4 << 20) };
        let p = layout::paddr(IMAGE);
        for reg in [
            Region { start: 0xfe00_0000, end: 0x1_0000_0000 },
            Region { start: p - GIB, end: p },
            Region { start: p + (4 << 20), end: p + GIB },
            Region { start: 0x3800_0000_0000, end: 0x3800_0000_0000 + (1 << 44) },
        ] {
            let with = device_untypeds(reg, kernel);
            assert_eq!(with, device_untypeds(reg, Region::EMPTY));
            assert_eq!(with, uncut_untypeds(reg));
            assert_eq!(total(&with), reg.end - reg.start);
        }
        let reg = Region { start: p - GIB, end: p + GIB };
        assert_eq!(total(&device_untypeds(reg, Region::EMPTY)), 2 * GIB);
    }

    struct CountingMem {
        mem: BTreeMap<u64, u64>,
        reads: core::cell::Cell<u64>,
        zeros: u64,
    }
    impl CountingMem {
        fn new() -> Self {
            Self { mem: BTreeMap::new(), reads: core::cell::Cell::new(0), zeros: 0 }
        }
    }
    impl Store for CountingMem {
        fn read(&self, a: u64) -> u64 {
            self.reads.set(self.reads.get() + 1);
            *self.mem.get(&a).unwrap_or(&0)
        }
        fn write(&mut self, a: u64, v: u64) {
            self.mem.insert(a, v);
        }
        fn zero(&mut self, a: u64, len: u64) {
            self.zeros += 1;
            for i in (0..len).step_by(8) {
                self.mem.insert(a + i, 0);
            }
        }
        fn clear_free(&mut self, a: u64, len: u64) {
            self.zero(a, len);
        }
        fn ks_base(&self) -> u64 {
            0x10_0000
        }
        fn cur_cpu(&self) -> u64 {
            0
        }
    }

    #[test]
    fn clear_dirty_skips_prezeroed_regions_in_o1() {
        let mut s = CountingMem::new();
        let mut zeroed = [Region::EMPTY; MAX_REGIONS];
        let base = layout::pptr(0x8000_0000);
        let size = 32 * GIB;
        zeroed[0] = Region { start: base, end: base + size };
        clear_dirty(&mut s, base, size, &zeroed, 1);
        assert_eq!(s.reads.get(), 0);
        assert_eq!(s.zeros, 0);
    }

    #[test]
    fn clear_dirty_only_reads_and_zeros_non_prezeroed_pages() {
        let mut s = CountingMem::new();
        let base = layout::pptr(0x4000_0000);
        let dtb_page = base + 0x1_0000;
        let len = 1 << 20; // 1 MiB
        s.mem.insert(dtb_page + 16, 0xd00d_feed);
        // Zeroed surrounds the carved-out DTB page.
        let mut zeroed = [Region::EMPTY; MAX_REGIONS];
        zeroed[0] = Region { start: base, end: dtb_page };
        zeroed[1] = Region { start: dtb_page + 4096, end: base + len };
        clear_dirty(&mut s, base, len, &zeroed, 2);
        // Only the carved-out DTB page was read (stopping at the first nonzero word) and zeroed.
        assert_eq!(s.reads.get(), 3);
        assert_eq!(s.zeros, 1);
        assert_eq!(*s.mem.get(&(dtb_page + 16)).unwrap(), 0);
    }
}
