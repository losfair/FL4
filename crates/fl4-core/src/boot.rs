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

pub const MAX_REGIONS: usize = 32;
pub const ROOT_CNODE_BITS: u64 = fl4_abi::config::ROOT_CNODE_SIZE_BITS;
pub const MAX_BOOTINFO_UNTYPEDS: u64 = 230;
pub const BOOT_THREAD_TIME_SLICE_US: u64 = 5 * 1000;
/// The root task's ASID.
pub const IT_ASID: u64 = 1;
/// CONFIG_PADDR_USER_DEVICE_TOP: 2^47.
pub const PADDR_USER_DEVICE_TOP: u64 = 1 << 47;

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
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BootError {
    NoMemory,
    TooManyCaps,
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

/// Map a page of the initial address space (seL4 `map_it_frame_cap`).
fn map_it_frame<S: Store>(s: &mut S, pml4: u64, vaddr: u64, paddr: u64) {
    let pdpt = next_table(s, pml4, vaddr, 39);
    let pd = next_table(s, pdpt, vaddr, 30);
    let pt = next_table(s, pd, vaddr, 21);
    s.write(entry_addr(pt, vaddr, 12), ((paddr | s.frame_masks().0) & 0x000f_ffff_ffff_f000) | 0x7);
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

/// seL4 `create_it_address_space` (x86_64).
fn create_it_address_space<S: Store>(s: &mut S, b: &mut Boot, it: Region, pml4: u64) -> Cap {
    vspace::copy_global_mappings(s, pml4);
    let cap = Cap::Pml4 { ptr: pml4, mapped: true, asid: IT_ASID };
    write_slot(s, root_slot(b, rs::InitThreadVSpace), cap);
    let first = b.slot_pos;
    // PDPTs, then page directories, then page tables, as seL4 does. The
    // loops count tables rather than step addresses, so they cannot wrap.
    let mut k: u64 = 0;
    while k < 3 {
        let level = 39 - 9 * k;
        let n = n_paging(it, level);
        let base = it.start & !((1u64 << (level & 63)).wrapping_sub(1));
        let mut j: u64 = 0;
        while j < n {
            let v = base.wrapping_add(j << (level & 63));
            let t = alloc(s, b, 12, 1);
            let e = (layout::paddr(t) & 0x000f_ffff_ffff_f000) | 0x7;
            let c = if level == 39 {
                s.write(entry_addr(pml4, v, 39), e);
                Cap::Pdpt { ptr: t, mapped: true, asid: IT_ASID, vaddr: v }
            } else if level == 30 {
                let pdpt = next_table(s, pml4, v, 39);
                s.write(entry_addr(pdpt, v, 30), e);
                Cap::PageDirectory { ptr: t, mapped: true, asid: IT_ASID, vaddr: v }
            } else {
                let pdpt = next_table(s, pml4, v, 39);
                let pd = next_table(s, pdpt, v, 30);
                s.write(entry_addr(pd, v, 21), e);
                Cap::PageTable { ptr: t, mapped: true, asid: IT_ASID, vaddr: v }
            };
            provide_cap(s, b, c);
            j += 1;
        }
        k += 1;
    }
    bi_set(s, b, bi::USER_IMAGE_PAGING, first);
    bi_set(s, b, bi::USER_IMAGE_PAGING + 1, b.slot_pos);
    cap
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

fn create_untypeds_for_region<S: Store>(s: &mut S, b: &mut Boot, device: bool, reg: Region, first: u64) {
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
            if i < MAX_BOOTINFO_UNTYPEDS {
                let paddr = if device { start } else { layout::paddr(start) };
                bi_set(s, b, bi::UNTYPED_LIST + 2 * i, paddr);
                bi_set(s, b, bi::UNTYPED_LIST + 2 * i + 1, size_bits | (if device { 1 << 8 } else { 0 }));
                let ptr = if device { layout::pptr(start) } else { start };
                // Boot untypeds are clean (l4h 0019): RAM is cleared here so
                // the free index can start at 0.
                if !device {
                    clear_dirty(s, start, 1u64 << (size_bits & 63));
                }
                provide_cap(s, b, Cap::Untyped { ptr, size_bits, free_index: 0, is_device: device });
            }
        }
        start = start.wrapping_add(1u64 << (size_bits & 63));
    }
}

/// l4h 0019: clear the pages of [start, start + len) that hold a nonzero
/// word and leave the others alone, so a hypervisor's shared zero pages
/// stay shared. `len` is a power of two of at least 16 bytes.
fn clear_dirty<S: Store>(s: &mut S, start: u64, len: u64) {
    let chunk = if len < 4096 { len } else { 4096 };
    if chunk == 0 {
        return;
    }
    let n = len / chunk;
    let mut i: u64 = 0;
    while i < n {
        let base = start.wrapping_add(i.wrapping_mul(chunk));
        if !all_zero(s, base, chunk / 8) {
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
    let ebits = extra_bi_size_bits(p.extra_bi_len);
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
    let mut b = Boot { root_cnode: 0, slot_pos: 0, bi_frame: 0, next: start, end: start.wrapping_add(l.total), full: false };
    let extra_bi = alloc_root_objects(s, &mut b, l.ebits, l.cnode_bits);
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

/// The root CNode, IO port control, domain and IRQ control caps, and the
/// initial IRQ states; returns the root CNode's cap.
fn init_root_cnode<S: Store>(s: &mut S, b: &Boot) -> Cap {
    let root_cap = Cap::CNode { ptr: b.root_cnode, radix: ROOT_CNODE_BITS, guard_size: 64 - ROOT_CNODE_BITS, guard: 0 };
    write_slot(s, root_slot(b, rs::InitThreadCNode), root_cap);
    write_slot(s, root_slot(b, rs::IOPortControl), Cap::IoPortControl);
    write_slot(s, root_slot(b, rs::Domain), Cap::Domain);
    init_irq_states(s);
    write_slot(s, root_slot(b, rs::IRQControl), Cap::IrqControl);
    root_cap
}

fn init_irq_states<S: Store>(s: &mut S) {
    let mut i = 0;
    while i <= irq::MAX {
        let st = if i == irq::TIMER {
            interrupt::IRQ_TIMER
        } else if i == irq::REMOTE_CALL_IPI || i == irq::RESCHEDULE_IPI {
            interrupt::IRQ_IPI
        } else {
            interrupt::IRQ_INACTIVE
        };
        ks_set(s, ks::IRQ_STATE.wrapping_add(i.wrapping_mul(8)), st);
        i += 1;
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
        create_untypeds_for_region(s, b, true, r, first);
        i += 1;
    }
    let mut i = 0;
    while i < p.n_free && i < MAX_REGIONS as u64 {
        let r = p.free[i as usize];
        create_untypeds_for_region(s, b, false, r, first);
        i += 1;
    }
    bi_set(s, b, bi::UNTYPED, first);
    bi_set(s, b, bi::UNTYPED + 1, b.slot_pos);
    bi_set(s, b, bi::EMPTY, b.slot_pos);
    bi_set(s, b, bi::EMPTY + 1, 1u64 << ROOT_CNODE_BITS);
}

fn objects_init_fpu<S: Store>(s: &mut S, t: Tcb) {
    let f = t.fpu_addr();
    s.write(f, 0x037f);
    s.write(f.wrapping_add(24), 0x0000_ffff_0000_1f80);
}
