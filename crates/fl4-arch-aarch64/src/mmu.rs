//! Address-space switches, broadcast TLB maintenance (l4h 0015: no IPIs)
//! and user cache maintenance.
use crate::{cpu, percpu};
use core::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use fl4_core::layout;

/// Physical ranges the kernel window maps (for cache maintenance through
/// it), set at boot.
/// As many as the kernel's window can have (fl4-kernel-aarch64 `fl4_boot`,
/// `bootmem::MAX_RANGES`: every memory map entry and then some).
pub const MAX_RANGES: usize = 272;
static RANGES: [(AtomicU64, AtomicU64); MAX_RANGES] = [const { (AtomicU64::new(0), AtomicU64::new(0)) }; MAX_RANGES];
static NRANGES: AtomicUsize = AtomicUsize::new(0);

/// Note a range the window maps; false, with nothing noted, when there is
/// no room (the caller fails the boot).
#[must_use]
pub fn add_window_range(start: u64, end: u64) -> bool {
    let n = NRANGES.load(Ordering::Relaxed);
    if n == MAX_RANGES {
        return false;
    }
    RANGES[n].0.store(start, Ordering::Relaxed);
    RANGES[n].1.store(end, Ordering::Relaxed);
    NRANGES.store(n + 1, Ordering::Release);
    true
}

/// `[start, start + len)` (physical) lies in one range the kernel window
/// maps.
pub fn in_window(start: u64, len: u64) -> bool {
    let n = NRANGES.load(Ordering::Acquire);
    (0..n).any(|i| {
        let s = RANGES[i].0.load(Ordering::Relaxed);
        let e = RANGES[i].1.load(Ordering::Relaxed);
        s <= start && start.wrapping_add(len) <= e && start.wrapping_add(len) >= start
    })
}

/// Any byte of `[start, start + len)` (physical) is in a range the kernel
/// window maps.
pub fn overlaps_window(start: u64, len: u64) -> bool {
    let end = start.saturating_add(len);
    let n = NRANGES.load(Ordering::Acquire);
    (0..n).any(|i| {
        let s = RANGES[i].0.load(Ordering::Relaxed);
        let e = RANGES[i].1.load(Ordering::Relaxed);
        s < end && start < e
    })
}

/// Whole-address-space invalidations so far (`invalidate_asid`).
///
/// ASIDs are the hardware ASIDs, so an ASID deleted while another core
/// still runs its old address space can be refilled there with the old
/// translations after the broadcast invalidation; once the ASID names a
/// new address space, that core would use them. So a core that switches
/// address space after any such invalidation first flushes its own TLB.
/// An invalidation counts itself before it broadcasts; a switch that
/// installs an ASID's new root follows the reassignment under the serial
/// gate, so it sees the count of the invalidation that retired the ASID.
///
/// As on x86_64 (tlb.rs), a switch publishes the core's new TTBR0 value,
/// then reads the count; an invalidation bumps the count, then reads which
/// cores run the ASID (`cores_on`). Both are sequentially consistent, so
/// either the invalidating core sees the switching one and calls it, or
/// the switching core sees the new count and flushes.
static ASID_GEN: AtomicU64 = AtomicU64::new(0);

/// The empty user table (fl4-core's `ks::KERNEL_ROOT`, kernel virtual),
/// which a core runs with ASID 0 once the ASID it ran is retired.
static EMPTY_ROOT: AtomicU64 = AtomicU64::new(0);

/// Set once at boot, before any core runs user code.
pub fn set_empty_root(root: u64) {
    EMPTY_ROOT.store(root, Ordering::Relaxed);
}

/// Run on the address space `root` (kernel virtual) with `asid`.
pub fn switch(root: u64, asid: u64) {
    switch_to(layout::paddr(root) | (asid << 48));
}

/// This core's MMU registers and per-CPU fields, for mmu_switch.rs.
struct Real {
    me: usize,
    pc: &'static percpu::PerCpu,
}

impl Real {
    #[inline(always)]
    fn new() -> Real {
        Real { me: percpu::cpu_index(), pc: percpu::get() }
    }
}

impl crate::mmu_switch::Hw for Real {
    #[inline(always)]
    fn kernel_ttbr1(&self) -> Option<u64> {
        kernel_ttbr1()
    }
    #[inline(always)]
    fn ttbr0(&self) -> u64 {
        percpu::ttbr0(self.me)
    }
    #[inline(always)]
    fn ttbr1(&self) -> Option<u64> {
        percpu::ttbr1(self.me)
    }
    #[inline(always)]
    fn write_ttbr0(&mut self, v: u64) {
        crate::msr!("ttbr0_el1", v);
        cpu::isb();
    }
    #[inline(always)]
    fn write_ttbr1(&mut self, v: u64) {
        crate::msr!("ttbr1_el1", v);
        cpu::isb();
    }
    #[inline(always)]
    fn publish_ttbr0(&mut self, v: u64) {
        percpu::set_ttbr0(v);
    }
    #[inline(always)]
    fn publish_ttbr1(&mut self, v: u64) {
        percpu::set_ttbr1(v);
    }
    #[inline(always)]
    fn asid_gen(&self) -> u64 {
        ASID_GEN.load(Ordering::SeqCst)
    }
    #[inline(always)]
    fn seen_asid_gen(&self) -> u64 {
        self.pc.asid_gen.get()
    }
    #[inline(always)]
    fn set_seen_asid_gen(&mut self, g: u64) {
        self.pc.asid_gen.set(g);
    }
    #[inline(always)]
    fn high_gen(&self) -> u64 {
        HIGH_GEN.load(Ordering::SeqCst)
    }
    #[inline(always)]
    fn seen_high_gen(&self) -> u64 {
        self.pc.high_gen.get()
    }
    #[inline(always)]
    fn set_seen_high_gen(&mut self, g: u64) {
        self.pc.high_gen.set(g);
    }
    #[inline(always)]
    fn high_pair(&self) -> Option<(u64, u64)> {
        match self.pc.high_asid.get() {
            0 => None,
            a => Some((self.pc.high_ttbr1.get(), a)),
        }
    }
    #[inline(always)]
    fn set_high_pair(&mut self, pair: Option<(u64, u64)>) {
        let (t, a) = pair.unwrap_or((0, 0));
        self.pc.high_ttbr1.set(t);
        self.pc.high_asid.set(a);
    }
    #[inline(always)]
    fn gate_held(&self) -> bool {
        self.pc.gate_held.get()
    }
    #[inline(always)]
    fn multi(&self) -> bool {
        crate::smp::multi()
    }
    #[inline(always)]
    fn set_vspace_stale(&mut self) {
        self.pc.vspace_stale.set(true);
    }
    #[inline(always)]
    fn tlbi_asid(&mut self, asid: u64) {
        unsafe { core::arch::asm!("tlbi aside1, {}", "dsb nsh", "isb", in(reg) asid << 48, options(nostack)) };
    }
    #[inline(always)]
    fn tlbi_all(&mut self) {
        unsafe { core::arch::asm!("tlbi vmalle1", "dsb nsh", "isb", options(nostack)) };
    }
}

/// Run on TTBR0 value `v` (table address and ASID); a new value leaves the
/// high window first (mmu_switch.rs `switch_to`).
fn switch_to(v: u64) {
    crate::mmu_switch::switch_to(&mut Real::new(), v);
}

/// Make page-table writes visible to the table walkers before user code
/// runs (exit path).
#[inline(always)]
pub fn publish_tables() {
    cpu::dsb_ishst();
}

pub fn invalidate_page(asid: u64, vaddr: u64) {
    let arg = (asid << 48) | ((vaddr >> 12) & 0xfff_ffff_ffff);
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vae1is, {}", "dsb ish", "isb", in(reg) arg, options(nostack));
    }
}

pub fn invalidate_asid(asid: u64) {
    ASID_GEN.fetch_add(1, Ordering::SeqCst);
    let arg = asid << 48;
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi aside1is, {}", "dsb ish", "isb", in(reg) arg, options(nostack));
    }
}

/// The cores other than this one whose current ASID is `asid`.
pub fn cores_on(asid: u64) -> fl4_core::machine::CoreMask {
    let me = percpu::cpu_index();
    let online = crate::smp::online_mask();
    let mut m = 0;
    for c in 0..percpu::MAX_CPUS {
        if c != me && online & (1 << c) != 0 && percpu::ttbr0(c) >> 48 == asid {
            m |= 1 << c;
        }
    }
    m
}

/// Remote side of `invalidate_asid` (`smp::CALL_ASID`): the broadcast
/// invalidation has run, but if the ASID was deleted its tables can be
/// freed and reused as soon as the call returns, while this core goes on
/// in the kernel with TTBR0 on them: its table walker may still walk them
/// (speculatively too), refilling the TLB from whatever they have become
/// and, with hardware access flags, setting bit 10 of words in them. So
/// it leaves them now for the empty table with ASID 0 (whose switch, the
/// count having moved, also flushes this core's TLB), and the exit sets
/// the address space again from the current thread's VSpace cap.
///
/// Its high window goes too (`switch_high`): the broadcast invalidation of
/// the ASID dropped the translations tagged with it, and ASID 0 never has
/// an `ArmHighVSpace`.
pub fn retired(asid: u64) {
    let pc = percpu::get();
    if asid != 0 && pc.high_asid.get() == asid {
        pc.high_asid.set(0);
        pc.high_ttbr1.set(0);
    }
    if percpu::ttbr0(percpu::cpu_index()) >> 48 == asid {
        switch_high(0, 0);
        switch(EMPTY_ROOT.load(Ordering::Relaxed), 0);
        pc.vspace_stale.set(true);
    }
}

// ---- The high window (TTBR1 EL0 mappings, `ArmHighVSpace`) -----------------
//
// A thread may run with TTBR1 on an `ArmHighVSpace` instead of the
// kernel's tables: a copy of their level-0 entries 0-510 whose entry 511
// points to its own level-1 table, entries 384-495 of which map user pages
// (nG, EL0 permissions, never executable by the kernel). The kernel's own
// TTBR1 leaves level-0 entry 511 invalid (the image and devices are in
// entry 510), so it adds nothing to the TLB there. TCR_EL1.A1 is 0, so the
// window's translations are tagged with the TTBR0 ASID, the same for every
// thread of a VSpace while only some of them have the window, and a TTBR1
// change without an ASID change is not seen by the TLB. So a core keeps
// one fact (`PerCpu::high_ttbr1`, `high_asid`): translations of a window
// may be in its TLB only tagged `high_asid`, all from `high_ttbr1`.
// mmu_switch.rs keeps that true with the order of its register writes and
// flushes only when the pair changes; its module comment has the state
// machine.
//
// Translations of the window itself go when it changes: one page by VA in
// every ASID on every core (`invalidate_high_page`), the whole of it when a
// table is unmapped or the window deleted (`invalidate_high_vspace`, which
// also makes every core running it leave it).

/// The kernel's own TTBR1 (physical), set at boot; `TTBR1_UNSET` before.
static KERNEL_TTBR1: AtomicU64 = AtomicU64::new(TTBR1_UNSET);
/// Not a TTBR1 value (those are page aligned; 0 is one).
const TTBR1_UNSET: u64 = u64::MAX;
/// The kernel's TTBR1 level-0 table and the level-1 table of the kernel
/// image (level-0 entry 510, `KERNEL_VBASE`), as the kernel reaches them
/// (`kernel_ttbr1_entry`).
static KERNEL_L0: AtomicU64 = AtomicU64::new(0);
static KERNEL_L1_TOP: AtomicU64 = AtomicU64::new(0);

/// Set once at boot, after the kernel's tables are complete and before
/// any user code runs: `ttbr1` physical, the tables kernel virtual.
pub fn set_kernel_ttbr1(ttbr1: u64, l0: u64, l1_top: u64) {
    KERNEL_TTBR1.store(ttbr1, Ordering::Relaxed);
    KERNEL_L0.store(l0, Ordering::Relaxed);
    KERNEL_L1_TOP.store(l1_top, Ordering::Relaxed);
}

/// The kernel's own TTBR1; None before boot set it.
pub fn kernel_ttbr1() -> Option<u64> {
    match KERNEL_TTBR1.load(Ordering::Relaxed) {
        TTBR1_UNSET => None,
        v => Some(v),
    }
}

/// Entry `index` of the kernel's TTBR1 level-0 (`level` 0) or top level-1
/// table (`level` 1); 0 before boot set them.
pub fn kernel_ttbr1_entry(level: u64, index: u64) -> u64 {
    let t = if level == 0 { KERNEL_L0.load(Ordering::Relaxed) } else { KERNEL_L1_TOP.load(Ordering::Relaxed) };
    if t == 0 || index >= 512 {
        return 0;
    }
    unsafe { core::ptr::read_volatile((t + index * 8) as *const u64) }
}

/// `invalidate_high_vspace`s so far: the count `switch_high` checks after it
/// publishes its TTBR1 (`PerCpu::high_gen`), apart from `ASID_GEN`, so a
/// window's retirement costs other address-space switches nothing.
static HIGH_GEN: AtomicU64 = AtomicU64::new(0);

/// Run with TTBR1 on the `ArmHighVSpace` at `root` (kernel virtual; 0 =
/// the kernel's own tables) beside TTBR0 ASID `ttbr0_asid`, which this core
/// already runs. (In VHE mode the name TTBR1_EL1 reaches TTBR1_EL2.) The
/// order of writes and flushes: mmu_switch.rs `switch_high`.
pub fn switch_high(root: u64, ttbr0_asid: u64) {
    // A window's physical address may be 0 (`root` == PPTR_BASE); `root`
    // 0 is none.
    let v = if root == 0 { None } else { Some(layout::paddr(root)) };
    crate::mmu_switch::switch_high(&mut Real::new(), v, ttbr0_asid);
}

/// Before this core enters a guest: the kernel's TTBR1 (in nVHE mode the
/// EL2 stub restores the boot TTBR1_EL1 when the guest exits).
pub fn leave_high() {
    let asid = percpu::ttbr0(percpu::cpu_index()) >> 48;
    switch_high(0, asid);
}

/// Drop the translations of high-window address `vaddr`, for every ASID,
/// on every core (VA bits 55:12 in the operand: bit 55 set for TTBR1).
pub fn invalidate_high_page(vaddr: u64) {
    let arg = (vaddr >> 12) & 0xfff_ffff_ffff;
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vaae1is, {}", "dsb ish", "isb", in(reg) arg, options(nostack));
    }
}

/// Remote side of `invalidate_high_vspace` (`smp::CALL_HIGH_VSPACE`): leave
/// the window `ttbr1` if this core runs it; the exit sets the address
/// space again from the current thread's caps.
pub fn high_retired(ttbr1: u64) {
    crate::mmu_switch::retire_window(&mut Real::new(), ttbr1, true);
}

/// No core may go on with the `ArmHighVSpace` at `root` (deleted, or one of
/// its tables unmapped and about to be freed): the cores running it leave
/// it (and their table walkers its tables) before this returns, and every
/// core's TLB is flushed. Under the serial gate.
pub fn invalidate_high_vspace(root: u64) {
    let target = layout::paddr(root);
    // Counted first, as `invalidate_asid` does (`switch_high` publishes its
    // TTBR1, then reads the count).
    HIGH_GEN.fetch_add(1, Ordering::SeqCst);
    let me = percpu::cpu_index();
    let online = crate::smp::online_mask();
    let mut mask: fl4_core::machine::CoreMask = 0;
    for c in 0..percpu::MAX_CPUS {
        if c != me && online & (1 << c) != 0 && percpu::ttbr1(c) == Some(target) {
            mask |= 1 << c;
        }
    }
    if mask != 0 {
        crate::smp::remote_call(crate::smp::CALL_HIGH_VSPACE, target, 0, mask);
    }
    // This core: as the others, its flush the broadcast below.
    crate::mmu_switch::retire_window(&mut Real::new(), target, false);
    // Every core's pairs may name the window's translations: drop them all
    // (the pairs stay true, now naming nothing).
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vmalle1is", "dsb ish", "isb", options(nostack));
    }
}

/// Everything, on every core (boot).
pub fn invalidate_all() {
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vmalle1is", "dsb ish", "isb", options(nostack));
    }
}

// ---- Stage-2 MMU & VMIDs (EL2 VHE / nVHE) ---------------------------------

/// Physical address of the empty 8 KiB Stage-2 root (2 zeroed pages, 8 KiB
/// aligned), set once at boot.
static EMPTY_S2_ROOT: AtomicU64 = AtomicU64::new(0);
/// Unified Stage-2 IPA width & VTCR_EL2.PS decided once on the boot core so
/// heterogeneous APs (`ap.pa_bits >= bsp.pa_bits`) program identical Stage-2
/// geometry and `VTCR_EL2`.
static S2_IPA_BITS: AtomicU64 = AtomicU64::new(0);
static S2_PS: AtomicU64 = AtomicU64::new(u64::MAX);
/// 8-bit VMID table (used when `FEAT_VMID16` is absent).
static VMID_TABLE: crate::vmid::VmidTable = crate::vmid::VmidTable::new();

pub fn set_empty_s2_root(pa: u64) {
    EMPTY_S2_ROOT.store(pa, Ordering::Relaxed);
}

/// Stage-2 IPA width used by all cores (40, 44, or 48), locked on the BSP.
pub fn s2_ipa_bits() -> u64 {
    let cached = S2_IPA_BITS.load(Ordering::Acquire);
    if cached != 0 {
        cached
    } else {
        crate::vmid::s2_ipa_bits_for_pa(cpu::pa_bits())
    }
}

/// Program `VTCR_EL2` and point `VTTBR_EL2` at the empty Stage-2 root.
pub fn init_stage2_core() {
    if !cpu::has_el2() {
        return;
    }
    let (ipa, ps) = {
        let cached = S2_IPA_BITS.load(Ordering::Acquire);
        if cached != 0 {
            (cached, S2_PS.load(Ordering::Relaxed))
        } else {
            let ipa = crate::vmid::s2_ipa_bits_for_pa(cpu::pa_bits());
            let ps = cpu::pa_range(); // capped at 5 (48-bit)
            S2_PS.store(ps, Ordering::Relaxed);
            S2_IPA_BITS.store(ipa, Ordering::Release);
            (ipa, ps)
        }
    };
    let (t0sz, sl0) = match ipa {
        40 => (64 - 40, 0b01u64), // 3 levels, L1 concatenated (2 pages = 8 KiB)
        44 => (64 - 44, 0b10u64), // 4 levels, L0
        _ => (64 - 48, 0b10u64),  // 4 levels, L0
    };
    let vs = if cpu::vmid16() { 1u64 << 19 } else { 0 };
    // RES1(31) | VS(19) | PS[18:16] | TG0=4K(0) | SH0=IS(3) | ORGN0=WB(1) | IRGN0=WB(1) | SL0 | T0SZ
    let vtcr = (1u64 << 31) | vs | (ps << 16) | (3 << 12) | (1 << 10) | (1 << 8) | (sl0 << 6) | t0sz;
    let empty = EMPTY_S2_ROOT.load(Ordering::Relaxed);
    if cpu::is_el2_nvhe() {
        crate::hyp_nvhe::set_vtcr(vtcr, empty);
    } else {
        crate::msr!("vtcr_el2", vtcr);
        crate::msr!("vttbr_el2", empty);
        cpu::isb();
        unsafe { core::arch::asm!("tlbi alle1", "dsb nsh", "isb", options(nostack)) };
    }
    percpu::set_vttbr(empty);
    percpu::set_s2_asid(0);
}

/// Non-allocating lookup of the hardware VMID currently assigned to `asid`.
pub fn lookup_vmid(asid: u64) -> Option<u64> {
    if asid == 0 {
        return Some(0);
    }
    if cpu::vmid16() {
        return Some(asid & 0xffff);
    }
    VMID_TABLE.lookup(asid)
}

/// Allocate or look up the hardware VMID for `asid`. On 8-bit VMID hardware,
/// any allocation (and wrap-around `CALL_VMID_RETIRE`) runs under the serial
/// gate (`arch.rs` `set_stage2_vspace`).
fn hw_vmid_for(asid: u64) -> u64 {
    if let Some(v) = lookup_vmid(asid) {
        return v;
    }
    let (slot, wrapped) = VMID_TABLE.alloc_step(asid);
    if wrapped {
        let new_gen = VMID_TABLE.bump_gen();
        // 1. Synchronously retire every remote core from old-generation VMIDs.
        crate::smp::remote_call(crate::smp::CALL_VMID_RETIRE, 0, 0, u128::MAX);
        // 2. Retire this core to the empty Stage-2 root as well.
        let empty = EMPTY_S2_ROOT.load(Ordering::Relaxed);
        if cpu::is_el2_vhe() {
            crate::msr!("vttbr_el2", empty);
            cpu::isb();
        }
        percpu::set_vttbr(empty);
        percpu::set_s2_asid(0);
        percpu::get().vmid_gen.set(new_gen);
        // 3. Broadcast-invalidate ALL EL1&0 Stage-1+2 TLB entries across all VMIDs.
        if cpu::is_el2_nvhe() {
            crate::hyp_nvhe::tlbi_alle1_is();
        } else {
            unsafe { core::arch::asm!("dsb ishst", "tlbi alle1is", "dsb ish", "isb", options(nostack)) };
        }
        // 4. Only after every core has left old VMIDs and TLBs are clean, reuse slot 1.
        VMID_TABLE.install_slot(slot, new_gen, asid);
    }
    slot
}

/// Remote handler for `CALL_VMID_RETIRE`: if `asid == 0` (8-bit VMID wrap) or
/// this core is running `asid`, switch `VTTBR_EL2` to the empty Stage-2 root,
/// flush local Stage-1+2 TLB (all VMIDs on wrap), and mark `vspace_stale`.
pub fn vmid_retired(asid: u64) {
    if !cpu::has_el2() {
        return;
    }
    let me = percpu::cpu_index();
    if asid == 0 || percpu::s2_asid(me) == asid {
        let empty = EMPTY_S2_ROOT.load(Ordering::Relaxed);
        if cpu::is_el2_nvhe() {
            if asid == 0 {
                crate::hyp_nvhe::tlbi_vmalls12_local();
            }
        } else {
            crate::msr!("vttbr_el2", empty);
            cpu::isb();
            if asid == 0 {
                unsafe { core::arch::asm!("tlbi alle1", "dsb nsh", "isb", options(nostack)) };
            }
        }
        percpu::set_vttbr(empty);
        percpu::set_s2_asid(0);
        let pc = percpu::get();
        pc.vmid_gen.set(VMID_TABLE.generation());
        pc.vspace_stale.set(true);
    }
}

/// Install Stage-2 root (`root` kernel VA, or 0 for empty Stage-2 root) & ASID into `VTTBR_EL2`.
pub fn switch_stage2(root: u64, asid: u64) {
    if !cpu::has_el2() {
        return;
    }
    let (vttbr, pub_asid) = if root == 0 || asid == 0 {
        (EMPTY_S2_ROOT.load(Ordering::Relaxed), 0)
    } else {
        let vmid = hw_vmid_for(asid);
        (layout::paddr(root) | (vmid << 48), asid)
    };
    let me = percpu::cpu_index();
    if cpu::is_el2_vhe() && percpu::vttbr(me) != vttbr {
        crate::msr!("vttbr_el2", vttbr);
        cpu::isb();
    }
    // Publish before reading VMID_GEN (symmetric with Stage-1 `switch_to`).
    percpu::set_vttbr(vttbr);
    percpu::set_s2_asid(pub_asid);
    let g = VMID_TABLE.generation();
    let pc = percpu::get();
    if pc.vmid_gen.get() != g {
        if cpu::is_el2_nvhe() {
            crate::hyp_nvhe::tlbi_vmalls12_local();
        } else {
            unsafe { core::arch::asm!("tlbi alle1", "dsb nsh", "isb", options(nostack)) };
        }
        pc.vmid_gen.set(g);
    }
}

/// Invalidate Stage-2 TLB for one IPA in `asid` across all cores.
pub fn invalidate_stage2_page(asid: u64, ipa: u64) {
    if !cpu::has_el2() || asid == 0 {
        return;
    }
    let Some(vmid) = lookup_vmid(asid) else {
        return;
    };
    let arg = (ipa >> 12) & 0xfff_ffff_ffff;
    if cpu::is_el2_nvhe() {
        crate::hyp_nvhe::tlbi_ipas2(vmid << 48, arg);
        return;
    }
    let old = crate::mrs!("vttbr_el2");
    crate::msr!("vttbr_el2", vmid << 48);
    cpu::isb();
    unsafe {
        core::arch::asm!(
            "dsb ishst",
            "tlbi ipas2e1is, {}",
            "dsb ish",
            "tlbi vmalle1is",
            "dsb ish",
            "isb",
            in(reg) arg,
            options(nostack)
        );
    }
    crate::msr!("vttbr_el2", old);
    cpu::isb();
}

/// Invalidate all Stage-1 + Stage-2 TLB entries for `asid`'s VMID across all
/// cores, and retire `VTTBR_EL2` on every core still running `asid`.
/// Caller holds the serial gate.
pub fn invalidate_stage2_vmid(asid: u64) {
    if !cpu::has_el2() || asid == 0 {
        return;
    }
    let old_vmid = lookup_vmid(asid);
    // 1. Synchronously retire every core currently running `asid` so no table
    //    walker can refill from the retiring Stage-2 tables after TLBI.
    let me = percpu::cpu_index();
    let online = crate::smp::online_mask();
    let mut mask: fl4_core::machine::CoreMask = 0;
    for c in 0..percpu::MAX_CPUS {
        if c != me && online & (1 << c) != 0 && percpu::s2_asid(c) == asid {
            mask |= 1 << c;
        }
    }
    if mask != 0 {
        crate::smp::remote_call(crate::smp::CALL_VMID_RETIRE, asid, 0, mask);
    }
    if percpu::s2_asid(me) == asid {
        let empty = EMPTY_S2_ROOT.load(Ordering::Relaxed);
        if cpu::is_el2_vhe() {
            crate::msr!("vttbr_el2", empty);
            cpu::isb();
        }
        percpu::set_vttbr(empty);
        percpu::set_s2_asid(0);
        percpu::get().vspace_stale.set(true);
    }
    // 2. Broadcast TLBI for `old_vmid`, then release its 8-bit slot (if any).
    if let Some(vmid) = old_vmid {
        if cpu::is_el2_nvhe() {
            crate::hyp_nvhe::tlbi_vmalls12_is(vmid << 48);
        } else {
            let old = crate::mrs!("vttbr_el2");
            crate::msr!("vttbr_el2", vmid << 48);
            cpu::isb();
            unsafe {
                core::arch::asm!("dsb ishst", "tlbi vmalls12e1is", "dsb ish", "isb", options(nostack));
            }
            crate::msr!("vttbr_el2", old);
            cpu::isb();
        }
        if !cpu::vmid16() && (1..256).contains(&vmid) {
            VMID_TABLE.release_slot(vmid);
        }
    }
}

/// seL4 `doFlush` for `len` bytes at user address `vaddr` of (`root`,
/// `asid`), physically `paddr`: through the kernel window when it maps
/// the range, otherwise through the user mapping itself (skipped when
/// `root == 0`, e.g. Stage-2 frames that must never be loaded into TTBR0).
pub fn cache_op(op: u64, root: u64, asid: u64, vaddr: u64, len: u64, paddr: u64) {
    use fl4_core::vspace::{CACHE_CLEAN, CACHE_CLEAN_INVALIDATE, CACHE_INVALIDATE};
    use crate::mmu_switch::CacheVia;
    let ttbr0 = if root == 0 { 0 } else { layout::paddr(root) | (asid << 48) };
    let (va, switched) = match crate::mmu_switch::cache_via(in_window(paddr, len), root, ttbr0) {
        CacheVia::Window => (layout::pptr(paddr), None),
        CacheVia::Skip => return,
        CacheVia::Borrow(v) => {
            // Under the serial gate in an SMP kernel. Page-table writes of
            // this entry reach the walker before it walks them. PSTATE.PAN
            // does not apply ("no effect on ... data cache instructions,
            // except DC ZVA", DDI 0487J.a). A different ASID runs without
            // this core's window meanwhile (mmu_switch.rs `borrow`).
            publish_tables();
            (vaddr, Some(crate::mmu_switch::borrow(&mut Real::new(), v)))
        }
    };
    if op == CACHE_CLEAN {
        cpu::clean_dcache_poc(va, len);
    } else if op == CACHE_INVALIDATE {
        cpu::inval_dcache_poc(va, len);
    } else if op == CACHE_CLEAN_INVALIDATE {
        cpu::clean_inval_dcache_poc(va, len);
    } else {
        cpu::sync_icache(va, len);
    }
    if let Some(old) = switched {
        crate::mmu_switch::unborrow(&mut Real::new(), old);
    }
}
