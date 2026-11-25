/// AArch64: the 48-bit physical address space; the backend also stops at
/// the processor's own size (ID_AA64MMFR0_EL1.PARange).
pub const PADDR_USER_DEVICE_TOP: u64 = 1 << 48;

/// l4h 0047 on AArch64 too: untypeds past `MAX_BOOTINFO_UNTYPEDS` go in
/// the extra chunk. A bare-metal machine's address space has enough holes
/// that its device untypeds alone can fill the BootInfo's list, and the
/// RAM's, made after them, would be dropped.
pub const EXTRA_UNTYPEDS: u64 = 4096;

/// AArch64: the same walk; the four levels are the VSpace and three page
/// tables.
fn map_it_frame<S: Store>(s: &mut S, pml4: u64, vaddr: u64, paddr: u64) {
    let pdpt = next_table(s, pml4, vaddr, 39);
    let pd = next_table(s, pdpt, vaddr, 30);
    let pt = next_table(s, pd, vaddr, 21);
    s.write(entry_addr(pt, vaddr, 12), vspace::it_page_entry(paddr));
}

/// seL4 `create_it_address_space` (AArch64): page tables at levels 1, 2
/// and 3, all `Cap::PageTable`.
fn create_it_address_space<S: Store>(s: &mut S, b: &mut Boot, it: Region, pml4: u64) -> Cap {
    let cap = Cap::Pml4 { ptr: pml4, mapped: true, asid: IT_ASID };
    write_slot(s, root_slot(b, rs::InitThreadVSpace), cap);
    let first = b.slot_pos;
    let mut k: u64 = 0;
    while k < 3 {
        let level = 39 - 9 * k;
        let n = n_paging(it, level);
        let base = it.start & !((1u64 << (level & 63)).wrapping_sub(1));
        let mut j: u64 = 0;
        while j < n {
            let v = base.wrapping_add(j << (level & 63));
            let t = alloc(s, b, 12, 1);
            let e = vspace::it_table_entry(layout::paddr(t));
            if level == 39 {
                s.write(entry_addr(pml4, v, 39), e);
            } else if level == 30 {
                let l1 = next_table(s, pml4, v, 39);
                s.write(entry_addr(l1, v, 30), e);
            } else {
                let l1 = next_table(s, pml4, v, 39);
                let l2 = next_table(s, l1, v, 30);
                s.write(entry_addr(l2, v, 21), e);
            }
            provide_cap(s, b, Cap::PageTable { ptr: t, mapped: true, asid: IT_ASID, vaddr: v });
            j += 1;
        }
        k += 1;
    }
    bi_set(s, b, bi::USER_IMAGE_PAGING, first);
    bi_set(s, b, bi::USER_IMAGE_PAGING + 1, b.slot_pos);
    cap
}

/// AArch64: no IO ports.
fn init_root_cnode<S: Store>(s: &mut S, b: &Boot) -> Cap {
    let root_cap = Cap::CNode { ptr: b.root_cnode, radix: ROOT_CNODE_BITS, guard_size: 64 - ROOT_CNODE_BITS, guard: 0 };
    write_slot(s, root_slot(b, rs::InitThreadCNode), root_cap);
    write_slot(s, root_slot(b, rs::Domain), Cap::Domain);
    init_irq_states(s);
    write_slot(s, root_slot(b, rs::IRQControl), Cap::IrqControl);
    root_cap
}

/// AArch64 has no TDX.
fn init_tdx_control<S: Store, A: Arch>(_s: &mut S, _a: &A, _b: &Boot) {}

/// AArch64: every core's timer PPI and kernel SGIs.
fn init_irq_states<S: Store>(s: &mut S) {
    let mut i = 0;
    while i <= irq::MAX {
        let id = irq::id(i);
        let st = if i >= irq::BANKED_BASE && id == irq::TIMER_ID {
            interrupt::IRQ_TIMER
        } else if i >= irq::BANKED_BASE && (id == irq::REMOTE_CALL_ID || id == irq::RESCHEDULE_ID) {
            interrupt::IRQ_IPI
        } else if i >= irq::SPI_MIN && i < irq::BANKED_BASE {
            interrupt::IRQ_INACTIVE
        } else if i >= irq::BANKED_BASE && id >= 16 {
            interrupt::IRQ_INACTIVE
        } else {
            // Other SGIs, and the unused numbers below the SPIs.
            interrupt::IRQ_RESERVED
        };
        ks_set(s, ks::IRQ_STATE.wrapping_add(i.wrapping_mul(8)), st);
        i += 1;
    }
}

/// AArch64: the initial FP/SIMD state is all zero, as the TCB already is.
fn objects_init_fpu<S: Store>(s: &mut S, t: Tcb) {
    let _ = (s, t);
}
