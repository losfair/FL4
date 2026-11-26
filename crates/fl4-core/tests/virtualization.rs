// x86_64 only: the AArch64 core has other registers and Arch methods.
#![cfg(not(feature = "aarch64"))]
use fl4_abi::label;
use fl4_core::capability::{Cap, FrameSize};
use fl4_core::error::{Exc, SysError};
use fl4_core::layout::{self, ks, node, reg, tcb};
use fl4_core::machine::{Arch, Store};
use fl4_core::obj::{ks_set, node_set, Ntfn, Sc, Slot, Tcb, NTFN_ACTIVE, NTFN_IDLE};
use fl4_core::{ept, notification, objects, sched, schedcontext, sporadic, vcpu, vspace};
use std::collections::BTreeMap;

#[derive(Default)]
struct Memory {
    words: BTreeMap<u64, u64>,
    cpu: u64,
    frame_masks: (u64, u64),
    writes: usize,
}
impl Store for Memory {
    fn frame_masks(&self) -> (u64, u64) { self.frame_masks }
    fn read(&self, a: u64) -> u64 {
        *self.words.get(&a).unwrap_or(&0)
    }
    fn write(&mut self, a: u64, v: u64) {
        self.writes += 1;
        self.words.insert(a, v);
    }
    fn zero(&mut self, a: u64, len: u64) {
        for i in (0..len).step_by(8) {
            self.write(a + i, 0);
        }
    }
    fn clear_free(&mut self, a: u64, len: u64) {
        self.zero(a, len);
    }
    fn ks_base(&self) -> u64 {
        0x100000
    }
    fn cur_cpu(&self) -> u64 {
        self.cpu
    }
}
#[derive(Default)]
struct Machine {
    backend: u64,
    /// The host's XCR0 (VCPU capability 0); None: 7.
    xcr0: Option<u64>,
    invalidations: Vec<(u64, u64)>,
    dma_transitions: Vec<(u64, u64, bool)>,
}
impl Arch for Machine {
    fn dma_ram(&self, _: u64, _: u64) -> bool { true }
    fn dma_frame(&mut self, base: u64, bytes: u64, shared: bool) {
        self.dma_transitions.push((base, bytes, shared));
    }
    fn virtualization(&self) -> u64 {
        self.backend
    }
    fn vcpu_capability(&self, f: u64) -> u64 {
        match f {
            0 => self.xcr0.unwrap_or(7),
            1 => 48,
            0x486 => 0x20,
            0x488 => 1 << 13,
            0x487 | 0x489 => u32::MAX as u64,
            _ => (u32::MAX as u64) << 32,
        }
    }
    fn invalidate_ept(&mut self, r: u64, m: u64) {
        self.invalidations.push((r, m));
    }
    fn now(&mut self) -> u64 {
        0
    }
    fn set_deadline(&mut self, _: u64) {}
    fn us_to_ticks(&self, x: u64) -> u64 {
        x
    }
    fn ticks_to_us(&self, x: u64) -> u64 {
        x
    }
    fn max_us(&self) -> u64 {
        u64::MAX
    }
    fn kernel_wcet_ticks(&self) -> u64 {
        1
    }
    fn irq_pending(&mut self) -> bool {
        false
    }
    fn take_pending_irq(&mut self) -> u64 {
        u64::MAX
    }
    fn mask_irq(&mut self, _: u64, _: bool) {}
    fn ack_irq(&mut self, _: u64) {}
    fn set_vspace(&mut self, _: u64, _: u64) {}
    fn invalidate_page(&mut self, _: u64, _: u64) {}
    fn invalidate_asid(&mut self, _: u64) {}
    fn invalidate_page_structures(&mut self, _: u64) {}
    fn ioapic_map(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool {
        false
    }
    fn ioapic_map_remapped(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool {
        false
    }
    fn num_ioapics(&self) -> u64 {
        0
    }
    fn ioapic_pins(&self, _: u64) -> u64 {
        0
    }
    fn port_in(&mut self, _: u64, _: u64) -> u64 {
        0
    }
    fn port_out(&mut self, _: u64, _: u64, _: u64) {}
    fn fpu_flush(&mut self, _: u64) {}
    fn fpu_sanitise(&mut self, _: u64) {}
    fn fpu_reload(&mut self, _: u64) {}
    fn fpu_release(&mut self, _: u64) {}
    fn remote_stall(&mut self, _: u64) {}
    fn send_reschedule(&mut self, _: u64) {}
    fn putc(&mut self, _: u64) {}
    fn get_char(&mut self) -> u64 {
        0
    }
    fn halt(&mut self) {}
}
fn fixture(backend: u64) -> (Memory, Machine, Tcb, u64) {
    let mut s = Memory::default();
    let a = Machine {
        backend,
        ..Default::default()
    };
    let t = Tcb(0x20000);
    node_set(&mut s, 0, node::CUR_THREAD, t.0);
    t.slot(tcb::SLOT_BUFFER).set_cap(
        &mut s,
        Cap::Frame {
            ptr: 0x40000,
            size: FrameSize::Small,
            rights: 3,
            is_device: false,
            mapped: false,
            is_ept: false,
            asid: 0,
            vaddr: 0,
        },
    );
    t.set_ipc_buffer(&mut s, 0x1000);
    vcpu::init(&mut s, &a, 0x80000);
    (s, a, t, 0x80000)
}

#[test]
fn sharing_checks_the_untyped_and_destination_before_changing_visibility() {
    let (mut s, mut a, t, _) = fixture(0);
    let ptr = layout::pptr(0x200000);
    let cap = Cap::Untyped { ptr, size_bits: 12, free_index: 0, is_device: false };
    let source = Slot(0x30000);
    let root = Slot(0x30100);
    let dest = Slot(0x50000);
    source.set_cap(&mut s, cap);
    source.set_next_flags(&mut s, Slot(0), true, true);
    root.set_cap(&mut s, Cap::CNode { ptr: dest.0, radix: 4, guard_size: 60, guard: 0 });
    t.set_reg(&mut s, reg::R10, 12);
    s.write(0x40000 + 5 * 8, 1);
    let share = |s: &mut Memory, a: &mut Machine| {
        let cap = source.cap(s);
        fl4_core::untyped::decode(s, a, label::UntypedRetypeShared, 5, source, cap, 0x40000, &[root, Slot(0), Slot(0)])
    };
    assert!(matches!(share(&mut s, &mut a), Err(Exc::Sys(SysError::IllegalOperation))));
    s.frame_masks = (1 << 51, 0);
    t.set_reg(&mut s, reg::R10, 13);
    assert!(matches!(share(&mut s, &mut a), Err(Exc::Sys(SysError::InvalidArgument { .. }))));
    for (bits, count, max) in [(21, 0, 1), (21, 2, 1), (21, 300, 1), (12, 0, 256), (12, 257, 256)] {
        t.set_reg(&mut s, reg::R10, bits);
        s.write(0x40000 + 5 * 8, count);
        assert!(share(&mut s, &mut a) == Err(Exc::Sys(SysError::RangeError { min: 1, max })));
    }
    t.set_reg(&mut s, reg::R10, 12);
    let second = Slot::index(dest.0, 1);
    second.set_cap(&mut s, Cap::Domain);
    s.write(0x40000 + 5 * 8, 2);
    assert!(matches!(share(&mut s, &mut a), Err(Exc::Sys(SysError::DeleteFirst))));
    assert!(matches!(dest.cap(&s), Cap::Null));
    assert!(source.cap(&s) == cap);
    assert!(a.dma_transitions.is_empty());
    second.set_cap(&mut s, Cap::Null);
    s.write(0x40000 + 5 * 8, 1);
    dest.set_cap(&mut s, Cap::Domain);
    assert!(matches!(share(&mut s, &mut a), Err(Exc::Sys(SysError::DeleteFirst))));
    assert!(source.cap(&s) == cap);
    assert!(a.dma_transitions.is_empty());

    dest.set_cap(&mut s, Cap::Null);
    assert!(share(&mut s, &mut a).is_ok());
    assert!(matches!(dest.cap(&s), Cap::Frame { ptr: p, is_device: true, size: FrameSize::Small, .. } if p == ptr));
    t.set_reg(&mut s, reg::R15, 1);
    assert!(matches!(share(&mut s, &mut a), Err(Exc::Sys(SysError::NotEnoughMemory { .. }))));
    let child = dest.cap(&s);
    objects::finalise_cap_object(&mut s, &mut a, child, false);
    assert_eq!(a.dma_transitions, [(ptr, 4096, true)]);
    assert!(fl4_core::cdt::delete(&mut s, &mut a, dest, true).is_ok());
    assert_eq!(a.dma_transitions, [(ptr, 4096, true), (ptr, 4096, false)]);
}

#[test]
fn nested_root_records_each_core_once_without_rewriting_the_page_table() {
    let mut s = Memory::default();
    let mut a = Machine::default();
    let root = 0x8000;
    for cpu in [0, 31, 32, 63] {
        s.cpu = cpu;
        let before = s.writes;
        ept::mark_core(&mut s, root);
        assert_eq!(s.writes, before + 1);
        for _ in 0..16 {
            ept::mark_core(&mut s, root);
        }
        assert_eq!(s.writes, before + 1, "a cached root must remain read-only");
    }
    let before = s.writes;
    ept::invalidate(&mut s, &mut a, root);
    assert_eq!(
        a.invalidations,
        [(root, (1 << 63) | (1 << 32) | (1 << 31) | 1)]
    );
    ept::mark_core(&mut s, root);
    assert_eq!(
        s.writes, before,
        "invalidation retains the lifetime core history"
    );
}
#[test]
fn debug_cap_identify_uses_sel4_virtualization_tags() {
    if !fl4_abi::config::DEBUG_BUILD {
        return;
    }
    let (mut s, mut a, t, v) = fixture(1);
    let cnode = 0x30000;
    t.slot(tcb::SLOT_CTABLE).set_cap(
        &mut s,
        Cap::CNode {
            ptr: cnode,
            radix: 4,
            guard_size: 60,
            guard: 0,
        },
    );
    // seL4's x86_64 structures.bf tags, visible through DebugCapIdentify.
    let mut caps = vec![(Cap::Vcpu { ptr: v }, 21)];
    for (level, tag) in [(0, 29), (39, 27), (30, 25), (21, 23)] {
        caps.push((
            Cap::Ept {
                ptr: layout::pptr(0x1000),
                level,
                mapped: false,
                asid: 0,
                vaddr: 0,
            },
            tag,
        ));
    }
    for (cap, expected) in caps {
        Slot::index(cnode, 1).set_cap(&mut s, cap);
        t.set_reg(&mut s, reg::CAP, 1);
        fl4_core::syscall::handle_syscall(&mut s, &mut a, fl4_abi::syscall::SysDebugCapIdentify);
        assert_eq!(t.reg(&s, reg::CAP), expected);
    }
}
#[test]
fn capability_encoding_preserves_nested_mapping_and_high_asid() {
    for c in [
        Cap::Frame {
            ptr: layout::pptr(0x400000),
            size: FrameSize::Large,
            rights: 3,
            is_device: false,
            mapped: true,
            is_ept: true,
            asid: 0xabcde,
            vaddr: 0x7fffffe00000,
        },
        Cap::Ept {
            ptr: layout::pptr(0x1000),
            level: 39,
            mapped: true,
            asid: 0xfedcb,
            vaddr: 0x7f8000000000,
        },
        Cap::Vcpu {
            ptr: layout::pptr(0x8000),
        },
        Cap::IoPort {
            first: 2,
            last: 65535,
            vcpu: layout::pptr(0x8000),
        },
    ] {
        let (a, b) = c.encode();
        assert!(Cap::decode(a, b) == c);
    }
}
#[test]
fn vmx_users_cannot_enable_host_address_controls_or_unswitched_state() {
    use vcpu::vmx::*;
    let a = Machine {
        backend: 1,
        ..Default::default()
    };
    let write = |f, v| vcpu::sanitize_vmcs(&a, f, v).ok().unwrap();
    let primary = write(CONTROL_PRIMARY_PROCESSOR_CONTROLS, 0);
    assert_eq!(primary & vcpu::PRIMARY_FORCED, vcpu::PRIMARY_FORCED);
    for forbidden in [17, 21] {
        assert_eq!(
            write(CONTROL_PRIMARY_PROCESSOR_CONTROLS, u64::MAX) & (1 << forbidden),
            0
        );
    }
    let secondary = write(CONTROL_SECONDARY_PROCESSOR_CONTROLS, u64::MAX);
    for forbidden in [0, 4, 8, 9, 10, 13, 14, 17, 18, 20, 22, 23, 25] {
        assert_eq!(secondary & (1 << forbidden), 0);
    }
    assert_eq!(secondary & 0x42, 0x42);
    assert_eq!(
        write(CONTROL_CR0_MASK, 0) & vcpu::CR0_OWNED,
        vcpu::CR0_OWNED
    );
    assert_eq!(write(CONTROL_CR4_MASK, 0), !vcpu::cr4_allowed(&a));
    assert_eq!(
        write(GUEST_CR4, u64::MAX) & !((1 << 13) | vcpu::cr4_allowed(&a)),
        0
    );
    assert!(vcpu::sanitize_vmcs(&a, CONTROL_EPT_POINTER, 0).is_err());
    assert!(vcpu::sanitize_vmcs(&a, GUEST_ACTIVITY, 2).is_err());
}
#[test]
fn svm_restricts_addresses_intercepts_and_pat() {
    let a = Machine {
        backend: 2,
        ..Default::default()
    };
    for f in [
        0x40,
        0x48,
        0x58,
        0x90,
        0x98,
        0xa0,
        0xb0,
        0xb8,
        0xc0,
        0xe0,
        0xf0,
        0xf8,
        0x108,
        0x1000,
        u64::MAX,
    ] {
        assert!(vcpu::sanitize_vmcb(&a, f, 0, u64::MAX).is_err());
    }
    for val in [0, 1, u64::MAX, 0x5555555555555555] {
        let cr = vcpu::sanitize_vmcb(&a, 0, 0, val).ok().unwrap();
        assert_eq!(cr & 0xffffffff00100000, 0xffffffff00100000);
        let misc = vcpu::sanitize_vmcb(&a, 8, 0, val).ok().unwrap();
        assert_eq!(
            misc & (vcpu::EXCEPTIONS | (vcpu::SVM_I1_FORCED << 32)),
            vcpu::EXCEPTIONS | (vcpu::SVM_I1_FORCED << 32)
        );
        assert_eq!(
            vcpu::sanitize_vmcb(&a, 0x548, 0, val).ok().unwrap() & !vcpu::cr4_allowed(&a),
            0
        );
    }
    assert!(vcpu::sanitize_vmcb(&a, 0x620, 0, 0x800000000000).is_err());
    assert!(vcpu::sanitize_vmcb(&a, 0x668, 0, 0x0202020202020202).is_err());
}
/// Audit r11 F1: guest INVLPGB and TLBSYNC (broadcast invalidation,
/// tagged with the ASID every FL4 VCPU shares) raise #UD unless VMCB
/// 0x090 bit 7 enables them. FL4 sets that word once, to nested paging
/// only, and the VMM cannot write it.
#[test]
fn svm_guests_cannot_enable_broadcast_tlb_invalidation() {
    let (s, _, _, v) = fixture(2);
    assert_eq!(vcpu::get(&s, v, vcpu::svm::NESTED_CTL), 1);
    let a = Machine { backend: 2, ..Default::default() };
    for val in [1 << 7, 0x81, u64::MAX] {
        assert!(vcpu::sanitize_vmcb(&a, vcpu::svm::NESTED_CTL, 1, val).is_err());
    }
}

/// The deferred exit IBPB is the VCPU holder's choice (WriteMSR of
/// MSR_VM_IBPB_DEFER, 0 or 1), off after retype, on both backends; and a
/// guest may have CR4.PKE.
#[test]
fn vm_ibpb_defer_is_the_holders_choice() {
    for backend in [1, 2] {
        let (mut s, mut a, t, v) = fixture(backend);
        assert_eq!(vcpu::get(&s, v, vcpu::VM_IBPB_DEFER), 0, "off after retype");
        for (val, ok) in [(1, true), (0, true), (2, false), (u64::MAX, false), (1, true)] {
            t.set_reg(&mut s, reg::R10, vcpu::MSR_VM_IBPB_DEFER);
            t.set_reg(&mut s, reg::R8, val);
            let r = vcpu::decode(&mut s, &mut a, label::X86VCPUWriteMSR, 2, v, true, 0, &[Slot(0); 3]);
            assert_eq!(r.is_ok(), ok, "backend {backend}, {val:#x}");
        }
        assert_eq!(vcpu::get(&s, v, vcpu::VM_IBPB_DEFER), 1, "a refused value leaves it");
        t.set_reg(&mut s, reg::R10, vcpu::MSR_VM_IBPB_DEFER);
        vcpu::decode(&mut s, &mut a, label::X86VCPUReadMSR, 1, v, true, 0, &[Slot(0); 3]).ok().unwrap();
        assert_eq!(t.reg(&s, reg::R10), 1, "ReadMSR");
    }
    assert_ne!(vcpu::CR4_ALLOWED & (1 << 22), 0, "CR4.PKE");
    // Only with PKRU in the host's XCR0, which switches it with the FPU.
    for (xcr0, pke) in [(7, false), (0x207, true)] {
        let a = Machine { backend: 2, xcr0: Some(xcr0), ..Default::default() };
        assert_eq!(vcpu::sanitize_vmcb(&a, 0x548, 0, 1 << 22).ok().unwrap() & (1 << 22) != 0, pke, "SVM, XCR0 {xcr0:#x}");
        assert_eq!(vcpu::sanitize_vmcs(&a, fl4_core::vcpu::vmx::CONTROL_CR4_MASK, 0).ok().unwrap() & (1 << 22) == 0, pke, "VMX mask, XCR0 {xcr0:#x}");
    }
}

#[test]
fn xcr0_groups_and_canonical_width_match_hardware_rules() {
    for x in [0, 4, 5, 0x21, 0x81, 0xe3, 0x20001, 0x40001] {
        assert!(!vcpu::valid_xcr0(x, u64::MAX));
    }
    for x in [1, 3, 7, 0xe7, 0x19, 0x60001] {
        assert!(vcpu::valid_xcr0(x, u64::MAX));
    }
    assert!(!vcpu::valid_xcr0(7, 3));
    assert!(!vcpu::canonical(0x800000000000, 48));
    assert!(vcpu::canonical(0x800000000000, 57));
    assert!(!vcpu::canonical(0x0200000000000000, 57));
}
#[test]
fn svm_software_paging_writes_flush_even_when_the_value_is_unchanged() {
    let (mut s, mut a, t, v) = fixture(2);
    for off in [
        vcpu::svm::CR0,
        vcpu::svm::CR3,
        vcpu::svm::CR4,
        vcpu::svm::EFER,
        vcpu::svm::G_PAT,
        vcpu::svm::RIP,
    ] {
        let value = vcpu::get(&s, v, off);
        vcpu::set(&mut s, v, vcpu::SVM_CPU, 1);
        t.set_reg(&mut s, reg::R10, off);
        t.set_reg(&mut s, reg::R8, value);
        vcpu::decode(
            &mut s,
            &mut a,
            label::X86VCPUWriteVMCB,
            2,
            v,
            true,
            0,
            &[Slot(0); 3],
        )
        .ok()
        .unwrap();
        assert_eq!(
            vcpu::get(&s, v, vcpu::SVM_CPU),
            if off == vcpu::svm::RIP { 1 } else { 0 }
        );
    }
    vcpu::set(&mut s, v, vcpu::SVM_CPU, 1);
    vcpu::decode(
        &mut s,
        &mut a,
        label::X86VCPUFlushTLB,
        0,
        v,
        true,
        0,
        &[Slot(0); 3],
    )
    .ok()
    .unwrap();
    assert_eq!(vcpu::get(&s, v, vcpu::SVM_CPU), 0);
    vcpu::set(&mut s, v, vcpu::SVM_CPU, 1);
    vcpu::reset_svm(&mut s, v);
    assert_eq!(vcpu::get(&s, v, vcpu::SVM_CPU), 0);
}

/// VMX tags guest translations with VPID 1 (fl4-arch-x86_64 `vm`), kept
/// while `SVM_CPU` names the core: as for SVM's ASID, a software write of
/// a paging register, FlushTLB and unbinding the VCPU revoke it; other
/// fields do not. The VMM never controls "enable VPID".
#[test]
fn vmx_software_paging_writes_flushes_and_unbinding_revoke_the_vpid() {
    use fl4_core::vcpu::vmx::*;
    let (mut s, mut a, t, v) = fixture(1);
    for (f, flush) in [
        (GUEST_CR0, true),
        (GUEST_CR3, true),
        (GUEST_CR4, true),
        (GUEST_EFER, true),
        (GUEST_PAT, true),
        (GUEST_PDPTE0, true),
        (GUEST_PDPTE1, true),
        (GUEST_PDPTE2, true),
        (GUEST_PDPTE3, true),
        (CONTROL_ENTRY_CONTROLS, true),
        (GUEST_RIP, false),
        (GUEST_RSP, false),
        (CONTROL_PRIMARY_PROCESSOR_CONTROLS, false),
    ] {
        let value = vcpu::read_vmcs(&s, v, f);
        vcpu::set(&mut s, v, vcpu::SVM_CPU, 1);
        t.set_reg(&mut s, reg::R10, f);
        t.set_reg(&mut s, reg::R8, value);
        vcpu::decode(&mut s, &mut a, label::X86VCPUWriteVMCS, 2, v, true, 0, &[Slot(0); 3]).ok().unwrap();
        assert_eq!(vcpu::get(&s, v, vcpu::SVM_CPU), if flush { 0 } else { 1 }, "field {f:#x}");
    }
    // A refused write changes nothing.
    vcpu::set(&mut s, v, vcpu::SVM_CPU, 1);
    t.set_reg(&mut s, reg::R10, GUEST_ACTIVITY);
    t.set_reg(&mut s, reg::R8, 2);
    assert!(vcpu::decode(&mut s, &mut a, label::X86VCPUWriteVMCS, 2, v, true, 0, &[Slot(0); 3]).is_err());
    assert_eq!(vcpu::get(&s, v, vcpu::SVM_CPU), 1);
    // ReadVMCS of a paging register keeps it.
    t.set_reg(&mut s, reg::R10, GUEST_CR3);
    vcpu::decode(&mut s, &mut a, label::X86VCPUReadVMCS, 1, v, true, 0, &[Slot(0); 3]).ok().unwrap();
    assert_eq!(vcpu::get(&s, v, vcpu::SVM_CPU), 1);
    vcpu::decode(&mut s, &mut a, label::X86VCPUFlushTLB, 0, v, true, 0, &[Slot(0); 3]).ok().unwrap();
    assert_eq!(vcpu::get(&s, v, vcpu::SVM_CPU), 0);
    // "Enable VPID" (secondary bit 5) stays out of the image.
    t.set_reg(&mut s, reg::R10, CONTROL_SECONDARY_PROCESSOR_CONTROLS);
    t.set_reg(&mut s, reg::R8, u64::MAX);
    vcpu::decode(&mut s, &mut a, label::X86VCPUWriteVMCS, 2, v, true, 0, &[Slot(0); 3]).ok().unwrap();
    assert_eq!(vcpu::read_vmcs(&s, v, CONTROL_SECONDARY_PROCESSOR_CONTROLS) & (1 << 5), 0);
    assert!(!vcpu::WRITE_FIELDS.contains(&CONTROL_VPID) && !vcpu::READ_FIELDS.contains(&CONTROL_VPID));
    // Unbinding.
    for backend in [1, 2] {
        let (mut s, mut a, t, v) = fixture(backend);
        vcpu::set(&mut s, v, vcpu::TCB, t.0);
        s.write(t.0 + tcb::VCPU, v);
        vcpu::set(&mut s, v, vcpu::SVM_CPU, 1);
        vcpu::detach(&mut s, &mut a, t);
        assert_eq!(vcpu::bound(&s, t), 0);
        assert_eq!(vcpu::get(&s, v, vcpu::SVM_CPU), 0, "backend {backend}");
    }
}

#[test]
fn vmcb_bulk_read_rejects_overflow_and_hides_physical_pointers() {
    let (mut s, mut a, t, v) = fixture(2);
    for (off, count) in [(u64::MAX, 1), (3, 1), (0, 65), (0, 0), (0x6e0, 2)] {
        t.set_reg(&mut s, reg::R10, off);
        t.set_reg(&mut s, reg::R8, count);
        assert!(matches!(
            vcpu::decode(
                &mut s,
                &mut a,
                label::X86VCPUReadVMCB,
                2,
                v,
                true,
                0,
                &[Slot(0); 3]
            ),
            Err(Exc::Sys(SysError::InvalidArgument { arg: 0 }))
        ));
    }
    vcpu::set(&mut s, v, 0x40, 0xdead000);
    t.set_reg(&mut s, reg::R10, 0x40);
    t.set_reg(&mut s, reg::R8, 2);
    assert!(vcpu::decode(
        &mut s,
        &mut a,
        label::X86VCPUReadVMCB,
        2,
        v,
        true,
        0,
        &[Slot(0); 3]
    )
    .is_ok());
    assert_eq!(t.reg(&s, reg::R10), 0);
    assert_eq!(t.reg(&s, reg::R8), 0);
}
#[test]
fn detach_reports_pending_exit_before_clearing_the_binding() {
    let (mut s, mut a, t, v) = fixture(2);
    vcpu::set(&mut s, v, vcpu::TCB, t.0);
    s.write(t.0 + tcb::VCPU, v);
    t.set_state(&mut s, sched::TS_RUNNING_VM);
    vcpu::set(&mut s, v, vcpu::PENDING, 1);
    vcpu::set(&mut s, v, vcpu::VALID, 1);
    vcpu::set(&mut s, v, vcpu::EXIT, 0x1234);
    vcpu::set(&mut s, v, vcpu::EXIT + 24, 0x41);
    vcpu::detach(&mut s, &mut a, t);
    assert_eq!(vcpu::bound(&s, t), 0);
    assert_eq!(t.state(&s), sched::TS_RUNNING);
    assert_eq!(t.reg(&s, reg::MSG_INFO), 1);
    assert_eq!(t.reg(&s, reg::R10), 0x1234);
    assert_eq!(t.reg(&s, reg::R15), 0x41);
}
#[test]
fn notification_before_entry_cannot_reuse_an_old_exits_fields() {
    let (mut s, a, t, v) = fixture(2);
    s.write(t.0 + tcb::VCPU, v);
    for i in 0..30 {
        vcpu::set(&mut s, v, vcpu::EXIT + i * 8, 0xdead);
    }
    vcpu::set(&mut s, v, vcpu::svm::RIP, 0x1234);
    vcpu::report(&mut s, &a, t, 0x42);
    assert_eq!(t.reg(&s, reg::MSG_INFO), 0);
    assert_eq!(t.reg(&s, reg::BADGE), 0x42);
    assert_eq!(t.reg(&s, reg::R9), 0);
    assert_eq!(s.read(0x40000 + 8 + 5 * 8), 0);
}
/// The ASID word (with the flush decision) and the clean bits are rewritten
/// on every entry from the core's cache state: ReadVMCB must not show them,
/// or one VMM learns whether another VCPU ran on the core. WriteVMCB
/// rejects them like the physical pointers.
#[test]
fn vmcb_hides_per_core_asid_and_clean_bits() {
    let (mut s, mut a, t, v) = fixture(2);
    vcpu::set(&mut s, v, vcpu::svm::ASID, 1 | (1 << 32));
    vcpu::set(&mut s, v, vcpu::svm::CLEAN, 0x3f);
    vcpu::set(&mut s, v, vcpu::svm::TSC_OFFSET, 0x77);
    for f in [vcpu::svm::ASID, vcpu::svm::CLEAN] {
        assert!(vcpu::vmcb_hidden(f));
        assert!(matches!(vcpu::sanitize_vmcb(&a, f, 0, 0), Err(Exc::Sys(SysError::IllegalOperation))));
        t.set_reg(&mut s, reg::R10, f);
        t.set_reg(&mut s, reg::R8, 1);
        assert!(matches!(
            vcpu::decode(&mut s, &mut a, label::X86VCPUWriteVMCB, 2, v, true, 0, &[Slot(0); 3]),
            Err(Exc::Sys(SysError::IllegalOperation))
        ));
    }
    assert_eq!(vcpu::get(&s, v, vcpu::svm::ASID), 1 | (1 << 32));
    assert_eq!(vcpu::get(&s, v, vcpu::svm::CLEAN), 0x3f);
    // A bulk read of 0x050..0x0c8: TSC_OFFSET (MR0) shows, the ASID word
    // (MR1) and the clean bits (MR14, in the IPC buffer) read as 0.
    t.set_reg(&mut s, reg::R10, 0x050);
    t.set_reg(&mut s, reg::R8, 16);
    s.write(0x40000 + 8 + 14 * 8, 0xdead);
    assert!(vcpu::decode(&mut s, &mut a, label::X86VCPUReadVMCB, 2, v, true, 0, &[Slot(0); 3]).is_ok());
    assert_eq!(t.reg(&s, reg::R10), 0x77);
    assert_eq!(t.reg(&s, reg::R8), 0);
    assert_eq!(s.read(0x40000 + 8 + 14 * 8), 0);
}

fn bind_ntfn(s: &mut Memory, t: Tcb) -> Ntfn {
    let n = Ntfn(0x60000);
    notification::bind_notification(s, t, n.0);
    n
}

#[test]
fn svm_vmenter_preserves_the_exception_error_code_for_each_caller() {
    for (request, input, error) in [(0, (0x30 << 32) | 0x8000_0b0d, 0x30),
                                    (vcpu::NUM_MRS, 0x8000_0b0d, 0x28)] {
        let (mut s, mut a, t, v) = fixture(2);
        s.write(t.0 + tcb::VCPU, v);
        vcpu::set(&mut s, v, vcpu::TCB, t.0);
        let n = bind_ntfn(&mut s, t);
        let event = 0x8000_0b0d; // #GP with an error code
        t.set_reg(&mut s, reg::R10, vcpu::svm::EVENT_INJ);
        t.set_reg(&mut s, reg::R8, (0x28 << 32) | event);
        assert!(vcpu::decode(&mut s, &mut a, label::X86VCPUWriteVMCB, 2, v, true, 0, &[Slot(0); 3]).is_ok());
        n.set_state(&mut s, NTFN_ACTIVE);
        t.set_reg(&mut s, reg::MSG_INFO, request);
        t.set_reg(&mut s, reg::R9, input);
        vcpu::enter(&mut s, &mut a, t);
        assert_eq!(vcpu::get(&s, v, vcpu::svm::EVENT_INJ), (error << 32) | event);
        assert_eq!(t.reg(&s, reg::R9), input);
    }
}

/// A pending signal returns the caller's MRs in the standard ABI and
/// the staged VCPU registers in the l4h ABI. Poison the old exit frame
/// and the IPC buffer so neither can pass for the current registers.
#[test]
fn vmenter_with_a_pending_signal() {
    for (backend, request) in [(1, 0), (2, 0), (1, vcpu::NUM_MRS), (2, vcpu::NUM_MRS)] {
        let (mut s, mut a, t, v) = fixture(backend);
        t.set_reg(&mut s, reg::MSG_INFO, request);
        s.write(t.0 + tcb::VCPU, v);
        vcpu::set(&mut s, v, vcpu::TCB, t.0);
        let n = bind_ntfn(&mut s, t);
        n.set_state(&mut s, NTFN_ACTIVE);
        n.set_badge(&mut s, 0x42);
        t.set_state(&mut s, sched::TS_RUNNING);
        for i in 0..30 {
            vcpu::set(&mut s, v, vcpu::EXIT + i * 8, 0xdead);
        }
        for i in 0..15 {
            vcpu::set(&mut s, v, vcpu::REGS + i * 8, 0x1230 + i);
        }
        // MR0..3 are R10, R8, R9 and R15; MR4.. are in the IPC buffer.
        t.set_reg(&mut s, reg::R10, 0x1234);
        t.set_reg(&mut s, reg::R8, 0xffff_ffff);
        t.set_reg(&mut s, reg::R9, 0x8000_0030);
        t.set_reg(&mut s, reg::R15, 0x5555);
        for i in 4..30 {
            s.write(0x40000 + 8 + i * 8, 0x1000 + i);
        }
        vcpu::enter(&mut s, &mut a, t);
        assert_eq!(t.state(&s), sched::TS_RUNNING);
        assert_eq!(n.state(&s), NTFN_IDLE);
        assert_eq!(t.reg(&s, reg::MSG_INFO), 0);
        assert_eq!(t.reg(&s, reg::BADGE), 0x42);
        assert_eq!(t.reg(&s, reg::R10), 0x1234);
        assert_eq!(t.reg(&s, reg::R9), 0x8000_0030);
        if request == vcpu::NUM_MRS {
            let ctl = if backend == 2 {
                vcpu::get(&s, v, vcpu::svm::INTERCEPT_EXC) >> 32
            } else {
                vcpu::read_vmcs(&s, v, vcpu::vmx::CONTROL_PRIMARY_PROCESSOR_CONTROLS)
            };
            assert_eq!(t.reg(&s, reg::R8), ctl);
            assert_eq!(t.reg(&s, reg::R15), if backend == 2 { 0x60 } else { 1 });
            for i in 4..30 {
                let expected = match i {
                    7 => 2, // initial RFLAGS
                    10..=24 => 0x1230 + i - 10,
                    _ => 0,
                };
                assert_eq!(s.read(0x40000 + 8 + i * 8), expected, "MR{i}");
            }
        } else {
            assert_eq!(t.reg(&s, reg::R8), 0xffff_ffff);
            assert_eq!(t.reg(&s, reg::R15), 0x5555);
            for i in 4..30 {
                assert_eq!(s.read(0x40000 + 8 + i * 8), 0x1000 + i, "MR{i}");
            }
        }
        let rip = if backend == 2 {
            vcpu::get(&s, v, vcpu::svm::RIP)
        } else {
            vcpu::read_vmcs(&s, v, vcpu::vmx::GUEST_RIP)
        };
        assert_eq!(rip, 0x1234);
        // Without a signal the thread enters RunningVM.
        vcpu::enter(&mut s, &mut a, t);
        assert_eq!(t.state(&s), sched::TS_RUNNING_VM);
    }
}

/// After a host exit the standard ABI returns the event staged for
/// re-entry. The l4h ABI reports interrupted delivery in MR27/28 so the
/// VMM can requeue the event with its error code.
#[test]
fn a_notification_after_a_host_exit() {
    for (backend, request) in [(1, 0), (2, 0), (1, vcpu::NUM_MRS), (2, vcpu::NUM_MRS)] {
        let (mut s, a, t, v) = fixture(backend);
        t.set_reg(&mut s, reg::MSG_INFO, request);
        s.write(t.0 + tcb::VCPU, v);
        vcpu::set(&mut s, v, vcpu::TCB, t.0);
        t.set_state(&mut s, sched::TS_RUNNING_VM);
        for i in 0..30 {
            vcpu::set(&mut s, v, vcpu::EXIT + i * 8, 0x2000 + i);
        }
        vcpu::set(&mut s, v, vcpu::VALID, 1);
        let ctl = if backend == 2 {
            vcpu::set(&mut s, v, vcpu::svm::RIP, 0x25);
            vcpu::set(&mut s, v, vcpu::svm::EVENT_INJ, 0x8000_0b0e);
            vcpu::get(&s, v, vcpu::svm::INTERCEPT_EXC) >> 32
        } else {
            use vcpu::vmx::*;
            vcpu::write_vmcs(&mut s, v, GUEST_RIP, 0x25);
            vcpu::write_vmcs(&mut s, v, CONTROL_ENTRY_INTERRUPTION_INFO, 0x8000_0b0e);
            vcpu::read_vmcs(&s, v, CONTROL_PRIMARY_PROCESSOR_CONTROLS)
        };
        assert_ne!(ctl, 0);
        vcpu::set(&mut s, v, vcpu::EXIT, 0x25);
        vcpu::set(&mut s, v, vcpu::EXIT + 8, ctl);
        vcpu::set(&mut s, v, vcpu::EXIT + 2 * 8, if backend == 2 { 0x28 << 32 } else { 0 });
        vcpu::set(&mut s, v, vcpu::EXIT + 27 * 8, 0x8000_0b0e);
        t.set_reg(&mut s, reg::R15, 0x5555);
        for i in 4..30 {
            s.write(0x40000 + 8 + i * 8, 0x1000 + i);
        }
        vcpu::report(&mut s, &a, t, 0x42);
        assert_eq!(t.state(&s), sched::TS_RUNNING);
        assert_eq!(t.reg(&s, reg::MSG_INFO), 0);
        assert_eq!(t.reg(&s, reg::BADGE), 0x42);
        assert_eq!(t.reg(&s, reg::R10), 0x25);
        assert_eq!(t.reg(&s, reg::R8), ctl);
        if request == vcpu::NUM_MRS {
            assert_eq!(t.reg(&s, reg::R9), 0);
            assert_eq!(t.reg(&s, reg::R15), if backend == 2 { 0x60 } else { 1 });
            for i in 4..30 {
                let expected = match i {
                    4 | 6 | 25 | 26 => 0,
                    27 => 0x8000_0b0e,
                    _ => 0x2000 + i,
                };
                assert_eq!(s.read(0x40000 + 8 + i * 8), expected, "MR{i}");
            }
        } else {
            assert_eq!(t.reg(&s, reg::R9), 0x8000_0b0e);
            assert_eq!(t.reg(&s, reg::R15), 0x5555);
            for i in 4..30 {
                assert_eq!(s.read(0x40000 + 8 + i * 8), 0x1000 + i, "MR{i}");
            }
        }
    }
}

/// seL4 `sendSignal` (CONFIG_VTX): a signal to a RunningVM thread on the
/// current core completes its VMEnter at once, so two signals give two
/// results (badge 1 now, badge 2 left active for the next VMEnter), not
/// one with the OR of both. The l4h ABI also completes a descheduled
/// remote thread immediately. A running remote thread or a pending
/// hardware exit leaves the badge for the owner's check.
#[test]
fn vm_signals_respect_the_running_core_and_pending_exit() {
    let setup = |cpu: u64, affinity: u64, current: bool, pending: bool| {
        let (mut s, a, t, v) = fixture(2);
        s.cpu = cpu;
        s.write(t.0 + tcb::VCPU, v);
        vcpu::set(&mut s, v, vcpu::TCB, t.0);
        vcpu::set(&mut s, v, vcpu::svm::RIP, 0x25);
        vcpu::set(&mut s, v, vcpu::PENDING, pending as u64);
        vcpu::set(&mut s, v, vcpu::VALID, pending as u64);
        t.set_affinity(&mut s, affinity);
        node_set(&mut s, affinity, node::CUR_THREAD, if current { t.0 } else { 0x30000 });
        t.set_state(&mut s, sched::TS_RUNNING_VM);
        t.set_reg(&mut s, reg::R15, 0x5555);
        let n = bind_ntfn(&mut s, t);
        (s, a, t, n)
    };
    for request in [0, vcpu::NUM_MRS] {
        let full = request == vcpu::NUM_MRS;
        for (cpu, affinity, current, pending) in [
            (0, 0, true, false), (0, 1, false, false), (1, 0, true, false),
            (0, 0, true, true), (0, 1, false, true),
        ] {
            let (mut s, mut a, t, n) = setup(cpu, affinity, current, pending);
            t.set_reg(&mut s, reg::MSG_INFO, request);
            notification::send_signal(&mut s, &mut a, n.0, 1);
            if !pending && (cpu == affinity || (full && !current)) {
                assert_eq!(t.state(&s), sched::TS_RUNNING);
                assert_eq!(t.reg(&s, reg::MSG_INFO), 0);
                assert_eq!(t.reg(&s, reg::BADGE), 1);
                assert_eq!(t.reg(&s, reg::R10), 0x25);
                assert_eq!(t.reg(&s, reg::R15), if full { 0x60 } else { 0x5555 });
                assert_eq!(n.state(&s), NTFN_IDLE);
                notification::send_signal(&mut s, &mut a, n.0, 2);
                assert_eq!(t.reg(&s, reg::BADGE), 1);
                assert_eq!(n.state(&s), NTFN_ACTIVE);
                assert_eq!(n.badge(&s), 2);
                s.cpu = affinity;
                t.set_reg(&mut s, reg::MSG_INFO, request);
                vcpu::enter(&mut s, &mut a, t);
                assert_eq!(t.reg(&s, reg::BADGE), 2);
                continue;
            }
            notification::send_signal(&mut s, &mut a, n.0, 2);
            assert_eq!(t.state(&s), sched::TS_RUNNING_VM);
            assert_eq!(n.state(&s), NTFN_ACTIVE);
            assert_eq!(n.badge(&s), 3);
            if pending {
                // The saved exit is reported first; the signal waits.
                s.cpu = affinity;
                vcpu::check(&mut s, &mut a, t);
                assert_eq!(t.reg(&s, reg::MSG_INFO), 1);
                assert_eq!(n.state(&s), NTFN_ACTIVE);
            }
        }
    }
}

/// The rest of seL4's same-core RunningVM case: a passive thread (no SC)
/// gets the notification's SC (`maybeDonateSchedContext`), is switched to
/// (`possibleSwitchTo`), and a sporadic SC has its refills unblocked.
#[test]
fn same_core_vm_signal_donates_the_notifications_sc_and_switches_to_it() {
    let (mut s, mut a, t, v) = fixture(2);
    s.write(t.0 + tcb::VCPU, v);
    vcpu::set(&mut s, v, vcpu::TCB, t.0);
    vcpu::set(&mut s, v, vcpu::svm::RIP, 0x25);
    t.set_state(&mut s, sched::TS_RUNNING_VM);
    // Another thread with its own SC runs on this core; `t` is passive.
    let other = Tcb(0x30000);
    let other_sc = Sc(0xa0000);
    other.set_state(&mut s, sched::TS_RUNNING);
    other.set_sc(&mut s, other_sc.0);
    node_set(&mut s, 0, node::CUR_THREAD, other.0);
    node_set(&mut s, 0, node::CUR_SC, other_sc.0);
    let n = bind_ntfn(&mut s, t);
    let sc = Sc(0x90000);
    sporadic::refill_new(&mut s, sc, 2, 1000, 10000);
    sc.set_sporadic(&mut s, 1);
    schedcontext::bind_ntfn(&mut s, sc, n);
    node_set(&mut s, 0, node::CUR_TIME, 500);
    assert_eq!(t.sc(&s), 0);
    assert_eq!(sporadic::head(&s, sc).time, 0);

    notification::send_signal(&mut s, &mut a, n.0, 7);
    assert_eq!(t.state(&s), sched::TS_RUNNING);
    assert_eq!(t.reg(&s, reg::BADGE), 7);
    assert_eq!(t.reg(&s, reg::R10), 0x25);
    assert_eq!(t.sc(&s), sc.0);
    assert_eq!(sc.tcb(&s), t.0);
    assert!(sched::is_schedulable(&s, t));
    assert!(!sched::in_release_queue(&s, t));
    assert_eq!(sched::action(&s), t.0);
    // `refill_unblock_check`: the stale head refill now starts at the
    // current time.
    assert_eq!(sporadic::head(&s, sc).time, 500);
    assert_eq!(n.state(&s), NTFN_IDLE);
}

#[test]
fn nested_asids_are_distinct_and_unmapping_reaches_all_recorded_cores() {
    let mut s = Memory::default();
    let mut a = Machine::default();
    let root = layout::pptr(0x1000);
    let pool = layout::pptr(0x2000);
    ks_set(&mut s, ks::ASID_TABLE, pool);
    s.write(pool + 8, root | 1);
    assert_eq!(ept::find(&s, 1).ok(), Some(root));
    assert!(vspace::find_vspace_for_asid(&s, 1).is_err());
    for (table, frame) in [(0x1000, 0x3000), (0x3000, 0x4000), (0x4000, 0x5000)] {
        s.write(layout::pptr(table), frame | 7);
    }
    s.write(layout::pptr(0x5000), 0x6000 | 7);
    ept::mark_core(&mut s, root);
    s.cpu = 1;
    ept::mark_core(&mut s, root);
    ept::unmap(&mut s, &mut a, 1, 0, layout::pptr(0x6000), 12, false);
    assert_eq!(s.read(layout::pptr(0x5000)), 0);
    assert_eq!(a.invalidations, vec![(root, 3)]);
    ept::mark_core(&mut s, root);
    vspace::delete_asid_pool(&mut s, &mut a, 0, pool);
    assert_eq!(a.invalidations.last(), Some(&(root, 3)));
    assert!(ept::find(&s, 1).is_err());
}
#[test]
fn port_cap_deletion_revokes_its_grant_even_when_not_final() {
    let (mut s, mut a, _, v) = fixture(1);
    let other = v + 0x8000;
    vcpu::init(&mut s, &a, other);
    vcpu::set(&mut s, v, vcpu::IO, 0);
    vcpu::set(&mut s, other, vcpu::IO, 0);
    let cap = Cap::IoPort {
        first: 7,
        last: 9,
        vcpu: v,
    };
    assert!(objects::finalise_cap_object(&mut s, &mut a, cap, false) == (Cap::Null, Cap::Null));
    assert_eq!(vcpu::get(&s, v, vcpu::IO), 0x380);
    assert_eq!(vcpu::get(&s, other, vcpu::IO), 0);
    let cap = Cap::IoPort {
        first: 7,
        last: 9,
        vcpu: other,
    };
    assert!(objects::finalise_cap_object(&mut s, &mut a, cap, true) == (Cap::Null, cap));
    assert_eq!(vcpu::get(&s, other, vcpu::IO), 0x380);
    // Final cleanup releases the global allocation without disturbing
    // unrelated guest grants. Each deleted cap has already revoked its own.
    vcpu::set(&mut s, v, vcpu::IO, 0);
    objects::post_cap_deletion(&mut s, &mut a, cap);
    assert_eq!(vcpu::get(&s, v, vcpu::IO), 0);
}

#[test]
fn stale_port_cap_owners_do_not_write_deleted_vcpus() {
    let (mut s, mut a, _, v) = fixture(1);
    let stale = v + 0x8000;
    let cap = Cap::IoPort {
        first: 7,
        last: 9,
        vcpu: stale,
    };
    vcpu::set(&mut s, stale, vcpu::IO, 0);
    objects::finalise_cap_object(&mut s, &mut a, cap, false);
    assert_eq!(vcpu::get(&s, stale, vcpu::IO), 0);
    assert_eq!(vcpu::get(&s, v, vcpu::IO), u64::MAX);
}

#[test]
fn unavailable_virtualization_retypes_fail_before_touching_the_destination() {
    use fl4_abi::consts::object;
    let (mut s, mut a, t, _) = fixture(0);
    t.set_reg(&mut s, reg::R10, object::X86Vcpu);
    assert!(matches!(
        fl4_core::untyped::decode(
            &mut s,
            &mut a,
            label::UntypedRetype,
            6,
            Slot(0),
            Cap::Null,
            0x40000,
            &[Slot(0x30000), Slot(0), Slot(0)]
        ),
        Err(Exc::Sys(SysError::InvalidArgument { arg: 0 }))
    ));
}
#[test]
fn ioport_reassignment_removes_the_caps_previous_grant() {
    let (mut s, mut a, t, v) = fixture(1);
    let other = v + 0x8000;
    vcpu::init(&mut s, &a, other);
    let port = Slot(0x30000);
    port.set_cap(
        &mut s,
        Cap::IoPort {
            first: 8,
            last: 15,
            vcpu: 0,
        },
    );
    let args = [port, Slot(0), Slot(0)];
    for target in [v, other] {
        t.set_reg(&mut s, reg::R10, 8);
        t.set_reg(&mut s, reg::R8, 9);
        assert!(vcpu::decode(
            &mut s,
            &mut a,
            label::X86VCPUEnableIOPort,
            2,
            target,
            false,
            0,
            &args
        )
        .is_ok());
    }
    assert_eq!(vcpu::get(&s, v, vcpu::IO), u64::MAX);
    assert_eq!(vcpu::get(&s, other, vcpu::IO), u64::MAX & !0x300);
    t.set_reg(&mut s, reg::R10, 15);
    t.set_reg(&mut s, reg::R8, 8);
    assert!(matches!(
        vcpu::decode(
            &mut s,
            &mut a,
            label::X86VCPUEnableIOPort,
            2,
            other,
            false,
            0,
            &args
        ),
        Err(Exc::Sys(SysError::InvalidArgument { arg: 0 }))
    ));
}

#[test]
fn an_ept_mapping_without_read_rights_gives_no_guest_access() {
    let (mut s, mut a, t, _) = fixture(2);
    let pool = layout::pptr(0x2000);
    let root = layout::pptr(0x1000);
    ks_set(&mut s, ks::ASID_TABLE, pool);
    s.write(pool + 8, root | 1);
    for (table, next) in [(0x1000, 0x3000), (0x3000, 0x4000), (0x4000, 0x5000)] {
        s.write(layout::pptr(table), next | 7);
    }
    let root_slot = Slot(0x30000);
    let frame_slot = Slot(0x31000);
    root_slot.set_cap(
        &mut s,
        Cap::Ept {
            ptr: root,
            level: 0,
            mapped: true,
            asid: 1,
            vaddr: 0,
        },
    );
    let cap = Cap::Frame {
        ptr: layout::pptr(0x6000),
        size: FrameSize::Small,
        rights: 3,
        is_device: false,
        mapped: false,
        is_ept: false,
        asid: 0,
        vaddr: 0,
    };
    t.set_reg(&mut s, reg::R10, 0);
    t.set_reg(&mut s, reg::R8, 0);
    t.set_reg(&mut s, reg::R9, 6);
    assert!(ept::map_frame(
        &mut s,
        &mut a,
        3,
        cap,
        frame_slot,
        0,
        &[root_slot, Slot(0), Slot(0)]
    )
    .is_ok());
    assert_eq!(s.read(layout::pptr(0x5000)), 0);
    // The cap is not marked mapped either: its deletion must not unmap
    // what another cap of the same frame maps there later.
    assert!(matches!(frame_slot.cap(&s), Cap::Frame { mapped: false, is_ept: false, asid: 0, vaddr: 0, .. }));
    let sibling = Slot(0x32000);
    t.set_reg(&mut s, reg::R8, 3);
    assert!(ept::map_frame(&mut s, &mut a, 3, cap, sibling, 0, &[root_slot, Slot(0), Slot(0)]).is_ok());
    let live = s.read(layout::pptr(0x5000));
    assert_eq!(live & 0x000f_ffff_ffff_f007, 0x6000 | 7);
    assert!(matches!(sibling.cap(&s), Cap::Frame { mapped: true, is_ept: true, asid: 1, vaddr: 0, .. }));
    let phantom = frame_slot.cap(&s);
    objects::finalise_cap(&mut s, &mut a, phantom, true, false);
    assert_eq!(s.read(layout::pptr(0x5000)), live);
}

#[test]
fn suspending_a_vm_preserves_the_syscall_restart_context() {
    let (mut s, mut a, t, v) = fixture(2);
    s.write(t.0 + tcb::VCPU, v);
    vcpu::set(&mut s, v, vcpu::TCB, t.0);
    t.set_state(&mut s, sched::TS_RUNNING_VM);
    t.set_reg(&mut s, reg::NEXT_IP, 0x1002);
    t.set_reg(&mut s, reg::FAULT_IP, 0x1000);
    t.set_reg(&mut s, reg::R10, 0x200);
    sched::suspend(&mut s, &mut a, t);
    assert_eq!(t.state(&s), sched::TS_INACTIVE);
    assert_eq!(t.reg(&s, reg::FAULT_IP), 0x1000);
    assert_eq!(t.reg(&s, reg::R10), 0x200);
    assert_eq!(vcpu::bound(&s, t), v);
}

/// A VMEnter that completes (a saved exit or a bound notification) has
/// finished its syscall: `report` settles `FAULT_IP` at `NEXT_IP` before
/// the thread leaves `TS_RUNNING_VM`. Otherwise the budget check that
/// follows can raise a timeout fault on the stale `FAULT_IP` (still the
/// VMEnter instruction), and a restarting reply (label 0) runs VMEnter
/// again and loses the exit just reported.
#[test]
fn vcpu_report_settles_fault_ip_before_timeout_fault() {
    use fl4_core::obj::Reply;
    use fl4_core::{endpoint, ipc, syscall};
    for (pending, request) in [(true, 0), (false, 0), (true, vcpu::NUM_MRS), (false, vcpu::NUM_MRS)] {
        let (mut s, mut a, t, v) = fixture(2);
        t.set_reg(&mut s, reg::MSG_INFO, request);
        s.write(t.0 + tcb::VCPU, v);
        vcpu::set(&mut s, v, vcpu::TCB, t.0);
        vcpu::set(&mut s, v, vcpu::svm::RIP, 0x25);
        let n = bind_ntfn(&mut s, t);
        if pending {
            vcpu::set(&mut s, v, vcpu::PENDING, 1);
            vcpu::set(&mut s, v, vcpu::VALID, 1);
            vcpu::set(&mut s, v, vcpu::EXIT, 0x1234);
        } else {
            n.set_state(&mut s, NTFN_ACTIVE);
            n.set_badge(&mut s, 0x42);
        }
        t.set_state(&mut s, sched::TS_RUNNING_VM);
        t.set_reg(&mut s, reg::FAULT_IP, 0x1000);
        t.set_reg(&mut s, reg::NEXT_IP, 0x1002);

        // An idle thread to switch to, and a periodic (not round-robin) SC
        // whose budget is used up.
        let idle = Tcb(0xc0000);
        let idle_sc = Sc(0xa0000);
        idle.set_state(&mut s, sched::TS_IDLE);
        idle.set_sc(&mut s, idle_sc.0);
        sporadic::refill_new(&mut s, idle_sc, 2, 100000, 0);
        node_set(&mut s, 0, node::IDLE_THREAD, idle.0);
        node_set(&mut s, 0, node::IDLE_SC, idle_sc.0);
        let sc = Sc(0x90000);
        sporadic::refill_new(&mut s, sc, 2, 1000, 10000);
        sc.set_tcb(&mut s, t.0);
        t.set_sc(&mut s, sc.0);
        node_set(&mut s, 0, node::CUR_SC, sc.0);
        node_set(&mut s, 0, node::CONSUMED, 1000);

        // A timeout handler waiting on its endpoint with a reply object.
        let ep = 0xd0000;
        let r = Reply(0xe0000);
        let handler = Tcb(0xb0000);
        handler.set_state(&mut s, sched::TS_RUNNING);
        let recv = Cap::Endpoint { ptr: ep, badge: 0, send: false, recv: true, grant: false, grant_reply: false };
        endpoint::receive_ipc(&mut s, &mut a, handler, recv, true, Cap::Reply { ptr: r.0, grant: true });
        assert_eq!(handler.state(&s), sched::TS_BLOCKED_ON_RECV);
        let th = Cap::Endpoint { ptr: ep, badge: 0x77, send: true, recv: false, grant: true, grant_reply: true };
        t.slot(tcb::SLOT_TIMEOUT_HANDLER).set_cap(&mut s, th);

        syscall::handle_vcpu_exit(&mut s, &mut a, syscall::NO_IRQ, false);
        assert_eq!(t.state(&s), sched::TS_BLOCKED_ON_REPLY, "pending={pending}: timeout fault");
        assert_eq!(t.fault_type(&s), fl4_abi::consts::fault::Timeout);
        assert_eq!(t.reg(&s, reg::FAULT_IP), 0x1002, "pending={pending}: FAULT_IP settled");

        // The handler restarts the thread: label 0, no registers.
        handler.set_reg(&mut s, reg::MSG_INFO, 0);
        ipc::do_reply_transfer(&mut s, &mut a, handler, r, false);
        assert_eq!(t.state(&s), sched::TS_RESTART);
        node_set(&mut s, 0, node::CUR_THREAD, t.0);
        sched::activate_thread(&mut s, &mut a);
        assert_eq!(t.state(&s), sched::TS_RUNNING);
        assert_eq!(t.reg(&s, reg::NEXT_IP), 0x1002, "pending={pending}: resumes after VMEnter");
        if pending {
            assert_eq!(t.reg(&s, reg::MSG_INFO), 1);
            assert_eq!(t.reg(&s, reg::BADGE), 0);
            assert_eq!(t.reg(&s, reg::R10), 0x1234);
        } else {
            assert_eq!(t.reg(&s, reg::MSG_INFO), 0);
            assert_eq!(t.reg(&s, reg::BADGE), 0x42);
            assert_eq!(t.reg(&s, reg::R10), 0x25);
        }
    }
}

/// A VMM may give its guest BTF (bit 1) of IA32_DEBUGCTL and nothing else:
/// LBR (0), BUS_LOCK_DETECT (2), TR (6), BTS (7), BTINT (8),
/// BTS_OFF_OS/USR (9, 10), the FREEZE bits (12, 14), RTM_DEBUG (15) and
/// every reserved bit act on the host's state or bus.
#[test]
fn guests_get_only_single_step_on_branches_in_debugctl() {
    use vcpu::vmx::*;
    let intel = Machine {
        backend: 1,
        ..Default::default()
    };
    let write = |v| vcpu::sanitize_vmcs(&intel, GUEST_DEBUGCTRL, v).ok().unwrap();
    assert_eq!(write(u64::MAX), 1 << 1);
    assert_eq!(write(1 << 1), 1 << 1);
    for bit in [0, 2, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 63] {
        assert_eq!(write(1 << bit), 0, "bit {bit}");
    }
    // TR without BTS: branch trace messages on the bus.
    assert_eq!(write((1 << 6) | (1 << 1)), 1 << 1);
}

/// FL4's host runs 4-level paging (VCPU capability 1 is 48), so a guest
/// may not turn on CR4.LA57 (bit 12) on either backend.
#[test]
fn guests_cannot_enable_five_level_paging() {
    use vcpu::vmx::*;
    const LA57: u64 = 1 << 12;
    assert_eq!(vcpu::CR4_ALLOWED & LA57, 0);
    let intel = Machine {
        backend: 1,
        ..Default::default()
    };
    assert_eq!(vcpu::sanitize_vmcs(&intel, GUEST_CR4, u64::MAX).ok().unwrap() & LA57, 0);
    assert_eq!(vcpu::sanitize_vmcs(&intel, GUEST_CR4, LA57).ok().unwrap() & LA57, 0);
    // The guest's own MOV to CR4.LA57 exits to the VMM.
    assert_eq!(vcpu::sanitize_vmcs(&intel, CONTROL_CR4_MASK, 0).ok().unwrap() & LA57, LA57);
    let amd = Machine {
        backend: 2,
        ..Default::default()
    };
    // Guest CR4 writes always exit (the forced intercept bit 20 of word
    // 0x000), so the VMCB's CR4 changes only through this check.
    assert_eq!(vcpu::sanitize_vmcb(&amd, 0, 0, 0).ok().unwrap() & (1 << 20), 1 << 20);
    assert_eq!(vcpu::sanitize_vmcb(&amd, 0x548, 0, u64::MAX).ok().unwrap() & LA57, 0);
    assert_eq!(vcpu::sanitize_vmcb(&amd, 0x548, 0, LA57).ok().unwrap() & LA57, 0);
}

/// CR0.CD (bit 30) and CR0.NW (bit 29) are in `CR0_OWNED`: the guest's
/// own MOV to them exits to the VMM, and neither the VMM nor the guest may
/// put them in the CR0 the hardware runs the guest with. In VMX non-root
/// operation, and in an SVM guest, they drive this core's caches (no-fill
/// mode); KVM keeps them out of the hardware CR0 on both backends.
#[test]
fn guests_cannot_disable_the_cores_caches() {
    use vcpu::vmx::*;
    const CD_NW: u64 = (1 << 30) | (1 << 29);
    // PG, AM, WP, NE, ET, TS, MP, PE: the bits a guest really runs with.
    const USUAL: u64 = 0x8005_003b;
    let intel = Machine {
        backend: 1,
        ..Default::default()
    };
    let write = |v| vcpu::sanitize_vmcs(&intel, GUEST_CR0, v).ok().unwrap();
    assert_eq!(write(u64::MAX) & CD_NW, 0);
    assert_eq!(write(1 << 30) & CD_NW, 0);
    assert_eq!(write(1 << 29) & CD_NW, 0);
    assert_eq!(write(USUAL | CD_NW), USUAL);
    assert_eq!(write(u64::MAX) & vcpu::CR0_OWNED, 0);
    // The guest's own MOV to CD or NW exits to the VMM.
    assert_eq!(vcpu::sanitize_vmcs(&intel, CONTROL_CR0_MASK, 0).ok().unwrap() & CD_NW, CD_NW);

    let amd = Machine {
        backend: 2,
        ..Default::default()
    };
    let write = |old, v| vcpu::sanitize_vmcb(&amd, vcpu::svm::CR0, old, v).ok().unwrap();
    assert_eq!(write(0, u64::MAX) & CD_NW, 0);
    assert_eq!(write(0, 1 << 30) & CD_NW, 0);
    assert_eq!(write(0, 1 << 29) & CD_NW, 0);
    assert_eq!(write(0, USUAL | CD_NW), USUAL);
    assert_eq!(write(CD_NW, USUAL), USUAL);
    assert_eq!(write(0, u64::MAX) & vcpu::CR0_OWNED, 0);
    // SVM has no CR0 guest/host mask: the selective CR0 write intercept
    // (bit 5 of the vector at 0x00c, bit 37 of word 0x008) makes every
    // guest CR0 write that changes more than TS and MP exit (AMD APM vol. 2,
    // selective CR0 write intercept), so CD and NW reach the VMCB only
    // through the check above.
    // CLTS and TS/MP-only writes (lazy FPU switching) still do not exit.
    const SEL_CR0: u64 = 1 << 5;
    assert_ne!(vcpu::SVM_I1_FORCED & SEL_CR0, 0);
    assert_eq!(vcpu::SVM_I1_WRITABLE & SEL_CR0, 0);
    for val in [0, u64::MAX] {
        assert_ne!(vcpu::sanitize_vmcb(&amd, 8, 0, val).ok().unwrap() & (SEL_CR0 << 32), 0);
    }
    let (s, _, _, v) = fixture(2);
    assert_ne!(vcpu::get(&s, v, 8) & (SEL_CR0 << 32), 0);
}
