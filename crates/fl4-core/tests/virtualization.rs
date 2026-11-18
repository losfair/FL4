use fl4_abi::label;
use fl4_core::capability::{Cap, FrameSize};
use fl4_core::error::{Exc, SysError};
use fl4_core::layout::{self, ks, node, reg, tcb};
use fl4_core::machine::{Arch, Store};
use fl4_core::obj::{ks_set, node_set, Slot, Tcb};
use fl4_core::{ept, objects, sched, vcpu, vspace};
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
            0 => 7,
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
    assert_eq!(write(CONTROL_CR4_MASK, 0), !vcpu::CR4_ALLOWED);
    assert_eq!(
        write(GUEST_CR4, u64::MAX) & !((1 << 13) | vcpu::CR4_ALLOWED),
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
            vcpu::sanitize_vmcb(&a, 0x548, 0, val).ok().unwrap() & !vcpu::CR4_ALLOWED,
            0
        );
    }
    assert!(vcpu::sanitize_vmcb(&a, 0x620, 0, 0x800000000000).is_err());
    assert!(vcpu::sanitize_vmcb(&a, 0x668, 0, 0x0202020202020202).is_err());
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
