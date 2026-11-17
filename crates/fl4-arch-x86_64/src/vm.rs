//! Trusted VMX/SVM instruction boundary. Policy lives in fl4-core::vcpu.
//!
//! Each core retains its own VMCS and resumes it after the first launch.
//! Its field cache follows VMWRITE and VMREAD, so unchanged fields need no
//! VMWRITE even when a guest changed them. A VCPU's complete software image
//! is saved before remote calls can move/delete it; the hardware VMCS never
//! migrates or belongs to user memory. EPT translations survive entries;
//! unmaps and root deletion invalidate every core recorded for the root.
//! VMX uses no VPID. SVM retains ASID 1 only for the last VCPU/root on a
//! core; migration, software paging changes and invalidation revoke it.
use crate::{cpu, fpu, percpu, spec, tlb};
use core::arch::asm;
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicU64, Ordering};
use fl4_core::layout;
use fl4_core::machine::Store;
use fl4_core::vcpu::{self, svm, vmx::*};

mod vmx_exit;

core::arch::global_asm!(
    include_str!("spec.S"), include_str!("vm.S"),
    spec_ibpb = const spec::policy::IBPB,
    spec_rsb = const spec::policy::RSB,
    spec_pbrsb = const spec::policy::PBRSB,
    spec_legacy = const spec::policy::LEGACY_IBRS,
    spec_bhb = const spec::policy::BHB,
    spec_ibhf = const spec::policy::IBHF,
    options(att_syntax)
);
// Exercise the real exit assembly in host tests without executing VMX:
// reproduce HOST_RSP, load the guest GPRs, and enter the real exit label.
#[cfg(test)]
core::arch::global_asm!(
    ".global fl4_test_vmx_exit
fl4_test_vmx_exit:
    save_host
    pushq %rsi
    load_guest
    movq (%rax), %rax
    ret",
    options(att_syntax)
);
extern "C" {
    fn fl4_vmx_run(run: *mut Run);
    fn fl4_vmx_exit();
    fn fl4_svm_run(run: *mut Run);
}

#[repr(C, align(4096))]
struct Page([u8; 4096]);

struct VmcsState {
    values: [u64; 2048],
    valid: [u64; 32],
    loaded: bool,
    launched: bool,
}

/// Only one SVM address space is retained per core. The VCPU's owner word
/// distinguishes migration and retype at the same address; core policy
/// also clears it for explicit TLB flushes and software paging writes.
struct SvmState {
    vcpu: u64,
    root: u64,
    valid: bool,
    values: [u64; SVM_CACHED.len()],
}
// AMD APM vol. 2 §15.15: every field in the clean groups we enable.
// Interrupt controls and unsupported groups stay dirty. VMLOAD/VMSAVE
// state, RIP/RSP/RAX, event injection and exit fields are never cached here.
const SVM_CACHED: &[(u64, u64)] = &[
    (0x000, 0),
    (0x008, 0),
    (0x010, 0),
    (0x038, 0),
    (0x050, 0),
    (0x040, 1),
    (0x048, 1),
    (0x058, 2),
    (0x090, 4),
    (0x0b0, 4),
    (0x668, 4),
    (0x4d0, 5),
    (0x548, 5),
    (0x550, 5),
    (0x558, 5),
    (0x560, 6),
    (0x568, 6),
    (0x460, 7),
    (0x468, 7),
    (0x480, 7),
    (0x488, 7),
    (0x400, 8),
    (0x408, 8),
    (0x410, 8),
    (0x418, 8),
    (0x420, 8),
    (0x428, 8),
    (0x430, 8),
    (0x438, 8),
    (0x4c8, 8),
    (0x640, 9),
];
impl SvmState {
    const fn new() -> Self {
        Self {
            vcpu: 0,
            root: 0,
            valid: false,
            values: [0; SVM_CACHED.len()],
        }
    }
    fn prepare(&mut self, vcpu: u64, root: u64, owner: u64, cpu: u64) -> bool {
        let flush = !self.valid || self.vcpu != vcpu || self.root != root || owner != cpu + 1;
        self.vcpu = vcpu;
        self.root = root;
        // A failed VMRUN need not have performed the requested flush.
        self.valid = false;
        flush
    }
    fn clean(&self, mut read: impl FnMut(u64) -> u64) -> u64 {
        let mut clean = 0x3f7; // Groups 0..9, except interrupt controls.
        for (i, &(offset, group)) in SVM_CACHED.iter().enumerate() {
            if read(offset) != self.values[i] {
                clean &= !(1 << group);
            }
        }
        clean
    }
    fn observe(&mut self, mut read: impl FnMut(u64) -> u64) {
        for (i, &(offset, _)) in SVM_CACHED.iter().enumerate() {
            self.values[i] = read(offset);
        }
    }
}

#[derive(Default)]
struct SvmHost {
    tls: Option<(u64, u64, u16, u16)>,
}
impl SvmHost {
    fn needs_save(&mut self, tls: (u64, u64, u16, u16), mutable_msrs: bool) -> bool {
        let save = mutable_msrs || self.tls != Some(tls);
        self.tls = Some(tls);
        save
    }
}
impl VmcsState {
    const fn new() -> Self {
        Self {
            values: [0; 2048],
            valid: [0; 32],
            loaded: false,
            launched: false,
        }
    }
    fn index(field: u64) -> usize {
        ((vcpu::vmcs_addr(0, field) - vcpu::SHADOW) / 8) as usize
    }
    fn get(&self, field: u64) -> Option<u64> {
        let i = Self::index(field);
        if self.valid[i / 64] & (1 << (i % 64)) != 0 {
            Some(self.values[i])
        } else {
            None
        }
    }
    fn observe(&mut self, field: u64, value: u64) {
        let i = Self::index(field);
        self.values[i] = value;
        self.valid[i / 64] |= 1 << (i % 64);
    }
    fn write(&mut self, field: u64, value: u64, write: impl FnOnce(u64, u64)) {
        if self.get(field) != Some(value) {
            write(field, value);
            self.observe(field, value);
        }
    }
    fn finish_entry(&mut self, failed: bool, reason: u64) -> bool {
        let valid = !failed && reason & (1 << 31) == 0;
        // Failed launches stay clear; failed resumes stay launched. Intel
        // sets the launch state only after guest-state and MSR checks.
        self.launched |= valid;
        valid
    }
}

#[repr(C, align(4096))]
struct Core {
    enable: Page,
    host: Page,
    vmcs: Page,
    vmx: VmcsState,
    svm: SvmState,
    svm_host: SvmHost,
}
struct Cores(UnsafeCell<[Core; percpu::MAX_CPUS]>);
// Each core alone accesses its pages, after BSP initialization.
unsafe impl Sync for Cores {}
static CORES: Cores = Cores(UnsafeCell::new(
    [const {
        Core {
            enable: Page([0; 4096]),
            host: Page([0; 4096]),
            vmcs: Page([0; 4096]),
            vmx: VmcsState::new(),
            svm: SvmState::new(),
            svm_host: SvmHost { tls: None },
        }
    }; percpu::MAX_CPUS],
));
#[repr(C, align(4096))]
struct Maps {
    io: [u8; 12288],
    msr: [u8; 8192],
    empty: Page,
}
struct Shared(UnsafeCell<Maps>);
// Written on the BSP before AP startup; read-only thereafter.
unsafe impl Sync for Shared {}
static MAPS: Shared = Shared(UnsafeCell::new(Maps {
    io: [255; 12288],
    msr: [255; 8192],
    empty: Page([0; 4096]),
}));
static BACKEND: AtomicU64 = AtomicU64::new(0);
static BASIC: AtomicU64 = AtomicU64::new(0);
static EPT_CAP: AtomicU64 = AtomicU64::new(0);
static SVM_FEATURES: AtomicU64 = AtomicU64::new(0);
static CAPS: [AtomicU64; 32] = [const { AtomicU64::new(0) }; 32];

#[repr(C)]
struct Run {
    regs: [u64; 15],
    reserved: u64,
    vmcb: u64,
    host: u64,
    host_cr2: u64,
    host_xcr0: u64,
    guest_xcr0: u64,
    guest_cr2: u64,
    failed: u64,
    resume: u64,
    host_rsp: u64,
    speculation: u64,
}
const _: () = assert!(
    core::mem::offset_of!(Run, vmcb) == 128
        && core::mem::offset_of!(Run, failed) == 176
        && core::mem::offset_of!(Run, resume) == 184
        && core::mem::offset_of!(Run, host_rsp) == 192
        && core::mem::offset_of!(Run, speculation) == 200
);
#[repr(C, align(16))]
struct Msr {
    number: u32,
    reserved: u32,
    value: u64,
}

fn physical(ptr: u64) -> u64 {
    if ptr >= layout::PPTR_TOP {
        ptr.wrapping_sub(0xffff_ffff_8000_0000)
    } else {
        layout::paddr(ptr)
    }
}
fn local() -> &'static mut Core {
    unsafe { &mut (*CORES.0.get())[percpu::cpu_index()] }
}
fn maps() -> &'static Maps {
    unsafe { &*MAPS.0.get() }
}
pub fn backend() -> u64 {
    BACKEND.load(Ordering::Acquire)
}
pub fn capability(field: u64) -> u64 {
    if field == 0 {
        return fpu::xcr0();
    }
    if field == 1 {
        return canonical_width(cpu::read_cr4());
    }
    if backend() != 1 || !(0x480..0x4a0).contains(&field) {
        return 0;
    }
    CAPS[(field - 0x480) as usize].load(Ordering::Relaxed)
}
/// Virtual-address width of the host's paging (VCPU capability 1): what
/// CR4.LA57 says it runs, not what CPUID says the CPU could. FL4 uses
/// 4-level paging, so this is 48 even on CPUs with LA57.
fn canonical_width(cr4: u64) -> u64 {
    if cr4 & (1 << 12) != 0 {
        57
    } else {
        48
    }
}
fn vmread(f: u64) -> u64 {
    let mut value = 0;
    unsafe {
        asm!("vmread {value}, {field}", value=inout(reg) value, field=in(reg) f, options(nostack));
    }
    // Guest execution can change fields without VMWRITE. The cache must
    // reflect hardware before a VMM changes one back to its old value.
    local().vmx.observe(f, value);
    value
}
fn vmwrite(f: u64, value: u64) {
    local().vmx.write(f, value, |field, value| unsafe {
        asm!("vmwrite {field}, {value}", field=in(reg) field, value=in(reg) value, options(nostack));
    });
}
fn vmclear(pa: u64) -> bool {
    let fail: u8;
    unsafe {
        asm!("vmclear [{pa}]", "setna {fail}", pa=in(reg) &pa, fail=out(reg_byte) fail, options(nostack));
    }
    fail == 0
}
fn vmptrld(pa: u64) -> bool {
    let fail: u8;
    unsafe {
        asm!("vmptrld [{pa}]", "setna {fail}", pa=in(reg) &pa, fail=out(reg_byte) fail, options(nostack));
    }
    fail == 0
}
fn pass_msr(bitmap: &mut [u8], msr: u32, amd: bool) {
    if amd {
        let (base, index) = if msr < 0x2000 {
            (0, msr)
        } else {
            (0x800, msr - 0xc000_0000)
        };
        bitmap[base + (index / 4) as usize] &= !(3 << ((index % 4) * 2));
    } else {
        let (base, index) = if msr < 0x2000 {
            (0, msr)
        } else {
            (1024, msr - 0xc000_0000)
        };
        bitmap[base + (index / 8) as usize] &= !(1 << (index % 8));
        bitmap[base + 2048 + (index / 8) as usize] &= !(1 << (index % 8));
    }
}
fn init_svm(bsp: bool) -> bool {
    if spec::vmexit().is_none() {
        return false;
    }
    if cpu::cpuid(0x8000_0000, 0).eax < 0x8000_000a || cpu::cpuid(0x8000_0001, 0).ecx & 4 == 0 {
        return false;
    }
    let c = cpu::cpuid(0x8000_000a, 0);
    if c.edx & 9 != 9 || c.ebx < 2 || cpu::rdmsr(0xc001_0114) & 16 != 0 {
        return false;
    }
    if bsp {
        SVM_FEATURES.store(c.edx as u64, Ordering::Relaxed);
        let m = unsafe { &mut *MAPS.0.get() };
        for msr in [
            0x174,
            0x175,
            0x176,
            0xc000_0081,
            0xc000_0082,
            0xc000_0083,
            0xc000_0084,
            0xc000_0100,
            0xc000_0101,
            0xc000_0102,
        ] {
            pass_msr(&mut m.msr, msr, true);
        }
    }
    cpu::wrmsr(cpu::msr::EFER, cpu::rdmsr(cpu::msr::EFER) | (1 << 12));
    cpu::wrmsr(0xc001_0117, physical(local().enable.0.as_ptr() as u64));
    true
}
fn control_msr(field: u32, true_controls: bool) -> u32 {
    if true_controls {
        match field {
            0x481 => 0x48d,
            0x482 => 0x48e,
            0x483 => 0x48f,
            0x484 => 0x490,
            _ => field,
        }
    } else {
        field
    }
}

/// Whether this processor's VMCS has `field` (SDM Vol. 3 App. B): two
/// fields exist only with the 1-setting of an optional control, and a
/// VMREAD or VMWRITE of a field that does not exist fails with VM-instruction
/// error 12, which would replace a failed entry's own error number and make
/// the VMCS cache record a write that did not happen. X86VCPUReadVMCS answers
/// 0 for both (fl4-core `vcpu`); `cap` is `capability`.
fn vmcs_field_exists(field: u64, cap: impl Fn(u64) -> u64) -> bool {
    match field {
        GUEST_PERF_GLOBAL_CTRL => cap(0x484) >> 32 & (1 << 13) != 0,
        GUEST_PREEMPTION_TIMER_VALUE => cap(0x481) >> 32 & (1 << 6) != 0,
        _ => true,
    }
}

fn has_perf_global_ctrl(max_leaf: u32, pmu_eax: u32) -> bool {
    // Version 1 is insufficient under KVM: it emulates GLOBAL_CTRL only
    // for architectural PMU version 2 or later. Nested VMX control MSRs
    // may still advertise the load controls when the PMU is hidden.
    max_leaf >= 0xa && pmu_eax & 0xff >= 2
}

fn pmu_controls(field: u32, value: u64, perf_global_ctrl: bool) -> Option<u64> {
    let bit = match field {
        0x483 => 1 << 12, // VM exit loads the host's GLOBAL_CTRL.
        0x484 => 1 << 13, // VM entry loads the guest's GLOBAL_CTRL.
        _ => 0,
    };
    if perf_global_ctrl {
        Some(value)
    } else if value & bit != 0 {
        // A mandatory load of an unavailable MSR cannot be made safe.
        None
    } else {
        Some(value & !(bit << 32))
    }
}

fn read_vmx_capabilities(
    true_controls: bool,
    perf_global_ctrl: bool,
    mut read_msr: impl FnMut(u32) -> u64,
) -> Option<[u64; 32]> {
    let mut caps = [0; 32];
    for field in [
        0x481u32, 0x482, 0x483, 0x484, 0x485, 0x486, 0x487, 0x488, 0x489, 0x48b,
    ] {
        // IA32_VMX_PROCBASED_CTLS2 exists only if primary controls allow
        // "activate secondary controls" (bit 31 in the allowed-1 mask).
        if field == 0x48b && caps[2] & (1 << 63) == 0 {
            return None;
        }
        caps[(field - 0x480) as usize] = pmu_controls(
            field,
            read_msr(control_msr(field, true_controls)),
            perf_global_ctrl,
        )?;
    }
    Some(caps)
}

fn init_vmx(bsp: bool) -> bool {
    if cpu::cpuid(1, 0).ecx & (1 << 5) == 0 {
        return false;
    }
    let Some(_) = spec::vmexit() else {
        return false;
    };
    let basic = cpu::rdmsr(0x480);
    if (basic >> 32) & 0x1fff > 4096 || (basic >> 50) & 15 != 6 {
        return false;
    }
    let true_controls = basic & (1 << 55) != 0;
    let max_leaf = cpu::cpuid(0, 0).eax;
    let pmu_eax = if max_leaf >= 0xa {
        cpu::cpuid(0xa, 0).eax
    } else {
        0
    };
    let perf_global_ctrl = has_perf_global_ctrl(max_leaf, pmu_eax);
    let Some(caps) = read_vmx_capabilities(true_controls, perf_global_ctrl, cpu::rdmsr) else {
        return false;
    };
    for (saved, value) in CAPS.iter().zip(caps) {
        if bsp {
            saved.store(value, Ordering::Relaxed);
        } else if saved.load(Ordering::Relaxed) != value {
            return false;
        }
    }
    let cap = |f: u64| CAPS[(f - 0x480) as usize].load(Ordering::Relaxed);
    for (f, required) in [
        (0x481, vcpu::PIN_ALLOWED),
        (0x482, vcpu::PRIMARY_FORCED),
        (0x483, vcpu::EXIT_FORCED),
        (0x48b, 2),
        (0x484, 1 << 9),
    ] {
        if (cap(f) >> 32) & required != required {
            return false;
        }
    }
    // Reading EPT_VPID_CAP is safe only after verifying EPT support.
    let ept = cpu::rdmsr(0x48c);
    let required = (1 << 6) | (1 << 14) | (1 << 16) | (1 << 20);
    if ept & required != required || ept & ((1 << 25) | (1 << 26)) == 0 {
        return false;
    }
    if bsp {
        BASIC.store(basic, Ordering::Relaxed);
        EPT_CAP.store(ept, Ordering::Relaxed);
    } else if BASIC.load(Ordering::Relaxed) != basic || EPT_CAP.load(Ordering::Relaxed) != ept {
        return false;
    }
    let cr0 = cpu::read_cr0();
    let cr4 = cpu::read_cr4() | (1 << 13);
    if cr0 & cap(0x486) != cap(0x486)
        || cr0 & !cap(0x487) != 0
        || cr4 & cap(0x488) != cap(0x488)
        || cr4 & !cap(0x489) != 0
    {
        return false;
    }
    let feature = cpu::rdmsr(0x3a);
    if feature & 1 != 0 && feature & 4 == 0 {
        return false;
    }
    if feature & 1 == 0 {
        cpu::wrmsr(0x3a, feature | 5);
    }
    let c = local();
    c.enable.0[..4].copy_from_slice(&(basic as u32 & 0x7fff_ffff).to_le_bytes());
    c.vmcs.0[..4].copy_from_slice(&(basic as u32 & 0x7fff_ffff).to_le_bytes());
    cpu::write_cr4(cr4);
    let pa = physical(c.enable.0.as_ptr() as u64);
    let fail: u8;
    unsafe {
        asm!("vmxon [{pa}]", "setna {fail}", pa=in(reg) &pa, fail=out(reg_byte) fail, options(nostack));
    }
    if fail != 0 {
        cpu::write_cr4(cr4 & !(1 << 13));
        return false;
    }
    if bsp {
        let m = unsafe { &mut *MAPS.0.get() };
        for msr in [0x174, 0x175, 0x176, 0xc000_0100, 0xc000_0101, 0xc000_0102] {
            pass_msr(&mut m.msr, msr, false);
        }
    }
    true
}
/// BSP picks the backend, APs must be able to provide the same interface.
pub fn init(bsp: bool) -> bool {
    if tlb::skim() || crate::sev::mask() != 0 {
        return true;
    }
    if !bsp && backend() == 0 {
        return true;
    }
    let chosen = if cpu::cpuid(1, 0).ecx & (1 << 5) != 0 {
        1
    } else {
        2
    };
    if !bsp && chosen != backend() {
        return false;
    }
    let ok = if chosen == 1 {
        init_vmx(bsp)
    } else {
        init_svm(bsp)
    };
    if bsp {
        BACKEND.store(if ok { chosen } else { 0 }, Ordering::Release);
        true
    } else {
        ok
    }
}

pub fn invalidate_local(root: u64) {
    if backend() == 2 {
        // This also handles roots destroyed and retyped at the same
        // address. The next VMRUN flushes before consuming any mapping.
        local().svm.valid = false;
        return;
    }
    if backend() != 1 {
        return;
    }
    let eptp = physical(root) | 6 | (3 << 3);
    let descriptor = [eptp, 0];
    let kind: u64 = if EPT_CAP.load(Ordering::Relaxed) & (1 << 25) != 0 {
        1
    } else {
        2
    };
    unsafe {
        asm!("invept {kind}, [{ptr}]", kind=in(reg) kind, ptr=in(reg) descriptor.as_ptr(), options(nostack));
    }
}

#[repr(C, packed)]
struct Table {
    limit: u16,
    base: u64,
}
fn host_tables() -> (Table, Table, u64) {
    let mut gdt = Table { limit: 0, base: 0 };
    let mut idt = Table { limit: 0, base: 0 };
    unsafe {
        asm!("sgdt [{}]", "sidt [{}]", in(reg) &mut gdt, in(reg) &mut idt, options(nostack));
    }
    let low = unsafe { ((gdt.base + 0x40) as *const u64).read() };
    let high = unsafe { ((gdt.base + 0x48) as *const u64).read() };
    let tr = ((low >> 16) & 0xff_ffff) | ((low >> 32) & 0xff00_0000) | (high << 32);
    (gdt, idt, tr)
}
fn host_vmcs(gdt: &Table, idt: &Table, tr: u64) {
    for (field, value) in [
        (HOST_CR0, cpu::read_cr0()),
        (HOST_CR3, cpu::read_cr3()),
        (HOST_CR4, cpu::read_cr4()),
        (HOST_ES_SELECTOR, 0x18),
        (HOST_CS_SELECTOR, 0x10),
        (HOST_SS_SELECTOR, 0x18),
        (HOST_DS_SELECTOR, 0x18),
        (HOST_FS_SELECTOR, 0),
        (HOST_GS_SELECTOR, 0),
        (HOST_TR_SELECTOR, 0x40),
        (HOST_FS_BASE, cpu::fs_base()),
        (HOST_GS_BASE, cpu::gs_base()),
        (HOST_TR_BASE, tr),
        (HOST_GDTR_BASE, gdt.base),
        (HOST_IDTR_BASE, idt.base),
        (HOST_SYSENTER_CS, 0),
        (HOST_SYSENTER_ESP, 0),
        (HOST_SYSENTER_EIP, 0),
        (HOST_EFER, cpu::rdmsr(cpu::msr::EFER)),
        (HOST_PAT, cpu::rdmsr(0x277)),
    ] {
        vmwrite(field, value);
    }
    // init_vmx removes this capability when CPUID does not expose a
    // usable PMU; a raw VMX capability bit alone cannot authorize RDMSR.
    if capability(0x483) >> 32 & (1 << 12) != 0 {
        vmwrite(HOST_PERF_GLOBAL_CTRL, cpu::rdmsr(0x38f));
    }
}

/// Run after the core registered the EPT root and current TCB under the
/// serial gate. Save every result before the caller services a remote IPI.
pub fn run<S: Store>(s: &mut S, v: u64, tcb: u64, root: u64) -> u64 {
    let amd = backend() == 2;
    fpu::lazy_load(tcb);
    if !amd || fl4_abi::config::HARDWARE_DEBUG_API {
        cpu::write_dr7(0x400);
        for i in 0..4 {
            cpu::write_dr(i, 0);
        }
    }
    percpu::get().dr_loaded.set(false);
    let mut run = Run {
        regs: [0; 15],
        reserved: 0,
        vmcb: physical(v),
        host: physical(local().host.0.as_ptr() as u64),
        host_cr2: cpu::read_cr2(),
        host_xcr0: fpu::xcr0(),
        guest_xcr0: vcpu::get(s, v, vcpu::XCR0),
        guest_cr2: vcpu::get(s, v, vcpu::CR2),
        failed: 0,
        resume: local().vmx.launched as u64,
        host_rsp: local().vmx.get(HOST_RSP).unwrap_or(0),
        speculation: spec::vmexit().expect("VM backend without speculation protection") as u64,
    };
    for i in 0..15 {
        run.regs[i] = vcpu::get(s, v, vcpu::REGS + i as u64 * 8);
    }
    // SVM saves/restores GDTR and IDTR itself. VMX needs their host
    // values and restores the original limits after VM exit.
    let (gdt, idt, tr) = if amd {
        (Table { limit: 0, base: 0 }, Table { limit: 0, base: 0 }, 0)
    } else {
        host_tables()
    };
    let msrs = [
        0xc000_0081u32,
        0xc000_0082,
        0xc000_0083,
        0xc000_0084,
        0xc000_0102,
    ];
    let mut guest_list: [Msr; 5] = core::array::from_fn(|i| Msr {
        number: msrs[i],
        reserved: 0,
        value: if amd {
            0
        } else {
            vcpu::get(s, v, vcpu::MSRS + i as u64 * 8)
        },
    });
    let host_list: [Msr; 5] = core::array::from_fn(|i| Msr {
        number: msrs[i],
        reserved: 0,
        value: if amd { 0 } else { cpu::rdmsr(msrs[i]) },
    });
    if amd {
        vcpu::set(s, v, svm::IOPM_BASE, physical(maps().io.as_ptr() as u64));
        vcpu::set(s, v, svm::MSRPM_BASE, physical(maps().msr.as_ptr() as u64));
        vcpu::set(s, v, svm::NESTED_CR3, physical(root));
        let flush = local()
            .svm
            .prepare(v, root, vcpu::get(s, v, vcpu::SVM_CPU), s.cur_cpu());
        vcpu::set(s, v, svm::ASID, 1 | ((flush as u64) << 32));
        let clean = if !flush && SVM_FEATURES.load(Ordering::Relaxed) & (1 << 5) != 0 {
            local().svm.clean(|off| vcpu::get(s, v, off))
        } else {
            0
        };
        vcpu::set(s, v, svm::CLEAN, clean);
        vcpu::set(s, v, svm::RAX, run.regs[0]);
        // TR, LDTR, KERNEL_GS_BASE and the syscall/SYSENTER MSRs are fixed
        // per core after initialization. FS/GS selectors and bases are the
        // only VMLOAD state normal user code can change. Inspect the real
        // bases, even without FSGSBASE: loading a selector can change them.
        let (fs, gs): (u16, u16);
        unsafe {
            asm!("mov {:x}, fs", "mov {:x}, gs", out(reg) fs, out(reg) gs,
                 options(nomem, nostack, preserves_flags));
        }
        let tls = (cpu::fs_base(), cpu::gs_base(), fs, gs);
        if local()
            .svm_host
            .needs_save(tls, fl4_abi::config::KERNEL_X86_DANGEROUS_MSR)
        {
            unsafe {
                asm!("vmsave rax", in("rax") run.host, options(nostack));
            }
        }
    } else {
        if !local().vmx.loaded {
            let pa = physical(local().vmcs.0.as_ptr() as u64);
            assert!(vmclear(pa) && vmptrld(pa));
            local().vmx.loaded = true;
        }
        for field in vcpu::WRITE_FIELDS {
            if vmcs_field_exists(field, capability) {
                vmwrite(field, vcpu::read_vmcs(s, v, field));
            }
        }
        vmwrite(CONTROL_PAGE_FAULT_MASK, 0);
        vmwrite(CONTROL_PAGE_FAULT_MATCH, 0);
        vmwrite(CONTROL_CR3_TARGET_COUNT, 0);
        vmwrite(GUEST_VMCS_LINK_POINTER, u64::MAX);
        vmwrite(CONTROL_IOA_ADDRESS, physical(v + vcpu::IO));
        vmwrite(CONTROL_IOB_ADDRESS, physical(v + vcpu::IO + 4096));
        vmwrite(CONTROL_MSR_ADDRESS, physical(maps().msr.as_ptr() as u64));
        vmwrite(CONTROL_EPT_POINTER, physical(root) | 6 | (3 << 3));
        vmwrite(
            CONTROL_EXIT_MSR_STORE_ADDRESS,
            physical(guest_list.as_mut_ptr() as u64),
        );
        vmwrite(
            CONTROL_EXIT_MSR_LOAD_ADDRESS,
            physical(host_list.as_ptr() as u64),
        );
        vmwrite(
            CONTROL_ENTRY_MSR_LOAD_ADDRESS,
            physical(guest_list.as_ptr() as u64),
        );
        vmwrite(CONTROL_EXIT_MSR_STORE_COUNT, 5);
        vmwrite(CONTROL_EXIT_MSR_LOAD_COUNT, 5);
        vmwrite(CONTROL_ENTRY_MSR_LOAD_COUNT, 5);
        vmwrite(HOST_RIP, fl4_vmx_exit as *const () as u64);
        host_vmcs(&gdt, &idt, tr);
    }
    if run.host_xcr0 != 0 && run.guest_xcr0 != run.host_xcr0 {
        cpu::xsetbv(0, run.guest_xcr0);
    }
    if !amd {
        unsafe {
            asm!("mov cr2, {}", in(reg) run.guest_cr2, options(nostack));
        }
    }
    unsafe {
        if amd {
            fl4_svm_run(&mut run)
        } else {
            fl4_vmx_run(&mut run)
        }
    }
    // Restore host-only state even if entry failed its checks.
    if run.host_xcr0 != 0 && run.guest_xcr0 != run.host_xcr0 {
        cpu::xsetbv(0, run.host_xcr0);
    }
    run.guest_cr2 = if amd {
        vcpu::get(s, v, svm::CR2)
    } else {
        cpu::read_cr2()
    };
    unsafe {
        asm!("mov cr2, {}", in(reg) run.host_cr2, options(nostack));
        if !amd {
            asm!("lgdt [{}]", "lidt [{}]", in(reg) &gdt, in(reg) &idt, options(nostack));
        }
    }
    if !amd || fl4_abi::config::HARDWARE_DEBUG_API {
        cpu::write_dr6(0xffff_0ff0);
        cpu::write_dr7(0x400);
    }
    let reason;
    let mut interrupt = u64::MAX;
    let mut exit = [0u64; 30];
    let valid;
    if amd {
        reason = vcpu::get(s, v, svm::EXIT_CODE);
        valid = reason != u64::MAX && reason != 0xffff_ffff;
        local().svm.valid = valid;
        if valid {
            // Snapshot hardware's final values, not the previous input:
            // the guest can change a cached register before exiting.
            local().svm.observe(|off| vcpu::get(s, v, off));
            vcpu::set(s, v, vcpu::SVM_CPU, s.cur_cpu() + 1);
        }
        run.regs[0] = vcpu::get(s, v, svm::RAX);
        exit[0] = vcpu::get(s, v, svm::RIP);
        exit[1] = vcpu::get(s, v, svm::INTERCEPT_EXC) >> 32;
        exit[2] = if valid {
            vcpu::get(s, v, svm::EVENT_INJ) & !(1 << 31)
        } else {
            vcpu::get(s, v, svm::EVENT_INJ)
        };
        exit[3] = if valid { reason } else { 0xffff_ffff };
        exit[4] = if valid {
            vcpu::get(s, v, svm::EXIT_INFO1)
        } else {
            0
        };
        let next = vcpu::get(s, v, svm::NEXT_RIP);
        exit[5] = if valid && next != 0 {
            next.wrapping_sub(exit[0])
        } else {
            0
        };
        exit[6] = if valid {
            vcpu::get(s, v, svm::EXIT_INFO2)
        } else {
            0
        };
        exit[7] = vcpu::get(s, v, svm::RFLAGS);
        exit[8] = vcpu::get(s, v, svm::INT_STATE);
        exit[9] = vcpu::get(s, v, svm::CR3);
        let vector = if valid {
            vcpu::get(s, v, svm::EXIT_INT_INFO)
        } else {
            0
        };
        exit[27] = vector & 0xffff_ffff;
        exit[28] = if vector & (1 << 11) != 0 {
            vector >> 32
        } else {
            0
        };
        if valid {
            vcpu::set(s, v, svm::EVENT_INJ, 0);
        }
        vcpu::set(s, v, svm::NEXT_RIP, 0);
        // Reinject events interrupted by exits invisible to userspace.
        if (0x60..=0x63).contains(&reason) && vector & (1 << 31) != 0 {
            let ty = (vector >> 8) & 7;
            if ty != 4 && !(ty == 3 && matches!(vector & 255, 3 | 4)) {
                vcpu::set(s, v, svm::EVENT_INJ, vector & vcpu::SVM_EVENT);
            }
        }
        if reason == 0x7f {
            vcpu::reset_svm(s, v);
            run.regs[0] = 0;
            exit[0] = 0xfff0;
            exit[7] = 2;
            exit[8] = 0;
            exit[9] = 0;
            run.guest_cr2 = 0;
        }
    } else {
        let raw = vmread(DATA_EXIT_REASON);
        reason = if run.failed != 0 {
            0xffff_ffff
        } else {
            raw & 0xffff
        };
        valid = local().vmx.finish_entry(run.failed != 0, raw);
        local().vmx.observe(HOST_RSP, run.host_rsp);
        for field in vcpu::READ_FIELDS {
            // Undefined exit fields must not expose another VCPU's last
            // exit from this core's reusable VMCS.
            let value = if field & 0xc00 == 0x400 || !vmcs_field_exists(field, capability) {
                0
            } else {
                vmread(field)
            };
            vcpu::write_vmcs(s, v, field, value);
        }
        for (i, msr) in guest_list.iter().enumerate() {
            vcpu::set(s, v, vcpu::MSRS + i as u64 * 8, msr.value);
        }
        exit[0] = vmread(GUEST_RIP);
        exit[1] = vcpu::read_vmcs(s, v, CONTROL_PRIMARY_PROCESSOR_CONTROLS);
        exit[2] = vmread(CONTROL_ENTRY_INTERRUPTION_INFO);
        if valid {
            exit[2] &= !(1 << 31);
            vcpu::write_vmcs(s, v, CONTROL_ENTRY_INTERRUPTION_INFO, exit[2]);
        }
        exit[3] = reason;
        if run.failed != 0 {
            exit[4] = u64::MAX;
        } else if matches!(reason, 0 | 4 | 9 | 14 | 19 | 21..=23 | 25 | 27..=30 | 33 | 34 | 36 | 43 | 44 | 46..=48 | 50 | 53 | 58)
        {
            exit[4] = vmread(DATA_EXIT_QUALIFICATION);
        }
        let metadata = vmx_exit::read(valid, reason, exit[4], BASIC.load(Ordering::Relaxed), vmread);
        let vector = metadata.vector;
        exit[5] = metadata.length;
        if valid && matches!(reason, 48 | 49) {
            exit[6] = vmread(DATA_GUEST_PHYSICAL);
        }
        exit[7] = vmread(GUEST_RFLAGS);
        exit[8] = vmread(GUEST_INTERRUPTABILITY);
        exit[25] = metadata.interrupt;
        exit[26] = metadata.interrupt_error;
        exit[27] = vector;
        exit[28] = metadata.vector_error;
        if reason == 1 && capability(0x483) >> 32 & (1 << 15) != 0 {
            interrupt = vmread(DATA_EXIT_INTERRUPT_INFO) & 255;
        }
        // Reinject events interrupted by exits invisible to userspace: an
        // external interrupt or an NMI the host takes. Software events go
        // unreinjected, as on SVM: the guest's RIP is still at the INT n,
        // INT3, INTO or INT1, which runs again; injecting them would need a
        // VM-entry instruction length these exits do not define.
        if vmx_exit::host_exit(reason, exit[25]) && vmx_exit::reinjected(vector) {
            vcpu::write_vmcs(s, v, CONTROL_ENTRY_INTERRUPTION_INFO, vector & !(1 << 12));
            vcpu::write_vmcs(s, v, CONTROL_ENTRY_EXCEPTION_ERROR_CODE, exit[28]);
            if (vector >> 8) & 7 == 2 {
                vcpu::write_vmcs(s, v, GUEST_INTERRUPTABILITY, exit[8] & !(1 << 3));
            }
        }
        if valid && reason == 30 {
            for (field, value) in [
                (DATA_IO_RCX, run.regs[2]),
                (DATA_IO_RSI, run.regs[4]),
                (DATA_IO_RDI, run.regs[5]),
                (DATA_IO_RIP, exit[0]),
            ] {
                vcpu::write_vmcs(s, v, field, value);
            }
        }
        for (field, value) in [
            (
                DATA_INSTRUCTION_ERROR,
                if run.failed != 0 {
                    vmread(DATA_INSTRUCTION_ERROR)
                } else {
                    0
                },
            ),
            (DATA_EXIT_INTERRUPT_INFO, exit[25]),
            (DATA_EXIT_INTERRUPT_ERROR, exit[26]),
            (DATA_IDT_VECTOR_INFO, exit[27]),
            (DATA_IDT_VECTOR_ERROR, exit[28]),
            (DATA_EXIT_INSTRUCTION_LENGTH, exit[5]),
            (DATA_EXIT_INSTRUCTION_INFO, metadata.instruction),
            (DATA_GUEST_PHYSICAL, exit[6]),
            (
                DATA_GUEST_LINEAR_ADDRESS,
                if reason == 48 && exit[4] & (1 << 7) != 0 {
                    vmread(DATA_GUEST_LINEAR_ADDRESS)
                } else {
                    0
                },
            ),
        ] {
            vcpu::write_vmcs(s, v, field, value);
        }
    }
    exit[10..25].copy_from_slice(&run.regs);
    exit[29] = run.guest_cr2;
    for (i, val) in run.regs.iter().enumerate() {
        vcpu::set(s, v, vcpu::REGS + i as u64 * 8, *val);
    }
    for (i, val) in exit.iter().enumerate() {
        vcpu::set(s, v, vcpu::EXIT + i as u64 * 8, *val);
    }
    vcpu::set(s, v, vcpu::CR2, run.guest_cr2);
    vcpu::set(s, v, vcpu::VALID, if valid { 1 } else { 0 });
    let host_exit = if amd {
        matches!(reason, 0x60..=0x63)
    } else {
        vmx_exit::host_exit(reason, exit[25])
    };
    if !amd && reason == 0 && host_exit {
        // An NMI exit leaves NMIs blocked until the next IRET, which VM
        // entry with virtual NMIs does not replace: unblock them now. (The
        // kernel's NMI handler ignores NMIs, so none is lost.)
        cpu::iret_to_self();
    }
    vcpu::set(s, v, vcpu::PENDING, if host_exit { 0 } else { 1 });
    // 0x100 means poll the local APIC; 0xff is spurious/no IRQ.
    if host_exit {
        if (amd && reason == 0x60) || (!amd && reason == 1) {
            if interrupt == u64::MAX {
                0x100
            } else {
                interrupt
            }
        } else {
            0xff
        }
    } else {
        0xff
    }
}
pub fn empty_root() -> u64 {
    maps().empty.0.as_ptr() as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vmx_exit_entries_preserve_guest_registers_and_restore_the_host_stack() {
        extern "C" {
            fn fl4_test_vmx_exit(run: *mut Run, exit: unsafe extern "C" fn());
        }
        // Exercise the real software sequences. Linked-image checks cover
        // privileged WRMSR ordering; AMD guest tests exercise IBPB. Intel
        // IBRS runtime validation requires Intel hardware.
        for speculation in [0, spec::policy::RSB, spec::policy::PBRSB,
                            spec::policy::BHB | spec::policy::IBHF,
                            spec::policy::RSB | spec::policy::PBRSB | spec::policy::BHB | spec::policy::IBHF] {
            let regs = core::array::from_fn(|i| 0x1234_5678_9abc_de00 + i as u64);
            let mut run = Run {
                regs,
                reserved: 0,
                vmcb: 0,
                host: 0,
                host_cr2: 0,
                host_xcr0: 0,
                guest_xcr0: 0,
                guest_cr2: 0,
                failed: 1,
                resume: 0,
                host_rsp: 0,
                speculation: speculation as u64,
            };
            unsafe { fl4_test_vmx_exit(&mut run, fl4_vmx_exit) };
            assert_eq!(run.regs, regs);
            assert_eq!(run.failed, 0);
        }
    }

    #[test]
    fn svm_host_save_tracks_tls_and_the_dangerous_msr_profile() {
        let mut host = SvmHost::default();
        assert!(host.needs_save((0, 0, 0, 0), false));
        assert!(!host.needs_save((0, 0, 0, 0), false));
        for tls in [
            (0x1000, 0, 0, 0),
            (0x1000, 0x2000, 0, 0),
            (0x1000, 0x2000, 0x2b, 0),
            (0x1000, 0x2000, 0x2b, 0x2b),
        ] {
            assert!(host.needs_save(tls, false));
            assert!(!host.needs_save(tls, false));
            assert!(host.needs_save(tls, true));
        }
    }
    #[test]
    fn svm_asid_reuse_requires_the_same_live_owner_and_completed_entry() {
        let mut state = SvmState::new();
        assert!(state.prepare(0x1000, 0x2000, 0, 0)); // First entry.
        assert!(state.prepare(0x1000, 0x2000, 1, 0)); // Failed entry.
        state.valid = true;
        assert!(!state.prepare(0x1000, 0x2000, 1, 0));
        for (v, root, owner) in [
            (0x1000, 0x2000, 2), // Migrated away and back.
            (0x1000, 0x2000, 0), // Retype, flush, paging write or reset.
            (0x1000, 0x3000, 1), // Replaced nested root.
            (0x4000, 0x3000, 1), // Another VCPU sharing that root.
        ] {
            state.valid = true;
            assert!(state.prepare(v, root, owner, 0));
        }
        state.valid = false; // Local or remote nested invalidation.
        assert!(state.prepare(0x4000, 0x3000, 1, 0));
    }

    #[test]
    fn svm_clean_groups_track_hardware_results_and_software_rewinds() {
        let mut state = SvmState::new();
        let mut vmcb = [0u64; 0x700 / 8];
        state.observe(|off| vmcb[off as usize / 8]);
        assert_eq!(state.clean(|off| vmcb[off as usize / 8]), 0x3f7);
        // Every represented field dirties its whole group, not others.
        for &(off, group) in SVM_CACHED {
            vmcb[off as usize / 8] = 1;
            assert_eq!(
                state.clean(|off| vmcb[off as usize / 8]),
                0x3f7 & !(1 << group)
            );
            vmcb[off as usize / 8] = 0;
        }
        // A guest changes CR3, then the VMM restores the previous value.
        vmcb[svm::CR3 as usize / 8] = 0x8000;
        state.observe(|off| vmcb[off as usize / 8]);
        vmcb[svm::CR3 as usize / 8] = 0;
        assert_eq!(state.clean(|off| vmcb[off as usize / 8]) & (1 << 5), 0);
        // Always-loaded RIP and event injection cannot become cached.
        vmcb[svm::RIP as usize / 8] = 0x1234;
        vmcb[svm::EVENT_INJ as usize / 8] = 1 << 31;
        assert_eq!(state.clean(|off| vmcb[off as usize / 8]), 0x3f7 & !(1 << 5));
    }

    #[test]
    fn vmcs_reentry_writes_no_unchanged_fields() {
        let mut state = VmcsState::new();
        let mut writes = 0;
        for field in vcpu::WRITE_FIELDS {
            state.write(field, 0, |_, _| writes += 1);
        }
        // Even zero-valued fields must be initialized on the first entry.
        assert_eq!(writes, vcpu::WRITE_FIELDS.len());
        writes = 0;
        for _ in 0..16 {
            for field in vcpu::WRITE_FIELDS {
                state.write(field, 0, |_, _| writes += 1);
            }
        }
        assert_eq!(writes, 0);
    }
    #[test]
    fn vmcs_cache_observes_guest_changes_before_restoring_old_values() {
        let mut state = VmcsState::new();
        state.write(GUEST_RIP, 0x20, |_, _| {});
        // Guest execution advanced RIP; VMREAD must update the cache.
        state.observe(GUEST_RIP, 0x21);
        state.write(GUEST_RIP, 0x21, |_, _| {
            panic!("RIP already matches hardware")
        });
        let mut write = None;
        state.write(GUEST_RIP, 0x20, |f, value| write = Some((f, value)));
        assert_eq!(write, Some((GUEST_RIP, 0x20)));
    }
    #[test]
    fn vmcs_switches_program_each_vcpus_values() {
        let mut state = VmcsState::new();
        let fields = [
            GUEST_CR3,
            GUEST_PAT,
            CONTROL_EPT_POINTER,
            CONTROL_IOA_ADDRESS,
        ];
        for base in [0x1000, 0x2000, 0x1000, 0] {
            let mut writes = 0;
            for (i, field) in fields.iter().enumerate() {
                state.write(*field, base + i as u64, |_, _| writes += 1);
            }
            assert_eq!(writes, fields.len());
            for (i, field) in fields.iter().enumerate() {
                assert_eq!(state.get(*field), Some(base + i as u64));
            }
        }
    }
    #[test]
    fn vmcs_failed_entries_preserve_the_launch_state() {
        let mut state = VmcsState::new();
        assert!(!state.launched);
        assert!(!state.finish_entry(true, 0));
        assert!(!state.finish_entry(false, (1 << 31) | 33));
        assert!(!state.launched);
        assert!(state.finish_entry(false, 10));
        assert!(state.launched);
        assert!(!state.finish_entry(true, 10));
        assert!(!state.finish_entry(false, (1 << 31) | 33));
        assert!(state.launched);
        assert!(state.finish_entry(false, 10));
    }
    #[test]
    fn vmx_probe_does_not_read_absent_secondary_controls() {
        for true_controls in [false, true] {
            let mut primary_read = false;
            let caps = read_vmx_capabilities(true_controls, true, |msr| match msr {
                0x482 | 0x48e => {
                    primary_read = true;
                    !(1 << 63)
                }
                0x48b => panic!("secondary-control MSR does not exist"),
                _ => u64::MAX,
            });
            assert!(primary_read);
            assert!(caps.is_none());
        }
    }
    #[test]
    fn vmx_probe_reads_supported_secondary_controls_after_primary_controls() {
        for true_controls in [false, true] {
            let mut primary_read = false;
            let caps = read_vmx_capabilities(true_controls, true, |msr| match msr {
                0x482 | 0x48e => {
                    primary_read = true;
                    1 << 63
                }
                0x48b => {
                    assert!(primary_read);
                    2 << 32
                }
                _ => 0,
            })
            .unwrap();
            assert_eq!(caps[2], 1 << 63);
            assert_eq!(caps[0xb], 2 << 32);
        }
    }
    #[test]
    fn vmx_perf_controls_require_an_available_pmu() {
        for (max_leaf, pmu_eax, available) in [
            (9, 2, false),
            (0xa, 0, false),
            (0xa, 0x0730_0400, false),
            (0xa, 1, false),
            (0xa, 0x0730_0402, true),
            (0x20, 5, true),
        ] {
            assert_eq!(has_perf_global_ctrl(max_leaf, pmu_eax), available);
            for (field, bit) in [(0x483, 1u64 << 12), (0x484, 1 << 13)] {
                let raw = 0xffff_ffff_0000_0000 | (1 << 9);
                let filtered = pmu_controls(field, raw, available).unwrap();
                assert_eq!((filtered >> 32) & bit != 0, available);
                assert_eq!(filtered & !(bit << 32), raw & !(bit << 32));
                assert_eq!(
                    pmu_controls(field, raw | bit, available).is_some(),
                    available
                );
            }
        }
        assert_eq!(pmu_controls(0x482, u64::MAX, false), Some(u64::MAX));
    }
    #[test]
    fn vmx_entries_skip_vmcs_fields_of_absent_controls() {
        // Neither the PMU load control nor the preemption timer: VM entry
        // and exit must not VMREAD/VMWRITE their fields (VM-instruction
        // error 12 would replace a failed entry's error number).
        let none = |f: u64| match f {
            0x481 => vcpu::PIN_ALLOWED << 32,
            0x484 => 1 << (32 + 9),
            _ => u64::MAX,
        };
        let all = |f: u64| none(f) | match f {
            0x481 => 1 << (32 + 6),
            0x484 => 1 << (32 + 13),
            _ => 0,
        };
        for (cap, expect) in [(&none as &dyn Fn(u64) -> u64, false), (&all, true)] {
            for list in [&vcpu::WRITE_FIELDS[..], &vcpu::READ_FIELDS[..]] {
                for &field in list {
                    let optional = matches!(field, GUEST_PERF_GLOBAL_CTRL | GUEST_PREEMPTION_TIMER_VALUE);
                    assert_eq!(vmcs_field_exists(field, cap), !optional || expect, "{field:#x}");
                }
            }
        }
        // The fields run() touches for every VCPU are always present.
        assert!(vmcs_field_exists(GUEST_RIP, none));
        assert!(vmcs_field_exists(CONTROL_ENTRY_CONTROLS, none));
    }
    #[test]
    fn vmx_true_control_msr_addresses() {
        for (base, address) in [
            (0x481, 0x48d),
            (0x482, 0x48e),
            (0x483, 0x48f),
            (0x484, 0x490),
            (0x48b, 0x48b),
        ] {
            assert_eq!(control_msr(base, true), address);
            assert_eq!(control_msr(base, false), base);
        }
    }
    #[test]
    fn address_width_follows_the_paging_mode_in_use() {
        // A CPU with LA57 (CPUID.07H:ECX[16]) that runs 4-level paging.
        assert_eq!(canonical_width(0x0035_06f0), 48);
        assert_eq!(canonical_width(0x0035_06f0 | 1 << 12), 57);
    }
    #[test]
    fn physical_addresses_cover_both_kernel_mappings() {
        assert_eq!(physical(layout::pptr(0x123000)), 0x123000);
        assert_eq!(physical(0xffffffff80123000), 0x123000);
    }
    #[test]
    fn msr_bitmaps_grant_only_the_requested_register() {
        let mut bitmap = [255u8; 8192];
        pass_msr(&mut bitmap, 0xc0000102, false);
        assert_eq!(bitmap[1024 + 32], 255 & !4);
        assert_eq!(bitmap[3072 + 32], 255 & !4);
        assert_eq!(bitmap.iter().filter(|&&v| v != 255).count(), 2);
        let mut bitmap = [255u8; 8192];
        pass_msr(&mut bitmap, 0xc0000102, true);
        assert_eq!(bitmap[0x800 + 64], 255 & !(3 << 4));
        assert_eq!(bitmap.iter().filter(|&&v| v != 255).count(), 1);
    }
}
