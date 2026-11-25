//! Trusted VMX/SVM instruction boundary. Policy lives in fl4-core::vcpu.
//!
//! Each core retains its own VMCS and resumes it after the first launch.
//! Its field cache follows VMWRITE and VMREAD, so unchanged fields need no
//! VMWRITE even when a guest changed them. A VCPU's complete software image
//! is saved before remote calls can move/delete it; the hardware VMCS never
//! migrates or belongs to user memory. EPT translations survive entries;
//! unmaps and root deletion invalidate every core recorded for the root.
//! VMX tags guest translations with VPID 1 when the CPU can invalidate it
//! (`vpid_mode`), as SVM does with ASID 1: either is retained only for the
//! last VCPU/root on a core; migration, software paging changes and
//! invalidation revoke it. VPID 0 (the host's and every native address
//! space's) is then no longer flushed at each VM entry and exit.
use crate::{cpu, fpu, percpu, spec, tlb};
use core::arch::asm;
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicU64, Ordering};
use fl4_abi::consts::kernel_config::{virt_features, virt_reject};
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

// The kernel's Safe RET routines (fl4-kernel's safe_ret.S), which vm.S's
// SVM exit calls; host test builds of this crate alone link without them,
// and never run a guest.
#[cfg(not(target_os = "none"))]
core::arch::global_asm!(
    ".weak fl4_untrain_ret", "fl4_untrain_ret: ret",
    ".weak __x86_return_thunk", "__x86_return_thunk: ret",
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

/// A VCPU's own VMCS (in its object at `vcpu::VMCS`, the VMCB's page) and
/// its bookkeeping (at `vcpu::VMX_STATE`, zero after retype). The VMCS
/// keeps the guest's state between exits, as seL4's and KVM's do: an exit
/// reads only what kernel logic and the exit message need (`EAGER`), and
/// the other guest-state fields reach the software image when an
/// invocation needs one (`sync`). A VMCS is VMCLEARed on the core that
/// last loaded it before another core loads it (`load`) or its object is
/// deleted (`release`).
///
/// Per tracked field (`slot`): `values` holds what the VMCS holds where
/// `valid` says so, so an entry writes only what changed; `synced` says
/// that the image holds it too. A field not synced is a guest-state field
/// the guest may have changed since its last exit; its image and `values`
/// still agree, so an entry leaves it alone.
#[repr(C)]
struct VmcsState {
    /// The core (index + 1) that loaded the VMCS since it was last
    /// cleared, if any.
    active: u64,
    flags: u64,
    valid: [u64; SLOT_WORDS],
    synced: [u64; SLOT_WORDS],
    values: [u64; SLOTS],
}
/// `VmcsState::flags`: the region has its revision identifier and its
/// tracked values; VMRESUME rather than VMLAUNCH.
const VMCS_INIT: u64 = 1;
const VMCS_LAUNCHED: u64 = 2;
const SLOTS: usize = 192;
const SLOT_WORDS: usize = SLOTS / 64;
const _: () = assert!(
    core::mem::size_of::<VmcsState>() as u64 <= vcpu::IO - vcpu::VMX_STATE
        && vcpu::VMX_STATE >= vcpu::EXIT + vcpu::NUM_MRS * 8
);

/// Fields the backend writes besides `vcpu::WRITE_FIELDS`: host state and
/// the kernel's own controls.
const BACKEND_FIELDS: [u64; 35] = [
    HOST_CR0, HOST_CR3, HOST_CR4, HOST_ES_SELECTOR, HOST_CS_SELECTOR, HOST_SS_SELECTOR, HOST_DS_SELECTOR,
    HOST_FS_SELECTOR, HOST_GS_SELECTOR, HOST_TR_SELECTOR, HOST_FS_BASE, HOST_GS_BASE, HOST_TR_BASE,
    HOST_GDTR_BASE, HOST_IDTR_BASE, HOST_SYSENTER_CS, HOST_SYSENTER_ESP, HOST_SYSENTER_EIP, HOST_EFER,
    HOST_PAT, HOST_PERF_GLOBAL_CTRL, HOST_RIP, HOST_RSP, CONTROL_VPID, CONTROL_PAGE_FAULT_MASK,
    CONTROL_PAGE_FAULT_MATCH, CONTROL_CR3_TARGET_COUNT, GUEST_VMCS_LINK_POINTER, CONTROL_IOA_ADDRESS,
    CONTROL_IOB_ADDRESS, CONTROL_MSR_ADDRESS, CONTROL_EPT_POINTER, CONTROL_EXIT_MSR_STORE_ADDRESS,
    CONTROL_EXIT_MSR_LOAD_ADDRESS, CONTROL_ENTRY_MSR_LOAD_ADDRESS,
];
const BACKEND_COUNTS: [u64; 3] =
    [CONTROL_EXIT_MSR_STORE_COUNT, CONTROL_EXIT_MSR_LOAD_COUNT, CONTROL_ENTRY_MSR_LOAD_COUNT];

/// The software image's index of `field` (`vcpu::vmcs_addr`).
const fn image_index(field: u64) -> usize {
    (((field & 0xff) >> 1) | (((field >> 10) & 3) << 7) | (((field >> 13) & 3) << 9)) as usize
}
/// Per image index: its slot + 1, or 0 for a field not tracked (always
/// written, never cached); and how many slots there are.
const fn slot_table() -> ([u8; 2048], usize) {
    let mut t = [0u8; 2048];
    let mut n = 0;
    let lists: [&[u64]; 4] = [&vcpu::READ_FIELDS, &vcpu::WRITE_FIELDS, &BACKEND_FIELDS, &BACKEND_COUNTS];
    let mut l = 0;
    while l < lists.len() {
        let mut i = 0;
        while i < lists[l].len() {
            let x = image_index(lists[l][i]);
            if t[x] == 0 {
                n += 1;
                t[x] = n as u8;
            }
            i += 1;
        }
        l += 1;
    }
    (t, n)
}
static SLOT: [u8; 2048] = slot_table().0;
const _: () = assert!(slot_table().1 <= SLOTS);
/// Per slot: its field, so that an encoding the image index aliases (a
/// high half, a reserved bit) is not taken for a tracked field.
static FIELD: [u64; SLOTS] = {
    let t = slot_table().0;
    let mut f = [u64::MAX; SLOTS];
    let lists: [&[u64]; 4] = [&vcpu::READ_FIELDS, &vcpu::WRITE_FIELDS, &BACKEND_FIELDS, &BACKEND_COUNTS];
    let mut l = 0;
    while l < lists.len() {
        let mut j = 0;
        while j < lists[l].len() {
            f[t[image_index(lists[l][j])] as usize - 1] = lists[l][j];
            j += 1;
        }
        l += 1;
    }
    f
};
/// Guest-state fields an exit reads (kernel logic and the exit message
/// use them); the guest's other guest-state fields are read on demand.
const fn eager(field: u64) -> bool {
    field & 0xc00 != 0x800 || matches!(field, GUEST_RIP | GUEST_RFLAGS | GUEST_INTERRUPTABILITY)
}
/// `VmcsState::synced` after an exit: every tracked field but the lazy
/// guest-state ones.
const SYNCED_AFTER_EXIT: [u64; SLOT_WORDS] = {
    let t = slot_table().0;
    let mut m = [0u64; SLOT_WORDS];
    let lists: [&[u64]; 4] = [&vcpu::READ_FIELDS, &vcpu::WRITE_FIELDS, &BACKEND_FIELDS, &BACKEND_COUNTS];
    let mut l = 0;
    while l < lists.len() {
        let mut j = 0;
        while j < lists[l].len() {
            let f = lists[l][j];
            let i = t[image_index(f)] as usize - 1;
            if eager(f) {
                m[i / 64] |= 1 << (i % 64);
            }
            j += 1;
        }
        l += 1;
    }
    m
};

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
/// VPID 1 on this core (`vpid_mode` nonzero): which VCPU and EPT root its
/// translations are of, as `SvmState` for ASID 1. The VCPU's owner word
/// (`vcpu::SVM_CPU`) distinguishes migration and retype at the same
/// address; core policy also clears it for explicit TLB flushes and
/// software writes of the guest's paging registers.
struct VmxVpidState {
    vcpu: u64,
    root: u64,
    valid: bool,
}
impl VmxVpidState {
    const fn new() -> Self {
        Self { vcpu: 0, root: 0, valid: false }
    }
    /// Whether VPID 1 must be invalidated before entering `vcpu` on
    /// `root`, whose owner word is `owner`, on core `cpu`.
    fn prepare(&mut self, vcpu: u64, root: u64, owner: u64, cpu: u64) -> bool {
        let flush = !self.valid || self.vcpu != vcpu || self.root != root || owner != cpu + 1;
        self.vcpu = vcpu;
        self.root = root;
        // A failed entry need not have run the guest on what was flushed;
        // the next one flushes again.
        self.valid = false;
        flush
    }
}

/// How VMX tags guest translations, from IA32_VMX_PROCBASED_CTLS2 (`secondary`,
/// allowed-1 settings in bits 63:32) and IA32_VMX_EPT_VPID_CAP (`ept`):
/// 0, no VPID (each entry and exit flushes VPID 0, the host's own);
/// 1, VPID 1 invalidated with single-context INVVPID (type 1); 2, with
/// all-context INVVPID (type 2, every VPID but 0). Both leave VPID 0's
/// translations alone. VPID needs "enable VPID" (secondary bit 5) and
/// INVVPID (EPT_VPID_CAP bit 32) with one of those types (bits 41, 42);
/// the single-context-retaining-globals type (bit 43) is never used: a
/// guest's global translations must not survive another VCPU's entry.
fn vpid_mode(secondary: u64, ept: u64) -> u64 {
    if (secondary >> 32) & (1 << 5) == 0 || ept & (1 << 32) == 0 {
        0
    } else if ept & (1 << 41) != 0 {
        1
    } else if ept & (1 << 42) != 0 {
        2
    } else {
        0
    }
}

/// INVVPID of `kind` (1 or 2, `vpid_mode`) for VPID 1: the descriptor's
/// bits 63:16 must be zero (SDM Vol. 3 INVVPID), and type 2 ignores the
/// VPID.
fn invvpid(kind: u64) {
    let descriptor: [u64; 2] = [if kind == 1 { 1 } else { 0 }, 0];
    unsafe {
        asm!("invvpid {kind}, [{ptr}]", kind=in(reg) kind, ptr=in(reg) descriptor.as_ptr(), options(nostack));
    }
}

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
    #[cfg(test)]
    const fn new() -> Self {
        Self { active: 0, flags: 0, valid: [0; SLOT_WORDS], synced: [0; SLOT_WORDS], values: [0; SLOTS] }
    }
    /// A fresh VMCS: nothing cached, the image is everything.
    fn reset(&mut self) {
        self.flags = VMCS_INIT;
        self.valid = [0; SLOT_WORDS];
        self.synced = [u64::MAX; SLOT_WORDS];
    }
    fn index(field: u64) -> Option<usize> {
        match SLOT[image_index(field) & 2047] {
            0 => None,
            n if FIELD[n as usize - 1] != field => None,
            n => Some(n as usize - 1),
        }
    }
    fn get(&self, field: u64) -> Option<u64> {
        let i = Self::index(field)?;
        if self.valid[i / 64] & (1 << (i % 64)) != 0 {
            Some(self.values[i])
        } else {
            None
        }
    }
    fn observe(&mut self, field: u64, value: u64) {
        if let Some(i) = Self::index(field) {
            self.values[i] = value;
            self.valid[i / 64] |= 1 << (i % 64);
        }
    }
    fn write(&mut self, field: u64, value: u64, write: impl FnOnce(u64, u64)) {
        if self.get(field) != Some(value) {
            write(field, value);
            self.observe(field, value);
        }
    }
    fn synced(&self, field: u64) -> bool {
        Self::index(field).is_none_or(|i| self.synced[i / 64] & (1 << (i % 64)) != 0)
    }
    fn set_synced(&mut self, field: u64) {
        if let Some(i) = Self::index(field) {
            self.synced[i / 64] |= 1 << (i % 64);
        }
    }
    fn launched(&self) -> bool {
        self.flags & VMCS_LAUNCHED != 0
    }
    fn finish_entry(&mut self, failed: bool, reason: u64) -> bool {
        let valid = !failed && reason & (1 << 31) == 0;
        // Failed launches stay clear; failed resumes stay launched. Intel
        // sets the launch state only after guest-state and MSR checks.
        if valid {
            self.flags |= VMCS_LAUNCHED;
        }
        valid
    }
}
/// VCPU `v`'s VMCS bookkeeping.
fn state(v: u64) -> &'static mut VmcsState {
    unsafe { &mut *((v + vcpu::VMX_STATE) as *mut VmcsState) }
}
/// The bookkeeping of this core's current VMCS.
fn cur() -> &'static mut VmcsState {
    debug_assert!(local().current != 0);
    state(local().current)
}

/// Whether VCPU `v`'s VMCS can be made current on this core without a
/// remote call: it is active here or nowhere (a VMCS may be active on
/// one core only).
pub fn loadable_here(v: u64) -> bool {
    backend() != 1 || v == 0 || state(v).active == 0 || state(v).active == percpu::cpu_index() as u64 + 1
}

/// VMCLEAR VCPU `v`'s VMCS on the core that last loaded it, if another,
/// so that this one may load it. A remote call: only with the serial gate
/// held or from a local path (`smp`'s module comment), never from `run`,
/// which runs after the gate is released and could otherwise take a stall
/// while it waits for `CALL_LOCK`. `v` does not run on any core.
pub fn evict(v: u64) {
    if backend() != 1 {
        return;
    }
    let st = state(v);
    let me = percpu::cpu_index() as u64 + 1;
    if st.active != 0 && st.active != me {
        crate::smp::remote_call(crate::smp::CALL_VMCLEAR, v, 0, 1 << (st.active - 1));
        st.active = 0;
    }
}

/// Make VCPU `v`'s VMCS current on this core, its region initialized the
/// first time. It is active here or nowhere (`evict` first). `v` does not
/// run on any core (it is this core's to run, or stalled).
fn load(v: u64) {
    let me = percpu::cpu_index() as u64 + 1;
    let st = state(v);
    assert!(st.active == 0 || st.active == me, "VMCS active on another core");
    let pa = physical(v + vcpu::VMCS);
    if st.active == 0 {
        if st.flags & VMCS_INIT == 0 {
            let id = BASIC.load(Ordering::Relaxed) as u32 & 0x7fff_ffff;
            unsafe { core::ptr::write_volatile((v + vcpu::VMCS) as *mut u32, id) };
            st.reset();
        }
        // Cleared (again): launch state clear, as VMPTRLD on a new core
        // needs. The region keeps the fields, so `values` stays valid.
        assert!(vmclear(pa) && vmptrld(pa));
        st.flags &= !VMCS_LAUNCHED;
        st.active = me;
    } else if local().current != v {
        assert!(vmptrld(pa));
    }
    local().current = v;
}

/// VMCLEAR VCPU `v`'s VMCS on this core (`smp::CALL_VMCLEAR`, `release`).
pub fn vmclear_local(v: u64) {
    assert!(vmclear(physical(v + vcpu::VMCS)));
    if local().current == v {
        local().current = 0;
    }
}

/// VCPU `v` is being deleted (`Arch::vcpu_release`): its VMCS is cleared
/// wherever it is active, so that no core writes it back to memory that
/// is reused.
pub fn release(v: u64) {
    if backend() != 1 {
        return;
    }
    let st = state(v);
    let me = percpu::cpu_index() as u64 + 1;
    match st.active {
        0 => {}
        a if a == me => vmclear_local(v),
        a => crate::smp::remote_call(crate::smp::CALL_VMCLEAR, v, 0, 1 << (a - 1)),
    }
    st.active = 0;
}

/// Before an invocation reads or writes field `field` of VCPU `v`'s
/// software image (`Arch::vcpu_sync`): a guest-state field the guest may
/// have changed since its last exit is read from its VMCS into the image
/// (and the cache, so a write of its old value back is seen as a change).
pub fn sync(v: u64, field: u64) {
    if backend() != 1 {
        return;
    }
    let st = state(v);
    if st.flags & VMCS_INIT == 0 || VmcsState::index(field).is_none() || st.synced(field) {
        return;
    }
    evict(v);
    load(v);
    let value = if !vmcs_field_exists(field, capability) {
        0
    } else if field == CONTROL_SECONDARY_PROCESSOR_CONTROLS {
        vmread(field) & !VPID_ENABLE
    } else {
        vmread(field)
    };
    unsafe { core::ptr::write_volatile(vcpu::vmcs_addr(v, field) as *mut u64, value) };
    st.set_synced(field);
}

#[repr(C, align(4096))]
struct Core {
    enable: Page,
    host: Page,
    /// The VCPU whose VMCS is current here (`load`), if any.
    current: u64,
    /// Host EFER, PAT and PERF_GLOBAL_CTRL, read once (`host_vmcs`).
    host_msrs: Option<[u64; 3]>,
    /// Host STAR, LSTAR, CSTAR and FMASK, read once (`run`).
    host_syscall: Option<[u64; 4]>,
    vmx_vpid: VmxVpidState,
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
            current: 0,
            host_msrs: None,
            host_syscall: None,
            vmx_vpid: VmxVpidState::new(),
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
/// Why the boot core has no backend (`virt_reject`); NONE with one.
static REJECT: AtomicU64 = AtomicU64::new(virt_reject::NONE);
static BASIC: AtomicU64 = AtomicU64::new(0);
static EPT_CAP: AtomicU64 = AtomicU64::new(0);
/// `vpid_mode` of the boot core, which every AP shares (`init_vmx` checks
/// that APs have the same capability MSRs).
static VPID_MODE: AtomicU64 = AtomicU64::new(0);
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

/// The physical address of `ptr`, in the window over physical memory or
/// in the kernel image, which the loader moved up by `delta`.
fn physical_at(ptr: u64, delta: u64) -> u64 {
    if ptr >= layout::PPTR_TOP {
        cpu::image_paddr_at(ptr, delta)
    } else {
        layout::paddr(ptr)
    }
}
fn physical(ptr: u64) -> u64 {
    physical_at(ptr, cpu::image_delta())
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
/// Why there is no backend (`virt_reject`), from the boot core's `init`.
pub(crate) fn reject() -> u64 {
    REJECT.load(Ordering::Relaxed)
}
/// The optional features in use (`virt_features`).
pub(crate) fn features() -> u64 {
    features_of(
        backend(),
        VPID_MODE.load(Ordering::Relaxed),
        EPT_CAP.load(Ordering::Relaxed),
        CAPS[0x484 - 0x480].load(Ordering::Relaxed),
        SVM_FEATURES.load(Ordering::Relaxed),
    )
}
/// `features` for a backend with these `vpid_mode`, EPT_VPID_CAP, VM-entry
/// controls and CPUID 8000_000AH:EDX. A probe that failed may have left
/// its findings behind: they count only for the backend chosen.
fn features_of(backend: u64, vpid: u64, ept: u64, entry_controls: u64, svm: u64) -> u64 {
    let on = |cond: bool, bit: u64| if cond { bit } else { 0 };
    match backend {
        1 => {
            on(vpid == 1, virt_features::X86_VPID_SINGLE)
                | on(vpid == 2, virt_features::X86_VPID_ALL)
                | on(ept & (1 << 25) != 0, virt_features::X86_INVEPT_SINGLE)
                | on(entry_controls >> 32 & (1 << 13) != 0, virt_features::X86_VMX_PERF_GLOBAL_CTRL)
        }
        2 => on(svm & (1 << 5) != 0, virt_features::X86_SVM_VMCB_CLEAN),
        _ => 0,
    }
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
    cur().observe(f, value);
    value
}
fn vmwrite(f: u64, value: u64) {
    cur().write(f, value, |field, value| unsafe {
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
/// CPUID 8000_000AH:EDX features `run` uses on every core as the boot
/// core found them (`SVM_FEATURES`): VMCB clean bits (bit 5). The ones
/// every core needs (nested paging, NRIP save) `init_svm` checks itself.
const SVM_SHARED: u32 = 1 << 5;

/// An AP whose CPUID 8000_000AH:EDX is `ap` has the shared features the
/// boot core (`bsp`) has.
fn svm_ap_compatible(bsp: u32, ap: u32) -> bool {
    bsp & SVM_SHARED & !ap == 0
}

/// Whether a core with CPUID 8000_0001H:ECX `ecx` (its maximum extended
/// leaf `max_ext`), CPUID 8000_000AH `svm` and VM_CR `vm_cr` (read only
/// once the rest allows it) can run guests under AMD-V, given the
/// speculation policy's leave (`policy`); else why not (`virt_reject`).
fn svm_usable(max_ext: u32, ecx: u32, policy: bool, svm: cpu::Cpuid, vm_cr: impl FnOnce() -> u64) -> Result<(), u64> {
    if max_ext < 0x8000_000a || ecx & 4 == 0 {
        return Err(virt_reject::NO_HW);
    }
    if !policy {
        return Err(virt_reject::SPEC_POLICY_REJECTED);
    }
    // Nested paging and NRIP save, and two ASIDs.
    if svm.edx & 9 != 9 || svm.ebx < 2 {
        return Err(virt_reject::MISSING_FEATURES);
    }
    // SVMDIS.
    if vm_cr() & 16 != 0 {
        return Err(virt_reject::DISABLED_BY_FIRMWARE);
    }
    Ok(())
}

fn init_svm(bsp: bool) -> Result<(), u64> {
    let max_ext = cpu::cpuid(0x8000_0000, 0).eax;
    let ecx = cpu::cpuid(0x8000_0001, 0).ecx;
    let c = cpu::cpuid(0x8000_000a, 0);
    svm_usable(max_ext, ecx, spec::vmexit().is_some(), c, || cpu::rdmsr(0xc001_0114))?;
    if !bsp && !svm_ap_compatible(SVM_FEATURES.load(Ordering::Relaxed) as u32, c.edx) {
        return Err(virt_reject::MISSING_FEATURES);
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
    Ok(())
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

/// IA32_FEATURE_CONTROL read as `feature`: the value to write first if it
/// is not locked yet, or why VMX cannot be used (locked with VMXON outside
/// SMX off).
fn vmx_feature_control(feature: u64) -> Result<Option<u64>, u64> {
    if feature & 1 == 0 {
        Ok(Some(feature | 5))
    } else if feature & 4 == 0 {
        Err(virt_reject::DISABLED_BY_FIRMWARE)
    } else {
        Ok(None)
    }
}

fn init_vmx(bsp: bool) -> Result<(), u64> {
    if cpu::cpuid(1, 0).ecx & (1 << 5) == 0 {
        return Err(virt_reject::NO_HW);
    }
    if spec::vmexit().is_none() {
        return Err(virt_reject::SPEC_POLICY_REJECTED);
    }
    let basic = cpu::rdmsr(0x480);
    if (basic >> 32) & 0x1fff > 4096 || (basic >> 50) & 15 != 6 {
        return Err(virt_reject::MISSING_FEATURES);
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
        return Err(virt_reject::MISSING_FEATURES);
    };
    for (saved, value) in CAPS.iter().zip(caps) {
        if bsp {
            saved.store(value, Ordering::Relaxed);
        } else if saved.load(Ordering::Relaxed) != value {
            return Err(virt_reject::MISSING_FEATURES);
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
            return Err(virt_reject::MISSING_FEATURES);
        }
    }
    // Reading EPT_VPID_CAP is safe only after verifying EPT support.
    let ept = cpu::rdmsr(0x48c);
    let required = (1 << 6) | (1 << 14) | (1 << 16) | (1 << 20);
    if ept & required != required || ept & ((1 << 25) | (1 << 26)) == 0 {
        return Err(virt_reject::MISSING_FEATURES);
    }
    if bsp {
        BASIC.store(basic, Ordering::Relaxed);
        EPT_CAP.store(ept, Ordering::Relaxed);
        VPID_MODE.store(vpid_mode(cap(0x48b), ept), Ordering::Relaxed);
    } else if BASIC.load(Ordering::Relaxed) != basic || EPT_CAP.load(Ordering::Relaxed) != ept {
        return Err(virt_reject::MISSING_FEATURES);
    }
    let cr0 = cpu::read_cr0();
    let cr4 = cpu::read_cr4() | (1 << 13);
    if cr0 & cap(0x486) != cap(0x486)
        || cr0 & !cap(0x487) != 0
        || cr4 & cap(0x488) != cap(0x488)
        || cr4 & !cap(0x489) != 0
    {
        return Err(virt_reject::MISSING_FEATURES);
    }
    if let Some(feature) = vmx_feature_control(cpu::rdmsr(0x3a))? {
        cpu::wrmsr(0x3a, feature);
    }
    let c = local();
    c.enable.0[..4].copy_from_slice(&(basic as u32 & 0x7fff_ffff).to_le_bytes());
    cpu::write_cr4(cr4);
    let pa = physical(c.enable.0.as_ptr() as u64);
    let fail: u8;
    unsafe {
        asm!("vmxon [{pa}]", "setna {fail}", pa=in(reg) &pa, fail=out(reg_byte) fail, options(nostack));
    }
    if fail != 0 {
        cpu::write_cr4(cr4 & !(1 << 13));
        return Err(virt_reject::VMXON_FAILED);
    }
    if bsp {
        let m = unsafe { &mut *MAPS.0.get() };
        for msr in [0x174, 0x175, 0x176, 0xc000_0100, 0xc000_0101, 0xc000_0102] {
            pass_msr(&mut m.msr, msr, false);
        }
    }
    Ok(())
}
/// Why a system with the skim window or in a confidential VM is not probed
/// for a backend.
fn unprobed(skim: bool, cvm: bool) -> Option<u64> {
    if cvm {
        Some(virt_reject::CVM_ACTIVE)
    } else if skim {
        Some(virt_reject::SKIM_ACTIVE)
    } else {
        None
    }
}

/// BSP picks the backend, APs must be able to provide the same interface.
pub fn init(bsp: bool) -> bool {
    if let Some(why) = unprobed(tlb::skim(), crate::cvm::active()) {
        if bsp {
            REJECT.store(why, Ordering::Relaxed);
        }
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
        REJECT.store(ok.err().unwrap_or(virt_reject::NONE), Ordering::Relaxed);
        BACKEND.store(if ok.is_ok() { chosen } else { 0 }, Ordering::Release);
        true
    } else {
        ok.is_ok()
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
    // INVEPT below removes this root's guest-physical and combined
    // translations for every VPID. Forget VPID 1 too: a root destroyed
    // and retyped at the same address must not find its old owner's.
    local().vmx_vpid.valid = false;
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
    let msrs = host_msrs();
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
        (HOST_EFER, msrs[0]),
        (HOST_PAT, msrs[1]),
    ] {
        vmwrite(field, value);
    }
    if capability(0x483) >> 32 & (1 << 12) != 0 {
        vmwrite(HOST_PERF_GLOBAL_CTRL, msrs[2]);
    }
}
/// The host's STAR, LSTAR, CSTAR and FMASK, read once per core; at every
/// entry where user code may write MSRs (KERNEL_X86_DANGEROUS_MSR, as
/// SVM's `SvmHost::needs_save`), so that such a write survives exits.
fn host_syscall_msrs() -> [u64; 4] {
    let read = || [cpu::rdmsr(0xc000_0081), cpu::rdmsr(0xc000_0082), cpu::rdmsr(0xc000_0083), cpu::rdmsr(0xc000_0084)];
    if fl4_abi::config::KERNEL_X86_DANGEROUS_MSR {
        return read();
    }
    *local().host_syscall.get_or_insert_with(read)
}
/// The host's EFER, PAT and PERF_GLOBAL_CTRL, which the kernel sets at
/// boot and never changes: read once per core, as an RDMSR is an exit of
/// its own under a hypervisor; at every entry where user code may write
/// MSRs (KERNEL_X86_DANGEROUS_MSR).
fn host_msrs() -> [u64; 3] {
    let read = || {
        // init_vmx removes this capability when CPUID does not expose a
        // usable PMU; a raw VMX capability bit alone cannot authorize RDMSR.
        let perf = if capability(0x483) >> 32 & (1 << 12) != 0 { cpu::rdmsr(0x38f) } else { 0 };
        [cpu::rdmsr(cpu::msr::EFER), cpu::rdmsr(0x277), perf]
    };
    if fl4_abi::config::KERNEL_X86_DANGEROUS_MSR {
        return read();
    }
    *local().host_msrs.get_or_insert_with(read)
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
        resume: 0,
        host_rsp: 0,
        speculation: spec::vmexit().expect("VM backend without speculation protection") as u64,
    };
    // The exit's IBPB at the next switch to another address space.
    if vcpu::get(s, v, vcpu::VM_IBPB_DEFER) != 0 && spec::vm_ibpb_deferred() {
        run.speculation &= !(spec::policy::IBPB as u64);
        percpu::get().guest_bp.set(percpu::get().cr3.get());
    }
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
    // STAR, LSTAR, CSTAR and FMASK are the kernel's, set at boot
    // (fl4-kernel's gdt.rs) and read once per core: under a hypervisor
    // each RDMSR of them is an exit of its own. KERNEL_GS_BASE holds the
    // swapped-out user GS base and is read every time.
    let syscall = if amd { [0; 4] } else { host_syscall_msrs() };
    let host_list: [Msr; 5] = core::array::from_fn(|i| Msr {
        number: msrs[i],
        reserved: 0,
        value: if amd {
            0
        } else if i < 4 {
            syscall[i]
        } else {
            cpu::rdmsr(msrs[i])
        },
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
        load(v);
        run.resume = cur().launched() as u64;
        run.host_rsp = cur().get(HOST_RSP).unwrap_or(0);
        let vpid = VPID_MODE.load(Ordering::Relaxed);
        for field in vcpu::WRITE_FIELDS {
            if vmcs_field_exists(field, capability) {
                vmwrite(field, secondary_with_vpid(field, vcpu::read_vmcs(s, v, field), vpid));
            }
        }
        if vpid != 0 {
            vmwrite(CONTROL_VPID, 1);
            if local().vmx_vpid.prepare(v, root, vcpu::get(s, v, vcpu::SVM_CPU), s.cur_cpu()) {
                invvpid(vpid);
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
        valid = cur().finish_entry(run.failed != 0, raw);
        cur().observe(HOST_RSP, run.host_rsp);
        if valid && VPID_MODE.load(Ordering::Relaxed) != 0 {
            local().vmx_vpid.valid = true;
            vcpu::set(s, v, vcpu::SVM_CPU, s.cur_cpu() + 1);
        }
        // The guest's other guest-state fields stay in its VMCS until an
        // invocation reads or writes one (`sync`).
        cur().synced = SYNCED_AFTER_EXIT;
        for field in vcpu::READ_FIELDS {
            // Exit fields this exit does not define, and fields this CPU
            // lacks (whatever a VMM wrote), read as zero.
            if field & 0xc00 == 0x400 || !vmcs_field_exists(field, capability) {
                vcpu::write_vmcs(s, v, field, 0);
            }
        }
        for (i, msr) in guest_list.iter().enumerate() {
            vcpu::set(s, v, vcpu::MSRS + i as u64 * 8, msr.value);
        }
        exit[0] = vmread(GUEST_RIP);
        vcpu::write_vmcs(s, v, GUEST_RIP, exit[0]);
        exit[1] = vcpu::read_vmcs(s, v, CONTROL_PRIMARY_PROCESSOR_CONTROLS);
        exit[2] = vmread(CONTROL_ENTRY_INTERRUPTION_INFO);
        if valid {
            exit[2] &= !(1 << 31);
        }
        vcpu::write_vmcs(s, v, CONTROL_ENTRY_INTERRUPTION_INFO, exit[2]);
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
        vcpu::write_vmcs(s, v, GUEST_RFLAGS, exit[7]);
        vcpu::write_vmcs(s, v, GUEST_INTERRUPTABILITY, exit[8]);
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
    // 0x100 means poll the local APIC; NO_INTERRUPT, that no host
    // interrupt caused the exit.
    if host_exit {
        if (amd && reason == 0x60) || (!amd && reason == 1) {
            if interrupt == u64::MAX {
                0x100
            } else {
                interrupt
            }
        } else {
            NO_INTERRUPT
        }
    } else {
        NO_INTERRUPT
    }
}

/// Secondary processor-based control 5, "enable VPID".
const VPID_ENABLE: u64 = 1 << 5;

/// The value `run` loads into VMCS `field` from the VCPU's image `value`:
/// the secondary controls with "enable VPID" when the kernel uses VPIDs
/// (`vpid` from `vpid_mode`). The image never holds that bit (fl4-core
/// `sanitize_vmcs` keeps it out, and `run` masks it from what it reads back).
fn secondary_with_vpid(field: u64, value: u64, vpid: u64) -> u64 {
    if field == CONTROL_SECONDARY_PROCESSOR_CONTROLS && vpid != 0 {
        value | VPID_ENABLE
    } else {
        value
    }
}

/// `run`'s result for an exit no host interrupt caused: told apart from a
/// delivered vector, so that the exit path asks the local APIC nothing
/// (an ISR read is itself an exit under a hypervisor, on every guest exit).
pub const NO_INTERRUPT: u64 = 0x1ff;
pub fn empty_root() -> u64 {
    maps().empty.0.as_ptr() as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An AP without VMCB clean bits beside a boot core with them would be
    /// given nonzero clean bits by `run` (all cores share `SVM_FEATURES`):
    /// it is rejected, as VMX APs are for any capability difference.
    #[test]
    fn svm_aps_need_the_boot_cores_vmcb_clean_bits() {
        let (np, nrips, clean, decode) = (1u32, 1u32 << 3, 1u32 << 5, 1u32 << 7);
        let base = np | nrips;
        assert!(!svm_ap_compatible(base | clean, base));
        assert!(!svm_ap_compatible(base | clean | decode, base | decode));
        assert!(svm_ap_compatible(base | clean, base | clean));
        assert!(svm_ap_compatible(base, base | clean));
        assert!(svm_ap_compatible(base, base));
        // Features `run` does not share are this core's own business.
        assert!(svm_ap_compatible(base | decode, base));
    }

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

    /// VPID only with "enable VPID" and INVVPID of type 1 or 2; type 1
    /// (one VPID) preferred; never type 3 alone.
    /// `virt_reject`: what a boot core without a backend is missing.
    #[test]
    fn virtualization_rejections_are_classified() {
        assert_eq!(unprobed(false, false), None);
        assert_eq!(unprobed(true, false), Some(virt_reject::SKIM_ACTIVE));
        assert_eq!(unprobed(false, true), Some(virt_reject::CVM_ACTIVE));
        assert_eq!(unprobed(true, true), Some(virt_reject::CVM_ACTIVE));

        let svm = |ebx, edx| cpu::Cpuid { eax: 1, ebx, ecx: 0, edx };
        let full = svm(8, 9);
        let no_read = || -> u64 { panic!("VM_CR read on a CPU that may not have it") };
        let max = 0x8000_0020;
        assert_eq!(svm_usable(max, 4, true, full, || 0), Ok(()));
        assert_eq!(svm_usable(0x8000_0008, 4, true, full, no_read), Err(virt_reject::NO_HW));
        assert_eq!(svm_usable(max, !4, true, full, no_read), Err(virt_reject::NO_HW));
        // No hardware is the reason even where the policy would refuse it.
        assert_eq!(svm_usable(max, 0, false, full, no_read), Err(virt_reject::NO_HW));
        assert_eq!(svm_usable(max, 4, false, full, no_read), Err(virt_reject::SPEC_POLICY_REJECTED));
        for missing in [svm(8, 1), svm(8, 8), svm(1, 9), svm(0, 0)] {
            assert_eq!(svm_usable(max, 4, true, missing, no_read), Err(virt_reject::MISSING_FEATURES));
        }
        assert_eq!(svm_usable(max, 4, true, full, || 16), Err(virt_reject::DISABLED_BY_FIRMWARE));
        assert_eq!(svm_usable(max, 4, true, full, || !16), Ok(()));

        // IA32_FEATURE_CONTROL: locked on, locked off, locked for SMX only,
        // not locked (locked on now).
        assert_eq!(vmx_feature_control(5), Ok(None));
        assert_eq!(vmx_feature_control(1), Err(virt_reject::DISABLED_BY_FIRMWARE));
        assert_eq!(vmx_feature_control(3), Err(virt_reject::DISABLED_BY_FIRMWARE));
        assert_eq!(vmx_feature_control(0), Ok(Some(5)));
        assert_eq!(vmx_feature_control(1 << 20), Ok(Some(1 << 20 | 5)));
    }

    #[test]
    fn virtualization_features_are_the_chosen_backends() {
        let (single, all) = (1 << 25, 1 << 26);
        let pmu = 1 << (32 + 13);
        assert_eq!(features_of(1, 0, all, 0, 0), 0);
        assert_eq!(features_of(1, 1, all, 0, 0), virt_features::X86_VPID_SINGLE);
        assert_eq!(features_of(1, 2, all, 0, 0), virt_features::X86_VPID_ALL);
        assert_eq!(features_of(1, 0, single, 0, 0), virt_features::X86_INVEPT_SINGLE);
        assert_eq!(features_of(1, 0, 0, pmu, 0), virt_features::X86_VMX_PERF_GLOBAL_CTRL);
        // Only the allowed-1 half counts.
        assert_eq!(features_of(1, 0, 0, 1 << 13, 0), 0);
        assert_eq!(features_of(1, 1, single, pmu, !0), 1 | 4 | 16);
        assert_eq!(features_of(2, 1, single, pmu, 1 << 5), virt_features::X86_SVM_VMCB_CLEAN);
        assert_eq!(features_of(2, 1, single, pmu, !(1 << 5)), 0);
        assert_eq!(features_of(0, 1, single, pmu, !0), 0);
    }

    #[test]
    fn vpid_mode_needs_enable_vpid_and_a_usable_invvpid() {
        let sec = 1u64 << (32 + 5);
        let invvpid = 1u64 << 32;
        let (single, all, globals) = (1u64 << 41, 1u64 << 42, 1u64 << 43);
        for (secondary, ept, mode) in [
            (0, invvpid | single | all, 0),         // No "enable VPID".
            (u64::MAX & !sec, u64::MAX, 0),         // Every other control.
            (sec, single | all, 0),                 // No INVVPID.
            (sec, invvpid, 0),                      // INVVPID of no type.
            (sec, invvpid | single, 1),
            (sec, invvpid | all, 2),
            (sec, invvpid | single | all, 1),
            (sec, invvpid | globals, 0),            // Retaining globals only.
            (sec, invvpid | globals | all, 2),
            (u64::MAX, u64::MAX, 1),
            (sec & 0xffff_ffff_0000_0000, (1 << 6) | invvpid | single, 1),
        ] {
            assert_eq!(vpid_mode(secondary, ept), mode, "{secondary:#x} {ept:#x}");
        }
        // The allowed-0 half (bits 31:0) is not what allows the control.
        assert_eq!(vpid_mode(1 << 5, invvpid | single), 0);
    }

    #[test]
    fn vpid_reuse_requires_the_same_live_owner_and_completed_entry() {
        let mut state = VmxVpidState::new();
        assert!(state.prepare(0x1000, 0x2000, 0, 0)); // First entry.
        assert!(state.prepare(0x1000, 0x2000, 1, 0)); // Failed entry.
        state.valid = true;
        assert!(!state.prepare(0x1000, 0x2000, 1, 0));
        state.valid = true;
        assert!(!state.prepare(0x1000, 0x2000, 4, 3)); // Owner is this core.
        for (v, root, owner, cpu) in [
            (0x1000, 0x2000, 2, 0), // Migrated away and back.
            (0x1000, 0x2000, 0, 0), // Retype, FlushTLB, paging write, detach.
            (0x1000, 0x3000, 1, 0), // Replaced EPT root.
            (0x4000, 0x3000, 1, 0), // Another VCPU sharing that root.
            (0x4000, 0x3000, 1, 1), // Same VCPU and root, another core's.
        ] {
            state.valid = true;
            assert!(state.prepare(v, root, owner, cpu));
        }
        state.valid = false; // Local or remote EPT invalidation.
        assert!(state.prepare(0x4000, 0x3000, 1, 0));
    }

    /// "Enable VPID" goes to the hardware secondary controls only, only
    /// when the kernel uses VPIDs, and never into another field.
    #[test]
    fn enable_vpid_is_added_to_the_secondary_controls_only() {
        let image = 0x82; // EPT and unrestricted guest, as sanitized.
        assert_eq!(secondary_with_vpid(CONTROL_SECONDARY_PROCESSOR_CONTROLS, image, 0), image);
        for mode in [1, 2] {
            assert_eq!(secondary_with_vpid(CONTROL_SECONDARY_PROCESSOR_CONTROLS, image, mode), image | VPID_ENABLE);
            assert_eq!(secondary_with_vpid(CONTROL_PRIMARY_PROCESSOR_CONTROLS, 0, mode), 0);
            assert_eq!(secondary_with_vpid(CONTROL_VPID, 0, mode), 0);
        }
        // The VPID field has a VMCS cache slot of its own.
        assert!(VmcsState::index(CONTROL_VPID).is_some());
        assert!(!vcpu::WRITE_FIELDS.iter().any(|&f| VmcsState::index(f) == VmcsState::index(CONTROL_VPID)));
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
    fn every_vmcs_field_has_its_own_slot() {
        let mut seen = [false; SLOTS];
        let mut n = 0;
        for list in [&vcpu::READ_FIELDS[..], &vcpu::WRITE_FIELDS[..], &BACKEND_FIELDS[..], &BACKEND_COUNTS[..]] {
            for &f in list {
                let i = VmcsState::index(f).expect("tracked");
                assert_eq!(image_index(f) as u64, (vcpu::vmcs_addr(0, f) - vcpu::SHADOW) / 8);
                if !seen[i] {
                    seen[i] = true;
                    n += 1;
                }
            }
        }
        assert_eq!(n, slot_table().1, "distinct fields, distinct slots");
        // Encodings the image index aliases are not tracked fields: a high
        // half, a reserved bit.
        assert_eq!(VmcsState::index(GUEST_EFER | 1), None);
        assert_eq!(VmcsState::index(GUEST_EFER | (1 << 12)), None);
        assert_eq!(VmcsState::index(GUEST_RIP | (1 << 15)), None);
    }
    #[test]
    fn an_exit_reads_only_what_kernel_logic_and_the_message_need() {
        let synced = SYNCED_AFTER_EXIT;
        let is = |f: u64| {
            let i = VmcsState::index(f).unwrap();
            synced[i / 64] & (1 << (i % 64)) != 0
        };
        for f in [GUEST_RIP, GUEST_RFLAGS, GUEST_INTERRUPTABILITY, CONTROL_ENTRY_INTERRUPTION_INFO,
            CONTROL_PRIMARY_PROCESSOR_CONTROLS, CONTROL_CR0_READ_SHADOW, DATA_EXIT_INSTRUCTION_LENGTH, HOST_RSP]
        {
            assert!(is(f), "{f:#x} is current after an exit");
        }
        for f in [GUEST_RSP, GUEST_CR0, GUEST_CR3, GUEST_CS_ACCESS_RIGHTS, GUEST_FS_BASE, GUEST_EFER, GUEST_ACTIVITY] {
            assert!(!is(f), "{f:#x} is read when an invocation needs it");
        }
    }
    #[test]
    fn lazy_guest_state_is_kept_until_synced_and_then_written_back() {
        let mut state = VmcsState::new();
        state.reset();
        // First entry: everything is written.
        state.write(GUEST_FS_BASE, 0x1000, |_, _| {});
        // An exit: FS base is not read; the guest may have changed it.
        state.synced = SYNCED_AFTER_EXIT;
        assert!(!state.synced(GUEST_FS_BASE));
        // Re-entry with the image unchanged leaves the VMCS's value alone.
        state.write(GUEST_FS_BASE, 0x1000, |_, _| panic!("lazy field rewritten"));
        // An invocation syncs it (the guest had written 0x2000), then the
        // VMM writes the old value back: that is a change for the VMCS.
        state.observe(GUEST_FS_BASE, 0x2000);
        state.set_synced(GUEST_FS_BASE);
        let mut wrote = None;
        state.write(GUEST_FS_BASE, 0x1000, |f, v| wrote = Some((f, v)));
        assert_eq!(wrote, Some((GUEST_FS_BASE, 0x1000)));
    }
    #[test]
    fn vmcs_failed_entries_preserve_the_launch_state() {
        let mut state = VmcsState::new();
        assert!(!state.launched());
        assert!(!state.finish_entry(true, 0));
        assert!(!state.finish_entry(false, (1 << 31) | 33));
        assert!(!state.launched());
        assert!(state.finish_entry(false, 10));
        assert!(state.launched());
        assert!(!state.finish_entry(true, 10));
        assert!(!state.finish_entry(false, (1 << 31) | 33));
        assert!(state.launched());
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
        assert_eq!(physical_at(layout::pptr(0x123000), 0), 0x123000);
        assert_eq!(physical_at(0xffffffff80123000, 0), 0x123000);
    }
    #[test]
    fn physical_addresses_of_statics_follow_a_moved_image() {
        // fl4-efi loads the image 2 MiB aligned wherever it found room:
        // VMXON regions, VMCSs, host-save areas and bitmaps in the image
        // are there, not at their offset from KERNEL_OFFSET (which is
        // free RAM the root task gets).
        let delta = 0x7e00_0000;
        assert_eq!(physical_at(0xffffffff80123000, delta), 0x7e12_3000);
        assert_eq!(physical_at(layout::pptr(0x123000), delta), 0x123000);
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
