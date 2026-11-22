//! Starting the other cores with PSCI CPU_ON (DESIGN.md §3: the cores
//! come from the MADT or the device tree). Each starts at `_ap_start` at
//! its physical address, leaves EL2 if it is there, turns its MMU on with
//! the kernel's tables, sets itself up and waits for the boot core.
use crate::{entry, kprintln, paging};
use core::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use fl4_arch_aarch64::{ap_caps, cpu, el0_access, fpu, gic, gic_layout, percpu, smp, timer};
use fl4_core::layout::{pptr, MAX_NODES};
use fl4_core::sched;

extern "C" {
    static _ap_start: u8;
    static fl4_ap_params: u8;
    static fl4_vectors: u8;
    static fl4_vectors_el2: u8;
}

static BOOT_DONE: AtomicBool = AtomicBool::new(false);
// An AP that cannot run beside the boot core says so here and stops: a
// panic would halt only that core and look like a startup timeout.
static AP_REJECTED: AtomicU8 = AtomicU8::new(0);
const REJECT_CAPS: u8 = 1;
const REJECT_GIC: u8 = 2;
/// The boot core's capabilities, for the other cores to match.
static mut BOOT_CAPS: ap_caps::Caps = ap_caps::Caps {
    asid16: false,
    hw_af: false,
    pan: false,
    pa_bits: 0,
    cntfrq: 0,
    el2: false,
    vhe: false,
    vmid16: false,
    vgic_lrs: 0,
    virt: false,
    vgic_vtr: 0,
};

fn reject_ap(reason: u8) -> ! {
    AP_REJECTED.store(reason, Ordering::Release);
    cpu::halt_forever()
}

/// Per core: what `fl4_ap_main` needs to find its redistributor.
static mut GICR: [(u64, u64); crate::hw::MAX_GICR] = [(0, 0); crate::hw::MAX_GICR];
static mut N_GICR: usize = 0;

/// This core's redistributor, from the ranges found at boot.
pub fn find_gicr() -> u64 {
    if gic::version() != 3 {
        return 0;
    }
    unsafe {
        for i in 0..N_GICR {
            let (base, len) = GICR[i];
            if let Some(r) = gic::find_redistributor(base, len) {
                return r;
            }
        }
    }
    crate::fail("no GIC redistributor for this core")
}

pub fn set_gicr(ranges: &[(u64, u64)]) {
    unsafe {
        N_GICR = ranges.len();
        for (i, r) in ranges.iter().enumerate() {
            GICR[i] = *r;
        }
    }
}

/// Per-core register state every core sets the same way.
pub fn init_core_regs() {
    let vecs = if cpu::is_el2_vhe() {
        unsafe { &fl4_vectors_el2 as *const u8 as u64 }
    } else {
        unsafe { &fl4_vectors as *const u8 as u64 }
    };
    fl4_arch_aarch64::msr!("vbar_el1", vecs);
    let mut tcr = fl4_arch_aarch64::mrs!("tcr_el1");
    if cpu::has_hw_af() {
        tcr |= 1 << 39;
    }
    fl4_arch_aarch64::msr!("tcr_el1", tcr);
    let mut sctlr = fl4_arch_aarch64::mrs!("sctlr_el1");
    if cpu::has_pan() {
        // SPAN clear: PSTATE.PAN is set on every exception to EL1.
        sctlr &= !(1 << 23);
        unsafe { core::arch::asm!(".arch_extension pan", "msr pan, #1") };
    }
    fl4_arch_aarch64::msr!("sctlr_el1", sctlr);
    // No debug events, and no EL0 access to the debug communications
    // channel or the PMU: both reset to UNKNOWN values the firmware may
    // have left set, the kernel has no hardware debug API on AArch64 to
    // manage them, and it switches none of their state between threads
    // (`el0_access`).
    fl4_arch_aarch64::msr!("mdscr_el1", el0_access::MDSCR_EL1);
    if el0_access::has_pmu(fl4_arch_aarch64::mrs!("id_aa64dfr0_el1")) {
        fl4_arch_aarch64::msr!("pmuserenr_el0", 0);
    }
    if cpu::has_el2() {
        fl4_arch_aarch64::mmu::init_stage2_core();
    }
    // AMUSERENR_EL0 is not touched: UNDEFINED without FEAT_AMUv1, its EN
    // bit resets to 0, and with CPTR_EL3.TAM set (TF-A without
    // ENABLE_FEAT_AMU) an EL1 access traps to EL3 and can stop the
    // firmware, while EL0 then cannot reach the monitors either.
    cpu::isb();
}

fn wait_us(us: u64) {
    let end = timer::now() + timer::us_to_ticks(us);
    while timer::now() < end {
        core::hint::spin_loop();
    }
}

/// Start the cores in `mpidrs` other than the boot core (which the tables
/// may also leave out); returns the number running.
pub fn start_aps(mpidrs: &[u64], ttbr1: u64) -> usize {
    let mut max = (MAX_NODES as usize).min(percpu::MAX_CPUS);
    if smp::psci() == smp::PSCI_NONE {
        if mpidrs.len() > 1 {
            kprintln!("FL4: no PSCI: running on the boot core only");
        }
        return 1;
    }
    let me = cpu::mpidr();
    let v3 = gic::version() == 3;
    let rss = gic::rss();
    // Cores an SGI cannot name would never answer a remote call.
    let reachable = |m: u64| !v3 || gic_layout::v3_sgi_reaches(m & 0xff, rss);
    if !reachable(me) || (!v3 && !gic::sgi_ok(0)) {
        if mpidrs.iter().any(|&m| m != me) {
            kprintln!("FL4: SGIs cannot reach the boot core: running on the boot core only");
        }
        return 1;
    }
    if v3 {
        gic::set_need_rss(mpidrs.iter().any(|&m| reachable(m) && m & 0xff >= 16) || me & 0xff >= 16);
    } else {
        max = max.min(gic_layout::V2_INTERFACES);
    }
    // Started cores take indices below `max`.
    crate::entry::GATE.set_cores(max);
    let entry_pa = paging::image_pa(unsafe { &_ap_start as *const u8 as u64 });
    let params_pa = paging::image_pa(unsafe { &fl4_ap_params as *const u8 as u64 });
    let params = pptr(params_pa) as *mut u64;
    unsafe { BOOT_CAPS = cpu::caps() };
    let mut next = 1;
    for &m in mpidrs {
        if m == me {
            continue;
        }
        if !reachable(m) {
            kprintln!("FL4: skipping core {:#x}: SGIs cannot name Aff0 {} without the GIC range selector", m, m & 0xff);
            continue;
        }
        if next >= max {
            break;
        }
        let c = next;
        let stack_top = percpu::init_stack(c);
        percpu::set_mpidr(c, m);
        unsafe {
            params.write_volatile(paging::ident_ttbr0());
            params.add(1).write_volatile(ttbr1);
            params.add(2).write_volatile(stack_top);
        }
        cpu::clean_dcache_poc(params as u64, 32);
        let before = smp::num_online();
        let r = smp::cpu_on(m, entry_pa, c as u64);
        if r != 0 {
            kprintln!("FL4: PSCI CPU_ON for core {:#x} failed ({})", m, r);
            continue;
        }
        let deadline = timer::now() + timer::us_to_ticks(1_000_000);
        while smp::num_online() == before && AP_REJECTED.load(Ordering::Acquire) == 0 && timer::now() < deadline {
            core::hint::spin_loop();
        }
        let rejected = AP_REJECTED.load(Ordering::Acquire);
        if rejected == REJECT_GIC {
            kprintln!("FL4: rejecting core {:#x}: SGIs cannot reach it or it cannot reach the others \
                (GICv2 CPU interface missing or shared, or no GICv3 range selector)", m);
            crate::fail("incompatible AP capabilities; refusing to start userspace");
        }
        if rejected != 0 {
            kprintln!("FL4: rejecting core {:#x}: ASID size, access-flag management, PAN, physical address size, \
                CNTFRQ_EL0, exception level (EL2, VHE), VMID size or VGIC (list registers, and with guests \
                its type register) differ from the boot core's", m);
            crate::fail("incompatible AP capabilities; refusing to start userspace");
        }
        if smp::num_online() == before {
            kprintln!("FL4: core {:#x} did not start", m);
            crate::fail("AP startup timed out; refusing to start userspace");
        }
        next += 1;
    }
    let _ = wait_us;
    smp::num_online() as usize
}

pub fn release_aps() {
    BOOT_DONE.store(true, Ordering::Release);
}

#[no_mangle]
extern "C" fn fl4_ap_main(c: u64, el_mode: u64) -> ! {
    percpu::init(c as usize);
    let ap_mode = cpu::ElMode::from_raw(el_mode);
    if ap_mode != cpu::el_mode() {
        reject_ap(REJECT_CAPS);
    }
    if cpu::is_el2_nvhe() {
        fl4_arch_aarch64::hyp_nvhe::init_core(
            c as usize,
            paging::hyp_ttbr0(),
            paging::image_pa(fl4_arch_aarch64::hyp_nvhe::hyp_vectors_va()),
            paging::image_pa(fl4_arch_aarch64::hyp_nvhe::hyp_cpu_va(c as usize)),
        );
    }
    if !ap_caps::ap_matches(unsafe { &*core::ptr::addr_of!(BOOT_CAPS) }, &cpu::caps_for(ap_mode)) {
        reject_ap(REJECT_CAPS);
    }
    init_core_regs();
    fpu::init();
    gic::init_cpu(find_gicr());
    if cpu::is_el2_nvhe() {
        fl4_arch_aarch64::hyp_nvhe::init_gic_core(
            c as usize,
            gic::version() == 3,
            gic::vgic_num_lrs(),
            if gic::version() == 3 { fl4_arch_aarch64::vcpu::gicv3_n_apr() } else { 0 },
        );
    }
    if !gic::sgi_ok(c as usize) {
        reject_ap(REJECT_GIC);
    }
    timer::init_core();
    if cpu::is_el2_nvhe() {
        fl4_arch_aarch64::hyp_nvhe::save_host_regs();
    }
    smp::set_online(c as usize);
    while !BOOT_DONE.load(Ordering::Acquire) {
        core::hint::spin_loop();
    }
    entry::lock();
    let mut s = entry::store();
    let mut a = fl4_arch_aarch64::arch::PhysArch;
    sched::schedule(&mut s, &mut a);
    sched::activate_thread(&mut s, &mut a);
    entry::exit()
}
