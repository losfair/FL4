//! Starting the other cores with PSCI CPU_ON (DESIGN.md §3: the cores
//! come from the MADT or the device tree). Each starts at `_ap_start` at
//! its physical address, leaves EL2 if it is there, turns its MMU on with
//! the kernel's tables, sets itself up and waits for the boot core.
use crate::{entry, kprintln, paging};
use core::sync::atomic::{AtomicBool, Ordering};
use fl4_arch_aarch64::{cpu, fpu, gic, percpu, smp, timer};
use fl4_core::layout::{pptr, MAX_NODES};
use fl4_core::sched;

extern "C" {
    static _ap_start: u8;
    static fl4_ap_params: u8;
    static fl4_vectors: u8;
}

static BOOT_DONE: AtomicBool = AtomicBool::new(false);

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
    fl4_arch_aarch64::msr!("vbar_el1", unsafe { &fl4_vectors as *const u8 as u64 });
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
    // No debug events and no EL0 PMU access: both reset to UNKNOWN values
    // the firmware may have left set, and the kernel has no hardware
    // debug API on AArch64 to manage them.
    fl4_arch_aarch64::msr!("mdscr_el1", 0);
    let pmuver = (fl4_arch_aarch64::mrs!("id_aa64dfr0_el1") >> 8) & 0xf;
    if pmuver != 0 && pmuver != 0xf {
        fl4_arch_aarch64::msr!("pmuserenr_el0", 0);
    }
    cpu::isb();
}

fn wait_us(us: u64) {
    let end = timer::now() + timer::us_to_ticks(us);
    while timer::now() < end {
        core::hint::spin_loop();
    }
}

/// Start the cores in `mpidrs` after the first (the boot core); returns
/// the number running.
pub fn start_aps(mpidrs: &[u64], ttbr1: u64) -> usize {
    let max = (MAX_NODES as usize).min(percpu::MAX_CPUS);
    if smp::psci() == smp::PSCI_NONE {
        if mpidrs.len() > 1 {
            kprintln!("FL4: no PSCI: running on the boot core only");
        }
        return 1;
    }
    let entry_pa = paging::image_pa(unsafe { &_ap_start as *const u8 as u64 });
    let params_pa = paging::image_pa(unsafe { &fl4_ap_params as *const u8 as u64 });
    let params = pptr(params_pa) as *mut u64;
    let mut next = 1;
    for &m in &mpidrs[1..] {
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
        while smp::num_online() == before && timer::now() < deadline {
            core::hint::spin_loop();
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
extern "C" fn fl4_ap_main(c: u64) -> ! {
    percpu::init(c as usize);
    init_core_regs();
    fpu::init();
    gic::init_cpu(find_gicr());
    timer::init_core();
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
