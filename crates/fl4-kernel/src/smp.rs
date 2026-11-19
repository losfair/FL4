//! Starting the application processors (seL4 arch/x86/kernel/smp_sys.c).
use crate::{entry, gdt, kprintln, paging};
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, Ordering};
use fl4_arch_x86_64::arch::TIMER_VECTOR;
use fl4_arch_x86_64::{apic, cpu, fpu, percpu, pit, sev::snp, smp, timer};
use fl4_core::layout::{pptr, MAX_NODES};
use fl4_core::sched;

core::arch::global_asm!(include_str!("ap.S"), options(att_syntax));

extern "C" {
    static fl4_ap_trampoline: u8;
    static fl4_ap_trampoline_end: u8;
    static fl4_ap_data: u8;
}

const AP_BASE: u64 = 0x8000;
/// The boot core has created the root task; started cores may schedule.
static BOOT_DONE: AtomicBool = AtomicBool::new(false);
/// Zero until the boot core patches text. Then the number of cores
/// whose instruction streams have been serialized since the patch.
static TEXT_SYNCED: AtomicU64 = AtomicU64::new(0);
// AP failures must reach the BSP: a panic halts only the failing CPU and
// would otherwise look like a startup timeout, allowing boot to continue.
static AP_REJECTED: AtomicU8 = AtomicU8::new(0);
const REJECT_SPEC: u8 = 1;
const REJECT_VM: u8 = 2;
const REJECT_APIC: u8 = 3;
const REJECT_FPU: u8 = 4;
const REJECT_TIMER: u8 = 5;
const REJECT_TLB: u8 = 6;
const REJECT_CR4: u8 = 7;

fn reject_ap(reason: u8) -> ! {
    AP_REJECTED.store(reason, Ordering::Release);
    cpu::halt_forever()
}

/// CPU features the boot core enabled, for the other cores to match.
#[derive(Clone, Copy)]
pub struct Features {
    pub cr4: u64,
    pub window_top: u64,
    pub efer_nx: bool,
}

static mut FEATURES: Features = Features { window_top: 0, cr4: 0, efer_nx: false };

/// PIT ticks for about `us` microseconds.
fn pit_us(us: u64) -> u16 {
    ((pit::HZ * us) / 1_000_000).clamp(1, 65535) as u16
}

fn wait_us(us: u64) {
    let end = cpu::rdtsc() + timer::us_to_ticks(us);
    while cpu::rdtsc() < end {
        core::hint::spin_loop();
    }
}

// Every per-core array the cores index by `percpu::cpu_index` without a
// bounds check (the transaction runtime's states, the serial gate's slots)
// and every core bit mask (u64) covers each core `start_aps` may start.
const _: () = assert!(
    percpu::MAX_CPUS <= fl4_store::tx::MAX_CPUS && percpu::MAX_CPUS <= fl4_sync::MAX_CPUS && percpu::MAX_CPUS <= 64
);

/// Start every other core listed in the MADT, up to the kernel's node
/// limit. Returns the number of cores running, the boot core included.
pub fn start_aps(apic_ids: &[u32], f: Features) -> usize {
    unsafe { FEATURES = f };
    let snp_guest = snp::active();
    if snp_guest && !snp::ap_creation() {
        kprintln!("FL4: SNP hypervisor does not advertise AP creation; using one core");
        return 1;
    }
    let max = (MAX_NODES as usize).min(percpu::MAX_CPUS);
    let bsp = percpu::apic_id(percpu::cpu_index());
    let smt_shift = fl4_arch_x86_64::spec::smt_shift();
    let tramp = unsafe { &fl4_ap_trampoline as *const u8 };
    let len = unsafe { &fl4_ap_trampoline_end as *const u8 as usize } - tramp as usize;
    let data_off = unsafe { &fl4_ap_data as *const u8 as usize } - tramp as usize;
    let boot_root = if snp_guest { 0 } else { paging::ap_boot_root() };
    let mut next = 1;
    for (i, &id) in apic_ids.iter().enumerate() {
        if next >= max || !crate::acpi::first_listing(apic_ids, i) || !fl4_arch_x86_64::spec::allow_ap(
            id, bsp, smt_shift, fl4_arch_x86_64::spec::no_smt()) {
            continue;
        }
        // An ID this APIC mode cannot name (an x2APIC entry above 0xfe in
        // xAPIC mode would be truncated to another core's), or the
        // broadcast ID, which would reset every core.
        if !apic::valid_physical_dest(id, apic::is_x2apic()) {
            kprintln!("FL4: skipping core with APIC id {:#x}: not addressable in this APIC mode", id);
            continue;
        }
        let c = next;
        let stack_top = percpu::stack_top(c);
        let before = smp::num_online();
        if snp_guest {
            crate::snp::start_ap(c, id, stack_top, fl4_ap_main as *const () as u64);
        } else {
            unsafe {
                core::ptr::copy_nonoverlapping(tramp, pptr(AP_BASE) as *mut u8, len);
                let d = (pptr(AP_BASE) as usize + data_off) as *mut u64;
                d.write_volatile(boot_root);
                d.add(1).write_volatile((1 << 8) | if f.efer_nx { 1 << 11 } else { 0 });
                d.add(2).write_volatile(stack_top);
                d.add(3).write_volatile(fl4_ap_main as *const () as u64);
                d.add(4).write_volatile(c as u64);
            }
            // INIT, then two STARTUPs with the trampoline's page number.
            apic::send_ipi(id, 0x4500);
            pit::wait(pit_us(10_000), || {});
            for _ in 0..2 {
                apic::send_ipi(id, 0x4600 | (AP_BASE >> 12) as u32);
                wait_us(200);
            }
        }
        let deadline = cpu::rdtsc() + timer::us_to_ticks(100_000);
        while smp::num_online() == before && AP_REJECTED.load(Ordering::Acquire) == 0
            && cpu::rdtsc() < deadline {
            core::hint::spin_loop();
        }
        let rejected = AP_REJECTED.load(Ordering::Acquire);
        if rejected != 0 {
            kprintln!("FL4: rejecting AP with APIC id {}: {}", id, match rejected {
                REJECT_SPEC => "speculation capabilities differ between cores",
                REJECT_APIC => "local APIC outside the physical window",
                REJECT_FPU => "FPU state components or save format differ between cores",
                REJECT_TIMER => "TSC-deadline timer missing on this core",
                REJECT_TLB => "PCID or INVPCID missing on this core",
                REJECT_CR4 => "SMEP, SMAP or FSGSBASE missing on this core",
                _ => "virtualization features differ between cores",
            });
            // VMX/SVM may already be active on other cores. Keep them at
            // BOOT_DONE and halt the BSP; never publish a partial backend.
            crate::fail("incompatible AP capabilities; refusing to start userspace");
        }
        if smp::num_online() == before {
            kprintln!("FL4: core with APIC id {} did not start", id);
            // An AP could still be probing. Do not reuse its per-core slot
            // or release userspace before its capabilities are known.
            crate::fail("AP startup timed out; refusing to start userspace");
        }
        next += 1;
    }
    smp::num_online() as usize
}

/// Synchronize the patched instructions before enabling the new native
/// entry path. APs acknowledge the patch while still at the boot barrier.
pub fn sync_patched_text() {
    cpu::serialize_instructions();
    TEXT_SYNCED.store(1, Ordering::Release);
    let online = smp::num_online();
    let deadline = cpu::rdtsc() + timer::us_to_ticks(100_000);
    while TEXT_SYNCED.load(Ordering::Acquire) < online {
        if cpu::rdtsc() >= deadline {
            crate::fail("AP did not synchronize patched instructions");
        }
        core::hint::spin_loop();
    }
}

/// The root task exists: let the other cores schedule.
pub fn release_aps() {
    BOOT_DONE.store(true, Ordering::Release);
}

/// An application processor, from the trampoline, on its kernel stack.
#[no_mangle]
extern "C" fn fl4_ap_main(c: u64) -> ! {
    let f = unsafe { FEATURES };
    if snp::active() { snp::register_cpu(); }
    cpu::write_cr3(paging::root_paddr());
    // Natively before CR4.PCIDE, SMEP, SMAP and FSGSBASE, which fault on a
    // core without them, with no IDT yet to catch it (OSXSAVE and VMXE are
    // left to fpu::init and vm::init). An SNP AP starts with the boot
    // core's CR4 (snp::start_ap) and takes #VC for CPUID, so it checks once
    // its own GDT and IDT are in.
    if !snp::active() && !fl4_arch_x86_64::tlb::core_supported() { reject_ap(REJECT_TLB); }
    if !snp::active() && !cpu::core_cr4_supported(f.cr4) { reject_ap(REJECT_CR4); }
    cpu::write_cr4(f.cr4);
    let stack_top = percpu::stack_top(c as usize);
    gdt::init_core(c as usize, stack_top);
    if snp::active() && !fl4_arch_x86_64::tlb::core_supported() { reject_ap(REJECT_TLB); }
    if snp::active() && !cpu::core_cr4_supported(f.cr4) { reject_ap(REJECT_CR4); }
    cpu::init_pat();
    if !fpu::init(false) { reject_ap(REJECT_FPU); }
    if !fl4_arch_x86_64::spec::init_core(false) { reject_ap(REJECT_SPEC); }
    if !fl4_arch_x86_64::vm::init(false) { reject_ap(REJECT_VM); }
    percpu::get().cr3.set(paging::root_paddr());
    if apic::enable(false, f.window_top).is_none() { reject_ap(REJECT_APIC); }
    apic::write(apic::REG_SVR, (1 << 8) | 0xff);
    apic::write(apic::REG_LVT_LINT0, 1 << 16);
    apic::write(apic::REG_LVT_LINT1, 1 << 16);
    apic::write(apic::REG_LVT_ERROR, 1 << 16);
    percpu::set_apic_id(apic::id());
    if !timer::core_supported() { reject_ap(REJECT_TIMER); }
    timer::init_core(TIMER_VECTOR);
    smp::set_online(c as usize);
    let mut text_synced = false;
    while !BOOT_DONE.load(Ordering::Acquire) {
        if !text_synced && TEXT_SYNCED.load(Ordering::Acquire) != 0 {
            cpu::serialize_instructions();
            TEXT_SYNCED.fetch_add(1, Ordering::AcqRel);
            text_synced = true;
        }
        core::hint::spin_loop();
    }
    entry::lock();
    let mut s = entry::store();
    let mut a = fl4_arch_x86_64::arch::PhysArch;
    sched::schedule(&mut s, &mut a);
    sched::activate_thread(&mut s, &mut a);
    entry::exit()
}
