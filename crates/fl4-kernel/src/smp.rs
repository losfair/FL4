//! Starting the application processors (seL4 arch/x86/kernel/smp_sys.c).
use crate::{entry, gdt, kprintln, paging};
use core::sync::atomic::{AtomicBool, Ordering};
use fl4_arch_x86_64::arch::TIMER_VECTOR;
use fl4_arch_x86_64::{apic, cpu, fpu, percpu, pit, smp, timer};
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

/// CPU features the boot core enabled, for the other cores to match.
#[derive(Clone, Copy)]
pub struct Features {
    pub cr4: u64,
    pub efer_nx: bool,
}

static mut FEATURES: Features = Features { cr4: 0, efer_nx: false };

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

/// Start every other core listed in the MADT, up to the kernel's node
/// limit. Returns the number of cores running, the boot core included.
pub fn start_aps(apic_ids: &[u32], f: Features) -> usize {
    unsafe { FEATURES = f };
    let max = (MAX_NODES as usize).min(percpu::MAX_CPUS);
    let bsp = percpu::get().apic_id;
    let tramp = unsafe { &fl4_ap_trampoline as *const u8 };
    let len = unsafe { &fl4_ap_trampoline_end as *const u8 as usize } - tramp as usize;
    let data_off = unsafe { &fl4_ap_data as *const u8 as usize } - tramp as usize;
    let boot_root = paging::ap_boot_root();
    let mut next = 1;
    for &id in apic_ids {
        if id == bsp || next >= max {
            continue;
        }
        let c = next;
        let stack_top = percpu::init(c);
        unsafe {
            core::ptr::copy_nonoverlapping(tramp, pptr(AP_BASE) as *mut u8, len);
            let d = (pptr(AP_BASE) as usize + data_off) as *mut u64;
            d.write_volatile(boot_root);
            d.add(1).write_volatile((1 << 8) | if f.efer_nx { 1 << 11 } else { 0 });
            d.add(2).write_volatile(stack_top);
            d.add(3).write_volatile(fl4_ap_main as *const () as u64);
            d.add(4).write_volatile(c as u64);
        }
        let before = smp::num_online();
        // INIT, then two STARTUPs with the trampoline's page number.
        apic::send_ipi(id, 0x4500);
        pit::wait(pit_us(10_000), || {});
        for _ in 0..2 {
            apic::send_ipi(id, 0x4600 | (AP_BASE >> 12) as u32);
            wait_us(200);
        }
        let deadline = cpu::rdtsc() + timer::us_to_ticks(100_000);
        while smp::num_online() == before && cpu::rdtsc() < deadline {
            core::hint::spin_loop();
        }
        if smp::num_online() == before {
            kprintln!("FL4: core with APIC id {} did not start", id);
            continue;
        }
        next += 1;
    }
    smp::num_online() as usize
}

/// The root task exists: let the other cores schedule.
pub fn release_aps() {
    BOOT_DONE.store(true, Ordering::Release);
}

/// An application processor, from the trampoline, on its kernel stack.
#[no_mangle]
extern "C" fn fl4_ap_main(c: u64) -> ! {
    let f = unsafe { FEATURES };
    cpu::write_cr3(paging::root_paddr());
    cpu::write_cr4(f.cr4);
    let stack_top = percpu::get_for(c as usize).stack_top;
    gdt::init_core(c as usize, stack_top);
    cpu::init_pat();
    fpu::init();
    assert!(fl4_arch_x86_64::vm::init(false), "virtualization features differ between cores");
    let pc = percpu::get();
    pc.cr3 = paging::root_paddr();
    pc.kernel_cr3 = fl4_arch_x86_64::tlb::kernel_cr3(paging::root_paddr());
    fl4_arch_x86_64::spec::init_core();
    apic::enable(pptr(apic::base_paddr()));
    apic::write(apic::REG_SVR, (1 << 8) | 0xff);
    apic::write(apic::REG_LVT_LINT0, 1 << 16);
    apic::write(apic::REG_LVT_LINT1, 1 << 16);
    apic::write(apic::REG_LVT_ERROR, 1 << 16);
    percpu::get().apic_id = apic::id();
    timer::init_core(TIMER_VECTOR);
    smp::set_online(c as usize);
    while !BOOT_DONE.load(Ordering::Acquire) {
        core::hint::spin_loop();
    }
    entry::lock();
    let mut s = entry::store();
    let mut a = fl4_arch_x86_64::arch::PhysArch;
    sched::schedule(&mut s, &mut a);
    sched::activate_thread(&mut s, &mut a);
    entry::exit()
}
