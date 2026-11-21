//! `fl4_core::machine::Arch` on AArch64 hardware. Every operation runs at
//! once: kernel entries run under the serial gate, or are local paths
//! beside it whose operations concern their own core (DESIGN.md §7).
use crate::{gic, percpu, serial, smp, timer};
use fl4_core::layout::irq;
use fl4_core::machine::Arch;

pub struct PhysArch;

fn mask(irq: u64, m: bool) {
    gic::mask(irq::id(irq), irq::core(irq), m);
}

/// Mask or unmask (`m`), or set the trigger of (`edge`), another core's
/// banked interrupt on GICv2 (`gic::remote`): that core does it, by a
/// remote call. It is done before the call
/// returns, so an IRQ handler deleted from here is masked on its core.
fn remote_gic(kind: u64, id: u64, core: u64, v: bool) {
    smp::remote_call(kind, id, v as u64, 1u64 << (core & 63));
}



/// The raw acknowledge value to end `irq` with.
fn eoi_value(irq: u64) -> u64 {
    let raw = percpu::get().iar.get();
    if raw & 0x3ff == irq::id(irq) {
        raw
    } else {
        irq::id(irq)
    }
}

/// Take the highest pending interrupt, leaving the remote-call SGI
/// pending: it is serviced on the way into the kernel, never by a
/// preemption point. Returns the interrupt's IRQ, or `NO_IRQ`.
pub fn poll_irq() -> u64 {
    let hp = gic::highest_pending();
    if hp >= 1020 || hp == irq::REMOTE_CALL_ID {
        return fl4_core::syscall::NO_IRQ;
    }
    let raw = gic::ack();
    let id = raw & 0x3ff;
    if raw == gic::SPURIOUS || id >= 1020 {
        return fl4_core::syscall::NO_IRQ;
    }
    if id == irq::REMOTE_CALL_ID {
        // Raced with a new remote call: it is serviced on entry anyway.
        gic::eoi(raw);
        return fl4_core::syscall::NO_IRQ;
    }
    if id == irq::TIMER_ID {
        timer::quiesce();
    }
    percpu::get().iar.set(raw);
    irq::of(id, percpu::cpu_index() as u64)
}

impl Arch for PhysArch {
    fn now(&mut self) -> u64 {
        timer::now()
    }
    fn set_deadline(&mut self, ticks: u64) {
        timer::set_deadline(ticks)
    }
    fn us_to_ticks(&self, us: u64) -> u64 {
        timer::us_to_ticks(us)
    }
    fn ticks_to_us(&self, ticks: u64) -> u64 {
        timer::ticks_to_us(ticks)
    }
    fn max_us(&self) -> u64 {
        timer::max_us()
    }
    fn kernel_wcet_ticks(&self) -> u64 {
        timer::us_to_ticks(timer::KERNEL_WCET_US)
    }

    fn irq_pending(&mut self) -> bool {
        gic::pending()
    }
    fn take_pending_irq(&mut self) -> u64 {
        poll_irq()
    }
    fn mask_irq(&mut self, irq: u64, m: bool) {
        if gic::remote(irq::id(irq), irq::core(irq)) {
            return remote_gic(smp::CALL_GIC_MASK, irq::id(irq), irq::core(irq), m);
        }
        mask(irq, m)
    }
    fn ack_irq(&mut self, irq: u64) {
        let raw = eoi_value(irq);
        gic::eoi(raw)
    }

    fn set_vspace(&mut self, root: u64, asid: u64) {
        crate::mmu::switch(root, asid)
    }
    // Until the broadcast invalidation completes another core may still use
    // the old translation; the entry holds the serial gate meanwhile.
    fn invalidate_page(&mut self, asid: u64, vaddr: u64) {
        crate::mmu::invalidate_page(asid, vaddr);
    }
    // Cores running the ASID are also interrupted: if it was deleted they
    // must stop walking its tables (`mmu::retired`).
    fn invalidate_asid(&mut self, asid: u64) {
        crate::mmu::invalidate_asid(asid);
        smp::remote_call(smp::CALL_ASID, asid, 0, crate::mmu::cores_on(asid));
    }
    fn invalidate_page_structures(&mut self, asid: u64) {
        self.invalidate_asid(asid)
    }

    fn ioapic_map(&mut self, _ioapic: u64, _pin: u64, _level: u64, _polarity: u64, _vector: u64) -> bool {
        false
    }
    fn ioapic_map_remapped(&mut self, _ioapic: u64, _pin: u64, _level: u64, _polarity: u64, _vector: u64, _handle: u64) -> bool {
        false
    }
    fn num_ioapics(&self) -> u64 {
        0
    }
    fn ioapic_pins(&self, _i: u64) -> u64 {
        0
    }
    fn port_in(&mut self, _port: u64, _size: u64) -> u64 {
        0
    }
    fn port_out(&mut self, _port: u64, _size: u64, _v: u64) {}

    fn fpu_flush(&mut self, tcb: u64) {
        crate::fpu::flush(tcb)
    }
    fn fpu_sanitise(&mut self, tcb: u64) {
        crate::fpu::sanitise(tcb)
    }
    fn fpu_reload(&mut self, tcb: u64) {
        crate::fpu::forget(tcb)
    }
    fn fpu_release(&mut self, tcb: u64) {
        crate::fpu::release(tcb)
    }

    fn remote_stall(&mut self, cpu: u64) {
        smp::remote_call(smp::CALL_STALL, 0, 0, 1u64 << (cpu & 63));
    }
    fn send_reschedule(&mut self, m: u64) {
        smp::reschedule(m)
    }

    fn cache_op(&mut self, op: u64, root: u64, asid: u64, vaddr: u64, len: u64, paddr: u64) {
        crate::mmu::cache_op(op, root, asid, vaddr, len, paddr)
    }
    fn hw_access_flag(&self) -> bool {
        crate::cpu::has_hw_af()
    }
    fn max_spi(&self) -> u64 {
        gic::max_spi()
    }
    fn configure_irq(&mut self, irq: u64, edge: bool, core: u64) {
        if gic::remote(irq::id(irq), core) {
            return remote_gic(smp::CALL_GIC_CONFIG, irq::id(irq), core, edge);
        }
        gic::configure(irq::id(irq), core, edge);
    }

    fn putc(&mut self, c: u64) {
        serial::putc(c as u8)
    }
    fn get_char(&mut self) -> u64 {
        match serial::getc() {
            Some(c) => c as u64,
            None => u64::MAX,
        }
    }
    fn halt(&mut self) {
        for b in b"FL4: halted by seL4_DebugHalt\n" {
            serial::putc(*b);
        }
        crate::cpu::halt_forever()
    }
}
