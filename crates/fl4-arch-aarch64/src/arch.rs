//! `fl4_core::machine::Arch` on AArch64 hardware.
//!
//! Inside a transaction (DESIGN.md §7) the operations fall in three groups,
//! as on x86_64: reads with no lasting effect run at once (time, pending
//! interrupts, cache cleaning, which is repeatable); operations other
//! cores or the hardware would observe are queued (`Effect`) and run after
//! commit; and operations that can be neither repeated nor deferred (remote
//! stalls, FP/SIMD state on another core, TLB invalidation after unmapping,
//! interrupt configuration, cache invalidation) send the entry to the
//! serial gate.
use crate::{gic, percpu, serial, smp, timer};
use fl4_core::layout::irq;
use fl4_core::machine::Arch;

pub struct PhysArch;

#[derive(Clone, Copy)]
pub enum Effect {
    Deadline(u64),
    Mask(u64, bool),
    /// End of interrupt, with the raw acknowledge value.
    Ack(u64),
    VSpace(u64, u64),
    Reschedule(u64),
    Putc(u8),
}

pub const MAX_EFFECTS: usize = 64;

fn in_tx() -> bool {
    percpu::get().tx.get()
}

fn serial_needed() {
    fl4_store::tx::doom_serial(percpu::cpu_index() as u64);
}

fn defer(e: Effect) -> bool {
    let pc = percpu::get();
    if !pc.tx.get() {
        return false;
    }
    let n = pc.neffects.get();
    if n == MAX_EFFECTS {
        serial_needed();
    } else {
        pc.effects[n].set(e);
        pc.neffects.set(n + 1);
    }
    true
}

fn mask(irq: u64, m: bool) {
    gic::mask(irq::id(irq), irq::core(irq), m);
}

pub fn apply_effects() {
    let n = percpu::get().neffects.get();
    for i in 0..n {
        match percpu::get().effects[i].get() {
            Effect::Deadline(t) => timer::set_deadline(t),
            Effect::Mask(irq, m) => mask(irq, m),
            Effect::Ack(raw) => gic::eoi(raw),
            Effect::VSpace(root, asid) => crate::mmu::switch(root, asid),
            Effect::Reschedule(m) => smp::reschedule(m),
            Effect::Putc(c) => serial::putc(c),
        }
    }
    percpu::get().neffects.set(0);
}

pub fn discard_effects() {
    percpu::get().neffects.set(0);
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
        if !defer(Effect::Deadline(ticks)) {
            timer::set_deadline(ticks)
        }
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
    /// An interrupt accepted here is kept until the entry completes, so a
    /// transaction that reruns sees it again.
    fn take_pending_irq(&mut self) -> u64 {
        let pc = percpu::get();
        if pc.held_irq.get() != percpu::NO_IRQ {
            pc.held_used.set(true);
            return pc.held_irq.get();
        }
        let v = poll_irq();
        pc.held_irq.set(if v == fl4_core::syscall::NO_IRQ { percpu::NO_IRQ } else { v });
        pc.held_used.set(pc.held_irq.get() != percpu::NO_IRQ);
        v
    }
    fn mask_irq(&mut self, irq: u64, m: bool) {
        if !defer(Effect::Mask(irq, m)) {
            mask(irq, m)
        }
    }
    fn ack_irq(&mut self, irq: u64) {
        let raw = eoi_value(irq);
        if !defer(Effect::Ack(raw)) {
            gic::eoi(raw)
        }
    }

    fn set_vspace(&mut self, root: u64, asid: u64) {
        if !defer(Effect::VSpace(root, asid)) {
            crate::mmu::switch(root, asid)
        }
    }
    // The page-table change reaches memory only at commit; until the
    // broadcast invalidation completes another core may still use the old
    // translation, so it must not be possible to reuse the memory before
    // then: invalidations run under the serial gate, as on x86_64.
    fn invalidate_page(&mut self, asid: u64, vaddr: u64) {
        if in_tx() {
            return serial_needed();
        }
        crate::mmu::invalidate_page(asid, vaddr);
    }
    // Cores running the ASID are also interrupted: if it was deleted they
    // must stop walking its tables (`mmu::retired`).
    fn invalidate_asid(&mut self, asid: u64) {
        if in_tx() {
            return serial_needed();
        }
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
        if in_tx() {
            if crate::fpu::is_live(tcb) {
                serial_needed();
            }
            return;
        }
        crate::fpu::flush(tcb)
    }
    fn fpu_sanitise(&mut self, tcb: u64) {
        if in_tx() {
            return serial_needed();
        }
        crate::fpu::sanitise(tcb)
    }
    fn fpu_reload(&mut self, tcb: u64) {
        if in_tx() {
            if crate::fpu::is_live(tcb) {
                serial_needed();
            }
            return;
        }
        crate::fpu::forget(tcb)
    }
    fn fpu_release(&mut self, tcb: u64) {
        if in_tx() {
            if crate::fpu::is_live(tcb) {
                serial_needed();
            }
            return;
        }
        crate::fpu::release(tcb)
    }

    fn remote_stall(&mut self, cpu: u64) {
        if in_tx() {
            return serial_needed();
        }
        smp::remote_call(smp::CALL_STALL, 0, 0, 1u64 << (cpu & 63));
    }
    fn send_reschedule(&mut self, m: u64) {
        if !defer(Effect::Reschedule(m)) {
            smp::reschedule(m)
        }
    }

    fn cache_op(&mut self, op: u64, root: u64, asid: u64, vaddr: u64, len: u64, paddr: u64) {
        // Discarding data cannot be repeated or undone: a transaction
        // that later fails must not have done it.
        if op == fl4_core::vspace::CACHE_INVALIDATE && in_tx() {
            return serial_needed();
        }
        crate::mmu::cache_op(op, root, asid, vaddr, len, paddr)
    }
    fn hw_access_flag(&self) -> bool {
        crate::cpu::has_hw_af()
    }
    fn max_spi(&self) -> u64 {
        gic::max_spi()
    }
    fn configure_irq(&mut self, irq: u64, edge: bool, core: u64) {
        if in_tx() {
            return serial_needed();
        }
        gic::configure(irq::id(irq), core, edge);
    }

    fn putc(&mut self, c: u64) {
        if !defer(Effect::Putc(c as u8)) {
            serial::putc(c as u8)
        }
    }
    fn get_char(&mut self) -> u64 {
        if in_tx() {
            serial_needed();
            return u64::MAX;
        }
        match serial::getc() {
            Some(c) => c as u64,
            None => u64::MAX,
        }
    }
    fn halt(&mut self) {
        if in_tx() {
            return serial_needed();
        }
        for b in b"FL4: halted by seL4_DebugHalt\n" {
            serial::putc(*b);
        }
        crate::cpu::halt_forever()
    }
}

/// Print how kernel entries ran (debug builds).
pub fn print_stats() {
    use core::sync::atomic::Ordering::Relaxed;
    let put = |s: &[u8]| {
        for &b in s {
            serial::putc(b);
        }
    };
    let num = |v: u64| {
        let mut buf = [0u8; 20];
        let mut i = 20;
        let mut v = v;
        loop {
            i -= 1;
            buf[i] = b'0' + (v % 10) as u8;
            v /= 10;
            if v == 0 {
                break;
            }
        }
        for &b in &buf[i..] {
            serial::putc(b);
        }
    };
    put(b"FL4: ");
    num(smp::TX_COMMITS.load(Relaxed));
    put(b" transactions committed, ");
    num(smp::TX_ABORTS.load(Relaxed));
    put(b" aborted, ");
    num(smp::SERIAL_ENTRIES.load(Relaxed));
    put(b" serial entries\n");
}
