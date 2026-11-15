//! `fl4_core::machine::Arch` on x86_64 hardware.
//!
//! Inside a transaction (DESIGN.md §7) the operations fall in three groups:
//! reads of the machine that have no lasting effect run at once (time, the
//! IRR); operations other cores or the hardware would observe are queued
//! (`Effect`) and run after commit; and operations that can be neither
//! repeated nor deferred (port I/O, remote stalls, IOAPIC programming, FPU
//! state on another core, TLB shootdowns) end the transaction's chances:
//! the entry reruns under the serial gate, where they run directly.
use crate::{apic, cpu, fpu, ioapic, percpu, serial, smp, timer, tlb};
use fl4_core::layout::{irq, PPTR_BASE};
use fl4_core::machine::Arch;

pub struct PhysArch;

/// IRR bits for the vectors the kernel takes as IRQs (0x20..=0x9f).
fn irq_requested() -> bool {
    let mut w = 1;
    while w <= 4 {
        let v = apic::read(apic::REG_IRR + w * 0x10);
        if v != 0 {
            return true;
        }
        w += 1;
    }
    false
}

#[derive(Clone, Copy)]
pub enum Effect {
    Deadline(u64),
    Mask(u64, bool),
    Ack,
    VSpace(u64, u64),
    Reschedule(u64),
    Putc(u8),
}

pub const MAX_EFFECTS: usize = 64;

fn in_tx() -> bool {
    percpu::get().tx
}

fn serial_needed() {
    fl4_store::tx::doom_serial(percpu::cpu_index() as u64);
}

/// Queue `e` if a transaction runs; returns whether it did.
fn defer(e: Effect) -> bool {
    let pc = percpu::get();
    if !pc.tx {
        return false;
    }
    if pc.neffects == MAX_EFFECTS {
        serial_needed();
    } else {
        pc.effects[pc.neffects] = e;
        pc.neffects += 1;
    }
    true
}

/// Run the effects the committed transaction queued.
pub fn apply_effects() {
    let n = percpu::get().neffects;
    for i in 0..n {
        match percpu::get().effects[i] {
            Effect::Deadline(t) => timer::set_deadline(t),
            Effect::Mask(irq, m) => ioapic::mask(irq, m),
            Effect::Ack => apic::eoi(),
            Effect::VSpace(root, asid) => switch_vspace(root, asid),
            Effect::Reschedule(m) => smp::reschedule(m),
            Effect::Putc(c) => serial::putc(c),
        }
    }
    percpu::get().neffects = 0;
}

/// Drop the effects of a transaction that did not commit.
pub fn discard_effects() {
    percpu::get().neffects = 0;
}

fn switch_vspace(root: u64, asid: u64) {
    tlb::switch(root.wrapping_sub(PPTR_BASE), asid);
}

impl Arch for PhysArch {
    fn virtualization(&self) -> u64 { crate::vm::backend() }
    fn vcpu_capability(&self, field: u64) -> u64 { crate::vm::capability(field) }
    fn vcpu_barrier(&mut self) { if in_tx() { serial_needed(); } }
    fn invalidate_ept(&mut self, root: u64, mask: u64) {
        if in_tx() { return serial_needed(); }
        crate::vm::invalidate_local(root);
        smp::remote_call(smp::CALL_EPT, root, 0, mask);
    }

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
        irq_requested()
    }
    /// An interrupt accepted here is kept until the entry completes, so a
    /// transaction that reruns sees it again.
    fn take_pending_irq(&mut self) -> u64 {
        let pc = percpu::get();
        if pc.held_irq != percpu::NO_IRQ {
            pc.held_used = true;
            return pc.held_irq;
        }
        pc.polled_irq = percpu::NO_IRQ;
        pc.polling = true;
        cpu::enable_interrupts_briefly();
        let pc = percpu::get();
        pc.polling = false;
        pc.held_irq = pc.polled_irq;
        pc.held_used = pc.held_irq != percpu::NO_IRQ;
        pc.polled_irq
    }
    fn mask_irq(&mut self, irq: u64, mask: bool) {
        if !defer(Effect::Mask(irq, mask)) {
            ioapic::mask(irq, mask)
        }
    }
    fn ack_irq(&mut self, _irq: u64) {
        if !defer(Effect::Ack) {
            apic::eoi()
        }
    }

    fn set_vspace(&mut self, root: u64, asid: u64) {
        if !defer(Effect::VSpace(root, asid)) {
            switch_vspace(root, asid)
        }
    }
    // An invalidation runs after the page tables changed, and other cores
    // running the address space are shot down (tlb.rs). The changes reach
    // memory only at commit, after which no IPI can be sent, so inside a
    // transaction an invalidation sends the entry to the serial gate.
    // (Mapping into an empty entry invalidates nothing and stays in the
    // transaction.)
    fn invalidate_page(&mut self, asid: u64, vaddr: u64) {
        if in_tx() {
            return serial_needed();
        }
        let remote = tlb::invalidate_page(asid, vaddr);
        smp::remote_call(smp::CALL_INVLPG, asid, vaddr, remote);
    }
    fn invalidate_asid(&mut self, asid: u64) {
        if in_tx() {
            return serial_needed();
        }
        let remote = tlb::invalidate_asid(asid);
        smp::remote_call(smp::CALL_FLUSH_TLB, asid, 0, remote);
    }
    fn invalidate_page_structures(&mut self, asid: u64) {
        self.invalidate_asid(asid)
    }

    fn ioapic_map(&mut self, ioapic: u64, pin: u64, level: u64, polarity: u64, vector: u64) -> bool {
        if ioapic >= ioapic::count() || pin >= ioapic::pins(ioapic) {
            return false;
        }
        if in_tx() {
            serial_needed();
            return true;
        }
        ioapic::map(ioapic, pin, level, polarity, vector, percpu::get_for(0).apic_id, 0, 0);
        true
    }
    fn ioapic_map_remapped(&mut self, ioapic: u64, pin: u64, level: u64, polarity: u64, vector: u64, handle: u64) -> bool {
        if ioapic >= ioapic::count() || pin >= ioapic::pins(ioapic) {
            return false;
        }
        if in_tx() {
            serial_needed();
            return true;
        }
        let high = (((handle & 0x7fff) as u32) << 17) | (1 << 16);
        let lo_extra = (((handle >> 15) & 1) as u32) << 11;
        ioapic::map(ioapic, pin, level, polarity, vector, 0, high, lo_extra);
        true
    }
    fn num_ioapics(&self) -> u64 {
        ioapic::count()
    }
    fn ioapic_pins(&self, i: u64) -> u64 {
        ioapic::pins(i)
    }

    fn port_in(&mut self, port: u64, size: u64) -> u64 {
        if in_tx() {
            serial_needed();
            return 0;
        }
        let p = port as u16;
        match size {
            1 => cpu::inb(p) as u64,
            2 => cpu::inw(p) as u64,
            _ => cpu::inl(p) as u64,
        }
    }
    fn port_out(&mut self, port: u64, size: u64, v: u64) {
        if in_tx() {
            return serial_needed();
        }
        let p = port as u16;
        match size {
            1 => cpu::outb(p, v as u8),
            2 => cpu::outw(p, v as u16),
            _ => cpu::outl(p, v as u32),
        }
    }

    // FPU images are written by XSAVE, not through the store: anything that
    // would touch live state, or write an image, runs serially.
    fn fpu_flush(&mut self, tcb: u64) {
        // Bringing a compacted image back to the standard format writes
        // the TCB outside the store.
        if in_tx() {
            if fpu::is_live(tcb) || fpu::compacting() {
                serial_needed();
            }
            return;
        }
        fpu::flush(tcb)
    }
    fn fpu_sanitise(&mut self, tcb: u64) {
        if in_tx() {
            return serial_needed();
        }
        fpu::sanitise(tcb)
    }
    fn fpu_reload(&mut self, tcb: u64) {
        if in_tx() {
            if fpu::is_live(tcb) {
                serial_needed();
            }
            return;
        }
        fpu::forget(tcb)
    }
    fn fpu_release(&mut self, tcb: u64) {
        if in_tx() {
            if fpu::is_live(tcb) {
                serial_needed();
            }
            return;
        }
        fpu::forget(tcb)
    }

    fn remote_stall(&mut self, cpu: u64) {
        if in_tx() {
            return serial_needed();
        }
        smp::remote_call(smp::CALL_STALL, 0, 0, 1u64 << (cpu & 63));
    }
    fn send_reschedule(&mut self, mask: u64) {
        if !defer(Effect::Reschedule(mask)) {
            smp::reschedule(mask)
        }
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
        if smp::multi() {
            print_stats();
        }
        cpu::halt_forever()
    }
}

/// Vector of the kernel timer interrupt.
pub const TIMER_VECTOR: u32 = (irq::TIMER + irq::INT_OFFSET) as u32;

/// Print how kernel entries ran (debug builds).
pub fn print_stats() {
    let mut line = [0u8; 96];
    let n = fmt_stats(&mut line);
    for &b in &line[..n] {
        serial::putc(b);
    }
    // This core's recent conflicts (fl4_store::tx::conflicts), in hex.
    let hex = |v: u64| {
        for i in (0..16).rev() {
            serial::putc(b"0123456789abcdef"[((v >> (4 * i)) & 15) as usize]);
        }
    };
    for b in b"FL4: recent conflicts:" {
        serial::putc(*b);
    }
    for c in fl4_store::tx::conflicts(percpu::cpu_index() as u64) {
        serial::putc(b' ');
        hex(c);
    }
    serial::putc(b'\n');
}

/// "FL4: N transactions committed, N aborted, N serial entries\n".
fn fmt_stats(out: &mut [u8; 96]) -> usize {
    use core::sync::atomic::Ordering::Relaxed;
    let mut n = 0;
    let mut put = |s: &[u8], n: &mut usize| {
        for &b in s {
            if *n < out.len() {
                out[*n] = b;
                *n += 1;
            }
        }
    };
    let num = |v: u64, buf: &mut [u8; 20]| -> usize {
        let mut i = 20;
        let mut v = v;
        loop {
            i -= 1;
            buf[i] = b'0' + (v % 10) as u8;
            v /= 10;
            if v == 0 {
                return i;
            }
        }
    };
    let mut b = [0u8; 20];
    put(b"FL4: ", &mut n);
    let i = num(smp::TX_COMMITS.load(Relaxed), &mut b);
    put(&b[i..], &mut n);
    put(b" transactions committed, ", &mut n);
    let i = num(smp::TX_ABORTS.load(Relaxed), &mut b);
    put(&b[i..], &mut n);
    put(b" aborted, ", &mut n);
    let i = num(smp::SERIAL_ENTRIES.load(Relaxed), &mut b);
    put(&b[i..], &mut n);
    put(b" serial entries\n", &mut n);
    n
}
