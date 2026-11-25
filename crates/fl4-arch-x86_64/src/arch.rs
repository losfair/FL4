//! `fl4_core::machine::Arch` on x86_64 hardware. Every operation runs at
//! once: kernel entries run under the serial gate, or are local paths
//! beside it whose operations concern their own core (DESIGN.md §7).
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

/// IRQ `irq` is free again (its handler was deleted): mask its pin and drop
/// its route (`ioapic::forget`).
pub fn forget_irq(irq: u64) {
    ioapic::forget(irq)
}

#[inline(always)]
fn switch_vspace(root: u64, asid: u64) {
    tlb::switch(root.wrapping_sub(PPTR_BASE), asid);
}

impl Arch for PhysArch {
    fn private_device_frame(&self, paddr: u64) -> bool { crate::cvm::private_device(paddr) }

    fn dma_ram(&self, base: u64, bytes: u64) -> bool { crate::cvm::is_dma_ram(base, bytes) }

    fn dma_frame(&mut self, base: u64, bytes: u64, shared: bool) {
        crate::cvm::transition(base, bytes, shared);
    }

    fn tdx_active(&self) -> bool { crate::tdx::active() }

    fn tdx_report(&mut self, frame_ptr: u64, d0: u64, d1: u64, d2: u64, d3: u64, d4: u64, d5: u64, d6: u64, d7: u64) -> u64 {
        crate::tdx::report(frame_ptr, &[d0, d1, d2, d3, d4, d5, d6, d7])
    }

    fn tdx_extend_rtmr(&mut self, index: u64, d0: u64, d1: u64, d2: u64, d3: u64, d4: u64, d5: u64) -> u64 {
        crate::tdx::extend_rtmr(index, &[d0, d1, d2, d3, d4, d5])
    }

    fn tdx_get_quote(&mut self, frame_ptr: u64, buf_len: u64) -> u64 {
        crate::tdx::get_quote(fl4_core::layout::paddr(frame_ptr) | crate::cvm::shared_mask(), buf_len)
    }

    fn virtualization(&self) -> u64 { crate::vm::backend() }
    fn vcpu_capability(&self, field: u64) -> u64 { crate::vm::capability(field) }
    fn vcpu_barrier(&mut self) {}
    fn vcpu_sync(&mut self, v: u64, field: u64) {
        crate::vm::sync(v, field)
    }
    fn vcpu_release(&mut self, v: u64) {
        crate::vm::release(v)
    }
    fn invalidate_ept(&mut self, root: u64, mask: u64) {
        crate::vm::invalidate_local(root);
        smp::remote_call(smp::CALL_EPT, root, 0, mask);
    }

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
        irq_requested()
    }
    fn take_pending_irq(&mut self) -> u64 {
        let pc = percpu::get();
        pc.polled_irq.set(percpu::NO_IRQ);
        pc.polling.set(true);
        cpu::enable_interrupts_briefly();
        let pc = percpu::get();
        pc.polling.set(false);
        pc.polled_irq.get()
    }
    fn mask_irq(&mut self, irq: u64, mask: bool) {
        ioapic::mask(irq, mask)
    }
    fn irq_free(&mut self, irq: u64) {
        forget_irq(irq);
    }
    fn ack_irq(&mut self, _irq: u64) {
        apic::eoi()
    }

    #[inline(always)]
    fn set_vspace(&mut self, root: u64, asid: u64) {
        switch_vspace(root, asid)
    }
    // An invalidation runs after the page tables changed, and other cores
    // running the address space are shot down (tlb.rs).
    fn invalidate_page(&mut self, asid: u64, vaddr: u64) {
        let remote = tlb::invalidate_page(asid, vaddr);
        smp::remote_call(smp::CALL_INVLPG, asid, vaddr, remote);
    }
    fn invalidate_asid(&mut self, asid: u64) {
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
        // False only for a boot CPU whose x2APIC ID a compatibility entry
        // cannot name; the pin then stays as it was (masked, unless an
        // earlier request routed it).
        ioapic::map(ioapic, pin, level, polarity, vector, percpu::apic_id(0), 0, 0)
    }
    fn ioapic_map_remapped(&mut self, ioapic: u64, pin: u64, level: u64, polarity: u64, vector: u64, handle: u64) -> bool {
        if ioapic >= ioapic::count() || pin >= ioapic::pins(ioapic) {
            return false;
        }
        let high = (((handle & 0x7fff) as u32) << 17) | (1 << 16);
        let lo_extra = (((handle >> 15) & 1) as u32) << 11;
        ioapic::map(ioapic, pin, level, polarity, vector, 0, high, lo_extra)
    }
    fn num_ioapics(&self) -> u64 {
        ioapic::count()
    }
    fn ioapic_pins(&self, i: u64) -> u64 {
        ioapic::pins(i)
    }

    fn port_in(&mut self, port: u64, size: u64) -> u64 {
        let p = port as u16;
        match size {
            1 => cpu::inb(p) as u64,
            2 => cpu::inw(p) as u64,
            _ => cpu::inl(p) as u64,
        }
    }
    fn port_out(&mut self, port: u64, size: u64, v: u64) {
        let p = port as u16;
        match size {
            1 => cpu::outb(p, v as u8),
            2 => cpu::outw(p, v as u16),
            _ => cpu::outl(p, v as u32),
        }
    }

    fn fpu_flush(&mut self, tcb: u64) {
        fpu::flush(tcb)
    }
    fn fpu_sanitise(&mut self, tcb: u64) {
        fpu::sanitise(tcb)
    }
    fn fpu_reload(&mut self, tcb: u64) {
        fpu::forget(tcb)
    }
    fn fpu_release(&mut self, tcb: u64) {
        fpu::release(tcb)
    }

    fn remote_stall(&mut self, cpu: u64) {
        smp::remote_call(smp::CALL_STALL, 0, 0, 1u64 << (cpu & 63));
    }
    fn send_reschedule(&mut self, mask: u64) {
        smp::reschedule(mask)
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
}

/// "FL4: N serial entries\n".
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
    let i = num(smp::SERIAL_ENTRIES.load(Relaxed), &mut b);
    put(&b[i..], &mut n);
    put(b" serial entries\n", &mut n);
    n
}
