//! Lazy FP/SIMD switching. A thread that does not own this core's FP/SIMD
//! registers runs with EL0 access trapped (CPACR_EL1.FPEN); its first
//! FP/SIMD instruction traps, and the entry glue loads its state and
//! returns to it without entering the core. A thread that keeps using
//! FP/SIMD is switched eagerly after its third trap, as on x86_64. The
//! kernel itself is built without FP/SIMD.
use crate::percpu;
use fl4_core::layout::tcb;

const EAGER_AFTER: u8 = 3;
/// CPACR_EL1.FPEN: EL0 traps (EL1 does not), or nothing traps.
const FPEN_EL0_TRAP: u64 = 1 << 20;
const FPEN_NONE: u64 = 3 << 20;

fn image(t: u64) -> u64 {
    t + tcb::FPU
}

fn use_count(t: u64) -> *mut u8 {
    (t + tcb::FPU_USE) as *mut u8
}

pub fn init() {
    crate::msr!("cpacr_el1", FPEN_EL0_TRAP);
    crate::cpu::isb();
    percpu::get().fp_enabled.set(false);
}

fn set_enabled(on: bool) {
    let pc = percpu::get();
    if pc.fp_enabled.get() != on {
        crate::msr!("cpacr_el1", if on { FPEN_NONE } else { FPEN_EL0_TRAP });
        crate::cpu::isb();
        pc.fp_enabled.set(on);
    }
}

fn save(t: u64) {
    let p = image(t);
    unsafe {
        core::arch::asm!(
            ".arch_extension fp",
            ".arch_extension simd",
            "stp q0, q1, [{p}, #0]",
            "stp q2, q3, [{p}, #32]",
            "stp q4, q5, [{p}, #64]",
            "stp q6, q7, [{p}, #96]",
            "stp q8, q9, [{p}, #128]",
            "stp q10, q11, [{p}, #160]",
            "stp q12, q13, [{p}, #192]",
            "stp q14, q15, [{p}, #224]",
            "stp q16, q17, [{p}, #256]",
            "stp q18, q19, [{p}, #288]",
            "stp q20, q21, [{p}, #320]",
            "stp q22, q23, [{p}, #352]",
            "stp q24, q25, [{p}, #384]",
            "stp q26, q27, [{p}, #416]",
            "stp q28, q29, [{p}, #448]",
            "stp q30, q31, [{p}, #480]",
            "mrs {a}, fpsr",
            "mrs {b}, fpcr",
            "str {a:w}, [{p}, #512]",
            "str {b:w}, [{p}, #516]",
            p = in(reg) p,
            a = out(reg) _,
            b = out(reg) _,
            options(nostack)
        );
    }
}

fn restore(t: u64) {
    let p = image(t);
    unsafe {
        core::arch::asm!(
            ".arch_extension fp",
            ".arch_extension simd",
            "ldp q0, q1, [{p}, #0]",
            "ldp q2, q3, [{p}, #32]",
            "ldp q4, q5, [{p}, #64]",
            "ldp q6, q7, [{p}, #96]",
            "ldp q8, q9, [{p}, #128]",
            "ldp q10, q11, [{p}, #160]",
            "ldp q12, q13, [{p}, #192]",
            "ldp q14, q15, [{p}, #224]",
            "ldp q16, q17, [{p}, #256]",
            "ldp q18, q19, [{p}, #288]",
            "ldp q20, q21, [{p}, #320]",
            "ldp q22, q23, [{p}, #352]",
            "ldp q24, q25, [{p}, #384]",
            "ldp q26, q27, [{p}, #416]",
            "ldp q28, q29, [{p}, #448]",
            "ldp q30, q31, [{p}, #480]",
            "ldr {a:w}, [{p}, #512]",
            "ldr {b:w}, [{p}, #516]",
            "msr fpsr, {a}",
            "msr fpcr, {b}",
            p = in(reg) p,
            a = out(reg) _,
            b = out(reg) _,
            options(nostack)
        );
    }
}

/// Exit path: make FP/SIMD right for thread `t`.
pub fn switch_to(t: u64, fpu_disabled: bool) {
    if fpu_disabled {
        set_enabled(false);
        return;
    }
    if owner() == t {
        set_enabled(true);
        return;
    }
    let n = unsafe { core::ptr::read_volatile(use_count(t)) };
    if n < EAGER_AFTER {
        set_enabled(false);
        return;
    }
    unsafe { core::ptr::write_volatile(use_count(t), n.wrapping_add(1)) };
    set_enabled(true);
    load(t);
}

/// The TCB whose state this core's registers hold (0 = none).
fn owner() -> u64 {
    percpu::fpu_owner(percpu::cpu_index())
}

/// Ownership moves only after the registers were saved, and with release
/// order (`percpu::set_fpu_owner`): a core that no longer sees a thread as
/// the owner here (`owner_core`, acquire) reads its saved image, which must
/// hold the saved registers, not what the TCB held before.
fn load(t: u64) {
    let old = owner();
    if old != 0 {
        save(old);
    }
    restore(t);
    percpu::set_fpu_owner(t);
}

/// An FP/SIMD trap from thread `t`: give it the registers.
pub fn lazy_load(t: u64) {
    unsafe {
        let n = core::ptr::read_volatile(use_count(t));
        core::ptr::write_volatile(use_count(t), n.saturating_add(1).max(1));
    }
    set_enabled(true);
    if owner() != t {
        load(t);
    }
}

/// Write `t`'s state back to its TCB if it is live on this core.
fn flush_local(t: u64) {
    if owner() == t {
        save(t);
    }
}

/// Forget `t`'s state if it is live on this core.
pub fn forget_local(t: u64) {
    if owner() == t {
        percpu::set_fpu_owner(0);
    }
}

/// Save `t`'s state to its TCB and forget it, if it is live on this core.
/// EL0 access ends up trapped: a thread that was running with the
/// registers (one whose FP/SIMD was just disabled) traps on its next
/// FP/SIMD instruction instead of changing registers no one saves; any
/// other thread on this core had it trapped already, as a thread that does
/// not own the registers runs so.
pub fn release_local(t: u64) {
    if owner() == t {
        save(t);
        percpu::set_fpu_owner(0);
        set_enabled(false);
    }
}

fn owner_core(t: u64) -> Option<usize> {
    (0..percpu::MAX_CPUS).find(|&c| percpu::fpu_owner(c) == t)
}

pub fn is_live(t: u64) -> bool {
    owner_core(t).is_some()
}

/// The remote call `flush` makes for state live on core `owner`, if any,
/// when it runs on core `me`.
///
/// Another core gives the state up, not just saves it: it still owns the
/// registers otherwise, and its next load for another thread (`lazy_load`
/// on an FP/SIMD trap, or an exit's `switch_to`, neither under the serial
/// gate) saves them over `t`'s image while this core reads or rewrites it
/// (TCB_ReadFPU, TCB_WriteFPU's copy and `sanitise`). `t` does not run
/// there (callers stall or migrate it first), so the release takes nothing
/// from the thread that does.
fn flush_call(owner: Option<usize>, me: usize) -> Option<(u64, usize)> {
    match owner {
        Some(c) if c != me => Some((crate::smp::CALL_FPU_RELEASE, c)),
        _ => None,
    }
}

/// Write `t`'s live state, wherever it is, back to its TCB. The caller
/// holds the serial gate when another core may hold the state; it is no
/// longer live there afterwards (`flush_call`).
pub fn flush(t: u64) {
    let owner = owner_core(t);
    let me = percpu::cpu_index();
    match flush_call(owner, me) {
        Some((call, c)) => crate::smp::remote_call(call, t, 0, 1 << c),
        None if owner == Some(me) => flush_local(t),
        None => {}
    }
}

/// `t`'s state is no longer (or no longer only) in some core's registers.
pub fn forget(t: u64) {
    match owner_core(t) {
        Some(c) if c == percpu::cpu_index() => forget_local(t),
        Some(c) => crate::smp::remote_call(crate::smp::CALL_FPU_DROP, t, 0, 1 << c),
        None => {}
    }
}

/// `t` is being deleted, moved away or loses FP/SIMD: save its live
/// state, wherever it is, to its TCB and forget it there (seL4
/// `fpuRelease`). The caller holds the serial gate when another core may
/// hold the state.
pub fn release(t: u64) {
    match owner_core(t) {
        Some(c) if c == percpu::cpu_index() => release_local(t),
        Some(c) => crate::smp::remote_call(crate::smp::CALL_FPU_RELEASE, t, 0, 1 << c),
        None => {}
    }
}

/// Keep only the defined FPSR and FPCR bits of a user-written image
/// (l4h 0002).
pub fn sanitise(t: u64) {
    let p = image(t) + 512;
    unsafe {
        let w = p as *mut u64;
        let v = core::ptr::read_volatile(w);
        let fpsr = (v as u32) & 0xf800_009f;
        let fpcr = ((v >> 32) as u32) & 0x07ff_9f07;
        core::ptr::write_volatile(w, fpsr as u64 | ((fpcr as u64) << 32));
    }
}

