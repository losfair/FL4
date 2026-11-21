//! FL4's AArch64 hardware backend (DESIGN.md §11). Trusted code: the GIC
//! (v2 or v3), the generic timer, the MMU's address-space switches and
//! broadcast TLB maintenance, lazy FP/SIMD switching, PSCI and the
//! console UART. The kernel runs at EL1 without EL2 support.
#![no_std]

pub mod ap_caps;
pub mod arch;
pub mod cpu;
pub mod el0_access;
pub mod fpu;
pub mod gic;
pub mod gic_layout;
pub mod mmu;
pub mod percpu;
pub mod serial;
pub mod smp;
pub mod timer;
