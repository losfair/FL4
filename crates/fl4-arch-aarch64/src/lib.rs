//! FL4's AArch64 hardware backend (DESIGN.md §11). Trusted code: the GIC
//! (v2 or v3), the generic timer, the MMU's address-space switches and
//! broadcast TLB maintenance, lazy FP/SIMD switching, PSCI and the
//! console UART. The kernel runs at EL1, at EL2 with VHE, or at EL1 beside
//! an EL2 nVHE switch stub (hyp_nvhe.rs), as `cpu::ElMode` decides at boot;
//! in the EL2 modes it runs guests (vcpu.rs).
#![no_std]

pub mod ap_caps;
pub mod arch;
pub mod cpu;
pub mod el0_access;
pub mod fpu;
pub mod gic;
pub mod gic_layout;
pub mod hyp_nvhe;
pub mod its;
pub mod mmu;
pub mod percpu;
pub mod serial;
pub mod smp;
pub mod timer;
pub mod vcpu;
pub mod vmid;
