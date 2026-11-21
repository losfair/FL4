//! FL4 kernel logic. Every kernel decision lives here. The crate must stay
//! inside the Rust subset that Charon and Aeneas translate (DESIGN.md §6):
//! no unsafe, no alloc, no closures stored in data, no `dyn`, explicit
//! checked or wrapping arithmetic, loops bounded by kernel-controlled data.
//!
//! All kernel state lives in memory reached through `machine::Store`;
//! hardware is reached through `machine::Arch`.
#![no_std]
#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments, clippy::needless_range_loop)]

// Select the source directory once. Keeping the items in their original
// Rust modules also keeps the declaration paths consumed by Aeneas stable.
macro_rules! select_arch {
    ($dir:literal, $debug:literal, $regs:literal, $vspace:literal) => {
        macro_rules! arch_items {
            ($file:literal) => {
                include!(concat!(env!("CARGO_MANIFEST_DIR"), "/src/", $dir, "/", $file));
            };
        }
        #[path = $debug]
        pub mod debug;
        #[path = $regs]
        pub mod regs;
        #[path = $vspace]
        pub mod vspace;
    };
}
#[cfg(feature = "aarch64")]
select_arch!("arch/aarch64", "arch/aarch64/debug.rs", "arch/aarch64/regs.rs", "arch/aarch64/vspace.rs");
#[cfg(not(feature = "aarch64"))]
select_arch!("arch/x86_64", "arch/x86_64/debug.rs", "arch/x86_64/regs.rs", "arch/x86_64/vspace.rs");

pub mod boot;
pub mod capability;
pub mod cdt;
pub mod cnode;
pub mod cspace;
pub mod domain;
pub mod endpoint;
pub mod ept;
pub mod error;
pub mod fastpath;
pub mod faults;
pub mod interrupt;
pub mod ioport;
pub mod ipc;
pub mod layout;
pub mod machine;
pub mod msg;
pub mod msginfo;
pub mod notification;
pub mod obj;
pub mod objects;
pub mod sched;
pub mod schedcontext;
pub mod smp;
pub mod sporadic;
pub mod syscall;
pub mod tcb;
pub mod tcbqueue;
pub mod timer;
pub mod untyped;
pub mod vcpu;
