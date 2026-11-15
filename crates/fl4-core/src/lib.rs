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

pub mod boot;
pub mod capability;
pub mod cdt;
pub mod cnode;
pub mod cspace;
pub mod debug;
pub mod domain;
pub mod endpoint;
pub mod ept;
pub mod error;
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
pub mod regs;
pub mod sched;
pub mod schedcontext;
pub mod smp;
pub mod sporadic;
pub mod syscall;
pub mod tcb;
pub mod tcbqueue;
pub mod timer;
pub mod untyped;
pub mod vspace;
pub mod vcpu;
