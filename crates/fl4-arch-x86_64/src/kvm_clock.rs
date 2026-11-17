//! Read KVM's virtual TSC rate once, before native CPUID or PIT calibration.
//! CPUID 0x15 can describe the physical CPU instead (GCE C3: 1.9 vs 2.7 GHz).

#[cfg(not(test))]
use crate::cpu::{cpuid, wrmsr};
use core::ptr::{addr_of, addr_of_mut};
use core::sync::atomic::{compiler_fence, Ordering};
#[cfg(test)]
use tests::{cpuid, wrmsr};

#[repr(C, align(32))]
struct ClockInfo {
    version: u32,
    pad: u32,
    tsc_timestamp: u64,
    system_time: u64,
    mul: u32,
    shift: i8,
    flags: u8,
    reserved: [u8; 2],
}

static mut CLOCK: ClockInfo = ClockInfo {
    version: 0,
    pad: 0,
    tsc_timestamp: 0,
    system_time: 0,
    mul: 0,
    shift: 0,
    flags: 0,
    reserved: [0; 2],
};

fn clock_msr() -> Option<u32> {
    if cpuid(1, 0).ecx & (1 << 31) == 0 {
        return None;
    }
    let r = cpuid(0x4000_0000, 0);
    if [r.ebx, r.ecx, r.edx] != [0x4b4d_564b, 0x564b_4d56, 0x4d]
        || (r.eax != 0 && r.eax < 0x4000_0001)
    {
        return None;
    }
    let features = cpuid(0x4000_0001, 0).eax;
    if features & (1 << 3) != 0 {
        Some(0x4b56_4d01)
    } else if features & 1 != 0 {
        Some(0x12)
    } else {
        None
    }
}

fn scale_mhz(mul: u32, shift: i8) -> u32 {
    if mul == 0 || !(-31..=31).contains(&shift) {
        return 0;
    }
    let mut khz = (1_000_000u128 << 32) / mul as u128;
    if shift < 0 {
        khz <<= -shift;
    } else {
        khz >>= shift;
    }
    ((khz + 500) / 1000).try_into().unwrap_or(0)
}

/// MHz, the unit FL4 publishes in bootinfo. The buffer is in the kernel
/// image mapping, not the physical-memory window. Only the boot core calls
/// this; unregister before returning so KVM stops writing to the buffer.
pub fn tsc_mhz() -> u32 {
    // KVM writes this buffer through its shared view. In an encrypted
    // guest it belongs to a private kernel page; use the other clock sources.
    if crate::sev::mask() != 0 { return 0; }
    let Some(msr) = clock_msr() else { return 0 };
    let clock = addr_of_mut!(CLOCK);
    compiler_fence(Ordering::SeqCst);
    wrmsr(msr, (clock as u64).wrapping_sub(0xffff_ffff_8000_0000) | 1);
    let mut mhz = 0;
    for _ in 0..10000 {
        // x86 orders the loads; volatile reads and compiler fences keep
        // the version checks on either side of this scale snapshot.
        let version = unsafe { addr_of!((*clock).version).read_volatile() };
        compiler_fence(Ordering::SeqCst);
        let mul = unsafe { addr_of!((*clock).mul).read_volatile() };
        let shift = unsafe { addr_of!((*clock).shift).read_volatile() };
        compiler_fence(Ordering::SeqCst);
        if version != 0
            && version & 1 == 0
            && version == unsafe { addr_of!((*clock).version).read_volatile() }
        {
            mhz = scale_mhz(mul, shift);
            break;
        }
    }
    wrmsr(msr, 0);
    compiler_fence(Ordering::SeqCst);
    mhz
}

#[cfg(test)]
mod tests {
    extern crate std;
    pub use io::{cpuid, wrmsr};
    mod io {
        use super::std;
        use crate::cpu::Cpuid;
        use std::cell::RefCell;
        use std::vec::Vec;
        #[derive(Clone)]
        pub struct Host {
            pub hypervisor: bool,
            pub kvm: bool,
            pub max_leaf: u32,
            pub features: u32,
            pub version: u32,
            pub mul: u32,
            pub shift: i8,
            pub writes: Vec<(u32, u64)>,
        }
        impl Default for Host {
            fn default() -> Self {
                Self {
                    hypervisor: true,
                    kvm: true,
                    max_leaf: 0x4000_0001,
                    features: 9,
                    version: 2,
                    mul: 1590728628,
                    shift: 0,
                    writes: std::vec![],
                }
            }
        }
        std::thread_local! { pub static HOST: RefCell<Host> = RefCell::new(Host::default()); }
        pub fn cpuid(leaf: u32, _: u32) -> Cpuid {
            let r = HOST.with_borrow(|h| match leaf {
                1 => [0, 0, if h.hypervisor { 1 << 31 } else { 0 }, 0],
                0x4000_0000 => [
                    h.max_leaf,
                    if h.kvm { 0x4b4d_564b } else { 0 },
                    0x564b_4d56,
                    0x4d,
                ],
                0x4000_0001 => [h.features, 0, 0, 0],
                _ => panic!("unexpected CPUID leaf {leaf:x}"),
            });
            Cpuid {
                eax: r[0],
                ebx: r[1],
                ecx: r[2],
                edx: r[3],
            }
        }
        pub fn wrmsr(msr: u32, value: u64) {
            HOST.with_borrow_mut(|h| {
                h.writes.push((msr, value));
                if value & 1 != 0 {
                    assert_eq!(value & 31, 1);
                    let p = (value & !1).wrapping_add(0xffff_ffff_8000_0000) as *mut u8;
                    unsafe {
                        p.cast::<u32>().write_volatile(h.version);
                        p.add(24).cast::<u32>().write_volatile(h.mul);
                        p.add(28).cast::<i8>().write_volatile(h.shift);
                    }
                }
            });
        }
    }

    #[test]
    fn scale_features_and_buffer_lifetime() {
        use io::Host;
        let check = |host: Host, expected, msr| {
            io::HOST.set(host);
            assert_eq!(super::tsc_mhz(), expected);
            io::HOST.with_borrow(|h| {
                assert_eq!(h.writes.len(), if msr == 0 { 0 } else { 2 });
                if msr != 0 {
                    assert_eq!(h.writes.last(), Some(&(msr, 0)));
                }
            });
        };
        let msr = 0x4b56_4d01;
        check(Host::default(), 2700, msr);
        check(
            Host {
                mul: 3181457256,
                shift: -1,
                ..Host::default()
            },
            2700,
            msr,
        );
        check(
            Host {
                mul: 2147483648,
                shift: 1,
                ..Host::default()
            },
            1000,
            msr,
        );
        check(
            Host {
                features: 1,
                max_leaf: 0,
                ..Host::default()
            },
            2700,
            0x12,
        );
        for version in [0, 1] {
            check(
                Host {
                    version,
                    ..Host::default()
                },
                0,
                msr,
            );
        }
        check(
            Host {
                mul: 0,
                ..Host::default()
            },
            0,
            msr,
        );
        for shift in [-128, -31, 127] {
            check(
                Host {
                    mul: 1,
                    shift,
                    ..Host::default()
                },
                0,
                msr,
            );
        }
        check(
            Host {
                features: 0,
                ..Host::default()
            },
            0,
            0,
        );
        check(
            Host {
                kvm: false,
                ..Host::default()
            },
            0,
            0,
        );
        check(
            Host {
                hypervisor: false,
                ..Host::default()
            },
            0,
            0,
        );
        check(
            Host {
                max_leaf: 0x4000_0000,
                ..Host::default()
            },
            0,
            0,
        );
    }
}
