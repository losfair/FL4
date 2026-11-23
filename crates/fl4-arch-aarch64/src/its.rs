//! The GICv3 ITS (GIC architecture specification, IHI 0069, chapters 5
//! and 6): MSIs of PCI functions become LPIs, the kernel's IRQs from
//! `irq::LPI_BASE` (`fl4_core` `GetMSI`). Boot gives the ITS its tables
//! and every redistributor its LPI tables; afterwards `map` and `unmap`
//! issue the commands for one event at a time, under the serial gate.
//!
//! Every table is in kernel RAM that user space never gets. The kernel
//! writes the command queue and the LPI configuration table, and cleans
//! what it wrote to the point of coherency whatever shareability the ITS
//! accepted; the tables the GIC itself writes are cleaned once, empty, at
//! boot, and never touched again.
//!
//! LPIs are edge triggered and have no active state: they are not masked
//! between a signal and its acknowledgement (as MSIs on x86_64), and a
//! deleted handler's event is discarded.
use crate::cpu;
use core::cell::UnsafeCell;
use fl4_core::layout::{irq, pptr};

/// Events per device (each device's ITT holds this many).
pub const EVENTS: u64 = 64;
const EVENT_BITS: u64 = 6;
/// Devices with an ITT at once.
pub const MAX_DEVICES: usize = 32;
/// Device IDs the device table covers at most: PCI requester IDs of
/// buses 0-15.
const DEVICE_IDS: u64 = 4096;

const PAGE64K: u64 = 0x1_0000;
/// The memory `init` lays out from its 64 KiB aligned base: the LPI
/// configuration table, the command queue, the device table, the
/// collection table, the ITTs, then one pending table per core.
const PROP_OFF: u64 = 0;
const CMD_OFF: u64 = PAGE64K;
const DEV_OFF: u64 = 2 * PAGE64K;
const COLL_OFF: u64 = 3 * PAGE64K;
const ITT_OFF: u64 = 4 * PAGE64K;
const PEND_OFF: u64 = 5 * PAGE64K;
const CMD_BYTES: u64 = PAGE64K;
const CMD_SLOTS: u64 = CMD_BYTES / 32;

/// Bytes `init` needs for `ncpus` cores, 64 KiB aligned.
pub const fn memory_size(ncpus: usize) -> u64 {
    PEND_OFF + ncpus as u64 * PAGE64K
}

/// LPI interrupt ID bits the configuration table covers (8192 + 8192).
const LPI_ID_BITS: u64 = 14;
const _: () = assert!(irq::LPI_ID_BASE + irq::NUM_LPIS <= 1 << LPI_ID_BITS);
/// An enabled LPI at the priority of every other interrupt (gic.rs).
const LPI_ENABLED: u8 = 0xa0 | 1;

const GITS_CTLR: u64 = 0x0;
const GITS_TYPER: u64 = 0x8;
const GITS_CBASER: u64 = 0x80;
const GITS_CWRITER: u64 = 0x88;
const GITS_CREADR: u64 = 0x90;
const GITS_BASER: u64 = 0x100;
/// The translation frame's doorbell, 64 KiB into the ITS.
pub const GITS_TRANSLATER: u64 = 0x1_0040;
/// The ITS's two 64 KiB frames.
pub const ITS_SIZE: u64 = 2 * PAGE64K;

const GICR_CTLR: u64 = 0x0;
const GICR_TYPER: u64 = 0x8;
const GICR_PROPBASER: u64 = 0x70;
const GICR_PENDBASER: u64 = 0x78;

/// Normal, inner and outer write-back read/write-allocate, inner
/// shareable: the attributes the kernel window maps RAM with.
const CACHE_RAWAWB: u64 = 7;
const SHARE_INNER: u64 = 1;

const BASER_VALID: u64 = 1 << 63;
const BASER_TYPE_DEVICE: u64 = 1;
const BASER_TYPE_COLLECTION: u64 = 4;

struct Device {
    id: u64,
    /// Events mapped, a bit each; 0: the slot is free.
    events: u64,
}

struct Its {
    va: u64,
    mem: u64,
    ready: bool,
    pta: bool,
    num_devices: u64,
    /// Bytes of one ITT, 256-aligned.
    itt_size: u64,
    /// RDbase field of each core's collection (`target`).
    rdbase: [u64; crate::percpu::MAX_CPUS],
    cwriter: u64,
    devices: [Device; MAX_DEVICES],
    /// Per LPI: device slot + 1 (0: unmapped), event.
    lpis: [(u8, u8); irq::NUM_LPIS as usize],
    failed: bool,
}

struct Global(UnsafeCell<Its>);
// SAFETY: boot runs before the other cores take interrupts or enter the
// kernel; afterwards only kernel entries under the serial gate call
// `map` and `unmap`.
unsafe impl Sync for Global {}

static ITS: Global = Global(UnsafeCell::new(Its {
    va: 0,
    mem: 0,
    ready: false,
    pta: false,
    num_devices: 0,
    itt_size: 0,
    rdbase: [0; crate::percpu::MAX_CPUS],
    cwriter: 0,
    devices: [const { Device { id: 0, events: 0 } }; MAX_DEVICES],
    lpis: [(0, 0); irq::NUM_LPIS as usize],
    failed: false,
}));

fn its() -> &'static mut Its {
    // SAFETY: see `Global`.
    unsafe { &mut *ITS.0.get() }
}

fn rd32(a: u64) -> u32 {
    unsafe { core::ptr::read_volatile(a as *const u32) }
}
fn wr32(a: u64, v: u32) {
    unsafe { core::ptr::write_volatile(a as *mut u32, v) }
}
fn rd64(a: u64) -> u64 {
    unsafe { core::ptr::read_volatile(a as *const u64) }
}
fn wr64(a: u64, v: u64) {
    unsafe { core::ptr::write_volatile(a as *mut u64, v) }
}

/// What the root task learns (`SEL4_BOOTINFO_HEADER_AARCH64_MSI_INFO`).
#[derive(Clone, Copy, Debug)]
pub struct Info {
    pub doorbell: u64,
    pub num_lpis: u64,
    pub num_events: u64,
    pub num_devices: u64,
}

/// Whether the distributor has LPIs with enough interrupt ID bits.
pub fn supported() -> bool {
    let typer = crate::gic::dist_typer();
    crate::gic::version() == 3 && typer & (1 << 17) != 0 && ((typer >> 19) & 0x1f) + 1 >= LPI_ID_BITS as u32
}

/// Set up the ITS mapped at `va` (physically `pa`, `ITS_SIZE` bytes) with
/// `memory_size(ncpus)` bytes of RAM at the 64 KiB aligned `mem`, and LPIs
/// on the first `ncpus` cores (`gicr_pa`: a core's redistributor's
/// physical address). After `smp::start_aps`. An error leaves LPIs off.
pub fn init(va: u64, pa: u64, mem: u64, ncpus: usize, gicr_pa: impl Fn(usize) -> Option<u64>) -> Result<Info, &'static str> {
    let s = its();
    if !supported() {
        return Err("the distributor has no LPIs");
    }
    if mem % PAGE64K != 0 || ncpus > s.rdbase.len() {
        return Err("bad ITS memory");
    }
    let mva = pptr(mem);
    unsafe { core::ptr::write_bytes(mva as *mut u8, 0, memory_size(ncpus) as usize) };
    cpu::clean_inval_dcache_poc(mva, memory_size(ncpus));
    cpu::dsb_sy();

    // Quiesce the ITS before giving it tables.
    wr32(va + GITS_CTLR, 0);
    let mut n = 0u64;
    while rd32(va + GITS_CTLR) & (1 << 31) == 0 {
        n += 1;
        if n > 10_000_000 {
            return Err("the ITS does not quiesce");
        }
        core::hint::spin_loop();
    }
    let typer = rd64(va + GITS_TYPER);
    if typer & 1 == 0 {
        return Err("the ITS has no physical LPIs");
    }
    let itt_esz = ((typer >> 4) & 0xf) + 1;
    let event_bits = ((typer >> 8) & 0x1f) + 1;
    let dev_bits = ((typer >> 13) & 0x1f) + 1;
    let pta = typer & (1 << 19) != 0;
    let hcc = (typer >> 24) & 0xff;
    let cil = typer & (1 << 36) != 0;
    let cid_bits = if cil { ((typer >> 32) & 0xf) + 1 } else { 16 };
    if event_bits < EVENT_BITS || (ncpus as u64) > (1 << cid_bits) {
        return Err("the ITS has too few event or collection IDs");
    }
    let mut num_devices = DEVICE_IDS.min(1 << dev_bits.min(32));

    // The device table (flat), and a collection table unless the ITS holds
    // every core's collection itself.
    let mut has_dev = false;
    for i in 0..8u64 {
        let reg = va + GITS_BASER + i * 8;
        let v = rd64(reg);
        let ty = (v >> 56) & 7;
        let esz = ((v >> 48) & 0x1f) + 1;
        let off = match ty {
            BASER_TYPE_DEVICE => {
                num_devices = num_devices.min(PAGE64K / esz);
                has_dev = true;
                DEV_OFF
            }
            BASER_TYPE_COLLECTION if hcc < ncpus as u64 => {
                if (ncpus as u64) * esz > PAGE64K {
                    return Err("collection table too large");
                }
                COLL_OFF
            }
            _ => {
                wr64(reg, 0);
                continue;
            }
        };
        let base = mem + off;
        let mut ok = false;
        // Page sizes 64, 16 and 4 KiB: the first the ITS keeps.
        for (psz_field, psz) in [(2u64, PAGE64K), (1, 0x4000), (0, 0x1000)] {
            let want = BASER_VALID | CACHE_RAWAWB << 59 | ty << 56 | base | SHARE_INNER << 10 | psz_field << 8 | (PAGE64K / psz - 1);
            wr64(reg, want);
            let got = rd64(reg);
            if (got >> 8) & 3 == psz_field {
                ok = got & BASER_VALID != 0;
                break;
            }
        }
        if !ok {
            return Err("the ITS refuses its table");
        }
    }
    if !has_dev {
        return Err("the ITS has no device table");
    }

    // The command queue.
    wr64(va + GITS_CBASER, BASER_VALID | CACHE_RAWAWB << 59 | (mem + CMD_OFF) | SHARE_INNER << 10 | (CMD_BYTES / 0x1000 - 1));
    wr64(va + GITS_CWRITER, 0);
    if rd64(va + GITS_CBASER) & BASER_VALID == 0 {
        return Err("the ITS refuses its command queue");
    }
    s.va = va;
    s.mem = mem;
    s.pta = pta;
    s.cwriter = 0;
    s.num_devices = num_devices;
    s.itt_size = (EVENTS * itt_esz).next_multiple_of(256);
    if s.itt_size * MAX_DEVICES as u64 > PAGE64K {
        return Err("ITTs too large");
    }
    wr32(va + GITS_CTLR, 1);

    // LPIs on every core's redistributor: one configuration table, a
    // pending table each.
    for c in 0..ncpus {
        let r = crate::percpu::gicr(c);
        if r == 0 {
            return Err("a core has no redistributor");
        }
        let rt = rd64(r + GICR_TYPER);
        if rt & 1 == 0 {
            return Err("a redistributor has no LPIs");
        }
        if rd32(r + GICR_CTLR) & 1 != 0 {
            return Err("LPIs already enabled by the firmware");
        }
        wr64(r + GICR_PROPBASER, (mem + PROP_OFF) | CACHE_RAWAWB << 7 | SHARE_INNER << 10 | (LPI_ID_BITS - 1));
        wr64(r + GICR_PENDBASER, 1 << 62 | (mem + PEND_OFF + c as u64 * PAGE64K) | CACHE_RAWAWB << 7 | SHARE_INNER << 10);
        cpu::dsb_sy();
        wr32(r + GICR_CTLR, rd32(r + GICR_CTLR) | 1);
        s.rdbase[c] = if pta {
            match gicr_pa(c) {
                Some(p) => p >> 16,
                None => return Err("a redistributor's address is unknown"),
            }
        } else {
            (rt >> 8) & 0xffff
        };
    }
    cpu::dsb_sy();
    for c in 0..ncpus {
        // MAPC: collection c to core c.
        command([0x09, 0, BASER_VALID | s.rdbase[c] << 16 | c as u64, 0]);
        command([0x05, 0, s.rdbase[c] << 16, 0]);
    }
    if s.failed {
        return Err("the ITS does not take commands");
    }
    s.ready = true;
    Ok(Info {
        doorbell: pa + GITS_TRANSLATER,
        num_lpis: irq::NUM_LPIS,
        num_events: EVENTS,
        num_devices,
    })
}

/// Queue one command and wait until the ITS has done it.
fn command(cmd: [u64; 4]) {
    let s = its();
    if s.failed {
        return;
    }
    let slot = pptr(s.mem + CMD_OFF) + s.cwriter * 32;
    for (i, w) in cmd.iter().enumerate() {
        wr64(slot + i as u64 * 8, *w);
    }
    cpu::clean_dcache_poc(slot, 32);
    cpu::dsb_sy();
    s.cwriter = (s.cwriter + 1) % CMD_SLOTS;
    wr64(s.va + GITS_CWRITER, s.cwriter * 32);
    let mut n = 0u64;
    loop {
        let r = rd64(s.va + GITS_CREADR);
        if r & 1 != 0 || n > 100_000_000 {
            // Stalled on an error, or never done: no more commands.
            s.failed = true;
            s.ready = false;
            return;
        }
        if (r >> 5) & (CMD_SLOTS - 1) == s.cwriter {
            return;
        }
        n += 1;
        core::hint::spin_loop();
    }
}

fn set_prop(n: u64, v: u8) {
    let a = pptr(its().mem + PROP_OFF) + n;
    unsafe { core::ptr::write_volatile(a as *mut u8, v) };
    cpu::clean_dcache_poc(a, 1);
    cpu::dsb_sy();
}

/// Map event `event` of device `device` to LPI `irq` on core `core`
/// (`fl4_core::machine::msi` codes; nothing changes unless OK). `irq` has
/// no mapping (its handler does not exist).
pub fn map(irq_n: u64, device: u64, event: u64, core: u64) -> u64 {
    use fl4_core::machine::msi;
    let s = its();
    if !s.ready || !irq::is_lpi(irq_n) || irq_n > irq::MAX || core as usize >= s.rdbase.len() {
        return msi::NO_ITS;
    }
    if device >= s.num_devices {
        return msi::BAD_DEVICE;
    }
    if event >= EVENTS {
        return msi::BAD_EVENT;
    }
    let n = irq_n - irq::LPI_BASE;
    let slot = match s.devices.iter().position(|d| d.events != 0 && d.id == device) {
        Some(i) => {
            if s.devices[i].events & (1 << event) != 0 {
                return msi::BAD_EVENT;
            }
            i
        }
        None => {
            let Some(i) = s.devices.iter().position(|d| d.events == 0) else {
                return msi::NO_ITS;
            };
            // MAPD: the device's ITT.
            let itt = s.mem + ITT_OFF + i as u64 * s.itt_size;
            command([0x08 | device << 32, EVENT_BITS - 1, BASER_VALID | itt, 0]);
            s.devices[i].id = device;
            i
        }
    };
    set_prop(n, LPI_ENABLED);
    let intid = irq::LPI_ID_BASE + n;
    // MAPTI, then INV (the configuration just written), then SYNC.
    command([0x0a | device << 32, event | intid << 32, core, 0]);
    command([0x0c | device << 32, event, 0, 0]);
    command([0x05, 0, s.rdbase[core as usize] << 16, 0]);
    if s.failed {
        set_prop(n, 0);
        return msi::NO_ITS;
    }
    s.devices[slot].events |= 1 << event;
    s.lpis[n as usize] = (slot as u8 + 1, event as u8);
    msi::OK
}

/// Undo `map` for LPI `irq` (nothing if it has no mapping).
pub fn unmap(irq_n: u64) {
    let s = its();
    if !irq::is_lpi(irq_n) || irq_n > irq::MAX {
        return;
    }
    let n = (irq_n - irq::LPI_BASE) as usize;
    let (slot1, event) = s.lpis[n];
    if slot1 == 0 {
        return;
    }
    let slot = slot1 as usize - 1;
    let device = s.devices[slot].id;
    let event = event as u64;
    s.lpis[n] = (0, 0);
    set_prop(n as u64, 0);
    // DISCARD the event, and the device's ITT with its last event.
    command([0x0f | device << 32, event, 0, 0]);
    s.devices[slot].events &= !(1 << event);
    if s.devices[slot].events == 0 {
        command([0x08 | device << 32, 0, 0, 0]);
    }
    command([0x05, 0, s.rdbase[0] << 16, 0]);
}
