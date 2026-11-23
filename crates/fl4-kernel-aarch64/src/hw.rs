//! Finding the hardware (DESIGN.md §3): the GIC, the cores, the console
//! UART, the PSCI conduit and the timer, from the ACPI tables (MADT, GTDT,
//! SPCR, FADT) when UEFI passed them, otherwise from the device tree. The
//! tables are read through the kernel window: only those it maps, and
//! only inside the lengths they give (a table the window does not reach
//! is skipped, as is a malformed one, rather than faulting at boot).
use fl4_arch_aarch64::{mmu, serial, smp};
use fl4_core::layout::pptr;

pub const MAX_CPUS: usize = 64;
/// Redistributor ranges: one per core when the MADT's GICC entries give
/// them (and the kernel reserves every one of them, started or not).
pub const MAX_GICR: usize = MAX_CPUS;
pub const RSDP_LEN: usize = 36;

pub struct Hw {
    pub source: &'static str,
    pub gic_version: u64,
    pub gicd: u64,
    /// GICv2 CPU interface.
    pub gicc: u64,
    /// Its size where the tables give one (0: they do not).
    pub gicc_len: u64,
    /// GICv3 redistributor ranges (base, length; length 0: until the
    /// frame marked last).
    pub gicr: [(u64, u64); MAX_GICR],
    pub n_gicr: usize,
    /// The tables gave more redistributor ranges than `gicr` holds: the
    /// rest would be user space's device memory, so the boot fails.
    pub gicr_lost: bool,
    /// Enabled cores' MPIDR affinities, the boot core first.
    pub cpus: [u64; MAX_CPUS],
    pub n_cpus: usize,
    pub uart_kind: u64,
    pub uart_base: u64,
    pub uart_shift: u64,
    pub uart_wide: bool,
    pub psci: u64,
    /// The EL1 virtual timer's interrupt ID (0 if not described).
    pub vtimer: u64,
    /// The EL1 non-secure physical timer's interrupt ID (0 if not described).
    pub ptimer: u64,
    /// The EL2 physical timer's interrupt ID (0 if not described).
    pub hyptimer: u64,
    /// The VGIC maintenance interrupt ID (0 if not described).
    pub vgic_maint: u64,
    /// GICv2 hypervisor control interface (GICH).
    pub gich: u64,
    pub gich_len: u64,
    /// The first GICv3 ITS (0: none), which the kernel drives for MSIs.
    pub its: u64,
    /// GICv2 virtual CPU interface (GICV).
    pub gicv: u64,
    pub gicv_len: u64,
    pub rsdp: [u8; RSDP_LEN],
    pub has_rsdp: bool,
}

impl Hw {
    const fn new() -> Hw {
        Hw {
            source: "nothing",
            gic_version: 0,
            gicd: 0,
            gicc: 0,
            gicc_len: 0,
            gicr: [(0, 0); MAX_GICR],
            n_gicr: 0,
            gicr_lost: false,
            cpus: [0; MAX_CPUS],
            n_cpus: 0,
            uart_kind: serial::KIND_NONE,
            uart_base: 0,
            uart_shift: 0,
            uart_wide: false,
            psci: smp::PSCI_NONE,
            vtimer: 0,
            ptimer: 0,
            hyptimer: 0,
            vgic_maint: 0,
            gich: 0,
            gich_len: 0,
            its: 0,
            gicv: 0,
            gicv_len: 0,
            rsdp: [0; RSDP_LEN],
            has_rsdp: false,
        }
    }

    /// Note a redistributor range, merged with the overlapping ones
    /// already noted (`gic_layout::add_redistributors`).
    fn add_gicr(&mut self, base: u64, len: u64) {
        if !fl4_arch_aarch64::gic_layout::add_redistributors(&mut self.gicr, &mut self.n_gicr, base, len) {
            self.gicr_lost = true;
        }
    }

    /// Add a core; the boot core always ends up first.
    fn add_cpu(&mut self, mpidr: u64) {
        if self.cpus[..self.n_cpus].contains(&mpidr) || self.n_cpus == MAX_CPUS {
            return;
        }
        self.cpus[self.n_cpus] = mpidr;
        self.n_cpus += 1;
        let me = fl4_arch_aarch64::cpu::mpidr();
        if let Some(i) = self.cpus[..self.n_cpus].iter().position(|&c| c == me) {
            self.cpus.swap(0, i);
        }
    }
}

fn rd8(p: u64) -> u8 {
    unsafe { core::ptr::read_volatile(pptr(p) as *const u8) }
}

fn rd16(p: u64) -> u16 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u16) }
}

fn rd32(p: u64) -> u32 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u32) }
}

fn rd64(p: u64) -> u64 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u64) }
}

fn be32(p: u64) -> u32 {
    u32::from_be(rd32(p))
}

/// `len` bytes at physical `p` can be read through the window.
fn mapped(p: u64, len: u64) -> bool {
    mmu::in_window(p, len)
}

fn checksum(p: u64, len: u64) -> bool {
    let mut s: u8 = 0;
    for i in 0..len {
        s = s.wrapping_add(rd8(p + i));
    }
    s == 0
}

// ---- ACPI ------------------------------------------------------------------

/// A table's header (36 bytes) and then all of it is in the window.
fn table_len(t: u64) -> Option<u64> {
    if !mapped(t, 36) {
        return None;
    }
    let len = rd32(t + 4) as u64;
    (len >= 36 && mapped(t, len)).then_some(len)
}

/// The RSDP at `p`: its signature and ACPI 1.0 checksum (20 bytes) hold.
/// Then whether it has ACPI 2.0 fields (fl4-kernel acpi.rs): revision 2 or
/// later, a length that covers them and the extended checksum over it.
fn rsdp(p: u64) -> Option<bool> {
    if !mapped(p, 20) || rd64(p) != u64::from_le_bytes(*b"RSD PTR ") || !checksum(p, 20) {
        return None;
    }
    if rd8(p + 15) < 2 || !mapped(p, RSDP_LEN as u64) {
        return Some(false);
    }
    let len = rd32(p + 20) as u64;
    Some((RSDP_LEN as u64..=4096).contains(&len) && mapped(p, len) && checksum(p, len))
}

fn acpi_tables(rsdp_p: u64, mut f: impl FnMut(&[u8; 4], u64, u64)) -> bool {
    let Some(v2) = rsdp(rsdp_p) else { return false };
    let (root, entry, sig) = if v2 && rd64(rsdp_p + 24) != 0 {
        (rd64(rsdp_p + 24), 8, *b"XSDT")
    } else {
        (rd32(rsdp_p + 16) as u64, 4, *b"RSDT")
    };
    let len = match table_len(root) {
        Some(l) if rd32(root).to_le_bytes() == sig => l,
        _ => return false,
    };
    let mut off = 36;
    while off + entry <= len {
        let t = if entry == 8 { rd64(root + off) } else { rd32(root + off) as u64 };
        if let Some(tl) = table_len(t) {
            let sig = rd32(t).to_le_bytes();
            f(&sig, t, tl);
        }
        off += entry;
    }
    true
}

fn parse_acpi(rsdp_p: u64, hw: &mut Hw) -> bool {
    let mut madt = false;
    let ok = acpi_tables(rsdp_p, |sig, t, len| match sig {
        b"APIC" => {
            madt = true;
            // GICR discovery ranges first: the GICC entries' redistributors
            // inside one then merge into it whatever the tables' order,
            // rather than fill `gicr` one core at a time before it comes.
            for gicr_pass in [true, false] {
                let mut off = 44;
                while off + 2 <= len {
                    let ty = rd8(t + off);
                    let l = rd8(t + off + 1) as u64;
                    if l < 2 || off + l > len {
                        break;
                    }
                    let e = t + off;
                    if (ty == 0x0e) != gicr_pass {
                        off += l;
                        continue;
                    }
                    match ty {
                        // GICC: enabled cores (flags bit 0), their MPIDR, the
                        // GICv2 CPU interface or a GICv3 redistributor.
                        0x0b if l >= 76 => {
                            if rd32(e + 12) & 1 != 0 {
                                hw.add_cpu(rd64(e + 68) & 0xff_00ff_ffff);
                            }
                            if hw.gicc == 0 {
                                hw.gicc = rd64(e + 32);
                            }
                            if hw.gicv == 0 {
                                hw.gicv = rd64(e + 40);
                            }
                            if hw.gich == 0 {
                                hw.gich = rd64(e + 48);
                            }
                            if hw.vgic_maint == 0 {
                                hw.vgic_maint = rd32(e + 56) as u64;
                            }
                            // A core's RD and SGI frames; GICv4 VLPI frames
                            // after them are found at boot (`gic::redistributor_span`).
                            let r = rd64(e + 60);
                            if r != 0 {
                                hw.add_gicr(r, fl4_arch_aarch64::gic_layout::GICR_FRAME);
                            }
                        }
                        0x0c if l >= 21 => {
                            hw.gicd = rd64(e + 8);
                            hw.gic_version = rd8(e + 20) as u64;
                        }
                        0x0e if l >= 16 => hw.add_gicr(rd64(e + 4), rd32(e + 12) as u64),
                        // GIC ITS: its base.
                        0x0f if l >= 16 => {
                            if hw.its == 0 {
                                hw.its = rd64(e + 8);
                            }
                        }
                        _ => {}
                    }
                    off += l;
                }
            }
        }
        b"GTDT" if len >= 72 => {
            hw.ptimer = rd32(t + 48) as u64;
            hw.vtimer = rd32(t + 64) as u64;
            if len >= 76 {
                hw.hyptimer = rd32(t + 72) as u64;
            }
        }
        b"SPCR" if len >= 52 => {
            let ty = rd8(t + 36);
            let space = rd8(t + 40);
            let width = rd8(t + 41);
            let access = rd8(t + 43);
            let addr = rd64(t + 44);
            if space == 0 && addr != 0 {
                match ty {
                    // PL011, SBSA 32-bit generic UART, SBSA (2.x).
                    0x03 | 0x0d | 0x0e => {
                        hw.uart_kind = serial::KIND_PL011;
                        hw.uart_base = addr;
                    }
                    // 16550 and compatible.
                    0x00 | 0x01 | 0x12 => {
                        hw.uart_kind = serial::KIND_16550;
                        hw.uart_base = addr;
                        let wide = access == 3 || width == 32;
                        hw.uart_wide = wide;
                        hw.uart_shift = if wide { 2 } else { 0 };
                    }
                    _ => {}
                }
            }
        }
        b"FACP" if len >= 131 => {
            let flags = rd16(t + 129);
            if flags & 1 != 0 {
                hw.psci = if flags & 2 != 0 { smp::PSCI_HVC } else { smp::PSCI_SMC };
            }
        }
        _ => {}
    });
    if !ok || !madt {
        return false;
    }
    if hw.gic_version == 0 {
        // ACPI 5.1 MADTs leave the version 0: a redistributor means v3.
        hw.gic_version = if hw.n_gicr > 0 { 3 } else { 2 };
    }
    if hw.gic_version >= 3 {
        hw.gic_version = 3;
    }
    // As much of the RSDP as its revision has (fl4-kernel acpi.rs).
    let n = if rsdp(rsdp_p) == Some(true) { RSDP_LEN } else { 20 };
    for i in 0..n {
        hw.rsdp[i] = rd8(rsdp_p + i as u64);
    }
    hw.has_rsdp = true;
    hw.source = "ACPI";
    true
}

// ---- device tree -------------------------------------------------------------

const FDT_BEGIN_NODE: u32 = 1;
const FDT_END_NODE: u32 = 2;
const FDT_PROP: u32 = 3;
const FDT_NOP: u32 = 4;
const FDT_END: u32 = 9;
const MAX_DEPTH: usize = 16;

/// A property: its node's path depth and name, the property's name and
/// value (physical address and length), and the `#address-cells` and
/// `#size-cells` of the node's parent, in which its `reg` is written.
struct Prop {
    depth: usize,
    node: &'static [u8],
    parent: &'static [u8],
    name: &'static [u8],
    val: u64,
    len: u64,
    ac: u64,
    sc: u64,
}

/// What a node's children have when it says nothing (Devicetree
/// Specification §2.3.5: not inherited from further up).
const DEFAULT_CELLS: (u64, u64) = (2, 1);

/// A NUL-terminated string at physical `p` (at most 256 bytes, and none
/// at or after `end`) as a slice through the window.
fn cstr(p: u64, end: u64) -> &'static [u8] {
    let mut n = 0;
    while n < 256 && p + n < end && rd8(p + n) != 0 {
        n += 1;
    }
    unsafe { core::slice::from_raw_parts(pptr(p) as *const u8, n as usize) }
}

/// The value of property `p` as a string.
fn prop_str(p: &Prop) -> &'static [u8] {
    cstr(p.val, p.val + p.len)
}

/// The blob at `dtb`, if the window holds all of it and its header is
/// sound (`fl4_bootinfo::fdt_header`).
fn fdt(dtb: u64) -> Option<fl4_bootinfo::Fdt> {
    if !mapped(dtb, 40) {
        return None;
    }
    let mut h = [0u8; 40];
    for (i, b) in h.iter_mut().enumerate() {
        *b = rd8(dtb + i as u64);
    }
    let f = fl4_bootinfo::fdt_header(&h)?;
    mapped(dtb, f.total).then_some(f)
}

/// Walk every property of the blob at `dtb`.
fn fdt_walk(dtb: u64, mut f: impl FnMut(&Prop)) -> bool {
    let h = match fdt(dtb) {
        Some(h) => h,
        None => return false,
    };
    let mut p = dtb + h.structs.0;
    let end = dtb + h.structs.1;
    let (strings, strings_end) = (dtb + h.strings.0, dtb + h.strings.1);
    let mut stack: [&'static [u8]; MAX_DEPTH] = [&[]; MAX_DEPTH];
    // Per open node: the cells its children's reg uses. A node's
    // properties all come before its children.
    let mut cells: [(u64, u64); MAX_DEPTH] = [DEFAULT_CELLS; MAX_DEPTH];
    let mut depth = 0usize;
    while p + 4 <= end {
        let tok = be32(p);
        p += 4;
        match tok {
            FDT_BEGIN_NODE => {
                let name = cstr(p, end);
                p = (p + name.len() as u64 + 1 + 3) & !3;
                if depth < MAX_DEPTH {
                    stack[depth] = name;
                    cells[depth] = DEFAULT_CELLS;
                }
                depth += 1;
            }
            FDT_END_NODE => {
                depth = depth.saturating_sub(1);
            }
            FDT_PROP => {
                if p + 8 > end {
                    return false;
                }
                let len = be32(p) as u64;
                let nameoff = be32(p + 4) as u64;
                let val = p + 8;
                if len > end - val || nameoff >= strings_end - strings {
                    return false;
                }
                p = (val + len + 3) & !3;
                if depth > 0 && depth <= MAX_DEPTH {
                    let node = stack[depth - 1];
                    let parent = if depth >= 2 { stack[depth - 2] } else { &[] };
                    let name = cstr(strings + nameoff, strings_end);
                    if len >= 4 && name == b"#address-cells" {
                        cells[depth - 1].0 = be32(val) as u64;
                    }
                    if len >= 4 && name == b"#size-cells" {
                        cells[depth - 1].1 = be32(val) as u64;
                    }
                    let (ac, sc) = if depth >= 2 { cells[depth - 2] } else { DEFAULT_CELLS };
                    f(&Prop { depth, node, parent, name, val, len, ac, sc });
                }
            }
            FDT_NOP => {}
            FDT_END => return true,
            _ => return false,
        }
    }
    true
}

fn has_compat(p: &Prop, want: &[u8]) -> bool {
    if p.name != b"compatible" {
        return false;
    }
    let mut i = 0;
    while i < p.len {
        let s = cstr(p.val + i, p.val + p.len);
        if s == want {
            return true;
        }
        i += s.len() as u64 + 1;
    }
    false
}

fn cells(p: u64, n: u64) -> u64 {
    if n == 2 {
        ((be32(p) as u64) << 32) | be32(p + 4) as u64
    } else {
        be32(p) as u64
    }
}

/// `reg` entries a node keeps: a GICv3's distributor and as many
/// redistributor regions as `Hw::gicr` holds.
const NODE_REGS: usize = 1 + MAX_GICR;

/// What a device tree node said about itself.
#[derive(Clone, Copy)]
struct Node {
    kind: u8,
    reg: [(u64, u64); NODE_REGS],
    n_reg: usize,
    /// The reg property could not be read whole: cells the kernel does
    /// not handle, or a length that is not a whole number of entries.
    reg_bad: bool,
    /// GICv3 `#redistributor-regions` (the binding's default is 1).
    redist_regions: u64,
    /// VGIC maintenance interrupt PPI from the GIC node's `interrupts`.
    vgic_maint: u64,
}

impl Node {
    const EMPTY: Node = Node {
        kind: 0,
        reg: [(0, 0); NODE_REGS],
        n_reg: 0,
        reg_bad: false,
        redist_regions: 1,
        vgic_maint: 0,
    };
}

const N_GICV3: u8 = 1;
const N_GICV2: u8 = 2;
const N_PL011: u8 = 3;
const N_16550: u8 = 4;
const N_ITS: u8 = 5;

fn parse_dt(dtb: u64, hw: &mut Hw) -> bool {
    // The console and PSCI, then a pass per node: compatible strings come
    // before or after reg, so each node's facts are gathered and used at
    // its end.
    let mut stdout: &'static [u8] = &[];
    let mut psci_method: &'static [u8] = &[];
    let ok = fdt_walk(dtb, |p| {
        if p.node == b"chosen" && p.name == b"stdout-path" {
            stdout = prop_str(p);
        }
        if p.node.starts_with(b"psci") && p.name == b"method" {
            psci_method = prop_str(p);
        }
    });
    if !ok {
        return false;
    }
    hw.psci = match psci_method {
        b"hvc" => smp::PSCI_HVC,
        b"smc" => smp::PSCI_SMC,
        _ => smp::PSCI_NONE,
    };
    // stdout-path names a node (possibly with ":options").
    let stdout_node: &[u8] = {
        let s = stdout.split(|&c| c == b':').next().unwrap_or(&[]);
        s.rsplit(|&c| c == b'/').next().unwrap_or(&[])
    };
    let mut cur = Node::EMPTY;
    let mut cur_name: &'static [u8] = &[];
    let mut uart_any: Option<(u8, u64)> = None;
    let mut uart_stdout: Option<(u8, u64)> = None;
    let flush = |hw: &mut Hw, name: &[u8], n: &Node, uart_any: &mut Option<(u8, u64)>, uart_stdout: &mut Option<(u8, u64)>| {
        if n.n_reg == 0 {
            return;
        }
        match n.kind {
            N_GICV3 => {
                hw.gic_version = 3;
                hw.gicd = n.reg[0].0;
                // Then `#redistributor-regions` redistributor regions;
                // GICC, GICH and GICV may follow, which are not regions.
                // A count that `gicr` cannot hold, that the reg property
                // does not have, or of none, leaves regions unknown: the
                // boot fails rather than give them to user space.
                hw.n_gicr = 0;
                hw.gicr_lost = false;
                let want = n.redist_regions;
                let have = (n.n_reg - 1) as u64;
                if n.reg_bad || want == 0 || want > MAX_GICR as u64 || want > have {
                    hw.gicr_lost = true;
                }
                for &r in &n.reg[1..1 + want.min(have) as usize] {
                    hw.add_gicr(r.0, r.1);
                }
                if n.vgic_maint != 0 {
                    hw.vgic_maint = n.vgic_maint;
                }
            }
            N_GICV2 => {
                hw.gic_version = 2;
                hw.gicd = n.reg[0].0;
                if n.n_reg > 1 {
                    hw.gicc = n.reg[1].0;
                    hw.gicc_len = n.reg[1].1;
                }
                if n.n_reg > 2 {
                    hw.gich = n.reg[2].0;
                    hw.gich_len = n.reg[2].1;
                }
                if n.n_reg > 3 {
                    hw.gicv = n.reg[3].0;
                    hw.gicv_len = n.reg[3].1;
                }
                if n.vgic_maint != 0 {
                    hw.vgic_maint = n.vgic_maint;
                }
            }
            N_ITS => {
                if hw.its == 0 {
                    hw.its = n.reg[0].0;
                }
            }
            N_PL011 | N_16550 => {
                let u = (n.kind, n.reg[0].0);
                if uart_any.is_none() {
                    *uart_any = Some(u);
                }
                if !name.is_empty() && name == stdout_node {
                    *uart_stdout = Some(u);
                }
            }
            _ => {}
        }
    };
    fdt_walk(dtb, |p| {
        if p.node.as_ptr() != cur_name.as_ptr() {
            flush(hw, cur_name, &cur, &mut uart_any, &mut uart_stdout);
            cur = Node::EMPTY;
            cur_name = p.node;
        }
        if has_compat(p, b"arm,gic-v3-its") {
            cur.kind = N_ITS;
        } else if has_compat(p, b"arm,gic-v3") {
            cur.kind = N_GICV3;
        } else if has_compat(p, b"arm,cortex-a15-gic") || has_compat(p, b"arm,gic-400") || has_compat(p, b"arm,cortex-a9-gic") {
            cur.kind = N_GICV2;
        } else if has_compat(p, b"arm,pl011") || has_compat(p, b"arm,sbsa-uart") {
            cur.kind = N_PL011;
        } else if has_compat(p, b"ns16550a") || has_compat(p, b"ns16550") || has_compat(p, b"snps,dw-apb-uart") {
            cur.kind = N_16550;
        }
        if p.name == b"reg" && p.depth >= 2 {
            if p.parent == b"cpus" {
                // A core's reg is its MPIDR affinity (#address-cells of
                // /cpus, 1 or 2).
                if p.node.starts_with(b"cpu@") && (1..=2).contains(&p.ac) && p.len >= p.ac * 4 {
                    hw.add_cpu(cells(p.val, p.ac) & 0xff_00ff_ffff);
                }
            } else if !(1..=2).contains(&p.ac) || !(1..=2).contains(&p.sc) || p.len % ((p.ac + p.sc) * 4) != 0 {
                cur.reg_bad = true;
            } else {
                let step = (p.ac + p.sc) * 4;
                let mut i = 0;
                while (i + 1) * step <= p.len && cur.n_reg < NODE_REGS {
                    let a = p.val + i * step;
                    cur.reg[cur.n_reg] = (cells(a, p.ac), cells(a + p.ac * 4, p.sc));
                    cur.n_reg += 1;
                    i += 1;
                }
            }
        }
        if p.name == b"#redistributor-regions" && p.len >= 4 {
            cur.redist_regions = be32(p.val) as u64;
        }
        if p.name == b"interrupts" && p.len >= 12 * 3 && p.node == b"timer" {
            // (type, number, flags) for the secure, non-secure, virtual
            // and hypervisor timers; PPIs number from 16.
            hw.ptimer = be32(p.val + 12 + 4) as u64 + 16;
            hw.vtimer = be32(p.val + 24 + 4) as u64 + 16;
            if p.len >= 12 * 4 {
                hw.hyptimer = be32(p.val + 36 + 4) as u64 + 16;
            }
        } else if p.name == b"interrupts" && p.len >= 12 && be32(p.val) == 1 {
            cur.vgic_maint = be32(p.val + 4) as u64 + 16;
        }
    });
    flush(hw, cur_name, &cur, &mut uart_any, &mut uart_stdout);
    if let Some((k, a)) = uart_stdout.or(uart_any) {
        hw.uart_kind = if k == N_PL011 { serial::KIND_PL011 } else { serial::KIND_16550 };
        hw.uart_base = a;
        if k == N_16550 {
            hw.uart_shift = 2;
            hw.uart_wide = true;
        }
    }
    hw.source = "device tree";
    hw.gic_version != 0
}

/// The hardware, from ACPI if `rsdp` is nonzero and usable, otherwise
/// from the device tree at `dtb`.
pub fn discover(rsdp: u64, dtb: u64) -> Option<Hw> {
    let mut hw = Hw::new();
    if rsdp != 0 && parse_acpi(rsdp, &mut hw) {
        return Some(hw);
    }
    let mut hw = Hw::new();
    if dtb != 0 && parse_dt(dtb, &mut hw) {
        return Some(hw);
    }
    None
}

/// The device tree blob's size: up to the end of its last block, which
/// can be far less than the header's total size (QEMU pads its blob to
/// 1 MiB, more than sel4test's heap holds for a copy).
pub fn dtb_size(dtb: u64) -> u64 {
    let h = match fdt(dtb) {
        Some(h) => h,
        None => return 0,
    };
    let total = h.total;
    let structs = h.structs.1;
    let strings = h.strings.1;
    // The memory reservation block ends with an all-zero entry.
    let mut rsv = h.rsv;
    while rsv + 16 <= total && (be32(dtb + rsv) | be32(dtb + rsv + 4) | be32(dtb + rsv + 8) | be32(dtb + rsv + 12)) != 0 {
        rsv += 16;
    }
    let used = structs.max(strings).max(rsv + 16).max(40);
    ((used + 7) & !7).min(total)
}
