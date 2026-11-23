//! The extra BootInfo's records (a chain of `seL4_BootInfoHeader`s), from
//! what boot found. No kernel dependencies, so the host tests include this
//! file too (xtask/tests/aarch64_boot.rs).
use fl4_abi::consts::bootinfo_header as id;
use fl4_bootinfo::Module;

fn put(buf: &mut [u8], off: &mut usize, b: &[u8]) -> Option<()> {
    let end = off.checked_add(b.len())?;
    buf.get_mut(*off..end)?.copy_from_slice(b);
    *off = end;
    Some(())
}

fn hdr(buf: &mut [u8], off: &mut usize, id: u64, len: u64) -> Option<()> {
    put(buf, off, &id.to_le_bytes())?;
    put(buf, off, &len.to_le_bytes())
}

/// `VirtInfo::flags` bit definitions.
#[allow(dead_code)]
pub const VIRT_READY: u64 = 1 << 0;
#[allow(dead_code)]
pub const EL2_VHE: u64 = 1 << 1;
#[allow(dead_code)]
pub const VMID16: u64 = 1 << 2;
#[allow(dead_code)]
pub const EL2_NVHE: u64 = 1 << 3;

/// AArch64 EL2/VHE virtualization capabilities and GIC/ID metadata
/// (`bootinfo_header::AARCH64_VIRT_INFO`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VirtInfo {
    /// bit 0 = virt_ready, bit 1 = el2_vhe, bit 2 = vmid16, bit 3 = el2_nvhe.
    pub flags: u64,
    pub ipa_bits: u64,
    pub gic_version: u64,
    pub vgic_vtr: u64,
    pub gicv_paddr: u64,
    pub gicv_size: u64,
    pub midr_el1: u64,
    pub ctr_el0: u64,
    pub id_aa64mmfr0_el1: u64,
    pub id_aa64mmfr1_el1: u64,
    pub id_aa64mmfr2_el1: u64,
    pub id_aa64dfr0_el1: u64,
    pub id_aa64dfr1_el1: u64,
}

impl VirtInfo {
    pub fn to_words(&self) -> [u64; 13] {
        [
            self.flags,
            self.ipa_bits,
            self.gic_version,
            self.vgic_vtr,
            self.gicv_paddr,
            self.gicv_size,
            self.midr_el1,
            self.ctr_el0,
            self.id_aa64mmfr0_el1,
            self.id_aa64mmfr1_el1,
            self.id_aa64mmfr2_el1,
            self.id_aa64dfr0_el1,
            self.id_aa64dfr1_el1,
        ]
    }
}

/// The UEFI TPM event log (`bootinfo_header::TPM_EVENT_LOG`,
/// seL4_TpmEventLog).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TpmEventLog {
    pub paddr: u64,
    pub size: u64,
    pub flags: u64,
}

/// Write the records into `buf`: the ACPI RSDP, the boot core's ID
/// registers (l4h 0018), optional virtualization info, the boot modules
/// (l4h 0021), the TPM event log, the ITS's MSI facts and the device tree. Returns their length, a multiple of 8
/// (a padding record ends the chain if needed, as on x86_64); none if
/// `buf` is too small.
///
/// All of `buf` is cleared first: it is free RAM with whatever the
/// firmware left there, and the root task gets every byte up to the
/// length rounded up to 8, the device tree record's padding included.
/// Each record is exactly as long as its header says.
pub fn build(
    buf: &mut [u8],
    rsdp: Option<&[u8]>,
    id_regs: &[u64; 5],
    virt_info: Option<&VirtInfo>,
    mods: &[Module],
    tpm_log: Option<&TpmEventLog>,
    msi: Option<&[u64; 4]>,
    dtb: &[u8],
) -> Option<usize> {
    buf.fill(0);
    let mut off = 0;
    if let Some(rsdp) = rsdp {
        hdr(buf, &mut off, id::X86_ACPI_RSDP, 16 + rsdp.len() as u64)?;
        put(buf, &mut off, rsdp)?;
    }
    hdr(buf, &mut off, id::AARCH64_ID_REGS, 16 + 8 * id_regs.len() as u64)?;
    for r in id_regs {
        put(buf, &mut off, &r.to_le_bytes())?;
    }
    if let Some(vi) = virt_info {
        let words = vi.to_words();
        hdr(buf, &mut off, id::AARCH64_VIRT_INFO, 16 + 8 * words.len() as u64)?;
        for w in words {
            put(buf, &mut off, &w.to_le_bytes())?;
        }
    }
    if !mods.is_empty() {
        hdr(buf, &mut off, id::X86_BOOT_MODULES, 16 + 8 + 80 * mods.len() as u64)?;
        put(buf, &mut off, &(mods.len() as u64).to_le_bytes())?;
        for m in mods {
            put(buf, &mut off, &m.paddr.to_le_bytes())?;
            put(buf, &mut off, &m.size.to_le_bytes())?;
            put(buf, &mut off, &m.name)?;
        }
    }
    if let Some(t) = tpm_log {
        hdr(buf, &mut off, id::TPM_EVENT_LOG, 16 + 24)?;
        for w in [t.paddr, t.size, t.flags] {
            put(buf, &mut off, &w.to_le_bytes())?;
        }
    }
    // seL4_AArch64MsiInfo: doorbell, num_lpis, num_events, num_devices.
    if let Some(m) = msi {
        hdr(buf, &mut off, id::AARCH64_MSI_INFO, 16 + 32)?;
        for w in m {
            put(buf, &mut off, &w.to_le_bytes())?;
        }
    }
    if !dtb.is_empty() {
        let len = dtb.len().checked_add(7)? & !7;
        hdr(buf, &mut off, id::FDT, 16 + len as u64)?;
        let at = off;
        let end = at.checked_add(len)?;
        buf.get(at..end)?;
        put(buf, &mut off, dtb)?;
        // The copy's total size is what was copied.
        if dtb.len() >= 8 {
            buf[at + 4..at + 8].copy_from_slice(&(dtb.len() as u32).to_be_bytes());
        }
        // The next record starts where this one's header says it ends.
        off = end;
    }
    if off % 8 != 0 {
        let pad = 8 - off % 8;
        hdr(buf, &mut off, id::PADDING, (16 + pad) as u64)?;
        put(buf, &mut off, &[0u8; 8][..pad])?;
    }
    Some(off)
}
