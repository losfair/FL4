//! Exercise the kernel's actual ACPI parser with host-allocated firmware tables.
//! Only the physical-to-virtual address translation is replaced for this test.
extern crate self as fl4_core;

pub mod layout {
    pub fn pptr(p: u64) -> u64 {
        p
    }
}

#[path = "../../crates/fl4-kernel/src/acpi.rs"]
mod acpi;

fn checksum(table: &mut [u8], offset: usize) {
    table[offset] = 0;
    table[offset] = table.iter().fold(0u8, |sum, byte| sum.wrapping_add(*byte)).wrapping_neg();
}

fn parse(entries: &[u8]) -> acpi::Info {
    let mut madt = vec![0; 44];
    madt.extend_from_slice(entries);
    let len = madt.len() as u32;
    madt[..4].copy_from_slice(b"APIC");
    madt[4..8].copy_from_slice(&len.to_le_bytes());
    madt[8] = 6;
    checksum(&mut madt, 9);

    let mut xsdt = [0u8; 44];
    xsdt[..4].copy_from_slice(b"XSDT");
    xsdt[4..8].copy_from_slice(&44u32.to_le_bytes());
    xsdt[8] = 1;
    xsdt[36..44].copy_from_slice(&(madt.as_ptr() as u64).to_le_bytes());
    checksum(&mut xsdt, 9);

    let mut rsdp = [0u8; 36];
    rsdp[..8].copy_from_slice(b"RSD PTR ");
    rsdp[15] = 2;
    rsdp[20..24].copy_from_slice(&36u32.to_le_bytes());
    rsdp[24..32].copy_from_slice(&(xsdt.as_ptr() as u64).to_le_bytes());
    checksum(&mut rsdp[..20], 8);
    checksum(&mut rsdp, 32);

    acpi::init(Some(rsdp.as_ptr() as u64)).expect("valid RSDP")
}

fn lapic(id: u8, flags: u32) -> [u8; 8] {
    let mut entry = [0u8; 8];
    entry[1] = 8;
    entry[2] = id;
    entry[3] = id;
    entry[4..8].copy_from_slice(&flags.to_le_bytes());
    entry
}

fn x2apic(id: u32, flags: u32) -> [u8; 16] {
    let mut entry = [0u8; 16];
    entry[0] = 9;
    entry[1] = 16;
    entry[4..8].copy_from_slice(&id.to_le_bytes());
    entry[8..12].copy_from_slice(&flags.to_le_bytes());
    entry[12..16].copy_from_slice(&id.to_le_bytes());
    entry
}

#[test]
fn only_enabled_lapic_and_x2apic_entries_are_boot_cpus() {
    let mut entries = Vec::new();
    // Unusable, online-capable only, enabled, and enabled with a reserved bit.
    for flags in [0, 2, 1, 3] {
        entries.extend_from_slice(&lapic(flags as u8, flags));
        entries.extend_from_slice(&x2apic(0x100 + flags, flags));
    }
    let mut ioapic = [1, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    ioapic[4..8].copy_from_slice(&0xfec0_0000u32.to_le_bytes());
    entries.extend_from_slice(&ioapic);

    let info = parse(&entries);
    assert_eq!(&info.cpus[..info.n_cpus], &[1, 0x101, 3, 0x103]);
    assert_eq!(&info.ioapics[..info.n_ioapics], &[0xfec0_0000]);
}

#[test]
fn hotplug_slots_do_not_consume_boot_cpu_capacity() {
    let mut entries = Vec::new();
    for id in 0..acpi::MAX_CPUS as u32 {
        entries.extend_from_slice(&lapic(id as u8, 2));
        entries.extend_from_slice(&x2apic(0x100 + id, 2));
    }
    entries.extend_from_slice(&lapic(0x80, 1));
    entries.extend_from_slice(&x2apic(0x180, 1));

    let info = parse(&entries);
    assert_eq!(&info.cpus[..info.n_cpus], &[0x80, 0x180]);
}
