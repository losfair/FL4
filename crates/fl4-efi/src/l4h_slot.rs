//! Load and measure L4H's slot files from the chainloader's device.

use super::*;

const TCG2_PROTOCOL: Guid = Guid(
    0x607f766c,
    0x7455,
    0x42be,
    [0x93, 0x0b, 0xe4, 0xd7, 0x6d, 0xb2, 0x72, 0x0f],
);
const EFI_LOAD_ERROR: Status = (1 << 63) | 1;
const EFI_NOT_FOUND: Status = (1 << 63) | 14;
const EFI_VOLUME_FULL: Status = (1 << 63) | 11;

#[repr(C)]
struct Tcg2Protocol {
    get_capability: usize,
    get_event_log: usize,
    hash_log_extend_event:
        extern "efiapi" fn(*mut Tcg2Protocol, u64, u64, u64, *const Tcg2Event) -> Status,
}

#[repr(C, packed)]
struct Tcg2Event {
    size: u32,
    header_size: u32,
    header_version: u16,
    pcr_index: u32,
    event_type: u32,
    data: [u8; 16],
}

fn measure_slot(files: &[BootFile<'_>]) -> Result<(), Status> {
    let mut protocol = core::ptr::null_mut();
    let status = (bs().locate_protocol)(&TCG2_PROTOCOL, core::ptr::null(), &mut protocol);
    if status == EFI_NOT_FOUND {
        say!("fl4-efi: TPM measurement protocol unavailable");
        return Ok(());
    }
    if status != SUCCESS {
        return Err(status);
    }
    let protocol = protocol.cast::<Tcg2Protocol>();
    for &(pa, len, name) in files {
        let mut event = Tcg2Event {
            size: core::mem::size_of::<Tcg2Event>() as u32,
            header_size: 14,
            header_version: 1,
            pcr_index: 9,
            event_type: 0x0d, // EV_IPL
            data: [0; 16],
        };
        event.data[..name.len()].copy_from_slice(name);
        let status = unsafe { ((*protocol).hash_log_extend_event)(protocol, 0, pa, len, &event) };
        // A full event log still extends the PCR.
        if status != SUCCESS && status != EFI_VOLUME_FULL {
            return Err(status);
        }
    }
    Ok(())
}

pub(super) fn boot_files(li: &LoadedImage) -> Result<([BootFile<'static>; 4], usize), Status> {
    // The firmware measures the embedded root task and guest kernel in PCR 4.
    if li.options_size != 0 {
        say!("fl4-efi: measured L4H slot loader rejects load options");
        return Err(EFI_LOAD_ERROR);
    }
    if embedded::ROOTSERVER.is_empty() || embedded::MODULE.is_empty() {
        say!("fl4-efi: measured L4H slot needs an embedded root task and guest kernel");
        return Err(EFI_LOAD_ERROR);
    }
    let mut files: [BootFile<'static>; 4] = [
        (
            embedded::ROOTSERVER.as_ptr() as u64,
            embedded::ROOTSERVER.len() as u64,
            b"rootserver",
        ),
        (
            embedded::MODULE.as_ptr() as u64,
            embedded::MODULE.len() as u64,
            b"guest-kernel",
        ),
        (0, 0, b"l4h-config"),
        (0, 0, b"dom0-initrd"),
    ];
    let slot = &mut files[2..];
    let result = (|| {
        for (file, path) in slot
            .iter_mut()
            .zip([&b"/l4h/l4h.conf"[..], &b"/l4h/dom0/initrd"[..]])
        {
            match try_read_file(li, path) {
                Ok((pa, len)) => {
                    file.0 = pa;
                    file.1 = len;
                    if len != 0 {
                        continue;
                    }
                    say!(
                        "fl4-efi: empty slot file {}",
                        core::str::from_utf8(path).unwrap()
                    );
                }
                Err(reason) => {
                    say!(
                        "fl4-efi: cannot load slot file {} ({})",
                        core::str::from_utf8(path).unwrap(),
                        reason
                    );
                }
            }
            return Err(EFI_LOAD_ERROR);
        }
        measure_slot(slot).map_err(|status| {
            say!("fl4-efi: slot TPM measurement failed ({:#x})", status);
            EFI_LOAD_ERROR
        })
    })();
    if result.is_err() {
        for &(pa, len, _) in slot.iter() {
            if pa != 0 {
                (bs().free_pages)(pa, len.div_ceil(PAGE).max(1) as usize);
            }
        }
    }
    result.map(|()| (files, files.len()))
}
