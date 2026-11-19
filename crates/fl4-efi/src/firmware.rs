//! EFI services and the x86 kernel handoff for a caller-supplied loader.

use super::*;
use core::marker::PhantomData;
use core::ptr::NonNull;

const EFI_LOAD_ERROR: Status = (1 << 63) | 1;

/// Run a loader while the firmware's boot services are live.
///
/// # Safety
///
/// Pass the image handle and system table supplied to this application's
/// EFI entry point. Call once, on the entry thread, before exiting boot services.
pub unsafe fn with_firmware(
    image: Handle,
    system: *mut SystemTable,
    load: impl FnOnce(&Firmware<'_>) -> Status,
) -> Status {
    unsafe { ST = system };
    (bs().set_watchdog_timer)(0, 0, 0, core::ptr::null());
    let mut li = core::ptr::null_mut();
    let status = (bs().handle_protocol)(image, &LOADED_IMAGE, &mut li);
    if status != SUCCESS {
        unsafe { ST = core::ptr::null_mut() };
        return status;
    }
    let loaded = unsafe { &*li.cast::<LoadedImage>() };
    let status = load(&Firmware { image, loaded });
    unsafe { ST = core::ptr::null_mut() };
    status
}

pub struct Firmware<'a> {
    image: Handle,
    loaded: &'a LoadedImage,
}

impl Firmware<'_> {
    pub fn has_load_options(&self) -> bool {
        self.loaded.options_size != 0
    }

    /// Read a file from the device that supplied this EFI image.
    pub fn read_file(&self, path: &[u8]) -> Result<FileContents<'_>, &'static str> {
        self.volume().read_file(path)
    }

    pub fn volume(&self) -> Volume<'_> {
        Volume {
            handle: self.loaded.device,
            _firmware: PhantomData,
        }
    }

    pub fn print(&self, args: core::fmt::Arguments<'_>) {
        let _ = core::fmt::Write::write_fmt(&mut Con, args);
        print("\n");
    }

    /// Locate a firmware protocol. The caller supplies its ABI when using the pointer.
    pub fn locate_protocol(&self, guid: Guid) -> Result<NonNull<c_void>, Status> {
        let mut protocol = core::ptr::null_mut();
        let status = (bs().locate_protocol)(&guid, core::ptr::null(), &mut protocol);
        if status != SUCCESS {
            return Err(status);
        }
        NonNull::new(protocol).ok_or(EFI_LOAD_ERROR)
    }

    /// Enter an x86_64 FL4 ELF kernel. The first module is the root task.
    /// Subsequent modules are passed in the order given.
    ///
    /// # Safety
    ///
    /// The kernel and root task must be trusted FL4 boot payloads for this
    /// handoff ABI. The loader writes the kernel's ELF segments to physical
    /// memory and transfers control to it after exiting boot services.
    pub unsafe fn boot(&self, kernel: &[u8], modules: &[(&[u8], &[u8])]) -> ! {
        let mut files = [(0, 0, &[][..]); 9];
        if modules.is_empty() || modules.len() > files.len() {
            fail("invalid number of boot modules");
        }
        for ((address, len, name), &(module_name, bytes)) in files.iter_mut().zip(modules) {
            *address = bytes.as_ptr() as u64;
            *len = bytes.len() as u64;
            *name = module_name;
        }
        x86::boot(self.image, kernel, &files[..modules.len()])
    }
}

const DEVICE_PATH: Guid = Guid(
    0x0957_6e91,
    0x6d3f,
    0x11d2,
    [0x8e, 0x39, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b],
);

/// A file system on an EFI device handle.
pub struct Volume<'a> {
    handle: Handle,
    _firmware: PhantomData<&'a Firmware<'a>>,
}

impl<'a> Volume<'a> {
    pub fn read_file(&self, path: &[u8]) -> Result<FileContents<'a>, &'static str> {
        let (address, size) = try_read_file(self.handle, path)?;
        Ok(FileContents {
            address,
            size,
            _firmware: PhantomData,
        })
    }

    pub fn partition_number(&self) -> Option<u32> {
        disk_path(self.handle).map(|(_, partition)| partition)
    }

    /// Open a file-system partition on the same disk as this volume.
    pub fn sibling_partition(&self, number: u32) -> Option<Self> {
        let (disk, _) = disk_path(self.handle)?;
        let mut count = 0;
        let mut handles = core::ptr::null_mut();
        // EFI_LOCATE_SEARCH_TYPE.ByProtocol enumerates file-system handles.
        if (bs().locate_handle_buffer)(2, &SIMPLE_FS, core::ptr::null(), &mut count, &mut handles)
            != SUCCESS
            || handles.is_null()
        {
            return None;
        }
        let first = unsafe { core::slice::from_raw_parts(handles, count) };
        let found = first.iter().copied().find(|&handle| {
            disk_path(handle)
                .is_some_and(|(parent, partition)| parent == disk && partition == number)
        });
        (bs().free_pool)(handles.cast());
        found.map(|handle| Self {
            handle,
            _firmware: PhantomData,
        })
    }
}

// Return the full hardware path before the hard-drive media node. EFI
// owns the device path and keeps it live while the handle is present.
fn disk_path(handle: Handle) -> Option<(&'static [u8], u32)> {
    let mut protocol = core::ptr::null_mut();
    if (bs().handle_protocol)(handle, &DEVICE_PATH, &mut protocol) != SUCCESS || protocol.is_null()
    {
        return None;
    }
    let start = protocol.cast::<u8>();
    let mut offset = 0;
    while offset <= 4092 {
        let node = unsafe { start.add(offset) };
        let header = unsafe { core::slice::from_raw_parts(node, 4) };
        let len = rd16(header, 2) as usize;
        match (header[0], header[1], len) {
            (4, 1, 42) if offset > 0 => {
                let partition = unsafe { node.add(4).cast::<u32>().read_unaligned() };
                return Some((
                    unsafe { core::slice::from_raw_parts(start, offset) },
                    partition,
                ));
            }
            (0x7f, _, _) | (_, _, 0..=3) => return None,
            _ => offset += len,
        }
    }
    None
}

/// Firmware pages holding a file, freed if the loader returns to EFI.
pub struct FileContents<'a> {
    address: u64,
    size: u64,
    _firmware: PhantomData<&'a Firmware<'a>>,
}

impl FileContents<'_> {
    pub fn bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.address as *const u8, self.size as usize) }
    }
}

impl Drop for FileContents<'_> {
    fn drop(&mut self) {
        (bs().free_pages)(self.address, self.size.div_ceil(PAGE).max(1) as usize);
    }
}
