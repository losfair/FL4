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
        let (address, size) = try_read_file(self.loaded, path)?;
        Ok(FileContents {
            address,
            size,
            _firmware: PhantomData,
        })
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
