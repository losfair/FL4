#![no_std]
#![no_main]

use core::arch::asm;
use fl4_efi::{Handle, Status, SystemTable};

#[no_mangle]
extern "efiapi" fn efi_main(image: Handle, system: *mut SystemTable) -> Status {
    unsafe { fl4_efi::start_default(image, system) }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {
        #[cfg(target_arch = "aarch64")]
        unsafe {
            asm!("wfi")
        };
        #[cfg(target_arch = "x86_64")]
        unsafe {
            asm!("hlt")
        };
    }
}
