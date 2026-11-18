// Exercise the kernel's parser against emulated physical memory.
extern crate self as fl4_core;

use std::cell::Cell;

thread_local! {
    static MEMORY: Cell<u64> = const { Cell::new(0) };
}

mod layout {
    pub fn pptr(address: u64) -> u64 {
        super::MEMORY.with(|base| base.get() + address)
    }
}

#[macro_export]
macro_rules! kprintln {
    ($($args:tt)*) => { eprintln!($($args)*) };
}

#[path = "../../fl4-kernel/src/mb2.rs"]
mod mb2;
#[allow(dead_code)]
#[path = "../../fl4-kernel/src/mboot.rs"]
mod mboot;

fn words(memory: &mut [u8], offset: usize, values: &[u32]) {
    for (chunk, value) in memory[offset..][..values.len() * 4]
        .chunks_exact_mut(4)
        .zip(values)
    {
        chunk.copy_from_slice(&value.to_le_bytes());
    }
}

fn parse(magic: u32, memory: &[u8]) -> mboot::BootInfo {
    MEMORY.with(|base| base.set(memory.as_ptr() as u64));
    let boot = mboot::parse(magic, 0).unwrap();
    MEMORY.with(|base| base.set(0));
    boot
}

#[test]
fn multiboot1_owns_the_module_name_and_truncates_it_to_the_abi() {
    let mut memory = [0; 256];
    words(&mut memory, 0, &[(1 << 3) | (1 << 6)]);
    words(&mut memory, 20, &[1, 64]);
    words(&mut memory, 44, &[24, 80]);
    words(&mut memory, 64, &[0x100000, 0x101000, 128, 0]);
    words(&mut memory, 80, &[20, 0x100000, 0, 0x100000, 0, 1]);
    memory[128..192].fill(b'x');

    let boot = parse(mboot::MB1_MAGIC, &memory);
    memory[128..192].fill(b'y');
    assert_eq!(boot.n_modules, 1);
    let module = &boot.modules[0];
    assert_eq!((module.start, module.end), (0x100000, 0x101000));
    assert_eq!(&module.name[..63], &[b'x'; 63]);
    assert_eq!(module.name[63], 0);
}

#[test]
fn multiboot2_owns_names_and_keeps_reads_inside_each_module_tag() {
    let mut memory = [0; 128];
    words(&mut memory, 0, &[112, 0]);
    words(&mut memory, 8, &[3, 29, 0x100000, 0x101000]);
    memory[24..37].copy_from_slice(b"guest-kernel\0");
    words(&mut memory, 40, &[3, 19, 0x101000, 0x102000]);
    // No terminator inside this tag. Padding is outside its declared size.
    memory[56..64].copy_from_slice(b"sdkpad!!");
    words(
        &mut memory,
        64,
        &[6, 40, 24, 0, 0x100000, 0, 0x100000, 0, 1, 0],
    );
    words(&mut memory, 104, &[0, 8]);

    let boot = parse(mboot::MB2_MAGIC, &memory);
    memory[8..64].fill(0);
    assert_eq!(boot.n_modules, 2);
    let guest = &boot.modules[0];
    assert_eq!((guest.start, guest.end), (0x100000, 0x101000));
    assert_eq!(&guest.name[..13], b"guest-kernel\0");
    assert!(guest.name[13..].iter().all(|&byte| byte == 0));
    assert_eq!(&boot.modules[1].name[..4], b"sdk\0");
}
