//! FL4's UEFI loader. Both architectures embed a kernel and can load the
//! root task and boot modules from the EFI volume. The AArch64 handoff uses
//! fl4-bootinfo. The x86_64 handoff builds Multiboot 2 information and keeps
//! long mode active for confidential guests.
#![no_std]
#![no_main]

use core::arch::asm;
use core::ffi::c_void;
#[cfg(target_arch = "aarch64")]
use fl4_bootinfo::{mem, BootInfo, MemRegion, Module, RootTask, KERNEL_VBASE, MAGIC, VERSION};

mod embedded {
    include!(concat!(env!("OUT_DIR"), "/embedded.rs"));
}

type Handle = *mut c_void;
type Status = usize;
const SUCCESS: Status = 0;
const BUFFER_TOO_SMALL: Status = (1 << 63) | 5;

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct Guid(u32, u16, u16, [u8; 8]);

const ACPI_20: Guid = Guid(0x8868_e871, 0xe4f1, 0x11d3, [0xbc, 0x22, 0x00, 0x80, 0xc7, 0x3c, 0x88, 0x81]);
const ACPI_10: Guid = Guid(0xeb9d_2d30, 0x2d88, 0x11d3, [0x9a, 0x16, 0x00, 0x90, 0x27, 0x3f, 0xc1, 0x4d]);
#[cfg(target_arch = "aarch64")]
const DTB: Guid = Guid(0xb1b6_21d5, 0xf19c, 0x41a5, [0x83, 0x0b, 0xd9, 0x15, 0x2c, 0x69, 0xaa, 0xe0]);
const LOADED_IMAGE: Guid = Guid(0x5b1b_31a1, 0x9562, 0x11d2, [0x8e, 0x3f, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b]);
const SIMPLE_FS: Guid = Guid(0x964e_5b22, 0x6459, 0x11d2, [0x8e, 0x39, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b]);
const FILE_INFO: Guid = Guid(0x0957_6e92, 0x6d3f, 0x11d2, [0x8e, 0x39, 0x00, 0xa0, 0xc9, 0x69, 0x72, 0x3b]);

#[repr(C)]
struct SystemTable {
    hdr: [u64; 3],
    vendor: *const u16,
    revision: u32,
    con_in_handle: Handle,
    con_in: *mut c_void,
    con_out_handle: Handle,
    con_out: *mut TextOutput,
    stderr_handle: Handle,
    stderr: *mut c_void,
    runtime: *mut c_void,
    boot: *mut BootServices,
    n_tables: usize,
    tables: *const ConfigTable,
}

#[repr(C)]
struct ConfigTable {
    guid: Guid,
    table: *mut c_void,
}

#[repr(C)]
struct TextOutput {
    reset: usize,
    output_string: extern "efiapi" fn(*mut TextOutput, *const u16) -> Status,
}

#[repr(C)]
struct BootServices {
    hdr: [u64; 3],
    raise_tpl: usize,
    restore_tpl: usize,
    allocate_pages: extern "efiapi" fn(u32, u32, usize, *mut u64) -> Status,
    free_pages: extern "efiapi" fn(u64, usize) -> Status,
    get_memory_map: extern "efiapi" fn(*mut usize, *mut u8, *mut usize, *mut usize, *mut u32) -> Status,
    allocate_pool: extern "efiapi" fn(u32, usize, *mut *mut u8) -> Status,
    free_pool: extern "efiapi" fn(*mut u8) -> Status,
    create_event: usize,
    set_timer: usize,
    wait_for_event: usize,
    signal_event: usize,
    close_event: usize,
    check_event: usize,
    install_protocol_interface: usize,
    reinstall_protocol_interface: usize,
    uninstall_protocol_interface: usize,
    handle_protocol: extern "efiapi" fn(Handle, *const Guid, *mut *mut c_void) -> Status,
    reserved: usize,
    register_protocol_notify: usize,
    locate_handle: usize,
    locate_device_path: usize,
    install_configuration_table: usize,
    load_image: usize,
    start_image: usize,
    exit: usize,
    unload_image: usize,
    exit_boot_services: extern "efiapi" fn(Handle, usize) -> Status,
    get_next_monotonic_count: usize,
    stall: extern "efiapi" fn(usize) -> Status,
    set_watchdog_timer: extern "efiapi" fn(usize, u64, usize, *const u16) -> Status,
}

#[repr(C)]
struct LoadedImage {
    revision: u32,
    parent: Handle,
    system_table: *mut SystemTable,
    device: Handle,
    file_path: *mut c_void,
    reserved: *mut c_void,
    options_size: u32,
    options: *const u16,
}

#[repr(C)]
struct SimpleFs {
    revision: u64,
    open_volume: extern "efiapi" fn(*mut SimpleFs, *mut *mut File) -> Status,
}

#[repr(C)]
struct File {
    revision: u64,
    open: extern "efiapi" fn(*mut File, *mut *mut File, *const u16, u64, u64) -> Status,
    close: extern "efiapi" fn(*mut File) -> Status,
    delete: usize,
    read: extern "efiapi" fn(*mut File, *mut usize, *mut u8) -> Status,
    write: usize,
    get_position: usize,
    set_position: usize,
    get_info: extern "efiapi" fn(*mut File, *const Guid, *mut usize, *mut u8) -> Status,
}

static mut ST: *mut SystemTable = core::ptr::null_mut();

fn st() -> &'static SystemTable {
    unsafe { &*ST }
}

fn bs() -> &'static BootServices {
    unsafe { &*st().boot }
}

/// Print `s` on the UEFI console.
fn print(s: &str) {
    let mut buf = [0u16; 128];
    let mut n = 0;
    for c in s.chars() {
        if c == '\n' {
            buf[n] = '\r' as u16;
            n += 1;
        }
        buf[n] = if (c as u32) < 0x10000 { c as u16 } else { '?' as u16 };
        n += 1;
        if n >= buf.len() - 3 {
            buf[n] = 0;
            let o = st().con_out;
            unsafe { ((*o).output_string)(o, buf.as_ptr()) };
            n = 0;
        }
    }
    buf[n] = 0;
    let o = st().con_out;
    unsafe { ((*o).output_string)(o, buf.as_ptr()) };
}

struct Con;
impl core::fmt::Write for Con {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        print(s);
        Ok(())
    }
}

macro_rules! say {
    ($($arg:tt)*) => {{
        let _ = core::fmt::Write::write_fmt(&mut Con, format_args!($($arg)*));
        print("\n");
    }};
}

#[cfg(target_arch = "x86_64")]
mod x86;

fn fail(msg: &str) -> ! {
    say!("fl4-efi: {}", msg);
    loop {
        #[cfg(target_arch = "aarch64")]
        unsafe { asm!("wfi") };
        #[cfg(target_arch = "x86_64")]
        unsafe { asm!("hlt") };
    }
}

const PAGE: u64 = 4096;
#[cfg(target_arch = "aarch64")]
const MB2: u64 = 2 << 20;

fn alloc_pages(n: u64) -> u64 {
    let mut p = 0u64;
    let r = (bs().allocate_pages)(0, 2, n as usize, &mut p);
    if r != SUCCESS {
        fail("out of memory");
    }
    p
}

/// `len` bytes, 2 MiB aligned.
#[cfg(target_arch = "aarch64")]
fn alloc_aligned(len: u64) -> u64 {
    let pages = len / PAGE;
    let extra = MB2 / PAGE;
    let p = alloc_pages(pages + extra);
    let a = (p + MB2 - 1) & !(MB2 - 1);
    if a > p {
        (bs().free_pages)(p, ((a - p) / PAGE) as usize);
    }
    let tail = (p + (pages + extra) * PAGE) - (a + len);
    if tail > 0 {
        (bs().free_pages)(a + len, (tail / PAGE) as usize);
    }
    a
}

fn rd16(b: &[u8], o: usize) -> u64 {
    u16::from_le_bytes([b[o], b[o + 1]]) as u64
}

fn rd32(b: &[u8], o: usize) -> u64 {
    u32::from_le_bytes(b[o..o + 4].try_into().unwrap()) as u64
}

fn rd64(b: &[u8], o: usize) -> u64 {
    u64::from_le_bytes(b[o..o + 8].try_into().unwrap())
}

#[cfg(target_arch = "aarch64")]
/// An AArch64 ELF64's loadable segments: (offset, vaddr, filesz, memsz).
fn segments(elf: &[u8], mut f: impl FnMut(u64, u64, u64, u64)) -> bool {
    if elf.len() < 64 || &elf[0..4] != b"\x7fELF" || elf[4] != 2 || rd16(elf, 18) != 183 {
        return false;
    }
    let phoff = rd64(elf, 32) as usize;
    let phentsize = rd16(elf, 54) as usize;
    let phnum = rd16(elf, 56) as usize;
    for i in 0..phnum {
        let ph = phoff + i * phentsize;
        if ph + 56 > elf.len() || rd32(elf, ph) != 1 {
            continue;
        }
        f(rd64(elf, ph + 8), rd64(elf, ph + 16), rd64(elf, ph + 32), rd64(elf, ph + 40));
    }
    true
}

/// Load `elf` at `dest` (physical) for virtual `v_start`.
#[cfg(target_arch = "aarch64")]
fn load_segments(elf: &[u8], dest: u64, v_start: u64, len: u64) {
    unsafe { core::ptr::write_bytes(dest as *mut u8, 0, len as usize) };
    segments(elf, |off, vaddr, filesz, _| {
        let n = filesz as usize;
        let src = &elf[off as usize..off as usize + n];
        unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), (dest + (vaddr - v_start)) as *mut u8, n) };
    });
}

#[cfg(target_arch = "aarch64")]
fn clean(start: u64, len: u64) {
    let line = 4u64 << ((unsafe {
        let v: u64;
        asm!("mrs {}, ctr_el0", out(reg) v);
        v
    } >> 16) & 0xf);
    let mut a = start & !(line - 1);
    while a < start + len {
        unsafe { asm!("dc cvac, {}", in(reg) a) };
        a += line;
    }
    unsafe { asm!("dsb sy") };
}

/// The load options as ASCII words (UCS-2 truncated).
struct Words {
    buf: [u8; 1024],
    n: usize,
}

impl Words {
    fn iter(&self) -> impl Iterator<Item = &[u8]> {
        self.buf[..self.n].split(|&c| c == b' ' || c == b'\t').filter(|w| !w.is_empty())
    }
}

fn options(li: &LoadedImage) -> Words {
    let mut w = Words { buf: [0; 1024], n: 0 };
    if li.options.is_null() {
        return w;
    }
    let units = (li.options_size / 2) as usize;
    for i in 0..units.min(1024) {
        let c = unsafe { *li.options.add(i) };
        if c == 0 {
            break;
        }
        w.buf[w.n] = if c < 0x80 { c as u8 } else { b'?' };
        w.n += 1;
    }
    w
}

/// Read the file `path` (ASCII, `\` or `/` separated) from the volume
/// this loader came from, into fresh pages; returns (address, size).
fn read_file(li: &LoadedImage, path: &[u8]) -> (u64, u64) {
    let mut fs: *mut c_void = core::ptr::null_mut();
    if (bs().handle_protocol)(li.device, &SIMPLE_FS, &mut fs) != SUCCESS {
        fail("no file system on the boot device");
    }
    let fs = fs as *mut SimpleFs;
    let mut root: *mut File = core::ptr::null_mut();
    if unsafe { ((*fs).open_volume)(fs, &mut root) } != SUCCESS {
        fail("cannot open the boot volume");
    }
    let mut name = [0u16; 256];
    for (i, &c) in path.iter().take(255).enumerate() {
        name[i] = if c == b'/' { b'\\' as u16 } else { c as u16 };
    }
    let mut f: *mut File = core::ptr::null_mut();
    if unsafe { ((*root).open)(root, &mut f, name.as_ptr(), 1, 0) } != SUCCESS {
        say!("fl4-efi: cannot open {}", core::str::from_utf8(path).unwrap_or("?"));
        fail("missing file");
    }
    let mut info = [0u8; 512];
    let mut isz = info.len();
    if unsafe { ((*f).get_info)(f, &FILE_INFO, &mut isz, info.as_mut_ptr()) } != SUCCESS {
        fail("cannot stat a file");
    }
    let size = rd64(&info, 8);
    let p = alloc_pages(size.div_ceil(PAGE).max(1));
    let mut n = size as usize;
    if unsafe { ((*f).read)(f, &mut n, p as *mut u8) } != SUCCESS || n as u64 != size {
        fail("cannot read a file");
    }
    unsafe {
        ((*f).close)(f);
        ((*root).close)(root);
    }
    (p, size)
}

fn config_table(g: Guid) -> u64 {
    let s = st();
    for i in 0..s.n_tables {
        let t = unsafe { &*s.tables.add(i) };
        if t.guid == g {
            return t.table as u64;
        }
    }
    0
}

/// The loader's page tables in the kernel region: the region mapped at
/// its own address (TTBR0) and at KERNEL_VBASE (TTBR1), in 2 MiB blocks,
/// normal memory (MAIR index 0), executable.
#[cfg(target_arch = "aarch64")]
fn build_tables(tables: u64, pa: u64, len: u64) -> (u64, u64) {
    let t = |i: u64| tables + i * PAGE;
    unsafe { core::ptr::write_bytes(tables as *mut u8, 0, 6 * PAGE as usize) };
    let w = |table: u64, idx: u64, v: u64| unsafe { ((table + (idx & 511) * 8) as *mut u64).write_volatile(v) };
    let table_desc = |p: u64| p | 3;
    // Normal, inner shareable, access flag, EL1 read-write.
    let block = |p: u64| p | 1 | (3 << 8) | (1 << 10);
    let map = |root: u64, l1: u64, l2: u64, va: u64| {
        w(root, va >> 39, table_desc(l1));
        w(l1, va >> 30, table_desc(l2));
        let mut off = 0;
        while off < len {
            w(l2, (va + off) >> 21, block(pa + off));
            off += MB2;
        }
    };
    map(t(0), t(1), t(2), pa);
    map(t(3), t(4), t(5), KERNEL_VBASE);
    (t(0), t(3))
}

/// Leave the loader for the kernel: caches and MMU off at this exception
/// level, then branch to `entry` (physical) with x0 = `arg`.
#[cfg(target_arch = "aarch64")]
unsafe fn enter(entry: u64, arg: u64) -> ! {
    asm!(
        "msr daifset, #0xf",
        "mrs x9, CurrentEL",
        "lsr x9, x9, #2",
        "cmp x9, #2",
        "b.eq 2f",
        "mrs x9, sctlr_el1",
        "bic x9, x9, #1",
        "bic x9, x9, #(1 << 2)",
        "bic x9, x9, #(1 << 12)",
        "msr sctlr_el1, x9",
        "b 3f",
        "2:",
        "mrs x9, sctlr_el2",
        "bic x9, x9, #1",
        "bic x9, x9, #(1 << 2)",
        "bic x9, x9, #(1 << 12)",
        "msr sctlr_el2, x9",
        "3:",
        "isb",
        "ic iallu",
        "dsb sy",
        "isb",
        "mov x0, x11",
        "br x10",
        in("x10") entry,
        in("x11") arg,
        options(noreturn)
    );
}

#[cfg(target_arch = "aarch64")]
fn mem_kind(ty: u32) -> u32 {
    match ty {
        // Loader code/data, boot services code/data, conventional.
        1 | 2 | 3 | 4 | 7 => mem::FREE,
        // Runtime services, ACPI reclaim and NVS, persistent memory.
        5 | 6 | 9 | 10 | 14 => mem::FIRMWARE,
        _ => mem::OTHER,
    }
}

#[cfg(target_arch = "aarch64")]
#[no_mangle]
extern "efiapi" fn efi_main(image: Handle, system: *mut SystemTable) -> Status {
    unsafe { ST = system };
    (bs().set_watchdog_timer)(0, 0, 0, core::ptr::null());
    say!("fl4-efi: FL4 UEFI loader (AArch64)");
    let mut li: *mut c_void = core::ptr::null_mut();
    if (bs().handle_protocol)(image, &LOADED_IMAGE, &mut li) != SUCCESS {
        fail("no loaded image protocol");
    }
    let li = unsafe { &*(li as *const LoadedImage) };
    let opts = options(li);

    // The kernel region: image, boot tables, boot record.
    let kernel = embedded::KERNEL;
    let mut k_end = 0;
    if !segments(kernel, |_, vaddr, _, memsz| k_end = k_end.max(vaddr + memsz)) || k_end <= KERNEL_VBASE {
        fail("no AArch64 kernel image built in");
    }
    let image_len = (k_end - KERNEL_VBASE + PAGE - 1) & !(PAGE - 1);
    let tables_off = image_len;
    let bi_off = tables_off + 6 * PAGE;
    let bi_len = (core::mem::size_of::<BootInfo>() as u64 + PAGE - 1) & !(PAGE - 1);
    let region_len = (bi_off + bi_len + MB2 - 1) & !(MB2 - 1);
    let region = alloc_aligned(region_len);
    load_segments(kernel, region, KERNEL_VBASE, image_len);
    let (ttbr0, ttbr1) = build_tables(region + tables_off, region, region_len);
    let bi = unsafe { &mut *((region + bi_off) as *mut BootInfo) };
    unsafe { core::ptr::write_bytes(bi as *mut BootInfo as *mut u8, 0, core::mem::size_of::<BootInfo>()) };
    bi.magic = MAGIC;
    bi.version = VERSION;
    bi.region_paddr = region;
    bi.region_len = region_len;
    bi.ttbr0 = ttbr0;
    bi.ttbr1 = ttbr1;

    // Options: the root task, boot modules, and the kernel command line.
    let mut first = true;
    let mut root_path: Option<&[u8]> = None;
    let mut cl = 0;
    for w in opts.iter() {
        let is_image = first && w.len() > 4 && w[w.len() - 4..].eq_ignore_ascii_case(b".efi");
        first = false;
        if is_image {
            continue;
        }
        if let Some(p) = w.strip_prefix(b"rootserver=") {
            root_path = Some(p);
        } else if let Some(p) = w.strip_prefix(b"module=") {
            let n = bi.n_modules as usize;
            if n == fl4_bootinfo::MAX_MODULES {
                fail("too many boot modules");
            }
            let (pa, size) = read_file(li, p);
            let mut name = [0u8; fl4_bootinfo::NAME_LEN];
            let base = p.rsplit(|&c| c == b'\\' || c == b'/').next().unwrap_or(p);
            for (i, &c) in base.iter().take(fl4_bootinfo::NAME_LEN - 1).enumerate() {
                name[i] = c;
            }
            bi.modules[n] = Module { paddr: pa, size, name };
            bi.n_modules += 1;
        } else if cl + w.len() + 1 < fl4_bootinfo::CMDLINE_LEN {
            if cl > 0 {
                bi.cmdline[cl] = b' ';
                cl += 1;
            }
            bi.cmdline[cl..cl + w.len()].copy_from_slice(w);
            cl += w.len();
        }
    }
    let root_file: &[u8] = match root_path {
        Some(p) => {
            let (pa, size) = read_file(li, p);
            unsafe { core::slice::from_raw_parts(pa as *const u8, size as usize) }
        }
        None => embedded::ROOTSERVER,
    };
    let (mut v_lo, mut v_hi) = (u64::MAX, 0);
    if !segments(root_file, |_, vaddr, _, memsz| {
        v_lo = v_lo.min(vaddr);
        v_hi = v_hi.max(vaddr + memsz);
    }) || v_hi <= v_lo
    {
        fail("no AArch64 root task (pass rootserver=\\path)");
    }
    let v_start = v_lo & !(PAGE - 1);
    let v_end = (v_hi + PAGE - 1) & !(PAGE - 1);
    let root_pa = alloc_pages((v_end - v_start) / PAGE);
    load_segments(root_file, root_pa, v_start, v_end - v_start);
    bi.root = RootTask { p_start: root_pa, p_end: root_pa + (v_end - v_start), v_start, entry: rd64(root_file, 24) };

    bi.rsdp = config_table(ACPI_20);
    if bi.rsdp == 0 {
        bi.rsdp = config_table(ACPI_10);
    }
    bi.dtb = config_table(DTB);
    if bi.dtb != 0 {
        let h = unsafe { core::slice::from_raw_parts(bi.dtb as *const u8, 8) };
        bi.dtb_len = u32::from_be_bytes(h[4..8].try_into().unwrap()) as u64;
    }
    say!("fl4-efi: kernel region {:#x} ({:#x} bytes), root task {:#x}..{:#x}, ACPI {:#x}, device tree {:#x}",
        region, region_len, bi.root.p_start, bi.root.p_end, bi.rsdp, bi.dtb);

    // The memory map, then leave boot services.
    let mut size = 0usize;
    let mut key = 0usize;
    let mut dsize = 0usize;
    let mut dver = 0u32;
    let r = (bs().get_memory_map)(&mut size, core::ptr::null_mut(), &mut key, &mut dsize, &mut dver);
    if r != BUFFER_TOO_SMALL && r != SUCCESS {
        fail("GetMemoryMap");
    }
    let cap = size + 16 * dsize.max(48);
    let buf = alloc_pages((cap as u64).div_ceil(PAGE));
    let mut tries = 0;
    loop {
        size = cap;
        if (bs().get_memory_map)(&mut size, buf as *mut u8, &mut key, &mut dsize, &mut dver) != SUCCESS {
            fail("GetMemoryMap");
        }
        if (bs().exit_boot_services)(image, key) == SUCCESS {
            break;
        }
        tries += 1;
        if tries > 8 {
            fail("ExitBootServices");
        }
    }
    // No boot services from here on.
    // Adjacent entries of the same kind are merged. Every entry must fit:
    // the kernel hands out what the map leaves out as device memory.
    let mut n = 0;
    let mut off = 0;
    while off + dsize <= size {
        let d = unsafe { core::slice::from_raw_parts((buf + off as u64) as *const u8, dsize) };
        let ty = rd32(d, 0) as u32;
        let base = rd64(d, 8);
        let pages = rd64(d, 24);
        let attr = rd64(d, 32);
        let e = MemRegion { base, len: pages * PAGE, kind: mem_kind(ty), cacheable: (attr & 8 != 0) as u32 };
        off += dsize;
        if n > 0 {
            let p = &mut bi.mmap[n - 1];
            if p.kind == e.kind && p.cacheable == e.cacheable && p.base + p.len == e.base {
                p.len += e.len;
                continue;
            }
        }
        if n == fl4_bootinfo::MAX_MMAP {
            // Boot services are gone: no console to say why.
            loop {
                unsafe { asm!("wfi") };
            }
        }
        bi.mmap[n] = e;
        n += 1;
    }
    bi.n_mmap = n as u64;
    clean(region, region_len);
    clean(bi.root.p_start, bi.root.p_end - bi.root.p_start);
    for i in 0..bi.n_modules as usize {
        clean(bi.modules[i].paddr, bi.modules[i].size);
    }
    unsafe { enter(region, bi_off) }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {
        #[cfg(target_arch = "aarch64")]
        unsafe { asm!("wfi") };
        #[cfg(target_arch = "x86_64")]
        unsafe { asm!("hlt") };
    }
}
