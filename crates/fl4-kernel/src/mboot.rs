//! Multiboot 1 and 2 boot information, and loading the root task's ELF
//! image (seL4 arch/x86/kernel/boot_sys.c).
use fl4_core::layout::pptr;

pub const MB1_MAGIC: u32 = 0x2bad_b002;
pub const MB2_MAGIC: u32 = 0x36d7_6289;
pub const MAX_MMAP: usize = 50;
/// The root task's image and up to eight more modules (l4h 0021).
pub const MAX_MODULES: usize = 9;
const MODULE_NAME_LEN: usize = 64;

#[derive(Clone, Copy, Default)]
pub struct MemRegion {
    pub base: u64,
    pub len: u64,
    pub ty: u32,
}

#[derive(Clone, Copy)]
pub struct Module {
    pub start: u64,
    pub end: u64,
    /// NUL-terminated name for seL4_X86_BootModules_t. Own the bytes before
    /// starting APs: their trampoline can overwrite the boot loader's data.
    pub name: [u8; MODULE_NAME_LEN],
}

impl Module {
    const EMPTY: Self = Self { start: 0, end: 0, name: [0; MODULE_NAME_LEN] };
}

pub struct BootInfo {
    pub mmap: [MemRegion; MAX_MMAP],
    pub n_mmap: usize,
    pub modules: [Module; MAX_MODULES],
    pub n_modules: usize,
    /// RSDP copied from Multiboot 2 tags, if any.
    pub rsdp: Option<u64>,
    /// The command line (a C string's physical address), or 0.
    pub cmdline: u64,
    /// The framebuffer the boot loader set up, if any.
    pub fb: Option<Framebuffer>,
}

/// seL4's `multiboot2_fb_t`.
#[derive(Clone, Copy)]
pub struct Framebuffer {
    pub addr: u64,
    pub pitch: u32,
    pub width: u32,
    pub height: u32,
    pub bpp: u8,
    pub ty: u8,
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

impl BootInfo {
    /// Note a module. One that ends before it starts is ignored (l4h 0021:
    /// its 32-bit difference looks positive), as are any past the limit.
    fn add_module(&mut self, start: u64, end: u64, name_addr: u64, name_len: u64) {
        if end < start {
            crate::kprintln!("FL4: boot module ends before it starts: ignored");
            return;
        }
        if self.n_modules == MAX_MODULES {
            crate::kprintln!("FL4: more than {} boot modules: the rest are ignored", MAX_MODULES - 1);
            return;
        }
        let mut module = Module { start, end, ..Module::EMPTY };
        if name_addr != 0 {
            let limit = name_len.min((MODULE_NAME_LEN - 1) as u64);
            for i in 0..limit {
                let byte = rd8(name_addr + i);
                if byte == 0 {
                    break;
                }
                module.name[i as usize] = byte;
            }
        }
        self.modules[self.n_modules] = module;
        self.n_modules += 1;
    }
}

/// Whether the command line has the word `opt` (a boolean option such as
/// `fb_console`; `opt=1`, `opt=true` and `opt=on` count too).
pub fn has_option(b: &BootInfo, opt: &[u8]) -> bool {
    if b.cmdline == 0 {
        return false;
    }
    let mut p = b.cmdline;
    loop {
        while rd8(p) == b' ' {
            p += 1;
        }
        if rd8(p) == 0 {
            return false;
        }
        let start = p;
        while rd8(p) != 0 && rd8(p) != b' ' {
            p += 1;
        }
        let word = |i: u64| rd8(start + i);
        let len = p - start;
        let n = opt.len() as u64;
        if len >= n && (0..n).all(|i| word(i) == opt[i as usize]) {
            if len == n {
                return true;
            }
            if word(n) == b'=' {
                let v = |s: &[u8]| len == n + 1 + s.len() as u64 && (0..s.len() as u64).all(|i| word(n + 1 + i) == s[i as usize]);
                return v(b"1") || v(b"true") || v(b"on");
            }
        }
    }
}

pub fn parse(magic: u32, info: u64) -> Option<BootInfo> {
    let mut b = BootInfo { mmap: [MemRegion::default(); MAX_MMAP], n_mmap: 0, modules: [Module::EMPTY; MAX_MODULES], n_modules: 0, rsdp: None, cmdline: 0, fb: None };
    if magic == MB1_MAGIC {
        let flags = rd32(info);
        if flags & (1 << 2) != 0 {
            b.cmdline = rd32(info + 16) as u64;
        }
        if flags & (1 << 12) != 0 {
            b.fb = Some(Framebuffer { addr: rd64(info + 88), pitch: rd32(info + 96), width: rd32(info + 100), height: rd32(info + 104), bpp: rd8(info + 108), ty: rd8(info + 109) });
        }
        if flags & (1 << 3) != 0 {
            let n = rd32(info + 20) as u64;
            let addr = rd32(info + 24) as u64;
            for i in 0..n {
                let m = addr + 16 * i;
                b.add_module(rd32(m) as u64, rd32(m + 4) as u64, rd32(m + 8) as u64, MODULE_NAME_LEN as u64);
            }
        }
        if flags & (1 << 6) == 0 {
            return None;
        }
        let len = rd32(info + 44) as u64;
        let addr = rd32(info + 48) as u64;
        let mut p = addr;
        while p < addr + len && b.n_mmap < MAX_MMAP {
            let size = rd32(p) as u64;
            b.mmap[b.n_mmap] = MemRegion { base: rd64(p + 4), len: rd64(p + 12), ty: rd32(p + 20) };
            b.n_mmap += 1;
            p += size + 4;
        }
        Some(b)
    } else if magic == MB2_MAGIC {
        crate::mb2::tags(info, rd32, |t, ty, size| match ty {
            1 => b.cmdline = t + 8,
            8 => b.fb = Some(Framebuffer { addr: rd64(t + 8), pitch: rd32(t + 16), width: rd32(t + 20), height: rd32(t + 24), bpp: rd8(t + 28), ty: rd8(t + 29) }),
            3 if size >= 16 => b.add_module(rd32(t + 8) as u64, rd32(t + 12) as u64, t + 16, size - 16),
            6 => {
                let esz = rd32(t + 8) as u64;
                let mut e = t + 16;
                while e + esz <= t + size && b.n_mmap < MAX_MMAP && esz >= 20 {
                    b.mmap[b.n_mmap] = MemRegion { base: rd64(e), len: rd64(e + 8), ty: rd32(e + 16) };
                    b.n_mmap += 1;
                    e += esz;
                }
            }
            14 | 15 => {
                if b.rsdp.is_none() || ty == 15 {
                    b.rsdp = Some(t + 8);
                }
            }
            _ => {}
        });
        if b.n_mmap == 0 {
            return None;
        }
        Some(b)
    } else {
        None
    }
}

/// A loaded root task image.
pub struct Image {
    pub p_start: u64,
    pub p_end: u64,
    pub v_start: u64,
    pub entry: u64,
}

const PAGE: u64 = 4096;

fn round_up(v: u64) -> u64 {
    (v + PAGE - 1) & !(PAGE - 1)
}

/// The virtual range an ELF64 image's loadable segments cover.
fn elf_range(elf: u64) -> Option<(u64, u64)> {
    if rd32(elf) != 0x464c_457f || rd8(elf + 4) != 2 || rd16(elf + 18) != 0x3e {
        return None;
    }
    let phoff = rd64(elf + 32);
    let phentsize = rd16(elf + 54) as u64;
    let phnum = rd16(elf + 56) as u64;
    let mut lo = u64::MAX;
    let mut hi = 0;
    for i in 0..phnum {
        let ph = elf + phoff + i * phentsize;
        if rd32(ph) == 1 {
            let vaddr = rd64(ph + 16);
            let memsz = rd64(ph + 40);
            lo = lo.min(vaddr);
            hi = hi.max(vaddr + memsz);
        }
    }
    if lo >= hi {
        return None;
    }
    Some((lo & !(PAGE - 1), round_up(hi)))
}

/// Copy the ELF image at physical `elf` to physical memory from `dest`
/// (page aligned), seL4 `load_boot_module`.
pub fn load_elf(elf: u64, dest: u64) -> Option<Image> {
    let (v_start, v_end) = elf_range(elf)?;
    let off = dest.wrapping_sub(v_start);
    let phoff = rd64(elf + 32);
    let phentsize = rd16(elf + 54) as u64;
    let phnum = rd16(elf + 56) as u64;
    unsafe { core::ptr::write_bytes(pptr(dest) as *mut u8, 0, (v_end - v_start) as usize) };
    for i in 0..phnum {
        let ph = elf + phoff + i * phentsize;
        if rd32(ph) != 1 {
            continue;
        }
        let offset = rd64(ph + 8);
        let vaddr = rd64(ph + 16);
        let filesz = rd64(ph + 32);
        unsafe {
            core::ptr::copy(pptr(elf + offset) as *const u8, pptr(vaddr.wrapping_add(off)) as *mut u8, filesz as usize);
        }
    }
    Some(Image { p_start: dest, p_end: dest + (v_end - v_start), v_start, entry: rd64(elf + 24) })
}
