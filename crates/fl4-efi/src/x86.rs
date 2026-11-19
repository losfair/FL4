//! Long-mode handoff for x86 guests. Firmware handles #VC until boot
//! services exit. The kernel takes over with its own private page tables.
use super::*;

const SNP_BLOB: Guid = Guid(
    0x067b_1f5f,
    0xcf26,
    0x44c5,
    [0x85, 0x54, 0x93, 0xd7, 0x77, 0x91, 0x2d, 0x42],
);
const TOP: u64 = 1 << 32;
const HUGE: u64 = 2 << 20;
const KERNEL_OFFSET: u64 = 0xffff_ffff_8000_0000;
const LINK_BASE: u64 = 0x10_0000;
const MB_MAGIC: u64 = 0x36d7_6289;
const TABLE_BYTES: u64 = 10 * PAGE;
const INFO_BYTES: u64 = 4 * PAGE;
// Match the kernel's mboot::MAX_MMAP after adjacent descriptors are merged.
const MAX_MMAP: u64 = 128;

fn alloc_low(bytes: u64) -> u64 {
    let mut address = TOP - 1;
    if (bs().allocate_pages)(1, 2, bytes.div_ceil(PAGE) as usize, &mut address) != SUCCESS {
        fail("cannot allocate boot memory below 4 GiB");
    }
    address
}

// Keep the instructions after the CR3 switch inside the new identity map,
// even if firmware loaded the EFI executable above 4 GiB.
core::arch::global_asm!(
    ".section .text",
    "fl4_handoff:",
    "mov cr3, rax",
    "jmp r10",
    "fl4_handoff_end:",
);

fn handoff_code() -> u64 {
    extern "C" {
        static fl4_handoff: u8;
        static fl4_handoff_end: u8;
    }
    let start = core::ptr::addr_of!(fl4_handoff) as u64;
    let end = core::ptr::addr_of!(fl4_handoff_end) as u64;
    let mut address = TOP - 1;
    // AllocateMaxAddress, EfiLoaderCode: executable in both page tables.
    if (bs().allocate_pages)(1, 1, 1, &mut address) != SUCCESS {
        fail("cannot allocate low boot trampoline");
    }
    write(address, unsafe {
        core::slice::from_raw_parts(start as *const u8, (end - start) as usize)
    });
    address
}

fn sev() -> (u64, u64, u64) {
    use core::arch::x86_64::__cpuid_count as cpuid;
    if cpuid(0x8000_0000, 0).eax < 0x8000_001f {
        return (0, 0, 0);
    }
    let leaf = cpuid(0x8000_001f, 0);
    if leaf.eax & 2 == 0 {
        return (0, 0, 0);
    }
    let (lo, hi): (u32, u32);
    unsafe { asm!("rdmsr", in("ecx") 0xc001_0131u32, out("eax") lo, out("edx") hi) };
    let status = ((hi as u64) << 32) | lo as u64;
    if status & 1 == 0 {
        return (0, 0, 0);
    }
    let mut cpuid_page = 0;
    let mut secrets_page = 0;
    if status & 4 != 0 {
        // This implementation uses the base SNP ABI with standard delivery.
        // Other SEV_FEATURES can change address, injection or VMSA semantics.
        if status != 7 {
            fail("unsupported SEV-SNP status bits");
        }
        let blob = config_table(SNP_BLOB);
        if blob == 0 {
            fail("missing SNP firmware CPUID table");
        }
        let b = unsafe { core::slice::from_raw_parts(blob as *const u8, 40) };
        cpuid_page = rd64(b, 24);
        secrets_page = rd64(b, 8);
        if rd32(b, 0) != 0x4544_4d41
            || rd16(b, 4) != 1
            || rd32(b, 32) != PAGE
            || cpuid_page == 0
            || cpuid_page % PAGE != 0
            || rd32(b, 16) != PAGE
            || secrets_page == 0
            || secrets_page % PAGE != 0
        {
            fail("invalid SNP firmware CPUID table");
        }
    } else if status & 2 != 0 {
        fail("SEV-ES without SNP");
    }
    let bit = leaf.ebx & 63;
    if !(32..=51).contains(&bit) {
        fail("invalid SEV C-bit");
    }
    (1 << bit, cpuid_page, secrets_page)
}

struct Info {
    base: u64,
    used: u64,
}

fn write(pa: u64, bytes: &[u8]) {
    unsafe { core::ptr::copy_nonoverlapping(bytes.as_ptr(), pa as *mut u8, bytes.len()) }
}

impl Info {
    fn tag(&mut self, kind: u32, len: u64) -> u64 {
        let p = self.base + self.used;
        self.used += (len + 15) & !7;
        assert!(self.used <= INFO_BYTES);
        write(p, &kind.to_le_bytes());
        write(p + 4, &((len + 8) as u32).to_le_bytes());
        p + 8
    }

    fn module(&mut self, pa: u64, len: u64, name: &[u8]) {
        let p = self.tag(3, 9 + name.len() as u64);
        write(p, &(pa as u32).to_le_bytes());
        write(p + 4, &((pa + len) as u32).to_le_bytes());
        write(p + 8, name);
    }
}

/// Conventional and reclaimable boot-services pages are free. Keep
/// firmware RAM distinguishable from device apertures for encrypted guests.
fn memory_kind(ty: u64, attributes: u64) -> u32 {
    match ty {
        1..=4 | 7 => 1,
        9 => 3,
        5 | 6 | 10 | 14 | 15 => 4,
        0 if attributes & 8 != 0 => 4,
        _ => 2,
    }
}

fn memory_map(
    info: &mut Info,
    map: &[u8],
    stride: usize,
    cpuid: u64,
    secrets: u64,
) -> Result<(), &'static str> {
    let tag = info.tag(6, 8);
    write(tag, &24u32.to_le_bytes());
    let mut count = 0;
    let mut previous: Option<(u64, u64, u32)> = None;
    let mut emit = |(base, bytes, kind): (u64, u64, u32)| {
        count += 1;
        if count > MAX_MMAP || info.used + 24 + 8 > INFO_BYTES {
            return Err("EFI memory map has too many regions for FL4");
        }
        let p = info.base + info.used;
        write(p, &base.to_le_bytes());
        write(p + 8, &bytes.to_le_bytes());
        write(p + 16, &(kind as u64).to_le_bytes());
        info.used += 24;
        Ok(())
    };
    for d in map.chunks_exact(stride) {
        let base = rd64(d, 8);
        let bytes = rd64(d, 24) * PAGE;
        let sensitive = [cpuid, secrets]
            .into_iter()
            .any(|page| page != 0 && base <= page && page - base < bytes);
        let kind = if sensitive {
            4
        } else {
            memory_kind(rd32(d, 0), rd64(d, 32))
        };
        if let Some((start, len, ty)) = previous {
            if start + len == base && ty == kind {
                previous = Some((start, len + bytes, ty));
                continue;
            }
            emit((start, len, ty))?;
        }
        previous = Some((base, bytes, kind));
    }
    if let Some(last) = previous {
        emit(last)?;
    }
    write(
        tag - 4,
        &((info.base + info.used - (tag - 8)) as u32).to_le_bytes(),
    );
    info.tag(0, 0);
    write(info.base, &(info.used as u32).to_le_bytes());
    Ok(())
}

/// After the first ExitBootServices call, the console protocol may have
/// shut down even if firmware returned an error. Halt without using it.
fn handoff_failed(attempt: usize, message: &str) -> ! {
    if attempt == 0 {
        fail(message);
    }
    loop {
        unsafe { asm!("cli; hlt", options(nomem, nostack)) };
    }
}

fn tables(pa: u64, delta: u64, mask: u64, end: u64) {
    let t = |i| pa + i * PAGE;
    let e = |i, slot, value: u64| write(t(i) + slot * 8, &value.to_le_bytes());
    let ptr = |i| t(i) | mask | 3;
    e(0, 0, ptr(1));
    e(0, 511, ptr(2));
    if mask != 0 {
        e(0, 510, ptr(9));
        for g in 0..4 {
            e(9, g, (g << 30) | 0x83);
        }
    }
    for g in 0..4 {
        e(1, g, ptr(3 + g));
        e(2, g, ptr(3 + g));
        for j in 0..512 {
            e(3 + g, j, ((g * 512 + j) * HUGE) | mask | 0x83);
        }
    }
    // The kernel's link-time physical offsets remain its high-half virtual
    // offsets even when firmware allocates the image elsewhere. delta is
    // 2 MiB aligned so these mappings use large pages as well.
    e(2, (KERNEL_OFFSET >> 30) & 511, ptr(7));
    e(2, 511, ptr(8));
    for (i, off) in (0..end).step_by(HUGE as usize).enumerate() {
        let slot = (KERNEL_OFFSET >> 21 & 511) + i as u64;
        e(7 + slot / 512, slot % 512, (delta + off) | mask | 0x83);
    }
}

/// The linker emits a named section for the long-mode entry. The ELF
/// entry point remains the 32-bit Multiboot entry, even in a stripped ELF.
fn long_mode_entry(kernel: &[u8]) -> Option<u64> {
    let table = rd64(kernel, 40) as usize;
    let stride = rd16(kernel, 58) as usize;
    let count = rd16(kernel, 60) as usize;
    let names = rd16(kernel, 62) as usize;
    if stride < 64 || names >= count {
        return None;
    }
    let end = table.checked_add(stride.checked_mul(count)?)?;
    let sections = kernel.get(table..end)?.chunks_exact(stride);
    let strings = sections.clone().nth(names)?;
    let start = rd64(strings, 24) as usize;
    let end = start.checked_add(rd64(strings, 32) as usize)?;
    let names = kernel.get(start..end)?;
    let entry = sections
        .filter(|s| rd64(s, 8) & 6 == 6 && rd64(s, 32) != 0)
        .find(|s| {
            names
                .get(rd32(s, 0) as usize..)
                .is_some_and(|name| name.starts_with(b".efi.entry\0"))
        })?;
    Some(rd64(entry, 16))
}

pub(super) type BootFile<'a> = (u64, u64, &'a [u8]);

fn boot_files<'a>(li: &LoadedImage, opts: &'a Words) -> ([BootFile<'a>; 9], usize) {
    let mut files = [(0, 0, &[][..]); 9];
    let mut n = 1;
    for opt in opts.iter() {
        if let Some(path) = opt.strip_prefix(b"rootserver=") {
            let (pa, len) = read_file(li, path);
            files[0] = (pa, len, path);
        } else if let Some(path) = opt.strip_prefix(b"module=") {
            if n == files.len() {
                fail("too many boot modules");
            }
            let (pa, len) = read_file(li, path);
            files[n] = (pa, len, path);
            n += 1;
        }
    }
    if files[0].1 == 0 {
        if embedded::ROOTSERVER.is_empty() {
            fail("no x86_64 root task");
        }
        files[0] = (
            embedded::ROOTSERVER.as_ptr() as u64,
            embedded::ROOTSERVER.len() as u64,
            b"rootserver",
        );
    }
    // The fallback EFI path has no load options. Allow a boot module to
    // be built in alongside the root task.
    if !embedded::MODULE.is_empty() {
        if n == files.len() {
            fail("too many boot modules");
        }
        files[n] = (
            embedded::MODULE.as_ptr() as u64,
            embedded::MODULE.len() as u64,
            b"module",
        );
        n += 1;
    }
    (files, n)
}

pub unsafe fn start_default(image: Handle, system: *mut SystemTable) -> Status {
    unsafe { ST = system };
    (bs().set_watchdog_timer)(0, 0, 0, core::ptr::null());
    say!("fl4-efi: FL4 UEFI loader (x86_64)");
    let mut li = core::ptr::null_mut();
    if (bs().handle_protocol)(image, &LOADED_IMAGE, &mut li) != SUCCESS {
        fail("no loaded image protocol");
    }
    let li = unsafe { &*(li as *const LoadedImage) };
    let opts = options(li);
    let (files, n) = boot_files(li, &opts);
    boot(image, embedded::KERNEL, &files[..n])
}

pub(super) fn boot(image: Handle, kernel: &[u8], files: &[BootFile<'_>]) -> ! {
    let cr4: u64;
    unsafe { asm!("mov {}, cr4", out(reg) cr4) };
    if cr4 & (1 << 12) != 0 {
        fail("firmware uses five-level paging");
    }
    let (mask, cpuid, secrets) = sev();
    if kernel.len() < 64 || &kernel[..5] != b"\x7fELF\x02" || rd16(kernel, 18) != 62 {
        fail("no x86_64 kernel image built in");
    }
    let ph = rd64(kernel, 32) as usize;
    let stride = rd16(kernel, 54) as usize;
    let segments = kernel[ph..ph + stride * rd16(kernel, 56) as usize]
        .chunks_exact(stride)
        .filter(|p| rd32(p, 0) == 1);
    let end = segments
        .clone()
        .map(|p| rd64(p, 24) + rd64(p, 40))
        .max()
        .unwrap_or(0);
    let entry = long_mode_entry(kernel)
        .filter(|&entry| {
            entry >= KERNEL_OFFSET
                && segments.clone().any(|p| {
                    let base = rd64(p, 16);
                    rd32(p, 4) & 1 != 0 && entry >= base && entry - base < rd64(p, 32)
                })
        })
        .unwrap_or_else(|| fail("no long-mode kernel entry"));
    let end = end.div_ceil(PAGE) * PAGE;
    let files_len: u64 = files
        .iter()
        .map(|&(_, len, _)| len.div_ceil(PAGE) * PAGE)
        .sum();
    let len = end + TABLE_BYTES + INFO_BYTES + 2 * PAGE + files_len;
    let base = alloc_low(len + HUGE);
    let delta = base.div_ceil(HUGE) * HUGE;
    unsafe {
        core::ptr::write_bytes(
            (delta + LINK_BASE) as *mut u8,
            0,
            (len - LINK_BASE) as usize,
        )
    };
    for p in segments {
        let off = rd64(p, 8) as usize;
        write(
            delta + rd64(p, 24),
            &kernel[off..off + rd64(p, 32) as usize],
        );
    }
    let root = delta + end;
    tables(root, delta, mask, end);
    let mut info = Info {
        base: root + TABLE_BYTES,
        used: 8,
    };
    let cpuid_copy = info.base + INFO_BYTES;
    if cpuid != 0 {
        write(cpuid_copy, unsafe {
            core::slice::from_raw_parts(cpuid as *const u8, PAGE as usize)
        });
    }
    let mut dst = cpuid_copy + 2 * PAGE;
    for &(src, size, path) in files {
        write(dst, unsafe {
            core::slice::from_raw_parts(src as *const u8, size as usize)
        });
        let name = path
            .rsplit(|&b| b == b'/' || b == b'\\')
            .next()
            .unwrap_or(path);
        info.module(dst, size, &name[..name.len().min(63)]);
        dst += size.div_ceil(PAGE) * PAGE;
    }
    let rsdp = config_table(ACPI_20);
    let (rsdp, kind, size) = if rsdp != 0 {
        (rsdp, 15, 36)
    } else {
        (config_table(ACPI_10), 14, 20)
    };
    if rsdp != 0 {
        write(info.tag(kind, size), unsafe {
            core::slice::from_raw_parts(rsdp as *const u8, size as usize)
        });
    }
    let trampoline = handoff_code();
    say!("fl4-efi: entering x86_64 kernel, SEV-SNP {}", cpuid != 0);
    let (mut size, mut key, mut stride, mut version) = (0, 0, 0, 0);
    if (bs().get_memory_map)(
        &mut size,
        core::ptr::null_mut(),
        &mut key,
        &mut stride,
        &mut version,
    ) != BUFFER_TOO_SMALL
    {
        fail("GetMemoryMap");
    }
    let capacity = size + 16 * stride;
    let buffer = alloc_pages((capacity as u64).div_ceil(PAGE));
    let tags_end = info.used;
    for attempt in 0..8 {
        size = capacity;
        if (bs().get_memory_map)(
            &mut size,
            buffer as *mut u8,
            &mut key,
            &mut stride,
            &mut version,
        ) != SUCCESS
        {
            handoff_failed(attempt, "GetMemoryMap");
        }
        if stride < 40 || size % stride != 0 {
            handoff_failed(attempt, "invalid EFI memory map");
        }
        let map = unsafe { core::slice::from_raw_parts(buffer as *const u8, size) };
        info.used = tags_end;
        if let Err(message) = memory_map(&mut info, map, stride, cpuid, secrets) {
            handoff_failed(attempt, message);
        }
        if (bs().exit_boot_services)(image, key) == SUCCESS {
            break;
        }
        if attempt == 7 {
            handoff_failed(attempt, "ExitBootServices");
        }
    }
    unsafe {
        asm!(
            "cli",
            "cld",
            "mov cr4, r11",
            "jmp r9",
            in("rax") root | mask,
            in("r10") entry,
            in("r11") cr4 & !(1 << 7),
            in("rdi") MB_MAGIC,
            in("rsi") info.base,
            in("rdx") mask,
            in("rcx") if cpuid != 0 { cpuid_copy } else { 0 },
            in("r8") delta,
            in("r9") trampoline,
            options(noreturn)
        )
    }
}
