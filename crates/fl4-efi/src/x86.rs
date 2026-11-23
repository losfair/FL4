//! Long-mode handoff for x86 guests. Firmware handles #VC until boot
//! services exit. The kernel takes over with its own private page tables.
use super::*;

const SNP_BLOB: Guid = Guid(
    0x067b_1f5f,
    0xcf26,
    0x44c5,
    [0x85, 0x54, 0x93, 0xd7, 0x77, 0x91, 0x2d, 0x42],
);
const GOP: Guid = Guid(
    0x9042_a9de,
    0x23dc,
    0x4a38,
    [0x96, 0xfb, 0x7a, 0xde, 0xd0, 0x80, 0x51, 0x6a],
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
/// FL4's Multiboot 2 tag for the TPM event log copy: physical address,
/// size, flags (the kernel's mboot.rs).
const MB2_TAG_TPM_EVENT_LOG: u32 = 0x464c_3401;
/// The same for the confidential-computing event log.
const MB2_TAG_CC_EVENT_LOG: u32 = 0x464c_3402;
/// A TDX guest's AP wakeup page (the kernel's mboot.rs): its address.
const MB2_TAG_TDX_AP_PAGE: u32 = 0x464c_3403;

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

/// A page below 4 GiB, executable in firmware's page tables as well as
/// the loader's (AllocateMaxAddress, EfiLoaderCode).
fn alloc_code_page() -> u64 {
    let mut address = TOP - 1;
    if (bs().allocate_pages)(1, 1, 1, &mut address) != SUCCESS {
        fail("cannot allocate low boot trampoline");
    }
    address
}

// The same for firmware in five-level paging (a TD with a 52-bit GPA width).
// CR4.LA57 changes only with paging off, from a 32-bit code segment, so this
// leaves long mode and comes back on the kernel's four-level tables. What it
// needs is in its own page, as the upper register halves do not survive.
core::arch::global_asm!(
    ".section .text",
    ".code64",
    "fl4_handoff_la57:",
    // PCIDE and CET must be off to clear CR0.PG.
    "movq %cr4, %rax",
    "andq $~((1 << 17) | (1 << 23)), %rax",
    "movq %rax, %cr4",
    "lgdtq la57_gdt_ptr(%rip)",
    "leaq fl4_handoff_la57(%rip), %rbx",
    "ljmpl *la57_to_compat(%rip)",
    ".code32",
    "fl4_handoff_la57_compat:",
    "movl $0x18, %eax",
    "movl %eax, %ds",
    "movl %eax, %es",
    "movl %eax, %ss",
    "movl %cr0, %eax",
    "andl $0x7fffffff, %eax",
    "movl %eax, %cr0",
    "movl %cr4, %eax",
    "andl $~(1 << 12), %eax",
    "movl %eax, %cr4",
    "movl (la57_cr3 - fl4_handoff_la57)(%ebx), %eax",
    "movl %eax, %cr3",
    "movl %cr0, %eax",
    "orl $0x80000000, %eax",
    "movl %eax, %cr0",
    "ljmpl *(la57_to_long - fl4_handoff_la57)(%ebx)",
    ".code64",
    "fl4_handoff_la57_long:",
    "movq la57_rdi(%rip), %rdi",
    "movq la57_rsi(%rip), %rsi",
    "movq la57_rdx(%rip), %rdx",
    "movq la57_rcx(%rip), %rcx",
    "movq la57_r8(%rip), %r8",
    "movq la57_entry(%rip), %r10",
    "jmp *%r10",
    ".p2align 3",
    "fl4_handoff_la57_gdt:", // accessed bits set: firmware may map it read-only
    ".quad 0",
    ".quad 0x00cf9b000000ffff", // 0x08 code, 32-bit
    ".quad 0x00af9b000000ffff", // 0x10 code, 64-bit
    ".quad 0x00cf93000000ffff", // 0x18 data
    "fl4_handoff_la57_data:",
    "la57_cr3: .quad 0",
    "la57_rdi: .quad 0",
    "la57_rsi: .quad 0",
    "la57_rdx: .quad 0",
    "la57_rcx: .quad 0",
    "la57_r8: .quad 0",
    "la57_entry: .quad 0",
    "la57_to_compat: .long 0",
    ".short 0x08, 0",
    "la57_to_long: .long 0",
    ".short 0x10, 0",
    "la57_gdt_ptr: .short 4 * 8 - 1",
    ".quad 0",
    "fl4_handoff_la57_end:",
    options(att_syntax),
);

/// The registers the kernel entry takes, and its address.
struct Handoff {
    cr3: u64,
    rdi: u64,
    rsi: u64,
    rdx: u64,
    rcx: u64,
    r8: u64,
    entry: u64,
}

/// Copy the five-level handoff to a page below 4 GiB and fill in its data.
fn handoff_code_la57(h: &Handoff) -> u64 {
    extern "C" {
        static fl4_handoff_la57: u8;
        static fl4_handoff_la57_compat: u8;
        static fl4_handoff_la57_long: u8;
        static fl4_handoff_la57_gdt: u8;
        static fl4_handoff_la57_data: u8;
        static fl4_handoff_la57_end: u8;
    }
    let start = core::ptr::addr_of!(fl4_handoff_la57) as u64;
    let end = core::ptr::addr_of!(fl4_handoff_la57_end) as u64;
    assert!(end - start <= PAGE);
    let address = alloc_code_page();
    write(address, unsafe { core::slice::from_raw_parts(start as *const u8, (end - start) as usize) });
    let at = |sym: *const u8| address + (sym as u64 - start);
    let data = at(core::ptr::addr_of!(fl4_handoff_la57_data));
    for (i, v) in [h.cr3, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.entry].into_iter().enumerate() {
        write(data + 8 * i as u64, &v.to_le_bytes());
    }
    // After those seven words: the two far pointers' offsets, and the GDT
    // pointer's base past its two limit bytes.
    write(data + 56, &(at(core::ptr::addr_of!(fl4_handoff_la57_compat)) as u32).to_le_bytes());
    write(data + 64, &(at(core::ptr::addr_of!(fl4_handoff_la57_long)) as u32).to_le_bytes());
    write(data + 72 + 2, &at(core::ptr::addr_of!(fl4_handoff_la57_gdt)).to_le_bytes());
    address
}

fn handoff_code() -> u64 {
    extern "C" {
        static fl4_handoff: u8;
        static fl4_handoff_end: u8;
    }
    let start = core::ptr::addr_of!(fl4_handoff) as u64;
    let end = core::ptr::addr_of!(fl4_handoff_end) as u64;
    let address = alloc_code_page();
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

/// Whether this is an Intel TDX guest: only a guest that is not SEV can be
/// a TD. A TD measures into its RTMRs and CC event log and ignores any TPM.
pub(super) fn is_tdx() -> bool {
    sev().0 == 0 && tdx_shared_mask() != 0
}

/// An Intel TDX guest's shared-page bit, the top bit of its guest physical
/// address width, or 0 outside a TD. CPUID leaf 21H comes from the TDX
/// module in a TD; a non-TD forging it faults on TDCALL, which is no worse
/// than the hypervisor refusing to run the guest.
fn tdx_shared_mask() -> u64 {
    use core::arch::x86_64::__cpuid_count as cpuid;
    if cpuid(0, 0).eax < 0x21 {
        return 0;
    }
    let l = cpuid(0x21, 0);
    if (l.ebx, l.edx, l.ecx) != (u32::from_le_bytes(*b"Inte"), u32::from_le_bytes(*b"lTDX"), u32::from_le_bytes(*b"    ")) {
        return 0;
    }
    let (status, rcx): (u64, u64);
    unsafe {
        asm!(
            ".byte 0x66, 0x0f, 0x01, 0xcc", // TDCALL
            inlateout("rax") 1u64 => status, // TDG.VP.INFO
            lateout("rcx") rcx,
            lateout("rdx") _,
            lateout("r8") _,
            lateout("r9") _,
            lateout("r10") _,
            lateout("r11") _,
            options(nostack),
        );
    }
    let gpaw = rcx & 0x3f;
    if status != 0 || !matches!(gpaw, 48 | 52) {
        fail("invalid TDX guest information");
    }
    1 << (gpaw - 1)
}

#[repr(C)]
struct Gop {
    query_mode: usize,
    set_mode: usize,
    blt: usize,
    mode: *const GopMode,
}

#[repr(C)]
struct GopMode {
    max_mode: u32,
    mode: u32,
    info: *const GopInfo,
    info_size: usize,
    base: u64,
    size: usize,
}

#[repr(C)]
struct GopInfo {
    version: u32,
    width: u32,
    height: u32,
    format: u32,
    masks: [u32; 4],
    per_line: u32,
}

/// The framebuffer tag for the mode firmware left the display in, as
/// GRUB passes it: no mode is set, and a machine without a usable linear
/// display boots without the tag.
fn framebuffer() -> Option<[u8; gop::LEN]> {
    let mut gop = core::ptr::null_mut();
    if (bs().locate_protocol)(&GOP, core::ptr::null(), &mut gop) != SUCCESS || gop.is_null() {
        return None;
    }
    let mode = unsafe { (*(gop as *const Gop)).mode };
    if mode.is_null() || unsafe { (*mode).info.is_null() } {
        return None;
    }
    let (mode, info) = unsafe { (&*mode, &*(*mode).info) };
    let tag = gop::tag(
        mode.base,
        mode.size as u64,
        info.width,
        info.height,
        info.format,
        info.per_line,
    )?;
    say!(
        "fl4-efi: GOP framebuffer {}x{} at {:#x}",
        info.width,
        info.height,
        mode.base
    );
    Some(tag)
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
    x86_mmap::regions(map, stride, cpuid, secrets, |(base, bytes, kind)| {
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
    })?;
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

/// The handoff's page tables. `private` is SEV's C-bit, on everything the
/// kernel runs from; `shared` is TDX's S-bit, on the shared window's leaves
/// only (one of them is 0).
fn tables(pa: u64, delta: u64, private: u64, shared: u64, end: u64) {
    let t = |i| pa + i * PAGE;
    let e = |i, slot, value: u64| write(t(i) + slot * 8, &value.to_le_bytes());
    let ptr = |i| t(i) | private | 3;
    e(0, 0, ptr(1));
    e(0, 511, ptr(2));
    if private | shared != 0 {
        e(0, 510, ptr(9));
        for g in 0..4 {
            e(9, g, (g << 30) | shared | 0x83);
        }
    }
    for g in 0..4 {
        e(1, g, ptr(3 + g));
        e(2, g, ptr(3 + g));
        for j in 0..512 {
            e(3 + g, j, ((g * 512 + j) * HUGE) | private | 0x83);
        }
    }
    // The kernel's link-time physical offsets remain its high-half virtual
    // offsets even when firmware allocates the image elsewhere. delta is
    // 2 MiB aligned so these mappings use large pages as well.
    e(2, (KERNEL_OFFSET >> 30) & 511, ptr(7));
    e(2, 511, ptr(8));
    for (i, off) in (0..end).step_by(HUGE as usize).enumerate() {
        let slot = (KERNEL_OFFSET >> 21 & 511) + i as u64;
        e(7 + slot / 512, slot % 512, (delta + off) | private | 0x83);
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

/// The files from the options extend RTMR[2] in a TD (`measure`), and TPM
/// PCR 9 when there is a TPM outside one: a TD ignores any TPM.
fn boot_files<'a>(li: &LoadedImage, opts: &'a Words, measure: bool) -> ([BootFile<'a>; 9], usize) {
    let mut files = [(0, 0, &[][..]); 9];
    let mut n = 1;
    for opt in opts.iter() {
        if let Some(path) = opt.strip_prefix(b"rootserver=") {
            let (pa, len) = read_file(li, path);
            if measure {
                ccel::measure_file(b"rootserver", path, pa, len);
            } else {
                tcg2::measure_file(b"rootserver", path, pa, len).unwrap_or_else(|e| fail(e));
            }
            files[0] = (pa, len, path);
        } else if let Some(path) = opt.strip_prefix(b"module=") {
            if n == files.len() {
                fail("too many boot modules");
            }
            let (pa, len) = read_file(li, path);
            if measure {
                ccel::measure_file(b"module", path, pa, len);
            } else {
                tcg2::measure_file(b"module", path, pa, len).unwrap_or_else(|e| fail(e));
            }
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
    let measure = is_tdx();
    let (files, n) = boot_files(li, &opts, measure);
    boot(image, embedded::KERNEL, &files[..n], c"")
}

pub(super) fn boot(image: Handle, kernel: &[u8], files: &[BootFile<'_>], cmdline: &core::ffi::CStr) -> ! {
    let cr4: u64;
    unsafe { asm!("mov {}, cr4", out(reg) cr4) };
    let (mask, cpuid, secrets) = sev();
    let shared = if mask == 0 { tdx_shared_mask() } else { 0 };
    // Only a TD goes back to four levels: its firmware picks five for a
    // 52-bit GPA width, which four-level tables address just as well.
    let la57 = cr4 & (1 << 12) != 0;
    if la57 && shared == 0 {
        fail("firmware uses five-level paging");
    }
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
    // The TPM event log goes after the files, with room for the events
    // ExitBootServices adds. A TD ignores any TPM: its measurements are
    // its RTMRs, whose CC event log goes after the TPM's place instead.
    // It first poisons the TPM's PCRs, so that none looks like a clean
    // boot's (it measured no boot file into PCR 9).
    if shared != 0 {
        tcg2::poison().unwrap_or_else(|e| fail(e));
    }
    let tpm = if shared == 0 { tcg2::collect() } else { None };
    let tpm_cap = tpm.as_ref().map_or(0, |t| t.capacity().div_ceil(PAGE) * PAGE);
    let cc = if shared != 0 { ccel::collect() } else { None };
    let cc_cap = cc.as_ref().map_or(0, |t| t.capacity().div_ceil(PAGE) * PAGE);
    let len = end + TABLE_BYTES + INFO_BYTES + 2 * PAGE + files_len + tpm_cap + cc_cap;
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
    tables(root, delta, mask, shared, end);
    let mut info = Info {
        base: root + TABLE_BYTES,
        used: 8,
    };
    // Multiboot 2 boot command line (tag type 1), NUL included. At most a
    // page, so the tags after it still fit.
    if !cmdline.is_empty() {
        let bytes = cmdline.to_bytes_with_nul();
        if bytes.len() as u64 > PAGE {
            fail("kernel command line too long");
        }
        write(info.tag(1, bytes.len() as u64), bytes);
    }
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
    let tpm_dst = dst;
    if let Some(t) = &tpm {
        t.copy_main(tpm_dst);
    }
    let cc_dst = tpm_dst + tpm_cap;
    if let Some(t) = &cc {
        t.copy_main(cc_dst);
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
    // Not for SEV or TDX guests: the framebuffer is device memory whose
    // shared or private status firmware does not state, and the kernel's
    // console refuses it under SNP and TDX (fbcon::usable) as well.
    if mask | shared == 0 {
        if let Some(fb) = framebuffer() {
            write(info.tag(8, gop::LEN as u64), &fb);
        }
    }
    // Its size and flags are final after ExitBootServices (below).
    let tpm_tag_pa = tpm.as_ref().map(|t| {
        let (size, flags) = t.record();
        let p = info.tag(MB2_TAG_TPM_EVENT_LOG, 24);
        write(p, &tpm_dst.to_le_bytes());
        write(p + 8, &size.to_le_bytes());
        write(p + 16, &flags.to_le_bytes());
        p
    });
    let cc_tag_pa = cc.as_ref().map(|t| {
        let (size, flags) = t.record();
        let p = info.tag(MB2_TAG_CC_EVENT_LOG, 24);
        write(p, &cc_dst.to_le_bytes());
        write(p + 8, &size.to_le_bytes());
        write(p + 16, &flags.to_le_bytes());
        p
    });
    // Firmware starts a TD's APs on its own page tables: the kernel's AP
    // trampoline goes on a page they map executable.
    if shared != 0 {
        let page = alloc_code_page();
        write(info.tag(MB2_TAG_TDX_AP_PAGE, 8), &page.to_le_bytes());
    }
    let trampoline = if la57 {
        handoff_code_la57(&Handoff {
            cr3: root,
            rdi: MB_MAGIC,
            rsi: info.base,
            rdx: mask,
            rcx: if cpuid != 0 { cpuid_copy } else { 0 },
            r8: delta,
            entry,
        })
    } else {
        handoff_code()
    };
    say!("fl4-efi: entering x86_64 kernel, SEV-SNP {}, TDX {}", cpuid != 0, shared != 0);
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
    let capacity = x86_mmap::capacity(size, stride).unwrap_or_else(|| fail("GetMemoryMap"));
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
        if !x86_mmap::layout_ok(size, stride, capacity) {
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
    // No boot services: firmware's identity map and the final events
    // table (ACPI NVS) are still there.
    if let (Some(t), Some(p)) = (&tpm, tpm_tag_pa) {
        let (size, flags) = t.finish(tpm_dst);
        write(p + 8, &size.to_le_bytes());
        write(p + 16, &flags.to_le_bytes());
    }
    if let (Some(t), Some(p)) = (&cc, cc_tag_pa) {
        let (size, flags) = t.finish(cc_dst);
        write(p + 8, &size.to_le_bytes());
        write(p + 16, &flags.to_le_bytes());
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
