//! The AArch64 ELF images the loader places (the kernel built in, the root
//! task from the boot volume): checking them before anything is copied,
//! as the x86_64 kernel's `elf.rs` does (seL4 `elf_checkFile` and
//! `load_boot_module`). Pure functions over the image's bytes, so they are
//! host-tested here.

const PAGE: u64 = 4096;
const EHDR_SIZE: usize = 64;
const PHDR_SIZE: usize = 56;
const PT_LOAD: u32 = 1;
const EM_AARCH64: u16 = 183;

/// Where a checked image goes: its loadable segments cover `[v_start,
/// v_end)` (page aligned), and `entry` lies inside them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub v_start: u64,
    pub v_end: u64,
    pub entry: u64,
}

impl Layout {
    pub fn size(&self) -> u64 {
        self.v_end - self.v_start
    }
}

/// A loadable segment with memory bytes: (file offset, vaddr, file bytes,
/// memory bytes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Segment {
    pub offset: u64,
    pub vaddr: u64,
    pub filesz: u64,
    pub memsz: u64,
}

fn rd16(b: &[u8], o: usize) -> u16 {
    u16::from_le_bytes([b[o], b[o + 1]])
}

fn rd32(b: &[u8], o: usize) -> u32 {
    u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]])
}

fn rd64(b: &[u8], o: usize) -> u64 {
    let mut w = [0u8; 8];
    w.copy_from_slice(&b[o..o + 8]);
    u64::from_le_bytes(w)
}

/// The program headers' place, if they lie inside the image.
fn headers(elf: &[u8]) -> Option<(usize, usize, usize)> {
    if elf.len() < EHDR_SIZE || &elf[0..4] != b"\x7fELF" || elf[4] != 2 || elf[5] != 1 || rd16(elf, 18) != EM_AARCH64 {
        return None;
    }
    let phoff = rd64(elf, 32);
    let phentsize = rd16(elf, 54) as u64;
    let phnum = rd16(elf, 56) as u64;
    let len = elf.len() as u64;
    if phentsize < PHDR_SIZE as u64 || phnum == 0 || phoff > len || phnum * phentsize > len - phoff {
        return None;
    }
    Some((phoff as usize, phentsize as usize, phnum as usize))
}

/// Every loadable segment with memory bytes, of an image `check` accepted
/// (others yield nothing).
pub fn segments(elf: &[u8]) -> impl Iterator<Item = Segment> + '_ {
    let (phoff, phentsize, phnum) = headers(elf).unwrap_or((0, 0, 0));
    (0..phnum).filter_map(move |i| {
        let ph = phoff + i * phentsize;
        if rd32(elf, ph) != PT_LOAD {
            return None;
        }
        let s = Segment { offset: rd64(elf, ph + 8), vaddr: rd64(elf, ph + 16), filesz: rd64(elf, ph + 32), memsz: rd64(elf, ph + 40) };
        (s.memsz != 0).then_some(s)
    })
}

/// Check an AArch64 ELF64 image: the headers and every loadable segment's
/// file bytes lie inside it, no segment has more file than memory bytes
/// or wraps, the segments (those with memory bytes) lie in `[v_min,
/// v_limit)` and the entry point inside them.
pub fn check(elf: &[u8], v_min: u64, v_limit: u64) -> Option<Layout> {
    let (phoff, phentsize, phnum) = headers(elf)?;
    let len = elf.len() as u64;
    let mut lo = u64::MAX;
    let mut hi = 0;
    for i in 0..phnum {
        let ph = phoff + i * phentsize;
        if rd32(elf, ph) != PT_LOAD {
            continue;
        }
        let offset = rd64(elf, ph + 8);
        let vaddr = rd64(elf, ph + 16);
        let filesz = rd64(elf, ph + 32);
        let memsz = rd64(elf, ph + 40);
        if offset > len || filesz > len - offset || filesz > memsz {
            return None;
        }
        let end = vaddr.checked_add(memsz)?;
        if memsz > 0 {
            lo = lo.min(vaddr);
            hi = hi.max(end);
        }
    }
    if lo >= hi || lo < v_min || hi > v_limit {
        return None;
    }
    let v_start = lo & !(PAGE - 1);
    let v_end = hi.checked_add(PAGE - 1)? & !(PAGE - 1);
    let entry = rd64(elf, 24);
    if entry < lo || entry >= hi {
        return None;
    }
    Some(Layout { v_start, v_end, entry })
}

/// Copy the image `check` accepted as `l` into `dest` (its `l.size()`
/// bytes, for `l.v_start` on): zero it, then copy each loadable segment's
/// file bytes to their place.
pub fn load(elf: &[u8], l: &Layout, dest: &mut [u8]) {
    dest.fill(0);
    for s in segments(elf) {
        let at = (s.vaddr - l.v_start) as usize;
        let n = s.filesz as usize;
        let from = s.offset as usize;
        dest[at..at + n].copy_from_slice(&elf[from..from + n]);
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use std::vec::Vec;

    /// An image with one PT_LOAD per (offset, vaddr, filesz, memsz) and
    /// the file bytes `fill`.
    fn image(entry: u64, segs: &[(u64, u64, u64, u64)], size: usize) -> Vec<u8> {
        let mut e = std::vec![0u8; size.max(EHDR_SIZE + segs.len() * PHDR_SIZE)];
        e[0..4].copy_from_slice(b"\x7fELF");
        e[4] = 2;
        e[5] = 1;
        e[18..20].copy_from_slice(&EM_AARCH64.to_le_bytes());
        e[24..32].copy_from_slice(&entry.to_le_bytes());
        e[32..40].copy_from_slice(&(EHDR_SIZE as u64).to_le_bytes());
        e[54..56].copy_from_slice(&(PHDR_SIZE as u16).to_le_bytes());
        e[56..58].copy_from_slice(&(segs.len() as u16).to_le_bytes());
        for (i, &(off, va, fs, ms)) in segs.iter().enumerate() {
            let p = EHDR_SIZE + i * PHDR_SIZE;
            e[p..p + 4].copy_from_slice(&PT_LOAD.to_le_bytes());
            e[p + 8..p + 16].copy_from_slice(&off.to_le_bytes());
            e[p + 16..p + 24].copy_from_slice(&va.to_le_bytes());
            e[p + 32..p + 40].copy_from_slice(&fs.to_le_bytes());
            e[p + 40..p + 48].copy_from_slice(&ms.to_le_bytes());
        }
        e
    }

    const TOP: u64 = 0x0000_8000_0000_0000;

    #[test]
    fn a_good_image_loads_its_segments_in_place() {
        let mut e = image(0x40_0010, &[(0x200, 0x40_0000, 0x20, 0x30), (0x220, 0x40_2008, 8, 0x1000), (0, 0x10, 0, 0)], 0x300);
        for (i, b) in e[0x200..0x228].iter_mut().enumerate() {
            *b = i as u8 + 1;
        }
        let l = check(&e, 0, TOP).unwrap();
        // The empty segment does not pull the start down to 0x10.
        assert_eq!(l, Layout { v_start: 0x40_0000, v_end: 0x40_4000, entry: 0x40_0010 });
        let mut dest = std::vec![0xffu8; l.size() as usize];
        load(&e, &l, &mut dest);
        assert_eq!(&dest[..0x20], &e[0x200..0x220]);
        assert!(dest[0x20..0x2008].iter().all(|&b| b == 0));
        assert_eq!(&dest[0x2008..0x2010], &e[0x220..0x228]);
        assert!(dest[0x2010..].iter().all(|&b| b == 0));
    }

    #[test]
    fn malformed_images_are_refused() {
        let ok = |segs: &[(u64, u64, u64, u64)], entry: u64| check(&image(entry, segs, 0x300), 0, TOP);
        assert!(ok(&[(0x200, 0x40_0000, 0x20, 0x30)], 0x40_0000).is_some());
        // More file than memory bytes: the copy would overrun the
        // allocation, which is sized from memory bytes.
        assert_eq!(ok(&[(0x200, 0x40_0000, 0x40, 0x30)], 0x40_0000), None);
        // File bytes beyond the image, or an offset that wraps.
        assert_eq!(ok(&[(0x2f0, 0x40_0000, 0x20, 0x30)], 0x40_0000), None);
        assert_eq!(ok(&[(u64::MAX - 8, 0x40_0000, 0x20, 0x30)], 0x40_0000), None);
        // Memory that wraps, or reaches past the limit.
        assert_eq!(ok(&[(0x200, u64::MAX - 0x10, 0x20, 0x30)], 0x40_0000), None);
        assert_eq!(ok(&[(0x200, TOP - 0x10, 0x20, 0x30)], TOP - 0x10), None);
        assert!(ok(&[(0x200, TOP - 0x30, 0x20, 0x30)], TOP - 0x30).is_some());
        // An entry point outside the segments, or no segment at all.
        assert_eq!(ok(&[(0x200, 0x40_0000, 0x20, 0x30)], 0x40_0030), None);
        assert_eq!(ok(&[(0x200, 0x40_0000, 0, 0)], 0x40_0000), None);
        // Below the lower bound (the kernel's KERNEL_VBASE).
        assert_eq!(check(&image(0x40_0000, &[(0x200, 0x40_0000, 0x20, 0x30)], 0x300), 0x40_1000, TOP), None);
        // Program headers out of the image, or of the wrong machine.
        let mut e = image(0x40_0000, &[(0x200, 0x40_0000, 0x20, 0x30)], 0x300);
        e[32..40].copy_from_slice(&0x2f0u64.to_le_bytes());
        assert_eq!(check(&e, 0, TOP), None);
        let mut e = image(0x40_0000, &[(0x200, 0x40_0000, 0x20, 0x30)], 0x300);
        e[18] = 0x3e;
        assert_eq!(check(&e, 0, TOP), None);
        assert_eq!(check(&e[..40], 0, TOP), None);
    }
}
