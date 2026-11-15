//! seL4 EPT objects. On AMD the same objects contain nested page tables.
use crate::capability::{mask_vm_rights, Cap, FrameSize, Rights, VM_KERNEL_ONLY, VM_READ_ONLY};
use crate::error::{
    illegal, invalid_arg, invalid_cap, truncated, Exc, KResult, LookupFault, SysError,
};
use crate::layout;
use crate::machine::{Arch, Store};
use crate::obj::Slot;
use crate::{cdt, msg, sched, vspace};
use fl4_abi::label;

const ADDRESS: u64 = 0x000f_ffff_ffff_f000;
const LIMIT: u64 = 1 << 47;
const CORES: u64 = 510 * 8;

pub fn find<S: Store>(s: &S, asid: u64) -> Result<u64, LookupFault> {
    let r = vspace::find_asid(s, asid)?;
    if r & 1 == 0 {
        Err(LookupFault::InvalidRoot)
    } else {
        Ok(r & !1)
    }
}
pub fn root<S: Store>(s: &S, c: Cap) -> KResult<(u64, u64)> {
    match c {
        Cap::Ept {
            ptr,
            level: 0,
            mapped: true,
            asid,
            ..
        } => {
            let r = find(s, asid)
                .map_err(|lf| Exc::Sys(SysError::FailedLookup { source: false, lf }))?;
            if r != ptr {
                return invalid_cap(1);
            }
            Ok((r, asid))
        }
        _ => invalid_cap(1),
    }
}
pub fn mark_core<S: Store>(s: &mut S, root: u64) {
    let cpu = s.cur_cpu();
    let addr = root.wrapping_add(CORES).wrapping_add((cpu / 32) * 8);
    let old = s.read(addr);
    s.write(addr, old | (1 << (32 + cpu % 32)));
}
pub fn invalidate<S: Store, A: Arch>(s: &mut S, a: &mut A, root: u64) {
    let mask = (s.read(root.wrapping_add(CORES)) >> 32)
        | (s.read(root.wrapping_add(CORES + 8)) & 0xffff_ffff_0000_0000);
    a.invalidate_ept(root, mask);
    // Keep a conservative history for the root's lifetime. Invalidation
    // changes no page-table memory; later flushes still reach every core
    // that could retain this root. Retyping the object clears the history.
}
pub fn lookup<S: Store>(s: &S, root: u64, gpa: u64, level: u64) -> Result<u64, LookupFault> {
    let mut table = root;
    let mut shift = 39;
    while shift > level && shift >= 21 {
        let e = s.read(table.wrapping_add(((gpa >> (shift & 63)) & 511) * 8));
        if e & 1 == 0 || e & 128 != 0 {
            return Err(LookupFault::MissingCapability { bits_left: shift });
        }
        table = layout::pptr(e & ADDRESS);
        shift -= 9;
    }
    Ok(table.wrapping_add(((gpa >> (level & 63)) & 511) * 8))
}
fn slot<S: Store>(s: &S, root: u64, gpa: u64, level: u64) -> KResult<u64> {
    lookup(s, root, gpa, level).map_err(|lf| Exc::Sys(SysError::FailedLookup { source: false, lf }))
}
fn memory_type(attr: u64) -> u64 {
    if matches!(attr, 0 | 1 | 4 | 6) {
        attr
    } else {
        6
    }
}
fn frame_entry(amd: bool, ptr: u64, rights: u64, attr: u64, large: bool) -> u64 {
    if rights == VM_KERNEL_ONLY {
        return 0;
    }
    let write = if rights == VM_READ_ONLY { 0 } else { 2 };
    let ps = if large { 128 } else { 0 };
    if amd {
        // PAT is the same fixed palette as native paging (UC, WC, WT, WP, WB).
        let pat = match memory_type(attr) {
            0 => 3,
            1 => 4,
            4 => 1,
            5 => 5,
            _ => 0,
        };
        let cache =
            ((pat & 1) << 3) | ((pat & 2) << 3) | ((pat & 4) << (if large { 10 } else { 5 }));
        layout::paddr(ptr) | 1 | write | 4 | ps | cache
    } else {
        layout::paddr(ptr) | 1 | write | 4 | ps | (memory_type(attr) << 3)
    }
}

#[allow(clippy::too_many_arguments)]
pub fn map_frame<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    length: u64,
    cap: Cap,
    dest: Slot,
    buf: u64,
    ex: &[Slot; 3],
) -> KResult<()> {
    if length < 3 || ex[0].is_null() {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    // seL4 rounds small frames to a page before testing large alignment.
    let gpa = msg::syscall_arg(s, ct, buf, 0) & !4095;
    if gpa >= LIMIT {
        return invalid_arg(0);
    }
    let mask = msg::syscall_arg(s, ct, buf, 1);
    let attr = msg::syscall_arg(s, ct, buf, 2);
    let (ptr, size, rights, device) = match cap {
        Cap::Frame {
            mapped: false,
            ptr,
            size,
            rights,
            is_device,
            ..
        } => (ptr, size, rights, is_device),
        _ => return invalid_cap(0),
    };
    let (r, asid) = root(s, ex[0].cap(s))?;
    if gpa & ((1 << size.bits()) - 1) != 0 {
        return Err(Exc::Sys(SysError::AlignmentError));
    }
    if matches!(size, FrameSize::Huge) {
        return invalid_cap(0);
    }
    let e = slot(s, r, gpa, size.bits())?;
    if s.read(e) & 1 != 0 {
        return Err(Exc::Sys(SysError::DeleteFirst));
    }
    let val = frame_entry(
        a.virtualization() == 2,
        ptr,
        mask_vm_rights(rights, Rights::from_word(mask)),
        attr,
        matches!(size, FrameSize::Large),
    );
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    dest.set_cap(
        s,
        Cap::Frame {
            ptr,
            size,
            rights,
            is_device: device,
            mapped: true,
            is_ept: true,
            asid,
            vaddr: gpa,
        },
    );
    s.write(e, val);
    Ok(())
}
pub fn unmap<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    asid: u64,
    gpa: u64,
    ptr: u64,
    level: u64,
    table: bool,
) {
    let r = match find(s, asid) {
        Ok(r) => r,
        Err(_) => return,
    };
    let addr = match lookup(s, r, gpa, level) {
        Ok(x) => x,
        Err(_) => return,
    };
    let e = s.read(addr);
    let large = if !table && level > 12 { true } else { false };
    let mask = if large {
        ADDRESS & !((1u64 << (level & 63)) - 1)
    } else {
        ADDRESS
    };
    if e & 1 == 0 || (level != 12 && (e & 128 != 0) != large) || (e & mask) != layout::paddr(ptr) {
        return;
    }
    s.write(addr, 0);
    invalidate(s, a, r);
}
pub fn finalise<S: Store, A: Arch>(s: &mut S, a: &mut A, c: Cap) {
    if let Cap::Ept {
        ptr,
        level,
        mapped: true,
        asid,
        vaddr,
    } = c
    {
        if level == 0 {
            vspace::delete_asid(s, a, asid, ptr);
        } else {
            unmap(s, a, asid, vaddr, ptr, level, true);
        }
    }
}
pub fn decode<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lbl: u64,
    length: u64,
    cap: Cap,
    dest: Slot,
    buf: u64,
    ex: &[Slot; 3],
) -> KResult<()> {
    let (ptr, level, mapped, asid, gpa) = match cap {
        Cap::Ept {
            ptr,
            level,
            mapped,
            asid,
            vaddr,
        } if level != 0 => (ptr, level, mapped, asid, vaddr),
        _ => return illegal(),
    };
    let (map, unmap_label) = if level == 39 {
        (label::X86EPTPDPTMap, label::X86EPTPDPTUnmap)
    } else if level == 30 {
        (label::X86EPTPDMap, label::X86EPTPDUnmap)
    } else {
        (label::X86EPTPTMap, label::X86EPTPTUnmap)
    };
    let ct = sched::cur_thread(s);
    if lbl == unmap_label {
        if !cdt::is_final_capability(s, dest) {
            return Err(Exc::Sys(SysError::RevokeFirst));
        }
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        if mapped {
            unmap(s, a, asid, gpa, ptr, level, true);
            s.zero(ptr, 4096);
        }
        dest.set_cap(
            s,
            Cap::Ept {
                ptr,
                level,
                mapped: false,
                asid: 0,
                vaddr: 0,
            },
        );
    } else if lbl == map {
        if length < 2 || ex[0].is_null() {
            return truncated();
        }
        if mapped {
            return invalid_cap(0);
        }
        let gpa = msg::syscall_arg(s, ct, buf, 0) & !((1u64 << (level & 63)) - 1);
        if gpa >= LIMIT {
            return invalid_arg(0);
        }
        let (r, asid) = root(s, ex[0].cap(s))?;
        let e = slot(s, r, gpa, level)?;
        if s.read(e) & 1 != 0 {
            return Err(Exc::Sys(SysError::DeleteFirst));
        }
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        s.write(e, layout::paddr(ptr) | 7);
        dest.set_cap(
            s,
            Cap::Ept {
                ptr,
                level,
                mapped: true,
                asid,
                vaddr: gpa,
            },
        );
    } else {
        return illegal();
    }
    Ok(())
}
