//! Capabilities. A slot stores a capability as two words in FL4's own
//! encoding (capability layout is not part of the API); the kernel works
//! on the decoded `Cap`.

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FrameSize {
    Small,
    Large,
    Huge,
}

impl FrameSize {
    pub fn bits(self) -> u64 {
        match self {
            FrameSize::Small => 12,
            FrameSize::Large => 21,
            FrameSize::Huge => 30,
        }
    }
    fn code(self) -> u64 {
        match self {
            FrameSize::Small => 0,
            FrameSize::Large => 1,
            FrameSize::Huge => 2,
        }
    }
    fn from_code(c: u64) -> FrameSize {
        if c == 1 {
            FrameSize::Large
        } else if c == 2 {
            FrameSize::Huge
        } else {
            FrameSize::Small
        }
    }
}

/// x86 VM rights of a frame capability (seL4's vm_rights_t).
pub const VM_KERNEL_ONLY: u64 = 1;
pub const VM_READ_ONLY: u64 = 2;
pub const VM_READ_WRITE: u64 = 3;

/// Zombie type for a TCB (otherwise the type is the CNode radix).
pub const ZOMBIE_TCB: u64 = 65;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Cap {
    Null,
    Untyped { ptr: u64, size_bits: u64, free_index: u64, is_device: bool },
    Endpoint { ptr: u64, badge: u64, send: bool, recv: bool, grant: bool, grant_reply: bool },
    Notification { ptr: u64, badge: u64, send: bool, recv: bool },
    Reply { ptr: u64, grant: bool },
    CNode { ptr: u64, radix: u64, guard_size: u64, guard: u64 },
    Thread { ptr: u64 },
    IrqControl,
    IrqHandler { irq: u64 },
    Zombie { ptr: u64, ztype: u64, number: u64 },
    Domain,
    SchedContext { ptr: u64, size_bits: u64 },
    SchedControl { cpu: u64 },
    Frame { ptr: u64, size: FrameSize, rights: u64, is_device: bool, mapped: bool, is_ept: bool, asid: u64, vaddr: u64 },
    PageTable { ptr: u64, mapped: bool, asid: u64, vaddr: u64 },
    PageDirectory { ptr: u64, mapped: bool, asid: u64, vaddr: u64 },
    Pdpt { ptr: u64, mapped: bool, asid: u64, vaddr: u64 },
    Pml4 { ptr: u64, mapped: bool, asid: u64 },
    Vcpu { ptr: u64 },
    Ept { ptr: u64, level: u64, mapped: bool, asid: u64, vaddr: u64 },
    AsidControl,
    AsidPool { ptr: u64, asid_base: u64 },
    IoPortControl,
    IoPort { first: u64, last: u64, vcpu: u64 },
}

const PTR_MASK: u64 = 0x0000_ffff_ffff_ffff;

fn pack_ptr(p: u64) -> u64 {
    p & PTR_MASK
}

fn unpack_ptr(w: u64) -> u64 {
    let p = w & PTR_MASK;
    if p & 0x0000_8000_0000_0000 != 0 {
        p | 0xffff_0000_0000_0000
    } else {
        p
    }
}

fn bit(w: u64, n: u64) -> bool {
    (w >> (n & 63)) & 1 != 0
}

fn b(v: bool, n: u64) -> u64 {
    if v {
        1u64 << (n & 63)
    } else {
        0
    }
}

/// Mapping caps keep a 20-bit ASID: the low 16 bits above the virtual
/// address in the second word, the high 4 at bit `at` of the first.
fn asid_high(asid: u64, at: u64) -> u64 {
    ((asid >> 16) & 0xf) << (at & 63)
}

fn unpack_asid(w0: u64, at: u64, w1: u64) -> u64 {
    (((w0 >> (at & 63)) & 0xf) << 16) | (w1 >> 48)
}

fn tag(t: u64) -> u64 {
    t << 59
}

impl Cap {
    #[inline(always)]
    pub fn decode(w0: u64, w1: u64) -> Cap {
        let t = w0 >> 59;
        let p = unpack_ptr(w0);
        match t {
            1 => Cap::Untyped { ptr: p, size_bits: (w0 >> 48) & 0x3f, free_index: w1, is_device: bit(w0, 54) },
            2 => Cap::Endpoint {
                ptr: p,
                badge: w1,
                send: bit(w0, 48),
                recv: bit(w0, 49),
                grant: bit(w0, 50),
                grant_reply: bit(w0, 51),
            },
            3 => Cap::Notification { ptr: p, badge: w1, send: bit(w0, 48), recv: bit(w0, 49) },
            4 => Cap::Reply { ptr: p, grant: bit(w0, 48) },
            5 => Cap::CNode {
                ptr: p,
                radix: (w0 >> 48) & 0x3f,
                guard_size: w1 >> 58,
                guard: w1 & 0x03ff_ffff_ffff_ffff,
            },
            6 => Cap::Thread { ptr: p },
            7 => Cap::IrqControl,
            8 => Cap::IrqHandler { irq: w1 },
            9 => Cap::Zombie { ptr: p, ztype: (w0 >> 48) & 0xff, number: w1 },
            10 => Cap::Domain,
            11 => Cap::SchedContext { ptr: p, size_bits: (w0 >> 48) & 0x3f },
            12 => Cap::SchedControl { cpu: w1 },
            13 => Cap::Frame {
                ptr: p,
                size: FrameSize::from_code((w0 >> 48) & 3),
                rights: (w0 >> 50) & 3,
                is_device: bit(w0, 52),
                mapped: bit(w0, 53),
                is_ept: bit(w0, 58),
                asid: unpack_asid(w0, 54, w1),
                vaddr: w1 & PTR_MASK,
            },
            14 => Cap::PageTable { ptr: p, mapped: bit(w0, 48), asid: unpack_asid(w0, 49, w1), vaddr: w1 & PTR_MASK },
            15 => Cap::PageDirectory { ptr: p, mapped: bit(w0, 48), asid: unpack_asid(w0, 49, w1), vaddr: w1 & PTR_MASK },
            16 => Cap::Pdpt { ptr: p, mapped: bit(w0, 48), asid: unpack_asid(w0, 49, w1), vaddr: w1 & PTR_MASK },
            17 => Cap::Pml4 { ptr: p, mapped: bit(w0, 48), asid: w1 },
            18 => Cap::AsidControl,
            19 => Cap::AsidPool { ptr: p, asid_base: w1 },
            22 => Cap::Vcpu { ptr: p },
            23 => Cap::Ept { ptr: p, level: (w0 >> 53) & 0x3f, mapped: bit(w0, 48), asid: unpack_asid(w0, 49, w1), vaddr: w1 & PTR_MASK },
            20 => Cap::IoPortControl,
            21 => Cap::IoPort { first: w1 & 0xffff, last: (w1 >> 16) & 0xffff, vcpu: if w0 & PTR_MASK == 0 { 0 } else { p } },
            _ => Cap::Null,
        }
    }

    pub fn encode(self) -> (u64, u64) {
        match self {
            Cap::Null => (0, 0),
            Cap::Untyped { ptr, size_bits, free_index, is_device } => {
                (tag(1) | pack_ptr(ptr) | ((size_bits & 0x3f) << 48) | b(is_device, 54), free_index)
            }
            Cap::Endpoint { ptr, badge, send, recv, grant, grant_reply } => (
                tag(2) | pack_ptr(ptr) | b(send, 48) | b(recv, 49) | b(grant, 50) | b(grant_reply, 51),
                badge,
            ),
            Cap::Notification { ptr, badge, send, recv } => {
                (tag(3) | pack_ptr(ptr) | b(send, 48) | b(recv, 49), badge)
            }
            Cap::Reply { ptr, grant } => (tag(4) | pack_ptr(ptr) | b(grant, 48), 0),
            Cap::CNode { ptr, radix, guard_size, guard } => (
                tag(5) | pack_ptr(ptr) | ((radix & 0x3f) << 48),
                ((guard_size & 0x3f) << 58) | (guard & 0x03ff_ffff_ffff_ffff),
            ),
            Cap::Thread { ptr } => (tag(6) | pack_ptr(ptr), 0),
            Cap::IrqControl => (tag(7), 0),
            Cap::IrqHandler { irq } => (tag(8), irq),
            Cap::Zombie { ptr, ztype, number } => (tag(9) | pack_ptr(ptr) | ((ztype & 0xff) << 48), number),
            Cap::Domain => (tag(10), 0),
            Cap::SchedContext { ptr, size_bits } => (tag(11) | pack_ptr(ptr) | ((size_bits & 0x3f) << 48), 0),
            Cap::SchedControl { cpu } => (tag(12), cpu),
            Cap::Frame { ptr, size, rights, is_device, mapped, is_ept, asid, vaddr } => (
                tag(13)
                    | pack_ptr(ptr)
                    | (size.code() << 48)
                    | ((rights & 3) << 50)
                    | b(is_device, 52)
                    | b(mapped, 53)
                    | b(is_ept, 58)
                    | asid_high(asid, 54),
                ((asid & 0xffff) << 48) | (vaddr & PTR_MASK),
            ),
            Cap::PageTable { ptr, mapped, asid, vaddr } => {
                (tag(14) | pack_ptr(ptr) | b(mapped, 48) | asid_high(asid, 49), ((asid & 0xffff) << 48) | (vaddr & PTR_MASK))
            }
            Cap::PageDirectory { ptr, mapped, asid, vaddr } => {
                (tag(15) | pack_ptr(ptr) | b(mapped, 48) | asid_high(asid, 49), ((asid & 0xffff) << 48) | (vaddr & PTR_MASK))
            }
            Cap::Pdpt { ptr, mapped, asid, vaddr } => {
                (tag(16) | pack_ptr(ptr) | b(mapped, 48) | asid_high(asid, 49), ((asid & 0xffff) << 48) | (vaddr & PTR_MASK))
            }
            Cap::Pml4 { ptr, mapped, asid } => (tag(17) | pack_ptr(ptr) | b(mapped, 48), asid),
            Cap::AsidControl => (tag(18), 0),
            Cap::AsidPool { ptr, asid_base } => (tag(19) | pack_ptr(ptr), asid_base),
            Cap::Vcpu { ptr } => (tag(22) | pack_ptr(ptr), 0),
            Cap::Ept { ptr, level, mapped, asid, vaddr } => (tag(23) | pack_ptr(ptr) | b(mapped, 48) | asid_high(asid, 49) | ((level & 0x3f) << 53), ((asid & 0xffff) << 48) | (vaddr & PTR_MASK)),
            Cap::IoPortControl => (tag(20), 0),
            Cap::IoPort { first, last, vcpu } => (tag(21) | pack_ptr(vcpu), (first & 0xffff) | ((last & 0xffff) << 16)),
        }
    }

    pub fn is_null(self) -> bool {
        matches!(self, Cap::Null)
    }

    /// seL4's `isArchCap`.
    pub fn is_arch(self) -> bool {
        matches!(
            self,
            Cap::Frame { .. }
                | Cap::PageTable { .. }
                | Cap::PageDirectory { .. }
                | Cap::Pdpt { .. }
                | Cap::Pml4 { .. }
                | Cap::AsidControl
                | Cap::AsidPool { .. }
                | Cap::Vcpu { .. }
                | Cap::Ept { .. }
                | Cap::IoPortControl
                | Cap::IoPort { .. }
        )
    }

    /// The object a capability refers to, for caps that name memory.
    pub fn ptr(self) -> u64 {
        match self {
            Cap::Untyped { ptr, .. }
            | Cap::Endpoint { ptr, .. }
            | Cap::Notification { ptr, .. }
            | Cap::Reply { ptr, .. }
            | Cap::CNode { ptr, .. }
            | Cap::Thread { ptr }
            | Cap::Zombie { ptr, .. }
            | Cap::SchedContext { ptr, .. }
            | Cap::Frame { ptr, .. }
            | Cap::PageTable { ptr, .. }
            | Cap::PageDirectory { ptr, .. }
            | Cap::Pdpt { ptr, .. }
            | Cap::Pml4 { ptr, .. }
            | Cap::Vcpu { ptr }
            | Cap::Ept { ptr, .. }
            | Cap::AsidPool { ptr, .. } => ptr,
            _ => 0,
        }
    }
}

/// `seL4_CapRights_t`: bit 0 write, 1 read, 2 grant, 3 grantReply.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Rights {
    pub write: bool,
    pub read: bool,
    pub grant: bool,
    pub grant_reply: bool,
}

impl Rights {
    pub fn from_word(w: u64) -> Rights {
        Rights { write: w & 1 != 0, read: w & 2 != 0, grant: w & 4 != 0, grant_reply: w & 8 != 0 }
    }
    pub fn all() -> Rights {
        Rights { write: true, read: true, grant: true, grant_reply: true }
    }
}

/// seL4 `maskVMRights`.
pub fn mask_vm_rights(vm: u64, r: Rights) -> u64 {
    if vm == VM_READ_ONLY && r.read {
        VM_READ_ONLY
    } else if vm == VM_READ_WRITE && r.read {
        if r.write {
            VM_READ_WRITE
        } else {
            VM_READ_ONLY
        }
    } else {
        VM_KERNEL_ONLY
    }
}

/// seL4 `maskCapRights`.
pub fn mask_cap_rights(r: Rights, c: Cap) -> Cap {
    match c {
        Cap::Endpoint { ptr, badge, send, recv, grant, grant_reply } => Cap::Endpoint {
            ptr,
            badge,
            send: send && r.write,
            recv: recv && r.read,
            grant: grant && r.grant,
            grant_reply: grant_reply && r.grant_reply,
        },
        Cap::Notification { ptr, badge, send, recv } => {
            Cap::Notification { ptr, badge, send: send && r.write, recv: recv && r.read }
        }
        Cap::Reply { ptr, grant } => Cap::Reply { ptr, grant: grant && r.grant },
        Cap::Frame { ptr, size, rights, is_device, mapped, is_ept, asid, vaddr } => Cap::Frame {
            ptr,
            size,
            rights: mask_vm_rights(rights, r),
            is_device,
            mapped,
            is_ept,
            asid,
            vaddr,
        },
        other => other,
    }
}
