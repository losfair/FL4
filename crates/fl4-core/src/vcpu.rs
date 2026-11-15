//! x86 virtualization policy and seL4/l4h VCPU invocations.
//!
//! Hardware owns a VCPU only while its bound TCB runs. Invocations stall
//! that TCB before touching it. VM exits save state and pending results
//! before servicing remote calls; a stall cannot discard an exit.
use crate::capability::Cap;
use crate::error::{illegal, invalid_arg, truncated, KResult};
use crate::layout::{self, ks, reg, tcb as tl};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::msginfo::MessageInfo;
use crate::obj::{ks_get, ks_set, Ntfn, Slot, Tcb, NTFN_ACTIVE, NTFN_IDLE};
use crate::{sched, smp};
use fl4_abi::label;

// 32 KiB: VMCB, VMCS software image, metadata/registers, I/O bitmap.
pub const SHADOW: u64 = 0x1000;
pub const TCB: u64 = 0x5000;
pub const NEXT: u64 = 0x5008;
pub const PREV: u64 = 0x5010;
pub const XCR0: u64 = 0x5018;
pub const CR2: u64 = 0x5020;
pub const PENDING: u64 = 0x5028;
pub const VALID: u64 = 0x5030;
pub const REGS: u64 = 0x5100;
pub const MSRS: u64 = 0x5180;
pub const EXIT: u64 = 0x5200;
pub const IO: u64 = 0x6000;
pub const NUM_MRS: u64 = 30;
pub const CR4_ALLOWED: u64 = 0x1fff | (1 << 16) | (1 << 17) | (1 << 18) | (1 << 20) | (1 << 21);
pub const CR0_OWNED: u64 = (3 << 29) | (0x3ff << 19) | (1 << 17) | (0x3ff << 6);
pub const EXCEPTIONS: u64 = (1 << 1) | (1 << 17) | (1 << 18);
pub const PIN_ALLOWED: u64 = (1 << 0) | (1 << 3) | (1 << 5);
pub const PRIMARY_ALLOWED: u64 = 0xfbd9_9e8c;
pub const PRIMARY_FORCED: u64 = (1 << 10)
    | (1 << 11)
    | (1 << 19)
    | (1 << 20)
    | (1 << 23)
    | (1 << 25)
    | (1 << 28)
    | (1 << 29)
    | (1 << 31);
pub const SECONDARY_ALLOWED: u64 = (1 << 1)
    | (1 << 2)
    | (1 << 3)
    | (1 << 5)
    | (1 << 6)
    | (1 << 7)
    | (1 << 11)
    | (1 << 12)
    | (1 << 16);
pub const EXIT_FORCED: u64 = (1 << 2) | (1 << 9) | (1 << 18) | (1 << 19) | (1 << 20) | (1 << 21);

pub mod vmx {
    pub const CONTROL_VPID: u64 = 0x00000000;
    pub const GUEST_ES_SELECTOR: u64 = 0x00000800;
    pub const GUEST_CS_SELECTOR: u64 = 0x00000802;
    pub const GUEST_SS_SELECTOR: u64 = 0x00000804;
    pub const GUEST_DS_SELECTOR: u64 = 0x00000806;
    pub const GUEST_FS_SELECTOR: u64 = 0x00000808;
    pub const GUEST_GS_SELECTOR: u64 = 0x0000080A;
    pub const GUEST_LDTR_SELECTOR: u64 = 0x0000080C;
    pub const GUEST_TR_SELECTOR: u64 = 0x0000080E;
    pub const HOST_ES_SELECTOR: u64 = 0x00000C00;
    pub const HOST_CS_SELECTOR: u64 = 0x00000C02;
    pub const HOST_SS_SELECTOR: u64 = 0x00000C04;
    pub const HOST_DS_SELECTOR: u64 = 0x00000C06;
    pub const HOST_FS_SELECTOR: u64 = 0x00000C08;
    pub const HOST_GS_SELECTOR: u64 = 0x00000C0A;
    pub const HOST_TR_SELECTOR: u64 = 0x00000C0C;
    pub const CONTROL_IOA_ADDRESS: u64 = 0x00002000;
    pub const CONTROL_IOB_ADDRESS: u64 = 0x00002002;
    pub const CONTROL_MSR_ADDRESS: u64 = 0x00002004;
    pub const CONTROL_EXIT_MSR_STORE_ADDRESS: u64 = 0x00002006;
    pub const CONTROL_EXIT_MSR_LOAD_ADDRESS: u64 = 0x00002008;
    pub const CONTROL_ENTRY_MSR_LOAD_ADDRESS: u64 = 0x0000200A;
    pub const CONTROL_EXECUTIVE_VMCS_POINTER: u64 = 0x0000200C;
    pub const CONTROL_TSC_OFFSET: u64 = 0x00002010;
    pub const CONTROL_VIRTUAL_APIC_ADDRESS: u64 = 0x00002012;
    pub const CONTROL_APIC_ACCESS_ADDRESS: u64 = 0x00002014;
    pub const CONTROL_EPT_POINTER: u64 = 0x0000201A;
    pub const DATA_GUEST_PHYSICAL: u64 = 0x00002400;
    pub const GUEST_VMCS_LINK_POINTER: u64 = 0x00002800;
    pub const GUEST_VMCS_LINK_POINTER_HIGH: u64 = 0x00002801;
    pub const GUEST_DEBUGCTRL: u64 = 0x00002802;
    pub const GUEST_PAT: u64 = 0x00002804;
    pub const GUEST_EFER: u64 = 0x00002806;
    pub const GUEST_PERF_GLOBAL_CTRL: u64 = 0x00002808;
    pub const GUEST_PDPTE0: u64 = 0x0000280A;
    pub const GUEST_PDPTE1: u64 = 0x0000280C;
    pub const GUEST_PDPTE2: u64 = 0x0000280E;
    pub const GUEST_PDPTE3: u64 = 0x00002810;
    pub const HOST_PAT: u64 = 0x00002C00;
    pub const HOST_EFER: u64 = 0x00002C02;
    pub const HOST_PERF_GLOBAL_CTRL: u64 = 0x00002C04;
    pub const CONTROL_PIN_EXECUTION_CONTROLS: u64 = 0x00004000;
    pub const CONTROL_PRIMARY_PROCESSOR_CONTROLS: u64 = 0x00004002;
    pub const CONTROL_EXCEPTION_BITMAP: u64 = 0x00004004;
    pub const CONTROL_PAGE_FAULT_MASK: u64 = 0x00004006;
    pub const CONTROL_PAGE_FAULT_MATCH: u64 = 0x00004008;
    pub const CONTROL_CR3_TARGET_COUNT: u64 = 0x0000400A;
    pub const CONTROL_EXIT_CONTROLS: u64 = 0x0000400C;
    pub const CONTROL_EXIT_MSR_STORE_COUNT: u64 = 0x0000400E;
    pub const CONTROL_EXIT_MSR_LOAD_COUNT: u64 = 0x00004010;
    pub const CONTROL_ENTRY_CONTROLS: u64 = 0x00004012;
    pub const CONTROL_ENTRY_MSR_LOAD_COUNT: u64 = 0x00004014;
    pub const CONTROL_ENTRY_INTERRUPTION_INFO: u64 = 0x00004016;
    pub const CONTROL_ENTRY_EXCEPTION_ERROR_CODE: u64 = 0x00004018;
    pub const CONTROL_ENTRY_INSTRUCTION_LENGTH: u64 = 0x0000401A;
    pub const CONTROL_TPR_THRESHOLD: u64 = 0x0000401C;
    pub const CONTROL_SECONDARY_PROCESSOR_CONTROLS: u64 = 0x0000401E;
    pub const CONTROL_PLE_GAP: u64 = 0x00004020;
    pub const CONTROL_PLE_WINDOW: u64 = 0x00004022;
    pub const DATA_INSTRUCTION_ERROR: u64 = 0x00004400;
    pub const DATA_EXIT_REASON: u64 = 0x00004402;
    pub const DATA_EXIT_INTERRUPT_INFO: u64 = 0x00004404;
    pub const DATA_EXIT_INTERRUPT_ERROR: u64 = 0x00004406;
    pub const DATA_IDT_VECTOR_INFO: u64 = 0x00004408;
    pub const DATA_IDT_VECTOR_ERROR: u64 = 0x0000440A;
    pub const DATA_EXIT_INSTRUCTION_LENGTH: u64 = 0x0000440C;
    pub const DATA_EXIT_INSTRUCTION_INFO: u64 = 0x0000440E;
    pub const GUEST_ES_LIMIT: u64 = 0x00004800;
    pub const GUEST_CS_LIMIT: u64 = 0x00004802;
    pub const GUEST_SS_LIMIT: u64 = 0x00004804;
    pub const GUEST_DS_LIMIT: u64 = 0x00004806;
    pub const GUEST_FS_LIMIT: u64 = 0x00004808;
    pub const GUEST_GS_LIMIT: u64 = 0x0000480A;
    pub const GUEST_LDTR_LIMIT: u64 = 0x0000480C;
    pub const GUEST_TR_LIMIT: u64 = 0x0000480E;
    pub const GUEST_GDTR_LIMIT: u64 = 0x00004810;
    pub const GUEST_IDTR_LIMIT: u64 = 0x00004812;
    pub const GUEST_ES_ACCESS_RIGHTS: u64 = 0x00004814;
    pub const GUEST_CS_ACCESS_RIGHTS: u64 = 0x00004816;
    pub const GUEST_SS_ACCESS_RIGHTS: u64 = 0x00004818;
    pub const GUEST_DS_ACCESS_RIGHTS: u64 = 0x0000481A;
    pub const GUEST_FS_ACCESS_RIGHTS: u64 = 0x0000481C;
    pub const GUEST_GS_ACCESS_RIGHTS: u64 = 0x0000481E;
    pub const GUEST_LDTR_ACCESS_RIGHTS: u64 = 0x00004820;
    pub const GUEST_TR_ACCESS_RIGHTS: u64 = 0x00004822;
    pub const GUEST_INTERRUPTABILITY: u64 = 0x00004824;
    pub const GUEST_ACTIVITY: u64 = 0x00004826;
    pub const GUEST_SMBASE: u64 = 0x00004828;
    pub const GUEST_SYSENTER_CS: u64 = 0x0000482A;
    pub const GUEST_PREEMPTION_TIMER_VALUE: u64 = 0x0000482E;
    pub const HOST_SYSENTER_CS: u64 = 0x00004C00;
    pub const CONTROL_CR0_MASK: u64 = 0x00006000;
    pub const CONTROL_CR4_MASK: u64 = 0x00006002;
    pub const CONTROL_CR0_READ_SHADOW: u64 = 0x00006004;
    pub const CONTROL_CR4_READ_SHADOW: u64 = 0x00006006;
    pub const CONTROL_CR3_TARGET0: u64 = 0x00006008;
    pub const CONTROL_CR3_TARGET1: u64 = 0x0000600A;
    pub const CONTROL_CR3_TARGET2: u64 = 0x0000600C;
    pub const CONTROL_CR3_TARGET3: u64 = 0x0000600E;
    pub const DATA_EXIT_QUALIFICATION: u64 = 0x00006400;
    pub const DATA_IO_RCX: u64 = 0x00006402;
    pub const DATA_IO_RSI: u64 = 0x00006404;
    pub const DATA_IO_RDI: u64 = 0x00006406;
    pub const DATA_IO_RIP: u64 = 0x00006408;
    pub const DATA_GUEST_LINEAR_ADDRESS: u64 = 0x0000640A;
    pub const GUEST_CR0: u64 = 0x00006800;
    pub const GUEST_CR3: u64 = 0x00006802;
    pub const GUEST_CR4: u64 = 0x00006804;
    pub const GUEST_ES_BASE: u64 = 0x00006806;
    pub const GUEST_CS_BASE: u64 = 0x00006808;
    pub const GUEST_SS_BASE: u64 = 0x0000680A;
    pub const GUEST_DS_BASE: u64 = 0x0000680C;
    pub const GUEST_FS_BASE: u64 = 0x0000680E;
    pub const GUEST_GS_BASE: u64 = 0x00006810;
    pub const GUEST_LDTR_BASE: u64 = 0x00006812;
    pub const GUEST_TR_BASE: u64 = 0x00006814;
    pub const GUEST_GDTR_BASE: u64 = 0x00006816;
    pub const GUEST_IDTR_BASE: u64 = 0x00006818;
    pub const GUEST_DR7: u64 = 0x0000681A;
    pub const GUEST_RSP: u64 = 0x0000681C;
    pub const GUEST_RIP: u64 = 0x0000681E;
    pub const GUEST_RFLAGS: u64 = 0x00006820;
    pub const GUEST_PENDING_DEBUG_EXCEPTIONS: u64 = 0x00006822;
    pub const GUEST_SYSENTER_ESP: u64 = 0x00006824;
    pub const GUEST_SYSENTER_EIP: u64 = 0x00006826;
    pub const HOST_CR0: u64 = 0x00006C00;
    pub const HOST_CR3: u64 = 0x00006C02;
    pub const HOST_CR4: u64 = 0x00006C04;
    pub const HOST_FS_BASE: u64 = 0x00006C06;
    pub const HOST_GS_BASE: u64 = 0x00006C08;
    pub const HOST_TR_BASE: u64 = 0x00006C0A;
    pub const HOST_GDTR_BASE: u64 = 0x00006C0C;
    pub const HOST_IDTR_BASE: u64 = 0x00006C0E;
    pub const HOST_SYSENTER_ESP: u64 = 0x00006C10;
    pub const HOST_SYSENTER_EIP: u64 = 0x00006C12;
    pub const HOST_RSP: u64 = 0x00006C14;
    pub const HOST_RIP: u64 = 0x00006C16;
}
pub mod svm {
    pub const INTERCEPT_CR: u64 = 0x000;
    pub const INTERCEPT_DR: u64 = 0x004;
    pub const INTERCEPT_EXC: u64 = 0x008;
    pub const INTERCEPT_MISC1: u64 = 0x00c;
    pub const INTERCEPT_MISC2: u64 = 0x010;
    pub const INTERCEPT_MISC3: u64 = 0x014;
    pub const PAUSE_FILTER: u64 = 0x038;
    pub const IOPM_BASE: u64 = 0x040;
    pub const MSRPM_BASE: u64 = 0x048;
    pub const TSC_OFFSET: u64 = 0x050;
    pub const ASID: u64 = 0x058;
    pub const INT_CTL: u64 = 0x060;
    pub const INT_STATE: u64 = 0x068;
    pub const EXIT_CODE: u64 = 0x070;
    pub const EXIT_INFO1: u64 = 0x078;
    pub const EXIT_INFO2: u64 = 0x080;
    pub const EXIT_INT_INFO: u64 = 0x088;
    pub const NESTED_CTL: u64 = 0x090;
    pub const AVIC_VAPIC_BAR: u64 = 0x098;
    pub const GHCB: u64 = 0x0a0;
    pub const EVENT_INJ: u64 = 0x0a8;
    pub const NESTED_CR3: u64 = 0x0b0;
    pub const VIRT_EXT: u64 = 0x0b8;
    pub const CLEAN: u64 = 0x0c0;
    pub const NEXT_RIP: u64 = 0x0c8;
    pub const INSN_BYTES: u64 = 0x0d0;
    pub const AVIC_BACKING: u64 = 0x0e0;
    pub const AVIC_LOGICAL: u64 = 0x0f0;
    pub const AVIC_PHYSICAL: u64 = 0x0f8;
    pub const VMSA: u64 = 0x108;
    pub const SAVE: u64 = 0x400;
    pub const ES: u64 = SAVE + 0x000;
    pub const CS: u64 = SAVE + 0x010;
    pub const SS: u64 = SAVE + 0x020;
    pub const DS: u64 = SAVE + 0x030;
    pub const FS: u64 = SAVE + 0x040;
    pub const GS: u64 = SAVE + 0x050;
    pub const GDTR: u64 = SAVE + 0x060;
    pub const LDTR: u64 = SAVE + 0x070;
    pub const IDTR: u64 = SAVE + 0x080;
    pub const TR: u64 = SAVE + 0x090;
    pub const CPL: u64 = SAVE + 0x0c8;
    pub const EFER: u64 = SAVE + 0x0d0;
    pub const CR4: u64 = SAVE + 0x148;
    pub const CR3: u64 = SAVE + 0x150;
    pub const CR0: u64 = SAVE + 0x158;
    pub const DR7: u64 = SAVE + 0x160;
    pub const DR6: u64 = SAVE + 0x168;
    pub const RFLAGS: u64 = SAVE + 0x170;
    pub const RIP: u64 = SAVE + 0x178;
    pub const RSP: u64 = SAVE + 0x1d8;
    pub const RAX: u64 = SAVE + 0x1f8;
    pub const STAR: u64 = SAVE + 0x200;
    pub const LSTAR: u64 = SAVE + 0x208;
    pub const CSTAR: u64 = SAVE + 0x210;
    pub const SFMASK: u64 = SAVE + 0x218;
    pub const KERNEL_GS_BASE: u64 = SAVE + 0x220;
    pub const SYSENTER_CS: u64 = SAVE + 0x228;
    pub const SYSENTER_ESP: u64 = SAVE + 0x230;
    pub const SYSENTER_EIP: u64 = SAVE + 0x238;
    pub const CR2: u64 = SAVE + 0x240;
    pub const G_PAT: u64 = SAVE + 0x268;
    pub const END: u64 = SAVE + 0x2e8;
}
use vmx::*;
pub const WRITE_FIELDS: [u64; 73] = [
    GUEST_RIP,
    GUEST_RSP,
    GUEST_ES_SELECTOR,
    GUEST_CS_SELECTOR,
    GUEST_SS_SELECTOR,
    GUEST_DS_SELECTOR,
    GUEST_FS_SELECTOR,
    GUEST_GS_SELECTOR,
    GUEST_LDTR_SELECTOR,
    GUEST_TR_SELECTOR,
    GUEST_DEBUGCTRL,
    GUEST_PAT,
    GUEST_EFER,
    GUEST_PERF_GLOBAL_CTRL,
    GUEST_PDPTE0,
    GUEST_PDPTE1,
    GUEST_PDPTE2,
    GUEST_PDPTE3,
    GUEST_ES_LIMIT,
    GUEST_CS_LIMIT,
    GUEST_SS_LIMIT,
    GUEST_DS_LIMIT,
    GUEST_FS_LIMIT,
    GUEST_GS_LIMIT,
    GUEST_LDTR_LIMIT,
    GUEST_TR_LIMIT,
    GUEST_GDTR_LIMIT,
    GUEST_IDTR_LIMIT,
    GUEST_ES_ACCESS_RIGHTS,
    GUEST_CS_ACCESS_RIGHTS,
    GUEST_SS_ACCESS_RIGHTS,
    GUEST_DS_ACCESS_RIGHTS,
    GUEST_FS_ACCESS_RIGHTS,
    GUEST_GS_ACCESS_RIGHTS,
    GUEST_LDTR_ACCESS_RIGHTS,
    GUEST_TR_ACCESS_RIGHTS,
    GUEST_INTERRUPTABILITY,
    GUEST_SMBASE,
    GUEST_SYSENTER_CS,
    GUEST_PREEMPTION_TIMER_VALUE,
    GUEST_ES_BASE,
    GUEST_CS_BASE,
    GUEST_SS_BASE,
    GUEST_DS_BASE,
    GUEST_FS_BASE,
    GUEST_GS_BASE,
    GUEST_LDTR_BASE,
    GUEST_TR_BASE,
    GUEST_GDTR_BASE,
    GUEST_IDTR_BASE,
    GUEST_DR7,
    GUEST_RFLAGS,
    GUEST_PENDING_DEBUG_EXCEPTIONS,
    GUEST_SYSENTER_ESP,
    GUEST_SYSENTER_EIP,
    CONTROL_CR0_READ_SHADOW,
    CONTROL_CR4_READ_SHADOW,
    GUEST_CR3,
    CONTROL_ENTRY_INTERRUPTION_INFO,
    CONTROL_ENTRY_EXCEPTION_ERROR_CODE,
    CONTROL_ENTRY_INSTRUCTION_LENGTH,
    CONTROL_TSC_OFFSET,
    GUEST_ACTIVITY,
    CONTROL_EXCEPTION_BITMAP,
    CONTROL_CR0_MASK,
    CONTROL_CR4_MASK,
    CONTROL_PIN_EXECUTION_CONTROLS,
    CONTROL_PRIMARY_PROCESSOR_CONTROLS,
    CONTROL_SECONDARY_PROCESSOR_CONTROLS,
    CONTROL_ENTRY_CONTROLS,
    CONTROL_EXIT_CONTROLS,
    GUEST_CR0,
    GUEST_CR4,
];
pub const READ_FIELDS: [u64; 84] = [
    GUEST_RIP,
    GUEST_RSP,
    GUEST_ES_SELECTOR,
    GUEST_CS_SELECTOR,
    GUEST_SS_SELECTOR,
    GUEST_DS_SELECTOR,
    GUEST_FS_SELECTOR,
    GUEST_GS_SELECTOR,
    GUEST_LDTR_SELECTOR,
    GUEST_TR_SELECTOR,
    GUEST_DEBUGCTRL,
    GUEST_PAT,
    GUEST_EFER,
    GUEST_PERF_GLOBAL_CTRL,
    GUEST_PDPTE0,
    GUEST_PDPTE1,
    GUEST_PDPTE2,
    GUEST_PDPTE3,
    GUEST_ES_LIMIT,
    GUEST_CS_LIMIT,
    GUEST_SS_LIMIT,
    GUEST_DS_LIMIT,
    GUEST_FS_LIMIT,
    GUEST_GS_LIMIT,
    GUEST_LDTR_LIMIT,
    GUEST_TR_LIMIT,
    GUEST_GDTR_LIMIT,
    GUEST_IDTR_LIMIT,
    GUEST_ES_ACCESS_RIGHTS,
    GUEST_CS_ACCESS_RIGHTS,
    GUEST_SS_ACCESS_RIGHTS,
    GUEST_DS_ACCESS_RIGHTS,
    GUEST_FS_ACCESS_RIGHTS,
    GUEST_GS_ACCESS_RIGHTS,
    GUEST_LDTR_ACCESS_RIGHTS,
    GUEST_TR_ACCESS_RIGHTS,
    GUEST_INTERRUPTABILITY,
    GUEST_ACTIVITY,
    GUEST_SMBASE,
    GUEST_SYSENTER_CS,
    GUEST_PREEMPTION_TIMER_VALUE,
    GUEST_ES_BASE,
    GUEST_CS_BASE,
    GUEST_SS_BASE,
    GUEST_DS_BASE,
    GUEST_FS_BASE,
    GUEST_GS_BASE,
    GUEST_LDTR_BASE,
    GUEST_TR_BASE,
    GUEST_GDTR_BASE,
    GUEST_IDTR_BASE,
    GUEST_DR7,
    GUEST_RFLAGS,
    GUEST_PENDING_DEBUG_EXCEPTIONS,
    GUEST_SYSENTER_ESP,
    GUEST_SYSENTER_EIP,
    CONTROL_CR0_MASK,
    CONTROL_CR4_MASK,
    CONTROL_CR0_READ_SHADOW,
    CONTROL_CR4_READ_SHADOW,
    DATA_INSTRUCTION_ERROR,
    DATA_EXIT_INTERRUPT_INFO,
    DATA_EXIT_INTERRUPT_ERROR,
    DATA_IDT_VECTOR_INFO,
    DATA_IDT_VECTOR_ERROR,
    DATA_EXIT_INSTRUCTION_LENGTH,
    DATA_EXIT_INSTRUCTION_INFO,
    DATA_GUEST_PHYSICAL,
    DATA_IO_RCX,
    DATA_IO_RSI,
    DATA_IO_RDI,
    DATA_IO_RIP,
    DATA_GUEST_LINEAR_ADDRESS,
    CONTROL_ENTRY_INTERRUPTION_INFO,
    CONTROL_TSC_OFFSET,
    CONTROL_PIN_EXECUTION_CONTROLS,
    CONTROL_PRIMARY_PROCESSOR_CONTROLS,
    CONTROL_SECONDARY_PROCESSOR_CONTROLS,
    CONTROL_EXCEPTION_BITMAP,
    CONTROL_ENTRY_CONTROLS,
    CONTROL_EXIT_CONTROLS,
    GUEST_CR0,
    GUEST_CR3,
    GUEST_CR4,
];

pub fn get<S: Store>(s: &S, v: u64, offset: u64) -> u64 {
    s.read(v.wrapping_add(offset))
}
pub fn set<S: Store>(s: &mut S, v: u64, offset: u64, x: u64) {
    s.write(v.wrapping_add(offset), x);
}
pub fn bound<S: Store>(s: &S, t: Tcb) -> u64 {
    s.read(t.0.wrapping_add(tl::VCPU))
}
pub fn vmcs_addr(v: u64, f: u64) -> u64 {
    let i = ((f & 0xff) >> 1) | (((f >> 10) & 3) << 7) | (((f >> 13) & 3) << 9);
    v.wrapping_add(SHADOW).wrapping_add(i * 8)
}
pub fn read_vmcs<S: Store>(s: &S, v: u64, f: u64) -> u64 {
    s.read(vmcs_addr(v, f))
}
pub fn write_vmcs<S: Store>(s: &mut S, v: u64, f: u64, value: u64) {
    s.write(vmcs_addr(v, f), value);
}
pub fn canonical(value: u64, width: u64) -> bool {
    let shift = if width == 57 { 56 } else { 47 };
    let top = value >> shift;
    top == 0 || top == (u64::MAX >> shift)
}
pub fn valid_xcr0(x: u64, host: u64) -> bool {
    if x & !host != 0 || x & 1 == 0 || (x & 4 != 0 && x & 2 == 0) {
        return false;
    }
    let avx512 = x & 0xe0;
    (avx512 == 0 || (avx512 == 0xe0 && x & 6 == 6))
        && (x & 0x18 == 0 || x & 0x18 == 0x18)
        && (x & 0x60000 == 0 || x & 0x60000 == 0x60000)
}
pub fn valid_pat(pat: u64) -> bool {
    let mut i: u64 = 0;
    let mut ok = true;
    while i < 8 {
        let t = (pat >> (i * 8)) & 255;
        ok = ok && (t <= 1 || (t >= 4 && t <= 7));
        i += 1;
    }
    ok
}
fn contains(fields: &[u64], f: u64) -> bool {
    let mut i = 0;
    let mut found = false;
    while i < fields.len() {
        if fields[i] == f {
            found = true;
        }
        i += 1;
    }
    found
}
fn controls<A: Arch>(a: &A, msr: u64, value: u64, forced: u64, allowed: u64) -> u64 {
    let cap = a.vcpu_capability(msr);
    let ones = (cap & 0xffff_ffff) | forced;
    (value | ones) & (cap >> 32) & (ones | allowed)
}
pub fn sanitize_vmcs<A: Arch>(a: &A, f: u64, value: u64) -> KResult<u64> {
    if !contains(&WRITE_FIELDS, f) {
        return illegal();
    }
    let v = match f {
        GUEST_ACTIVITY => {
            if value > 1 {
                return invalid_arg(1);
            }
            value
        }
        CONTROL_EXCEPTION_BITMAP => value | EXCEPTIONS,
        CONTROL_CR0_MASK => value | CR0_OWNED,
        CONTROL_CR4_MASK => value | !CR4_ALLOWED,
        CONTROL_PIN_EXECUTION_CONTROLS => controls(a, 0x481, value, PIN_ALLOWED, PIN_ALLOWED),
        CONTROL_PRIMARY_PROCESSOR_CONTROLS => {
            controls(a, 0x482, value, PRIMARY_FORCED, PRIMARY_ALLOWED)
        }
        // VPIDs are deliberately disabled: each VM entry flushes guest translations.
        CONTROL_SECONDARY_PROCESSOR_CONTROLS => controls(
            a,
            0x48b,
            value,
            2 | ((a.vcpu_capability(0x48b) >> 32) & 64),
            SECONDARY_ALLOWED & !(1 << 5),
        ),
        CONTROL_EXIT_CONTROLS => controls(
            a,
            0x483,
            value,
            EXIT_FORCED | ((a.vcpu_capability(0x483) >> 32) & ((1 << 12) | (1 << 15))),
            EXIT_FORCED | (1 << 12) | (1 << 15),
        ),
        CONTROL_ENTRY_CONTROLS => {
            let perf = if a.vcpu_capability(0x483) >> 32 & (1 << 12) != 0 {
                1 << 13
            } else {
                0
            };
            controls(
                a,
                0x484,
                value,
                0,
                (1 << 2) | (1 << 9) | (1 << 14) | (1 << 15) | perf,
            )
        }
        GUEST_CR0 => {
            let mut fixed = a.vcpu_capability(0x486);
            if a.vcpu_capability(0x48b) >> 32 & 128 != 0 {
                fixed &= !((1 << 31) | 1);
            }
            (value | fixed) & a.vcpu_capability(0x487)
        }
        GUEST_CR4 => {
            let fixed = a.vcpu_capability(0x488);
            (value | fixed) & a.vcpu_capability(0x489) & (fixed | CR4_ALLOWED)
        }
        _ => value,
    };
    // VMCS field widths; VM-entry checks handle guest-only invalid state.
    Ok(match f >> 13 {
        0 => v & 0xffff,
        2 => v & 0xffff_ffff,
        _ => v,
    })
}
pub const SVM_I1_FORCED: u64 = 0x9c40_800f;
pub const SVM_I1_WRITABLE: u64 = 0x63bf_7ff0;
pub const SVM_I2_FORCED: u64 = 0x7e7d;
pub const SVM_EVENT: u64 = 0xffff_ffff_8000_0fff;

/// VMCB words and masks from l4h 0040; physical pointers never appear here.
pub fn sanitize_vmcb<A: Arch>(a: &A, f: u64, old: u64, value: u64) -> KResult<u64> {
    let (mask, forced, addr) = match f {
        0x000 => (0xffff_ffff, 0xffff_ffff_0010_0000, false),
        0x008 => (
            0xffff_ffff | (SVM_I1_WRITABLE << 32),
            EXCEPTIONS | (SVM_I1_FORCED << 32),
            false,
        ),
        0x010 => (0x182, SVM_I2_FORCED, false),
        0x038 => (0xffff_ffff_0000_0000, 0, false),
        0x050 => (u64::MAX, 0, false),
        0x060 => (0xff_001f_01ff, 1 << 24, false),
        0x068 => (1, 0, false),
        0x0a8 => (SVM_EVENT, 0, false),
        0x0c8 => (u64::MAX, 0, false),
        0x4c8 => (0xff00_0000, 0, false),
        0x4d0 => (u64::MAX, 1 << 12, false),
        0x548 => (CR4_ALLOWED, 0, false),
        0x400 | 0x410 | 0x420 | 0x430 | 0x440 | 0x450 | 0x460 | 0x470 | 0x480 | 0x490 | 0x550
        | 0x558 | 0x560 | 0x568 | 0x570 | 0x578 | 0x5d8 | 0x5f8 | 0x600 | 0x618 | 0x628 | 0x640
        | 0x668 => (u64::MAX, 0, false),
        0x408 | 0x418 | 0x428 | 0x438 | 0x448 | 0x458 | 0x468 | 0x478 | 0x488 | 0x498 | 0x608
        | 0x610 | 0x620 | 0x630 | 0x638 => (u64::MAX, 0, true),
        _ => return illegal(),
    };
    if addr && !canonical(value, a.vcpu_capability(1)) {
        return invalid_arg(1);
    }
    if f == svm::G_PAT && !valid_pat(value) {
        return invalid_arg(1);
    }
    Ok((old & !mask) | (value & mask) | forced)
}
pub fn vmcb_hidden(f: u64) -> bool {
    matches!(
        f,
        0x040 | 0x048 | 0x098 | 0x0a0 | 0x0b0 | 0x0e0 | 0x0f0 | 0x0f8 | 0x108
    )
}

pub fn init<S: Store, A: Arch>(s: &mut S, a: &A, v: u64) {
    let head = ks_get(s, ks::VCPU_HEAD);
    set(s, v, NEXT, head);
    if head != 0 {
        set(s, head, PREV, v);
    }
    ks_set(s, ks::VCPU_HEAD, v);
    set(s, v, XCR0, a.vcpu_capability(0));
    let mut i = 0;
    while i < 1024 {
        set(s, v, IO + i * 8, u64::MAX);
        i += 1;
    }
    if a.virtualization() == 2 {
        reset_svm(s, v);
        set(s, v, 0, 0xffff_ffff_0010_0000);
        set(s, v, 8, EXCEPTIONS | (SVM_I1_FORCED << 32));
        set(s, v, 0x10, SVM_I2_FORCED);
        set(s, v, svm::INT_CTL, 1 << 24);
        set(s, v, svm::NESTED_CTL, 1);
    } else {
        let mut j = 0;
        while j < WRITE_FIELDS.len() {
            let f = WRITE_FIELDS[j];
            if let Ok(value) = sanitize_vmcs(a, f, 0) {
                write_vmcs(s, v, f, value);
            }
            j += 1;
        }
        let entry = sanitize_vmcs(a, CONTROL_ENTRY_CONTROLS, 1 << 9).unwrap_or(0);
        write_vmcs(s, v, CONTROL_ENTRY_CONTROLS, entry);
        write_vmcs(s, v, GUEST_RFLAGS, 2);
        write_vmcs(s, v, GUEST_PAT, 0x0007_0406_0007_0406);
    }
}
pub fn reset_svm<S: Store>(s: &mut S, v: u64) {
    s.zero(v.wrapping_add(0x400), svm::END - 0x400);
    let mut off = 0x400;
    while off <= 0x490 {
        let attr = if off == 0x410 {
            0x9b
        } else if off == 0x470 {
            0x82
        } else if off == 0x490 {
            0x8b
        } else {
            0x93
        };
        set(s, v, off, 0xffff_0000_0000 | (attr << 16));
        off += 16;
    }
    set(s, v, 0x410, 0xffff_009b_f000);
    set(s, v, 0x418, 0xffff_0000);
    set(s, v, svm::EFER, 1 << 12);
    set(s, v, svm::CR0, 0x10);
    set(s, v, svm::DR6, 0xffff_0ff0);
    set(s, v, svm::DR7, 0x400);
    set(s, v, svm::RFLAGS, 2);
    set(s, v, svm::RIP, 0xfff0);
    set(s, v, svm::G_PAT, 0x0007_0406_0007_0406);
}
pub fn stall<S: Store, A: Arch>(s: &mut S, a: &mut A, v: u64) {
    a.vcpu_barrier();
    let t = Tcb(get(s, v, TCB));
    if !t.is_null() {
        smp::remote_tcb_stall(s, a, t);
    }
}
fn reply<S: Store>(s: &mut S, call: bool, value: u64) {
    let ct = sched::cur_thread(s);
    if call {
        let b = msg::lookup_ipc_buffer(s, true, ct);
        msg::set_mr(s, ct, b, 0, value);
        ct.set_reg(s, reg::BADGE, 0);
        msg::set_msg_info(s, ct, MessageInfo::new(0, 0, 0, 1));
    }
    sched::set_thread_state(s, ct, sched::TS_RUNNING);
}
pub fn detach<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    let v = bound(s, t);
    if v == 0 {
        return;
    }
    stall(s, a, v);
    if t.state(s) == sched::TS_RUNNING_VM {
        report(s, a, t, 0);
    }
    set(s, v, TCB, 0);
    s.write(t.0.wrapping_add(tl::VCPU), 0);
}
pub fn finalise<S: Store, A: Arch>(s: &mut S, a: &mut A, v: u64) {
    stall(s, a, v);
    let t = Tcb(get(s, v, TCB));
    if !t.is_null() {
        detach(s, a, t);
    }
    let prev = get(s, v, PREV);
    let next = get(s, v, NEXT);
    if prev == 0 {
        ks_set(s, ks::VCPU_HEAD, next);
    } else {
        set(s, prev, NEXT, next);
    }
    if next != 0 {
        set(s, next, PREV, prev);
    }
}
fn ports<S: Store>(s: &mut S, v: u64, low: u64, high: u64, disable: bool) {
    let mut port = low;
    while port <= high && port < 65536 {
        let addr = v.wrapping_add(IO).wrapping_add((port >> 6) * 8);
        let bit = 1 << (port & 63);
        let old = s.read(addr);
        s.write(addr, if disable { old | bit } else { old & !bit });
        port += 1;
    }
}
/// Revoke a cap's grant, as seL4's clearVPIDIOPortMappings does on every
/// cap finalisation. A stale owner must still name a live VCPU before use.
pub fn revoke_ports<S: Store, A: Arch>(s: &mut S, a: &mut A, owner: u64, low: u64, high: u64) {
    if owner == 0 {
        return;
    }
    a.vcpu_barrier();
    let mut v = ks_get(s, ks::VCPU_HEAD);
    let mut fuel = layout::WALK_FUEL;
    while v != 0 && fuel > 0 {
        fuel -= 1;
        if v == owner {
            stall(s, a, v);
            ports(s, v, low, high, true);
        }
        v = get(s, v, NEXT);
    }
}

fn msr_slot(f: u64) -> Option<u64> {
    match f {
        0xc000_0081 => Some(0),
        0xc000_0082 => Some(1),
        0xc000_0083 => Some(2),
        0xc000_0084 => Some(3),
        0xc000_0102 => Some(4),
        _ => None,
    }
}
fn svm_msr(f: u64) -> Option<u64> {
    match f {
        0xc000_0081 => Some(svm::STAR),
        0xc000_0082 => Some(svm::LSTAR),
        0xc000_0083 => Some(svm::CSTAR),
        0xc000_0084 => Some(svm::SFMASK),
        0xc000_0102 => Some(svm::KERNEL_GS_BASE),
        0xffff_ffff => Some(svm::CR2),
        _ => None,
    }
}
fn msr_addr(v: u64, f: u64, amd: bool) -> Option<u64> {
    if f == 0xffff_fffe {
        return Some(v.wrapping_add(XCR0));
    }
    if amd {
        return svm_msr(f).map(|off| v.wrapping_add(off));
    }
    if f == 0xffff_ffff {
        return Some(v.wrapping_add(CR2));
    }
    msr_slot(f).map(|i| v.wrapping_add(MSRS).wrapping_add(i.wrapping_mul(8)))
}

#[allow(clippy::too_many_arguments)]
pub fn decode<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lbl: u64,
    length: u64,
    v: u64,
    call: bool,
    buf: u64,
    ex: &[Slot; 3],
) -> KResult<()> {
    stall(s, a, v);
    let ct = sched::cur_thread(s);
    let amd = a.virtualization() == 2;
    let f = if length > 0 {
        msg::syscall_arg(s, ct, buf, 0)
    } else {
        0
    };
    let value = if length > 1 {
        msg::syscall_arg(s, ct, buf, 1)
    } else {
        0
    };
    if lbl == label::X86VCPUSetTCB {
        if ex[0].is_null() {
            return truncated();
        }
        let target = match ex[0].cap(s) {
            Cap::Thread { ptr } => Tcb(ptr),
            _ => return illegal(),
        };
        smp::remote_tcb_stall(s, a, target);
        detach(s, a, target);
        let old = Tcb(get(s, v, TCB));
        if !old.is_null() {
            detach(s, a, old);
        }
        set(s, v, TCB, target.0);
        s.write(target.0.wrapping_add(tl::VCPU), v);
    } else if lbl == label::X86VCPUWriteRegisters {
        if length < 15 {
            return truncated();
        }
        let mut i = 0;
        while i < 15 {
            let val = msg::syscall_arg(s, ct, buf, i);
            set(s, v, REGS + i * 8, val);
            i += 1;
        }
        if amd {
            let val = get(s, v, REGS);
            set(s, v, svm::RAX, val);
        }
    } else if lbl == label::X86VCPUFlushTLB {
        // VMX has no VPID, and SVM flushes its ASID at every entry.
    } else if lbl == label::X86VCPUReadVMCS || lbl == label::X86VCPUWriteVMCS {
        if amd {
            return illegal();
        }
        if length < (if lbl == label::X86VCPUWriteVMCS { 2 } else { 1 }) {
            return illegal();
        }
        if lbl == label::X86VCPUWriteVMCS {
            let val = sanitize_vmcs(a, f, value)?;
            write_vmcs(s, v, f, val);
            reply(s, call, val);
        } else {
            if !contains(&READ_FIELDS, f) {
                return illegal();
            }
            let supported =
                if f == GUEST_PERF_GLOBAL_CTRL && a.vcpu_capability(0x484) >> 32 & (1 << 13) == 0 {
                    false
                } else if f == GUEST_PREEMPTION_TIMER_VALUE
                    && a.vcpu_capability(0x481) >> 32 & (1 << 6) == 0
                {
                    false
                } else {
                    true
                };
            let val = if supported { read_vmcs(s, v, f) } else { 0 };
            reply(s, call, val);
        }
        return Ok(());
    } else if lbl == label::X86VCPUReadVMCB || lbl == label::X86VCPUWriteVMCB {
        if !amd {
            return illegal();
        }
        if length < 2 {
            return truncated();
        }
        if lbl == label::X86VCPUWriteVMCB {
            let old = if f < svm::END && f & 7 == 0 {
                get(s, v, f)
            } else {
                0
            };
            let val = sanitize_vmcb(a, f, old, value)?;
            set(s, v, f, val);
            if f == svm::RAX {
                set(s, v, REGS, val);
            }
            reply(s, call, val);
        } else {
            if f & 7 != 0 || f >= svm::END || value == 0 || value > 64 || value > (svm::END - f) / 8
            {
                return invalid_arg(0);
            }
            if call {
                let b = msg::lookup_ipc_buffer(s, true, ct);
                let mut i = 0;
                let mut n = 0;
                while i < value {
                    let off = f.wrapping_add(i.wrapping_mul(8));
                    let val = if vmcb_hidden(off) {
                        0
                    } else if off == svm::RAX {
                        get(s, v, REGS)
                    } else {
                        get(s, v, off)
                    };
                    n = msg::set_mr(s, ct, b, i, val);
                    i += 1;
                }
                ct.set_reg(s, reg::BADGE, 0);
                msg::set_msg_info(s, ct, MessageInfo::new(0, 0, 0, n));
            }
            sched::set_thread_state(s, ct, sched::TS_RUNNING);
        }
        return Ok(());
    } else if lbl == label::X86VCPUReadMSR || lbl == label::X86VCPUWriteMSR {
        let write = lbl == label::X86VCPUWriteMSR;
        if length < (if write { 2 } else { 1 }) {
            return illegal();
        }
        if f == 0x485 && !write {
            reply(s, call, if amd { 0 } else { a.vcpu_capability(f) });
            return Ok(());
        }
        let addr = match msr_addr(v, f, amd) {
            Some(x) => x,
            None => return illegal(),
        };
        if write {
            if (f == 0xc000_0082 || f == 0xc000_0083 || f == 0xc000_0102)
                && !canonical(value, a.vcpu_capability(1))
            {
                return invalid_arg(1);
            }
            if f == 0xffff_fffe && !valid_xcr0(value, a.vcpu_capability(0)) {
                return invalid_arg(1);
            }
            s.write(addr, value);
        }
        reply(s, call, s.read(addr));
        return Ok(());
    } else if lbl == label::X86VCPUEnableIOPort || lbl == label::X86VCPUDisableIOPort {
        if amd {
            return illegal();
        }
        if length < 2 {
            return truncated();
        }
        let low = f & 0xffff;
        let high = value & 0xffff;
        if low > high {
            return invalid_arg(0);
        }
        let enable = lbl == label::X86VCPUEnableIOPort;
        if enable {
            if ex[0].is_null() {
                return truncated();
            }
            match ex[0].cap(s) {
                Cap::IoPort {
                    first,
                    last,
                    vcpu: prior,
                } => {
                    if low < first || high > last {
                        return invalid_arg(0);
                    }
                    // Like seL4's VPID link, reassigning this cap removes
                    // its previous grant. Validate the list membership
                    // before touching an object that may have been deleted.
                    let mut old = ks_get(s, ks::VCPU_HEAD);
                    let mut fuel = layout::WALK_FUEL;
                    while old != 0 && fuel > 0 {
                        fuel -= 1;
                        if old == prior {
                            stall(s, a, old);
                            ports(s, old, first, last, true);
                        }
                        old = get(s, old, NEXT);
                    }
                    ex[0].set_cap(
                        s,
                        Cap::IoPort {
                            first,
                            last,
                            vcpu: v,
                        },
                    );
                }
                _ => return illegal(),
            }
        }
        ports(s, v, low, high, !enable);
    } else {
        return illegal();
    }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    Ok(())
}

/// Enter request: MR0..2 are in registers even without an IPC buffer.
pub fn enter<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    a.vcpu_barrier();
    let v = bound(s, t);
    if v == 0 {
        t.set_reg(s, reg::MSG_INFO, 0);
        return;
    }
    let b = msg::lookup_ipc_buffer(s, false, t);
    let ip = msg::syscall_arg(s, t, b, 0);
    let ctl = msg::syscall_arg(s, t, b, 1);
    let intr = msg::syscall_arg(s, t, b, 2);
    if a.virtualization() == 2 {
        set(s, v, svm::RIP, ip);
        let old = get(s, v, svm::INTERCEPT_EXC);
        let val = (ctl & SVM_I1_WRITABLE) | SVM_I1_FORCED;
        set(s, v, svm::INTERCEPT_EXC, (old & 0xffff_ffff) | (val << 32));
        set(s, v, svm::EVENT_INJ, intr & SVM_EVENT);
    } else {
        write_vmcs(s, v, GUEST_RIP, ip);
        let val =
            sanitize_vmcs(a, CONTROL_PRIMARY_PROCESSOR_CONTROLS, ctl).unwrap_or(PRIMARY_FORCED);
        write_vmcs(s, v, CONTROL_PRIMARY_PROCESSOR_CONTROLS, val);
        write_vmcs(s, v, CONTROL_ENTRY_INTERRUPTION_INFO, intr & 0xffff_ffff);
    }
    set(s, v, VALID, 0);
    set(s, v, PENDING, 0);
    sched::set_thread_state(s, t, sched::TS_RUNNING_VM);
    check(s, a, t);
}
/// Run before every hardware re-entry, under the serial gate.
pub fn check<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    if t.state(s) != sched::TS_RUNNING_VM {
        return;
    }
    let v = bound(s, t);
    if v != 0 && get(s, v, PENDING) != 0 {
        report(s, a, t, 0);
        return;
    }
    let n = Ntfn(t.bound_ntfn(s));
    if n.0 != 0 && n.state(s) == NTFN_ACTIVE {
        let badge = n.badge(s);
        n.set_state(s, NTFN_IDLE);
        report(s, a, t, badge);
    } else if v == 0 {
        report(s, a, t, 0);
    }
}
/// Complete a VMEnter, preferring a saved exit to a later notification.
pub fn report<S: Store, A: Arch>(s: &mut S, a: &A, t: Tcb, badge: u64) {
    let v = bound(s, t);
    let pending = v != 0 && get(s, v, PENDING) != 0;
    let b = msg::lookup_ipc_buffer(s, true, t);
    let mut i = 0;
    while i < NUM_MRS {
        let val = if v != 0 && (pending || get(s, v, VALID) != 0) {
            get(s, v, EXIT + i * 8)
        } else {
            0
        };
        msg::set_mr(s, t, b, i, val);
        i += 1;
    }
    // Without an exit yet, report the supplied entry state and current GPRs.
    if v != 0 && get(s, v, VALID) == 0 {
        let amd = a.virtualization() == 2;
        let ip = if amd {
            get(s, v, svm::RIP)
        } else {
            read_vmcs(s, v, GUEST_RIP)
        };
        let ctl = if amd {
            get(s, v, svm::INTERCEPT_EXC) >> 32
        } else {
            read_vmcs(s, v, CONTROL_PRIMARY_PROCESSOR_CONTROLS)
        };
        let intr = if amd {
            get(s, v, svm::EVENT_INJ)
        } else {
            read_vmcs(s, v, CONTROL_ENTRY_INTERRUPTION_INFO)
        };
        msg::set_mr(s, t, b, 0, ip);
        msg::set_mr(s, t, b, 1, ctl);
        msg::set_mr(s, t, b, 2, intr);
        let mut j = 0;
        while j < 15 {
            msg::set_mr(s, t, b, 10 + j, get(s, v, REGS + j * 8));
            j += 1;
        }
    }
    if v != 0 && get(s, v, VALID) == 0 {
        let amd = a.virtualization() == 2;
        let flags = if amd {
            get(s, v, svm::RFLAGS)
        } else {
            read_vmcs(s, v, GUEST_RFLAGS)
        };
        let int = if amd {
            get(s, v, svm::INT_STATE)
        } else {
            read_vmcs(s, v, GUEST_INTERRUPTABILITY)
        };
        let cr3 = if amd { get(s, v, svm::CR3) } else { 0 };
        let cr2 = if amd {
            get(s, v, svm::CR2)
        } else {
            get(s, v, CR2)
        };
        msg::set_mr(s, t, b, 7, flags);
        msg::set_mr(s, t, b, 8, int);
        msg::set_mr(s, t, b, 9, cr3);
        msg::set_mr(s, t, b, 29, cr2);
    }
    if !pending {
        msg::set_mr(s, t, b, 3, 0);
        msg::set_mr(s, t, b, 4, 0);
    }
    if v != 0 {
        set(s, v, PENDING, 0);
    }
    t.set_reg(s, reg::MSG_INFO, if pending { 1 } else { 0 });
    t.set_reg(s, reg::BADGE, if pending { 0 } else { badge });
    sched::set_thread_state(s, t, sched::TS_RUNNING);
}
