/* VT-x/AMD-V regressions for the shared seL4/l4h virtualization API. */
#include <stdio.h>
#include <string.h>
#include <sel4/sel4.h>
#ifdef CONFIG_VTX
#include <sel4/arch/vmenter.h>
#endif
#include <vka/object.h>
#include <vka/capops.h>
#include <vspace/vspace.h>
#include <sel4test/testutil.h>
#include <sel4test/macros.h>
#include "../helpers.h"

#ifdef CONFIG_VTX
static int alloc_vm(env_t env, vka_object_t *v)
{
    /* Retype is the runtime feature probe, including on CPUs without VT-x/SVM. */
    int err = vka_alloc_vcpu(&env->vka, v);
    if (err) {
        test_eq(err, seL4_InvalidArgument);
        printf("Virtualization unavailable; skipping guest execution\n");
        return 0;
    }
    return 1;
}
static int is_amd(seL4_CPtr v)
{
    return seL4_X86_VCPU_ReadVMCB(v, 0, 1).error == seL4_NoError;
}
static int vmcb_write(seL4_CPtr v, seL4_Word off, seL4_Word val)
{
    return seL4_X86_VCPU_WriteVMCB(v, off, val).error;
}
static int vmcs_write(seL4_CPtr v, seL4_Word field, seL4_Word val)
{
    return seL4_X86_VCPU_WriteVMCS(v, field, val).error;
}
static unsigned pmu_version(void)
{
    unsigned a, b, c, d;
    asm volatile("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d) : "a"(0), "c"(0));
    if (a < 0xa) { return 0; }
    asm volatile("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d) : "a"(0xa), "c"(0));
    return a & 0xff;
}
static int test_vm_policy(env_t env)
{
    vka_object_t v;
    if (!alloc_vm(env, &v)) { return sel4test_get_result(); }
#ifdef CONFIG_DEBUG_BUILD
    test_eq(seL4_DebugCapIdentify(v.cptr), 21);
#endif
    int amd = is_amd(v.cptr);
    test_eq(seL4_X86_VCPU_WriteMSR(v.cptr, SEL4_VCPU_MSR_CR2, 0x12345678).error, seL4_NoError);
    test_eq(seL4_X86_VCPU_ReadMSR(v.cptr, SEL4_VCPU_MSR_CR2).value, 0x12345678);
    test_eq(seL4_X86_VCPU_WriteMSR(v.cptr, SEL4_VCPU_MSR_XCR0, 0).error, seL4_InvalidArgument);
    test_eq(seL4_X86_VCPU_WriteMSR(v.cptr, 0xc0000102, 0x0200000000000000ull).error, seL4_InvalidArgument);
    /* The VMM API must not modify the host's speculation controls. */
    const seL4_Word protected_msrs[] = {0x48, 0x49, 0x122, 0x123, 0xc0011029, 0xc001102e};
    for (unsigned i = 0; i < sizeof(protected_msrs) / sizeof(protected_msrs[0]); i++) {
        test_eq(seL4_X86_VCPU_ReadMSR(v.cptr, protected_msrs[i]).error, seL4_IllegalOperation);
        test_eq(seL4_X86_VCPU_WriteMSR(v.cptr, protected_msrs[i], 0).error, seL4_IllegalOperation);
    }
    test_eq(seL4_X86_VCPU_FlushTLB(v.cptr), seL4_NoError);
    if (amd) {
        test_eq(seL4_X86_VCPU_ReadVMCS(v.cptr, 0x6800).error, seL4_IllegalOperation);
        test_eq(vmcb_write(v.cptr, 0x40, 0), seL4_IllegalOperation);
        test_eq(vmcb_write(v.cptr, 0xb0, 0), seL4_IllegalOperation);
        test_eq(vmcb_write(v.cptr, 0x58, 0), seL4_IllegalOperation);
        test_eq(vmcb_write(v.cptr, 0xc0, 0), seL4_IllegalOperation);
        test_eq(vmcb_write(v.cptr, 0x668, 0x0202020202020202ull), seL4_InvalidArgument);
        test_eq(vmcb_write(v.cptr, 0x620, 0x0200000000000000ull), seL4_InvalidArgument);
        test_eq(seL4_X86_VCPU_ReadVMCB(v.cptr, 3, 1).error, seL4_InvalidArgument);
        test_eq(seL4_X86_VCPU_ReadVMCB(v.cptr, 0, 65).error, seL4_InvalidArgument);
        test_eq(vmcb_write(v.cptr, 0, 0), seL4_NoError);
        seL4_X86_VCPU_ReadVMCB_t r = seL4_X86_VCPU_ReadVMCB(v.cptr, 0, 2);
        test_eq(r.error, seL4_NoError);
        test_eq(r.value, 0xffffffff00100000ull);
        test_eq(seL4_GetMR(1) >> 32 & 0x9c40800f, 0x9c40800f);
        test_eq(seL4_X86_VCPU_ReadVMCB(v.cptr, 0x40, 1).value, 0);
        test_eq(seL4_X86_VCPU_ReadVMCB(v.cptr, 0x48, 1).value, 0);
    } else {
        test_eq(seL4_X86_VCPU_ReadVMCB(v.cptr, 0, 1).error, seL4_IllegalOperation);
        test_eq(vmcs_write(v.cptr, 0x4826, 2), seL4_InvalidArgument);
        test_eq(vmcs_write(v.cptr, 0x201a, 0), seL4_IllegalOperation);
        test_eq(vmcs_write(v.cptr, 0x4002, 0), seL4_NoError);
        seL4_Word ctl = seL4_X86_VCPU_ReadVMCS(v.cptr, 0x4002).value;
        test_check((ctl & ((1 << 19) | (1 << 20) | (1 << 23))) == ((1 << 19) | (1 << 20) | (1 << 23)));
        test_eq(vmcs_write(v.cptr, 0x6000, 0), seL4_NoError);
        test_check((seL4_X86_VCPU_ReadVMCS(v.cptr, 0x6000).value & (3ull << 29)) == (3ull << 29));
        /* VMX load-control capability bits alone do not imply that the
         * PMU MSR exists (e.g. nested KVM with -cpu host,pmu=off). */
        seL4_X86_VCPU_WriteVMCS_t entry = seL4_X86_VCPU_WriteVMCS(v.cptr, 0x4012, 1 << 13);
        seL4_X86_VCPU_WriteVMCS_t exit = seL4_X86_VCPU_WriteVMCS(v.cptr, 0x400c, 1 << 12);
        test_eq(entry.error, seL4_NoError);
        test_eq(exit.error, seL4_NoError);
        if (pmu_version() < 2) {
            test_eq(entry.written & (1 << 13), 0);
            test_eq(exit.written & (1 << 12), 0);
        }
    }
    vka_free_object(&env->vka, &v);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VCPU0001, "VCPU backend checks, forced controls, MSRs and hidden host addresses", test_vm_policy, true)

static int guest_worker(seL4_Word ctl, seL4_Word ip, seL4_Word c, seL4_Word d)
{
    seL4_SetMR(0, ip); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
    seL4_Word badge;
    seL4_Word result = seL4_VMEnter(&badge);
    return result == SEL4_VMENTER_RESULT_FAULT ? seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR) : 0;
}

/* Two VMEnters, each with sentinels in MR3: the first runs the guest at
 * loop_ip until a notification ends it, the second starts at hlt_ip. */
static volatile seL4_Word vm_results[8];
static int notif_worker(seL4_Word ctl, seL4_Word loop_ip, seL4_Word hlt_ip, seL4_Word full)
{
    seL4_Word badge = 0;
    seL4_SetMR(0, loop_ip); seL4_SetMR(1, ctl); seL4_SetMR(2, 0); seL4_SetMR(3, 0x5a5a);
    vm_results[0] = full ? seL4_VMEnterFull(&badge) : seL4_VMEnter(&badge);
    vm_results[1] = badge;
    vm_results[2] = seL4_GetMR(0);
    vm_results[3] = seL4_GetMR(3);
    badge = 0;
    seL4_SetMR(0, hlt_ip); seL4_SetMR(1, ctl); seL4_SetMR(2, 0); seL4_SetMR(3, 0xa5a5);
    vm_results[4] = full ? seL4_VMEnterFull(&badge) : seL4_VMEnter(&badge);
    vm_results[5] = badge;
    vm_results[6] = seL4_GetMR(0);
    vm_results[7] = seL4_GetMR(3);
    return 0;
}

static int send_vm_badges(seL4_Word one, seL4_Word two, seL4_Word sent, seL4_Word unused)
{
    seL4_Signal(one);
    seL4_Signal(two);
    __atomic_store_n((unsigned char *)sent, 1, __ATOMIC_RELEASE);
    return 0;
}

static int wait_for_flag(volatile unsigned char *flag)
{
    uint64_t end = __builtin_ia32_rdtsc() + 3000000000ull;
    while (!__atomic_load_n(flag, __ATOMIC_ACQUIRE) && __builtin_ia32_rdtsc() < end) { asm volatile("pause"); }
    return __atomic_load_n(flag, __ATOMIC_ACQUIRE);
}

/* A 16-bit guest at GPA zero. CPUID exits without advancing RIP, then HLT
 * exits after the VMM advances it, preserving all general registers. */
static int test_vm_execute(env_t env)
{
    vka_object_t v, root, pdpt, pd, pt;
    if (!alloc_vm(env, &v)) { return sel4test_get_result(); }
    int amd = is_amd(v.cptr);
    if (!amd) {
        seL4_X86_VCPU_WriteVMCS_t ctl = seL4_X86_VCPU_WriteVMCS(v.cptr, 0x401e, 2 | (1 << 7));
        test_eq(ctl.error, seL4_NoError);
        if (!(ctl.written & (1 << 7))) {
            printf("Real-mode guest regression requires unrestricted guest support\n");
            vka_free_object(&env->vka, &v);
            return sel4test_get_result();
        }
    }
    test_eq(vka_alloc_object(&env->vka, seL4_X86_EPTPML4Object, 0, &root), 0);
    test_eq(vka_alloc_object(&env->vka, seL4_X86_EPTPDPTObject, 0, &pdpt), 0);
    test_eq(vka_alloc_object(&env->vka, seL4_X86_EPTPDObject, 0, &pd), 0);
    test_eq(vka_alloc_object(&env->vka, seL4_X86_EPTPTObject, 0, &pt), 0);
#ifdef CONFIG_DEBUG_BUILD
    test_eq(seL4_DebugCapIdentify(root.cptr), 29);
    test_eq(seL4_DebugCapIdentify(pdpt.cptr), 27);
    test_eq(seL4_DebugCapIdentify(pd.cptr), 25);
    test_eq(seL4_DebugCapIdentify(pt.cptr), 23);
#endif
    test_eq(seL4_X86_ASIDPool_Assign(env->asid_pool, root.cptr), seL4_NoError);
    test_eq(seL4_X86_EPTPDPT_Map(pdpt.cptr, root.cptr, 0, seL4_X86_EPT_Default_VMAttributes), seL4_NoError);
    test_eq(seL4_X86_EPTPD_Map(pd.cptr, root.cptr, 0, seL4_X86_EPT_Default_VMAttributes), seL4_NoError);
    test_eq(seL4_X86_EPTPT_Map(pt.cptr, root.cptr, 0, seL4_X86_EPT_Default_VMAttributes), seL4_NoError);
    void *code = vspace_new_pages(&env->vspace, seL4_AllRights, 1, seL4_PageBits);
    test_assert(code != NULL);
    const unsigned char bytes[] = {0x0f, 0xa2, 0xf4, 0xeb, 0xfe};
    memcpy(code, bytes, sizeof(bytes));
    cspacepath_t copy, src;
    test_eq(vka_cspace_alloc_path(&env->vka, &copy), 0);
    vka_cspace_make_path(&env->vka, vspace_get_cap(&env->vspace, code), &src);
    test_eq(vka_cnode_copy(&copy, &src, seL4_AllRights), seL4_NoError);
    test_eq(seL4_X86_Page_MapEPT(copy.capPtr, root.cptr, 0, seL4_AllRights, seL4_X86_EPT_Default_VMAttributes), seL4_NoError);
    test_eq(seL4_X86_Page_MapEPT(copy.capPtr, root.cptr, 0, seL4_AllRights, seL4_X86_EPT_Default_VMAttributes), seL4_InvalidCapability);
    test_eq(seL4_TCB_SetEPTRoot(env->tcb, root.cptr), seL4_NoError);
    test_eq(seL4_X86_VCPU_SetTCB(v.cptr, env->tcb), seL4_NoError);
    seL4_Word ctl;
    if (amd) {
        test_eq(vmcb_write(v.cptr, 0x410, 0xffff009b0000ull), seL4_NoError);
        test_eq(vmcb_write(v.cptr, 0x418, 0), seL4_NoError);
        test_eq(vmcb_write(v.cptr, 0x578, 0), seL4_NoError);
        test_eq(vmcb_write(v.cptr, 0x008, (1ull << 50) | (1ull << 56)), seL4_NoError);
        ctl = seL4_X86_VCPU_ReadVMCB(v.cptr, 8, 1).value >> 32;
    } else {
        test_eq(vmcs_write(v.cptr, 0x4012, 1 << 13), seL4_NoError);
        test_eq(vmcs_write(v.cptr, 0x401e, 2 | (1 << 7)), seL4_NoError);
        test_eq(vmcs_write(v.cptr, 0x6800, 0x20), seL4_NoError);
        test_eq(vmcs_write(v.cptr, 0x6820, 2), seL4_NoError);
        for (int i = 0; i < 8; i++) {
            test_eq(vmcs_write(v.cptr, 0x800 + 2 * i, 0), seL4_NoError);
            test_eq(vmcs_write(v.cptr, 0x4800 + 2 * i, 0xffff), seL4_NoError);
            test_eq(vmcs_write(v.cptr, 0x4814 + 2 * i, i == 1 ? 0x9b : (i == 7 ? 0x8b : (i == 6 ? 0x82 : 0x93))), seL4_NoError);
        }
        ctl = (1 << 7); /* HLT exiting */
    }
    seL4_VCPUContext regs = { .eax = 0x12345678, .ebx = 0x87654321, .r15 = 0x1122334455667788ull };
    test_eq(seL4_X86_VCPU_WriteRegisters(v.cptr, &regs), seL4_NoError);
    /* Failed entries restore host state and do not consume an injection. */
    if (amd) { test_eq(vmcb_write(v.cptr, 0x4d0, (1ull << 63) | (1 << 12)), seL4_NoError); }
    else { test_eq(vmcs_write(v.cptr, 0x6820, 0), seL4_NoError); }
    seL4_SetMR(0, 0); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
    seL4_Word badge;
    test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
    seL4_Word failed_reason = seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR);
    test_check(failed_reason == 0xffffffff || (!amd && failed_reason == 33));
    test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_INSTRUCTION_LEN_MR), 0);
    test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_IDT_VECTOR_INFO), 0);
    if (amd) { test_eq(vmcb_write(v.cptr, 0x4d0, 1 << 12), seL4_NoError); }
    else { test_eq(vmcs_write(v.cptr, 0x6820, 2), seL4_NoError); }
    seL4_SetMR(0, 0); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
    test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
    test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), amd ? 0x72 : 10);
    test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_EAX), regs.eax);
    test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_R15), regs.r15);
    test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_INSTRUCTION_LEN_MR), 2);
    if (amd) {
        /* The entry rewrote the ASID word and clean bits from this core's
         * cache state: ReadVMCB hides both, WriteVMCB rejects both. */
        test_eq(seL4_X86_VCPU_ReadVMCB(v.cptr, 0x58, 1).value, 0);
        test_eq(seL4_X86_VCPU_ReadVMCB(v.cptr, 0xc0, 1).value, 0);
        seL4_X86_VCPU_ReadVMCB_t bulk = seL4_X86_VCPU_ReadVMCB(v.cptr, 0x50, 16);
        test_eq(bulk.error, seL4_NoError);
        test_eq(seL4_GetMR(1), 0);
        test_eq(seL4_GetMR(14), 0);
        test_eq(vmcb_write(v.cptr, 0x58, 0), seL4_IllegalOperation);
        test_eq(vmcb_write(v.cptr, 0xc0, 0), seL4_IllegalOperation);
    }
    if (!amd) {
        /* Both kinds of failed VMRESUME must leave the VMCS launched,
         * and must not return the preceding CPUID exit's length. */
        test_eq(vmcs_write(v.cptr, 0x6820, 0), seL4_NoError);
        seL4_SetMR(0, 0); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
        test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), 33);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_INSTRUCTION_LEN_MR), 0);
        test_eq(vmcs_write(v.cptr, 0x6820, 2), seL4_NoError);
        /* Reserved interruption type 1 fails the VM-entry control checks. */
        seL4_SetMR(0, 0); seL4_SetMR(1, ctl); seL4_SetMR(2, 0x80000100);
        test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), 0xffffffff);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_INSTRUCTION_LEN_MR), 0);
    }
    /* Each entry must rewind the RIP advanced by the preceding guest run.
     * A cache that remembers only the last VMWRITE would skip that rewind. */
    const unsigned char increment[] = {0x40, 0x0f, 0xa2}; /* INC AX; CPUID */
    memcpy((unsigned char *)code + 0x20, increment, sizeof(increment));
    const int entry_rounds = 512;
    __builtin_ia32_lfence();
    uint64_t entry_start = __builtin_ia32_rdtsc();
    for (int i = 1; i <= entry_rounds; i++) {
        seL4_SetMR(0, 0x20); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
        test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), amd ? 0x72 : 10);
        test_eq(seL4_GetMR(SEL4_VMENTER_CALL_EIP_MR), 0x21);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_EAX), (regs.eax & ~0xffffull) | ((regs.eax + i) & 0xffff));
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_R15), regs.r15);
    }
    __builtin_ia32_lfence();
    uint64_t entry_ticks = __builtin_ia32_rdtsc() - entry_start;
    printf("VCPU CPUID round trip: %llu TSC ticks/entry (%d entries, includes VMM checks)\n",
           (unsigned long long)(entry_ticks / entry_rounds), entry_rounds);
    test_eq(seL4_X86_VCPU_WriteRegisters(v.cptr, &regs), seL4_NoError);
    printf("VCPU repeated-entry checks completed\n");
    /* Guest instructions must exit too, independently of the VMM API.
     * A passthrough WRMSR here would turn off host IBRS/STIBP. */
    const unsigned char read_spec[] = {0x0f, 0x32, 0xf4};
    const unsigned char write_spec[] = {0x0f, 0x30, 0xf4};
    memcpy((unsigned char *)code + 0x60, read_spec, sizeof(read_spec));
    memcpy((unsigned char *)code + 0x70, write_spec, sizeof(write_spec));
    for (int write = 0; write < 2; write++) {
        seL4_VCPUContext spec_regs = {.ecx = 0x48};
        test_eq(seL4_X86_VCPU_WriteRegisters(v.cptr, &spec_regs), seL4_NoError);
        seL4_SetMR(0, write ? 0x70 : 0x60); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
        test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), amd ? 0x7c : (write ? 32 : 31));
        test_eq(seL4_GetMR(SEL4_VMENTER_CALL_EIP_MR), write ? 0x70 : 0x60);
    }
    test_eq(seL4_X86_VCPU_WriteRegisters(v.cptr, &regs), seL4_NoError);
    if (!amd) {
        /* Seed instruction information with SGDT, then execute scalar IN
         * and UD2. Their undefined fields must not retain the old exit. */
        const unsigned char metadata[] = {0x0f, 0x01, 0x07, 0xe4, 0x80, 0x0f, 0x0b};
        memcpy((unsigned char *)code + 0x40, metadata, sizeof(metadata));
        seL4_X86_VCPU_WriteVMCS_t secondary = seL4_X86_VCPU_WriteVMCS(v.cptr, 0x401e, 2 | (1 << 7) | (1 << 2));
        test_eq(secondary.error, seL4_NoError);
        if (secondary.written & (1 << 2)) {
            seL4_SetMR(0, 0x40); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
            test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
            test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), 46);
            test_check(seL4_X86_VCPU_ReadVMCS(v.cptr, 0x440e).value != 0);
        }
        seL4_SetMR(0, 0x43); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
        test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), 30);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_INSTRUCTION_LEN_MR), 2);
        test_eq(seL4_X86_VCPU_ReadVMCS(v.cptr, 0x440e).value, 0);
        test_eq(vmcs_write(v.cptr, 0x4004, 1 << 6), seL4_NoError);
        seL4_SetMR(0, 0x45); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
        test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), 0);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_INSTRUCTION_LEN_MR), 0);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_IDT_VECTOR_INFO), 0);
        test_eq(seL4_X86_VCPU_ReadVMCS(v.cptr, 0x4404).value & ~0x1000ull, 0x80000306);
        test_eq(seL4_X86_VCPU_ReadVMCS(v.cptr, 0x4406).value, 0);
        test_eq(seL4_X86_VCPU_ReadVMCS(v.cptr, 0x440a).value, 0);
        test_eq(seL4_X86_VCPU_ReadVMCS(v.cptr, 0x440e).value, 0);
        test_eq(vmcs_write(v.cptr, 0x4004, 0), seL4_NoError);
        test_eq(vmcs_write(v.cptr, 0x401e, 2 | (1 << 7)), seL4_NoError);
        printf("VCPU undefined-exit-metadata checks completed\n");
    }
    if (amd) {
        /* Cache a guest-linear translation, edit its PTE without changing
         * the nested mapping, then demand invalidation through both APIs.
         * A same-value CR3 write must invalidate too. */
        void *pages[4];
        for (int i = 0; i < 4; i++) {
            pages[i] = vspace_new_pages(&env->vspace, seL4_AllRights, 1, seL4_PageBits);
            test_assert(pages[i] != NULL);
            memset(pages[i], 0, 4096);
            cspacepath_t alias;
            test_eq(vka_cspace_alloc_path(&env->vka, &alias), 0);
            vka_cspace_make_path(&env->vka, vspace_get_cap(&env->vspace, pages[i]), &src);
            test_eq(vka_cnode_copy(&alias, &src, seL4_AllRights), seL4_NoError);
            test_eq(seL4_X86_Page_MapEPT(alias.capPtr, root.cptr, (i + 1) * 4096,
                    seL4_AllRights, seL4_X86_EPT_Default_VMAttributes), seL4_NoError);
        }
        volatile uint32_t *gpd = pages[0], *gpt = pages[1];
        gpd[0] = 0x2003;
        gpt[0] = 3;
        gpt[8] = 0x3003;
        *(uint32_t *)pages[2] = 0x11112222;
        *(uint32_t *)pages[3] = 0x33334444;
        const unsigned char load[] = {0xa1, 0x00, 0x80, 0x00, 0x00, 0x0f, 0xa2};
        memcpy((unsigned char *)code + 0x40, load, sizeof(load)); /* MOV EAX,[0x8000]; CPUID */
        const seL4_Word fields[] = {0x410, 0x430, 0x550, 0x558};
        seL4_Word saved[4];
        for (int i = 0; i < 4; i++) { saved[i] = seL4_X86_VCPU_ReadVMCB(v.cptr, fields[i], 1).value; }
        test_eq(vmcb_write(v.cptr, 0x410, 0xffffffff0c9b0000ull), seL4_NoError);
        test_eq(vmcb_write(v.cptr, 0x430, 0xffffffff0c930000ull), seL4_NoError);
        test_eq(vmcb_write(v.cptr, 0x550, 0x1000), seL4_NoError);
        test_eq(vmcb_write(v.cptr, 0x558, 0x80000011), seL4_NoError);
        for (int round = 0; round < 3; round++) {
            if (round == 1) {
                gpt[8] = 0x4003;
                test_eq(seL4_X86_VCPU_FlushTLB(v.cptr), seL4_NoError);
            } else if (round == 2) {
                gpt[8] = 0x3003;
                test_eq(vmcb_write(v.cptr, 0x550, 0x1000), seL4_NoError);
            }
            seL4_SetMR(0, 0x40); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
            test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
            test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), 0x72);
            test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_EAX), round == 1 ? 0x33334444 : 0x11112222);
        }
        for (int i = 0; i < 4; i++) { test_eq(vmcb_write(v.cptr, fields[i], saved[i]), seL4_NoError); }
        test_eq(seL4_X86_VCPU_WriteRegisters(v.cptr, &regs), seL4_NoError);
        printf("VCPU guest-TLB invalidation checks completed\n");
    }
    seL4_SetMR(0, 2); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
    test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
    test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), amd ? 0x78 : 12);
    test_eq(seL4_GetMR(SEL4_VMENTER_CALL_EIP_MR), 2);
    /* Replace a cached nested translation with a different frame. Entries
     * do no INVEPT: the unmap itself must evict the old translation. */
    unsigned char *replacement = vspace_new_pages(&env->vspace, seL4_AllRights, 1, seL4_PageBits);
    test_assert(replacement != NULL);
    replacement[0] = 0xf4; /* HLT, where the original frame has CPUID. */
    cspacepath_t replacement_cap;
    test_eq(vka_cspace_alloc_path(&env->vka, &replacement_cap), 0);
    vka_cspace_make_path(&env->vka, vspace_get_cap(&env->vspace, replacement), &src);
    test_eq(vka_cnode_copy(&replacement_cap, &src, seL4_AllRights), seL4_NoError);
    for (int round = 0; round < 3; round++) {
        test_eq(seL4_X86_Page_Unmap(copy.capPtr), seL4_NoError);
        test_eq(seL4_X86_Page_MapEPT(replacement_cap.capPtr, root.cptr, 0, seL4_AllRights, seL4_X86_EPT_Default_VMAttributes), seL4_NoError);
        seL4_SetMR(0, 0); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
        test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), amd ? 0x78 : 12);
        test_eq(seL4_X86_Page_Unmap(replacement_cap.capPtr), seL4_NoError);
        test_eq(seL4_X86_Page_MapEPT(copy.capPtr, root.cptr, 0, seL4_AllRights, seL4_X86_EPT_Default_VMAttributes), seL4_NoError);
        seL4_SetMR(0, 0); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
        test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), amd ? 0x72 : 10);
    }
    printf("VCPU nested-mapping replacement checks completed\n");
    /* An armed host timer must end a guest loop, including with guest IF
     * clear. A pending signal also completes VMEnter without executing. */
    seL4_CPtr ntfn = vka_alloc_notification_leaky(&env->vka);
    test_eq(seL4_TCB_BindNotification(env->tcb, ntfn), seL4_NoError);
    /* The l4h ABI also replaces the sentinels with the notification
     * frame, both before entry and after a timer interrupts the guest. */
    const seL4_Word intr_reason = amd ? 0x60 : 1;
    if (!amd) {
        seL4_X86_VCPU_WriteVMCS_t primary = seL4_X86_VCPU_WriteVMCS(v.cptr, 0x4002, ctl);
        test_eq(primary.error, seL4_NoError);
        ctl = primary.written;
    }
    for (int full = 0; full <= 1; full++) {
        seL4_Signal(ntfn);
        seL4_SetMR(0, 3); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
        seL4_SetMR(SEL4_VMENTER_FAULT_REASON_MR, 0x5a5a);
        seL4_SetMR(SEL4_VMENTER_FAULT_INSTRUCTION_LEN_MR, 0x6b6b);
        test_eq((full ? seL4_VMEnterFull(&badge) : seL4_VMEnter(&badge)), SEL4_VMENTER_RESULT_NOTIF);
        test_eq(seL4_GetMR(SEL4_VMENTER_CALL_EIP_MR), 3);
        test_eq(seL4_GetMR(SEL4_VMENTER_CALL_CONTROL_PPC_MR), ctl);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), full ? intr_reason : 0x5a5a);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_INSTRUCTION_LEN_MR), full ? 0 : 0x6b6b);
        test_eq(seL4_TCB_SetTimer(env->tcb, __builtin_ia32_rdtsc() + 5000000, 0x42), seL4_NoError);
        seL4_SetMR(0, 3); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
        seL4_SetMR(SEL4_VMENTER_FAULT_REASON_MR, 0x5a5a);
        seL4_SetMR(SEL4_VMENTER_FAULT_INSTRUCTION_LEN_MR, 0x6b6b);
        test_eq((full ? seL4_VMEnterFull(&badge) : seL4_VMEnter(&badge)), SEL4_VMENTER_RESULT_NOTIF);
        test_eq(badge, 0x42);
        test_eq(seL4_GetMR(SEL4_VMENTER_CALL_EIP_MR), 3);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), full ? intr_reason : 0x5a5a);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_INSTRUCTION_LEN_MR), full ? 0 : 0x6b6b);
    }
    test_eq(seL4_TCB_UnbindNotification(env->tcb), seL4_NoError);
    for (int full = 0; full <= 1; full++) {
        /* seL4 sendSignal: signals to a RunningVM thread on the current
         * core complete its VMEnter one at a time. A lower-priority worker
         * on this core runs the guest loop; a timer wakes us, preempting
         * it in RunningVM; we signal twice. The first badge ends the
         * running VMEnter, the second completes the next one at once. */
        const unsigned char spin[] = {0xc6, 0x06, 0x00, 0x01, 0x01, 0xeb, 0xfe};
        memcpy((unsigned char *)code + 0x20, spin, sizeof(spin));
        volatile unsigned char *flag = (unsigned char *)code + 0x100;
        *flag = 0;
        seL4_CPtr wake = vka_alloc_notification_leaky(&env->vka);
        test_eq(seL4_TCB_BindNotification(env->tcb, wake), seL4_NoError);
        seL4_CPtr vm_ntfn = vka_alloc_notification_leaky(&env->vka);
        cspacepath_t n_src, n_one, n_two;
        vka_cspace_make_path(&env->vka, vm_ntfn, &n_src);
        test_eq(vka_cspace_alloc_path(&env->vka, &n_one), 0);
        test_eq(vka_cspace_alloc_path(&env->vka, &n_two), 0);
        test_eq(vka_cnode_mint(&n_one, &n_src, seL4_AllRights, 1), seL4_NoError);
        test_eq(vka_cnode_mint(&n_two, &n_src, seL4_AllRights, 2), seL4_NoError);
        helper_thread_t worker;
        create_helper_thread(env, &worker);
        set_helper_priority(env, &worker, env->priority - 1);
        if (env->cores > 1) { set_helper_affinity(env, &worker, 0); }
        test_eq(seL4_TCB_BindNotification(get_helper_tcb(&worker), vm_ntfn), seL4_NoError);
        test_eq(seL4_TCB_SetEPTRoot(get_helper_tcb(&worker), root.cptr), seL4_NoError);
        test_eq(seL4_X86_VCPU_SetTCB(v.cptr, get_helper_tcb(&worker)), seL4_NoError);
        start_helper(env, &worker, notif_worker, ctl, 0x20, 2, full);
        for (int i = 0; i < 100 && !*flag; i++) {
            test_eq(seL4_TCB_SetTimer(env->tcb, __builtin_ia32_rdtsc() + 20000000, 7), seL4_NoError);
            seL4_Word ignored;
            seL4_Wait(wake, &ignored);
        }
        test_assert(*flag);
        if (full && env->cores > 1) {
            /* Keep the worker preempted here while the other core sends
             * both badges. Blocking this thread would let the worker run. */
            unsigned char sent = 0;
            helper_thread_t sender;
            create_helper_thread(env, &sender);
            set_helper_affinity(env, &sender, 1);
            start_helper(env, &sender, send_vm_badges, n_one.capPtr, n_two.capPtr, (seL4_Word)&sent, 0);
            test_assert(wait_for_flag(&sent));
            test_eq(wait_for_helper(&sender), 0);
            cleanup_helper(env, &sender);
        } else {
            seL4_Signal(n_one.capPtr);
            seL4_Signal(n_two.capPtr);
        }
        test_eq(wait_for_helper(&worker), 0);
        test_eq(vm_results[0], SEL4_VMENTER_RESULT_NOTIF);
        test_eq(vm_results[1], 1);
        test_eq(vm_results[2], 0x25);
        test_eq(vm_results[3], full ? intr_reason : 0x5a5a);
        test_eq(vm_results[4], SEL4_VMENTER_RESULT_NOTIF);
        test_eq(vm_results[5], 2);
        test_eq(vm_results[6], 2);
        test_eq(vm_results[7], full ? intr_reason : 0xa5a5);
        cleanup_helper(env, &worker);
        test_eq(seL4_TCB_UnbindNotification(env->tcb), seL4_NoError);
        test_eq(seL4_TCB_SetEPTRoot(env->tcb, root.cptr), seL4_NoError);
        test_eq(seL4_X86_VCPU_SetTCB(v.cptr, env->tcb), seL4_NoError);
        vka_cnode_delete(&n_one);
        vka_cnode_delete(&n_two);
    }
    printf("VCPU notification checks completed\n");
    /* Native mapping remains readable after the guest and the EPT alias
     * is revoked while the underlying frame remains allocated. */
    test_eq(((unsigned char *)code)[0], 0x0f);
    if (env->cores > 1) {
        /* Guest execution itself sets the flag through its nested mapping;
         * the parent therefore knows it is stopping a running VM. */
        const unsigned char loop[] = {0xc6, 0x06, 0x00, 0x01, 0x01, 0xeb, 0xfe};
        memcpy((unsigned char *)code + 3, loop, sizeof(loop));
        for (int round = 0; round < 3; round++) {
            if (round == 2) {
                test_eq(seL4_X86_Page_MapEPT(copy.capPtr, root.cptr, 0, seL4_AllRights, seL4_X86_EPT_Default_VMAttributes), seL4_NoError);
            }
            helper_thread_t worker;
            create_helper_thread(env, &worker);
            set_helper_affinity(env, &worker, 1);
            set_helper_priority(env, &worker, env->priority);
            test_eq(seL4_TCB_SetEPTRoot(get_helper_tcb(&worker), root.cptr), seL4_NoError);
            test_eq(seL4_X86_VCPU_SetTCB(v.cptr, get_helper_tcb(&worker)), seL4_NoError);
            volatile unsigned char *flag = (unsigned char *)code + 0x100;
            *flag = 0;
            start_helper(env, &worker, guest_worker, ctl, 3, 0, 0);
            test_assert(wait_for_flag(flag));
            if (round == 0) {
                test_eq(seL4_X86_VCPU_SetTCB(v.cptr, env->tcb), seL4_NoError);
                test_eq(wait_for_helper(&worker), 0);
            } else if (round == 1) {
                set_helper_affinity(env, &worker, 0);
                set_helper_affinity(env, &worker, 1);
                test_eq(seL4_X86_Page_Unmap(copy.capPtr), seL4_NoError);
                test_eq(wait_for_helper(&worker), amd ? 0x400 : 48);
            } else {
                vka_free_object(&env->vka, &v);
                test_eq(wait_for_helper(&worker), 0);
            }
            cleanup_helper(env, &worker);
        }
    } else {
        test_eq(seL4_X86_Page_Unmap(copy.capPtr), seL4_NoError);
        seL4_SetMR(0, 0); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
        test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_FAULT);
        test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), amd ? 0x400 : 48);
        vka_free_object(&env->vka, &v);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4VCPU0002, "A real guest exits on CPUID/HLT, preserves GPRs and loses unmapped memory", test_vm_execute, true)
#elif defined(CONFIG_ARCH_AARCH64)

_Static_assert(sizeof(seL4_ARM_VCPUState) == 1024, "seL4_ARM_VCPUState size");

/* Helper: probe AArch64 EL2 VHE virtualization via Retype. */
static int aarch64_alloc_vcpu(env_t env, vka_object_t *v)
{
    int err = vka_alloc_object(&env->vka, seL4_ARM_VCPUObject, seL4_ARM_VCPUBits, v);
    if (err) {
        test_eq(err, seL4_InvalidArgument);
        printf("AArch64 virtualization unavailable; skipping guest execution\n");
        return 0;
    }
    return 1;
}

typedef struct {
    vka_object_t ut;
    cspacepath_t cap;
    seL4_CPtr cptr;
} aarch64_s2_t;

static int aarch64_alloc_s2(env_t env, aarch64_s2_t *s2)
{
    test_eq(vka_alloc_untyped(&env->vka, seL4_ARM_Stage2VSpaceBits, &s2->ut), 0);
    test_eq(vka_cspace_alloc_path(&env->vka, &s2->cap), 0);
    test_eq(seL4_Untyped_Retype(s2->ut.cptr, seL4_ARM_Stage2VSpaceObject, 0,
                                s2->cap.root, 0, 0, s2->cap.capPtr, 1), seL4_NoError);
    s2->cptr = s2->cap.capPtr;
    test_eq(seL4_ARM_ASIDPool_Assign(env->asid_pool, s2->cptr), seL4_NoError);
    return 0;
}

static void aarch64_free_s2(env_t env, aarch64_s2_t *s2)
{
    vka_cnode_delete(&s2->cap);
    vka_cspace_free(&env->vka, s2->cap.capPtr);
    vka_free_object(&env->vka, &s2->ut);
}

/* Map a 4 KiB or 2 MiB frame into Stage-2, allocating intermediate tables as needed
 * (works for 40-bit 3-level and 44/48-bit 4-level Stage-2). */
static int s2_map_frame(env_t env, seL4_CPtr s2_root, seL4_CPtr frame, seL4_Word ipa,
                        seL4_CapRights_t rights, seL4_ARM_VMAttributes attr)
{
    for (int tries = 0; tries < 4; tries++) {
        int err = seL4_ARM_Page_Map(frame, s2_root, ipa, rights, attr);
        if (err == seL4_NoError) {
            return 0;
        }
        test_eq(err, seL4_FailedLookup);
        seL4_CPtr pt = vka_alloc_page_table_leaky(&env->vka);
        test_assert(pt != 0);
        test_eq(seL4_ARM_PageTable_Map(pt, s2_root, ipa, seL4_ARM_Default_VMAttributes), seL4_NoError);
    }
    test_assert(0);
    return 0;
}

/* Configure a helper TCB as a guest running in Stage-2 `s2_root` with fault handler `fault_ep`. */
static void setup_guest_tcb(env_t env, helper_thread_t *h, seL4_CPtr vcpu, seL4_CPtr s2_root,
                            seL4_CPtr fault_ep, seL4_Word entry_ipa, seL4_Word sp_ipa)
{
    create_helper_thread(env, h);
    seL4_CPtr tcb = get_helper_tcb(h);
    test_eq(seL4_TCB_SetSpace(tcb, fault_ep, env->cspace_root, seL4_NilData, s2_root, seL4_NilData), seL4_NoError);
    test_eq(seL4_ARM_VCPU_SetTCB(vcpu, tcb), seL4_NoError);
    set_helper_priority(env, h, env->priority - 1);
    seL4_UserContext regs;
    memset(&regs, 0, sizeof(regs));
    regs.pc = entry_ipa;
    regs.sp = sp_ipa;
    regs.spsr = 0x3c5; /* EL1h, DAIF masked */
    test_eq(seL4_TCB_WriteRegisters(tcb, true, 0, sizeof(regs) / sizeof(seL4_Word), &regs), seL4_NoError);
}

static void advance_guest_pc(seL4_CPtr tcb, seL4_Word delta)
{
    seL4_UserContext regs;
    test_eq(seL4_TCB_ReadRegisters(tcb, false, 0, sizeof(regs) / sizeof(seL4_Word), &regs), seL4_NoError);
    regs.pc += delta;
    test_eq(seL4_TCB_WriteRegisters(tcb, false, 0, sizeof(regs) / sizeof(seL4_Word), &regs), seL4_NoError);
}

/* FL4VCPU0001: runtime probe, ReadRegs/WriteRegs/ReadState/WriteState, HCR & VGIC LR & SPSR sanitization. */
static int test_aarch64_vcpu_policy(env_t env)
{
    vka_object_t v;
    if (!aarch64_alloc_vcpu(env, &v)) {
        return sel4test_get_result();
    }
    seL4_ARM_VCPU_ReadRegs_t r = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_VTR);
    test_eq(r.error, seL4_NoError);
    test_assert(r.value != 0);
    seL4_Word hcr_init = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_HCR).value;
    int gic_v3 = (hcr_init & (1ul << 11)) != 0;

    /* Read-only regs reject WriteRegs. */
    test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_FAR_EL2, 0), seL4_InvalidArgument);
    test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_VTR, 0), seL4_InvalidArgument);
    test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_ESR_EL2, 0), seL4_InvalidArgument);

    /* HCR_EL2 whitelist sanitization: forced bits (incl. TIDCP) stay 1, disallowed bits (TGE/DC/CD/ID/AT/FWB/NV*) stripped. */
    const seL4_Word hcr_forced = (1ul << 0) | (1ul << 1) | (1ul << 3) | (1ul << 4) | (1ul << 5)
                               | (1ul << 19) | (1ul << 20) | (1ul << 21) | (1ul << 31) | (1ul << 34);
    const seL4_Word hcr_disallowed = (1ul << 12) | (1ul << 27) | (1ul << 32) | (1ul << 33)
                                   | (1ul << 40) | (1ul << 41) | (1ul << 42) | (1ul << 43)
                                   | (1ul << 44) | (1ul << 45) | (1ul << 46) | (1ul << 56);
    test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_HCR_EL2, hcr_disallowed | (1ul << 13)), seL4_NoError);
    seL4_Word hcr_got = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_HCR_EL2).value;
    test_eq(hcr_got & hcr_forced, hcr_forced);
    test_eq(hcr_got & hcr_disallowed, 0ul);
    test_assert((hcr_got & (1ul << 13)) != 0);

    /* VGIC_HCR sanitization: reserved bits stripped on both GICv3 and GICv2. */
    const seL4_Word vgic_hcr_mask = gic_v3
        ? ((0x1ful << 27) | (1ul << 14) | (1ul << 12) | (1ul << 11) | (1ul << 10) | 0xfful)
        : ((0x1ful << 27) | 0xfful);
    test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_HCR, ~0ul), seL4_NoError);
    test_eq(seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_HCR).value, vgic_hcr_mask);
    test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_HCR, hcr_init), seL4_NoError);

    /* VGIC LR sanitization: HW forced 0, illegal INTID rejected, LPI accepted on GICv3. */
    if (gic_v3) {
        seL4_Word lr = (1ul << 62) | (1ul << 61) | (1ul << 60) | (0x80ul << 48) | (1ul << 41) | 40ul;
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_LR0, lr), seL4_NoError);
        seL4_Word got = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_LR0).value;
        test_eq(got & (1ul << 61), 0ul);
        test_eq(got & 0xfffffffful, 40ul);
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_LR0, (1ul << 62) | 1020ul), seL4_InvalidArgument);
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_LR0, (1ul << 62) | (1ul << 60) | 8192ul), seL4_NoError);
    } else {
        seL4_Word lr = (1ul << 31) | (1ul << 30) | (1ul << 28) | (0x10ul << 23) | (1ul << 19) | 40ul;
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_LR0, lr), seL4_NoError);
        seL4_Word got = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_LR0).value;
        test_eq(got & (1ul << 31), 0ul);
        test_eq(got & 0x3fful, 40ul);
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_LR0, (1ul << 28) | 1020ul), seL4_InvalidArgument);
    }
    test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_LR0, 0), seL4_NoError);

    /* Bulk ReadState / WriteState (1024-byte 64B-aligned RAM frame). */
    seL4_CPtr state_cap = vka_alloc_frame_leaky(&env->vka, seL4_PageBits);
    void *state_va = vspace_map_pages(&env->vspace, &state_cap, NULL, seL4_AllRights, 1, seL4_PageBits, 1);
    test_assert(state_va != NULL);
    seL4_ARM_VCPUState *st = (seL4_ARM_VCPUState *)state_va;
    memset(st, 0, sizeof(*st));
    test_eq(seL4_ARM_VCPU_ReadState(v.cptr, state_cap, 32, seL4_ARM_VCPUState_ALL), seL4_InvalidArgument);
    test_eq(seL4_ARM_VCPU_ReadState(v.cptr, state_cap, 0, seL4_ARM_VCPUState_ALL), seL4_NoError);
    test_eq(st->regs[seL4_VCPUReg_VGIC_VTR], r.value);
    st->regs[seL4_VCPUReg_TPIDR_EL1] = 0xfeedfacecafebeefULL;
    test_eq(seL4_ARM_VCPU_WriteState(v.cptr, state_cap, 0, seL4_ARM_VCPUState_EL1_SYSREGS), seL4_NoError);
    test_eq(seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_TPIDR_EL1).value, 0xfeedfacecafebeefULL);

    /* SPSR sanitization for VCPU thread & downgrade to EL0t on detach. */
    helper_thread_t h;
    create_helper_thread(env, &h);
    seL4_CPtr tcb = get_helper_tcb(&h);
    test_eq(seL4_ARM_VCPU_SetTCB(v.cptr, tcb), seL4_NoError);
    seL4_UserContext regs;
    memset(&regs, 0, sizeof(regs));
    regs.spsr = 0x3c9; /* EL2h -> must be forced to EL1h (0x5) */
    test_eq(seL4_TCB_WriteRegisters(tcb, false, 0, sizeof(regs) / sizeof(seL4_Word), &regs), seL4_NoError);
    test_eq(seL4_TCB_ReadRegisters(tcb, false, 0, sizeof(regs) / sizeof(seL4_Word), &regs), seL4_NoError);
    test_eq(regs.spsr & 0x1ful, 0x5ul);
    /* Deleting the VCPU detaches `tcb` and downgrades SPSR_EL1 back to EL0t. */
    vka_free_object(&env->vka, &v);
    test_eq(seL4_TCB_ReadRegisters(tcb, false, 0, sizeof(regs) / sizeof(seL4_Word), &regs), seL4_NoError);
    test_eq(regs.spsr & 0x1ful, 0x0ul);

    cleanup_helper(env, &h);
    printf("FL4VCPU0001: policy/state/sanitization checks passed (GICv%d)\n", gic_v3 ? 3 : 2);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VCPU0001, "AArch64 VCPU probe, regs/state bulk API, HCR/VGIC/SPSR sanitization", test_aarch64_vcpu_policy, true)

/* FL4VCPU0002: real EL1 guest execution (4K+2M Stage-2, HVC/SMC/WFI/MRS, unmapped+RO VMFault,
 * Stage-1 MMU on + AT S1E1R permission fault, lazy FP/SIMD isolation). */
static int test_aarch64_vcpu_execute(env_t env)
{
    vka_object_t v;
    aarch64_s2_t s2;
    if (!aarch64_alloc_vcpu(env, &v)) {
        return sel4test_get_result();
    }
    aarch64_alloc_s2(env, &s2);

    const seL4_Word CODE_IPA = 0x40000000ul;
    const seL4_Word RO_IPA   = 0x40001000ul;
    const seL4_Word UNM_IPA  = 0x40002000ul;
    const seL4_Word BIG_IPA  = 0x40200000ul;

    seL4_CPtr code_cap = vka_alloc_frame_leaky(&env->vka, seL4_PageBits);
    seL4_CPtr ro_cap   = vka_alloc_frame_leaky(&env->vka, seL4_PageBits);
    seL4_CPtr big_cap  = vka_alloc_frame_leaky(&env->vka, seL4_LargePageBits);
    uint32_t *code_va  = vspace_map_pages(&env->vspace, &code_cap, NULL, seL4_AllRights, 1, seL4_PageBits, 1);
    uint64_t *big_va   = vspace_map_pages(&env->vspace, &big_cap, NULL, seL4_AllRights, 1, seL4_LargePageBits, 1);
    test_assert(code_va != NULL && big_va != NULL);
    memset(code_va, 0, 4096);
    memset(big_va, 0, 1 << 21);

    /* Copy caps for Stage-2 mapping (each cap maps into one VSpace). */
    cspacepath_t src, c_code, c_ro, c_big;
    vka_cspace_make_path(&env->vka, code_cap, &src);
    test_eq(vka_cspace_alloc_path(&env->vka, &c_code), 0);
    test_eq(vka_cnode_copy(&c_code, &src, seL4_AllRights), seL4_NoError);
    vka_cspace_make_path(&env->vka, ro_cap, &src);
    test_eq(vka_cspace_alloc_path(&env->vka, &c_ro), 0);
    test_eq(vka_cnode_copy(&c_ro, &src, seL4_AllRights), seL4_NoError);
    vka_cspace_make_path(&env->vka, big_cap, &src);
    test_eq(vka_cspace_alloc_path(&env->vka, &c_big), 0);
    test_eq(vka_cnode_copy(&c_big, &src, seL4_AllRights), seL4_NoError);

    s2_map_frame(env, s2.cptr, c_code.capPtr, CODE_IPA, seL4_AllRights, seL4_ARM_Default_VMAttributes);
    s2_map_frame(env, s2.cptr, c_ro.capPtr, RO_IPA, seL4_CanRead, seL4_ARM_Default_VMAttributes);
    s2_map_frame(env, s2.cptr, c_big.capPtr, BIG_IPA, seL4_AllRights, seL4_ARM_Default_VMAttributes);

    /* Build guest Stage-1 identity page tables inside `big_va`:
     * L1 at BIG_IPA + 0x10000 (entry 1 maps 0x40000000..0x7fffffff as 1 GiB RWX normal block). */
    uint64_t *s1_l1 = (uint64_t *)((uintptr_t)big_va + 0x10000);
    /* 1 GiB block descriptor at VA 0x40000000 -> PA 0x40000000: Valid(1), AttrIdx=0, AP=0, SH=IS(3), AF=1 */
    s1_l1[1] = 0x40000000ULL | (3ULL << 8) | (1ULL << 10) | 1ULL;

    /* Guest EL1 program at CODE_IPA:
     *  0: movz x10, #0x4020, lsl #16    -> x10 = 0x40200000 (BIG_IPA)
     *  1: movz x11, #0x1234
     *  2: str  x11, [x10]               -> write 2 MiB Stage-2 page
     *  3: hvc  #0x123                   -> VCPUFault EC=0x16, ISS=0x123
     *  4: smc  #0x45                    -> VCPUFault EC=0x17, ISS=0x45
     *  5: wfi                           -> VCPUFault EC=0x01 (TWI=1)
     *  6: mrs  x12, id_aa64pfr0_el1     -> VCPUFault EC=0x18 (TID3=1)
     *  7: movz x13, #0x4000, lsl #16
     *  8: movk x13, #0x2000             -> x13 = UNM_IPA (0x40002000)
     *  9: str  x11, [x13]               -> VMFault translation fault at UNM_IPA
     * 10: movz x14, #0x4000, lsl #16
     * 11: movk x14, #0x1000             -> x14 = RO_IPA (0x40001000)
     * 12: str  x11, [x14]               -> VMFault permission fault (Stage-1 off) at RO_IPA
     * 13: Enable Stage-1 MMU (MAIR=0xff, TCR=T0SZ=25/3-level L1, TTBR0=BIG_IPA+0x10000, SCTLR.M=1)
     *     movz x0, #0xff
     *     msr  mair_el1, x0
     *     movz x0, #0x3519              -> T0SZ=25 (39-bit VA -> L1 start), IRGN0=WB, ORGN0=WB, SH0=IS
     *     movk x0, #0x8080, lsl #16     -> EPD1=1, IPS=010 (40-bit) -> actually set IPS=2 (bit 33)
     *     ... simpler: set T0SZ=25 (39-bit VA) | SH0=3 | ORGN0=1 | IRGN0=1 | EPD1=1 | IPS=2
     *     msr  tcr_el1, x0
     *     movz x0, #0x4021, lsl #16     -> BIG_IPA + 0x10000 = 0x40210000
     *     msr  ttbr0_el1, x0
     *     isb
     *     mrs  x0, sctlr_el1
     *     orr  x0, x0, #1               -> M=1
     *     msr  sctlr_el1, x0
     *     isb
     *     str  x11, [x14]               -> VMFault permission fault WITH Stage-1 MMU ON (AT S1E1R -> RO_IPA)!
     *     Enable CPACR_EL1.FPEN=3 for guest EL1, then run FP/SIMD:
     *     movz x0, #0x30, lsl #16       -> 0x00300000 (FPEN=0b11)
     *     msr  cpacr_el1, x0
     *     isb
     *     movz x1, #0x4045, lsl #48     -> double 42.0 (0x4045000000000000)
     *     fmov d0, x1
     *     fadd d0, d0, d0               -> double 84.0 (0x4055000000000000)
     *     fmov x2, d0
     *     str  x2, [x10, #8]            -> store 84.0 bits at BIG_IPA + 8
     *     hvc  #0x777                   -> done!
     */
    const uint32_t prog[] = {
        0xd2a8040a, /* movz x10, #0x4020, lsl #16 */
        0xd282468b, /* movz x11, #0x1234 */
        0xf900014b, /* str  x11, [x10] */
        0xd4002462, /* hvc  #0x123 */
        0xd40008a3, /* smc  #0x45 */
        0xd503207f, /* wfi */
        0xd538040c, /* mrs  x12, id_aa64pfr0_el1 */
        0xd2a8000d, /* movz x13, #0x4000, lsl #16 */
        0xf284000d, /* movk x13, #0x2000 */
        0xf90001ab, /* str  x11, [x13] */
        0xd2a8000e, /* movz x14, #0x4000, lsl #16 */
        0xf282000e, /* movk x14, #0x1000 */
        0xf90001cb, /* str  x11, [x14] */
        /* Stage-1 MMU setup */
        0xd2801fe0, /* movz x0, #0xff */
        0xd518a200, /* msr  mair_el1, x0 */
        0xd286a320, /* movz x0, #0x3519 */
        0xf2a01000, /* movk x0, #0x0080, lsl #16 (EPD1=1, bit 23) */
        0xf2c00040, /* movk x0, #0x0002, lsl #32 (IPS=2, 40-bit) */
        0xd5182040, /* msr  tcr_el1, x0 */
        0xd2a80420, /* movz x0, #0x4021, lsl #16 */
        0xd5182000, /* msr  ttbr0_el1, x0 */
        0xd5033fdf, /* isb */
        0xd5381000, /* mrs  x0, sctlr_el1 */
        0xb2400000, /* orr  x0, x0, #1 */
        0xd5181000, /* msr  sctlr_el1, x0 */
        0xd5033fdf, /* isb */
        0xf90001cb, /* str  x11, [x14] (Stage-2 perm fault with S1 MMU on) */
        /* FP/SIMD in guest EL1 (uses d8 so host callee-saved d8 isolation is tested) */
        0xd2a00600, /* movz x0, #0x30, lsl #16 */
        0xd5181040, /* msr  cpacr_el1, x0 */
        0xd5033fdf, /* isb */
        0xd2e808a1, /* movz x1, #0x4045, lsl #48 (42.0) */
        0x9e670028, /* fmov d8, x1 */
        0x1e682908, /* fadd d8, d8, d8 (84.0) */
        0x9e660102, /* fmov x2, d8 */
        0xf9000542, /* str  x2, [x10, #8] */
        0xd400eee2, /* hvc  #0x777 */
    };
    memcpy(code_va, prog, sizeof(prog));
    test_eq(seL4_ARM_Page_Unify_Instruction(c_code.capPtr, 0, sizeof(prog)), seL4_NoError);

    /* Enable TWI (bit 13) and TID3 (bit 18) in guest HCR_EL2. */
    seL4_Word hcr = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_HCR_EL2).value;
    test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_HCR_EL2, hcr | (1ul << 13) | (1ul << 18)), seL4_NoError);

    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    vka_object_t reply;
    test_eq(vka_alloc_reply(&env->vka, &reply), 0);
    helper_thread_t guest;
    setup_guest_tcb(env, &guest, v.cptr, s2.cptr, fault_ep, CODE_IPA, BIG_IPA + 0x8000);
    seL4_CPtr gtcb = get_helper_tcb(&guest);

    /* 1. HVC #0x123 */
    seL4_MessageInfo_t info = seL4_Recv(fault_ep, NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VCPUFault);
    seL4_Word hsr = seL4_GetMR(seL4_VCPUFault_HSR);
    test_eq((hsr >> 26) & 0x3ful, 0x16ul);
    test_eq(hsr & 0xfffful, 0x123ul);
    test_eq(big_va[0], 0x1234ULL);

    /* 2. SMC #0x45 (trapped SMC points ELR_EL2 at the SMC instruction -> advance PC by 4) */
    info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VCPUFault);
    hsr = seL4_GetMR(seL4_VCPUFault_HSR);
    test_eq((hsr >> 26) & 0x3ful, 0x17ul);
    test_eq(hsr & 0xfffful, 0x45ul);
    advance_guest_pc(gtcb, 4);

    /* 3. WFI (TWI) -> advance PC by 4 */
    info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VCPUFault);
    test_eq((seL4_GetMR(seL4_VCPUFault_HSR) >> 26) & 0x3ful, 0x01ul);
    advance_guest_pc(gtcb, 4);

    /* 4. MRS ID_AA64PFR0_EL1 (TID3) -> advance PC by 4 */
    info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VCPUFault);
    test_eq((seL4_GetMR(seL4_VCPUFault_HSR) >> 26) & 0x3ful, 0x18ul);
    advance_guest_pc(gtcb, 4);

    /* 5. Unmapped Stage-2 write -> VMFault at UNM_IPA */
    info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), UNM_IPA);
    test_eq((seL4_GetMR(seL4_VMFault_FSR) >> 26) & 0x3ful, 0x24ul);
    advance_guest_pc(gtcb, 4);

    /* 6. Read-only Stage-2 write (Stage-1 off) -> VMFault permission fault at RO_IPA */
    info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), RO_IPA);
    test_eq(seL4_GetMR(seL4_VMFault_FSR) & 0x3cul, 0x0cul);
    advance_guest_pc(gtcb, 4);

    /* 7. Read-only Stage-2 write WITH Stage-1 MMU ON -> AT S1E1R resolves exact RO_IPA & records HPFAR_EL2 */
    info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), RO_IPA);
    test_eq(seL4_GetMR(seL4_VMFault_FSR) & 0x3cul, 0x0cul);
    test_eq(seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_HPFAR_EL2).value, RO_IPA >> 8);
    advance_guest_pc(gtcb, 4);

    /* 8. Final HVC #0x777 after guest FP/SIMD (verify host callee-saved d8 is untouched) */
    uint64_t host_d8_in = 0x3ff0000000000000ULL; /* 1.0 */
    uint64_t host_d8_out = 0;
    asm volatile("fmov d8, %0" :: "r"(host_d8_in) : "d8");
    info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
    asm volatile("fmov %0, d8" : "=r"(host_d8_out));
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VCPUFault);
    test_eq(seL4_GetMR(seL4_VCPUFault_HSR) & 0xfffful, 0x777ul);
    test_eq(big_va[1], 0x4055000000000000ULL); /* 84.0 */
    test_eq(host_d8_out, host_d8_in);

    vka_free_object(&env->vka, &v);
    aarch64_free_s2(env, &s2);
    cleanup_helper(env, &guest);
    printf("FL4VCPU0002: EL1 guest traps, Stage-2 faults, Stage-1 MMU + AT S1E1R, FPU isolation passed\n");
    return sel4test_get_result();
}
DEFINE_TEST(FL4VCPU0002, "AArch64 EL1 guest traps, Stage-2/Stage-1 MMU, AT S1E1R and FPU isolation", test_aarch64_vcpu_execute, true)

/* FL4VCPU0003: VGIC virtual IRQ injection & VGICMaintenance fault (GICv3 & GICv2). */
static int test_aarch64_vcpu_vgic(env_t env)
{
    vka_object_t v;
    aarch64_s2_t s2;
    if (!aarch64_alloc_vcpu(env, &v)) {
        return sel4test_get_result();
    }
    aarch64_alloc_s2(env, &s2);
    int gic_v3 = (seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_HCR).value & (1ul << 11)) != 0;

    const seL4_Word CODE_IPA = 0x40000000ul;
    const seL4_Word VBAR_IPA = 0x40000800ul; /* 2 KiB aligned inside the 4 KiB page */
    seL4_CPtr code_cap = vka_alloc_frame_leaky(&env->vka, seL4_PageBits);
    uint8_t *page_va = vspace_map_pages(&env->vspace, &code_cap, NULL, seL4_AllRights, 1, seL4_PageBits, 1);
    test_assert(page_va != NULL);
    memset(page_va, 0, 4096);
    cspacepath_t src, c_code;
    vka_cspace_make_path(&env->vka, code_cap, &src);
    test_eq(vka_cspace_alloc_path(&env->vka, &c_code), 0);
    test_eq(vka_cnode_copy(&c_code, &src, seL4_AllRights), seL4_NoError);
    s2_map_frame(env, s2.cptr, c_code.capPtr, CODE_IPA, seL4_AllRights, seL4_ARM_Default_VMAttributes);

    /* Data mailbox at CODE_IPA + 0x100 (offset 0x100). */
    volatile uint64_t *mbox = (volatile uint64_t *)(page_va + 0x100);

    /* Main guest entry at CODE_IPA (0x40000000):
     *   set VBAR_EL1 = 0x40000800
     *   if GICv3: enable ICC_SRE_EL1=1, ICC_PMR_EL1=0xff, ICC_IGRPEN1_EL1=1
     *   msr daifclr, #2 (unmask IRQ)
     *   loop: wfe / b loop (wait for IRQ handler to run and exit via hvc #0x55) */
    uint32_t *entry = (uint32_t *)page_va;
    int n = 0;
    entry[n++] = 0xd2a80000; /* movz x0, #0x4000, lsl #16 */
    entry[n++] = 0xf2810000; /* movk x0, #0x0800 */
    entry[n++] = 0xd518c000; /* msr  vbar_el1, x0 */
    entry[n++] = 0xd5033fdf; /* isb */
    if (gic_v3) {
        entry[n++] = 0xd2800020; /* movz x0, #1 */
        entry[n++] = 0xd518cca0; /* msr  s3_0_c12_c12_5 (ICC_SRE_EL1), x0 */
        entry[n++] = 0xd5033fdf; /* isb */
        entry[n++] = 0xd2801fe0; /* movz x0, #0xff */
        entry[n++] = 0xd5184600; /* msr  s3_0_c4_c6_0 (ICC_PMR_EL1), x0 */
        entry[n++] = 0xd2800020; /* movz x0, #1 */
        entry[n++] = 0xd518cce0; /* msr  s3_0_c12_c12_7 (ICC_IGRPEN1_EL1), x0 */
        entry[n++] = 0xd5033fdf; /* isb */
    }
    entry[n++] = 0xd50342ff; /* msr  daifclr, #2 (unmask IRQ) */
    entry[n++] = 0x14000000; /* b    . (spin until IRQ fires) */

    /* EL1h IRQ vector at VBAR_IPA + 0x280 = page_va + 0xa80: */
    uint32_t *vec = (uint32_t *)(page_va + 0x800 + 0x280);
    int v_n = 0;
    vec[v_n++] = 0xd2a80001; /* movz x1, #0x4000, lsl #16 */
    vec[v_n++] = 0xf2802001; /* movk x1, #0x0100 (mbox) */
    if (gic_v3) {
        vec[v_n++] = 0xd538cc02; /* mrs  x2, s3_0_c12_c12_0 (ICC_IAR1_EL1) */
        vec[v_n++] = 0xf9000022; /* str  x2, [x1] */
        vec[v_n++] = 0xd518cc22; /* msr  s3_0_c12_c12_1 (ICC_EOIR1_EL1), x2 -> triggers VGICMaintenance! */
        vec[v_n++] = 0xd5033fdf; /* isb */
    } else {
        vec[v_n++] = 0xd2800502; /* movz x2, #40 (marker that EL1h IRQ fired on GICv2) */
        vec[v_n++] = 0xf9000022; /* str  x2, [x1] */
    }
    vec[v_n++] = 0xd4000aa2; /* hvc  #0x55 */

    test_eq(seL4_ARM_Page_Unify_Instruction(c_code.capPtr, 0, 4096), seL4_NoError);

    /* Validate InjectIRQ bounds & busy slot check, then inject vIRQ 40 into LR0. */
    test_eq(seL4_ARM_VCPU_InjectIRQ(v.cptr, 1020, 0x80, 1, 0), seL4_RangeError);
    test_eq(seL4_ARM_VCPU_InjectIRQ(v.cptr, 40, gic_v3 ? 0x80 : 0x10, 1, 0), seL4_NoError);
    test_eq(seL4_ARM_VCPU_InjectIRQ(v.cptr, 41, gic_v3 ? 0x80 : 0x10, 1, 0), seL4_DeleteFirst);
    if (!gic_v3) {
        /* Enable GICv2 virtual CPU interface Group 1 + priority mask in VGIC_VMCR. */
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_VMCR, (0x1ful << 27) | 3ul), seL4_NoError);
    }

    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    vka_object_t reply;
    test_eq(vka_alloc_reply(&env->vka, &reply), 0);
    helper_thread_t guest;
    setup_guest_tcb(env, &guest, v.cptr, s2.cptr, fault_ep, CODE_IPA, CODE_IPA + 0x700);

    if (gic_v3) {
        /* Guest EOIs vIRQ 40 -> VGICMaintenance fault with IDX=0; VGIC_HCR must retain En & TALL0. */
        seL4_MessageInfo_t info = seL4_Recv(fault_ep, NULL, reply.cptr);
        test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VGICMaintenance);
        test_eq(seL4_MessageInfo_get_length(info), 1ul);
        test_eq(seL4_GetMR(seL4_VGICMaintenance_IDX), 0ul);
        seL4_Word mhcr = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_HCR).value;
        test_eq(mhcr & (1ul | (1ul << 11)), 1ul | (1ul << 11));
        /* Clear LR0 and resume guest to finish hvc #0x55. */
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_LR0, 0), seL4_NoError);
        info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
        test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VCPUFault);
        test_eq(seL4_GetMR(seL4_VCPUFault_HSR) & 0xfffful, 0x55ul);
        test_eq(*mbox, 40ULL);
    } else {
        /* Guest receives virtual IRQ at VBAR+0x280 and exits via hvc #0x55. */
        seL4_MessageInfo_t info = seL4_Recv(fault_ep, NULL, reply.cptr);
        test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VCPUFault);
        test_eq(seL4_GetMR(seL4_VCPUFault_HSR) & 0xfffful, 0x55ul);
        test_eq(*mbox, 40ULL);
        /* Clear LR0 and enable GICH_HCR.UIE (bit 3) to verify GICv2 PPI 25 VGICMaintenance
         * and that VGIC_HCR retains En & UIE after maintenance delivery. */
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_LR0, 0), seL4_NoError);
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_HCR, 1ul | (1ul << 3)), seL4_NoError);
        info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
        test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VGICMaintenance);
        test_eq(seL4_MessageInfo_get_length(info), 0ul);
        seL4_Word mhcr = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_HCR).value;
        test_eq(mhcr & (1ul | (1ul << 3)), 1ul | (1ul << 3));
    }

    vka_free_object(&env->vka, &v);
    aarch64_free_s2(env, &s2);
    cleanup_helper(env, &guest);
    printf("FL4VCPU0003: VGICv%d virtual IRQ injection & VGICMaintenance passed\n", gic_v3 ? 3 : 2);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VCPU0003, "AArch64 VGICv2/v3 virtual IRQ injection and VGICMaintenance", test_aarch64_vcpu_vgic, true)

/* FL4VCPU0004: Guest virtual timer PPI 27 VPPIEvent + AckVPPI(27). */
static int test_aarch64_vcpu_vppi(env_t env)
{
    vka_object_t v;
    aarch64_s2_t s2;
    if (!aarch64_alloc_vcpu(env, &v)) {
        return sel4test_get_result();
    }
    aarch64_alloc_s2(env, &s2);

    const seL4_Word CODE_IPA = 0x40000000ul;
    seL4_CPtr code_cap = vka_alloc_frame_leaky(&env->vka, seL4_PageBits);
    uint32_t *code_va = vspace_map_pages(&env->vspace, &code_cap, NULL, seL4_AllRights, 1, seL4_PageBits, 1);
    test_assert(code_va != NULL);
    cspacepath_t src, c_code;
    vka_cspace_make_path(&env->vka, code_cap, &src);
    test_eq(vka_cspace_alloc_path(&env->vka, &c_code), 0);
    test_eq(vka_cnode_copy(&c_code, &src, seL4_AllRights), seL4_NoError);
    s2_map_frame(env, s2.cptr, c_code.capPtr, CODE_IPA, seL4_AllRights, seL4_ARM_Default_VMAttributes);

    /* Guest arms CNTV_CVAL_EL0 = cntvct_el0 + 1000, CNTV_CTL_EL0 = 1 (enable), then spins. */
    const uint32_t prog[] = {
        0xd53be040, /* mrs  x0, cntvct_el0 */
        0x910fa000, /* add  x0, x0, #1000 */
        0xd51be340, /* msr  cntv_cval_el0, x0 */
        0xd2800020, /* movz x0, #1 */
        0xd51be320, /* msr  cntv_ctl_el0, x0 */
        0xd5033fdf, /* isb */
        0x14000000, /* b    . */
    };
    memcpy(code_va, prog, sizeof(prog));
    test_eq(seL4_ARM_Page_Unify_Instruction(c_code.capPtr, 0, sizeof(prog)), seL4_NoError);

    test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_CNTVOFF, 0x1000), seL4_NoError);

    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    vka_object_t reply;
    test_eq(vka_alloc_reply(&env->vka, &reply), 0);
    helper_thread_t guest;
    setup_guest_tcb(env, &guest, v.cptr, s2.cptr, fault_ep, CODE_IPA, CODE_IPA + 0x700);

    /* First VPPIEvent(27). */
    seL4_MessageInfo_t info = seL4_Recv(fault_ep, NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VPPIEvent);
    test_eq(seL4_GetMR(seL4_VPPIEvent_IRQ), 27ul);

    /* Invalid IRQ rejected; AckVPPI(27) unmasks PPI 27 so it fires again. */
    test_eq(seL4_ARM_VCPU_AckVPPI(v.cptr, 26), seL4_InvalidArgument);
    test_eq(seL4_ARM_VCPU_AckVPPI(v.cptr, 27), seL4_NoError);

    info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VPPIEvent);
    test_eq(seL4_GetMR(seL4_VPPIEvent_IRQ), 27ul);

    vka_free_object(&env->vka, &v);
    aarch64_free_s2(env, &s2);
    cleanup_helper(env, &guest);
    printf("FL4VCPU0004: guest vTimer VPPIEvent(27) + AckVPPI(27) passed\n");
    return sel4test_get_result();
}
DEFINE_TEST(FL4VCPU0004, "AArch64 guest vTimer PPI 27 VPPIEvent and AckVPPI", test_aarch64_vcpu_vppi, true)

/* FL4VCPU0005: SMP cross-core VCPU migration (0 -> 1 -> 0), SetTCB rebind, clean deletion. */
static int test_aarch64_vcpu_smp_migrate(env_t env)
{
    vka_object_t v;
    aarch64_s2_t s2;
    if (!aarch64_alloc_vcpu(env, &v)) {
        return sel4test_get_result();
    }
    aarch64_alloc_s2(env, &s2);

    const seL4_Word CODE_IPA = 0x40000000ul;
    seL4_CPtr code_cap = vka_alloc_frame_leaky(&env->vka, seL4_PageBits);
    uint32_t *code_va = vspace_map_pages(&env->vspace, &code_cap, NULL, seL4_AllRights, 1, seL4_PageBits, 1);
    test_assert(code_va != NULL);
    cspacepath_t src, c_code;
    vka_cspace_make_path(&env->vka, code_cap, &src);
    test_eq(vka_cspace_alloc_path(&env->vka, &c_code), 0);
    test_eq(vka_cnode_copy(&c_code, &src, seL4_AllRights), seL4_NoError);
    s2_map_frame(env, s2.cptr, c_code.capPtr, CODE_IPA, seL4_AllRights, seL4_ARM_Default_VMAttributes);

    /* Guest writes TPIDR_EL1 = 0xdead0001, HVC #1; reads TPIDR_EL1 into x0, writes 0xbeef0002, HVC #2;
     * reads TPIDR_EL1 into x0, HVC #3. */
    const uint32_t prog[] = {
        0xd2a1bd5a, /* movz x26, #0x0dea? -> use simple 16-bit values: */
        0xd2800020, /* movz x0, #1 */
        0xf2a12340, /* movk x0, #0x091a, lsl #16 */
        0xd518d080, /* msr  tpidr_el1, x0 */
        0xd4000022, /* hvc  #1 */
        0xd538d080, /* mrs  x0, tpidr_el1 */
        0xd2800041, /* movz x1, #2 */
        0xf2a56781, /* movk x1, #0x2b3c, lsl #16 */
        0xd518d081, /* msr  tpidr_el1, x1 */
        0xd4000042, /* hvc  #2 */
        0xd538d080, /* mrs  x0, tpidr_el1 */
        0xd4000062, /* hvc  #3 */
    };
    memcpy(code_va, prog, sizeof(prog));
    test_eq(seL4_ARM_Page_Unify_Instruction(c_code.capPtr, 0, sizeof(prog)), seL4_NoError);

    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    vka_object_t reply;
    test_eq(vka_alloc_reply(&env->vka, &reply), 0);
    helper_thread_t guest;
    setup_guest_tcb(env, &guest, v.cptr, s2.cptr, fault_ep, CODE_IPA, CODE_IPA + 0x700);
    seL4_CPtr gtcb = get_helper_tcb(&guest);

    /* Run step 1 on core 0; do NOT call ReadRegs before migrating so the VCPU
     * stays lazily owned on core 0 and migrate_tcb must flush it via CALL_VCPU_FLUSH. */
    seL4_MessageInfo_t info = seL4_Recv(fault_ep, NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VCPUFault);
    test_eq(seL4_GetMR(seL4_VCPUFault_HSR) & 0xfffful, 1ul);

    /* Migrate to core 1 (if SMP) and run step 2; guest reads TPIDR_EL1 into x0. */
    if (env->cores > 1) {
        set_helper_affinity(env, &guest, 1);
    }
    info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VCPUFault);
    test_eq(seL4_GetMR(seL4_VCPUFault_HSR) & 0xfffful, 2ul);
    seL4_UserContext regs;
    test_eq(seL4_TCB_ReadRegisters(gtcb, false, 0, sizeof(regs) / sizeof(seL4_Word), &regs), seL4_NoError);
    test_eq(regs.x0, 0x091a0001ul);

    /* Migrate back to core 0 and run step 3. */
    if (env->cores > 1) {
        set_helper_affinity(env, &guest, 0);
    }
    info = seL4_ReplyRecv(fault_ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(info), seL4_Fault_VCPUFault);
    test_eq(seL4_GetMR(seL4_VCPUFault_HSR) & 0xfffful, 3ul);
    test_eq(seL4_TCB_ReadRegisters(gtcb, false, 0, sizeof(regs) / sizeof(seL4_Word), &regs), seL4_NoError);
    test_eq(regs.x0, 0x2b3c0002ul);

    /* Rebind VCPU to a second helper TCB -> first TCB's SPSR downgrades to EL0t. */
    helper_thread_t guest2;
    create_helper_thread(env, &guest2);
    test_eq(seL4_ARM_VCPU_SetTCB(v.cptr, get_helper_tcb(&guest2)), seL4_NoError);
    test_eq(seL4_TCB_ReadRegisters(gtcb, false, 0, sizeof(regs) / sizeof(seL4_Word), &regs), seL4_NoError);
    test_eq(regs.spsr & 0x1ful, 0x0ul);

    vka_free_object(&env->vka, &v);
    aarch64_free_s2(env, &s2);
    cleanup_helper(env, &guest2);
    cleanup_helper(env, &guest);
    printf("FL4VCPU0005: SMP migration (0->1->0), SetTCB rebind & cleanup passed\n");
    return sel4test_get_result();
}
DEFINE_TEST(FL4VCPU0005, "AArch64 SMP VCPU migration, SetTCB rebind and cleanup", test_aarch64_vcpu_smp_migrate, true)

/* FL4VCPU0006: ARMVCPURun single-call fast path (HVC exit, Stage-2 VMFault,
 * lazy VGIC=0 + sparse LR2 VGIC IRQ/EOI -> VGICMaint, and bound notification Interrupt). */
static int test_aarch64_vcpu_run(env_t env)
{
    vka_object_t v;
    aarch64_s2_t s2;
    if (!aarch64_alloc_vcpu(env, &v)) {
        return sel4test_get_result();
    }
    aarch64_alloc_s2(env, &s2);

    seL4_Word hcr_init = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_HCR).value;
    int gic_v3 = (hcr_init & (1ul << 11)) != 0;

    /* Caller's IPC buffer frame: offset 1024 holds seL4_ARM_VCPUState (disjoint from seL4_IPCBuffer). */
    uintptr_t ipc_va = (uintptr_t)seL4_GetIPCBuffer();
    test_eq(ipc_va & 0xffful, 0ul);
    const seL4_Word STATE_OFF = 1024ul;
    seL4_ARM_VCPUState *st = (seL4_ARM_VCPUState *)(ipc_va + STATE_OFF);
    memset(st, 0, sizeof(*st));

    const seL4_Word CODE_IPA = 0x40000000ul;
    const seL4_Word UNM_IPA  = 0x40002000ul;
    seL4_CPtr code_cap = vka_alloc_frame_leaky(&env->vka, seL4_PageBits);
    uint8_t *page_va = vspace_map_pages(&env->vspace, &code_cap, NULL, seL4_AllRights, 1, seL4_PageBits, 1);
    test_assert(page_va != NULL);
    memset(page_va, 0, 4096);
    cspacepath_t src, c_code;
    vka_cspace_make_path(&env->vka, code_cap, &src);
    test_eq(vka_cspace_alloc_path(&env->vka, &c_code), 0);
    test_eq(vka_cnode_copy(&c_code, &src, seL4_AllRights), seL4_NoError);
    s2_map_frame(env, s2.cptr, c_code.capPtr, CODE_IPA, seL4_AllRights, seL4_ARM_Default_VMAttributes);

    volatile uint64_t *mbox = (volatile uint64_t *)(page_va + 0x100);
    mbox[0] = 0;
    mbox[1] = 0;

    /* Guest EL1 code at CODE_IPA:
     *  1) add x0, x0, #1; msr tpidrro_el0, x0; hvc #0x11 (HVC + TPIDRRO_EL0 save)
     *  2) mrs x0, tpidrro_el0; hvc #0x12                 (TPIDRRO_EL0 preserved across Run)
     *  3) movz x1, #0x4000, lsl #16; movk x1, #0x2000;
     *     str x0, [x1]                                   (Stage-2 VMFault at UNM_IPA)
     *  4) enable VBAR_EL1 = CODE_IPA+0x800, GICv3 ICC (if v3), unmask IRQ, spin
     *  5) EL1h IRQ vector at VBAR+0x280: ack/EOI vIRQ 40, store 40 to mbox[0], hvc #0x33,
     *     then unmask SError (daifclr #4; isb), hvc #0x45 (no re-delivery check)
     *  6) EL1h SError vector at VBAR+0x380: inc mbox[1], hvc #0x44, hvc #0x45
     */
    uint32_t *entry = (uint32_t *)page_va;
    int n = 0;
    entry[n++] = 0x91000400; /* add  x0, x0, #1 */
    entry[n++] = 0xd51bd060; /* msr  tpidrro_el0, x0 */
    entry[n++] = 0xd4000222; /* hvc  #0x11 */
    entry[n++] = 0xd53bd060; /* mrs  x0, tpidrro_el0 */
    entry[n++] = 0xd4000242; /* hvc  #0x12 */
    entry[n++] = 0xd2a80001; /* movz x1, #0x4000, lsl #16 */
    entry[n++] = 0xf2840001; /* movk x1, #0x2000 */
    entry[n++] = 0xf9000020; /* str  x0, [x1] */
    entry[n++] = 0xd2a80000; /* movz x0, #0x4000, lsl #16 */
    entry[n++] = 0xf2810000; /* movk x0, #0x0800 (VBAR_IPA) */
    entry[n++] = 0xd518c000; /* msr  vbar_el1, x0 */
    if (gic_v3) {
        entry[n++] = 0xd2801fe0; /* movz x0, #0xff */
        entry[n++] = 0xd5184600; /* msr  s3_0_c4_c6_0 (ICC_PMR_EL1), x0 */
        entry[n++] = 0xd2800020; /* movz x0, #1 */
        entry[n++] = 0xd518cce0; /* msr  s3_0_c12_c12_7 (ICC_IGRPEN1_EL1), x0 */
        entry[n++] = 0xd5033fdf; /* isb */
    }
    entry[n++] = 0xd50342ff; /* msr  daifclr, #2 */
    entry[n++] = 0x14000000; /* b    . */

    uint32_t *vec = (uint32_t *)(page_va + 0x800 + 0x280);
    int v_n = 0;
    vec[v_n++] = 0xd2a80001; /* movz x1, #0x4000, lsl #16 */
    vec[v_n++] = 0xf2802001; /* movk x1, #0x0100 (mbox) */
    if (gic_v3) {
        vec[v_n++] = 0xd538cc02; /* mrs  x2, s3_0_c12_c12_0 (ICC_IAR1_EL1) */
        vec[v_n++] = 0xf9000022; /* str  x2, [x1] */
        vec[v_n++] = 0xd518cc22; /* msr  s3_0_c12_c12_1 (ICC_EOIR1_EL1), x2 */
        vec[v_n++] = 0xd5033fdf; /* isb */
    } else {
        vec[v_n++] = 0xd2800502; /* movz x2, #40 */
        vec[v_n++] = 0xf9000022; /* str  x2, [x1] */
    }
    vec[v_n++] = 0xd4000662; /* hvc  #0x33 */
    vec[v_n++] = 0xd50344ff; /* msr  daifclr, #4 (unmask SError A) */
    vec[v_n++] = 0xd5033fdf; /* isb */
    vec[v_n++] = 0xd40008a2; /* hvc  #0x45 */

    uint32_t *serr = (uint32_t *)(page_va + 0x800 + 0x380);
    int s_n = 0;
    serr[s_n++] = 0xd2a80001; /* movz x1, #0x4000, lsl #16 */
    serr[s_n++] = 0xf2802101; /* movk x1, #0x0108 (&mbox[1]) */
    serr[s_n++] = 0xf9400022; /* ldr  x2, [x1] */
    serr[s_n++] = 0x91000442; /* add  x2, x2, #1 */
    serr[s_n++] = 0xf9000022; /* str  x2, [x1] */
    serr[s_n++] = 0xd4000882; /* hvc  #0x44 */
    serr[s_n++] = 0xd50344ff; /* msr  daifclr, #4 */
    serr[s_n++] = 0xd5033fdf; /* isb */
    if (gic_v3) {
        serr[s_n++] = 0xd2800022; /* movz x2, #1 */
        serr[s_n++] = 0xd518cce2; /* msr  s3_0_c12_c12_7 (ICC_IGRPEN1_EL1), x2 */
        serr[s_n++] = 0xd5033fdf; /* isb */
    }
    serr[s_n++] = 0xd40008a2; /* hvc  #0x45 */
    test_eq(seL4_ARM_Page_Unify_Instruction(c_code.capPtr, 0, 4096), seL4_NoError);

    /* Bind VCPU to a dormant guest TCB (never resumed; ARMVCPURun runs it on env->tcb). */
    helper_thread_t guest;
    create_helper_thread(env, &guest);
    seL4_CPtr gtcb = get_helper_tcb(&guest);
    test_eq(seL4_TCB_SetSpace(gtcb, 0, env->cspace_root, seL4_NilData, s2.cptr, seL4_NilData), seL4_NoError);
    test_eq(seL4_ARM_VCPU_SetTCB(v.cptr, gtcb), seL4_NoError);

    /* 1. HVC exit with VGIC_HCR = 0 + TPIDRRO_EL0 save/restore across Run. */
    test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_HCR, 0), seL4_NoError);
    st->gprs[0]  = 41;              /* x0 */
    st->gprs[31] = CODE_IPA + 0x700;/* sp_el0 */
    st->gprs[32] = CODE_IPA;        /* elr */
    st->gprs[33] = 0x3c5;           /* spsr: EL1h, DAIF masked */
    st->gprs[36] = 0x9999;          /* initial tpidrro_el0 */
    seL4_ARM_VCPU_Run_t r = seL4_ARM_VCPU_Run(v.cptr, STATE_OFF, seL4_ARM_VCPUState_GPRS, seL4_ARM_VCPUState_GPRS);
    test_eq(r.error, seL4_NoError);
    test_eq(r.stop, seL4_ARM_VCPURunStop_VCPUFault);
    test_eq(r.w1 >> 26, 0x16ul);
    test_eq(r.w1 & 0xfffful, 0x11ul);
    test_eq(st->gprs[0], 42ul);
    test_eq(st->gprs[36], 42ul);    /* guest-written TPIDRRO_EL0 saved on VHE & nVHE */

    /* Re-enter with in_mask=0: guest reads TPIDRRO_EL0 back into x0 -> still 42. */
    st->gprs[0] = 0;
    r = seL4_ARM_VCPU_Run(v.cptr, STATE_OFF, 0, seL4_ARM_VCPUState_GPRS);
    test_eq(r.error, seL4_NoError);
    test_eq(r.stop, seL4_ARM_VCPURunStop_VCPUFault);
    test_eq(r.w1 & 0xfffful, 0x12ul);
    test_eq(st->gprs[0], 42ul);

    /* 2. Stage-2 VMFault at UNM_IPA (in_mask = 0, out_mask = GPRS). */
    r = seL4_ARM_VCPU_Run(v.cptr, STATE_OFF, 0, seL4_ARM_VCPUState_GPRS);
    test_eq(r.error, seL4_NoError);
    test_eq(r.stop, seL4_ARM_VCPURunStop_VMFault);
    test_eq(r.w1 >> 26, 0x24ul);    /* EC_DABT_LOW */
    test_eq(r.w2, UNM_IPA);         /* ipa */
    test_eq(r.w3, UNM_IPA);         /* far */

    /* Advance guest PC past the faulting str instruction (+4) and inject vIRQ 40 into sparse LR2 (LR0=LR1=0).
     * On GICv3, also arm UIE (bit 1) with a lower-priority pending vIRQ 41 in LR3 so EOI of LR2 drops
     * valid LRs from 2 -> 1 (<= 1), asserting both MISR.EOI (bit 0) and MISR.U (bit 1) simultaneously. */
    st->gprs[32] += 4;
    test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_HCR, gic_v3 ? (hcr_init | (1ul << 1)) : hcr_init), seL4_NoError);
    test_eq(seL4_ARM_VCPU_InjectIRQ(v.cptr, 40, gic_v3 ? 0x80 : 0x10, 1, 2), seL4_NoError);
    if (gic_v3) {
        test_eq(seL4_ARM_VCPU_InjectIRQ(v.cptr, 41, 0x90, 1, 3), seL4_NoError);
    } else {
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_VMCR, (0x1ful << 27) | 3ul), seL4_NoError);
    }

    /* 3. Sparse LR2 VGIC IRQ + EOI -> VGICMaint (GICv3) or HVC #0x33 (GICv2).
     *    On GICv3, exit with out_mask = 0 (covers both VHE lazy suspend() and nVHE
     *    implicit HYP_VGIC_OWNER switch), run a second VCPU v2 (VGIC_HCR=0), and verify:
     *    - v2 does NOT inherit v's physical LR2 EOI bit (v2 VGIC_EISR == 0);
     *    - v preserves VMCR, EISR (1 << 2) and MISR (EOI | U == 0x3) across PPI 25 quiesce & owner switch. */
    r = seL4_ARM_VCPU_Run(v.cptr, STATE_OFF, seL4_ARM_VCPUState_GPRS,
                          gic_v3 ? 0 : seL4_ARM_VCPUState_VGIC);
    test_eq(r.error, seL4_NoError);
    if (gic_v3) {
        test_eq(r.stop, seL4_ARM_VCPURunStop_VGICMaint);
        test_eq(r.w1, 1ul << 2); /* EISR bit 2 for LR2 */

        /* Force implicit HYP_VGIC_OWNER switch from v to v2 on this core. */
        vka_object_t v2;
        helper_thread_t guest2;
        test_assert(aarch64_alloc_vcpu(env, &v2));
        create_helper_thread(env, &guest2);
        seL4_CPtr gtcb2 = get_helper_tcb(&guest2);
        test_eq(seL4_TCB_SetSpace(gtcb2, 0, env->cspace_root, seL4_NilData, s2.cptr, seL4_NilData), seL4_NoError);
        test_eq(seL4_ARM_VCPU_SetTCB(v2.cptr, gtcb2), seL4_NoError);
        test_eq(seL4_ARM_VCPU_WriteRegs(v2.cptr, seL4_VCPUReg_VGIC_HCR, 0), seL4_NoError);
        seL4_ARM_VCPUState saved_v = *st;
        st->gprs[0]  = 10;
        st->gprs[31] = CODE_IPA + 0x600;
        st->gprs[32] = CODE_IPA;
        st->gprs[33] = 0x3c5;
        seL4_ARM_VCPU_Run_t r2 = seL4_ARM_VCPU_Run(v2.cptr, STATE_OFF, seL4_ARM_VCPUState_GPRS, 0);
        test_eq(r2.error, seL4_NoError);
        test_eq(r2.stop, seL4_ARM_VCPURunStop_VCPUFault);
        test_eq(r2.w1 & 0xfffful, 0x11ul);
        /* v2 ran with VGIC_HCR=0: must NOT inherit v's LR2 EOI bit into v2's EISR. */
        test_eq(seL4_ARM_VCPU_ReadRegs(v2.cptr, seL4_VCPUReg_VGIC_EISR).value, 0ul);
        /* Verify v's VMCR (VPMR=0xf8/0xff per PRIbits, VENG1=1), EISR (bit 2) and MISR (EOI|U) survived. */
        seL4_Word v_vmcr = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_VMCR).value;
        seL4_Word v_eisr = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_EISR).value;
        seL4_Word v_misr = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_MISR).value;
        test_eq((v_vmcr >> 24) & 0xf0ul, 0xf0ul);
        test_assert((v_vmcr & (1ul << 1)) != 0);
        test_eq(v_eisr, 1ul << 2);
        test_eq(v_misr & 0x3ul, 0x3ul);
        vka_free_object(&env->vka, &v2);
        cleanup_helper(env, &guest2);
        *st = saved_v;

        /* Clear LR2 & LR3 (and drop UIE) via VGIC_LR in the same Run call and arm HCR_EL2.VSE while A is masked. */
        seL4_Word hcr_v = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_HCR_EL2).value;
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_HCR_EL2, hcr_v | (1ul << 8)), seL4_NoError);
        st->regs[seL4_VCPUReg_VGIC_HCR] = hcr_init;
        st->regs[seL4_VCPUReg_VGIC_LR0 + 2] = 0;
        st->regs[seL4_VCPUReg_VGIC_LR0 + 3] = 0;
        r = seL4_ARM_VCPU_Run(v.cptr, STATE_OFF, seL4_ARM_VCPUState_VGIC_LR, 0);
        test_eq(r.error, seL4_NoError);
        test_eq(r.stop, seL4_ARM_VCPURunStop_VCPUFault);
        test_eq(r.w1 & 0xfffful, 0x33ul);
        /* Guest had PSTATE.A masked -> HCR_EL2.VSE must still be armed. */
        test_assert((seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_HCR_EL2).value & (1ul << 8)) != 0);
    } else {
        test_eq(r.stop, seL4_ARM_VCPURunStop_VCPUFault);
        test_eq(r.w1 & 0xfffful, 0x33ul);
        seL4_Word hcr_v = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_HCR_EL2).value;
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_HCR_EL2, hcr_v | (1ul << 8)), seL4_NoError);
    }
    test_eq(mbox[0], 40ULL);

    /* 3b. Guest unmasks SError (daifclr #4): HCR_EL2.VSE delivers once -> hvc #0x44,
     *     hardware auto-clears VSE and kernel syncs it back to 0; next Run hits hvc #0x45
     *     without re-delivering SError. */
    r = seL4_ARM_VCPU_Run(v.cptr, STATE_OFF, 0, 0);
    test_eq(r.error, seL4_NoError);
    test_eq(r.stop, seL4_ARM_VCPURunStop_VCPUFault);
    test_eq(r.w1 & 0xfffful, 0x44ul);
    test_eq(mbox[1], 1ULL);
    test_eq(seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_HCR_EL2).value & (1ul << 8), 0ul);

    if (gic_v3) {
        /* Clear VENG1 (bit 1) in memory before entering; guest sets ICC_IGRPEN1_EL1=1
         * before hvc #0x45 (out_mask=0), leaving hardware VENG1=1 while memory has VENG1=0. */
        seL4_Word vmcr_cur = seL4_ARM_VCPU_ReadRegs(v.cptr, seL4_VCPUReg_VGIC_VMCR).value;
        test_eq(seL4_ARM_VCPU_WriteRegs(v.cptr, seL4_VCPUReg_VGIC_VMCR, vmcr_cur & ~(1ul << 1)), seL4_NoError);
    }
    r = seL4_ARM_VCPU_Run(v.cptr, STATE_OFF, 0, 0);
    test_eq(r.error, seL4_NoError);
    test_eq(r.stop, seL4_ARM_VCPURunStop_VCPUFault);
    test_eq(r.w1 & 0xfffful, 0x45ul);
    test_eq(mbox[1], 1ULL);

    /* 4. Bound notification immediately interrupts ARMVCPURun with badge.
     *    On GICv3, arm VGrp1EIE (bit 6) via slim VGIC_LR input with out_mask=VGIC
     *    and verify decode_run synced hardware VMCR (VENG1=1) so MISR.VGrp1E (bit 6)
     *    agrees with VMCR.VENG1 even on early notification return. */
    vka_object_t ntfn;
    test_eq(vka_alloc_notification(&env->vka, &ntfn), 0);
    cspacepath_t n_src, n_badged;
    vka_cspace_make_path(&env->vka, ntfn.cptr, &n_src);
    test_eq(vka_cspace_alloc_path(&env->vka, &n_badged), 0);
    test_eq(vka_cnode_mint(&n_badged, &n_src, seL4_AllRights, 0x55aaul), seL4_NoError);
    test_eq(seL4_TCB_BindNotification(env->tcb, ntfn.cptr), seL4_NoError);
    seL4_Signal(n_badged.capPtr);
    if (gic_v3) {
        st->regs[seL4_VCPUReg_VGIC_HCR] = hcr_init | (1ul << 6); /* En | VGrp1EIE */
        r = seL4_ARM_VCPU_Run(v.cptr, STATE_OFF, seL4_ARM_VCPUState_VGIC_LR, seL4_ARM_VCPUState_VGIC);
        test_eq(r.error, seL4_NoError);
        test_eq(r.stop, seL4_ARM_VCPURunStop_Interrupt);
        test_eq(r.w1, 0x55aaul);
        test_assert((st->regs[seL4_VCPUReg_VGIC_VMCR] & (1ul << 1)) != 0);
        test_assert((st->regs[seL4_VCPUReg_VGIC_MISR] & (1ul << 6)) != 0);
    } else {
        r = seL4_ARM_VCPU_Run(v.cptr, STATE_OFF, 0, 0);
        test_eq(r.error, seL4_NoError);
        test_eq(r.stop, seL4_ARM_VCPURunStop_Interrupt);
        test_eq(r.w1, 0x55aaul);
    }
    test_eq(seL4_TCB_UnbindNotification(env->tcb), seL4_NoError);

    vka_cnode_delete(&n_badged);
    vka_cspace_free(&env->vka, n_badged.capPtr);
    vka_free_object(&env->vka, &ntfn);
    vka_free_object(&env->vka, &v);
    aarch64_free_s2(env, &s2);
    cleanup_helper(env, &guest);
    printf("FL4VCPU0006: ARMVCPURun (HVC, VMFault, sparse LR2 VGICv%d, bound ntfn) passed\n", gic_v3 ? 3 : 2);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VCPU0006, "AArch64 ARMVCPURun single-call HVC/VMFault/VGIC/Interrupt", test_aarch64_vcpu_run, true)
#endif
