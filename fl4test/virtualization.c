/* VT-x/AMD-V regressions for the shared seL4/l4h virtualization API. */
#include <stdio.h>
#include <string.h>
#include <sel4/sel4.h>
#include <sel4/arch/vmenter.h>
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
    const seL4_Word protected_msrs[] = {0x48, 0x49, 0x122, 0x123, 0xc0011029};
    for (unsigned i = 0; i < sizeof(protected_msrs) / sizeof(protected_msrs[0]); i++) {
        test_eq(seL4_X86_VCPU_ReadMSR(v.cptr, protected_msrs[i]).error, seL4_IllegalOperation);
        test_eq(seL4_X86_VCPU_WriteMSR(v.cptr, protected_msrs[i], 0).error, seL4_IllegalOperation);
    }
    test_eq(seL4_X86_VCPU_FlushTLB(v.cptr), seL4_NoError);
    if (amd) {
        test_eq(seL4_X86_VCPU_ReadVMCS(v.cptr, 0x6800).error, seL4_IllegalOperation);
        test_eq(vmcb_write(v.cptr, 0x40, 0), seL4_IllegalOperation);
        test_eq(vmcb_write(v.cptr, 0xb0, 0), seL4_IllegalOperation);
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

static int wait_guest_started(volatile unsigned char *flag)
{
    uint64_t end = __builtin_ia32_rdtsc() + 3000000000ull;
    while (!*flag && __builtin_ia32_rdtsc() < end) { asm volatile("pause"); }
    return *flag;
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
    seL4_Signal(ntfn);
    seL4_SetMR(0, 3); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
    test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_NOTIF);
    test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), 0);
    test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_INSTRUCTION_LEN_MR), 0);
    test_eq(seL4_TCB_SetTimer(env->tcb, __builtin_ia32_rdtsc() + 5000000, 0x42), seL4_NoError);
    seL4_SetMR(0, 3); seL4_SetMR(1, ctl); seL4_SetMR(2, 0);
    test_eq(seL4_VMEnter(&badge), SEL4_VMENTER_RESULT_NOTIF);
    test_eq(badge, 0x42);
    test_eq(seL4_GetMR(SEL4_VMENTER_FAULT_REASON_MR), 0);
    test_eq(seL4_TCB_UnbindNotification(env->tcb), seL4_NoError);
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
            test_assert(wait_guest_started(flag));
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
#endif
