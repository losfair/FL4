/*
 * fl4test (DESIGN.md §12): FL4's extensions and the l4h fixes FL4 takes,
 * on sel4test's framework. `cargo xtask fl4test` links this file into the
 * sel4test workspace and runs the tests whose names start with FL4; plain
 * sel4test runs leave them out.
 */
#include <stdio.h>
#include <string.h>
#include <sel4/sel4.h>
#include <vka/object.h>
#include <vka/capops.h>
#include <vspace/vspace.h>
#include <sel4test/testutil.h>
#include <sel4test/macros.h>

#include "../helpers.h"

static uint64_t rdtsc(void)
{
    return __builtin_ia32_rdtsc();
}

/* ---- l4h 0001: seL4_TCBFlag_trapSyscalls ---------------------------- */

static int yield_once(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    seL4_Yield();
    return 0;
}

/* A thread with trapSyscalls set makes no seL4 calls: its syscall
 * instruction reaches its fault handler as an UnknownSyscall fault that
 * names the syscall. */
static int test_trap_syscalls(env_t env)
{
    helper_thread_t t;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &t);
    int error = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                                  api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                  env->page_directory, seL4_NilData);
    test_error_eq(error, seL4_NoError);
    seL4_TCB_SetFlags_t f = seL4_TCB_SetFlags(get_helper_tcb(&t), 0, seL4_TCBFlag_trapSyscalls);
    test_error_eq(f.error, seL4_NoError);
    test_check(f.flags & seL4_TCBFlag_trapSyscalls);
    start_helper(env, &t, yield_once, 0, 0, 0, 0);
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UnknownSyscall);
    test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_Syscall), (seL4_Word) seL4_SysYield);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4TRAP0001, "trapSyscalls sends syscalls to the fault handler (l4h 0001)", test_trap_syscalls, true)

/* int $0xa0, the first gate open to user space, with RAX = 39 (Linux's
 * getpid). */
extern char fl4trap_int_ip[];
static int int_gate_once(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    seL4_Word rax = 39;
    asm volatile("fl4trap_int_ip: int $0xa0" : "+a"(rax) : : "memory");
    return 0;
}

/* `int $N` on an open gate is an UnknownSyscall for an ordinary thread. For
 * a thread with trapSyscalls set it is the #GP that int $N raises where the
 * gate is closed: UserException 13 with error code (vector << 3) | 2, at
 * the INT instruction (GitHub issue #1). */
static int test_trap_int_gate(env_t env)
{
    for (int trap = 0; trap <= 1; trap++) {
        helper_thread_t t;
        vka_object_t reply;
        test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
        seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
        create_helper_thread(env, &t);
        int error = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                                      api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                      env->page_directory, seL4_NilData);
        test_error_eq(error, seL4_NoError);
        seL4_TCB_SetFlags_t f = seL4_TCB_SetFlags(get_helper_tcb(&t), 0, trap ? seL4_TCBFlag_trapSyscalls : 0);
        test_error_eq(f.error, seL4_NoError);
        start_helper(env, &t, int_gate_once, 0, 0, 0, 0);
        seL4_Word badge;
        seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
        if (trap) {
            test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UserException);
            test_eq((seL4_Word) seL4_GetMR(seL4_UserException_FaultIP), (seL4_Word) fl4trap_int_ip);
            test_eq((seL4_Word) seL4_GetMR(seL4_UserException_Number), (seL4_Word) 13);
            test_eq((seL4_Word) seL4_GetMR(seL4_UserException_Code), (seL4_Word) ((0xa0 << 3) | 2));
        } else {
            test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UnknownSyscall);
            test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_FaultIP), (seL4_Word) fl4trap_int_ip);
            test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_Syscall), (((seL4_Word) 0xa0 << 24) | 39));
        }
        cleanup_helper(env, &t);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4TRAP0002, "int $N on an open gate: UnknownSyscall, or #GP with trapSyscalls (l4h 0001)",
            test_trap_int_gate, true)

/* One syscall instruction with RDX = n, as a Linux program would make with
 * whatever RDX happens to hold. */
static int syscall_once(seL4_Word n, seL4_Word b, seL4_Word c, seL4_Word d)
{
    seL4_Word rax = 39;
    asm volatile("syscall" : "+a"(rax) : "d"(n) : "rcx", "r11", "memory");
    return 0;
}

/* With trapSyscalls set, every syscall instruction is an UnknownSyscall
 * fault naming RDX, whatever RDX holds: seL4 calls, debug calls and
 * SetTLSBase are none of them interpreted (GitHub issue #7). */
static int test_trap_syscall_sweep(env_t env)
{
    for (int n = -1; n >= -64; n--) {
        helper_thread_t t;
        vka_object_t reply;
        test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
        seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
        create_helper_thread(env, &t);
        int error = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                                      api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                      env->page_directory, seL4_NilData);
        test_error_eq(error, seL4_NoError);
        seL4_TCB_SetFlags_t f = seL4_TCB_SetFlags(get_helper_tcb(&t), 0, seL4_TCBFlag_trapSyscalls);
        test_error_eq(f.error, seL4_NoError);
        start_helper(env, &t, syscall_once, (seL4_Word) n, 0, 0, 0);
        seL4_Word badge;
        seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
        test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UnknownSyscall);
        test_eq((seL4_Word) seL4_GetMR(seL4_UnknownSyscall_Syscall), (seL4_Word) (seL4_Int64) n);
        cleanup_helper(env, &t);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4TRAP0003, "trapSyscalls: every RDX from -1 to -64 faults, SetTLSBase included (l4h 0001)",
            test_trap_syscall_sweep, true)

/* ---- l4h 0003, 0006: seL4_TCB_SetTimer ------------------------------ */

/* The timer signals its badge to the TCB's bound notification, not before
 * the deadline. */
static int test_tcb_timer(env_t env)
{
    seL4_CPtr ntfn = vka_alloc_notification_leaky(&env->vka);
    test_error_eq(seL4_TCB_BindNotification(env->tcb, ntfn), seL4_NoError);
    uint64_t deadline = rdtsc() + 2000000;
    test_error_eq(seL4_TCB_SetTimer(env->tcb, deadline, 0x42), seL4_NoError);
    seL4_Word badge = 0;
    seL4_Wait(ntfn, &badge);
    uint64_t now = rdtsc();
    test_eq(badge, (seL4_Word) 0x42);
    test_geq(now, deadline);
    test_error_eq(seL4_TCB_UnbindNotification(env->tcb), seL4_NoError);
    return sel4test_get_result();
}
DEFINE_TEST(FL4TIMER0001, "TCB_SetTimer signals the bound notification at the deadline (l4h 0003)", test_tcb_timer, true)

/* A deadline in the past fires at once; deadline 0 disarms. */
static int test_tcb_timer_past_and_disarm(env_t env)
{
    seL4_CPtr ntfn = vka_alloc_notification_leaky(&env->vka);
    test_error_eq(seL4_TCB_BindNotification(env->tcb, ntfn), seL4_NoError);
    test_error_eq(seL4_TCB_SetTimer(env->tcb, 1, 0x7), seL4_NoError);
    seL4_Word badge = 0;
    seL4_Wait(ntfn, &badge);
    test_eq(badge, (seL4_Word) 0x7);

    test_error_eq(seL4_TCB_SetTimer(env->tcb, rdtsc() + 1000000, 0x9), seL4_NoError);
    test_error_eq(seL4_TCB_SetTimer(env->tcb, 0, 0), seL4_NoError);
    uint64_t until = rdtsc() + 4000000;
    while (rdtsc() < until) {
    }
    badge = 0;
    seL4_Poll(ntfn, &badge);
    test_eq(badge, (seL4_Word) 0);
    test_error_eq(seL4_TCB_UnbindNotification(env->tcb), seL4_NoError);
    return sel4test_get_result();
}
DEFINE_TEST(FL4TIMER0002, "TCB_SetTimer: past deadlines fire at once, 0 disarms (l4h 0003)", test_tcb_timer_past_and_disarm, true)

/* ---- l4h 0002: seL4_TCB_ReadFPU and seL4_TCB_WriteFPU -------------- */

#define FPU_BYTES 4096

/* Map a fresh frame, returning its cap and address. */
static void *map_frame(env_t env, seL4_CPtr *cap)
{
    *cap = vka_alloc_frame_leaky(&env->vka, seL4_PageBits);
    if (!*cap) {
        return NULL;
    }
    return vspace_map_pages(&env->vspace, cap, NULL, seL4_AllRights, 1, seL4_PageBits, 1);
}

/* An image written to a thread reads back in the standard XSAVE layout,
 * with MXCSR's reserved bits cleared. */
static int test_fpu_read_write(env_t env)
{
    helper_thread_t t;
    create_helper_thread(env, &t);
    seL4_CPtr fcap;
    uint8_t *frame = map_frame(env, &fcap);
    test_assert(frame != NULL);
    test_error_eq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    /* XMM0 is at byte 160 of the legacy area; MXCSR at 24. */
    for (int i = 0; i < 16; i++) {
        frame[160 + i] = 0xa0 + i;
    }
    /* XSTATE_BV bit 1 marks the XMM payload as present in this image. */
    frame[512] |= 2;
    uint32_t mxcsr = 0x1f80 | 0xffff0000u;
    memcpy(frame + 24, &mxcsr, 4);
    test_error_eq(seL4_TCB_WriteFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    memset(frame, 0, FPU_BYTES);
    test_error_eq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    for (int i = 0; i < 16; i++) {
        test_eq((int) frame[160 + i], 0xa0 + i);
    }
    /* Bits outside the CPU's MXCSR_MASK are cleared. */
    memcpy(&mxcsr, frame + 24, 4);
    static uint8_t fx[512] __attribute__((aligned(16)));
    __asm__ volatile("fxsave64 %0" : "=m"(fx));
    uint32_t mask;
    memcpy(&mask, fx + 28, 4);
    if (mask == 0) {
        mask = 0xffbf;
    }
    test_eq(mxcsr & ~mask, 0u);
    test_eq(mxcsr & 0xffff, 0x1f80u);
    /* Misaligned offsets are refused. */
    test_neq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 8), seL4_NoError);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4FPU0001, "TCB_ReadFPU and TCB_WriteFPU round trip, sanitised (l4h 0002)", test_fpu_read_write, true)

/* MXCSR, which the thread's start-up code leaves alone. */
static int read_mxcsr(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    uint32_t v;
    __asm__ volatile("stmxcsr %0" : "=m"(v));
    return (int)(v & 0xffff);
}

/* A thread starts with the FPU state written to it. */
static int test_fpu_write_runs(env_t env)
{
    helper_thread_t t;
    create_helper_thread(env, &t);
    seL4_CPtr fcap;
    uint8_t *frame = map_frame(env, &fcap);
    test_assert(frame != NULL);
    test_error_eq(seL4_TCB_ReadFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    /* Flush-to-zero on: 0x9f80. */
    uint32_t mxcsr = 0x9f80;
    memcpy(frame + 24, &mxcsr, 4);
    /* XSTATE_BV: x87 and SSE state present. */
    uint64_t bv;
    memcpy(&bv, frame + 512, 8);
    bv |= 3;
    memcpy(frame + 512, &bv, 8);
    test_error_eq(seL4_TCB_WriteFPU(get_helper_tcb(&t), fcap, 0), seL4_NoError);
    start_helper(env, &t, read_mxcsr, 0, 0, 0, 0);
    test_eq(wait_for_helper(&t), 0x9f80);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4FPU0002, "A thread runs with the FPU state written to it (l4h 0002)", test_fpu_write_runs, true)

/* ---- l4h 0009: seL4_X86_ExecuteNever; 0023: TestAndClearAccessed ----- */

/* Map `cap` at `vaddr` with `attr`, after vspace has made the page tables. */
static int remap(env_t env, seL4_CPtr cap, void *vaddr, seL4_Word attr)
{
    int err = seL4_X86_Page_Unmap(cap);
    if (err) {
        return err;
    }
    return seL4_X86_Page_Map(cap, env->page_directory, (seL4_Word) vaddr, seL4_AllRights, attr);
}

static int jump_to(seL4_Word target, seL4_Word b, seL4_Word c, seL4_Word d)
{
    ((void (*)(void)) target)();
    return 0;
}

/* Executing from a page mapped ExecuteNever faults as an instruction fetch. */
static int test_execute_never(env_t env)
{
    seL4_CPtr fcap;
    uint8_t *page = map_frame(env, &fcap);
    test_assert(page != NULL);
    page[0] = 0xc3; /* ret */
    test_error_eq(remap(env, fcap, page, seL4_X86_Default_VMAttributes | seL4_X86_ExecuteNever), seL4_NoError);

    helper_thread_t t;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &t);
    int error = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                                  api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                  env->page_directory, seL4_NilData);
    test_error_eq(error, seL4_NoError);
    start_helper(env, &t, jump_to, (seL4_Word) page, 0, 0, 0);
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), (seL4_Word) page);
    test_eq(seL4_GetMR(seL4_VMFault_PrefetchFault), (seL4_Word) 1);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VM0001, "ExecuteNever mappings fault on instruction fetch (l4h 0009)", test_execute_never, true)

/* TestAndClearAccessed reports and clears the accessed bit. */
static int test_accessed(env_t env)
{
    seL4_CPtr fcap;
    volatile uint8_t *page = map_frame(env, &fcap);
    test_assert(page != NULL);
    (void) page[0];
    seL4_X86_Page_TestAndClearAccessed_t r = seL4_X86_Page_TestAndClearAccessed(fcap);
    test_error_eq(r.error, seL4_NoError);
    test_eq(r.accessed, (seL4_Word) 1);
    r = seL4_X86_Page_TestAndClearAccessed(fcap);
    test_error_eq(r.error, seL4_NoError);
    test_eq(r.accessed, (seL4_Word) 0);
    /* The bit was cleared without a flush: drop the TLB entry, then touch. */
    test_error_eq(remap(env, fcap, (void *) page, seL4_X86_Default_VMAttributes), seL4_NoError);
    (void) page[1];
    r = seL4_X86_Page_TestAndClearAccessed(fcap);
    test_eq(r.accessed, (seL4_Word) 1);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VM0002, "Page_TestAndClearAccessed (l4h 0023)", test_accessed, true)

/* ---- l4h 0029: Page_DeriveSubframe ------------------------------------ */

/* 4 KiB aliases of a 2 MiB frame see its contents. */
static int test_derive_subframe(env_t env)
{
    seL4_CPtr large = vka_alloc_frame_leaky(&env->vka, seL4_LargePageBits);
    if (!large) {
        return sel4test_get_result();
    }
    uint8_t *big = vspace_map_pages(&env->vspace, &large, NULL, seL4_AllRights, 1, seL4_LargePageBits, 1);
    test_assert(big != NULL);
    for (int i = 0; i < 4; i++) {
        big[0x3000 + i * 4096] = 0x50 + i;
    }
    /* The aliases go in a new 4-slot CNode, then move to our CSpace. */
    vka_object_t cn;
    test_error_eq(vka_alloc_cnode_object(&env->vka, 2, &cn), 0);
    int err = seL4_X86_Page_DeriveSubframe(large, env->cspace_root, cn.cptr, seL4_WordBits, 0, 0x3000, 4, seL4_AllRights);
    test_error_eq(err, seL4_NoError);
    seL4_CPtr subs[4];
    for (int i = 0; i < 4; i++) {
        subs[i] = get_free_slot(env);
        test_error_eq(seL4_CNode_Move(env->cspace_root, subs[i], seL4_WordBits, cn.cptr, i, 2), seL4_NoError);
    }
    for (int i = 0; i < 4; i++) {
        seL4_CPtr sub = subs[i];
        uint8_t *p = vspace_map_pages(&env->vspace, &sub, NULL, seL4_AllRights, 1, seL4_PageBits, 1);
        test_assert(p != NULL);
        test_eq((int) p[0], 0x50 + i);
        p[1] = 0x60 + i;
        test_eq((int) big[0x3001 + i * 4096], 0x60 + i);
    }
    /* Revoking the large frame removes its aliases. */
    test_error_eq(cnode_revoke(env, large), seL4_NoError);
    test_check(is_slot_empty(env, subs[0]));
    return sel4test_get_result();
}
DEFINE_TEST(FL4VM0003, "Page_DeriveSubframe aliases a 2 MiB frame (l4h 0029)", test_derive_subframe, true)

/* ---- l4h 0028: user selectors ---------------------------------------- */

static int test_user_selectors(env_t env)
{
    uint16_t cs, ss;
    __asm__ volatile("mov %%cs, %0" : "=r"(cs));
    __asm__ volatile("mov %%ss, %0" : "=r"(ss));
    test_eq((int) cs, 0x33);
    test_eq((int) ss, 0x2b);
    return sel4test_get_result();
}
DEFINE_TEST(FL4SEL0001, "User code runs with the Linux selectors (l4h 0028)", test_user_selectors, true)

/* ---- l4h 0017: seL4_X86_DeferFlush and seL4_X64_PML4_Flush ------------ */

static int write_byte(seL4_Word addr, seL4_Word b, seL4_Word c, seL4_Word d)
{
    *(volatile uint8_t *) addr = 1;
    return 0;
}

/* A remap that lowers rights with DeferFlush takes effect, on every core,
 * once the address space is flushed. */
static int test_defer_flush(env_t env)
{
    seL4_CPtr fcap;
    volatile uint8_t *page = map_frame(env, &fcap);
    test_assert(page != NULL);
    page[0] = 1;
    int err = seL4_X86_Page_Map(fcap, env->page_directory, (seL4_Word) page, seL4_CanRead,
                                seL4_X86_Default_VMAttributes | seL4_X86_DeferFlush);
    test_error_eq(err, seL4_NoError);
    test_error_eq(seL4_X64_PML4_Flush(env->page_directory), seL4_NoError);

    helper_thread_t t;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &t);
    err = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                            api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                            env->page_directory, seL4_NilData);
    test_error_eq(err, seL4_NoError);
    start_helper(env, &t, write_byte, (seL4_Word) page, 0, 0, 0);
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), (seL4_Word) page);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VM0004, "DeferFlush remaps take effect after PML4_Flush (l4h 0017)", test_defer_flush, true)

/* ---- FL4: TCB_CopyRegisters stalls a running source ------------------- */

static int count_forever(seL4_Word counter, seL4_Word b, seL4_Word c, seL4_Word d)
{
    volatile seL4_Word *n = (volatile seL4_Word *) counter;
    while (1) {
        (*n)++;
    }
    return 0;
}

/* Copying from a thread running on another core with suspendSource stops
 * it at once (DESIGN.md §4, fixes found while building FL4). seL4 stalls
 * only the target, so the source runs on until that core next enters the
 * kernel. */
static int test_copy_registers_stalls_source(env_t env)
{
    if (env->cores < 2) {
        return sel4test_get_result();
    }
    helper_thread_t src, dst;
    volatile seL4_Word counter = 0;
    create_helper_thread(env, &src);
    create_helper_thread(env, &dst);
    set_helper_affinity(env, &src, 1);
    start_helper(env, &src, count_forever, (seL4_Word) &counter, 0, 0, 0);
    while (counter == 0) {
    }
    int err = seL4_TCB_CopyRegisters(get_helper_tcb(&dst), get_helper_tcb(&src), true, false, true, true, 0);
    test_error_eq(err, seL4_NoError);
    seL4_Word stopped = counter;
    uint64_t until = rdtsc() + 20000000;
    while (rdtsc() < until) {
    }
    test_eq(counter, stopped);
    cleanup_helper(env, &src);
    cleanup_helper(env, &dst);
    return sel4test_get_result();
}
DEFINE_TEST(FL4SMP0001, "CopyRegisters with suspendSource stops a source on another core", test_copy_registers_stalls_source,
            config_set(CONFIG_ENABLE_SMP_SUPPORT))

/* ---- l4h 0008: error replies start with an empty message ------------ */

/* With KernelInvocationReportErrorIPC, the error string in the IPC buffer
 * belongs to the invocation that failed: whatever the buffer held before,
 * a failed invocation leaves it empty (FL4 keeps no error strings). */
static int test_error_string_empty(env_t env)
{
#ifdef CONFIG_KERNEL_INVOCATION_REPORT_ERROR_IPC
    char *s = seL4_GetDebugError();
    strcpy(s, "stale");
    char old = seL4_CanPrintError();
    seL4_SetPrintError(0);
    /* Slot 0 is always empty: suspending it fails with InvalidCapability. */
    int error = seL4_TCB_Suspend(seL4_CapNull);
    seL4_SetPrintError(old);
    test_eq(error, seL4_InvalidCapability);
    test_eq(s[0], 0);
#endif
    return sel4test_get_result();
}
DEFINE_TEST(FL4ERR0001, "A failed invocation reports no stale error string (l4h 0008)", test_error_string_empty, true)

/* ---- IPC round trips (DESIGN.md §12, performance) ------------------- */

static int ipc_server(seL4_Word ep, seL4_Word reply, seL4_Word c, seL4_Word d)
{
    seL4_Word badge;
    seL4_Recv(ep, &badge, reply);
    while (1) {
        seL4_ReplyRecv(ep, seL4_MessageInfo_new(0, 0, 0, 0), &badge, reply);
    }
    return 0;
}

/* Not a pass/fail check: prints the cost of a same-address-space
 * Call/ReplyRecv round trip, and gives a profiler a steady IPC loop. */
static int test_ipc_round_trip(env_t env)
{
    enum { N = 2000000 };
    helper_thread_t server;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &server);
    set_helper_priority(env, &server, env->priority);
    start_helper(env, &server, ipc_server, ep, reply.cptr, 0, 0);
    seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
    uint64_t t0 = rdtsc();
    for (int i = 0; i < N; i++) {
        seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
    }
    uint64_t t1 = rdtsc();
    printf("FL4 IPC: %lu TSC ticks per Call/ReplyRecv round trip\n", (unsigned long)((t1 - t0) / N));
    cleanup_helper(env, &server);
    return sel4test_get_result();
}
DEFINE_TEST(FL4PERF0001, "IPC round trip cost (printed, not checked)", test_ipc_round_trip, true)

/* ---- Lazy FPU switching (DESIGN.md §3) ------------------------------ */

static inline void xmm1_set(uint64_t v)
{
    __asm__ volatile("movq %0, %%xmm1" :: "r"(v) : "xmm1");
}

static inline uint64_t xmm1_get(void)
{
    uint64_t v;
    __asm__ volatile("movq %%xmm1, %0" : "=r"(v));
    return v;
}

static int fpu_pong(seL4_Word ep, seL4_Word reply, seL4_Word c, seL4_Word d)
{
    seL4_Word badge;
    seL4_Recv(ep, &badge, reply);
    xmm1_set(0x5e5e5e5e00000000ull);
    seL4_Word bad = 0;
    while (1) {
        if (xmm1_get() != 0x5e5e5e5e00000000ull) {
            bad++;
        }
        seL4_SetMR(0, bad);
        seL4_ReplyRecv(ep, seL4_MessageInfo_new(0, 0, 0, 1), &badge, reply);
    }
    return 0;
}

/* Two threads keep different values in xmm1 across IPCs: each must see its
 * own after every switch, whichever way the FPU is switched. */
static int test_fpu_ping_pong(env_t env)
{
    helper_thread_t server;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &server);
    set_helper_priority(env, &server, env->priority);
    start_helper(env, &server, fpu_pong, ep, reply.cptr, 0, 0);
    seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
    int mine_bad = 0;
    for (int i = 0; i < 10000; i++) {
        xmm1_set(0xc1c1c1c100000000ull + i);
        seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
        if (xmm1_get() != 0xc1c1c1c100000000ull + i) {
            mine_bad++;
        }
    }
    test_eq(mine_bad, 0);
    test_eq((int) seL4_GetMR(0), 0);
    cleanup_helper(env, &server);
    return sel4test_get_result();
}
DEFINE_TEST(FL4FPU0003, "Threads keep their own FPU registers across IPC", test_fpu_ping_pong, true)

/* ---- 20-bit ASIDs (DESIGN.md §3) ------------------------------------- */

static int add_one(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    return a + 1;
}

/*
 * Make 200 ASID pools: the last one's ASIDs are above 2^16, past what
 * seL4 has, so a process there runs on a PCID of its core's cache and its
 * mapping caps carry the high ASID bits. Remapping a frame checks that its
 * cap still names the process's ASID.
 */
static int test_high_asids(env_t env)
{
    seL4_CPtr pool = 0;
    for (int i = 0; i < 200; i++) {
        seL4_CPtr ut = vka_alloc_untyped_leaky(&env->vka, seL4_ASIDPoolBits);
        test_assert(ut);
        cspacepath_t path;
        test_eq(vka_cspace_alloc_path(&env->vka, &path), 0);
        test_eq(seL4_X86_ASIDControl_MakePool(env->asid_ctrl, ut, env->cspace_root, path.capPtr, path.capDepth),
                seL4_NoError);
        pool = path.capPtr;
    }
    helper_thread_t t;
    create_helper_process_custom_asid(env, &t, pool);
    void *v = vspace_new_pages(&t.process.vspace, seL4_AllRights, 1, seL4_PageBits);
    test_assert(v != NULL);
    seL4_CPtr frame = vspace_get_cap(&t.process.vspace, v);
    test_eq(seL4_X86_Page_Map(frame, t.process.pd.cptr, (seL4_Word) v, seL4_AllRights, seL4_X86_Default_VMAttributes),
            seL4_NoError);
    start_helper(env, &t, add_one, 41, 0, 0, 0);
    test_eq(wait_for_helper(&t), 42);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4ASID0001, "A process with an ASID above 2^16 runs, and its mapping caps keep the ASID", test_high_asids, true)

/* ---- Unmap of PAT mappings ------------------------------------------- */

static int read_byte(seL4_Word addr, seL4_Word b, seL4_Word c, seL4_Word d)
{
    return *(volatile uint8_t *) addr;
}

/*
 * A 4 KiB mapping with the PAT bit (write-combining) is really unmapped:
 * bit 7 of a 4K entry is PAT, which FL4 once mistook for the large-page
 * bit and left the entry in place.
 */
static int test_unmap_pat(env_t env)
{
    seL4_CPtr fcap;
    volatile uint8_t *page = map_frame(env, &fcap);
    test_assert(page != NULL);
    test_error_eq(remap(env, fcap, (void *) page, seL4_X86_WriteCombining), seL4_NoError);
    page[0] = 1;
    test_error_eq(seL4_X86_Page_Unmap(fcap), seL4_NoError);

    helper_thread_t t;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &t);
    int error = api_tcb_set_space(get_helper_tcb(&t), fault_ep, env->cspace_root,
                                  api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                                  env->page_directory, seL4_NilData);
    test_error_eq(error, seL4_NoError);
    start_helper(env, &t, read_byte, (seL4_Word) page, 0, 0, 0);
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_VMFault);
    test_eq(seL4_GetMR(seL4_VMFault_Addr), (seL4_Word) page);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4VM0005, "Unmapping a 4K page mapped with PAT removes the mapping", test_unmap_pat, true)

/* ---- Security audit: debug exceptions and FS/GS bases at the boundary - */

#define RFLAGS_TF 0x100
#define FL4_DONE_LABEL 0x7d

/* Give `t` `fault_ep` as its fault handler. */
static int set_fault_ep(env_t env, helper_thread_t *t, seL4_CPtr fault_ep)
{
    return api_tcb_set_space(get_helper_tcb(t), fault_ep, env->cspace_root,
                             api_make_guard_skip_word(seL4_WordBits - env->cspace_size_bits),
                             env->page_directory, seL4_NilData);
}

static void reply_to(seL4_CPtr reply, seL4_MessageInfo_t info)
{
#ifdef CONFIG_KERNEL_MCS
    seL4_Send(reply, info);
#else
    (void) reply;
    seL4_Reply(info);
#endif
}

/* Answer a single-step or breakpoint fault so the thread goes on without
 * stepping: with the debug API, stop single-stepping; without it (a plain
 * #DB UserException), resume after the trap with TF clear. Returns 0 if
 * `tag` was such a fault. */
static int resume_after_debug_fault(seL4_MessageInfo_t tag, seL4_CPtr reply)
{
    seL4_Word label = seL4_MessageInfo_get_label(tag);
#ifdef CONFIG_HARDWARE_DEBUG_API
    if (label == seL4_Fault_DebugException) {
        seL4_SetMR(0, 0);
        reply_to(reply, seL4_MessageInfo_new(0, 0, 0, 1));
        return 0;
    }
#endif
    if (label == seL4_Fault_UserException && seL4_GetMR(seL4_UserException_Number) == 1) {
        seL4_Word ip = seL4_GetMR(seL4_UserException_FaultIP);
        seL4_Word sp = seL4_GetMR(seL4_UserException_SP);
        seL4_Word flags = seL4_GetMR(seL4_UserException_FLAGS) & ~(seL4_Word) RFLAGS_TF;
        seL4_SetMR(seL4_UserException_FaultIP, ip);
        seL4_SetMR(seL4_UserException_SP, sp);
        seL4_SetMR(seL4_UserException_FLAGS, flags);
        reply_to(reply, seL4_MessageInfo_new(0, 0, 0, 3));
        return 0;
    }
    return -1;
}

/* Set TF itself: the next instruction raises #DB from user mode, on the
 * #DB IST stack. */
static int set_trap_flag(seL4_Word a, seL4_Word b, seL4_Word c, seL4_Word d)
{
    __asm__ volatile("pushfq\n\torq $0x100, (%%rsp)\n\tpopfq\n\tnop" ::: "memory", "cc");
    return 0x5a5a;
}

/* A user #DB on another core is that core's entry: the kernel must not run
 * it as core 0 (whose current thread, state and gate slot it would use). */
static int test_user_debug_trap_on_ap(env_t env)
{
    helper_thread_t t;
    vka_object_t reply;
    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
    seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
    create_helper_thread(env, &t);
    test_error_eq(set_fault_ep(env, &t, fault_ep), seL4_NoError);
    if (env->cores >= 2) {
        set_helper_affinity(env, &t, 1);
    }
    start_helper(env, &t, set_trap_flag, 0, 0, 0, 0);
    seL4_Word badge;
    seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
#ifdef CONFIG_HARDWARE_DEBUG_API
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_DebugException);
    test_eq(seL4_GetMR(seL4_DebugException_ExceptionReason), (seL4_Word) seL4_SingleStep);
#else
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) seL4_Fault_UserException);
    test_eq(seL4_GetMR(seL4_UserException_Number), (seL4_Word) 1);
#endif
    test_eq(resume_after_debug_fault(tag, reply.cptr), 0);
    test_eq(wait_for_helper(&t), 0x5a5a);
    cleanup_helper(env, &t);
    return sel4test_get_result();
}
DEFINE_TEST(FL4SMP0002, "A user-set trap flag on another core faults on that core", test_user_debug_trap_on_ap, true)

/* The selector MOV SS loads, under a data breakpoint. */
static volatile uint16_t fl4_ss_selector = 0x2b;

/* Path 0: single-step a SYSCALL. Path 1: MOV SS from a watched word, then
 * SYSCALL, so the #DB the CPU holds back for MOV SS arrives after SYSCALL
 * has switched to kernel mode (CVE-2018-8897). Either #DB belongs to user
 * mode; the thread then says it is done on `done_ep`. */
static int debug_across_syscall(seL4_Word path, seL4_Word done_ep, seL4_Word c, seL4_Word d)
{
    seL4_Word rax = 0;
    if (path == 0) {
        __asm__ volatile("pushfq\n\torq $0x100, (%%rsp)\n\tpopfq\n\tsyscall"
                         : "+a"(rax) : "d"((seL4_Word) seL4_SysYield) : "rcx", "r11", "memory", "cc");
    } else {
        __asm__ volatile("movw (%1), %%ss\n\tsyscall"
                         : "+a"(rax) : "r"(&fl4_ss_selector), "d"((seL4_Word) seL4_SysYield)
                         : "rcx", "r11", "memory");
    }
    seL4_Send(done_ep, seL4_MessageInfo_new(FL4_DONE_LABEL, 0, 0, 0));
    return 0x7e57;
}

/* A kernel-mode #DB at the SYSCALL entry is user mode's: the kernel goes
 * on with the syscall instead of stopping at a kernel exception. */
static int test_debug_across_syscall(env_t env)
{
    int paths = 1;
#ifdef CONFIG_HARDWARE_DEBUG_API
    paths = 2;
#endif
    for (int path = 0; path < paths; path++) {
        helper_thread_t t;
        vka_object_t reply;
        test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
        seL4_CPtr fault_ep = vka_alloc_endpoint_leaky(&env->vka);
        create_helper_thread(env, &t);
        test_error_eq(set_fault_ep(env, &t, fault_ep), seL4_NoError);
#ifdef CONFIG_HARDWARE_DEBUG_API
        if (path == 1) {
            int err = seL4_TCB_SetBreakpoint(get_helper_tcb(&t), 0, (seL4_Word) &fl4_ss_selector,
                                             seL4_DataBreakpoint, 2, seL4_BreakOnReadWrite);
            test_error_eq(err, seL4_NoError);
        }
#endif
        start_helper(env, &t, debug_across_syscall, path, fault_ep, 0, 0);
        /* Debug faults, if the CPU reports the #DB in user mode, then done. */
        for (int faults = 0; ; faults++) {
            test_assert(faults < 4);
            seL4_Word badge;
            seL4_MessageInfo_t tag = api_recv(fault_ep, &badge, reply.cptr);
            if (seL4_MessageInfo_get_label(tag) == FL4_DONE_LABEL) {
                break;
            }
            test_eq(resume_after_debug_fault(tag, reply.cptr), 0);
        }
        test_eq(wait_for_helper(&t), 0x7e57);
        cleanup_helper(env, &t);
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4DBG0001, "A #DB held across SYSCALL (single step, MOV SS) is not a kernel fault",
            test_debug_across_syscall, true)

/* Raw syscalls that touch no thread-local storage: these threads run with
 * an FS base that is not their TLS. */
static inline __attribute__((always_inline)) void raw_recv(seL4_Word ep, seL4_Word reply)
{
    register seL4_Word r12 __asm__("r12") = reply;
    seL4_Word src = ep, info;
    __asm__ volatile("movq %%rsp, %%rbx\n\tsyscall\n\tmovq %%rbx, %%rsp"
                     : "+D"(src), "=S"(info)
                     : "d"((seL4_Word) seL4_SysRecv), "r"(r12)
                     : "rbx", "rcx", "r11", "r10", "r8", "r9", "r15", "memory");
}

static inline __attribute__((always_inline)) void raw_send(seL4_Word ep, seL4_Word mr0)
{
    register seL4_Word r10 __asm__("r10") = mr0;
    __asm__ volatile("movq %%rsp, %%rbx\n\tsyscall\n\tmovq %%rbx, %%rsp"
                     :
                     : "d"((seL4_Word) seL4_SysSend), "D"(ep), "S"(seL4_MessageInfo_new(0, 0, 0, 1).words[0]), "r"(r10)
                     : "rbx", "rcx", "r11", "memory");
}

/* Waits for `go`, loads FS with a selector (which sets the hidden base to
 * the descriptor's, 0), then wakes the reader. */
__attribute__((no_stack_protector))
static int fs_clobberer(seL4_Word ready, seL4_Word go, seL4_Word reply, seL4_Word next)
{
    seL4_Send(ready, seL4_MessageInfo_new(0, 0, 0, 0));
    raw_recv(go, reply);
    __asm__ volatile("movw %0, %%fs" : : "r"((uint16_t) 0x2b));
    raw_send(next, 0);
    raw_recv(go, reply);
    return 0;
}

/* Waits to be woken, then reads the word at its FS base and sends it. */
__attribute__((no_stack_protector))
static int fs_reader(seL4_Word ready, seL4_Word go, seL4_Word reply, seL4_Word result)
{
    seL4_Send(ready, seL4_MessageInfo_new(0, 0, 0, 0));
    raw_recv(go, reply);
    seL4_Word v;
    __asm__ volatile("movq %%fs:0, %0" : "=r"(v));
    raw_send(result, v);
    raw_recv(go, reply);
    return 0;
}

/* Two threads with the same FS base: the first changes its hidden FS base
 * by loading a selector (which needs no FSGSBASE), then switches to the
 * second, which must run with the base it was given. */
static int test_fs_base_after_selector_load(env_t env)
{
    const uint64_t magic = 0x1122334455667788ULL;
    seL4_CPtr fcap;
    uint64_t *page = map_frame(env, &fcap);
    test_assert(page != NULL);
    page[0] = magic;
    seL4_CPtr ready = vka_alloc_endpoint_leaky(&env->vka);
    seL4_CPtr go1 = vka_alloc_endpoint_leaky(&env->vka);
    seL4_CPtr go2 = vka_alloc_endpoint_leaky(&env->vka);
    seL4_CPtr result = vka_alloc_endpoint_leaky(&env->vka);
    vka_object_t r1, r2, rmain;
    test_error_eq(vka_alloc_reply(&env->vka, &r1), 0);
    test_error_eq(vka_alloc_reply(&env->vka, &r2), 0);
    test_error_eq(vka_alloc_reply(&env->vka, &rmain), 0);
    helper_thread_t t1, t2;
    create_helper_thread(env, &t1);
    create_helper_thread(env, &t2);
    /* A fault of the reader (reading through a stale base) comes here too. */
    test_error_eq(set_fault_ep(env, &t2, result), seL4_NoError);
    /* Below this thread: once it waits for the result, only they run on
     * this core, the reader right after the writer. */
    set_helper_priority(env, &t1, env->priority - 1);
    set_helper_priority(env, &t2, env->priority - 1);
    start_helper(env, &t2, fs_reader, ready, go2, r2.cptr, result);
    start_helper(env, &t1, fs_clobberer, ready, go1, r1.cptr, go2);
    seL4_Word badge;
    api_recv(ready, &badge, rmain.cptr);
    api_recv(ready, &badge, rmain.cptr);
    /* Both are past their last use of their TLS. */
    test_error_eq(seL4_TCB_SetTLSBase(get_helper_tcb(&t1), (seL4_Word) page), seL4_NoError);
    test_error_eq(seL4_TCB_SetTLSBase(get_helper_tcb(&t2), (seL4_Word) page), seL4_NoError);
    seL4_Send(go1, seL4_MessageInfo_new(0, 0, 0, 0));
    seL4_MessageInfo_t tag = api_recv(result, &badge, rmain.cptr);
    test_eq(seL4_MessageInfo_get_label(tag), (seL4_Word) 0);
    test_eq((uint64_t) seL4_GetMR(0), magic);
    cleanup_helper(env, &t1);
    cleanup_helper(env, &t2);
    return sel4test_get_result();
}
DEFINE_TEST(FL4TLS0001, "A selector load in one thread does not change the FS base of the next",
            test_fs_base_after_selector_load, true)
