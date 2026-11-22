/*
 * Multi-core IPC scaling (DESIGN.md §12, performance): k independent
 * client/server pairs, pair i on core i, for k = 1 up to the number of
 * cores. Uses only the seL4 API, so the same test runs on FL4 and on
 * upstream seL4 (`FL4_KERNEL=sel4`): FL4 should scale, seL4's big kernel
 * lock should not. Prints throughput; nothing is checked.
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

#define CALLS 100000

static uint64_t tsc(void)
{
#ifdef CONFIG_ARCH_AARCH64
    uint64_t v;
    __asm__ volatile("isb; mrs %0, cntvct_el0" : "=r"(v));
    return v;
#else
    return __builtin_ia32_rdtsc();
#endif
}

static int scale_server(seL4_Word ep, seL4_Word reply, seL4_Word c, seL4_Word d)
{
    seL4_Word badge;
    seL4_Recv(ep, &badge, reply);
    while (1) {
        seL4_ReplyRecv(ep, seL4_MessageInfo_new(0, 0, 0, 0), &badge, reply);
    }
    return 0;
}

struct span {
    volatile uint64_t start, end;
};

static int scale_client(seL4_Word ep, seL4_Word done, seL4_Word span, seL4_Word d)
{
    struct span *s = (struct span *) span;
    /* The first Call meets the server; time the rest. */
    seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
    s->start = tsc();
    for (int i = 0; i < CALLS; i++) {
        seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
    }
    s->end = tsc();
    seL4_Signal(done);
    while (1) {
        seL4_Yield();
    }
    return 0;
}

static int test_ipc_scaling(env_t env)
{
    int n = env->cores;
    for (int k = 1; k <= n; k++) {
        /* Static: a helper_thread_t per core overflows the test's stack
         * on many cores. */
        static helper_thread_t servers[CONFIG_MAX_NUM_NODES], clients[CONFIG_MAX_NUM_NODES];
        static vka_object_t replies[CONFIG_MAX_NUM_NODES];
        static seL4_CPtr done[CONFIG_MAX_NUM_NODES];
        static struct span spans[CONFIG_MAX_NUM_NODES];
        for (int i = 0; i < k; i++) {
            seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
            test_error_eq(vka_alloc_reply(&env->vka, &replies[i]), 0);
            done[i] = vka_alloc_notification_leaky(&env->vka);
            spans[i].start = spans[i].end = 0;
            create_helper_thread(env, &servers[i]);
            create_helper_thread(env, &clients[i]);
            set_helper_priority(env, &servers[i], env->priority);
            set_helper_priority(env, &clients[i], env->priority);
            set_helper_affinity(env, &servers[i], i);
            set_helper_affinity(env, &clients[i], i);
            start_helper(env, &servers[i], scale_server, ep, replies[i].cptr, 0, 0);
            start_helper(env, &clients[i], scale_client, ep, done[i], (seL4_Word) &spans[i], 0);
        }
        uint64_t first = UINT64_MAX, last = 0;
        for (int i = 0; i < k; i++) {
            seL4_Wait(done[i], NULL);
            if (spans[i].start < first) {
                first = spans[i].start;
            }
            if (spans[i].end > last) {
                last = spans[i].end;
            }
        }
        uint64_t ticks = last - first;
        printf("IPC scaling: %d pair(s): %lu round trips per million TSC ticks\n", k,
               (unsigned long)((uint64_t) k * CALLS * 1000000 / (ticks ? ticks : 1)));
        for (int i = 0; i < k; i++) {
            cleanup_helper(env, &clients[i]);
            cleanup_helper(env, &servers[i]);
        }
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4PERF0002, "Multi-core IPC scaling (printed, not checked)", test_ipc_scaling,
            config_set(CONFIG_ENABLE_SMP_SUPPORT))

/*
 * Kernel-intensive SMP throughput (DESIGN.md §12): for k = 1, 2, 4, ... up
 * to the number of cores, k workers, worker i on core i, each repeat one
 * kernel operation on objects of its own for a fixed window of TSC ticks
 * (all start together), so a run takes seconds however slow an operation
 * is. Prints aggregate operations per million TSC ticks. With independent objects FL4's transactions should
 * scale; seL4's big kernel lock serialises every entry.
 *
 *   yield    seL4_Yield
 *   signal   seL4_Signal + seL4_Wait on the worker's notification
 *   ipc      seL4_Call to a server thread on the same core (ReplyRecv)
 *   xipc     seL4_Call to a server on the next core (k >= 2)
 *   cap      CNode_Copy of a cap into a slot, then CNode_Delete
 *   retype   Untyped_Retype of an endpoint, then CNode_Delete (the next
 *            retype resets the untyped)
 *   map      Page_Unmap + Page_Map of a 4 KiB frame (one shared address
 *            space, so each unmap also shoots down the other workers' cores)
 */
/* Each measurement: the workers start together at `begin` and stop at
 * `begin + KWINDOW` (about 26 ms at 3.8 GHz). */
#define KWINDOW 100000000ull

enum { W_YIELD, W_SIGNAL, W_IPC, W_XIPC, W_CAP, W_RETYPE, W_MAP, W_COUNT };
static const char *wname[W_COUNT] = { "yield", "signal", "ipc", "xipc", "cap", "retype", "map" };

struct kwork {
    int kind;
    seL4_CPtr ntfn, ep, done;
    cspacepath_t src, dst, ut;
    seL4_CPtr frame, pd;
    seL4_Word vaddr;
    volatile uint64_t begin, ops;
    volatile int err;
};

static int kworker(seL4_Word arg, seL4_Word b, seL4_Word c, seL4_Word d)
{
    struct kwork *w = (struct kwork *) arg;
    int err = 0;
    /* One untimed operation meets the IPC server; then wait for the start. */
    uint64_t ops = 0, stop = w->begin + KWINDOW;
    for (int round = 0; round < 2; round++) {
        if (round) {
            while (tsc() < w->begin) {
            }
        }
        while (!err && (round ? tsc() < stop : ops == 0)) {
            switch (w->kind) {
            case W_YIELD:
                seL4_Yield();
                break;
            case W_SIGNAL:
                seL4_Signal(w->ntfn);
                seL4_Wait(w->ntfn, NULL);
                break;
            case W_IPC:
            case W_XIPC:
                seL4_Call(w->ep, seL4_MessageInfo_new(0, 0, 0, 0));
                break;
            case W_CAP:
                err = seL4_CNode_Copy(w->dst.root, w->dst.capPtr, w->dst.capDepth,
                                      w->src.root, w->src.capPtr, w->src.capDepth, seL4_AllRights);
                err = err ? err : seL4_CNode_Delete(w->dst.root, w->dst.capPtr, w->dst.capDepth);
                break;
            case W_RETYPE:
                err = seL4_Untyped_Retype(w->ut.capPtr, seL4_EndpointObject, 0, w->dst.root,
                                          w->dst.dest, w->dst.destDepth, w->dst.offset, 1);
                err = err ? err : seL4_CNode_Delete(w->dst.root, w->dst.capPtr, w->dst.capDepth);
                break;
            case W_MAP:
#ifdef CONFIG_ARCH_AARCH64
                err = seL4_ARM_Page_Unmap(w->frame);
                err = err ? err : seL4_ARM_Page_Map(w->frame, w->pd, w->vaddr, seL4_AllRights,
                                                    seL4_ARM_Default_VMAttributes);
#else
                err = seL4_X86_Page_Unmap(w->frame);
                err = err ? err : seL4_X86_Page_Map(w->frame, w->pd, w->vaddr, seL4_AllRights,
                                                    seL4_X86_Default_VMAttributes);
#endif
                break;
            }
            ops++;
        }
        if (!round) {
            ops = 0;
        }
    }
    w->ops = ops;
    w->err = err;
    seL4_Signal(w->done);
    while (1) {
        seL4_Yield();
    }
    return 0;
}

static int test_kernel_scaling(env_t env)
{
    int n = env->cores;
    for (int kind = 0; kind < W_COUNT; kind++) {
        for (int k = 1; k <= n; k = k < 4 ? k * 2 : (k + 2 > n && k != n ? n : k + 2)) {
            if (kind == W_XIPC && k < 2) {
                continue;
            }
            /* Static, as in test_ipc_scaling. */
            static helper_thread_t workers[CONFIG_MAX_NUM_NODES], servers[CONFIG_MAX_NUM_NODES];
            static struct kwork w[CONFIG_MAX_NUM_NODES];
            int nserv = 0;
            for (int i = 0; i < k; i++) {
                memset(&w[i], 0, sizeof(w[i]));
                w[i].kind = kind;
                w[i].done = vka_alloc_notification_leaky(&env->vka);
                w[i].ntfn = vka_alloc_notification_leaky(&env->vka);
                if (kind == W_IPC || kind == W_XIPC) {
                    vka_object_t reply;
                    w[i].ep = vka_alloc_endpoint_leaky(&env->vka);
                    test_error_eq(vka_alloc_reply(&env->vka, &reply), 0);
                    create_helper_thread(env, &servers[i]);
                    set_helper_priority(env, &servers[i], env->priority);
                    set_helper_affinity(env, &servers[i], kind == W_IPC ? i : (i + 1) % k);
                    start_helper(env, &servers[i], scale_server, w[i].ep, reply.cptr, 0, 0);
                    nserv++;
                }
                if (kind == W_CAP || kind == W_RETYPE) {
                    vka_cspace_make_path(&env->vka, w[i].ntfn, &w[i].src);
                    seL4_CPtr slot;
                    test_error_eq(vka_cspace_alloc(&env->vka, &slot), 0);
                    vka_cspace_make_path(&env->vka, slot, &w[i].dst);
                }
                if (kind == W_RETYPE) {
                    seL4_CPtr ut = vka_alloc_untyped_leaky(&env->vka, seL4_PageBits);
                    test_assert(ut);
                    vka_cspace_make_path(&env->vka, ut, &w[i].ut);
                }
                if (kind == W_MAP) {
                    void *v = vspace_new_pages(&env->vspace, seL4_AllRights, 1, seL4_PageBits);
                    test_assert(v != NULL);
                    w[i].vaddr = (seL4_Word) v;
                    w[i].frame = vspace_get_cap(&env->vspace, v);
                    w[i].pd = env->page_directory;
                }
                create_helper_thread(env, &workers[i]);
                set_helper_priority(env, &workers[i], env->priority);
                set_helper_affinity(env, &workers[i], i);
            }
            /* Start 20M ticks from now: enough for every worker to start. */
            uint64_t begin = tsc() + 20000000;
            for (int i = 0; i < k; i++) {
                w[i].begin = begin;
                start_helper(env, &workers[i], kworker, (seL4_Word) &w[i], 0, 0, 0);
            }
            uint64_t ops = 0;
            for (int i = 0; i < k; i++) {
                seL4_Wait(w[i].done, NULL);
                test_eq(w[i].err, 0);
                ops += w[i].ops;
            }
            printf("KBENCH %s cores=%d ops_per_Mtick=%lu\n", wname[kind], k,
                   (unsigned long)(ops * 1000000 / KWINDOW));
            for (int i = 0; i < k; i++) {
                cleanup_helper(env, &workers[i]);
            }
            for (int i = 0; i < nserv; i++) {
                cleanup_helper(env, &servers[i]);
            }
        }
    }
    return sel4test_get_result();
}
DEFINE_TEST(FL4PERF0003, "Kernel-intensive SMP scaling (printed, not checked)", test_kernel_scaling,
            config_set(CONFIG_ENABLE_SMP_SUPPORT))
