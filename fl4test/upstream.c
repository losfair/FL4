/*
 * sel4test cases that upstream turns off because seL4 fails them, run under
 * FL4 names (DESIGN.md §12). sel4test itself stays unmodified. Uses only
 * the seL4 API, so the same tests also run on upstream seL4
 * (`FL4_KERNEL=sel4`) for comparison.
 *
 *   FL4UP0001  IPC0028, cross-core SC donation to a passive server
 *              (seL4 issue #941, PR #986). Upstream seL4 hangs in it under
 *              KVM with 4 cores; FL4 passes.
 *
 * PAGEFAULT1005 (undefined instruction, inter-AS) is not ported: the test
 * itself is wrong. Its handler runs in another process and dereferences
 * the faulter's stack pointer and reads a static the faulter wrote, both
 * in its own address space, so it fails on any kernel. The kernel path it
 * exercises is PAGEFAULT0005's, in one address space.
 */
#include <stdio.h>
#include <sel4/sel4.h>
#include <vka/object.h>
#include <sel4test/testutil.h>
#include <sel4test/macros.h>

#include "../test.h"
#include "../helpers.h"

/* IPC0028, copied from upstream's ipc.c: a passive server on core 0
 * serves a client on every other core, each donating its SC. */
#define UP_RUNS 10

static void up_ipc28_server_fn(seL4_CPtr ep, seL4_CPtr reply, volatile int *state)
{
    api_nbsend_recv(ep, seL4_MessageInfo_new(0, 0, 0, 0), ep, NULL, reply);
    while (1) {
        *state = *state + 1;
        seL4_ReplyRecv(ep, seL4_MessageInfo_new(0, 0, 0, 0), NULL, reply);
    }
}

static int up_ipc28_client_fn(seL4_CPtr ep, volatile int *state)
{
    while (*state < UP_RUNS) {
        seL4_Call(ep, seL4_MessageInfo_new(0, 0, 0, 0));
        *state = *state + 1;
    }
    return 0;
}

static int test_sched_donation_cross_core(env_t env)
{
    seL4_CPtr ep = vka_alloc_endpoint_leaky(&env->vka);
    /* Static: a helper_thread_t per core overflows the test's stack on
     * many cores. */
    static helper_thread_t clients[CONFIG_MAX_NUM_NODES];
    helper_thread_t server;
    static volatile int states[CONFIG_MAX_NUM_NODES];
    volatile seL4_Word server_state = 0;

    create_helper_thread(env, &server);
    for (int i = 0; i < env->cores - 1; i++) {
        states[i] = 0;
        create_helper_thread(env, &clients[i]);
        set_helper_affinity(env, &clients[i], i + 1);
    }
    start_helper(env, &server, (helper_fn_t) up_ipc28_server_fn, ep, get_helper_reply(&server),
                 (seL4_Word) &server_state, 0);
    /* Wait for the server to start, then make it passive. */
    seL4_Wait(ep, NULL);
    int error = api_sc_unbind(get_helper_sched_context(&server));
    test_eq(error, seL4_NoError);

    for (int i = 0; i < env->cores - 1; i++) {
        start_helper(env, &clients[i], (helper_fn_t) up_ipc28_client_fn, ep, (seL4_Word) &states[i], 0, 0);
    }
    for (int i = 0; i < env->cores - 1; i++) {
        error = wait_for_helper(&clients[i]);
        test_eq(error, 0);
        test_eq(states[i], UP_RUNS);
    }
    test_eq(server_state, UP_RUNS * (env->cores - 1));
    return sel4test_get_result();
}
DEFINE_TEST(FL4UP0001, "IPC0028: cross-core SC donation", test_sched_donation_cross_core,
            config_set(CONFIG_ENABLE_SMP_SUPPORT))
