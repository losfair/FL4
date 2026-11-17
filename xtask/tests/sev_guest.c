/* Freestanding root task for the GCE SEV smoke test. Its only NVMe command
 * is Identify Controller. Boot firmware has already finished using the disk. */
#include <stddef.h>
#include <stdint.h>
#include <sel4/sel4.h>
#include <sel4/arch/bootinfo_types.h>

LIBSEL4_THREAD_LOCAL seL4_IPCBuffer *__sel4_ipc_buffer;
#ifdef CONFIG_KERNEL_INVOCATION_REPORT_ERROR_IPC
LIBSEL4_THREAD_LOCAL char __sel4_print_error;
#endif
__asm__(".bss\n.balign 16\n.skip 16384\nstack_top:\n.text\n.global _start\n"
        "_start: lea stack_top(%rip),%rsp\n call run\n ud2");

static void say(const char *s) { while (*s) seL4_DebugPutChar(*s++); }
#define CHECK(condition) do { if (!(condition)) { say("SEV test failed: " #condition "\n"); seL4_DebugHalt(); } } while (0)
#define ROOT seL4_CapInitThreadCNode
#define VSPACE seL4_CapInitThreadVSpace

static seL4_BootInfo *bi;
static seL4_CPtr next_slot, pci;
static const uintptr_t small_va = 0x20000000, large_va = 0x20200000;

static seL4_CPtr retype(seL4_CPtr parent, seL4_Word type, unsigned bits, unsigned count)
{
    seL4_CPtr first = next_slot;
    next_slot += count;
    CHECK(next_slot <= bi->empty.end);
    CHECK(!seL4_Untyped_Retype(parent, type, bits, ROOT, 0, 0, first, count));
    return first;
}

static void map(seL4_CPtr frame, uintptr_t va, seL4_X86_VMAttributes attr)
{
    CHECK(!seL4_X86_Page_Map(frame, VSPACE, va, seL4_AllRights, attr));
}

static uintptr_t address(seL4_CPtr frame)
{
    seL4_X86_Page_GetAddress_t result = seL4_X86_Page_GetAddress(frame);
    CHECK(!result.error);
    return result.paddr;
}

static uint32_t config(unsigned dev, unsigned reg)
{
    CHECK(!seL4_X86_IOPort_Out32(pci, 0xcf8, 0x80000000 | (dev << 11) | reg));
    seL4_X86_IOPort_In32_t result = seL4_X86_IOPort_In32(pci, 0xcfc);
    CHECK(!result.error);
    return result.result;
}

/* Split the device untyped covering this aligned physical region. */
static seL4_CPtr device_frames(uint64_t pa, unsigned target_bits)
{
    for (seL4_CPtr i = bi->untyped.start; i < bi->untyped.end; i++) {
        seL4_UntypedDesc u = bi->untypedList[i - bi->untyped.start];
        unsigned bits = u.sizeBits;
        uint64_t base = u.paddr;
        if (!u.isDevice || bits < target_bits || pa < base || pa - base > (1ULL << bits) - (1ULL << target_bits)) continue;
        seL4_CPtr parent = i;
        while (bits > target_bits) {
            uint64_t half = 1ULL << --bits;
            parent = retype(parent, seL4_UntypedObject, bits, 2);
            if (pa - base >= half) { base += half; parent++; }
        }
        CHECK(base == pa);
        CHECK(seL4_Untyped_RetypeShared(parent, ROOT, 0, 0, next_slot) == seL4_IllegalOperation);
        seL4_CPtr f = retype(parent, seL4_X86_4K, 0, 1u << (target_bits - 12));
        CHECK(address(f) == pa);
        return f;
    }
    CHECK(0);
    return 0;
}

static void check_module(void)
{
    const char *extra = (const char *)bi + seL4_BootInfoFrameSize;
    for (size_t pos = 0; pos < bi->extraLen;) {
        const seL4_BootInfoHeader *header = (const void *)(extra + pos);
        CHECK(header->len >= sizeof(*header) && header->len <= bi->extraLen - pos);
        if (header->id == SEL4_BOOTINFO_HEADER_X86_BOOT_MODULES) {
            const seL4_X86_BootModules_t *modules = (const void *)header;
            CHECK(modules->count == 1 && modules->modules[0].size == 8);
            seL4_CPtr f = device_frames(modules->modules[0].paddr, 12);
            uintptr_t va = small_va + 0x3000;
            map(f, va, seL4_X86_Default_VMAttributes);
            for (unsigned i = 0; i < 8; i++) CHECK(((volatile char *)va)[i] == "FL4 SEV!"[i]);
            return;
        }
        pos += header->len;
    }
    CHECK(0);
}

static void ready(volatile uint32_t *status, unsigned wanted)
{
    uint64_t start = __builtin_ia32_rdtsc();
    while ((*status & 1) != wanted) {
        CHECK(!(*status & 2) && __builtin_ia32_rdtsc() - start < 30000000000ULL);
        __builtin_ia32_pause();
    }
}

static void identify(uint64_t dma)
{
    pci = next_slot++;
    CHECK(!seL4_X86_IOPortControl_Issue(seL4_CapIOPortControl, 0xcf8, 0xcff, ROOT, pci, 64));
    unsigned dev = 0;
    while (dev < 32 && config(dev, 8) >> 8 != 0x010802) dev++;
    CHECK(dev < 32);
    unsigned vendor = config(dev, 0) & 0xffff;
    uint32_t low = config(dev, 0x10);
    uint64_t bar = low & ~15u;
    if ((low & 6) == 4) bar |= (uint64_t)config(dev, 0x14) << 32;
    seL4_CPtr mmio = device_frames(bar, 13);
    for (unsigned j = 0; j < 2; j++) map(mmio + j, small_va + j * 4096, seL4_X86_Uncacheable);
    uint16_t command = config(dev, 4);
    CHECK(!seL4_X86_IOPort_Out16(pci, 0xcfc, command | 6));

    volatile uint32_t *regs = (void *)small_va;
    volatile uint32_t *cc = regs + 0x14 / 4, *status = regs + 0x1c / 4;
    unsigned stride = 1u << (regs[1] & 15);
    CHECK(stride < 1024);
    *cc = 0;
    ready(status, 0);
    regs[0x24 / 4] = (1u << 16) | 1; /* two entries per admin queue */
    *(volatile uint64_t *)(small_va + 0x28) = dma;
    *(volatile uint64_t *)(small_va + 0x30) = dma + 4096;
    *cc = (4u << 20) | (6u << 16) | 1;
    ready(status, 1);

    volatile uint32_t *sq = (void *)large_va;
    volatile uint16_t *cq = (void *)(large_va + 4096);
    sq[0] = 0x06; /* Identify, command ID zero */
    sq[6] = (uint32_t)(dma + 8192);
    sq[7] = (uint32_t)((dma + 8192) >> 32);
    sq[10] = 1; /* CNS = Controller */
    __atomic_thread_fence(__ATOMIC_SEQ_CST);
    regs[0x1000 / 4] = 1;
    uint64_t start = __builtin_ia32_rdtsc();
    while (!(cq[7] & 1)) {
        CHECK(!(*status & 2) && __builtin_ia32_rdtsc() - start < 30000000000ULL);
        __builtin_ia32_pause();
    }
    CHECK(cq[7] == 1 && cq[6] == 0);
    CHECK(*(volatile uint16_t *)(large_va + 8192) == vendor);
    regs[0x1000 / 4 + stride] = 1;
    *cc = 0;
    ready(status, 0);
    say("SEV test: NVMe Identify DMA passed\n");
}

static void exercise(seL4_CPtr ram, unsigned bits, uintptr_t va)
{
    seL4_CPtr source = retype(ram, seL4_UntypedObject, bits, 1);
    unsigned type = bits == 12 ? seL4_X86_4K : seL4_X86_LargePageObject;
    volatile uint64_t *page = (void *)va;
    seL4_CPtr ordinary = retype(source, type, 0, 1);
    uint64_t pa = address(ordinary);
    map(ordinary, va, seL4_X86_Default_VMAttributes);
    *page = 0x123456789abcdef0ULL;
    seL4_CPtr shared = next_slot++;
    CHECK(seL4_Untyped_RetypeShared(source, ROOT, 0, 0, shared) == seL4_RevokeFirst);
    CHECK(!seL4_CNode_Revoke(ROOT, source, 64));
    CHECK(!seL4_Untyped_RetypeShared(source, ROOT, 0, 0, shared));
    CHECK(address(shared) == pa);
    seL4_CPtr copy = next_slot++;
    CHECK(!seL4_CNode_Copy(ROOT, copy, 64, ROOT, shared, 64, seL4_AllRights));
    map(copy, va, seL4_X86_Default_VMAttributes);
    CHECK(!seL4_CNode_Delete(ROOT, shared, 64));
    CHECK(*page == 0);
    if (bits == 21) identify(pa);
    *page = ~0ULL;
    CHECK(!seL4_CNode_Revoke(ROOT, source, 64));
    ordinary = retype(source, type, 0, 1);
    CHECK(address(ordinary) == pa);
    map(ordinary, va, seL4_X86_Default_VMAttributes);
    CHECK(*page == 0);
    *page = 42;
    CHECK(*page == 42);
}

void run(seL4_BootInfo *boot)
{
#ifdef CONFIG_LIB_SEL4_USE_THREAD_LOCALS
    /* The only TLS data is the libsel4 IPC pointer and optional error flag. */
    static uintptr_t tls[8] __attribute__((aligned(64)));
    tls[7] = (uintptr_t)&tls[7];
    seL4_SetTLSBase(tls[7]);
#endif
    bi = boot;
    seL4_SetIPCBuffer(bi->ipcBuffer);
    next_slot = bi->empty.start;
    seL4_CPtr ram = bi->untyped.start;
    while (ram < bi->untyped.end) {
        seL4_UntypedDesc u = bi->untypedList[ram - bi->untyped.start];
        if (!u.isDevice && u.sizeBits >= 24) break;
        ram++;
    }
    CHECK(ram < bi->untyped.end);
    seL4_CPtr pt = retype(ram, seL4_X86_PageTableObject, 0, 1);
    CHECK(!seL4_X86_PageTable_Map(pt, VSPACE, small_va, seL4_X86_Default_VMAttributes));
    check_module();
    exercise(ram, 12, small_va + 0x2000);
    exercise(ram, 21, large_va);
    say("SEV test: shared and private frame lifecycle passed\n");
    seL4_DebugHalt();
}
