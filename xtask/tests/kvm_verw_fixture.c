/*
 * TEST ONLY: make KVM advertise AMD VERW_CLEAR to the nested test kernel.
 * This models updated firmware for functional tests of entry/exit code.
 * It does NOT update microcode or validate TSA mitigation on the host.
 * xtask loads this library into QEMU only when FL4_TEST_VERW_FIXTURE=1.
 * FL4_TEST_AP_REJECT optionally injects incompatible capabilities on AP 1.
 * Never use this fixture with untrusted guests or sensitive workloads.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <linux/kvm.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>

int ioctl(int fd, unsigned long request, ...)
{
    static int (*next_ioctl)(int, unsigned long, ...);
    if (!next_ioctl) {
        next_ioctl = dlsym(RTLD_NEXT, "ioctl");
    }
    va_list ap;
    va_start(ap, request);
    unsigned long arg = va_arg(ap, unsigned long);
    va_end(ap);
    if (request == KVM_SET_CPUID2) {
        struct kvm_cpuid2 *cpuid = (void *)(uintptr_t)arg;
        int amd = 0;
        unsigned apic_id = ~0u;
        const char *reject = getenv("FL4_TEST_AP_REJECT");
        for (unsigned i = 0; i < cpuid->nent; ++i) {
            struct kvm_cpuid_entry2 *e = &cpuid->entries[i];
            if (e->function == 0) {
                amd = e->ebx == 0x68747541 && e->edx == 0x69746e65 && e->ecx == 0x444d4163;
            }
            if (e->function == 1) {
                apic_id = e->ebx >> 24;
            }
        }
        for (unsigned i = 0; amd && i < cpuid->nent; ++i) {
            struct kvm_cpuid_entry2 *e = &cpuid->entries[i];
            if (reject && apic_id == 1 && !strcmp(reject, "ibpb") && e->function == 0x80000008) {
                e->ebx &= ~(1u << 12);
            }
            if (e->function == 0x80000021 && e->index == 0) {
                e->eax |= 1u << 5;
                if (reject && !strcmp(reject, "smt")) {
                    /* Make the BSP permit SMT, but require AP 1 to park siblings. */
                    if (apic_id == 1) { e->eax &= ~(1u << 29); }
                    else { e->eax |= 1u << 29; }
                }
                if (reject && apic_id == 1 && !strcmp(reject, "lfence")) {
                    e->eax &= ~(1u << 2);
                }
                fprintf(stderr, "TEST FIXTURE: advertising VERW_CLEAR; TSA protection is NOT validated\n");
            }
        }
        if (amd && reject && apic_id == 1) {
            fprintf(stderr, "TEST FIXTURE: injecting AP 1 capability mismatch: %s\n", reject);
        }
    }
    return next_ioctl(fd, request, arg);
}
