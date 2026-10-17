#ifndef WE_CACHE_TIMING_H
#define WE_CACHE_TIMING_H

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "we_rdtsc_x86.h"

static void we_pin_cpu_from_env(void)
{
#ifdef _WIN32
    const char *setting = getenv("WE_CPU");
    if (setting && *setting && strcmp(setting, "any") == 0) return;
    if (setting && *setting) {
        char *end;
        unsigned long cpu = strtoul(setting, &end, 10);
        if (*end || cpu >= 8 * sizeof(DWORD_PTR) ||
            !SetThreadAffinityMask(GetCurrentThread(), (DWORD_PTR)1 << cpu)) {
            fprintf(stderr, "WE_CPU=%s could not select a logical CPU.\n", setting);
        } else {
            printf("Pinned to logical CPU %lu.\n", cpu);
        }
    } else {
        unsigned long cpu = GetCurrentProcessorNumber();
        if (cpu < 8 * sizeof(DWORD_PTR) &&
            SetThreadAffinityMask(GetCurrentThread(), (DWORD_PTR)1 << cpu))
            printf("Pinned to logical CPU %lu (automatic).\n", cpu);
        else
            fprintf(stderr, "Could not pin the current logical CPU.\n");
    }
#elif defined(__linux__)
    const char *setting = getenv("WE_CPU");
    int cpu = sched_getcpu();
    cpu_set_t mask;
    if (setting && strcmp(setting, "any") == 0) return;
    if (setting && *setting) {
        char *end;
        long selected = strtol(setting, &end, 10);
        if (*end || selected < 0 || selected >= CPU_SETSIZE) {
            fprintf(stderr, "Invalid WE_CPU=%s.\n", setting);
            exit(2);
        }
        cpu = (int)selected;
    }
    if (cpu < 0 || cpu >= CPU_SETSIZE) {
        fputs("Could not identify a logical CPU for pinning.\n", stderr);
        exit(2);
    }
    CPU_ZERO(&mask);
    CPU_SET(cpu, &mask);
    if (sched_setaffinity(0, sizeof mask, &mask) != 0) {
        perror("sched_setaffinity");
        exit(2);
    }
    printf("Pinned to logical CPU %d.\n", cpu);
#endif
}

typedef struct we_cache_calibration {
    int threshold;
    uint64_t hot_p90;
    uint64_t cold_p10;
} we_cache_calibration;

#define WE_CALIBRATION_UNAVAILABLE (-1)

#if !defined(NOCLFLUSH)
static int we_compare_cycles(const void *left, const void *right)
{
    uint64_t a = *(const uint64_t *)left, b = *(const uint64_t *)right;
    return (a > b) - (a < b);
}

static uint64_t we_probe_cycles(volatile uint8_t *address)
{
#ifndef NORDTSCP
    unsigned int auxiliary;
    uint64_t start = __rdtscp(&auxiliary);
    volatile uint8_t value = *address;
    uint64_t elapsed = __rdtscp(&auxiliary) - start;
    (void)value;
    return elapsed;
#else
#if defined(_MSC_VER) && defined(_M_IX86)
    return we_rdtsc_probe_x86(address);
#else
    uint64_t start, elapsed;
    volatile uint8_t value;
#ifndef NOMFENCE
    _mm_lfence();
#endif
    start = __rdtsc();
#ifndef NOMFENCE
    _mm_lfence();
#endif
    value = *address;
#ifndef NOMFENCE
    _mm_lfence();
#endif
    elapsed = __rdtsc() - start;
#ifndef NOMFENCE
    _mm_lfence();
#endif
    (void)value;
    return elapsed;
#endif
#endif
}

static we_cache_calibration we_calibrate_cache_threshold(volatile uint8_t *address)
{
    uint64_t hot[256], cold[256];
    we_cache_calibration result;
    int i;
    for (i = 0; i < 256; ++i) {
        (void)*address;
        hot[i] = we_probe_cycles(address);
        _mm_clflush((const void *)address);
        _mm_mfence();
        cold[i] = we_probe_cycles(address);
    }
    qsort(hot, 256, sizeof(hot[0]), we_compare_cycles);
    qsort(cold, 256, sizeof(cold[0]), we_compare_cycles);
    result.hot_p90 = hot[230];
    result.cold_p10 = cold[25];
    result.threshold = result.cold_p10 > result.hot_p90
        ? (int)((result.hot_p90 + result.cold_p10) / 2)
        : WE_CALIBRATION_UNAVAILABLE;
    return result;
}
#else
static we_cache_calibration we_calibrate_cache_threshold(volatile uint8_t *address)
{
    we_cache_calibration result = { WE_CALIBRATION_UNAVAILABLE, 0, 0 };
    (void)address;
    return result;
}
#endif

#endif
