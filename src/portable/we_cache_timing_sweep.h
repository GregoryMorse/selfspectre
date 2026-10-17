#ifndef WE_CACHE_TIMING_SWEEP_H
#define WE_CACHE_TIMING_SWEEP_H

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "we_rdtsc_x86.h"

#define WE_CALIBRATION_SAMPLES 256
#define WE_CALIBRATION_MAX_GROUPS 16
#define WE_PROBES_PER_GROUP 256
#define WE_SWEEP_COLD_PERCENTILE 1

typedef struct {
    int threshold;
    int valid;
    uint64_t hot_p90;
    uint64_t cold_p10;
    uint64_t sweep_cold_p01;
} we_cache_calibration;

/* Keep calibration and the reload loop on the same logical CPU by default. */
static void we_pin_cpu_from_env(void)
{
#ifdef _WIN32
    const char *choice = getenv("WE_CPU");
    DWORD cpu = GetCurrentProcessorNumber();
    DWORD_PTR mask;
    char *end;
    if (choice && strcmp(choice, "any") == 0) {
        puts("CPU pinning disabled (WE_CPU=any).");
        return;
    }
    if (choice && *choice) {
        unsigned long selected = strtoul(choice, &end, 10);
        if (*end || selected >= sizeof(DWORD_PTR) * 8) {
            fprintf(stderr, "Invalid WE_CPU=%s; use a logical CPU index or 'any'.\n", choice);
            exit(2);
        }
        cpu = (DWORD)selected;
    }
    mask = (DWORD_PTR)1 << cpu;
    if (!SetThreadAffinityMask(GetCurrentThread(), mask)) {
        fprintf(stderr, "Cannot pin to logical CPU %lu (error %lu).\n",
            (unsigned long)cpu, (unsigned long)GetLastError());
        exit(2);
    }
    printf("Pinned to logical CPU %lu.\n", (unsigned long)cpu);
#elif defined(__linux__)
    const char *choice = getenv("WE_CPU");
    int cpu = sched_getcpu();
    cpu_set_t mask;
    char *end;
    if (choice && strcmp(choice, "any") == 0) {
        puts("CPU pinning disabled (WE_CPU=any).");
        return;
    }
    if (choice && *choice) {
        long selected = strtol(choice, &end, 10);
        if (*end || selected < 0 || selected >= CPU_SETSIZE) {
            fprintf(stderr, "Invalid WE_CPU=%s.\n", choice);
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
#else
    const char *choice = getenv("WE_CPU");
    if (choice && *choice) {
        fprintf(stderr, "WE_CPU pinning is supported by the demos on Windows and Linux.\n");
        exit(2);
    }
#endif
}

static int we_timer_rdtscp;
static int we_timer_fence;

static void we_configure_probe_timer(we_cpu_features features)
{
#ifndef NORDTSCP
    we_timer_rdtscp = features.rdtscp;
#endif
#ifndef NOMFENCE
    we_timer_fence = features.sse2;
#endif
    printf("Probe timer: %s.\n", we_timer_rdtscp ? "RDTSCP" :
        (we_timer_fence ? "RDTSC with LFENCE" : "RDTSC"));
}

static int we_compare_cycles(const void *a, const void *b)
{
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return (x > y) - (x < y);
}

#ifdef _MSC_VER
#define WE_TIMING_INLINE static __forceinline
#else
#define WE_TIMING_INLINE static inline __attribute__((always_inline))
#endif

WE_TIMING_INLINE uint64_t we_probe_cycles(volatile uint8_t *address, unsigned int *junk)
{
    uint64_t start, end;
    if (we_timer_rdtscp) {
        start = __rdtscp(junk);
        *junk = *address;
        end = __rdtscp(junk);
    } else {
#if defined(_MSC_VER) && defined(_M_IX86) && defined(NORDTSCP)
        *junk = 0;
        return we_rdtsc_probe_x86(address);
#else
        if (we_timer_fence) _mm_lfence();
        start = __rdtsc();
        if (we_timer_fence) _mm_lfence();
        *junk = *address;
        if (we_timer_fence) _mm_lfence();
        end = __rdtsc();
        if (we_timer_fence) _mm_lfence();
#endif
    }
    return end - start;
}

#ifndef NOCLFLUSH
/* A lone flushed line can look cold while a full reload walk produces
   prefetch/cache false hits. Measure both conditions before choosing a cut. */
static we_cache_calibration we_calibrate_cache_threshold(uint8_t *probe, int groups)
{
    we_cache_calibration out = {0};
    uint64_t hot[WE_CALIBRATION_SAMPLES], cold[WE_CALIBRATION_SAMPLES];
    uint64_t sweep[WE_CALIBRATION_MAX_GROUPS * WE_PROBES_PER_GROUP];
    uint8_t order[WE_PROBES_PER_GROUP];
    unsigned int junk = 0;
    uint32_t state = (uint32_t)__rdtsc() | 1U;
    int i, group, count = groups * WE_PROBES_PER_GROUP;
    if (groups < 1 || groups > WE_CALIBRATION_MAX_GROUPS) return out;
    for (i = 0; i < WE_CALIBRATION_SAMPLES; ++i) {
        volatile uint8_t *line = probe + (i % WE_PROBES_PER_GROUP) * WE_PROBE_STRIDE;
        (void)*line;
        hot[i] = we_probe_cycles(line, &junk);
        _mm_clflush((void *)line);
        _mm_mfence();
        cold[i] = we_probe_cycles(line, &junk);
    }
    qsort(hot, WE_CALIBRATION_SAMPLES, sizeof hot[0], we_compare_cycles);
    qsort(cold, WE_CALIBRATION_SAMPLES, sizeof cold[0], we_compare_cycles);
    out.hot_p90 = hot[WE_CALIBRATION_SAMPLES * 9 / 10];
    out.cold_p10 = cold[WE_CALIBRATION_SAMPLES / 10];

    for (group = 0; group < groups; ++group)
        for (i = 0; i < WE_PROBES_PER_GROUP; ++i)
            _mm_clflush(probe + (group * WE_PROBES_PER_GROUP + i) * WE_PROBE_STRIDE);
    _mm_mfence();
    for (group = 0; group < groups; ++group) {
        we_shuffle_probe_order(order, &state);
        for (i = 0; i < WE_PROBES_PER_GROUP; ++i)
            sweep[group * WE_PROBES_PER_GROUP + i] = we_probe_cycles(
                probe + (group * WE_PROBES_PER_GROUP + order[i]) * WE_PROBE_STRIDE, &junk);
    }
    qsort(sweep, count, sizeof sweep[0], we_compare_cycles);
    out.sweep_cold_p01 = sweep[count * WE_SWEEP_COLD_PERCENTILE / 100];
    if (out.hot_p90 >= out.cold_p10 || out.hot_p90 >= out.sweep_cold_p01)
        return out;
    /* The decoder actually reads a full array, so use that cold distribution
       for the cut. The isolated-line check remains a guard on timer validity. */
    out.threshold = (int)(out.hot_p90 + (out.sweep_cold_p01 - out.hot_p90) / 2);
    if ((uint64_t)out.threshold >= out.cold_p10)
        out.threshold = (int)(out.cold_p10 - 1);
    out.valid = 1;
    return out;
}
#else
static we_cache_calibration we_calibrate_cache_threshold(uint8_t *probe, int groups)
{
    we_cache_calibration out = {0};
    (void)probe; (void)groups;
    return out;
}
#endif

#endif
