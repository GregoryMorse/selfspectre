#ifndef WE_CPU_FEATURES_H
#define WE_CPU_FEATURES_H

#ifndef _MSC_VER
#include <cpuid.h>
#endif

typedef struct {
    int rdtsc;
    int rdtscp;
    int clflush;
    int sse2;
    int aesni;
} we_cpu_features;

static void we_cpuid(unsigned int leaf, unsigned int subleaf, unsigned int out[4])
{
#ifdef _MSC_VER
    int info[4];
    __cpuidex(info, (int)leaf, (int)subleaf);
    out[0] = (unsigned int)info[0]; out[1] = (unsigned int)info[1];
    out[2] = (unsigned int)info[2]; out[3] = (unsigned int)info[3];
#else
    __cpuid_count(leaf, subleaf, out[0], out[1], out[2], out[3]);
#endif
}

static we_cpu_features we_detect_cpu_features(void)
{
    we_cpu_features f = {0};
    unsigned int v[4], max_basic, max_extended;
    we_cpuid(0, 0, v); max_basic = v[0];
    we_cpuid(0x80000000U, 0, v); max_extended = v[0];
    if (max_basic >= 1) {
        we_cpuid(1, 0, v);
        f.rdtsc = !!(v[3] & (1U << 4));
        f.clflush = !!(v[3] & (1U << 19));
        f.sse2 = !!(v[3] & (1U << 26));
        f.aesni = !!(v[2] & (1U << 25));
    }
    if (max_extended >= 0x80000001U) {
        we_cpuid(0x80000001U, 0, v);
        f.rdtscp = !!(v[3] & (1U << 27));
    }
    return f;
}

static int we_check_cpu_features(we_cpu_features f)
{
    printf("CPU features: RDTSC=%d RDTSCP=%d CLFLUSH=%d SSE2=%d AES-NI=%d.\n",
        f.rdtsc, f.rdtscp, f.clflush, f.sse2, f.aesni);
    if (!f.rdtsc) {
        fputs("This demo requires RDTSC for probe timing.\n", stderr);
        return 0;
    }
    if (!f.sse2) {
        fputs("This demo requires SSE2 for ordered cache timing.\n", stderr);
        return 0;
    }
#ifndef NOCLFLUSH
    if (!f.clflush) {
        fputs("This build requires CLFLUSH for probe eviction.\n", stderr);
        return 0;
    }
#endif
#ifndef NORDTSCP
    if (!f.rdtscp) {
        fputs("This build requires RDTSCP; rebuild with NORDTSCP for the RDTSC timer.\n", stderr);
        return 0;
    }
#endif
    return 1;
}

#endif
