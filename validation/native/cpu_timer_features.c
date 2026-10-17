/* Exit 0 for RDTSCP, 3 for an RDTSC+SSE2 fallback, 2 for no usable timer. */
#ifdef _MSC_VER
#include <intrin.h>
#else
#include <cpuid.h>
#endif

int main(void)
{
    int has_rdtsc, has_sse2, has_rdtscp = 0;
#ifdef _MSC_VER
    int f[4];
    __cpuid(f, 1);
    has_rdtsc = !!(f[3] & (1 << 4));
    has_sse2 = !!(f[3] & (1 << 26));
    __cpuid(f, 0x80000000);
    if ((unsigned int)f[0] >= 0x80000001U) {
        __cpuid(f, 0x80000001U);
        has_rdtscp = !!(f[3] & (1U << 27));
    }
#else
    unsigned int a, b, c, d;
    __cpuid(1, a, b, c, d);
    has_rdtsc = !!(d & (1U << 4));
    has_sse2 = !!(d & (1U << 26));
    if (__get_cpuid_max(0x80000000U, 0) >= 0x80000001U) {
        __cpuid(0x80000001U, a, b, c, d);
        has_rdtscp = !!(d & (1U << 27));
    }
#endif
    if (has_rdtscp) return 0;
    if (has_rdtsc && has_sse2) return 3;
    return 2;
}
