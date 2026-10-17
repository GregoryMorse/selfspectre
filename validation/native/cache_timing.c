/* Measure the hot/cold classification used by the native demos. */
#include <intrin.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define SAMPLES 4096
#define MAX_PROBE_STRIDE 4096

__declspec(align(64)) static uint8_t line[64];
static uint8_t probe[16 * 256 * MAX_PROBE_STRIDE];
static volatile unsigned int sink;

static int compare_u64(const void *a, const void *b)
{
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return (x > y) - (x < y);
}

static uint64_t measure(volatile uint8_t *addr, int fenced)
{
    unsigned int aux;
    uint64_t start, end;
    start = __rdtscp(&aux);
    if (fenced) _mm_lfence();
    sink ^= *addr;
    end = __rdtscp(&aux);
    return end - start;
}

static void report(const char *name, uint64_t *samples)
{
    unsigned int below80 = 0;
    int i;
    qsort(samples, SAMPLES, sizeof(samples[0]), compare_u64);
    for (i = 0; i < SAMPLES; ++i) if (samples[i] <= 80) ++below80;
    printf("%-13s p10=%llu p50=%llu p90=%llu <=80=%u/%d\n", name,
        (unsigned long long)samples[SAMPLES / 10],
        (unsigned long long)samples[SAMPLES / 2],
        (unsigned long long)samples[SAMPLES * 9 / 10], below80, SAMPLES);
}

static void sweep(int stride, int fenced, int shuffled)
{
    uint64_t times[SAMPLES];
    unsigned short order[SAMPLES];
    unsigned int state = 0x9e3779b9U;
    char label[32];
    int i;
    for (i = 0; i < SAMPLES; ++i) {
        probe[i * stride] = 1;
        order[i] = (unsigned short)i;
    }
    if (shuffled) {
        for (i = SAMPLES - 1; i > 0; --i) {
            int j;
            unsigned short swap;
            state ^= state << 13;
            state ^= state >> 17;
            state ^= state << 5;
            j = state % (unsigned int)(i + 1);
            swap = order[i]; order[i] = order[j]; order[j] = swap;
        }
    }
    for (i = 0; i < SAMPLES; ++i) _mm_clflush(&probe[i * stride]);
    _mm_mfence();
    for (i = 0; i < SAMPLES; ++i) {
        int index = shuffled ? order[i]
            : (i / 256) * 256 + (((i % 256) * 167 + 13) & 255);
        times[i] = measure(&probe[index * stride], fenced);
    }
    sprintf_s(label, sizeof(label), "%d %s%s", stride,
        shuffled ? "shuffle" : "mixed", fenced ? " fenced" : "");
    report(label, times);
}

int main(void)
{
    uint64_t hot[2][SAMPLES], cold[2][SAMPLES];
    int fenced, i;
    line[0] = 1;
    for (fenced = 0; fenced <= 1; ++fenced) {
        for (i = 0; i < SAMPLES; ++i) {
            sink ^= line[0];
            hot[fenced][i] = measure(line, fenced);
            _mm_clflush(line);
            _mm_mfence();
            cold[fenced][i] = measure(line, fenced);
        }
    }
    report("hot original", hot[0]);
    report("cold original", cold[0]);
    report("hot fenced", hot[1]);
    report("cold fenced", cold[1]);
    sweep(512, 0, 0);
    sweep(512, 1, 0);
    sweep(512, 1, 1);
    sweep(4096, 0, 0);
    sweep(4096, 1, 0);
    sweep(4096, 1, 1);
    return 0;
}
