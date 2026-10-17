#ifndef WE_CACHE_PROBE_H
#define WE_CACHE_PROBE_H

#include <stdint.h>

/* One candidate per page avoids the false hits seen with the old 512-byte stride. */
#define WE_PROBE_STRIDE 4096

/* Vary the probe order to avoid teaching a stride prefetcher the reload walk. */
static void we_shuffle_probe_order(uint8_t order[256], uint32_t *state)
{
    int i;
    for (i = 0; i < 256; ++i) order[i] = (uint8_t)i;
    for (i = 255; i > 0; --i) {
        int j;
        uint8_t tmp;
        *state ^= *state << 13;
        *state ^= *state >> 17;
        *state ^= *state << 5;
        j = (int)(*state % (uint32_t)(i + 1));
        tmp = order[i]; order[i] = order[j]; order[j] = tmp;
    }
}

#endif
