#ifndef WE_PROBE_PREFLIGHT_H
#define WE_PROBE_PREFLIGHT_H

#define WE_PREFLIGHT_PROBES_PER_GROUP 256
#define WE_PREFLIGHT_MAX_FALSE_HIT_PERCENT 5

/* Run after threshold calibration, before any victim calls. Every line is
   flushed, so a hit here is background classification, not victim activity. */
static int we_probe_preflight(uint8_t *probe, int groups, int threshold)
{
#ifndef NOCLFLUSH
    uint8_t order[WE_PREFLIGHT_PROBES_PER_GROUP];
    uint32_t state = (uint32_t)__rdtsc() | 1U;
    int group, i, hits = 0, total = groups * WE_PREFLIGHT_PROBES_PER_GROUP;
    for (group = 0; group < groups; ++group)
        for (i = 0; i < WE_PREFLIGHT_PROBES_PER_GROUP; ++i)
            _mm_clflush(probe + (group * WE_PREFLIGHT_PROBES_PER_GROUP + i) * WE_PROBE_STRIDE);
    _mm_mfence();
    for (group = 0; group < groups; ++group) {
        we_shuffle_probe_order(order, &state);
        for (i = 0; i < WE_PREFLIGHT_PROBES_PER_GROUP; ++i) {
            volatile uint8_t *line = probe +
                (group * WE_PREFLIGHT_PROBES_PER_GROUP + order[i]) * WE_PROBE_STRIDE;
            if (we_probe_cycles(line) <= (uint64_t)threshold) ++hits;
        }
    }
    printf("Probe preflight: %d/%d flushed lines classified as hits.\n", hits, total);
    if (hits * 100 > total * WE_PREFLIGHT_MAX_FALSE_HIT_PERCENT) {
        fputs("Probe preflight failed: background hits would swamp the decoder; try another logical CPU or inspect cache_timing.\n", stderr);
        return 0;
    }
    return 1;
#else
    (void)probe; (void)groups; (void)threshold;
    puts("Probe preflight unavailable without CLFLUSH.");
    return 1;
#endif
}

#endif
