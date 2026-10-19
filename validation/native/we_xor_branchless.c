/* Focused native Write-Execute diagnostic. Keep the comparison branchless in
   the hot loop: this checks whether the returned byte is wrong independently
   of the full arithmetic harness and its mismatch/retry path. Not a CI test;
   rare failures depend strongly on linked code placement. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "../../src/portable/writeexec_api.h"

static uint64_t state = UINT64_C(0x8d9d9278a41c6e31);
static uint32_t next32(void) {
    state ^= state << 13;
    state ^= state >> 7;
    state ^= state << 17;
    return (uint32_t)(state >> 16);
}

int main(int argc, char **argv) {
    uint64_t n = argc > 1 ? strtoull(argv[1], NULL, 0) : 20000000;
    we_make_code_writable();
    uint64_t bad = 0, got_sum = 0, want_sum = 0;
    for (uint64_t i = 0; i < n; i++) {
        uint32_t a = next32(), b = next32();
        uint8_t want = (uint8_t)(a ^ b);
        uint8_t got = WriteExecXOR_C((uint8_t)a, (uint8_t)b);
        bad += got != want;
        got_sum += got;
        want_sum += want;
    }
    printf("xor8 branchless n=%" PRIu64 " errors=%" PRIu64 " got_sum=%" PRIu64
           " want_sum=%" PRIu64 " cpu=%d\n", n, bad, got_sum, want_sum, we_cpu());
    return bad != 0;
}
