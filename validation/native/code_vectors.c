/* Checks the corrected C reference functions of spectreopt.c (errata L02, L03) against exact vectors.
   Build: see validation/native.py --vectors. Prints nothing and exits 0 on success. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "../../src/portable/we_cache_probe.h"
unsigned int array1_size; uint8_t array1[160]; uint8_t array2[256 * WE_PROBE_STRIDE * 16]; uint8_t tmp;
#define main spectreopt_main_unused
#include "../../src/spectreopt.c"
#undef main
#include "vectors.h"
int main(void) {
	int bad = 0;
	for (size_t i = 0; i < sizeof(MULMOD) / sizeof(MULMOD[0]); i++)
		if (mulmod(MULMOD[i].a, MULMOD[i].b, MULMOD[i].m) != MULMOD[i].r) { bad++; printf("mulmod %u %u %u\n", MULMOD[i].a, MULMOD[i].b, MULMOD[i].m); }
	for (size_t i = 0; i < sizeof(MODEXP) / sizeof(MODEXP[0]); i++) {
		if (fastmodexp(MODEXP[i].a, MODEXP[i].b, MODEXP[i].m) != MODEXP[i].r) { bad++; printf("fastmodexp %u %u %u\n", MODEXP[i].a, MODEXP[i].b, MODEXP[i].m); }
		if (MODEXP[i].b < 100000 && modexp(MODEXP[i].a, MODEXP[i].b, MODEXP[i].m) != MODEXP[i].r) { bad++; printf("modexp %u %u %u\n", MODEXP[i].a, MODEXP[i].b, MODEXP[i].m); }
	}
	return bad ? 1 : 0;
}
