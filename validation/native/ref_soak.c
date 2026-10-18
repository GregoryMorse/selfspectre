/* Soak test of the plain-C reference arithmetic of writeexec.c (no self-modifying code is involved): the same random checks
   as the first block of the legacy harness, run for many iterations. On a mismatch the iteration is recomputed immediately, so that
   a transient result (wrong once, right on recomputation) can be told from a deterministic one. The functions below are copied
   verbatim from writeexec.c. Usage: ref_soak [iterations] [seed]. Evidence about the machine, not about the Lean development. */
#define _CRT_RAND_S
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "portable/we_portable.h"

unsigned long long doMultiplication(unsigned int x, unsigned int y)
{
	unsigned long long result = 0, tx = x;
	while (y != 0) {
		if ((y & 1) != 0) {
			result = result + tx;
		}
		tx = tx << 1;
		y = (unsigned int)y >> 1;
	}
	return result;
}

unsigned long long doMul(unsigned int x, unsigned int y)
{
	return x * y;
}

//no difference when 32 bit * 32 bit goes to 32 bit, only must deal with sign in 64 bit result
long long doSignMultiplication(int x, int y)
{
	int negative = (x < 0) != (y < 0);
	uint32_t a = x < 0 ? 0u - (uint32_t)x : (uint32_t)x;
	uint32_t b = y < 0 ? 0u - (uint32_t)y : (uint32_t)y;
	uint64_t result = 0, tx = a;
	while (b != 0) {
		if (b & 1) result += tx;
		tx <<= 1;
		b >>= 1;
	}
	return negative ? -(int64_t)result : (int64_t)result;
}

int doSignMul(int x, int y)
{
	return x * y;
}

unsigned int doDivision32(unsigned int x, unsigned int y, int ismod)
{
	unsigned int quot, rem, t;
	int bits_left;
	quot = x;
	rem = 0;
	for (bits_left = 32; bits_left > 0; bits_left--) {
		t = quot;
		quot <<= 1;
		rem = (rem << 1) + (quot < t);
		if (rem >= y) {
			rem -= y;
			quot++;
		}
	}
	return ismod ? rem : quot;
}

int isgte(unsigned long long a, unsigned long long b)
{
	//a & !b ^ !(a ^ b) & !c
	//!(a & !b ^ (a ^ b) | c)
	return ~(a & ~b ^ ((a ^ b) | (a-b))) >> 63;
}

unsigned int doDivision(unsigned long long x, unsigned int y, int ismod)
{
	unsigned long long quot, t;
	unsigned int rem;
	int bits_left;
	quot = x;
	rem = 0;
	for (bits_left = 64; bits_left > 0; bits_left--) {
		t = quot;
		quot <<= 1;
		int remof = (rem & 0x80000000) != 0;
		rem = (rem << 1) + (quot < t);
		if (remof || rem >= y) {
			rem -= y;
			quot++;
		}
	}
	return ismod ? rem : (uint32_t)quot;
}

unsigned int doDiv(unsigned int x, unsigned int y, int ismod)
{
	return ismod ? x % y : x / y;
}

int doSignDivision(long long x, int y, int ismod)
{
	uint64_t quot = x < 0 ? 0ull - (uint64_t)x : (uint64_t)x;
	uint32_t divisor = y < 0 ? 0u - (uint32_t)y : (uint32_t)y;
	uint64_t rem = 0;
	int negative = ismod ? (x < 0) : ((x < 0) != (y < 0));
	for (int bits_left = 64; bits_left > 0; bits_left--) {
		uint64_t high = quot >> 63;
		quot <<= 1;
		rem = (rem << 1) | high;
		if (rem >= divisor) {
			rem -= divisor;
			quot++;
		}
	}
	uint32_t bits = (uint32_t)(ismod ? rem : quot);
	if (negative) bits = 0u - bits;
	int32_t signed_result;
	memcpy(&signed_result, &bits, sizeof signed_result);
	return signed_result;
}

int doSignDiv(int x, int y, int ismod)
{
	return ismod ? x % y : x / y;
}

static int64_t signed_bits64(uint64_t bits) { int64_t value; memcpy(&value, &bits, sizeof value); return value; }
static int32_t signed_bits32(uint32_t bits) { int32_t value; memcpy(&value, &bits, sizeof value); return value; }


static uint64_t rs = 88172645463325252ull;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)(rs >> 16); }

/* Returns a bit mask of the failed checks for one set of inputs. */
static int check(uint32_t num1, uint32_t num2, uint32_t num3, uint32_t num4) {
	int bad = 0; uint64_t r64; uint32_t r32;
	r64 = doMultiplication(num1, num2);
	if (r64 != num1 * (unsigned long long)num2) bad |= 1;
	if (doDivision(r64, num2, 0) != num1) bad |= 2;
	r64 = doSignMultiplication(signed_bits32(num1), signed_bits32(num2));
	if (signed_bits64(r64) != (long long)signed_bits32(num1) * (long long)signed_bits32(num2)) bad |= 4;
	if (doSignDivision(signed_bits64(r64), signed_bits32(num2), 0) != num1) bad |= 8;
	r32 = doDivision32(num1, num2, 0); if (r32 != num1 / num2) bad |= 16;
	r32 = doDivision32(num1, num2, 1); if (r32 != num1 % num2) bad |= 32;
	r32 = doDivision((uint64_t)num1 << 32 | num2, num3, 1); if (r32 != ((uint64_t)num1 << 32 | num2) % num3) bad |= 64;
	int64_t signed_numerator = signed_bits64((uint64_t)num1 << 32 | num2);
	int32_t signed_divisor = signed_bits32(num3);
	int32_t expected_remainder = (signed_numerator == INT64_MIN && signed_divisor == -1)
		? 0 : (int32_t)(signed_numerator % signed_divisor);
	r32 = doSignDivision(signed_numerator, signed_divisor, 1);
	if (r32 != (uint32_t)expected_remainder) bad |= 128;
	if (isgte((uint64_t)num1 << 32 | num2, (uint64_t)num3 << 32 | num4) != (((uint64_t)num1 << 32 | num2) >= ((uint64_t)num3 << 32 | num4))) bad |= 256;
	return bad;
}

int main(int argc, char **argv) {
	long long n = argc > 1 ? atoll(argv[1]) : 100000000LL, bad_it = 0, transient = 0;
	static const uint32_t edge[] = { 0, 1, 2, 0x7fffffff, 0x80000000, 0xffffffff };
	for (size_t a = 0; a < sizeof edge / sizeof edge[0]; a++)
	for (size_t b = 1; b < sizeof edge / sizeof edge[0]; b++)
	for (size_t c = 1; c < sizeof edge / sizeof edge[0]; c++) {
		int failed = check(edge[a], edge[b], edge[c], edge[(a+b+c) % (sizeof edge / sizeof edge[0])]);
		if (failed) {
			printf("edge inputs %08x %08x %08x failed checks 0x%x\n", edge[a], edge[b], edge[c], failed);
			return 1;
		}
	}
	if (argc > 2) rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ull;
	for (long long it = 0; it < n; it++) {
		uint32_t num1 = rnd(), num2 = rnd() | 1, num3 = rnd() | 1, num4 = rnd(); /* divisors are nonzero */
		int bad = check(num1, num2, num3, num4);
		if (bad) {
			int c0 = we_cpu(), again1 = check(num1, num2, num3, num4), again2 = check(num1, num2, num3, num4);
			bad_it++; if (!again1 && !again2) transient++;
			printf("iteration %lld: failed checks 0x%x, recomputed 0x%x 0x%x (cpu %d then %d) inputs %08x %08x %08x %08x\n", it, bad, again1, again2, c0, we_cpu(), num1, num2, num3, num4);
		}
	}
	printf("%lld iterations, %lld with a mismatch (%lld right on recomputation)\n", n, bad_it, transient);
	return bad_it != 0;
}
