/* Soak test of the plain-C reference arithmetic of writeexec.c (no self-modifying code is involved): the same random checks
   as the first block of the legacy harness, run for many iterations. On a mismatch the iteration is recomputed immediately, so that
   a transient result (wrong once, right on recomputation) can be told from a deterministic one. The functions below are copied
   verbatim from writeexec.c. Usage: ref_soak [iterations] [seed]. Evidence about the machine, not about the Lean development. */
#define _CRT_RAND_S
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
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
	int negative = ((x & 0x80000000) ^ (y & 0x80000000)) != 0;
	y = y < 0 ? -y : y;
	long long result = 0, tx = x < 0 ? -x : x;
	while (y != 0) {
		if ((y & 1) != 0) {
			result = result + tx;
		}
		tx = tx << 1;
		y = (unsigned int)y >> 1;
	}
	return negative ? -result : result;
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
	return ismod ? rem : *(unsigned int*)&quot;
}

unsigned int doDiv(unsigned int x, unsigned int y, int ismod)
{
	return ismod ? x % y : x / y;
}

int doSignDivision(long long x, int y, int ismod)
{
	unsigned long long quot, t;
	uint32_t rem;
	int bits_left;
	int negative = (ismod ? (x & 0x8000000000000000) : (((x & 0x8000000000000000) >> 32) ^ (y & 0x80000000))) != 0;
	if (x < 0) x = -x;
	if (y < 0) y = -y;
	quot = *(unsigned long long*)&x;
	rem = 0;
	for (bits_left = 64; bits_left > 0; bits_left--) {
		t = quot;
		quot <<= 1;
		rem = (rem << 1) + (quot < t);
		if (rem >= *(unsigned int*)&y) {
			rem -= *(unsigned int*)&y;
			quot++;
		}
	}
	return ismod ? (negative ? -*(int*)&rem : *(int*)&rem) : (negative ? -*(int*)&quot : *(int*)&quot);
}

int doSignDiv(int x, int y, int ismod)
{
	return ismod ? x % y : x / y;
}


static uint64_t rs = 88172645463325252ull;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)(rs >> 16); }

/* Returns a bit mask of the failed checks for one set of inputs. */
static int check(uint32_t num1, uint32_t num2, uint32_t num3, uint32_t num4) {
	int bad = 0; uint64_t r64; uint32_t r32;
	r64 = doMultiplication(num1, num2);
	if (r64 != num1 * (unsigned long long)num2) bad |= 1;
	if (doDivision(r64, num2, 0) != num1) bad |= 2;
	r64 = doSignMultiplication(num1, num2);
	if ((int64_t)r64 != (long long)(int32_t)num1 * (long long)(int32_t)num2) bad |= 4;
	if (doSignDivision(r64, num2, 0) != num1) bad |= 8;
	r32 = doDivision32(num1, num2, 0); if (r32 != num1 / num2) bad |= 16;
	r32 = doDivision32(num1, num2, 1); if (r32 != num1 % num2) bad |= 32;
	r32 = doDivision((uint64_t)num1 << 32 | num2, num3, 1); if (r32 != ((uint64_t)num1 << 32 | num2) % num3) bad |= 64;
	r32 = doSignDivision((uint64_t)num1 << 32 | num2, num3, 1);
	if (r32 != (int32_t)((long long)((int64_t)num1 << 32 | num2) % (int32_t)num3)) bad |= 128;
	if (isgte((uint64_t)num1 << 32 | num2, (uint64_t)num3 << 32 | num4) != (((uint64_t)num1 << 32 | num2) >= ((uint64_t)num3 << 32 | num4))) bad |= 256;
	return bad;
}

int main(int argc, char **argv) {
	long long n = argc > 1 ? atoll(argv[1]) : 100000000LL, bad_it = 0, transient = 0;
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
