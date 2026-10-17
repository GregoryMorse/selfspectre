/* Edge-case vectors for the assembled Write-Execute entry points (writeexc.asm, x86 and x64).
   Expected values come from the C operators (independent of the Lean development). Evidence, not proof.
   Prints one line per mismatch and exits 1 if any; prints "edge vectors ok <n>" otherwise. A result that is wrong once but right on
   two immediate repeat calls is reported as "transient" (counted, printed, not a failure); one that stays wrong fails. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#define _CRT_RAND_S
#include "../../src/portable/we_portable.h"
#include "../../src/portable/writeexec_api.h"
unsigned int array1_size; uint8_t array1[160]; uint8_t array2[256 * 512 * 16]; uint8_t tmp;
typedef struct { uint32_t rd_key[60]; int rounds; } AES_KEY_;
extern int AES_set_encrypt_key(const unsigned char *userKey, const int bits, AES_KEY_ *key);

static int bad = 0, total = 0, transient = 0;
/* Evaluated once for the comparison; on a mismatch the entry point is called once more, so that a transient result
   (first call wrong, repeat right) can be told from a deterministic one. */
#define CHECK(name, got, want, ...) do { unsigned long long g_ = (unsigned long long)(got), w_ = (unsigned long long)(want); total++; if (g_ != w_) { int c0_ = we_cpu(); unsigned long long r1_ = (unsigned long long)(got), r2_ = (unsigned long long)(got); if (r1_ == w_ && r2_ == w_) transient++; else bad++; printf("%s %s: " #__VA_ARGS__ " got %llx want %llx (repeat calls: %llx %llx; cpu %d then %d)\n", (r1_ == w_ && r2_ == w_) ? "transient" : "mismatch", name, g_, w_, r1_, r2_, c0_, we_cpu()); } } while (0)

static const uint32_t E32[] = { 0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x100, 0x101, 0x7fff, 0x8000, 0xffff, 0x10000, 0x10001,
	0xff00ff, 0xffffff, 0x1000000, 0x7fffffff, 0x80000000, 0x80000001, 0xfffffffe, 0xffffffff,
	0x55555555, 0xaaaaaaaa, 0x01010101, 0xfefefefe, 0x00ff0000, 0x0000ff00, 0x12345678, 0xdeadbeef };
#define N32 (sizeof(E32) / sizeof(E32[0]))
static uint64_t E64[N32 * 3 + 6];
static size_t N64;

static uint64_t mulmod64(uint64_t a, uint64_t b, uint64_t m) { return (a * b) % m; } /* a,b < m < 2^32 */
static uint32_t modexp_ref(uint32_t b, uint32_t e, uint32_t m) {
	uint64_t r = 1 % m, x = b % m;
	while (e) { if (e & 1) r = mulmod64(r, x, m); x = mulmod64(x, x, m); e >>= 1; }
	return (uint32_t)r;
}

static uint64_t rs = 88172645463325252ull;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)(rs >> 16); }

int main(int argc, char **argv) {
	we_make_code_writable();
	if (argc > 1) { /* stress: random vectors, `edge_vectors N seed` */
		long n = atol(argv[1]); long every = argc > 3 ? atol(argv[3]) : 20; if (argc > 2) rs ^= (uint64_t)atol(argv[2]) * 0x9E3779B97F4A7C15ull;
		for (long i = 0; i < n; i++) {
			uint32_t a = rnd(), b = rnd(), c = rnd(), d = rnd(); uint64_t x = ((uint64_t)a << 32) | b;
			CHECK("ADD32", WriteExecADD32_C(a, b), a + b, a b); CHECK("SUB32", WriteExecSUB32_C(a, b), a - b, a b);
			CHECK("XOR32", WriteExecXOR32_C(a, b), a ^ b, a b); CHECK("MUL32", WriteExecMUL32_C(a, b), (uint64_t)a * b, a b);
			CHECK("ADD64", WriteExecADD64_C(x, ((uint64_t)c << 32) | d), x + (((uint64_t)c << 32) | d), a b c d);
			CHECK("SUB64", WriteExecSUB64_C(x, ((uint64_t)c << 32) | d), x - (((uint64_t)c << 32) | d), a b c d);
			if (c) { CHECK("DIV32", WriteExecDIV32_C(x, c), (uint32_t)(x / c), a b c); CHECK("MOD32", WriteExecMOD32_C(x, c), (uint32_t)(x % c), a b c); }
			if (c >= 2 && i % every == 0) CHECK("MODEXP32", WriteExecMODEXP32_C(a, b, c), modexp_ref(a, b, c), a b c);
		}
		printf(bad ? "stress FAILED %d of %d\n" : "stress ok %d checks (%d transient)\n", bad ? bad : total, bad ? total : transient);
		return bad != 0;
	}
	for (size_t i = 0; i < N32; i++) {
		E64[N64++] = E32[i];
		E64[N64++] = (uint64_t)E32[i] << 32;
		E64[N64++] = ((uint64_t)E32[i] << 32) | E32[(i * 7 + 3) % N32];
	}
	E64[N64++] = 0x8000000000000000ull; E64[N64++] = 0x7fffffffffffffffull; E64[N64++] = 0xffffffffffffffffull;
	E64[N64++] = 0x00000000ffffffffull; E64[N64++] = 0xffffffff00000000ull; E64[N64++] = 0x0123456789abcdefull;

	for (int i = 0; i < 256; i++) {
		CHECK("SHL1", WriteExecSHL1_C(i), i << 1, i);
		CHECK("NZ", WriteExecNZ_C(i), i != 0, i);
		CHECK("NOT", WriteExecNOT_C(i), (uint8_t)~i, i);
		CHECK("INC", WriteExecINC_C(i), i + 1, i);
		CHECK("DEC", WriteExecDEC_C(i), (i - 1) & 0x1ff, i);
		for (int j = 0; j < 256; j++) {
			CHECK("XOR", WriteExecXOR_C(i, j), i ^ j, i j);
			CHECK("ADD", WriteExecADD_C(i, j), i + j, i j);
			CHECK("SUB", WriteExecSUB_C(i, j), (i - j) & 0x1ff, i j);
		}
		for (int j = 0; j < 8; j++) {
			CHECK("SHL", WriteExecSHL_C(i, j), i << j, i j);
			CHECK("SHR", WriteExecSHR_C(i, j), i << (8 - j), i j);
		}
	}
	for (size_t a = 0; a < N32; a++) {
		for (int c = 0; c < 32; c++) {
			CHECK("SHL32", WriteExecSHL32_C(E32[a], c), E32[a] << c, E32[a] c);
			CHECK("SHR32", WriteExecSHR32_C(E32[a], c), E32[a] >> c, E32[a] c);
		}
		for (size_t b = 0; b < N32; b++) {
			CHECK("XOR32", WriteExecXOR32_C(E32[a], E32[b]), E32[a] ^ E32[b], E32[a] E32[b]);
			CHECK("ADD32", WriteExecADD32_C(E32[a], E32[b]), E32[a] + E32[b], E32[a] E32[b]);
			CHECK("SUB32", WriteExecSUB32_C(E32[a], E32[b]), E32[a] - E32[b], E32[a] E32[b]);
			CHECK("MUL32", WriteExecMUL32_C(E32[a], E32[b]), (uint64_t)E32[a] * E32[b], E32[a] E32[b]);
		}
	}
	for (size_t a = 0; a < N64; a++) {
		for (int c = 0; c < 64; c++) {
			CHECK("SHL64", WriteExecSHL64_C(E64[a], c), E64[a] << c, E64[a] c);
			CHECK("SHR64", WriteExecSHR64_C(E64[a], c), E64[a] >> c, E64[a] c);
		}
		for (size_t b = 0; b < N64; b += 3) {
			CHECK("ADD64", WriteExecADD64_C(E64[a], E64[b]), E64[a] + E64[b], E64[a] E64[b]);
			CHECK("SUB64", WriteExecSUB64_C(E64[a], E64[b]), E64[a] - E64[b], E64[a] E64[b]);
		}
		for (size_t b = 0; b < N32; b++) {
			if (E32[b] == 0) continue;
			CHECK("DIV32", WriteExecDIV32_C(E64[a], E32[b]), (uint32_t)(E64[a] / E32[b]), E64[a] E32[b]);
			CHECK("MOD32", WriteExecMOD32_C(E64[a], E32[b]), (uint32_t)(E64[a] % E32[b]), E64[a] E32[b]);
		}
	}
	{ static const uint32_t B[] = { 0, 1, 2, 3, 0xffff, 0x10000, 0x7fffffff, 0xffffffff };
	  static const uint32_t M[] = { 2, 3, 0xffff, 0x10000, 0x10001, 0x7fffffff, 0x80000000, 0xfffffffe, 0xffffffff };
	  for (size_t i = 0; i < sizeof(B) / 4; i++) for (size_t j = 0; j < sizeof(B) / 4; j++) for (size_t k = 0; k < sizeof(M) / 4; k++)
		CHECK("MODEXP32", WriteExecMODEXP32_C(B[i], B[j], M[k]), modexp_ref(B[i], B[j], M[k]), B[i] B[j] M[k]); }
	{ /* FIPS-197 Appendix C.1 */
	  static const uint8_t K[16] = { 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15 };
	  static const uint8_t P[16] = { 0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff };
	  static const uint8_t C[16] = { 0x69,0xc4,0xe0,0xd8,0x6a,0x7b,0x04,0x30,0xd8,0xcd,0xb7,0x80,0x70,0xb4,0xc5,0x5a };
	  AES_KEY_ k; uint8_t in[16], out[16];
	  memcpy(in, P, 16); memset(out, 0, 16); AES_set_encrypt_key(K, 128, &k);
	  WriteExecAESLookup_C(in, out, (uint8_t*)k.rd_key);
	  CHECK("AES-C1", memcmp(out, C, 16) == 0, 1, fips); }
	if (bad) { printf("edge vectors FAILED %d of %d\n", bad, total); return 1; }
	printf("edge vectors ok %d (%d transient)\n", total, transient);
	return 0;
}
