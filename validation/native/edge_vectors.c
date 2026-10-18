/* Edge-case vectors for the assembled Write-Execute entry points (writeexc.asm, x86 and x64).
   Expected values come from the C operators (independent of the Lean development). Evidence, not proof.
   Prints one line per mismatch and exits 1 if any; prints "edge vectors ok <n>" otherwise. A result that is wrong once but right on
   two immediate repeat calls is classified as "transient", but still fails the run. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#define _CRT_RAND_S
#define WE_PREPRIVATE_DIAGNOSTIC 1
#include "../../src/portable/we_portable.h"
#include "../../src/portable/we_cache_probe.h"
#include "../../src/portable/writeexec_api.h"
unsigned int array1_size; uint8_t array1[160]; uint8_t array2[256 * WE_PROBE_STRIDE * 16]; uint8_t tmp;
typedef struct { uint32_t rd_key[60]; int rounds; } AES_KEY_;
extern int AES_set_encrypt_key(const unsigned char *userKey, const int bits, AES_KEY_ *key);
#if defined(_WIN32)
/* The first SHR32 instruction contains the count immediate at byte 6. Read it
   only after a mismatch, outside the Write-Execute computation. */
extern void WriteExecSHR32(void);
extern void shlarg1(void);
extern void shlarg6(void);
extern void shrarg2(void);
#endif

static int bad = 0, total = 0, transient = 0;
/* Evaluated once for the comparison; on a mismatch the entry point is called once more, so that a transient result
   (first call wrong, repeat right) can be told from a deterministic one. */
#define CHECK(name, got, want, ...) do { unsigned long long g_ = (unsigned long long)(got), w_ = (unsigned long long)(want); total++; if (g_ != w_) { int c0_ = we_cpu(); unsigned long long r1_ = (unsigned long long)(got), r2_ = (unsigned long long)(got); bad++; if (r1_ == w_ && r2_ == w_) transient++; printf("%s %s: " #__VA_ARGS__ " got %llx want %llx (repeat calls: %llx %llx; cpu %d then %d)\n", (r1_ == w_ && r2_ == w_) ? "transient" : "mismatch", name, g_, w_, r1_, r2_, c0_, we_cpu()); } } while (0)

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

static void check_modexp(uint32_t b, uint32_t e, uint32_t m) {
	uint32_t want = modexp_ref(b, e, m), got = WriteExecMODEXP32_C(b, e, m);
	total++;
	if (got != want) {
		int cpu = we_cpu();
		uint32_t r1 = WriteExecMODEXP32_C(b, e, m), r2 = WriteExecMODEXP32_C(b, e, m);
		bad++;
		if (r1 == want && r2 == want) transient++;
		printf("%s MODEXP32 inputs %08x %08x %08x got %08x want %08x (repeat calls: %08x %08x; cpu %d then %d)\n",
			(r1 == want && r2 == want) ? "transient" : "mismatch", b, e, m, got, want, r1, r2, cpu, we_cpu());
	}
}

static uint64_t rs = 88172645463325252ull;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)(rs >> 16); }

int main(int argc, char **argv) {
	we_make_code_writable();
	if (argc > 1 && strcmp(argv[1], "mul32") == 0) {
		long n = argc > 2 ? atol(argv[2]) : 20000;
		uint32_t seed;
		if (argc > 3) seed = (uint32_t)strtoull(argv[3], 0, 0);
		else if (rand_s(&seed)) { fputs("random seed unavailable\n", stderr); return 2; }
		rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ull;
		printf("MUL32 seed %08x, %ld calls\n", seed, n); fflush(stdout);
		for (long i = 0; i < n; i++) {
			uint32_t a = rnd(), b = rnd();
			uint64_t want = (uint64_t)a * b;
			uint64_t got = WriteExecMUL32_C(a, b);
			if (got != want) {
				int cpu = we_cpu(), patched_shift = -1;
#if defined(_WIN32)
				patched_shift = ((volatile const uint8_t *)(uintptr_t)&WriteExecSHR32)[6];
#endif
				uint64_t r1 = WriteExecMUL32_C(a, b);
				uint64_t r2 = WriteExecMUL32_C(a, b);
				printf("MUL32 mismatch iteration %ld inputs %08x %08x got %016llx want %016llx patched SHR32 %d repeats %016llx %016llx cpu %d then %d\n",
					i, a, b, (unsigned long long)got, (unsigned long long)want, patched_shift,
					(unsigned long long)r1, (unsigned long long)r2, cpu, we_cpu());
				return 1;
			}
		}
		printf("MUL32 stress ok %ld\n", n);
		return 0;
	}
	if (argc > 1 && strcmp(argv[1], "shr32") == 0) {
		long n = argc > 2 ? atol(argv[2]) : 32000;
		uint32_t seed;
		if (argc > 3) seed = (uint32_t)strtoull(argv[3], 0, 0);
		else if (rand_s(&seed)) { fputs("random seed unavailable\n", stderr); return 2; }
		rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ull;
		printf("SHR32 seed %08x, %ld calls\n", seed, n); fflush(stdout);
		uint32_t input = 0;
		for (long i = 0; i < n; i++) {
			unsigned shift = (unsigned)i % 32;
			if (!shift) input = rnd();
			uint32_t want = input >> shift;
			uint32_t got = WriteExecSHR32_C(input, (uint8_t)shift);
			if (got != want) {
				int cpu = we_cpu(), patched = -1, split_input = -1, lane_shift = -1, lane_index = -1;
#if defined(_WIN32)
				patched = ((volatile const uint8_t *)(uintptr_t)&WriteExecSHR32)[6];
				split_input = ((volatile const uint8_t *)(uintptr_t)&shlarg1)[6];
				lane_shift = ((volatile const uint8_t *)(uintptr_t)&shrarg2)[6];
				lane_index = ((volatile const uint8_t *)(uintptr_t)&shlarg6)[2];
#endif
				uint32_t r1 = WriteExecSHR32_C(input, (uint8_t)shift);
				uint32_t r2 = WriteExecSHR32_C(input, (uint8_t)shift);
				printf("SHR32 mismatch iteration %ld input %08x shift %u got %08x want %08x prior %08x patched %d split %d lane %d index %d repeats %08x %08x cpu %d then %d\n",
					i, input, shift, got, want, shift ? input >> (shift - 1) : 0, patched, split_input, lane_shift, lane_index, r1, r2, cpu, we_cpu());
				return 1;
			}
		}
		printf("SHR32 stress ok %ld\n", n);
		return 0;
	}
	if (argc > 1 && strcmp(argv[1], "modexp") == 0) {
		/* Focused random differential run. Stop on the first bad call so the exact
		   operands and whether two immediate repeats agree are preserved. */
		long n = argc > 2 ? atol(argv[2]) : 10000;
		uint32_t seed;
		if (argc > 3) seed = (uint32_t)strtoull(argv[3], 0, 0);
		else if (rand_s(&seed)) { fputs("random seed unavailable\n", stderr); return 2; }
		rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ull;
		printf("MODEXP32 seed %08x, %ld calls\n", seed, n); fflush(stdout);
		for (long i = 0; i < n; i++) {
			/* Preserve the seed-to-sequence mapping for hosted failure replay. */
			uint32_t b = i ? rnd() : 0x2997D078u;
			uint32_t e = i ? rnd() : 0x4C815A47u;
			uint32_t m = i ? rnd() : 0x2A94AE94u;
			if (m < 2) m = 2;
			/* Exercise the same shared MUL32/DIV32 patch sites through their C
			   wrappers before MODEXP32, as the legacy harness does. */
			uint64_t product = (uint64_t)b * m;
			uint32_t expected_mod = b % m;
			uint64_t prior_mul = WriteExecMUL32_C(b, m);
			uint32_t prior_mod = WriteExecMOD32_C(product + expected_mod, m);
			if (prior_mul != product || prior_mod != expected_mod) {
				printf("MODEXP32 prelude mismatch iteration %ld inputs %08x %08x %08x mul %llx want %llx mod %08x want %08x\n",
					i, b, e, m, (unsigned long long)prior_mul, (unsigned long long)product, prior_mod, expected_mod);
				return 1;
			}
			uint32_t want = modexp_ref(b, e, m);
			uint32_t got = WriteExecMODEXP32_C(b, e, m);
			if (got != want) {
				int cpu = we_cpu();
				uint32_t r1 = WriteExecMODEXP32_C(b, e, m);
				uint32_t r2 = WriteExecMODEXP32_C(b, e, m);
				printf("MODEXP32 mismatch iteration %ld inputs %08x %08x %08x got %08x want %08x repeats %08x %08x cpu %d then %d\n",
					i, b, e, m, got, want, r1, r2, cpu, we_cpu());
				return 1;
			}
		}
		printf("MODEXP32 stress ok %ld\n", n);
		return 0;
	}
	if (argc > 1) { /* stress: random vectors, `edge_vectors N seed` */
		long n = atol(argv[1]); long every = argc > 3 ? atol(argv[3]) : 20; if (argc > 2) rs ^= (uint64_t)atol(argv[2]) * 0x9E3779B97F4A7C15ull;
		for (long i = 0; i < n; i++) {
			uint32_t a = rnd(), b = rnd(), c = rnd(), d = rnd(); uint64_t x = ((uint64_t)a << 32) | b;
			CHECK("ADD32", WriteExecADD32_C(a, b), a + b, a b); CHECK("SUB32", WriteExecSUB32_C(a, b), a - b, a b);
			CHECK("XOR32", WriteExecXOR32_C(a, b), a ^ b, a b); CHECK("MUL32", WriteExecMUL32_C(a, b), (uint64_t)a * b, a b);
			CHECK("ADD64", WriteExecADD64_C(x, ((uint64_t)c << 32) | d), x + (((uint64_t)c << 32) | d), a b c d);
			CHECK("SUB64", WriteExecSUB64_C(x, ((uint64_t)c << 32) | d), x - (((uint64_t)c << 32) | d), a b c d);
			if (c) { CHECK("DIV32", WriteExecDIV32_C(x, c), (uint32_t)(x / c), a b c); CHECK("MOD32", WriteExecMOD32_C(x, c), (uint32_t)(x % c), a b c); }
			if (c >= 2 && i % every == 0) check_modexp(a, b, c);
		}
		printf(bad ? "stress FAILED %d of %d (%d transient)\n" : "stress ok %d checks (%d transient)\n", bad ? bad : total, transient);
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
		check_modexp(B[i], B[j], M[k]); }
	/* Recheck exact operands from four CI transients in every ordinary edge run. */
	check_modexp(0x2997D078u, 0x4C815A47u, 0x2A94AE94u);
	check_modexp(0xA9EEB105u, 0xC209D12Du, 0xEB5D2736u);
	check_modexp(0x42A8399Eu, 0xFF9BD8CDu, 0x218628ACu);
	check_modexp(0x0FF37687u, 0x7785A53Au, 0x751DAE10u);
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
