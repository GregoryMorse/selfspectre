/* Edge-case vectors for the assembled Write-Execute entry points (writeexc.asm, x86 and x64).
   Expected values come from the C operators (independent of the Lean development). Evidence, not proof.
   Prints one line per mismatch and exits 1 if any; prints "edge vectors ok <n>" otherwise. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
unsigned int array1_size; uint8_t array1[160]; uint8_t array2[256 * 512 * 16]; uint8_t tmp;
extern uint16_t WriteExecSHL1_C(uint8_t);
extern uint16_t WriteExecSHL_C(uint8_t, uint8_t);
extern uint32_t WriteExecSHL32_C(uint32_t, uint8_t);
extern uint64_t WriteExecSHL64_C(uint64_t, uint8_t);
extern uint16_t WriteExecSHR_C(uint8_t, uint8_t);
extern uint32_t WriteExecSHR32_C(uint32_t, uint8_t);
extern uint64_t WriteExecSHR64_C(uint64_t, uint8_t);
extern uint8_t WriteExecNZ_C(uint8_t);
extern uint8_t WriteExecNOT_C(uint8_t);
extern uint16_t WriteExecINC_C(uint8_t);
extern uint16_t WriteExecDEC_C(uint8_t);
extern uint8_t WriteExecXOR_C(uint8_t, uint8_t);
extern uint32_t WriteExecXOR32_C(uint32_t, uint32_t);
extern uint16_t WriteExecADD_C(uint8_t, uint8_t);
extern uint32_t WriteExecADD32_C(uint32_t, uint32_t);
extern uint64_t WriteExecADD64_C(uint64_t, uint64_t);
extern uint16_t WriteExecSUB_C(uint8_t, uint8_t);
extern uint32_t WriteExecSUB32_C(uint32_t, uint32_t);
extern uint64_t WriteExecSUB64_C(uint64_t, uint64_t);
extern uint64_t WriteExecMUL32_C(uint32_t, uint32_t);
extern uint32_t WriteExecDIV32_C(uint64_t, uint32_t);
extern uint32_t WriteExecMOD32_C(uint64_t, uint32_t);
extern uint32_t WriteExecMODEXP32_C(uint32_t, uint32_t, uint32_t);
extern void WriteExecAESLookup_C(uint8_t*, uint8_t*, uint8_t*);
typedef struct { unsigned long rd_key[60]; int rounds; } AES_KEY_;
extern int AES_set_encrypt_key(const unsigned char *userKey, const int bits, AES_KEY_ *key);

static int bad = 0, total = 0;
#define CHECK(name, got, want, ...) do { total++; if ((got) != (want)) { bad++; printf("%s mismatch: " #__VA_ARGS__ " got %llx want %llx\n", name, (unsigned long long)(got), (unsigned long long)(want)); } } while (0)

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

int main(void) {
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
	printf("edge vectors ok %d\n", total);
	return 0;
}
