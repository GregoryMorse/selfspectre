/* Portability layer for the native Write-Execute harnesses (Windows MSVC, Linux, macOS; x86 and x64). */
#ifndef WE_PORTABLE_H
#define WE_PORTABLE_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#if defined(__x86_64__) && !defined(_WIN32)
#define WE_ABI __attribute__((ms_abi))
#else
#define WE_ABI
#endif

#define WE_SYM(n)

/* Diagnostic for the intermittent single-result mismatches seen on Windows runners: with the environment variable
   WE_PIN=1 the thread stays on the CPU it started on (rules thread migration in or out of the picture). */
#if defined(_WIN32)
#include <windows.h>
static void we_pin_if_requested(void) {
	const char *p = getenv("WE_PIN");
	if (p && *p == '1') SetThreadAffinityMask(GetCurrentThread(), (DWORD_PTR)1 << GetCurrentProcessorNumber());
}
#elif defined(__linux__)
#include <sched.h>
static void we_pin_if_requested(void) {
	const char *p = getenv("WE_PIN");
	if (p && *p == '1') { cpu_set_t m; CPU_ZERO(&m); CPU_SET(sched_getcpu(), &m); sched_setaffinity(0, sizeof m, &m); }
}
#else
static void we_pin_if_requested(void) {}
#endif

#if defined(__linux__)
#include <sys/mman.h>
#include <unistd.h>
extern char __executable_start, etext;
/* The Write-Execute procedures modify their own code: make the program text writable (Linux; Windows uses
   /SECTION:.text,ERW and macOS -segprot __TEXT,rwx,rwx at link time). */
static void we_make_code_writable(void) {
	uintptr_t pg = (uintptr_t)sysconf(_SC_PAGESIZE);
	uintptr_t a = (uintptr_t)&__executable_start & ~(pg - 1), b = ((uintptr_t)&etext + pg - 1) & ~(pg - 1);
	if (mprotect((void *)a, b - a, PROT_READ | PROT_WRITE | PROT_EXEC)) { perror("mprotect"); exit(2); }
	we_pin_if_requested();
}
#else
#define we_make_code_writable() we_pin_if_requested()
#endif

/* Logical processor the calling thread is on (-1 if unknown); printed with a mismatch to show thread migration. */
#if defined(_WIN32)
#define we_cpu() ((int)GetCurrentProcessorNumber())
#elif defined(__linux__)
#define we_cpu() sched_getcpu()
#else
#define we_cpu() (-1)
#endif

#if defined(_MSC_VER)
#include <windows.h>
/* rand_s needs _CRT_RAND_S defined before <stdlib.h>; the sources define it first. */
static double we_now(void) {
	LARGE_INTEGER f, c;
	QueryPerformanceFrequency(&f); QueryPerformanceCounter(&c);
	return (double)c.QuadPart / (double)f.QuadPart;
}
#else
#include <time.h>
#if defined(__APPLE__)
/* arc4random_buf is in <stdlib.h> */
#else
#include <sys/random.h>
#endif
/* Windows timer API used by the Spectre programs. */
typedef union { struct { uint32_t LowPart; int32_t HighPart; } u; int64_t QuadPart; } LARGE_INTEGER;
static int QueryPerformanceCounter(LARGE_INTEGER *c) {
	struct timespec t;
	clock_gettime(CLOCK_MONOTONIC, &t);
	c->QuadPart = (int64_t)t.tv_sec * 1000000000LL + t.tv_nsec;
	return 1;
}
static int QueryPerformanceFrequency(LARGE_INTEGER *f) { f->QuadPart = 1000000000LL; return 1; }
/* `__cdecl` marks the assembled SpecRSA procedures: ms_abi on x86-64 Unix, plain cdecl on x86. */
#ifndef __cdecl
#define __cdecl WE_ABI
#endif
static double we_now(void) {
	struct timespec t;
	clock_gettime(CLOCK_MONOTONIC, &t);
	return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}
/* rand_s replacement: xorshift64* seeded once from the operating system. */
static int rand_s(unsigned int *out) {
	static uint64_t s; static int seeded;
	if (!seeded) {
#if defined(__APPLE__)
		arc4random_buf(&s, sizeof s);
#else
		if (getrandom(&s, sizeof s, 0) != (ssize_t)sizeof s) s = 0x9E3779B97F4A7C15ull ^ (uint64_t)time(0);
#endif
		if (!s) s = 0x9E3779B97F4A7C15ull;
		seeded = 1;
	}
	s ^= s >> 12; s ^= s << 25; s ^= s >> 27;
	*out = (unsigned int)((s * 0x2545F4914F6CDD1Dull) >> 32);
	return 0;
}
#endif

#endif
