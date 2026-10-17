#ifndef WE_RDTSC_X86_H
#define WE_RDTSC_X86_H

#if defined(_MSC_VER) && defined(_M_IX86) && defined(NORDTSCP)
/* MSVC x86 may move a C volatile load outside an intrinsic RDTSC pair.
   Keep both timestamps and the load in one assembly block. */
static uint64_t we_rdtsc_probe_x86(volatile uint8_t *address)
{
    unsigned int start_lo, start_hi, end_lo, end_hi;
    __asm {
        lfence
        rdtsc
        mov start_lo, eax
        mov start_hi, edx
        mov ecx, address
        movzx ecx, byte ptr [ecx]
        lfence
        rdtsc
        mov end_lo, eax
        mov end_hi, edx
    }
    return (((uint64_t)end_hi << 32) | end_lo) -
        (((uint64_t)start_hi << 32) | start_lo);
}
#endif

#endif
