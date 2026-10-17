/* The assembled Write-Execute entry points (writeexc.asm). MASM x64 code follows the Win64 calling
   convention, so on x86-64 Linux and macOS they are called through ms_abi; Mach-O C symbols carry an
   underscore prefix that the assembler does not add, so they are bound by assembler label there. */
#ifndef WRITEEXEC_API_H
#define WRITEEXEC_API_H
#include <stdint.h>
#include "we_portable.h"

extern uint16_t WE_ABI WriteExecSHL1_C(uint8_t) WE_SYM(WriteExecSHL1_C);
extern uint16_t WE_ABI WriteExecSHL_C(uint8_t, uint8_t) WE_SYM(WriteExecSHL_C);
extern uint32_t WE_ABI WriteExecSHL32_C(uint32_t, uint8_t) WE_SYM(WriteExecSHL32_C);
extern uint64_t WE_ABI WriteExecSHL64_C(uint64_t, uint8_t) WE_SYM(WriteExecSHL64_C);
extern uint16_t WE_ABI WriteExecSHR_C(uint8_t, uint8_t) WE_SYM(WriteExecSHR_C);
extern uint32_t WE_ABI WriteExecSHR32_C(uint32_t, uint8_t) WE_SYM(WriteExecSHR32_C);
extern uint64_t WE_ABI WriteExecSHR64_C(uint64_t, uint8_t) WE_SYM(WriteExecSHR64_C);
extern uint8_t WE_ABI WriteExecNZ_C(uint8_t) WE_SYM(WriteExecNZ_C);
extern uint8_t WE_ABI WriteExecNOT_C(uint8_t) WE_SYM(WriteExecNOT_C);
extern uint16_t WE_ABI WriteExecINC_C(uint8_t) WE_SYM(WriteExecINC_C);
extern uint16_t WE_ABI WriteExecDEC_C(uint8_t) WE_SYM(WriteExecDEC_C);
extern uint8_t WE_ABI WriteExecXOR_C(uint8_t, uint8_t) WE_SYM(WriteExecXOR_C);
extern uint32_t WE_ABI WriteExecXOR32_C(uint32_t, uint32_t) WE_SYM(WriteExecXOR32_C);
extern uint8_t WE_ABI WriteExecOR_C(uint8_t, uint8_t) WE_SYM(WriteExecOR_C);
extern uint8_t WE_ABI WriteExecAND_C(uint8_t, uint8_t) WE_SYM(WriteExecAND_C);
extern uint16_t WE_ABI WriteExecADD_C(uint8_t, uint8_t) WE_SYM(WriteExecADD_C);
extern uint32_t WE_ABI WriteExecADD32_C(uint32_t, uint32_t) WE_SYM(WriteExecADD32_C);
extern uint64_t WE_ABI WriteExecADD64_C(uint64_t, uint64_t) WE_SYM(WriteExecADD64_C);
extern uint16_t WE_ABI WriteExecSUB_C(uint8_t, uint8_t) WE_SYM(WriteExecSUB_C);
extern uint32_t WE_ABI WriteExecSUB32_C(uint32_t, uint32_t) WE_SYM(WriteExecSUB32_C);
extern uint64_t WE_ABI WriteExecSUB64_C(uint64_t, uint64_t) WE_SYM(WriteExecSUB64_C);
extern uint64_t WE_ABI WriteExecMUL32_C(uint32_t, uint32_t) WE_SYM(WriteExecMUL32_C);
extern uint32_t WE_ABI WriteExecDIV32_C(uint64_t, uint32_t) WE_SYM(WriteExecDIV32_C);
extern uint32_t WE_ABI WriteExecMOD32_C(uint64_t, uint32_t) WE_SYM(WriteExecMOD32_C);
extern uint32_t WE_ABI WriteExecMODEXP32_C(uint32_t, uint32_t, uint32_t) WE_SYM(WriteExecMODEXP32_C);
extern uint32_t WE_ABI WriteExecTe0_C(uint8_t) WE_SYM(WriteExecTe0_C);
extern uint32_t WE_ABI WriteExecTe1_C(uint8_t) WE_SYM(WriteExecTe1_C);
extern uint32_t WE_ABI WriteExecTe2_C(uint8_t) WE_SYM(WriteExecTe2_C);
extern uint32_t WE_ABI WriteExecTe3_C(uint8_t) WE_SYM(WriteExecTe3_C);
extern uint8_t WE_ABI WriteExecTe4_C(uint8_t) WE_SYM(WriteExecTe4_C);
extern void WE_ABI WriteExecAESLookup_C(uint8_t*, uint8_t*, uint8_t*) WE_SYM(WriteExecAESLookup_C);

#endif
