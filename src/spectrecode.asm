ifndef X64
.model flat, C
endif
option casemap :none

; Keep in sync with WE_PROBE_STRIDE in portable/we_cache_probe.h.
PROBE_STRIDE EQU 4096
PROBE_SHIFT EQU 12

.code

;EXTERN tmp:BYTE
;array1_size equ 16

ifndef X64
SIZEWORD TEXTEQU <dword>
acmltr TEXTEQU <eax>
ctr TEXTEQU <ecx>

;eax, ecx, edx are considered volatile
SpecRSA1 PROC x1: DWORD, base: DWORD
else
SIZEWORD TEXTEQU <qword>
acmltr TEXTEQU <rax>
ctr TEXTEQU <rcx>

x1 TEXTEQU <rcx>
base TEXTEQU <edx>

;rax, rcx, rdx, r8, r9, r10, r11 are considered volatile
;x64 calling convention passes arguments fastcall: RCX, RDX, R8, R9, on stack but using default argument scheme uses stack and without first 4 indexes them incorrectly
;PROC -> DWORD PTR[rsp + 40] also could work here to use a more appropriate esp based indexing instead of ebp

SpecRSA1 PROC
endif

EXTERN array1:SIZEWORD
EXTERN array1_size:DWORD
EXTERN _n:DWORD ;61 * 53
EXTERN _ns:QWORD 
EXTERN array2:SIZEWORD

mov eax, array1_size
cmp x1, acmltr
jae nospecrsa
ifndef X64
mov eax, x1
mov eax, dword ptr [array1 + acmltr]
else
lea acmltr, [array1] ; 64-bits cannot be addressed in indirect mov without using linker option /LARGEADDRESSAWARE:NO to handle ADDR32 relocations
mov eax, dword ptr [acmltr + x1]
endif
mov ecx, base

mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n] ; avoid overflow and branching by dividing the high part by factoring out 2^32*n
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx
and acmltr, 0ffh
shl acmltr, PROBE_SHIFT
lea ctr, array2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff00h
shl acmltr, PROBE_SHIFT - 8
lea ctr, array2 + 256 * PROBE_STRIDE
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff0000h
shr acmltr, 16 - PROBE_SHIFT
lea ctr, array2 + 256 * PROBE_STRIDE * 2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff000000h
shr acmltr, 24 - PROBE_SHIFT ; 24 - 12, where shl rax, 12 comes from 1000h
lea ctr, array2 + 256 * PROBE_STRIDE * 3
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

nospecrsa:
ret
SpecRSA1 ENDP

ifndef X64
SpecRSA2 PROC x1: DWORD, base: DWORD
else
SpecRSA2 PROC
endif

mov eax, array1_size
cmp x1, acmltr
jae nospecrsa
ifndef X64
mov eax, x1
mov eax, dword ptr [array1 + acmltr]
else
lea acmltr, [array1] ; 64-bits cannot be addressed in indirect mov without using linker option /LARGEADDRESSAWARE:NO to handle ADDR32 relocations
mov eax, dword ptr [acmltr + x1]
endif
mov ecx, base

mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n] ; avoid overflow and branching by dividing the high part by factoring out 2^32*n
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx
and acmltr, 0ffh
shl acmltr, PROBE_SHIFT
lea ctr, array2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff00h
shl acmltr, PROBE_SHIFT - 8
lea ctr, array2 + 256 * PROBE_STRIDE
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff0000h
shr acmltr, 16 - PROBE_SHIFT
lea ctr, array2 + 256 * PROBE_STRIDE * 2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff000000h
shr acmltr, 24 - PROBE_SHIFT ; 24 - 12, where shl rax, 12 comes from 1000h
lea ctr, array2 + 256 * PROBE_STRIDE * 3
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

nospecrsa:
ret
SpecRSA2 ENDP

ifndef X64
SpecRSA4 PROC x1: DWORD, base: DWORD
else
SpecRSA4 PROC
endif

mov eax, array1_size
cmp x1, acmltr
jae nospecrsa
ifndef X64
mov eax, x1
mov eax, dword ptr [array1 + acmltr]
else
lea acmltr, [array1] ; 64-bits cannot be addressed in indirect mov without using linker option /LARGEADDRESSAWARE:NO to handle ADDR32 relocations
mov eax, dword ptr [acmltr + x1]
endif
mov ecx, base

mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n] ; avoid overflow and branching by dividing the high part by factoring out 2^32*n
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx
and acmltr, 0ffh
shl acmltr, PROBE_SHIFT
lea ctr, array2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff00h
shl acmltr, PROBE_SHIFT - 8
lea ctr, array2 + 256 * PROBE_STRIDE
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff0000h
shr acmltr, 16 - PROBE_SHIFT
lea ctr, array2 + 256 * PROBE_STRIDE * 2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff000000h
shr acmltr, 24 - PROBE_SHIFT ; 24 - 12, where shl rax, 12 comes from 1000h
lea ctr, array2 + 256 * PROBE_STRIDE * 3
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

nospecrsa:
ret
SpecRSA4 ENDP

ifndef X64
SpecRSA5 PROC x1: DWORD, base: DWORD
else
SpecRSA5 PROC
endif

mov eax, array1_size
cmp x1, acmltr
jae nospecrsa
ifndef X64
mov eax, x1
mov eax, dword ptr [array1 + acmltr]
else
lea acmltr, [array1] ; 64-bits cannot be addressed in indirect mov without using linker option /LARGEADDRESSAWARE:NO to handle ADDR32 relocations
mov eax, dword ptr [acmltr + x1]
endif
mov ecx, base

mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n] ; avoid overflow and branching by dividing the high part by factoring out 2^32*n
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx
and acmltr, 0ffh
shl acmltr, PROBE_SHIFT
lea ctr, array2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff00h
shl acmltr, PROBE_SHIFT - 8
lea ctr, array2 + 256 * PROBE_STRIDE
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff0000h
shr acmltr, 16 - PROBE_SHIFT
lea ctr, array2 + 256 * PROBE_STRIDE * 2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff000000h
shr acmltr, 24 - PROBE_SHIFT ; 24 - 12, where shl rax, 12 comes from 1000h
lea ctr, array2 + 256 * PROBE_STRIDE * 3
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

nospecrsa:
ret
SpecRSA5 ENDP

ifndef X64
SpecRSA6 PROC x1: DWORD, base: DWORD
else
SpecRSA6 PROC
endif

mov eax, array1_size
cmp x1, acmltr
jae nospecrsa
ifndef X64
mov eax, x1
mov eax, dword ptr [array1 + acmltr]
else
lea acmltr, [array1] ; 64-bits cannot be addressed in indirect mov without using linker option /LARGEADDRESSAWARE:NO to handle ADDR32 relocations
mov eax, dword ptr [acmltr + x1]
endif
mov ecx, base

mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n] ; avoid overflow and branching by dividing the high part by factoring out 2^32*n
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx
and acmltr, 0ffh
shl acmltr, PROBE_SHIFT
lea ctr, array2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff00h
shl acmltr, PROBE_SHIFT - 8
lea ctr, array2 + 256 * PROBE_STRIDE
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff0000h
shr acmltr, 16 - PROBE_SHIFT
lea ctr, array2 + 256 * PROBE_STRIDE * 2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff000000h
shr acmltr, 24 - PROBE_SHIFT ; 24 - 12, where shl rax, 12 comes from 1000h
lea ctr, array2 + 256 * PROBE_STRIDE * 3
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

nospecrsa:
ret
SpecRSA6 ENDP

ifndef X64
SpecRSA8 PROC x1: DWORD, base: DWORD
else
SpecRSA8 PROC
endif

mov eax, array1_size
cmp x1, acmltr
jae nospecrsa
ifndef X64
mov eax, x1
mov eax, dword ptr [array1 + acmltr]
else
lea acmltr, [array1] ; 64-bits cannot be addressed in indirect mov without using linker option /LARGEADDRESSAWARE:NO to handle ADDR32 relocations
mov eax, dword ptr [acmltr + x1]
endif
mov ecx, base

mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n] ; avoid overflow and branching by dividing the high part by factoring out 2^32*n
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx ; zero extension occurs automatically per spec
mul ctr
ifndef X64
push eax
mov eax, edx
xor edx, edx
div dword ptr [_n]
pop eax
div dword ptr [_n]
else
xor edx, edx
div qword ptr [_ns]
endif

mov eax, edx
and acmltr, 0ffh
shl acmltr, PROBE_SHIFT
lea ctr, array2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff00h
shl acmltr, PROBE_SHIFT - 8
lea ctr, array2 + 256 * PROBE_STRIDE
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff0000h
shr acmltr, 16 - PROBE_SHIFT
lea ctr, array2 + 256 * PROBE_STRIDE * 2
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

mov eax, edx
and acmltr, 0ff000000h
shr acmltr, 24 - PROBE_SHIFT ; 24 - 12, where shl rax, 12 comes from 1000h
lea ctr, array2 + 256 * PROBE_STRIDE * 3
mov al, byte ptr [ctr + acmltr]
;and al, byte ptr [tmp]

nospecrsa:
ret
SpecRSA8 ENDP

;SpecAES PROC
;SpecAES ENDP

;SpecProcAES PROC

;SpecProcAES ENDP

END
