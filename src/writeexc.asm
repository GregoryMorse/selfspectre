ifndef X64
.model flat, C
endif
option casemap :none

.code
PUBLIC shlarg1, shlarg6, shrarg2 ; read-only diagnostics for the SHR32 native harness

DEFINESHL macro Index, Lbl, Ct
	&Lbl&_&Index&: mov word ptr [Lbl+1+6], Index shl Ct
	jmp [Lbl]
	db 256-($-&Lbl&_&Index&) dup (090h) ;; nop
endm

WriteExecSHL1 PROC
shlarg:: jmp shlres_0+08000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINESHL %idx_value, shlres, 1
	idx_value = idx_value + 1
ENDM
shlres:: mov word ptr [shlres+6], 8000h
shlret:: jmp $+80000000h
WriteExecSHL1 ENDP

ShlArg TEXTEQU <cl>

ifndef X64
SIZEWORD TEXTEQU <dword>
acmltr TEXTEQU <eax>
ctr TEXTEQU <ecx>

WriteExecSHL1_C PROC shl1arg: BYTE
mov cl, byte ptr [shl1arg]
else
WriteExecSHL1_C PROC
endif
mov byte ptr [shlarg+2], cl
ifdef X64
mov dword ptr [shlres+1+2], shlretval + 1+1 - shlret
else
mov dword ptr [shlres+1+2], shlretval + 1+1
endif
mov dword ptr [shlret+1], shlretval - shlret - 5
jmp WriteExecSHL1
shlretval: mov ax, 8000h
ret
WriteExecSHL1_C ENDP

WriteExecSHL4 PROC
shlarg4:: jmp shlres4_0+08000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINESHL %idx_value, shlres4, 4
	idx_value = idx_value + 1
ENDM
shlres4:: mov word ptr [shlres4+6], 8000h
shlret4:: jmp $+80000000h
WriteExecSHL4 ENDP

WriteExecSHL5 PROC
shlarg5:: jmp shlres5_0+08000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINESHL %idx_value, shlres5, 5
	idx_value = idx_value + 1
ENDM
shlres5:: mov word ptr [shlres5+6], 8000h
shlret5:: jmp $+80000000h
WriteExecSHL5 ENDP

WriteExecSHL6 PROC
shlarg6:: jmp shlres6_0+08000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINESHL %idx_value, shlres6, 6
	idx_value = idx_value + 1
ENDM
shlres6:: mov word ptr [shlres6+6], 8000h
shlret6:: jmp $+80000000h
WriteExecSHL6 ENDP

WriteExecSHL7 PROC
shlarg7:: jmp shlres7_0+08000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINESHL %idx_value, shlres7, 7
	idx_value = idx_value + 1
ENDM
shlres7:: mov word ptr [shlres7+6], 8000h
shlret7:: jmp $+80000000h
WriteExecSHL7 ENDP

DEFINENOT macro Index, Lbl
	&Lbl&_&Index&: mov byte ptr [Lbl+6], not Index
	jmp [Lbl] ;; preprocessor wrongly assumes 10 bytes for jump unfortunately not 2 or 5 bytes
IF Index GT 0f7h ;; preprocessor also cannot look at distance to future labels
	db 7 dup (090h)
ELSE
	db 4 dup (090h)
	;;db 16-($-&Lbl&_&Index&) dup (090h) ;; nop
ENDIF
endm

WriteExecNOT PROC
notarg:: mov byte ptr [shlarg4+2], 0
ifdef X64
mov dword ptr [shlres4+1+2], notargshl + 1 - shlret4
else
mov dword ptr [shlres4+1+2], notargshl + 1
endif
mov dword ptr [shlret4+1], notargshl - shlret4 - 5
jmp WriteExecSHL4

notargshl: jmp notres_0+08000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINENOT %idx_value, notres
	idx_value = idx_value + 1
ENDM
notres:: mov byte ptr [notres+6], 0
notret:: jmp $+80000000h
WriteExecNOT ENDP

ifndef X64
WriteExecNOT_C PROC not1arg: BYTE
mov cl, byte ptr [not1arg]
else
WriteExecNOT_C PROC
endif
mov byte ptr [notarg+2+4], cl
ifdef X64
mov dword ptr [notres+2], notretval + 1 - notret
else
mov dword ptr [notres+2], notretval + 1
endif
mov dword ptr [notret+1], notretval - notret - 5
jmp WriteExecNOT
notretval: mov al, 0h
ret
WriteExecNOT_C ENDP

DEFINENZ macro Index, Lbl
	&Lbl&_&Index&: mov byte ptr [Lbl+6], (Index NE 0) and 1
	jmp [Lbl] ;; preprocessor wrongly assumes 10 bytes for jump unfortunately not 2 or 5 bytes
IF Index GT 0f7h ;; preprocessor also cannot look at distance to future labels
	db 7 dup (090h)
ELSE
	db 4 dup (090h)
	;;db 16-($-&Lbl&_&Index&) dup (090h) ;; nop
ENDIF
endm

WriteExecNZ PROC
nzarg:: mov byte ptr [shlarg4+2], 0
ifdef X64
mov dword ptr [shlres4+1+2], nzargshl + 1 - shlret4
else
mov dword ptr [shlres4+1+2], nzargshl + 1
endif
mov dword ptr [shlret4+1], nzargshl - shlret4 - 5
jmp WriteExecSHL4

nzargshl: jmp nzres_0+08000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINENZ %idx_value, nzres
	idx_value = idx_value + 1
ENDM
nzres:: mov byte ptr [nzres+6], 0
nzret:: jmp $+80000000h
WriteExecNZ ENDP

ifndef X64
WriteExecNZ_C PROC nz1arg: BYTE
mov cl, byte ptr [nz1arg]
else
WriteExecNZ_C PROC
endif
mov byte ptr [nzarg+2+4], cl
ifdef X64
mov dword ptr [nzres+2], nzretval + 1 - nzret
else
mov dword ptr [nzres+2], nzretval + 1
endif
mov dword ptr [nzret+1], nzretval - nzret - 5
jmp WriteExecNZ
nzretval: mov al, 0h
ret
WriteExecNZ_C ENDP

DEFINEXOR macro Orig, Index
	xor&Orig&_&Index&: mov byte ptr [xorres+6], Orig xor Index
	jmp [xorres]
IF Index EQ 0ffh
	dt 409 dup (090909090909090909090h)
	db 5 dup (090h)
	;;db 4096+16-5-($-xor&Orig&_&Index&) dup (090h) ;; nop
ELSE
	db 4 dup (090h)
	;;db 16-($-xor&Orig&_&Index&) dup (090h) ;; nop
ENDIF
endm

DEFINEXORGRP macro Index
xorarg1_&Index&: jmp xor&Index&_0+08000h
IRP ct_value, <0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63>
	DEFINEXOR Index, %ct_value
ENDM
IRP ct_value, <64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127>
	DEFINEXOR Index, %ct_value
ENDM
IRP ct_value, <128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191>
	DEFINEXOR Index, %ct_value
ENDM
IRP ct_value, <192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255>
	DEFINEXOR Index, %ct_value
ENDM
endm

DEFINEXORJMP macro Index
	mov dword ptr [xorargshl2+1+2], xorarg1_&Index&+1
	jmp xorargshl2
	;; extra padding is wasteful but otherwise would need a shl 4, not just the shl 5
IF Index GT 0fbh
	db 20 dup (090h)
ELSE
	db 17 dup (090h)
ENDIF
ENDM

WriteExecXOR PROC

xorarg1:: mov byte ptr [shlarg5+2], 0
ifdef X64
mov dword ptr [shlres5+1+2], xorargshl1 + 1 + 2 + 4 - shlret5
else
mov dword ptr [shlres5+1+2], xorargshl1 + 1 + 2 + 4
endif
mov dword ptr [shlret5+1], shlretval5 - shlret5 - 5
jmp WriteExecSHL5
shlretval5:

xorarg2:: mov byte ptr [shlarg4+2], 0
ifdef X64
mov dword ptr [shlres4+1+2], xorargshl2 + 1 + 2 + 4 - shlret4
else
mov dword ptr [shlres4+1+2], xorargshl2 + 1 + 2 + 4
endif
mov dword ptr [shlret4+1], shlretval4 - shlret4 - 5
jmp WriteExecSHL4
shlretval4:

ifdef X64
mov dword ptr [xorargshl1 + 1+2], xorj+2-xorargshl1-1-2-4-2
else
mov dword ptr [xorargshl1 + 1+2], xorj+2
endif
mov byte ptr [xorloop + 1], xorhead-xorloop-2
jmp xorargshl1
xorhead: mov byte ptr [xorloop+1], 0 ;exit loop
xorargshl1: mov word ptr [xorj+2], 8000h
ifdef X64
mov dword ptr [xorargshl1 + 1+2], xorargshl2+2+2-xorargshl1-1-2-4-2
else
mov dword ptr [xorargshl1 + 1+2], xorargshl2jmp+1
endif
xorloop: jmp xorhead

ifndef X64
xorargshl2jmp: jmp xorargshl2begin+08000h
xorargshl2begin:
idx_value = 0
WHILE idx_value LT 100h
	DEFINEXORJMP %idx_value
	idx_value = idx_value + 1
ENDM
endif
xorargshl2: mov word ptr [xorarg1_0+1], 8000h

xorj: jmp xorarg1_0+0800000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINEXORGRP %idx_value	
	idx_value = idx_value + 1
ENDM
xorres:: mov byte ptr [xorres+6], 0
xorret:: jmp $+80000000h
WriteExecXOR ENDP

ifndef X64
WriteExecXOR_C PROC xor1arg: BYTE, xor2arg: BYTE
mov cl, byte ptr [xor1arg]
mov dl, byte ptr [xor2arg]
else
WriteExecXOR_C PROC
endif
mov byte ptr [xorarg1+6], cl
mov byte ptr [xorarg2+6], dl
ifdef X64
mov dword ptr [xorres+2], xorretval + 1 - xorret
else
mov dword ptr [xorres+2], xorretval + 1
endif
mov dword ptr [xorret+1], xorretval - xorret - 5
jmp WriteExecXOR
xorretval: mov al, 80h
ret
WriteExecXOR_C ENDP

WriteExecXOR32 PROC
IRP val, <1, 2, 3, 4>
xor32arg1_&val&:: mov byte ptr [xorarg1+6], 0
xor32arg2_&val&:: mov byte ptr [xorarg2+6], 0
ifdef X64
mov dword ptr [xorres+2], xorres&val& + 2+4 - xorret
else
mov dword ptr [xorres+2], xorres&val& + 2+4
endif
mov dword ptr [xorret+1], xor32narg_&val& - xorret - 5
jmp WriteExecXOR
xor32narg_&val&:
ENDM
xorres1:: mov byte ptr [xorres1+6], 0
xorres2:: mov byte ptr [xorres2+6], 0
xorres3:: mov byte ptr [xorres3+6], 0
xorres4:: mov byte ptr [xorres4+6], 0
xor32ret:: jmp $+80000000h
WriteExecXOR32 ENDP

ifndef X64
WriteExecXOR32_C PROC xor32_1arg: DWORD, xor32_2arg: DWORD
mov ecx, dword ptr [xor32_1arg]
mov edx, dword ptr [xor32_2arg]
else
WriteExecXOR32_C PROC
endif
mov byte ptr [xor32arg1_1+6], cl
mov byte ptr [xor32arg2_1+6], dl
mov byte ptr [xor32arg1_2+6], ch
mov byte ptr [xor32arg2_2+6], dh
shr ecx, 16
shr edx, 16
mov byte ptr [xor32arg1_3+6], cl
mov byte ptr [xor32arg2_3+6], dl
mov byte ptr [xor32arg1_4+6], ch
mov byte ptr [xor32arg2_4+6], dh
ifdef X64
mov dword ptr [xorres1+2], xorretval + 1 - xorres2
mov dword ptr [xorres2+2], xorretval + 2 - xorres3
mov dword ptr [xorres3+2], xorretval + 3 - xorres4
mov dword ptr [xorres4+2], xorretval + 4 - xor32ret
else
mov dword ptr [xorres1+2], xorretval + 1
mov dword ptr [xorres2+2], xorretval + 2
mov dword ptr [xorres3+2], xorretval + 3
mov dword ptr [xorres4+2], xorretval + 4
endif
mov dword ptr [xor32ret+1], xorretval - xor32ret - 5
jmp WriteExecXOR32
xorretval: mov eax, 80000000h
ret
WriteExecXOR32_C ENDP

DEFINEOR macro Orig, Index
	or&Orig&_&Index&: mov byte ptr [orres+6], Orig or Index
	jmp [orres]
IF Index EQ 0ffh
	dt 409 dup (090909090909090909090h)
	db 5 dup (090h)
	;;db 4096+16-5-($-or&Orig&_&Index&) dup (090h) ;; nop
ELSE
	db 4 dup (090h)
	;;db 16-($-or&Orig&_&Index&) dup (090h) ;; nop
ENDIF
endm

DEFINEORGRP macro Index
orarg1_&Index&: jmp or&Index&_0+08000h
IRP ct_value, <0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63>
	DEFINEOR Index, %ct_value
ENDM
IRP ct_value, <64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127>
	DEFINEOR Index, %ct_value
ENDM
IRP ct_value, <128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191>
	DEFINEOR Index, %ct_value
ENDM
IRP ct_value, <192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255>
	DEFINEOR Index, %ct_value
ENDM
endm

DEFINEORJMP macro Index
	mov dword ptr [orargshl2+1+2], orarg1_&Index&+1
	jmp orargshl2
	;; extra padding is wasteful but otherwise would need a shl 4, not just the shl 5
IF Index GT 0fbh
	db 20 dup (090h)
ELSE
	db 17 dup (090h)
ENDIF
ENDM

WriteExecOR PROC

orarg1:: mov byte ptr [shlarg5+2], 0
ifdef X64
mov dword ptr [shlres5+1+2], orargshl1 + 1 + 2 + 4 - shlret5
else
mov dword ptr [shlres5+1+2], orargshl1 + 1 + 2 + 4
endif
mov dword ptr [shlret5+1], shlretval5 - shlret5 - 5
jmp WriteExecSHL5
shlretval5:

orarg2:: mov byte ptr [shlarg4+2], 0
ifdef X64
mov dword ptr [shlres4+1+2], orargshl2 + 1 + 2 + 4 - shlret4
else
mov dword ptr [shlres4+1+2], orargshl2 + 1 + 2 + 4
endif
mov dword ptr [shlret4+1], shlretval4 - shlret4 - 5
jmp WriteExecSHL4
shlretval4:

ifdef X64
mov dword ptr [orargshl1 + 1+2], orj+2-orargshl1-1-2-4-2
else
mov dword ptr [orargshl1 + 1+2], orj+2
endif
mov byte ptr [orloop + 1], orhead-orloop-2
jmp orargshl1
orhead: mov byte ptr [orloop+1], 0 ;exit loop
orargshl1: mov word ptr [orj+2], 8000h
ifdef X64
mov dword ptr [orargshl1 + 1+2], orargshl2+2+2-orargshl1-1-2-4-2
else
mov dword ptr [orargshl1 + 1+2], orargshl2jmp+1
endif
orloop: jmp orhead

ifndef X64
orargshl2jmp: jmp orargshl2begin+08000h
orargshl2begin:
idx_value = 0
WHILE idx_value LT 100h
	DEFINEORJMP %idx_value
	idx_value = idx_value + 1
ENDM
endif
orargshl2: mov word ptr [orarg1_0+1], 8000h

orj: jmp orarg1_0+0800000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINEORGRP %idx_value	
	idx_value = idx_value + 1
ENDM
orres:: mov byte ptr [orres+6], 0
orret:: jmp $+80000000h
WriteExecOR ENDP

ifndef X64
WriteExecOR_C PROC or1arg: BYTE, or2arg: BYTE
mov cl, byte ptr [or1arg]
mov dl, byte ptr [or2arg]
else
WriteExecOR_C PROC
endif
mov byte ptr [orarg1+6], cl
mov byte ptr [orarg2+6], dl
ifdef X64
mov dword ptr [orres+2], orretval + 1 - orret
else
mov dword ptr [orres+2], orretval + 1
endif
mov dword ptr [orret+1], orretval - orret - 5
jmp WriteExecOR
orretval: mov al, 80h
ret
WriteExecOR_C ENDP

DEFINEAND macro Orig, Index
	and&Orig&_&Index&: mov byte ptr [andres+6], Orig and Index
	jmp [andres]
IF Index EQ 0ffh
	dt 409 dup (090909090909090909090h)
	db 5 dup (090h)
	;;db 4096+16-5-($-and&Orig&_&Index&) dup (090h) ;; nop
ELSE
	db 4 dup (090h)
	;;db 16-($-and&Orig&_&Index&) dup (090h) ;; nop
ENDIF
endm

DEFINEANDGRP macro Index
andarg1_&Index&: jmp and&Index&_0+08000h
IRP ct_value, <0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63>
	DEFINEAND Index, %ct_value
ENDM
IRP ct_value, <64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127>
	DEFINEAND Index, %ct_value
ENDM
IRP ct_value, <128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191>
	DEFINEAND Index, %ct_value
ENDM
IRP ct_value, <192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255>
	DEFINEAND Index, %ct_value
ENDM
endm

DEFINEANDJMP macro Index
	mov dword ptr [andargshl2+1+2], andarg1_&Index&+1
	jmp andargshl2
	;; extra padding is wasteful but otherwise would need a shl 4, not just the shl 5
IF Index GT 0fbh
	db 20 dup (090h)
ELSE
	db 17 dup (090h)
ENDIF
ENDM

WriteExecAND PROC

andarg1:: mov byte ptr [shlarg5+2], 0
ifdef X64
mov dword ptr [shlres5+1+2], andargshl1 + 1 + 2 + 4 - shlret5
else
mov dword ptr [shlres5+1+2], andargshl1 + 1 + 2 + 4
endif
mov dword ptr [shlret5+1], shlretval5 - shlret5 - 5
jmp WriteExecSHL5
shlretval5:

andarg2:: mov byte ptr [shlarg4+2], 0
ifdef X64
mov dword ptr [shlres4+1+2], andargshl2 + 1 + 2 + 4 - shlret4
else
mov dword ptr [shlres4+1+2], andargshl2 + 1 + 2 + 4
endif
mov dword ptr [shlret4+1], shlretval4 - shlret4 - 5
jmp WriteExecSHL4
shlretval4:

ifdef X64
mov dword ptr [andargshl1 + 1+2], andj+2-andargshl1-1-2-4-2
else
mov dword ptr [andargshl1 + 1+2], andj+2
endif
mov byte ptr [andloop + 1], andhead-andloop-2
jmp andargshl1
andhead: mov byte ptr [andloop+1], 0 ;exit loop
andargshl1: mov word ptr [andj+2], 8000h
ifdef X64
mov dword ptr [andargshl1 + 1+2], andargshl2+2+2-andargshl1-1-2-4-2
else
mov dword ptr [andargshl1 + 1+2], andargshl2jmp+1
endif
andloop: jmp andhead

ifndef X64
andargshl2jmp: jmp andargshl2begin+08000h
andargshl2begin:
idx_value = 0
WHILE idx_value LT 100h
	DEFINEANDJMP %idx_value
	idx_value = idx_value + 1
ENDM
endif
andargshl2: mov word ptr [andarg1_0+1], 8000h

andj: jmp andarg1_0+0800000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINEANDGRP %idx_value	
	idx_value = idx_value + 1
ENDM
andres:: mov byte ptr [andres+6], 0
andret:: jmp $+80000000h
WriteExecAND ENDP

ifndef X64
WriteExecAND_C PROC and1arg: BYTE, and2arg: BYTE
mov cl, byte ptr [and1arg]
mov dl, byte ptr [and2arg]
else
WriteExecAND_C PROC
endif
mov byte ptr [andarg1+6], cl
mov byte ptr [andarg2+6], dl
ifdef X64
mov dword ptr [andres+2], andretval + 1 - andret
else
mov dword ptr [andres+2], andretval + 1
endif
mov dword ptr [andret+1], andretval - andret - 5
jmp WriteExecAND
andretval: mov al, 80h
ret
WriteExecAND_C ENDP

DEFINESHLGEN macro Orig, Index, Lbl, Lbl2
	shl&Orig&_&Index&: mov byte ptr [Lbl+6], (Index shl Orig) and 0ffh
	mov byte ptr [Lbl2+6], Index shr (8-Orig)
	jmp [Lbl]
IF Index EQ 0ffh
	dt 820 dup (090909090909090909090h)
	;;db 8192+32-5-($-shl&Orig&_&Index&) dup (090h) ;; nop
ELSE
	db 13 dup (090h)
	;;db 32-($-shl&Orig&_&Index&) dup (090h) ;; nop
ENDIF
endm

DEFINESHLGRP macro Index, Lbl, Lbl2
shlarg2_&Index&: jmp shl&Index&_0+08000h
IRP ct_value, <0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63>
	DEFINESHLGEN Index, %ct_value, Lbl, Lbl2
ENDM
IRP ct_value, <64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127>
	DEFINESHLGEN Index, %ct_value, Lbl, Lbl2
ENDM
IRP ct_value, <128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191>
	DEFINESHLGEN Index, %ct_value, Lbl, Lbl2
ENDM
IRP ct_value, <192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255>
	DEFINESHLGEN Index, %ct_value, Lbl, Lbl2
ENDM
endm

DEFINESHLJMP macro Index
	mov dword ptr [shlargshl1+1+2], shlarg2_&Index&+1
	jmp shlargshl1
	;; extra padding is wasteful but otherwise would need a shl 4, not just the shl 5
IF Index GT 5
	db 32+20 dup (090h)
ELSE
	db 32+17 dup (090h)
ENDIF
ENDM

WriteExecSHL PROC
shlarg1:: mov byte ptr [shlarg5+2], 0
ifdef X64
mov dword ptr [shlres5+1+2], shlargshl1 + 1 + 2 + 4 - shlret5
else
mov dword ptr [shlres5+1+2], shlargshl1 + 1 + 2 + 4
endif
mov dword ptr [shlret5+1], shlretval5 - shlret5 - 5
jmp WriteExecSHL5
shlretval5:

shlarg2:: mov byte ptr [shlarg6+2], 0
ifdef X64
mov dword ptr [shlres6+1+2], shlargshl2 + 1 + 2 + 4 - shlret6
else
mov dword ptr [shlres6+1+2], shlargshl2 + 1 + 2 + 4
endif
mov dword ptr [shlret6+1], shlretval6 - shlret6 - 5
jmp WriteExecSHL6
shlretval6:

ifdef X64
mov dword ptr [shlargshl2 + 1+2], shlj+2-shlargshl2-1-2-4-2
else
mov dword ptr [shlargshl2 + 1+2], shlj+2
endif
mov byte ptr [shlloop + 1], shlhead-shlloop-2
jmp shlargshl2
shlhead: mov byte ptr [shlloop+1], 0 ;exit loop
shlargshl2: mov word ptr [shlj+2], 8000h
ifdef X64
mov dword ptr [shlargshl2 + 1+2], shlargshl1+2+2-shlargshl2-1-2-4-2
else
mov dword ptr [shlargshl2 + 1+2], shlargshl1jmp+1
endif
shlloop: jmp shlhead

ifndef X64
shlargshl1jmp: jmp shlargshl1begin+08000h
shlargshl1begin:
idx_value = 0
WHILE idx_value LT 8
	DEFINESHLJMP %idx_value
	idx_value = idx_value + 1
ENDM
endif
shlargshl1: mov word ptr [shlarg2_0+1], 8000h

shlj: jmp shlarg2_0+0800000h
idx_value = 0
WHILE idx_value LT 8
	DEFINESHLGRP %idx_value, shlbres, shlbres2
	idx_value = idx_value + 1
ENDM
shlbres:: mov byte ptr [shlbres+6], 0
shlbres2:: mov byte ptr [shlbres2+6], 0
shlbret:: jmp $+80000000h
WriteExecSHL ENDP

ifndef X64
WriteExecSHL_C PROC shl1arg: BYTE, shl2arg: BYTE
mov cl, byte ptr [shl1arg]
mov dl, byte ptr [shl2arg]
else
WriteExecSHL_C PROC
endif
mov byte ptr [shlarg1+2+4], cl
mov byte ptr [shlarg2+2+4], dl
ifdef X64
mov dword ptr [shlbres+2], shlretval + 1+1 - shlbres2
mov dword ptr [shlbres2+2], shlretval + 1+2 - shlbret
else
mov dword ptr [shlbres+2], shlretval + 1+1
mov dword ptr [shlbres2+2], shlretval + 1+2
endif
mov dword ptr [shlbret+1], shlretval - shlbret - 5
jmp WriteExecSHL
shlretval: mov ax, 8000h
ret
WriteExecSHL_C ENDP

SHLBYTE macro Idx, NxtIdx, Sz
shl&Sz&arg1_&Idx&copy: mov byte ptr [shlarg1+6], 0
shl&Sz&arg2_&Idx&copy: mov byte ptr [shlarg2+6], 0
ifdef X64
IF Idx EQ 1
mov dword ptr [shlbres+2], shl&Sz&res&Idx& + 2+4 - shlbres2
ELSE
mov dword ptr [shlbres+2], shl&Sz&res1_&Idx& + 2+4 - shlbres2
ENDIF
mov dword ptr [shlbres2+2], carry&Idx& + 2+4 - shlbret
else
IF Idx EQ 1
mov dword ptr [shlbres+2], shl&Sz&res&Idx& + 2+4
ELSE
mov dword ptr [shlbres+2], shl&Sz&res1_&Idx& + 2+4
ENDIF
mov dword ptr [shlbres2+2], carry&Idx& + 2+4
endif
IF NxtIdx EQ 0
mov dword ptr [shlbret+1], carry1 - shlbret - 5
ELSE
mov dword ptr [shlbret+1], shl&Sz&arg1_&NxtIdx&copy - shlbret - 5
ENDIF
jmp WriteExecSHL
ENDM

SHLCARRY macro Idx, NxtIdx, Sz
IF NxtIdx EQ 0
carry&Idx&: mov byte ptr [carry&Idx&+6], 0
ELSE
carry&Idx&: mov byte ptr [xorarg1+6], 0
shl&Sz&res1_&NxtIdx&: mov byte ptr [xorarg2+6], 0
ifdef X64
mov dword ptr [xorres+2], shl&Sz&res&NxtIdx& + 2+4 - xorret
else
mov dword ptr [xorres+2], shl&Sz&res&NxtIdx& + 2+4
endif
mov dword ptr [xorret+1], carry&NxtIdx& - xorret - 5
jmp WriteExecXOR
ENDIF
ENDM

WriteExecSHL32 PROC
;; shl 5, then shl 3 to split byte vs bits
shl32arg2_1:: mov byte ptr [shlarg1+6], 0
mov byte ptr [shlarg2+2+4], 5
ifdef X64
mov dword ptr [shlbres+2], shlsmall + 2+4 - shlbres2
mov dword ptr [shlbres2+2], shlrounds + 2+4 - shlbret
else
mov dword ptr [shlbres+2], shlsmall + 2+4
mov dword ptr [shlbres2+2], shlrounds + 2+4
endif
mov dword ptr [shlbret+1], shlsmall - shlbret - 5
jmp WriteExecSHL
shlsmall: mov byte ptr [shlarg1+6], 0
mov byte ptr [shlarg2+2+4], 3
ifdef X64
mov dword ptr [shlbres+2], shlsmall + 2+4 - shlbres2
mov dword ptr [shlbres2+2], shl32arg2small + 2+4 - shlbret
else
mov dword ptr [shlbres+2], shlsmall + 2+4
mov dword ptr [shlbres2+2], shl32arg2small + 2+4
endif
mov dword ptr [shlbret+1], shlrounds - shlbret - 5
jmp WriteExecSHL

shlrounds: mov byte ptr [shlarg6+2], 0
ifdef X64
mov dword ptr [shlres6+1+2], shlretval6 + 1 - shlret6
else
mov dword ptr [shlres6+1+2], shlretval6 + 1
endif
mov dword ptr [shlret6+1], shlretval6 - shlret6 - 5
jmp WriteExecSHL6
shlretval6: jmp $+8000h
ifdef X64
mov dword ptr [shl32arg1_1+2], shl32arg1_1copy+6 - shl32arg1_2
mov dword ptr [shl32arg1_2+2], shl32arg1_2copy+6 - shl32arg1_3
mov dword ptr [shl32arg1_3+2], shl32arg1_3copy+6 - shl32arg1_4
mov dword ptr [shl32arg1_4+2], shl32arg1_4copy+6 - shl32copied
else
mov dword ptr [shl32arg1_1+2], shl32arg1_1copy+6
mov dword ptr [shl32arg1_2+2], shl32arg1_2copy+6
mov dword ptr [shl32arg1_3+2], shl32arg1_3copy+6
mov dword ptr [shl32arg1_4+2], shl32arg1_4copy+6
endif
jmp shl32arg1_1
db 19 dup (090h)
ifdef X64
mov dword ptr [shl32arg1_1+2], shl32arg1_2copy+6 - shl32arg1_2
mov dword ptr [shl32arg1_2+2], shl32arg1_3copy+6 - shl32arg1_3
mov dword ptr [shl32arg1_3+2], shl32arg1_4copy+6 - shl32arg1_4
mov dword ptr [shl32arg1_4+2], shl32arg1_1copy+6 - shl32copied
else
mov dword ptr [shl32arg1_1+2], shl32arg1_2copy+6
mov dword ptr [shl32arg1_2+2], shl32arg1_3copy+6
mov dword ptr [shl32arg1_3+2], shl32arg1_4copy+6
mov dword ptr [shl32arg1_4+2], shl32arg1_1copy+6
endif
mov byte ptr [shl32arg1_4+6], 0
jmp shl32arg1_1
db 12 dup (090h)
ifdef X64
mov dword ptr [shl32arg1_1+2], shl32arg1_3copy+6 - shl32arg1_2
mov dword ptr [shl32arg1_2+2], shl32arg1_4copy+6 - shl32arg1_3
mov dword ptr [shl32arg1_3+2], shl32arg1_1copy+6 - shl32arg1_4
mov dword ptr [shl32arg1_4+2], shl32arg1_2copy+6 - shl32copied
else
mov dword ptr [shl32arg1_1+2], shl32arg1_3copy+6
mov dword ptr [shl32arg1_2+2], shl32arg1_4copy+6
mov dword ptr [shl32arg1_3+2], shl32arg1_1copy+6
mov dword ptr [shl32arg1_4+2], shl32arg1_2copy+6
endif
mov byte ptr [shl32arg1_3+6], 0
mov byte ptr [shl32arg1_4+6], 0
jmp shl32arg1_1
db 8 dup (090h)
ifdef X64
mov dword ptr [shl32arg1_1+2], shl32arg1_4copy+6 - shl32arg1_2
mov dword ptr [shl32arg1_2+2], shl32arg1_1copy+6 - shl32arg1_3
mov dword ptr [shl32arg1_3+2], shl32arg1_2copy+6 - shl32arg1_4
mov dword ptr [shl32arg1_4+2], shl32arg1_3copy+6 - shl32copied
else
mov dword ptr [shl32arg1_1+2], shl32arg1_4copy+6
mov dword ptr [shl32arg1_2+2], shl32arg1_1copy+6
mov dword ptr [shl32arg1_3+2], shl32arg1_2copy+6
mov dword ptr [shl32arg1_4+2], shl32arg1_3copy+6
endif
mov byte ptr [shl32arg1_2+6], 0
mov byte ptr [shl32arg1_3+6], 0
mov byte ptr [shl32arg1_4+6], 0

jmp shl32arg1_1 ; branch after patching code before executing it
shl32arg1_1:: mov byte ptr [shl32arg1_1copy+6], 0
shl32arg1_2:: mov byte ptr [shl32arg1_2copy+6], 0
shl32arg1_3:: mov byte ptr [shl32arg1_3copy+6], 0
shl32arg1_4:: mov byte ptr [shl32arg1_4copy+6], 0
shl32copied:

ifdef X64
mov dword ptr [shl32arg2small + 2], shl32arg2_1copy+6-shl32arg2small-2-4-1
else
mov dword ptr [shl32arg2small + 2], shl32arg2_1copy+6
endif
mov byte ptr [shlargloop + 1], shlarghead3-shlargloop-2
jmp shl32arg2small
shlarghead3: mov byte ptr [shlargloop+1], shlarghead2-shlargloop-2
ifdef X64
mov dword ptr [shl32arg2small + 2], shl32arg2_4copy+6-shl32arg2small-2-4-1
else
mov dword ptr [shl32arg2small + 2], shl32arg2_4copy+6
endif
jmp shl32arg2small
shlarghead2: mov byte ptr [shlargloop+1], shlarghead-shlargloop-2
ifdef X64
mov dword ptr [shl32arg2small + 2], shl32arg2_3copy+6-shl32arg2small-2-4-1
else
mov dword ptr [shl32arg2small + 2], shl32arg2_3copy+6
endif
jmp shl32arg2small
shlarghead: mov byte ptr [shlargloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [shl32arg2small + 2], shl32arg2_2copy+6-shl32arg2small-2-4-1
else
mov dword ptr [shl32arg2small + 2], shl32arg2_2copy+6
endif
jmp shl32arg2small ; branch after patching code before executing it
shl32arg2small:: mov byte ptr [shl32arg2_1copy+6], 0
shlargloop: jmp shlarghead3

SHLBYTE 1,2,32
SHLBYTE 2,3,32
SHLBYTE 3,4,32
SHLBYTE 4,0,32
SHLCARRY 1,2,32
SHLCARRY 2,3,32
SHLCARRY 3,4,32
SHLCARRY 4,0,32

shl32res1:: mov byte ptr [shl32res1+6], 0
shl32res2:: mov byte ptr [shl32res2+6], 0
shl32res3:: mov byte ptr [shl32res3+6], 0
shl32res4:: mov byte ptr [shl32res4+6], 0
shl32ret:: jmp $+80000000h
WriteExecSHL32 ENDP

ifndef X64
WriteExecSHL32_C PROC shl32_1arg: DWORD, shl32_2arg: BYTE
mov ecx, dword ptr [shl32_1arg]
mov dl, byte ptr [shl32_2arg]
else
WriteExecSHL32_C PROC
endif
mov byte ptr [shl32arg1_1+6], cl
mov byte ptr [shl32arg2_1+6], dl
mov byte ptr [shl32arg1_2+6], ch
shr ecx, 16
mov byte ptr [shl32arg1_3+6], cl
mov byte ptr [shl32arg1_4+6], ch
ifdef X64
mov dword ptr [shl32res1+2], shlretval + 1 - shl32res2
mov dword ptr [shl32res2+2], shlretval + 2 - shl32res3
mov dword ptr [shl32res3+2], shlretval + 3 - shl32res4
mov dword ptr [shl32res4+2], shlretval + 4 - shl32ret
else
mov dword ptr [shl32res1+2], shlretval + 1
mov dword ptr [shl32res2+2], shlretval + 2
mov dword ptr [shl32res3+2], shlretval + 3
mov dword ptr [shl32res4+2], shlretval + 4
endif
mov dword ptr [shl32ret+1], shlretval - shl32ret - 5
jmp WriteExecSHL32
shlretval: mov eax, 80000000h
ret
WriteExecSHL32_C ENDP

WriteExecSHL64 PROC
;; shl 5, then shl 3 to split byte vs bits
shl64arg2_1:: mov byte ptr [shlarg1+6], 0
mov byte ptr [shlarg2+2+4], 5
ifdef X64
mov dword ptr [shlbres+2], shlsmall + 2+4 - shlbres2
mov dword ptr [shlbres2+2], shlrounds + 2+4 - shlbret
else
mov dword ptr [shlbres+2], shlsmall + 2+4
mov dword ptr [shlbres2+2], shlrounds + 2+4
endif
mov dword ptr [shlbret+1], shlsmall - shlbret - 5
jmp WriteExecSHL
shlsmall: mov byte ptr [shlarg1+6], 0
mov byte ptr [shlarg2+2+4], 3
ifdef X64
mov dword ptr [shlbres+2], shlsmall + 2+4 - shlbres2
mov dword ptr [shlbres2+2], shl64arg2small + 2+4 - shlbret
else
mov dword ptr [shlbres+2], shlsmall + 2+4
mov dword ptr [shlbres2+2], shl64arg2small + 2+4
endif
mov dword ptr [shlbret+1], shlrounds - shlbret - 5
jmp WriteExecSHL

shlrounds: mov byte ptr [shlarg7+2], 0
ifdef X64
mov dword ptr [shlres7+1+2], shlretval7 + 1 - shlret7
else
mov dword ptr [shlres7+1+2], shlretval7 + 1
endif
mov dword ptr [shlret7+1], shlretval7 - shlret7 - 5
jmp WriteExecSHL7
shlretval7: jmp $+8000h
ifdef X64
mov dword ptr [shl64arg1_1+2], shl64arg1_1copy+6 - shl64arg1_2
mov dword ptr [shl64arg1_2+2], shl64arg1_2copy+6 - shl64arg1_3
mov dword ptr [shl64arg1_3+2], shl64arg1_3copy+6 - shl64arg1_4
mov dword ptr [shl64arg1_4+2], shl64arg1_4copy+6 - shl64arg1_5
mov dword ptr [shl64arg1_5+2], shl64arg1_5copy+6 - shl64arg1_6
mov dword ptr [shl64arg1_6+2], shl64arg1_6copy+6 - shl64arg1_7
mov dword ptr [shl64arg1_7+2], shl64arg1_7copy+6 - shl64arg1_8
mov dword ptr [shl64arg1_8+2], shl64arg1_8copy+6 - shl64copied
else
mov dword ptr [shl64arg1_1+2], shl64arg1_1copy+6
mov dword ptr [shl64arg1_2+2], shl64arg1_2copy+6
mov dword ptr [shl64arg1_3+2], shl64arg1_3copy+6
mov dword ptr [shl64arg1_4+2], shl64arg1_4copy+6
mov dword ptr [shl64arg1_5+2], shl64arg1_5copy+6
mov dword ptr [shl64arg1_6+2], shl64arg1_6copy+6
mov dword ptr [shl64arg1_7+2], shl64arg1_7copy+6
mov dword ptr [shl64arg1_8+2], shl64arg1_8copy+6
endif
jmp shl64arg1_1
db (128-80-5) dup (090h)
ifdef X64
mov dword ptr [shl64arg1_1+2], shl64arg1_2copy+6 - shl64arg1_2
mov dword ptr [shl64arg1_2+2], shl64arg1_3copy+6 - shl64arg1_3
mov dword ptr [shl64arg1_3+2], shl64arg1_4copy+6 - shl64arg1_4
mov dword ptr [shl64arg1_4+2], shl64arg1_5copy+6 - shl64arg1_5
mov dword ptr [shl64arg1_5+2], shl64arg1_6copy+6 - shl64arg1_6
mov dword ptr [shl64arg1_6+2], shl64arg1_7copy+6 - shl64arg1_7
mov dword ptr [shl64arg1_7+2], shl64arg1_8copy+6 - shl64arg1_8
mov dword ptr [shl64arg1_8+2], shl64arg1_1copy+6 - shl64copied
else
mov dword ptr [shl64arg1_1+2], shl64arg1_2copy+6
mov dword ptr [shl64arg1_2+2], shl64arg1_3copy+6
mov dword ptr [shl64arg1_3+2], shl64arg1_4copy+6
mov dword ptr [shl64arg1_4+2], shl64arg1_5copy+6
mov dword ptr [shl64arg1_5+2], shl64arg1_6copy+6
mov dword ptr [shl64arg1_6+2], shl64arg1_7copy+6
mov dword ptr [shl64arg1_7+2], shl64arg1_8copy+6
mov dword ptr [shl64arg1_8+2], shl64arg1_1copy+6
endif
mov byte ptr [shl64arg1_8+6], 0
jmp shl64arg1_1
db (128-80-7-5) dup (090h)
ifdef X64
mov dword ptr [shl64arg1_1+2], shl64arg1_3copy+6 - shl64arg1_2
mov dword ptr [shl64arg1_2+2], shl64arg1_4copy+6 - shl64arg1_3
mov dword ptr [shl64arg1_3+2], shl64arg1_5copy+6 - shl64arg1_4
mov dword ptr [shl64arg1_4+2], shl64arg1_6copy+6 - shl64arg1_5
mov dword ptr [shl64arg1_5+2], shl64arg1_7copy+6 - shl64arg1_6
mov dword ptr [shl64arg1_6+2], shl64arg1_8copy+6 - shl64arg1_7
mov dword ptr [shl64arg1_7+2], shl64arg1_1copy+6 - shl64arg1_8
mov dword ptr [shl64arg1_8+2], shl64arg1_2copy+6 - shl64copied
else
mov dword ptr [shl64arg1_1+2], shl64arg1_3copy+6
mov dword ptr [shl64arg1_2+2], shl64arg1_4copy+6
mov dword ptr [shl64arg1_3+2], shl64arg1_5copy+6
mov dword ptr [shl64arg1_4+2], shl64arg1_6copy+6
mov dword ptr [shl64arg1_5+2], shl64arg1_7copy+6
mov dword ptr [shl64arg1_6+2], shl64arg1_8copy+6
mov dword ptr [shl64arg1_7+2], shl64arg1_1copy+6
mov dword ptr [shl64arg1_8+2], shl64arg1_2copy+6
endif
mov byte ptr [shl64arg1_7+6], 0
mov byte ptr [shl64arg1_8+6], 0
jmp shl64arg1_1
db (128-80-7*2-5) dup (090h)
ifdef X64
mov dword ptr [shl64arg1_1+2], shl64arg1_4copy+6 - shl64arg1_2
mov dword ptr [shl64arg1_2+2], shl64arg1_5copy+6 - shl64arg1_3
mov dword ptr [shl64arg1_3+2], shl64arg1_6copy+6 - shl64arg1_4
mov dword ptr [shl64arg1_4+2], shl64arg1_7copy+6 - shl64arg1_5
mov dword ptr [shl64arg1_5+2], shl64arg1_8copy+6 - shl64arg1_6
mov dword ptr [shl64arg1_6+2], shl64arg1_1copy+6 - shl64arg1_7
mov dword ptr [shl64arg1_7+2], shl64arg1_2copy+6 - shl64arg1_8
mov dword ptr [shl64arg1_8+2], shl64arg1_3copy+6 - shl64copied
else
mov dword ptr [shl64arg1_1+2], shl64arg1_4copy+6
mov dword ptr [shl64arg1_2+2], shl64arg1_5copy+6
mov dword ptr [shl64arg1_3+2], shl64arg1_6copy+6
mov dword ptr [shl64arg1_4+2], shl64arg1_7copy+6
mov dword ptr [shl64arg1_5+2], shl64arg1_8copy+6
mov dword ptr [shl64arg1_6+2], shl64arg1_1copy+6
mov dword ptr [shl64arg1_7+2], shl64arg1_2copy+6
mov dword ptr [shl64arg1_8+2], shl64arg1_3copy+6
endif
mov byte ptr [shl64arg1_6+6], 0
mov byte ptr [shl64arg1_7+6], 0
mov byte ptr [shl64arg1_8+6], 0
jmp shl64arg1_1
db (128-80-7*3-5) dup (090h)
ifdef X64
mov dword ptr [shl64arg1_1+2], shl64arg1_5copy+6 - shl64arg1_2
mov dword ptr [shl64arg1_2+2], shl64arg1_6copy+6 - shl64arg1_3
mov dword ptr [shl64arg1_3+2], shl64arg1_7copy+6 - shl64arg1_4
mov dword ptr [shl64arg1_4+2], shl64arg1_8copy+6 - shl64arg1_5
mov dword ptr [shl64arg1_5+2], shl64arg1_1copy+6 - shl64arg1_6
mov dword ptr [shl64arg1_6+2], shl64arg1_2copy+6 - shl64arg1_7
mov dword ptr [shl64arg1_7+2], shl64arg1_3copy+6 - shl64arg1_8
mov dword ptr [shl64arg1_8+2], shl64arg1_4copy+6 - shl64copied
else
mov dword ptr [shl64arg1_1+2], shl64arg1_5copy+6
mov dword ptr [shl64arg1_2+2], shl64arg1_6copy+6
mov dword ptr [shl64arg1_3+2], shl64arg1_7copy+6
mov dword ptr [shl64arg1_4+2], shl64arg1_8copy+6
mov dword ptr [shl64arg1_5+2], shl64arg1_1copy+6
mov dword ptr [shl64arg1_6+2], shl64arg1_2copy+6
mov dword ptr [shl64arg1_7+2], shl64arg1_3copy+6
mov dword ptr [shl64arg1_8+2], shl64arg1_4copy+6
endif
mov byte ptr [shl64arg1_5+6], 0
mov byte ptr [shl64arg1_6+6], 0
mov byte ptr [shl64arg1_7+6], 0
mov byte ptr [shl64arg1_8+6], 0
jmp shl64arg1_1
db (128-80-7*4-5) dup (090h)
ifdef X64
mov dword ptr [shl64arg1_1+2], shl64arg1_6copy+6 - shl64arg1_2
mov dword ptr [shl64arg1_2+2], shl64arg1_7copy+6 - shl64arg1_3
mov dword ptr [shl64arg1_3+2], shl64arg1_8copy+6 - shl64arg1_4
mov dword ptr [shl64arg1_4+2], shl64arg1_1copy+6 - shl64arg1_5
mov dword ptr [shl64arg1_5+2], shl64arg1_2copy+6 - shl64arg1_6
mov dword ptr [shl64arg1_6+2], shl64arg1_3copy+6 - shl64arg1_7
mov dword ptr [shl64arg1_7+2], shl64arg1_4copy+6 - shl64arg1_8
mov dword ptr [shl64arg1_8+2], shl64arg1_5copy+6 - shl64copied
else
mov dword ptr [shl64arg1_1+2], shl64arg1_6copy+6
mov dword ptr [shl64arg1_2+2], shl64arg1_7copy+6
mov dword ptr [shl64arg1_3+2], shl64arg1_8copy+6
mov dword ptr [shl64arg1_4+2], shl64arg1_1copy+6
mov dword ptr [shl64arg1_5+2], shl64arg1_2copy+6
mov dword ptr [shl64arg1_6+2], shl64arg1_3copy+6
mov dword ptr [shl64arg1_7+2], shl64arg1_4copy+6
mov dword ptr [shl64arg1_8+2], shl64arg1_5copy+6
endif
mov byte ptr [shl64arg1_4+6], 0
mov byte ptr [shl64arg1_5+6], 0
mov byte ptr [shl64arg1_6+6], 0
mov byte ptr [shl64arg1_7+6], 0
mov byte ptr [shl64arg1_8+6], 0
jmp shl64arg1_1
db (128-80-7*5-5) dup (090h)
ifdef X64
mov dword ptr [shl64arg1_1+2], shl64arg1_7copy+6 - shl64arg1_2
mov dword ptr [shl64arg1_2+2], shl64arg1_8copy+6 - shl64arg1_3
mov dword ptr [shl64arg1_3+2], shl64arg1_1copy+6 - shl64arg1_4
mov dword ptr [shl64arg1_4+2], shl64arg1_2copy+6 - shl64arg1_5
mov dword ptr [shl64arg1_5+2], shl64arg1_3copy+6 - shl64arg1_6
mov dword ptr [shl64arg1_6+2], shl64arg1_4copy+6 - shl64arg1_7
mov dword ptr [shl64arg1_7+2], shl64arg1_5copy+6 - shl64arg1_8
mov dword ptr [shl64arg1_8+2], shl64arg1_6copy+6 - shl64copied
else
mov dword ptr [shl64arg1_1+2], shl64arg1_7copy+6
mov dword ptr [shl64arg1_2+2], shl64arg1_8copy+6
mov dword ptr [shl64arg1_3+2], shl64arg1_1copy+6
mov dword ptr [shl64arg1_4+2], shl64arg1_2copy+6
mov dword ptr [shl64arg1_5+2], shl64arg1_3copy+6
mov dword ptr [shl64arg1_6+2], shl64arg1_4copy+6
mov dword ptr [shl64arg1_7+2], shl64arg1_5copy+6
mov dword ptr [shl64arg1_8+2], shl64arg1_6copy+6
endif
mov byte ptr [shl64arg1_3+6], 0
mov byte ptr [shl64arg1_4+6], 0
mov byte ptr [shl64arg1_5+6], 0
mov byte ptr [shl64arg1_6+6], 0
mov byte ptr [shl64arg1_7+6], 0
mov byte ptr [shl64arg1_8+6], 0
jmp shl64arg1_1
db (128-80-7*6-5) dup (090h)
ifdef X64
mov dword ptr [shl64arg1_1+2], shl64arg1_8copy+6 - shl64arg1_2
mov dword ptr [shl64arg1_2+2], shl64arg1_1copy+6 - shl64arg1_3
mov dword ptr [shl64arg1_3+2], shl64arg1_2copy+6 - shl64arg1_4
mov dword ptr [shl64arg1_4+2], shl64arg1_3copy+6 - shl64arg1_5
mov dword ptr [shl64arg1_5+2], shl64arg1_4copy+6 - shl64arg1_6
mov dword ptr [shl64arg1_6+2], shl64arg1_5copy+6 - shl64arg1_7
mov dword ptr [shl64arg1_7+2], shl64arg1_6copy+6 - shl64arg1_8
mov dword ptr [shl64arg1_8+2], shl64arg1_7copy+6 - shl64copied
else
mov dword ptr [shl64arg1_1+2], shl64arg1_8copy+6
mov dword ptr [shl64arg1_2+2], shl64arg1_1copy+6
mov dword ptr [shl64arg1_3+2], shl64arg1_2copy+6
mov dword ptr [shl64arg1_4+2], shl64arg1_3copy+6
mov dword ptr [shl64arg1_5+2], shl64arg1_4copy+6
mov dword ptr [shl64arg1_6+2], shl64arg1_5copy+6
mov dword ptr [shl64arg1_7+2], shl64arg1_6copy+6
mov dword ptr [shl64arg1_8+2], shl64arg1_7copy+6
endif
mov byte ptr [shl64arg1_2+6], 0
mov byte ptr [shl64arg1_3+6], 0
mov byte ptr [shl64arg1_4+6], 0
mov byte ptr [shl64arg1_5+6], 0
mov byte ptr [shl64arg1_6+6], 0
mov byte ptr [shl64arg1_7+6], 0
mov byte ptr [shl64arg1_8+6], 0

jmp shl64arg1_1 ; branch after patching code before executing it
shl64arg1_1:: mov byte ptr [shl64arg1_1copy+6], 0
shl64arg1_2:: mov byte ptr [shl64arg1_2copy+6], 0
shl64arg1_3:: mov byte ptr [shl64arg1_3copy+6], 0
shl64arg1_4:: mov byte ptr [shl64arg1_4copy+6], 0
shl64arg1_5:: mov byte ptr [shl64arg1_5copy+6], 0
shl64arg1_6:: mov byte ptr [shl64arg1_6copy+6], 0
shl64arg1_7:: mov byte ptr [shl64arg1_7copy+6], 0
shl64arg1_8:: mov byte ptr [shl64arg1_8copy+6], 0
shl64copied:

ifdef X64
mov dword ptr [shl64arg2small + 2], shl64arg2_1copy+6-shl64arg2small-2-4-1
else
mov dword ptr [shl64arg2small + 2], shl64arg2_1copy+6
endif
mov dword ptr [shlargloop + 1], shlarghead7-shlargloop-5
jmp shl64arg2small
shlarghead7: mov dword ptr [shlargloop+1], shlarghead6-shlargloop-5
ifdef X64
mov dword ptr [shl64arg2small + 2], shl64arg2_8copy+6-shl64arg2small-2-4-1
else
mov dword ptr [shl64arg2small + 2], shl64arg2_8copy+6
endif
jmp shl64arg2small
shlarghead6: mov dword ptr [shlargloop+1], shlarghead5-shlargloop-5
ifdef X64
mov dword ptr [shl64arg2small + 2], shl64arg2_7copy+6-shl64arg2small-2-4-1
else
mov dword ptr [shl64arg2small + 2], shl64arg2_7copy+6
endif
jmp shl64arg2small
shlarghead5: mov dword ptr [shlargloop+1], shlarghead4-shlargloop-5
ifdef X64
mov dword ptr [shl64arg2small + 2], shl64arg2_6copy+6-shl64arg2small-2-4-1
else
mov dword ptr [shl64arg2small + 2], shl64arg2_6copy+6
endif
jmp shl64arg2small
shlarghead4: mov dword ptr [shlargloop+1], shlarghead3-shlargloop-5
ifdef X64
mov dword ptr [shl64arg2small + 2], shl64arg2_5copy+6-shl64arg2small-2-4-1
else
mov dword ptr [shl64arg2small + 2], shl64arg2_5copy+6
endif
jmp shl64arg2small
shlarghead3: mov dword ptr [shlargloop+1], shlarghead2-shlargloop-5
ifdef X64
mov dword ptr [shl64arg2small + 2], shl64arg2_4copy+6-shl64arg2small-2-4-1
else
mov dword ptr [shl64arg2small + 2], shl64arg2_4copy+6
endif
jmp shl64arg2small
shlarghead2: mov dword ptr [shlargloop+1], shlarghead-shlargloop-5
ifdef X64
mov dword ptr [shl64arg2small + 2], shl64arg2_3copy+6-shl64arg2small-2-4-1
else
mov dword ptr [shl64arg2small + 2], shl64arg2_3copy+6
endif
jmp shl64arg2small
shlarghead: mov dword ptr [shlargloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [shl64arg2small + 2], shl64arg2_2copy+6-shl64arg2small-2-4-1
else
mov dword ptr [shl64arg2small + 2], shl64arg2_2copy+6
endif
jmp shl64arg2small ; branch after patching code before executing it
shl64arg2small:: mov byte ptr [shl64arg2_1copy+6], 0
shlargloop: jmp shlarghead7

SHLBYTE 1,2,64
SHLBYTE 2,3,64
SHLBYTE 3,4,64
SHLBYTE 4,5,64
SHLBYTE 5,6,64
SHLBYTE 6,7,64
SHLBYTE 7,8,64
SHLBYTE 8,0,64
SHLCARRY 1,2,64
SHLCARRY 2,3,64
SHLCARRY 3,4,64
SHLCARRY 4,5,64
SHLCARRY 5,6,64
SHLCARRY 6,7,64
SHLCARRY 7,8,64
SHLCARRY 8,0,64

shl64res1:: mov byte ptr [shl64res1+6], 0
shl64res2:: mov byte ptr [shl64res2+6], 0
shl64res3:: mov byte ptr [shl64res3+6], 0
shl64res4:: mov byte ptr [shl64res4+6], 0
shl64res5:: mov byte ptr [shl64res5+6], 0
shl64res6:: mov byte ptr [shl64res6+6], 0
shl64res7:: mov byte ptr [shl64res7+6], 0
shl64res8:: mov byte ptr [shl64res8+6], 0
shl64ret:: jmp $+80000000h
WriteExecSHL64 ENDP

ifndef X64
gcx TEXTEQU <ecx>
WriteExecSHL64_C PROC shl64_1arg: QWORD, shl64_2arg: BYTE
mov ecx, dword ptr [shl64_1arg]
mov dl, byte ptr [shl64_2arg]
else
gcx TEXTEQU <rcx>
WriteExecSHL64_C PROC
endif
mov byte ptr [shl64arg1_1+6], cl
mov byte ptr [shl64arg2_1+6], dl
mov byte ptr [shl64arg1_2+6], ch
shr gcx, 16
mov byte ptr [shl64arg1_3+6], cl
mov byte ptr [shl64arg1_4+6], ch
ifndef X64
mov ecx, dword ptr [shl64_1arg+4]
else
shr gcx, 16
endif
mov byte ptr [shl64arg1_5+6], cl
mov byte ptr [shl64arg1_6+6], ch
shr gcx, 16
mov byte ptr [shl64arg1_7+6], cl
mov byte ptr [shl64arg1_8+6], ch
ifdef X64
mov dword ptr [shl64res1+2], shlretval + 2 - shl64res2
mov dword ptr [shl64res2+2], shlretval + 3 - shl64res3
mov dword ptr [shl64res3+2], shlretval + 4 - shl64res4
mov dword ptr [shl64res4+2], shlretval + 5 - shl64res5
mov dword ptr [shl64res5+2], shlretval + 6 - shl64res6
mov dword ptr [shl64res6+2], shlretval + 7 - shl64res7
mov dword ptr [shl64res7+2], shlretval + 8 - shl64res8
mov dword ptr [shl64res8+2], shlretval + 9 - shl64ret
else
mov dword ptr [shl64res1+2], shlretval + 1
mov dword ptr [shl64res2+2], shlretval + 2
mov dword ptr [shl64res3+2], shlretval + 3
mov dword ptr [shl64res4+2], shlretval + 4
mov dword ptr [shl64res5+2], shlretval2 + 1
mov dword ptr [shl64res6+2], shlretval2 + 2
mov dword ptr [shl64res7+2], shlretval2 + 3
mov dword ptr [shl64res8+2], shlretval2 + 4
endif
mov dword ptr [shl64ret+1], shlretval - shl64ret - 5
jmp WriteExecSHL64
ifndef X64
shlretval: mov eax, 80000000h
shlretval2: mov edx, 80000000h
else
shlretval: mov rax, 80000000h
endif
ret
WriteExecSHL64_C ENDP

DEFINESHRGEN macro Orig, Index, Lbl, Lbl2
	shr&Orig&_&Index&: mov byte ptr [Lbl+6], (Index shl (8-Orig)) and 0ffh
	mov byte ptr [Lbl2+6], Index shr Orig
	jmp [Lbl]
IF Index EQ 0ffh
	dt 820 dup (090909090909090909090h)
	;;db 8192+32-5-($-shr&Orig&_&Index&) dup (090h) ;; nop
ELSE
	db 13 dup (090h)
	;;db 32-($-shr&Orig&_&Index&) dup (090h) ;; nop
ENDIF
endm

DEFINESHRGRP macro Index, Lbl, Lbl2
shrarg2_&Index&: jmp shr&Index&_0+08000h
IRP ct_value, <0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63>
	DEFINESHRGEN Index, %ct_value, Lbl, Lbl2
ENDM
IRP ct_value, <64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127>
	DEFINESHRGEN Index, %ct_value, Lbl, Lbl2
ENDM
IRP ct_value, <128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191>
	DEFINESHRGEN Index, %ct_value, Lbl, Lbl2
ENDM
IRP ct_value, <192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255>
	DEFINESHRGEN Index, %ct_value, Lbl, Lbl2
ENDM
endm

DEFINESHRJMP macro Index
	mov dword ptr [shrargshl1+1+2], shrarg2_&Index&+1
	jmp shrargshl1
	;; extra padding is wasteful but otherwise would need a shl 4, not just the shl 5
IF Index GT 5
	db 32+20 dup (090h)
ELSE
	db 32+17 dup (090h)
ENDIF
ENDM

WriteExecSHR PROC
shrarg1:: mov byte ptr [shlarg5+2], 0
ifdef X64
mov dword ptr [shlres5+1+2], shrargshl1 + 1 + 2 + 4 - shlret5
else
mov dword ptr [shlres5+1+2], shrargshl1 + 1 + 2 + 4
endif
mov dword ptr [shlret5+1], shrretval5 - shlret5 - 5
jmp WriteExecSHL5
shrretval5:

shrarg2:: mov byte ptr [shlarg6+2], 0
ifdef X64
mov dword ptr [shlres6+1+2], shrargshl2 + 1 + 2 + 4 - shlret6
else
mov dword ptr [shlres6+1+2], shrargshl2 + 1 + 2 + 4
endif
mov dword ptr [shlret6+1], shrretval6 - shlret6 - 5
jmp WriteExecSHL6
shrretval6:

ifdef X64
mov dword ptr [shrargshl2 + 1+2], shrj+2-shrargshl2-1-2-4-2
else
mov dword ptr [shrargshl2 + 1+2], shrj+2
endif
mov byte ptr [shrloop + 1], shrhead-shrloop-2
jmp shrargshl2
shrhead: mov byte ptr [shrloop+1], 0 ;exit loop
shrargshl2: mov word ptr [shrj+2], 8000h
ifdef X64
mov dword ptr [shrargshl2 + 1+2], shrargshl1+2+2-shrargshl2-1-2-4-2
else
mov dword ptr [shrargshl2 + 1+2], shrargshl1jmp+1
endif
shrloop: jmp shrhead

ifndef X64
shrargshl1jmp: jmp shrargshl1begin+08000h
shrargshl1begin:
idx_value = 0
WHILE idx_value LT 8
	DEFINESHRJMP %idx_value
	idx_value = idx_value + 1
ENDM
endif
shrargshl1: mov word ptr [shrarg2_0+1], 8000h

shrj: jmp shrarg2_0+0800000h
idx_value = 0
WHILE idx_value LT 8
	DEFINESHRGRP %idx_value, shrbres, shrbres2
	idx_value = idx_value + 1
ENDM
shrbres:: mov byte ptr [shrbres+6], 0
shrbres2:: mov byte ptr [shrbres2+6], 0
shrbret:: jmp $+80000000h
WriteExecSHR ENDP

ifndef X64
WriteExecSHR_C PROC shr1arg: BYTE, shr2arg: BYTE
mov cl, byte ptr [shr1arg]
mov dl, byte ptr [shr2arg]
else
WriteExecSHR_C PROC
endif
mov byte ptr [shrarg1+2+4], cl
mov byte ptr [shrarg2+2+4], dl
ifdef X64
mov dword ptr [shrbres+2], shrretval + 1+1 - shrbres2
mov dword ptr [shrbres2+2], shrretval + 1+2 - shrbret
else
mov dword ptr [shrbres+2], shrretval + 1+1
mov dword ptr [shrbres2+2], shrretval + 1+2
endif
mov dword ptr [shrbret+1], shrretval - shrbret - 5
jmp WriteExecSHR
shrretval: mov ax, 8000h
ret
WriteExecSHR_C ENDP

SHRBYTE macro Idx, NxtIdx, PrevIdx, Sz
shr&Sz&arg1_&Idx&copy: mov byte ptr [shrarg1+6], 0
shr&Sz&arg2_&Idx&copy: mov byte ptr [shrarg2+6], 0
ifdef X64
mov dword ptr [shrbres+2], carry&PrevIdx& + 2+4 - shrbres2
IF NxtIdx EQ 0
mov dword ptr [shrbres2+2], shr&Sz&res&Idx& + 2+4 - shrbret
ELSE
mov dword ptr [shrbres2+2], shr&Sz&res1_&Idx& + 2+4 - shrbret
ENDIF
else
mov dword ptr [shrbres+2], carry&PrevIdx& + 2+4
IF NxtIdx EQ 0
mov dword ptr [shrbres2+2], shr&Sz&res&Idx& + 2+4
ELSE
mov dword ptr [shrbres2+2], shr&Sz&res1_&Idx& + 2+4
ENDIF
endif
IF NxtIdx EQ 0
mov dword ptr [shrbret+1], carry1 - shrbret - 5
ELSE
mov dword ptr [shrbret+1], shr&Sz&arg1_&NxtIdx&copy - shrbret - 5
ENDIF
jmp WriteExecSHR
ENDM

SHRCARRY macro Idx, NxtIdx, Sz
IF NxtIdx EQ 0
carry&Idx&: mov byte ptr [carry&Idx&+6], 0
ELSE
carry&Idx&: mov byte ptr [xorarg1+6], 0
shr&Sz&res1_&Idx&: mov byte ptr [xorarg2+6], 0
ifdef X64
mov dword ptr [xorres+2], shr&Sz&res&Idx& + 2+4 - xorret
else
mov dword ptr [xorres+2], shr&Sz&res&Idx& + 2+4
endif
mov dword ptr [xorret+1], carry&NxtIdx& - xorret - 5
jmp WriteExecXOR
ENDIF
ENDM

WriteExecSHR32 PROC
;; shl 5, then shl 3 to split byte vs bits
shr32arg2_1:: mov byte ptr [shlarg1+6], 0
mov byte ptr [shlarg2+2+4], 5
ifdef X64
mov dword ptr [shlbres+2], shrsmall + 2+4 - shlbres2
mov dword ptr [shlbres2+2], shrrounds + 2+4 - shlbret
else
mov dword ptr [shlbres+2], shrsmall + 2+4
mov dword ptr [shlbres2+2], shrrounds + 2+4
endif
mov dword ptr [shlbret+1], shrsmall - shlbret - 5
jmp WriteExecSHL
shrsmall: mov byte ptr [shlarg1+6], 0
mov byte ptr [shlarg2+2+4], 3
ifdef X64
mov dword ptr [shlbres+2], shrsmall + 2+4 - shlbres2
mov dword ptr [shlbres2+2], shr32arg2small + 2+4 - shlbret
else
mov dword ptr [shlbres+2], shrsmall + 2+4
mov dword ptr [shlbres2+2], shr32arg2small + 2+4
endif
mov dword ptr [shlbret+1], shrrounds - shlbret - 5
jmp WriteExecSHL

shrrounds: mov byte ptr [shlarg6+2], 0
ifdef X64
mov dword ptr [shlres6+1+2], shlretval6 + 1 - shlret6
else
mov dword ptr [shlres6+1+2], shlretval6 + 1
endif
mov dword ptr [shlret6+1], shlretval6 - shlret6 - 5
jmp WriteExecSHL6
shlretval6: jmp $+8000h
ifdef X64
mov dword ptr [shr32arg1_1+2], shr32arg1_1copy+6 - shr32arg1_2
mov dword ptr [shr32arg1_2+2], shr32arg1_2copy+6 - shr32arg1_3
mov dword ptr [shr32arg1_3+2], shr32arg1_3copy+6 - shr32arg1_4
mov dword ptr [shr32arg1_4+2], shr32arg1_4copy+6 - shr32copied
else
mov dword ptr [shr32arg1_1+2], shr32arg1_1copy+6
mov dword ptr [shr32arg1_2+2], shr32arg1_2copy+6
mov dword ptr [shr32arg1_3+2], shr32arg1_3copy+6
mov dword ptr [shr32arg1_4+2], shr32arg1_4copy+6
endif
jmp shr32arg1_1
db 19 dup (090h)
ifdef X64
mov dword ptr [shr32arg1_1+2], shr32arg1_4copy+6 - shr32arg1_2
mov dword ptr [shr32arg1_2+2], shr32arg1_1copy+6 - shr32arg1_3
mov dword ptr [shr32arg1_3+2], shr32arg1_2copy+6 - shr32arg1_4
mov dword ptr [shr32arg1_4+2], shr32arg1_3copy+6 - shr32copied
else
mov dword ptr [shr32arg1_1+2], shr32arg1_4copy+6
mov dword ptr [shr32arg1_2+2], shr32arg1_1copy+6
mov dword ptr [shr32arg1_3+2], shr32arg1_2copy+6
mov dword ptr [shr32arg1_4+2], shr32arg1_3copy+6
endif
mov byte ptr [shr32arg1_1+6], 0
jmp shr32arg1_1
db 12 dup (090h)
ifdef X64
mov dword ptr [shr32arg1_1+2], shr32arg1_3copy+6 - shr32arg1_2
mov dword ptr [shr32arg1_2+2], shr32arg1_4copy+6 - shr32arg1_3
mov dword ptr [shr32arg1_3+2], shr32arg1_1copy+6 - shr32arg1_4
mov dword ptr [shr32arg1_4+2], shr32arg1_2copy+6 - shr32copied
else
mov dword ptr [shr32arg1_1+2], shr32arg1_3copy+6
mov dword ptr [shr32arg1_2+2], shr32arg1_4copy+6
mov dword ptr [shr32arg1_3+2], shr32arg1_1copy+6
mov dword ptr [shr32arg1_4+2], shr32arg1_2copy+6
endif
mov byte ptr [shr32arg1_1+6], 0
mov byte ptr [shr32arg1_2+6], 0
jmp shr32arg1_1
db 8 dup (090h)
ifdef X64
mov dword ptr [shr32arg1_1+2], shr32arg1_2copy+6 - shr32arg1_2
mov dword ptr [shr32arg1_2+2], shr32arg1_3copy+6 - shr32arg1_3
mov dword ptr [shr32arg1_3+2], shr32arg1_4copy+6 - shr32arg1_4
mov dword ptr [shr32arg1_4+2], shr32arg1_1copy+6 - shr32copied
else
mov dword ptr [shr32arg1_1+2], shr32arg1_2copy+6
mov dword ptr [shr32arg1_2+2], shr32arg1_3copy+6
mov dword ptr [shr32arg1_3+2], shr32arg1_4copy+6
mov dword ptr [shr32arg1_4+2], shr32arg1_1copy+6
endif
mov byte ptr [shr32arg1_1+6], 0
mov byte ptr [shr32arg1_2+6], 0
mov byte ptr [shr32arg1_3+6], 0

jmp shr32arg1_1 ; branch after patching code before executing it
shr32arg1_1:: mov byte ptr [shr32arg1_1copy+6], 0
shr32arg1_2:: mov byte ptr [shr32arg1_2copy+6], 0
shr32arg1_3:: mov byte ptr [shr32arg1_3copy+6], 0
shr32arg1_4:: mov byte ptr [shr32arg1_4copy+6], 0
shr32copied:

ifdef X64
mov dword ptr [shr32arg2small + 2], shr32arg2_1copy+6-shr32arg2small-2-4-1
else
mov dword ptr [shr32arg2small + 2], shr32arg2_1copy+6
endif
mov byte ptr [shrargloop + 1], shrarghead3-shrargloop-2
jmp shr32arg2small
shrarghead3: mov byte ptr [shrargloop+1], shrarghead2-shrargloop-2
ifdef X64
mov dword ptr [shr32arg2small + 2], shr32arg2_4copy+6-shr32arg2small-2-4-1
else
mov dword ptr [shr32arg2small + 2], shr32arg2_4copy+6
endif
jmp shr32arg2small
shrarghead2: mov byte ptr [shrargloop+1], shrarghead-shrargloop-2
ifdef X64
mov dword ptr [shr32arg2small + 2], shr32arg2_3copy+6-shr32arg2small-2-4-1
else
mov dword ptr [shr32arg2small + 2], shr32arg2_3copy+6
endif
jmp shr32arg2small
shrarghead: mov byte ptr [shrargloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [shr32arg2small + 2], shr32arg2_2copy+6-shr32arg2small-2-4-1
else
mov dword ptr [shr32arg2small + 2], shr32arg2_2copy+6
endif
jmp shr32arg2small ; branch after patching code before executing it
shr32arg2small:: mov byte ptr [shr32arg2_1copy+6], 0
shrargloop: jmp shrarghead3

SHRBYTE 1,2,4,32
SHRBYTE 2,3,1,32
SHRBYTE 3,4,2,32
SHRBYTE 4,0,3,32
SHRCARRY 1,2,32
SHRCARRY 2,3,32
SHRCARRY 3,4,32
SHRCARRY 4,0,32

shr32res1:: mov byte ptr [shr32res1+6], 0
shr32res2:: mov byte ptr [shr32res2+6], 0
shr32res3:: mov byte ptr [shr32res3+6], 0
shr32res4:: mov byte ptr [shr32res4+6], 0
shr32ret:: jmp $+80000000h
WriteExecSHR32 ENDP

ifndef X64
WriteExecSHR32_C PROC shr32_1arg: DWORD, shr32_2arg: BYTE
mov ecx, dword ptr [shr32_1arg]
mov dl, byte ptr [shr32_2arg]
else
WriteExecSHR32_C PROC
endif
mov byte ptr [shr32arg1_1+6], cl
mov byte ptr [shr32arg2_1+6], dl
mov byte ptr [shr32arg1_2+6], ch
shr ecx, 16
mov byte ptr [shr32arg1_3+6], cl
mov byte ptr [shr32arg1_4+6], ch
ifdef X64
mov dword ptr [shr32res1+2], shrretval + 1 - shr32res2
mov dword ptr [shr32res2+2], shrretval + 2 - shr32res3
mov dword ptr [shr32res3+2], shrretval + 3 - shr32res4
mov dword ptr [shr32res4+2], shrretval + 4 - shr32ret
else
mov dword ptr [shr32res1+2], shrretval + 1
mov dword ptr [shr32res2+2], shrretval + 2
mov dword ptr [shr32res3+2], shrretval + 3
mov dword ptr [shr32res4+2], shrretval + 4
endif
mov dword ptr [shr32ret+1], shrretval - shr32ret - 5
jmp WriteExecSHR32
shrretval: mov eax, 80000000h
ret
WriteExecSHR32_C ENDP

WriteExecSHR64 PROC
;; shl 5, then shl 3 to split byte vs bits
shr64arg2_1:: mov byte ptr [shlarg1+6], 0
mov byte ptr [shlarg2+2+4], 5
ifdef X64
mov dword ptr [shlbres+2], shrsmall + 2+4 - shlbres2
mov dword ptr [shlbres2+2], shrrounds + 2+4 - shlbret
else
mov dword ptr [shlbres+2], shrsmall + 2+4
mov dword ptr [shlbres2+2], shrrounds + 2+4
endif
mov dword ptr [shlbret+1], shrsmall - shlbret - 5
jmp WriteExecSHL
shrsmall: mov byte ptr [shlarg1+6], 0
mov byte ptr [shlarg2+2+4], 3
ifdef X64
mov dword ptr [shlbres+2], shrsmall + 2+4 - shlbres2
mov dword ptr [shlbres2+2], shr64arg2small + 2+4 - shlbret
else
mov dword ptr [shlbres+2], shrsmall + 2+4
mov dword ptr [shlbres2+2], shr64arg2small + 2+4
endif
mov dword ptr [shlbret+1], shrrounds - shlbret - 5
jmp WriteExecSHL

shrrounds: mov byte ptr [shlarg7+2], 0
ifdef X64
mov dword ptr [shlres7+1+2], shlretval7 + 1 - shlret7
else
mov dword ptr [shlres7+1+2], shlretval7 + 1
endif
mov dword ptr [shlret7+1], shlretval7 - shlret7 - 5
jmp WriteExecSHL7
shlretval7: jmp $+8000h
ifdef X64
mov dword ptr [shr64arg1_1+2], shr64arg1_1copy+6 - shr64arg1_2
mov dword ptr [shr64arg1_2+2], shr64arg1_2copy+6 - shr64arg1_3
mov dword ptr [shr64arg1_3+2], shr64arg1_3copy+6 - shr64arg1_4
mov dword ptr [shr64arg1_4+2], shr64arg1_4copy+6 - shr64arg1_5
mov dword ptr [shr64arg1_5+2], shr64arg1_5copy+6 - shr64arg1_6
mov dword ptr [shr64arg1_6+2], shr64arg1_6copy+6 - shr64arg1_7
mov dword ptr [shr64arg1_7+2], shr64arg1_7copy+6 - shr64arg1_8
mov dword ptr [shr64arg1_8+2], shr64arg1_8copy+6 - shr64copied
else
mov dword ptr [shr64arg1_1+2], shr64arg1_1copy+6
mov dword ptr [shr64arg1_2+2], shr64arg1_2copy+6
mov dword ptr [shr64arg1_3+2], shr64arg1_3copy+6
mov dword ptr [shr64arg1_4+2], shr64arg1_4copy+6
mov dword ptr [shr64arg1_5+2], shr64arg1_5copy+6
mov dword ptr [shr64arg1_6+2], shr64arg1_6copy+6
mov dword ptr [shr64arg1_7+2], shr64arg1_7copy+6
mov dword ptr [shr64arg1_8+2], shr64arg1_8copy+6
endif
jmp shr64arg1_1
db (128-80-5) dup (090h)
ifdef X64
mov dword ptr [shr64arg1_1+2], shr64arg1_8copy+6 - shr64arg1_2
mov dword ptr [shr64arg1_2+2], shr64arg1_1copy+6 - shr64arg1_3
mov dword ptr [shr64arg1_3+2], shr64arg1_2copy+6 - shr64arg1_4
mov dword ptr [shr64arg1_4+2], shr64arg1_3copy+6 - shr64arg1_5
mov dword ptr [shr64arg1_5+2], shr64arg1_4copy+6 - shr64arg1_6
mov dword ptr [shr64arg1_6+2], shr64arg1_5copy+6 - shr64arg1_7
mov dword ptr [shr64arg1_7+2], shr64arg1_6copy+6 - shr64arg1_8
mov dword ptr [shr64arg1_8+2], shr64arg1_7copy+6 - shr64copied
else
mov dword ptr [shr64arg1_1+2], shr64arg1_8copy+6
mov dword ptr [shr64arg1_2+2], shr64arg1_1copy+6
mov dword ptr [shr64arg1_3+2], shr64arg1_2copy+6
mov dword ptr [shr64arg1_4+2], shr64arg1_3copy+6
mov dword ptr [shr64arg1_5+2], shr64arg1_4copy+6
mov dword ptr [shr64arg1_6+2], shr64arg1_5copy+6
mov dword ptr [shr64arg1_7+2], shr64arg1_6copy+6
mov dword ptr [shr64arg1_8+2], shr64arg1_7copy+6
endif
mov byte ptr [shr64arg1_1+6], 0
jmp shr64arg1_1
db (128-80-7-5) dup (090h)
ifdef X64
mov dword ptr [shr64arg1_1+2], shr64arg1_7copy+6 - shr64arg1_2
mov dword ptr [shr64arg1_2+2], shr64arg1_8copy+6 - shr64arg1_3
mov dword ptr [shr64arg1_3+2], shr64arg1_1copy+6 - shr64arg1_4
mov dword ptr [shr64arg1_4+2], shr64arg1_2copy+6 - shr64arg1_5
mov dword ptr [shr64arg1_5+2], shr64arg1_3copy+6 - shr64arg1_6
mov dword ptr [shr64arg1_6+2], shr64arg1_4copy+6 - shr64arg1_7
mov dword ptr [shr64arg1_7+2], shr64arg1_5copy+6 - shr64arg1_8
mov dword ptr [shr64arg1_8+2], shr64arg1_6copy+6 - shr64copied
else
mov dword ptr [shr64arg1_1+2], shr64arg1_7copy+6
mov dword ptr [shr64arg1_2+2], shr64arg1_8copy+6
mov dword ptr [shr64arg1_3+2], shr64arg1_1copy+6
mov dword ptr [shr64arg1_4+2], shr64arg1_2copy+6
mov dword ptr [shr64arg1_5+2], shr64arg1_3copy+6
mov dword ptr [shr64arg1_6+2], shr64arg1_4copy+6
mov dword ptr [shr64arg1_7+2], shr64arg1_5copy+6
mov dword ptr [shr64arg1_8+2], shr64arg1_6copy+6
endif
mov byte ptr [shr64arg1_1+6], 0
mov byte ptr [shr64arg1_2+6], 0
jmp shr64arg1_1
db (128-80-7*2-5) dup (090h)
ifdef X64
mov dword ptr [shr64arg1_1+2], shr64arg1_6copy+6 - shr64arg1_2
mov dword ptr [shr64arg1_2+2], shr64arg1_7copy+6 - shr64arg1_3
mov dword ptr [shr64arg1_3+2], shr64arg1_8copy+6 - shr64arg1_4
mov dword ptr [shr64arg1_4+2], shr64arg1_1copy+6 - shr64arg1_5
mov dword ptr [shr64arg1_5+2], shr64arg1_2copy+6 - shr64arg1_6
mov dword ptr [shr64arg1_6+2], shr64arg1_3copy+6 - shr64arg1_7
mov dword ptr [shr64arg1_7+2], shr64arg1_4copy+6 - shr64arg1_8
mov dword ptr [shr64arg1_8+2], shr64arg1_5copy+6 - shr64copied
else
mov dword ptr [shr64arg1_1+2], shr64arg1_6copy+6
mov dword ptr [shr64arg1_2+2], shr64arg1_7copy+6
mov dword ptr [shr64arg1_3+2], shr64arg1_8copy+6
mov dword ptr [shr64arg1_4+2], shr64arg1_1copy+6
mov dword ptr [shr64arg1_5+2], shr64arg1_2copy+6
mov dword ptr [shr64arg1_6+2], shr64arg1_3copy+6
mov dword ptr [shr64arg1_7+2], shr64arg1_4copy+6
mov dword ptr [shr64arg1_8+2], shr64arg1_5copy+6
endif
mov byte ptr [shr64arg1_1+6], 0
mov byte ptr [shr64arg1_2+6], 0
mov byte ptr [shr64arg1_3+6], 0
jmp shr64arg1_1
db (128-80-7*3-5) dup (090h)
ifdef X64
mov dword ptr [shr64arg1_1+2], shr64arg1_5copy+6 - shr64arg1_2
mov dword ptr [shr64arg1_2+2], shr64arg1_6copy+6 - shr64arg1_3
mov dword ptr [shr64arg1_3+2], shr64arg1_7copy+6 - shr64arg1_4
mov dword ptr [shr64arg1_4+2], shr64arg1_8copy+6 - shr64arg1_5
mov dword ptr [shr64arg1_5+2], shr64arg1_1copy+6 - shr64arg1_6
mov dword ptr [shr64arg1_6+2], shr64arg1_2copy+6 - shr64arg1_7
mov dword ptr [shr64arg1_7+2], shr64arg1_3copy+6 - shr64arg1_8
mov dword ptr [shr64arg1_8+2], shr64arg1_4copy+6 - shr64copied
else
mov dword ptr [shr64arg1_1+2], shr64arg1_5copy+6
mov dword ptr [shr64arg1_2+2], shr64arg1_6copy+6
mov dword ptr [shr64arg1_3+2], shr64arg1_7copy+6
mov dword ptr [shr64arg1_4+2], shr64arg1_8copy+6
mov dword ptr [shr64arg1_5+2], shr64arg1_1copy+6
mov dword ptr [shr64arg1_6+2], shr64arg1_2copy+6
mov dword ptr [shr64arg1_7+2], shr64arg1_3copy+6
mov dword ptr [shr64arg1_8+2], shr64arg1_4copy+6
endif
mov byte ptr [shr64arg1_1+6], 0
mov byte ptr [shr64arg1_2+6], 0
mov byte ptr [shr64arg1_3+6], 0
mov byte ptr [shr64arg1_4+6], 0
jmp shr64arg1_1
db (128-80-7*4-5) dup (090h)
ifdef X64
mov dword ptr [shr64arg1_1+2], shr64arg1_4copy+6 - shr64arg1_2
mov dword ptr [shr64arg1_2+2], shr64arg1_5copy+6 - shr64arg1_3
mov dword ptr [shr64arg1_3+2], shr64arg1_6copy+6 - shr64arg1_4
mov dword ptr [shr64arg1_4+2], shr64arg1_7copy+6 - shr64arg1_5
mov dword ptr [shr64arg1_5+2], shr64arg1_8copy+6 - shr64arg1_6
mov dword ptr [shr64arg1_6+2], shr64arg1_1copy+6 - shr64arg1_7
mov dword ptr [shr64arg1_7+2], shr64arg1_2copy+6 - shr64arg1_8
mov dword ptr [shr64arg1_8+2], shr64arg1_3copy+6 - shr64copied
else
mov dword ptr [shr64arg1_1+2], shr64arg1_4copy+6
mov dword ptr [shr64arg1_2+2], shr64arg1_5copy+6
mov dword ptr [shr64arg1_3+2], shr64arg1_6copy+6
mov dword ptr [shr64arg1_4+2], shr64arg1_7copy+6
mov dword ptr [shr64arg1_5+2], shr64arg1_8copy+6
mov dword ptr [shr64arg1_6+2], shr64arg1_1copy+6
mov dword ptr [shr64arg1_7+2], shr64arg1_2copy+6
mov dword ptr [shr64arg1_8+2], shr64arg1_3copy+6
endif
mov byte ptr [shr64arg1_1+6], 0
mov byte ptr [shr64arg1_2+6], 0
mov byte ptr [shr64arg1_3+6], 0
mov byte ptr [shr64arg1_4+6], 0
mov byte ptr [shr64arg1_5+6], 0
jmp shr64arg1_1
db (128-80-7*5-5) dup (090h)
ifdef X64
mov dword ptr [shr64arg1_1+2], shr64arg1_3copy+6 - shr64arg1_2
mov dword ptr [shr64arg1_2+2], shr64arg1_4copy+6 - shr64arg1_3
mov dword ptr [shr64arg1_3+2], shr64arg1_5copy+6 - shr64arg1_4
mov dword ptr [shr64arg1_4+2], shr64arg1_6copy+6 - shr64arg1_5
mov dword ptr [shr64arg1_5+2], shr64arg1_7copy+6 - shr64arg1_6
mov dword ptr [shr64arg1_6+2], shr64arg1_8copy+6 - shr64arg1_7
mov dword ptr [shr64arg1_7+2], shr64arg1_1copy+6 - shr64arg1_8
mov dword ptr [shr64arg1_8+2], shr64arg1_2copy+6 - shr64copied
else
mov dword ptr [shr64arg1_1+2], shr64arg1_3copy+6
mov dword ptr [shr64arg1_2+2], shr64arg1_4copy+6
mov dword ptr [shr64arg1_3+2], shr64arg1_5copy+6
mov dword ptr [shr64arg1_4+2], shr64arg1_6copy+6
mov dword ptr [shr64arg1_5+2], shr64arg1_7copy+6
mov dword ptr [shr64arg1_6+2], shr64arg1_8copy+6
mov dword ptr [shr64arg1_7+2], shr64arg1_1copy+6
mov dword ptr [shr64arg1_8+2], shr64arg1_2copy+6
endif
mov byte ptr [shr64arg1_1+6], 0
mov byte ptr [shr64arg1_2+6], 0
mov byte ptr [shr64arg1_3+6], 0
mov byte ptr [shr64arg1_4+6], 0
mov byte ptr [shr64arg1_5+6], 0
mov byte ptr [shr64arg1_6+6], 0
jmp shr64arg1_1
db (128-80-7*6-5) dup (090h)
ifdef X64
mov dword ptr [shr64arg1_1+2], shr64arg1_2copy+6 - shr64arg1_2
mov dword ptr [shr64arg1_2+2], shr64arg1_3copy+6 - shr64arg1_3
mov dword ptr [shr64arg1_3+2], shr64arg1_4copy+6 - shr64arg1_4
mov dword ptr [shr64arg1_4+2], shr64arg1_5copy+6 - shr64arg1_5
mov dword ptr [shr64arg1_5+2], shr64arg1_6copy+6 - shr64arg1_6
mov dword ptr [shr64arg1_6+2], shr64arg1_7copy+6 - shr64arg1_7
mov dword ptr [shr64arg1_7+2], shr64arg1_8copy+6 - shr64arg1_8
mov dword ptr [shr64arg1_8+2], shr64arg1_1copy+6 - shr64copied
else
mov dword ptr [shr64arg1_1+2], shr64arg1_2copy+6
mov dword ptr [shr64arg1_2+2], shr64arg1_3copy+6
mov dword ptr [shr64arg1_3+2], shr64arg1_4copy+6
mov dword ptr [shr64arg1_4+2], shr64arg1_5copy+6
mov dword ptr [shr64arg1_5+2], shr64arg1_6copy+6
mov dword ptr [shr64arg1_6+2], shr64arg1_7copy+6
mov dword ptr [shr64arg1_7+2], shr64arg1_8copy+6
mov dword ptr [shr64arg1_8+2], shr64arg1_1copy+6
endif
mov byte ptr [shr64arg1_1+6], 0
mov byte ptr [shr64arg1_2+6], 0
mov byte ptr [shr64arg1_3+6], 0
mov byte ptr [shr64arg1_4+6], 0
mov byte ptr [shr64arg1_5+6], 0
mov byte ptr [shr64arg1_6+6], 0
mov byte ptr [shr64arg1_7+6], 0

jmp shr64arg1_1 ; branch after patching code before executing it
shr64arg1_1:: mov byte ptr [shr64arg1_1copy+6], 0
shr64arg1_2:: mov byte ptr [shr64arg1_2copy+6], 0
shr64arg1_3:: mov byte ptr [shr64arg1_3copy+6], 0
shr64arg1_4:: mov byte ptr [shr64arg1_4copy+6], 0
shr64arg1_5:: mov byte ptr [shr64arg1_5copy+6], 0
shr64arg1_6:: mov byte ptr [shr64arg1_6copy+6], 0
shr64arg1_7:: mov byte ptr [shr64arg1_7copy+6], 0
shr64arg1_8:: mov byte ptr [shr64arg1_8copy+6], 0
shr64copied:

ifdef X64
mov dword ptr [shr64arg2small + 2], shr64arg2_1copy+6-shr64arg2small-2-4-1
else
mov dword ptr [shr64arg2small + 2], shr64arg2_1copy+6
endif
mov dword ptr [shrargloop + 1], shrarghead7-shrargloop-5
jmp shr64arg2small
shrarghead7: mov dword ptr [shrargloop+1], shrarghead6-shrargloop-5
ifdef X64
mov dword ptr [shr64arg2small + 2], shr64arg2_8copy+6-shr64arg2small-2-4-1
else
mov dword ptr [shr64arg2small + 2], shr64arg2_8copy+6
endif
jmp shr64arg2small
shrarghead6: mov dword ptr [shrargloop+1], shrarghead5-shrargloop-5
ifdef X64
mov dword ptr [shr64arg2small + 2], shr64arg2_7copy+6-shr64arg2small-2-4-1
else
mov dword ptr [shr64arg2small + 2], shr64arg2_7copy+6
endif
jmp shr64arg2small
shrarghead5: mov dword ptr [shrargloop+1], shrarghead4-shrargloop-5
ifdef X64
mov dword ptr [shr64arg2small + 2], shr64arg2_6copy+6-shr64arg2small-2-4-1
else
mov dword ptr [shr64arg2small + 2], shr64arg2_6copy+6
endif
jmp shr64arg2small
shrarghead4: mov dword ptr [shrargloop+1], shrarghead3-shrargloop-5
ifdef X64
mov dword ptr [shr64arg2small + 2], shr64arg2_5copy+6-shr64arg2small-2-4-1
else
mov dword ptr [shr64arg2small + 2], shr64arg2_5copy+6
endif
jmp shr64arg2small
shrarghead3: mov dword ptr [shrargloop+1], shrarghead2-shrargloop-5
ifdef X64
mov dword ptr [shr64arg2small + 2], shr64arg2_4copy+6-shr64arg2small-2-4-1
else
mov dword ptr [shr64arg2small + 2], shr64arg2_4copy+6
endif
jmp shr64arg2small
shrarghead2: mov dword ptr [shrargloop+1], shrarghead-shrargloop-5
ifdef X64
mov dword ptr [shr64arg2small + 2], shr64arg2_3copy+6-shr64arg2small-2-4-1
else
mov dword ptr [shr64arg2small + 2], shr64arg2_3copy+6
endif
jmp shr64arg2small
shrarghead: mov dword ptr [shrargloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [shr64arg2small + 2], shr64arg2_2copy+6-shr64arg2small-2-4-1
else
mov dword ptr [shr64arg2small + 2], shr64arg2_2copy+6
endif
jmp shr64arg2small ; branch after patching code before executing it
shr64arg2small:: mov byte ptr [shr64arg2_1copy+6], 0
shrargloop: jmp shrarghead7

SHRBYTE 1,2,8,64
SHRBYTE 2,3,1,64
SHRBYTE 3,4,2,64
SHRBYTE 4,5,3,64
SHRBYTE 5,6,4,64
SHRBYTE 6,7,5,64
SHRBYTE 7,8,6,64
SHRBYTE 8,0,7,64
SHRCARRY 1,2,64
SHRCARRY 2,3,64
SHRCARRY 3,4,64
SHRCARRY 4,5,64
SHRCARRY 5,6,64
SHRCARRY 6,7,64
SHRCARRY 7,8,64
SHRCARRY 8,0,64

shr64res1:: mov byte ptr [shr64res1+6], 0
shr64res2:: mov byte ptr [shr64res2+6], 0
shr64res3:: mov byte ptr [shr64res3+6], 0
shr64res4:: mov byte ptr [shr64res4+6], 0
shr64res5:: mov byte ptr [shr64res5+6], 0
shr64res6:: mov byte ptr [shr64res6+6], 0
shr64res7:: mov byte ptr [shr64res7+6], 0
shr64res8:: mov byte ptr [shr64res8+6], 0
shr64ret:: jmp $+80000000h
WriteExecSHR64 ENDP

ifndef X64
WriteExecSHR64_C PROC shr64_1arg: QWORD, shr64_2arg: BYTE
mov ecx, dword ptr [shr64_1arg]
mov dl, byte ptr [shr64_2arg]
else
WriteExecSHR64_C PROC
endif
mov byte ptr [shr64arg1_1+6], cl
mov byte ptr [shr64arg2_1+6], dl
mov byte ptr [shr64arg1_2+6], ch
shr gcx, 16
mov byte ptr [shr64arg1_3+6], cl
mov byte ptr [shr64arg1_4+6], ch
ifndef X64
mov ecx, dword ptr [shr64_1arg+4]
else
shr gcx, 16
endif
mov byte ptr [shr64arg1_5+6], cl
mov byte ptr [shr64arg1_6+6], ch
shr gcx, 16
mov byte ptr [shr64arg1_7+6], cl
mov byte ptr [shr64arg1_8+6], ch
ifdef X64
mov dword ptr [shr64res1+2], shrretval + 2 - shr64res2
mov dword ptr [shr64res2+2], shrretval + 3 - shr64res3
mov dword ptr [shr64res3+2], shrretval + 4 - shr64res4
mov dword ptr [shr64res4+2], shrretval + 5 - shr64res5
mov dword ptr [shr64res5+2], shrretval + 6 - shr64res6
mov dword ptr [shr64res6+2], shrretval + 7 - shr64res7
mov dword ptr [shr64res7+2], shrretval + 8 - shr64res8
mov dword ptr [shr64res8+2], shrretval + 9 - shr64ret
else
mov dword ptr [shr64res1+2], shrretval + 1
mov dword ptr [shr64res2+2], shrretval + 2
mov dword ptr [shr64res3+2], shrretval + 3
mov dword ptr [shr64res4+2], shrretval + 4
mov dword ptr [shr64res5+2], shrretval2 + 1
mov dword ptr [shr64res6+2], shrretval2 + 2
mov dword ptr [shr64res7+2], shrretval2 + 3
mov dword ptr [shr64res8+2], shrretval2 + 4
endif
mov dword ptr [shr64ret+1], shrretval - shr64ret - 5
jmp WriteExecSHR64
ifndef X64
shrretval: mov eax, 80000000h
shrretval2: mov edx, 80000000h
else
shrretval: mov rax, 80000000h
endif
ret
WriteExecSHR64_C ENDP

DEFINEINC macro Index, Lbl, Lbl2
	mov byte ptr [Lbl+6], (Index+1) and 255
	&Lbl&_&Index&: mov byte ptr [Lbl2+6], (Index+1) shr 8
	jmp [Lbl] ;; preprocessor wrongly assumes 10 bytes for jump unfortunately not 2 or 5 bytes
IF Index GT 0fah ;; preprocessor also cannot look at distance to future labels
	db 16 dup (090h)
ELSE
	db 13 dup (090h)
	;;db 16-($-&Lbl&_&Index&) dup (090h) ;; nop
ENDIF
endm

WriteExecINC PROC
incarg:: mov byte ptr [shlarg5+2], 0
ifdef X64
mov dword ptr [shlres5+1+2], incargshl + 1 - shlret5
else
mov dword ptr [shlres5+1+2], incargshl + 1
endif
mov dword ptr [shlret5+1], incargshl - shlret5 - 5
jmp WriteExecSHL5

incargshl: jmp incres_0+08000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINEINC %idx_value, incres, incres2
	idx_value = idx_value + 1
ENDM
incres:: mov byte ptr [incres+6], 0
incres2:: mov byte ptr [incres+6], 0
incret:: jmp $+80000000h
WriteExecINC ENDP

ifndef X64
WriteExecINC_C PROC inc1arg: BYTE
mov cl, byte ptr [inc1arg]
else
WriteExecINC_C PROC
endif
mov byte ptr [incarg+2+4], cl
ifdef X64
mov dword ptr [incres+2], incretval + 1+1 - incres2
mov dword ptr [incres2+2], incretval + 1+2 - incret
else
mov dword ptr [incres+2], incretval + 1+1
mov dword ptr [incres2+2], incretval + 1+2
endif
mov dword ptr [incret+1], incretval - incret - 5
jmp WriteExecINC
incretval: mov ax, 0h
ret
WriteExecINC_C ENDP

DEFINEADD macro Orig, Index
	add&Orig&_&Index&: mov byte ptr [addres+6], (Orig + Index) and 0ffh
	; 1 1 ?    0 1 0    1 0 0
	mov byte ptr [addcry+6], (Orig and 80h and Index and 80h or ((not (Orig + Index)) and 80h) and ((Index and 80h) xor (Orig and 80h))) shr 7;; (Orig + Index) shr 8
	jmp [addres]
IF Index EQ 0ffh
	dt 820 dup (090909090909090909090h)
	;;db 8192+32-5-($-add&Orig&_&Index&) dup (090h) ;; nop
ELSE
	db 13 dup (090h)
	;;db 32-($-add&Orig&_&Index&) dup (090h) ;; nop
ENDIF
endm

DEFINEADDGRP macro Index
addarg1_&Index&: jmp add&Index&_0+08000h
IRP ct_value, <0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63>
	DEFINEADD Index, %ct_value
ENDM
IRP ct_value, <64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127>
	DEFINEADD Index, %ct_value
ENDM
IRP ct_value, <128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191>
	DEFINEADD Index, %ct_value
ENDM
IRP ct_value, <192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255>
	DEFINEADD Index, %ct_value
ENDM
endm

DEFINEADDJMP macro Index
	mov dword ptr [addargshl2+1+2], addarg1_&Index&+1
	jmp addargshl2
	;; extra padding is wasteful but otherwise would need a shl 4, not just the shl 5
IF Index GT 0fdh
	db 52 dup (090h)
ELSE
	db 49 dup (090h)
ENDIF
ENDM

WriteExecADD PROC

addarg1:: mov byte ptr [shlarg6+2], 0
ifdef X64
mov dword ptr [shlres6+1+2], addargshl1 + 1 + 2 + 4 - shlret6
else
mov dword ptr [shlres6+1+2], addargshl1 + 1 + 2 + 4
endif
mov dword ptr [shlret6+1], shlretval6 - shlret6 - 5
jmp WriteExecSHL6
shlretval6:

addarg2:: mov byte ptr [shlarg5+2], 0
ifdef X64
mov dword ptr [shlres5+1+2], addargshl2 + 1 + 2 + 4 - shlret5
else
mov dword ptr [shlres5+1+2], addargshl2 + 1 + 2 + 4
endif
mov dword ptr [shlret5+1], shlretval5 - shlret5 - 5
jmp WriteExecSHL5
shlretval5:

ifdef X64
mov dword ptr [addargshl1 + 1+2], addj+2-addargshl1-1-2-4-2
else
mov dword ptr [addargshl1 + 1+2], addj+2
endif
mov byte ptr [addloop + 1], addhead-addloop-2
jmp addargshl1
addhead: mov byte ptr [addloop+1], 0 ;exit loop
addargshl1: mov word ptr [addj+2], 8000h
ifdef X64
mov dword ptr [addargshl1 + 1+2], addargshl2+2+2-addargshl1-1-2-4-2
else
mov dword ptr [addargshl1 + 1+2], addargshl2jmp+1
endif
addloop: jmp addhead

ifndef X64
addargshl2jmp: jmp addargshl2begin+08000h
addargshl2begin:
idx_value = 0
WHILE idx_value LT 100h
	DEFINEADDJMP %idx_value
	idx_value = idx_value + 1
ENDM
else
endif
addargshl2: mov word ptr [addarg1_0+1], 8000h

addj: jmp addarg1_0+0800000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINEADDGRP %idx_value	
	idx_value = idx_value + 1
ENDM
addres:: mov byte ptr [addres+6], 0
addcry:: mov byte ptr [addcry+6], 0
addret:: jmp $+80000000h
WriteExecADD ENDP

ifndef X64
WriteExecADD_C PROC add1arg: BYTE, add2arg: BYTE
mov cl, byte ptr [add1arg]
mov dl, byte ptr [add2arg]
else
WriteExecADD_C PROC
endif
mov byte ptr [addarg1+6], cl
mov byte ptr [addarg2+6], dl
ifdef X64
mov dword ptr [addres+2], addretval + 1+1 - addcry
mov dword ptr [addcry+2], addretval + 1+2 - addret
else
mov dword ptr [addres+2], addretval + 1+1
mov dword ptr [addcry+2], addretval + 1+2
endif
mov dword ptr [addret+1], addretval - addret - 5
jmp WriteExecADD
addretval: mov ax, 8000h
ret
WriteExecADD_C ENDP

;WriteExecADD Proto
;EXTERNDEF addret:near
;EXTERNDEF addres:near
;EXTERNDEF addcry:near
;EXTERNDEF addarg1:near
;EXTERNDEF addarg2:near

ADDBYTE macro Idx, NxtIdx, LastIdx, Sz
IF Idx EQ 1
add&Sz&arg1_&Idx&:: mov byte ptr [addarg1+6], 0
ELSE
add&Sz&arg1_&Idx&copy: mov byte ptr [addarg1+6], 0
ENDIF
add&Sz&arg2_&Idx&:: mov byte ptr [addarg2+6], 0
ifdef X64
mov dword ptr [addres+2], add&Sz&res&Idx& + 2+4 - addcry
mov dword ptr [addcry+2], carry&Idx& + 2+4 - addret
else
mov dword ptr [addres+2], add&Sz&res&Idx& + 2+4
mov dword ptr [addcry+2], carry&Idx& + 2+4
endif
IF Idx NE LastIdx
mov dword ptr [addret+1], carry&Idx& - addret - 5
ELSE
mov dword ptr [addret+1], add&Sz&res1 - addret - 5
ENDIF
jmp WriteExecADD
IF Idx NE LastIdx
IF NxtIdx EQ LastIdx
carry&LastIdx&:
ENDIF
carry&Idx&: mov byte ptr [shlarg+2], 0
ifdef X64
mov dword ptr [shlres+1+2], carry&Idx&retval + 1 - shlret
else
mov dword ptr [shlres+1+2], carry&Idx&retval + 1
endif
mov dword ptr [shlret+1], carry&Idx&shlret - shlret - 5
jmp WriteExecSHL1
carry&Idx&shlret:
IF Idx NE 1
carry&Idx&_2: mov byte ptr [shlarg+2], 0
ifdef X64
mov dword ptr [shlres+1+2], carry&Idx&_2retval + 1 - shlret
else
mov dword ptr [shlres+1+2], carry&Idx&_2retval + 1
endif
mov dword ptr [shlret+1], carry&Idx&_2shlret - shlret - 5
jmp WriteExecSHL1
carry&Idx&_2shlret:
ENDIF

ifdef X64
mov dword ptr [add&Sz&arg1_&NxtIdx& + 2], add&Sz&arg1_&NxtIdx&copy+6-add&Sz&arg1_&NxtIdx&-2-4-1
else
mov dword ptr [add&Sz&arg1_&NxtIdx& + 2], add&Sz&arg1_&NxtIdx&copy+6
endif
mov byte ptr [addarg&Idx&loop + 1], addarg&Idx&head-addarg&Idx&loop-2
jmp add&Sz&arg1_&NxtIdx&
addarg&Idx&head: mov byte ptr [addarg&Idx&loop+1], 0 ;exit loop
add&Sz&arg1_&NxtIdx&:: mov byte ptr [add&Sz&arg1_&NxtIdx&copy+6], 0
ifdef X64
mov dword ptr [add&Sz&arg1_&NxtIdx& + 2], hascarry&Idx&+6-add&Sz&arg1_&NxtIdx&-2-4-1
else
mov dword ptr [add&Sz&arg1_&NxtIdx& + 2], hascarry&Idx&+6
endif
addarg&Idx&loop: jmp addarg&Idx&head
IF NxtIdx NE LastIdx
mov byte ptr [carry&NxtIdx&_2 + 2 + 4], 0
ENDIF

If Idx NE 1
carry&Idx&_2retval: jmp nocarry&Idx&_2+8000h
nocarry&Idx&_2: jmp carry&Idx&retval
jmp hascarry&Idx&
ENDIF

carry&Idx&retval: jmp nocry&Idx&+8000h
nocry&Idx&: jmp add&Sz&arg1_&NxtIdx&copy
hascarry&Idx&:

mov byte ptr [incarg+2+4], 0
ifdef X64
mov dword ptr [incres+2], add&Sz&arg1_&NxtIdx&copy + 2+4 - incres2
IF NxtIdx EQ LastIdx
mov dword ptr [incres2+2], carry&Idx&_2 + 2+4 - incret
ELSE
mov dword ptr [incres2+2], carry&NxtIdx&_2 + 2+4 - incret
ENDIF
else
mov dword ptr [incres+2], add&Sz&arg1_&NxtIdx&copy + 2+4
IF NxtIdx EQ LastIdx
mov dword ptr [incres2+2], carry&Idx&_2 + 2+4
ELSE
mov dword ptr [incres2+2], carry&NxtIdx&_2 + 2+4
ENDIF
endif
mov dword ptr [incret+1], add&Sz&arg1_&NxtIdx&copy - incret - 5
jmp WriteExecINC
ENDIF
ENDM

WriteExecADD32 PROC
ADDBYTE 1,2,4,32
ADDBYTE 2,3,4,32
ADDBYTE 3,4,4,32
ADDBYTE 4,0,4,32

add32res1:: mov byte ptr [add32res1+6], 0
add32res2:: mov byte ptr [add32res2+6], 0
add32res3:: mov byte ptr [add32res3+6], 0
add32res4:: mov byte ptr [add32res4+6], 0
add32ret:: jmp $+80000000h
WriteExecADD32 ENDP

ifndef X64
WriteExecADD32_C PROC add32_1arg: DWORD, add32_2arg: DWORD
mov ecx, dword ptr [add32_1arg]
mov edx, dword ptr [add32_2arg]
else
WriteExecADD32_C PROC
endif
mov byte ptr [add32arg1_1+6], cl
mov byte ptr [add32arg2_1+6], dl
mov byte ptr [add32arg1_2+6], ch
mov byte ptr [add32arg2_2+6], dh
shr ecx, 16
shr edx, 16
mov byte ptr [add32arg1_3+6], cl
mov byte ptr [add32arg2_3+6], dl
mov byte ptr [add32arg1_4+6], ch
mov byte ptr [add32arg2_4+6], dh
ifdef X64
mov dword ptr [add32res1+2], addretval + 1 - add32res2
mov dword ptr [add32res2+2], addretval + 2 - add32res3
mov dword ptr [add32res3+2], addretval + 3 - add32res4
mov dword ptr [add32res4+2], addretval + 4 - add32ret
else
mov dword ptr [add32res1+2], addretval + 1
mov dword ptr [add32res2+2], addretval + 2
mov dword ptr [add32res3+2], addretval + 3
mov dword ptr [add32res4+2], addretval + 4
endif
mov dword ptr [add32ret+1], addretval - add32ret - 5
jmp WriteExecADD32
addretval: mov eax, 80000000h
ret
WriteExecADD32_C ENDP

WriteExecADD64 PROC
ADDBYTE 1,2,8,64
ADDBYTE 2,3,8,64
ADDBYTE 3,4,8,64
ADDBYTE 4,5,8,64
ADDBYTE 5,6,8,64
ADDBYTE 6,7,8,64
ADDBYTE 7,8,8,64
ADDBYTE 8,0,8,64

add64res1:: mov byte ptr [add64res1+6], 0
add64res2:: mov byte ptr [add64res2+6], 0
add64res3:: mov byte ptr [add64res3+6], 0
add64res4:: mov byte ptr [add64res4+6], 0
add64res5:: mov byte ptr [add64res5+6], 0
add64res6:: mov byte ptr [add64res6+6], 0
add64res7:: mov byte ptr [add64res7+6], 0
add64res8:: mov byte ptr [add64res8+6], 0
add64ret:: jmp $+80000000h
WriteExecADD64 ENDP

ifndef X64
gdx textequ <edx>
WriteExecADD64_C PROC add64_1arg: QWORD, add64_2arg: QWORD
mov ecx, dword ptr [add64_1arg]
mov edx, dword ptr [add64_2arg]
else
gdx textequ <rdx>
WriteExecADD64_C PROC
endif
mov byte ptr [add64arg1_1+6], cl
mov byte ptr [add64arg2_1+6], dl
mov byte ptr [add64arg1_2+6], ch
mov byte ptr [add64arg2_2+6], dh
shr gcx, 16
shr gdx, 16
mov byte ptr [add64arg1_3+6], cl
mov byte ptr [add64arg2_3+6], dl
mov byte ptr [add64arg1_4+6], ch
mov byte ptr [add64arg2_4+6], dh
ifdef X64
shr gcx, 16
shr gdx, 16
else
mov ecx, dword ptr [add64_1arg+4]
mov edx, dword ptr [add64_2arg+4]
endif
mov byte ptr [add64arg1_5+6], cl
mov byte ptr [add64arg2_5+6], dl
mov byte ptr [add64arg1_6+6], ch
mov byte ptr [add64arg2_6+6], dh
shr gcx, 16
shr gdx, 16
mov byte ptr [add64arg1_7+6], cl
mov byte ptr [add64arg2_7+6], dl
mov byte ptr [add64arg1_8+6], ch
mov byte ptr [add64arg2_8+6], dh
ifdef X64
mov dword ptr [add64res1+2], addretval + 2 - add64res2
mov dword ptr [add64res2+2], addretval + 3 - add64res3
mov dword ptr [add64res3+2], addretval + 4 - add64res4
mov dword ptr [add64res4+2], addretval + 5 - add64res5
mov dword ptr [add64res5+2], addretval + 6 - add64res6
mov dword ptr [add64res6+2], addretval + 7 - add64res7
mov dword ptr [add64res7+2], addretval + 8 - add64res8
mov dword ptr [add64res8+2], addretval + 9 - add64ret
else
mov dword ptr [add64res1+2], addretval + 1
mov dword ptr [add64res2+2], addretval + 2
mov dword ptr [add64res3+2], addretval + 3
mov dword ptr [add64res4+2], addretval + 4
mov dword ptr [add64res5+2], addretval2 + 1
mov dword ptr [add64res6+2], addretval2 + 2
mov dword ptr [add64res7+2], addretval2 + 3
mov dword ptr [add64res8+2], addretval2 + 4
endif
mov dword ptr [add64ret+1], addretval - add64ret - 5
jmp WriteExecADD64
ifndef X64
addretval: mov eax, 80000000h
addretval2: mov edx, 80000000h
else
addretval: mov rax, 80000000h
endif
ret
WriteExecADD64_C ENDP

DEFINEDEC macro Index, Lbl, Lbl2
	mov byte ptr [Lbl+6], (Index-1) and 255
	&Lbl&_&Index&: mov byte ptr [Lbl2+6], (Index EQ 0) and 1
	jmp [Lbl] ;; preprocessor wrongly assumes 10 bytes for jump unfortunately not 2 or 5 bytes
IF Index GT 0fah ;; preprocessor also cannot look at distance to future labels
	db 16 dup (090h)
ELSE
	db 13 dup (090h)
	;;db 16-($-&Lbl&_&Index&) dup (090h) ;; nop
ENDIF
endm

WriteExecDEC PROC
decarg:: mov byte ptr [shlarg5+2], 0
ifdef X64
mov dword ptr [shlres5+1+2], decargshl + 1 - shlret5
else
mov dword ptr [shlres5+1+2], decargshl + 1
endif
mov dword ptr [shlret5+1], decargshl - shlret5 - 5
jmp WriteExecSHL5

decargshl: jmp decres_0+08000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINEDEC %idx_value, decres, decres2
	idx_value = idx_value + 1
ENDM
decres:: mov byte ptr [decres+6], 0
decres2:: mov byte ptr [decres+6], 0
decret:: jmp $+80000000h
WriteExecDEC ENDP

ifndef X64
WriteExecDEC_C PROC dec1arg: BYTE
mov cl, byte ptr [dec1arg]
else
WriteExecDEC_C PROC
endif
mov byte ptr [decarg+2+4], cl
ifdef X64
mov dword ptr [decres+2], decretval + 1+1 - decres2
mov dword ptr [decres2+2], decretval + 1+2 - decret
else
mov dword ptr [decres+2], decretval + 1+1
mov dword ptr [decres2+2], decretval + 1+2
endif
mov dword ptr [decret+1], decretval - decret - 5
jmp WriteExecDEC
decretval: mov ax, 0h
ret
WriteExecDEC_C ENDP

DEFINESUB macro Orig, Index
	sub&Orig&_&Index&: mov byte ptr [subres+6], (Orig - Index) and 0ffh
	; 1 1 ?    0 1 0    1 0 0
	mov byte ptr [subcry+6], (Orig LT Index) and 1
	jmp [subres]
IF Index EQ 0ffh
	dt 820 dup (090909090909090909090h)
	;;db 8192+32-5-($-sub&Orig&_&Index&) dup (090h) ;; nop
ELSE
	db 13 dup (090h)
	;;db 32-($-sub&Orig&_&Index&) dup (090h) ;; nop
ENDIF
endm

DEFINESUBGRP macro Index
subarg1_&Index&: jmp sub&Index&_0+08000h
IRP ct_value, <0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63>
	DEFINESUB Index, %ct_value
ENDM
IRP ct_value, <64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127>
	DEFINESUB Index, %ct_value
ENDM
IRP ct_value, <128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191>
	DEFINESUB Index, %ct_value
ENDM
IRP ct_value, <192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255>
	DEFINESUB Index, %ct_value
ENDM
endm

DEFINESUBJMP macro Index
	mov dword ptr [subargshl2+1+2], subarg1_&Index&+1
	jmp subargshl2
	;; extra padding is wasteful but otherwise would need a shl 4, not just the shl 5
IF Index GT 0fdh
	db 52 dup (090h)
ELSE
	db 49 dup (090h)
ENDIF
ENDM

WriteExecSUB PROC

subarg1:: mov byte ptr [shlarg6+2], 0
ifdef X64
mov dword ptr [shlres6+1+2], subargshl1 + 1 + 2 + 4 - shlret6
else
mov dword ptr [shlres6+1+2], subargshl1 + 1 + 2 + 4
endif
mov dword ptr [shlret6+1], shlretval6 - shlret6 - 5
jmp WriteExecSHL6
shlretval6:

subarg2:: mov byte ptr [shlarg5+2], 0
ifdef X64
mov dword ptr [shlres5+1+2], subargshl2 + 1 + 2 + 4 - shlret5
else
mov dword ptr [shlres5+1+2], subargshl2 + 1 + 2 + 4
endif
mov dword ptr [shlret5+1], shlretval5 - shlret5 - 5
jmp WriteExecSHL5
shlretval5:

ifdef X64
mov dword ptr [subargshl1 + 1+2], subj+2-subargshl1-1-2-4-2
else
mov dword ptr [subargshl1 + 1+2], subj+2
endif
mov byte ptr [subloop + 1], subhead-subloop-2
jmp subargshl1
subhead: mov byte ptr [subloop+1], 0 ;exit loop
subargshl1: mov word ptr [subj+2], 8000h
ifdef X64
mov dword ptr [subargshl1 + 1+2], subargshl2+2+2-subargshl1-1-2-4-2
else
mov dword ptr [subargshl1 + 1+2], subargshl2jmp+1
endif
subloop: jmp subhead

ifndef X64
subargshl2jmp: jmp subargshl2begin+08000h
subargshl2begin:
idx_value = 0
WHILE idx_value LT 100h
	DEFINESUBJMP %idx_value
	idx_value = idx_value + 1
ENDM
else
endif
subargshl2: mov word ptr [subarg1_0+1], 8000h

subj: jmp subarg1_0+0800000h
idx_value = 0
WHILE idx_value LT 100h
	DEFINESUBGRP %idx_value	
	idx_value = idx_value + 1
ENDM
subres:: mov byte ptr [subres+6], 0
subcry:: mov byte ptr [subcry+6], 0
subret:: jmp $+80000000h
WriteExecSUB ENDP

ifndef X64
WriteExecSUB_C PROC sub1arg: BYTE, sub2arg: BYTE
mov cl, byte ptr [sub1arg]
mov dl, byte ptr [sub2arg]
else
WriteExecSUB_C PROC
endif
mov byte ptr [subarg1+6], cl
mov byte ptr [subarg2+6], dl
ifdef X64
mov dword ptr [subres+2], subretval + 1+1 - subcry
mov dword ptr [subcry+2], subretval + 1+2 - subret
else
mov dword ptr [subres+2], subretval + 1+1
mov dword ptr [subcry+2], subretval + 1+2
endif
mov dword ptr [subret+1], subretval - subret - 5
jmp WriteExecSUB
subretval: mov ax, 8000h
ret
WriteExecSUB_C ENDP

WriteExecSUB Proto
;EXTERNDEF subret:near
;EXTERNDEF subres:near
;EXTERNDEF subcry:near
;EXTERNDEF subarg1:near
;EXTERNDEF subarg2:near

SUBBYTE macro Idx, NxtIdx, LastIdx, Sz
IF Idx EQ 1
sub&Sz&arg1_&Idx&:: mov byte ptr [subarg1+6], 0
ELSE
sub&Sz&arg1_&Idx&copy: mov byte ptr [subarg1+6], 0
ENDIF
sub&Sz&arg2_&Idx&:: mov byte ptr [subarg2+6], 0
ifdef X64
mov dword ptr [subres+2], sub&Sz&res&Idx& + 2+4 - subcry
mov dword ptr [subcry+2], carry&Idx& + 2+4 - subret
else
mov dword ptr [subres+2], sub&Sz&res&Idx& + 2+4
mov dword ptr [subcry+2], carry&Idx& + 2+4
endif
IF Idx NE LastIdx
mov dword ptr [subret+1], carry&Idx& - subret - 5
ELSE
mov dword ptr [subret+1], sub&Sz&res1 - subret - 5
ENDIF
jmp WriteExecSUB
IF Idx NE LastIdx
IF NxtIdx EQ LastIdx
carry&LastIdx&:
ENDIF
carry&Idx&: mov byte ptr [shlarg+2], 0
ifdef X64
mov dword ptr [shlres+1+2], carry&Idx&retval + 1 - shlret
else
mov dword ptr [shlres+1+2], carry&Idx&retval + 1
endif
mov dword ptr [shlret+1], carry&Idx&shlret - shlret - 5
jmp WriteExecSHL1
carry&Idx&shlret:
IF Idx NE 1
carry&Idx&_2: mov byte ptr [shlarg+2], 0
ifdef X64
mov dword ptr [shlres+1+2], carry&Idx&_2retval + 1 - shlret
else
mov dword ptr [shlres+1+2], carry&Idx&_2retval + 1
endif
mov dword ptr [shlret+1], carry&Idx&_2shlret - shlret - 5
jmp WriteExecSHL1
carry&Idx&_2shlret:
ENDIF

ifdef X64
mov dword ptr [sub&Sz&arg1_&NxtIdx& + 2], sub&Sz&arg1_&NxtIdx&copy+6-sub&Sz&arg1_&NxtIdx&-2-4-1
else
mov dword ptr [sub&Sz&arg1_&NxtIdx& + 2], sub&Sz&arg1_&NxtIdx&copy+6
endif
mov byte ptr [subarg&Idx&loop + 1], subarg&Idx&head-subarg&Idx&loop-2
jmp sub&Sz&arg1_&NxtIdx&
subarg&Idx&head: mov byte ptr [subarg&Idx&loop+1], 0 ;exit loop
sub&Sz&arg1_&NxtIdx&:: mov byte ptr [sub&Sz&arg1_&NxtIdx&copy+6], 0
ifdef X64
mov dword ptr [sub&Sz&arg1_&NxtIdx& + 2], hascarry&Idx&+6-sub&Sz&arg1_&NxtIdx&-2-4-1
else
mov dword ptr [sub&Sz&arg1_&NxtIdx& + 2], hascarry&Idx&+6
endif
subarg&Idx&loop: jmp subarg&Idx&head
IF NxtIdx NE LastIdx
mov byte ptr [carry&NxtIdx&_2 + 2 + 4], 0
ENDIF

If Idx NE 1
carry&Idx&_2retval: jmp nocarry&Idx&_2+8000h
nocarry&Idx&_2: jmp carry&Idx&retval
jmp hascarry&Idx&
ENDIF

carry&Idx&retval: jmp nocry&Idx&+8000h
nocry&Idx&: jmp sub&Sz&arg1_&NxtIdx&copy
hascarry&Idx&:

mov byte ptr [decarg+2+4], 0
ifdef X64
mov dword ptr [decres+2], sub&Sz&arg1_&NxtIdx&copy + 2+4 - decres2
IF NxtIdx EQ LastIdx
mov dword ptr [decres2+2], carry&Idx&_2 + 2+4 - decret
ELSE
mov dword ptr [decres2+2], carry&NxtIdx&_2 + 2+4 - decret
ENDIF
else
mov dword ptr [decres+2], sub&Sz&arg1_&NxtIdx&copy + 2+4
IF NxtIdx EQ LastIdx
mov dword ptr [decres2+2], carry&Idx&_2 + 2+4
ELSE
mov dword ptr [decres2+2], carry&NxtIdx&_2 + 2+4
ENDIF
endif
mov dword ptr [decret+1], sub&Sz&arg1_&NxtIdx&copy - decret - 5
jmp WriteExecDEC
ENDIF
ENDM

WriteExecSUB32 PROC
SUBBYTE 1,2,4,32
SUBBYTE 2,3,4,32
SUBBYTE 3,4,4,32
SUBBYTE 4,0,4,32

sub32res1:: mov byte ptr [sub32res1+6], 0
sub32res2:: mov byte ptr [sub32res2+6], 0
sub32res3:: mov byte ptr [sub32res3+6], 0
sub32res4:: mov byte ptr [sub32res4+6], 0
sub32ret:: jmp $+80000000h
WriteExecSUB32 ENDP

ifndef X64
WriteExecSUB32_C PROC sub32_1arg: DWORD, sub32_2arg: DWORD
mov ecx, dword ptr [sub32_1arg]
mov edx, dword ptr [sub32_2arg]
else
WriteExecSUB32_C PROC
endif
mov byte ptr [sub32arg1_1+6], cl
mov byte ptr [sub32arg2_1+6], dl
mov byte ptr [sub32arg1_2+6], ch
mov byte ptr [sub32arg2_2+6], dh
shr ecx, 16
shr edx, 16
mov byte ptr [sub32arg1_3+6], cl
mov byte ptr [sub32arg2_3+6], dl
mov byte ptr [sub32arg1_4+6], ch
mov byte ptr [sub32arg2_4+6], dh
ifdef X64
mov dword ptr [sub32res1+2], subretval + 1 - sub32res2
mov dword ptr [sub32res2+2], subretval + 2 - sub32res3
mov dword ptr [sub32res3+2], subretval + 3 - sub32res4
mov dword ptr [sub32res4+2], subretval + 4 - sub32ret
else
mov dword ptr [sub32res1+2], subretval + 1
mov dword ptr [sub32res2+2], subretval + 2
mov dword ptr [sub32res3+2], subretval + 3
mov dword ptr [sub32res4+2], subretval + 4
endif
mov dword ptr [sub32ret+1], subretval - sub32ret - 5
jmp WriteExecSUB32
subretval: mov eax, 80000000h
ret
WriteExecSUB32_C ENDP

WriteExecSUB64 PROC
SUBBYTE 1,2,8,64
SUBBYTE 2,3,8,64
SUBBYTE 3,4,8,64
SUBBYTE 4,5,8,64
SUBBYTE 5,6,8,64
SUBBYTE 6,7,8,64
SUBBYTE 7,8,8,64
SUBBYTE 8,0,8,64

sub64res1:: mov byte ptr [sub64res1+6], 0
sub64res2:: mov byte ptr [sub64res2+6], 0
sub64res3:: mov byte ptr [sub64res3+6], 0
sub64res4:: mov byte ptr [sub64res4+6], 0
sub64res5:: mov byte ptr [sub64res5+6], 0
sub64res6:: mov byte ptr [sub64res6+6], 0
sub64res7:: mov byte ptr [sub64res7+6], 0
sub64res8:: mov byte ptr [sub64res8+6], 0
sub64ret:: jmp $+80000000h
WriteExecSUB64 ENDP

ifndef X64
gcx textequ <ecx>
gdx textequ <edx>
WriteExecSUB64_C PROC sub64_1arg: QWORD, sub64_2arg: QWORD
mov ecx, dword ptr [sub64_1arg]
mov edx, dword ptr [sub64_2arg]
else
gcx textequ <rcx>
gdx textequ <rdx>
WriteExecSUB64_C PROC
endif
mov byte ptr [sub64arg1_1+6], cl
mov byte ptr [sub64arg2_1+6], dl
mov byte ptr [sub64arg1_2+6], ch
mov byte ptr [sub64arg2_2+6], dh
shr gcx, 16
shr gdx, 16
mov byte ptr [sub64arg1_3+6], cl
mov byte ptr [sub64arg2_3+6], dl
mov byte ptr [sub64arg1_4+6], ch
mov byte ptr [sub64arg2_4+6], dh
ifdef X64
shr gcx, 16
shr gdx, 16
else
mov ecx, dword ptr [sub64_1arg+4]
mov edx, dword ptr [sub64_2arg+4]
endif
mov byte ptr [sub64arg1_5+6], cl
mov byte ptr [sub64arg2_5+6], dl
mov byte ptr [sub64arg1_6+6], ch
mov byte ptr [sub64arg2_6+6], dh
shr gcx, 16
shr gdx, 16
mov byte ptr [sub64arg1_7+6], cl
mov byte ptr [sub64arg2_7+6], dl
mov byte ptr [sub64arg1_8+6], ch
mov byte ptr [sub64arg2_8+6], dh
ifdef X64
mov dword ptr [sub64res1+2], subretval + 2 - sub64res2
mov dword ptr [sub64res2+2], subretval + 3 - sub64res3
mov dword ptr [sub64res3+2], subretval + 4 - sub64res4
mov dword ptr [sub64res4+2], subretval + 5 - sub64res5
mov dword ptr [sub64res5+2], subretval + 6 - sub64res6
mov dword ptr [sub64res6+2], subretval + 7 - sub64res7
mov dword ptr [sub64res7+2], subretval + 8 - sub64res8
mov dword ptr [sub64res8+2], subretval + 9 - sub64ret
else
mov dword ptr [sub64res1+2], subretval + 1
mov dword ptr [sub64res2+2], subretval + 2
mov dword ptr [sub64res3+2], subretval + 3
mov dword ptr [sub64res4+2], subretval + 4
mov dword ptr [sub64res5+2], subretval2 + 1
mov dword ptr [sub64res6+2], subretval2 + 2
mov dword ptr [sub64res7+2], subretval2 + 3
mov dword ptr [sub64res8+2], subretval2 + 4
endif
mov dword ptr [sub64ret+1], subretval - sub64ret - 5
jmp WriteExecSUB64
ifndef X64
subretval: mov eax, 80000000h
subretval2: mov edx, 80000000h
else
subretval: mov rax, 80000000h
endif
ret
WriteExecSUB64_C ENDP

WriteExecMUL32 PROC
mov byte ptr [mulres1+6], 0
mov byte ptr [mulres2+6], 0
mov byte ptr [mulres3+6], 0
mov byte ptr [mulres4+6], 0
mov byte ptr [mulres5+6], 0
mov byte ptr [mulres6+6], 0
mov byte ptr [mulres7+6], 0
mov byte ptr [mulres8+6], 0
mov byte ptr [mulrest1+6], 0
mov byte ptr [mulrest2+6], 0
mov byte ptr [mulrest3+6], 0
mov byte ptr [mulrest4+6], 0
mov byte ptr [mulrest5+6], 0
mov byte ptr [mulrest6+6], 0
mov byte ptr [mulrest7+6], 0
mov byte ptr [mulrest8+6], 0
mov byte ptr [mul32arg1_5+6], 0
mov byte ptr [mul32arg1_6+6], 0
mov byte ptr [mul32arg1_7+6], 0
mov byte ptr [mul32arg1_8+6], 0

mainloop:

;; copy x to addition, shift left
ifdef X64
mov dword ptr [mul32arg1_1 + 2], mulx1+6-mul32arg1_1-2-4-1
mov dword ptr [mul32arg1_2 + 2], mulx2+6-mul32arg1_2-2-4-1
mov dword ptr [mul32arg1_3 + 2], mulx3+6-mul32arg1_3-2-4-1
mov dword ptr [mul32arg1_4 + 2], mulx4+6-mul32arg1_4-2-4-1
mov dword ptr [mul32arg1_5 + 2], mulx5+6-mul32arg1_5-2-4-1
mov dword ptr [mul32arg1_6 + 2], mulx6+6-mul32arg1_6-2-4-1
mov dword ptr [mul32arg1_7 + 2], mulx7+6-mul32arg1_7-2-4-1
mov dword ptr [mul32arg1_8 + 2], mulx8+6-mul32arg1_8-2-4-1
else
mov dword ptr [mul32arg1_1 + 2], mulx1+6
mov dword ptr [mul32arg1_2 + 2], mulx2+6
mov dword ptr [mul32arg1_3 + 2], mulx3+6
mov dword ptr [mul32arg1_4 + 2], mulx4+6
mov dword ptr [mul32arg1_5 + 2], mulx5+6
mov dword ptr [mul32arg1_6 + 2], mulx6+6
mov dword ptr [mul32arg1_7 + 2], mulx7+6
mov dword ptr [mul32arg1_8 + 2], mulx8+6
endif
mov dword ptr [mularg1loop + 1], mularg1head-mularg1loop-5
jmp mul32arg1_1
mularg1head: mov dword ptr [mularg1loop+1], 0 ;exit loop
ifdef X64
mov dword ptr [mul32arg1_1 + 2], shlx1+6-mul32arg1_1-2-4-1
mov dword ptr [mul32arg1_2 + 2], shlx2+6-mul32arg1_2-2-4-1
mov dword ptr [mul32arg1_3 + 2], shlx3+6-mul32arg1_3-2-4-1
mov dword ptr [mul32arg1_4 + 2], shlx4+6-mul32arg1_4-2-4-1
mov dword ptr [mul32arg1_5 + 2], shlx5+6-mul32arg1_5-2-4-1
mov dword ptr [mul32arg1_6 + 2], shlx6+6-mul32arg1_6-2-4-1
mov dword ptr [mul32arg1_7 + 2], shlx7+6-mul32arg1_7-2-4-1
mov dword ptr [mul32arg1_8 + 2], shlx8+6-mul32arg1_8-2-4-1
else
mov dword ptr [mul32arg1_1 + 2], shlx1+6
mov dword ptr [mul32arg1_2 + 2], shlx2+6
mov dword ptr [mul32arg1_3 + 2], shlx3+6
mov dword ptr [mul32arg1_4 + 2], shlx4+6
mov dword ptr [mul32arg1_5 + 2], shlx5+6
mov dword ptr [mul32arg1_6 + 2], shlx6+6
mov dword ptr [mul32arg1_7 + 2], shlx7+6
mov dword ptr [mul32arg1_8 + 2], shlx8+6
endif
jmp mul32arg1_1 ; branch after patching code before executing it
mul32arg1_1:: mov byte ptr [mulx1+6], 0
mul32arg1_2:: mov byte ptr [mulx2+6], 0
mul32arg1_3:: mov byte ptr [mulx3+6], 0
mul32arg1_4:: mov byte ptr [mulx4+6], 0
mul32arg1_5:: mov byte ptr [mulx5+6], 0
mul32arg1_6:: mov byte ptr [mulx6+6], 0
mul32arg1_7:: mov byte ptr [mulx7+6], 0
mul32arg1_8:: mov byte ptr [mulx8+6], 0
mularg1loop: jmp mularg1head

;; copy y to 0 check, low byte to bit check, shift right
ifdef X64
mov dword ptr [mul32arg2_1 + 2], mul32arg2_1copy+6-mul32arg2_1-2-4-1
else
mov dword ptr [mul32arg2_1 + 2], mul32arg2_1copy+6
endif
mov byte ptr [mulargyloop + 1], mulargyhead-mulargyloop-2
jmp mul32arg2_1
mulargyhead: mov byte ptr [mulargyloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [mul32arg2_1 + 2], yand+6-mul32arg2_1-2-4-1
else
mov dword ptr [mul32arg2_1 + 2], yand+6
endif
jmp mul32arg2_1 ; branch after patching code before executing it
mul32arg2_1:: mov byte ptr [mul32arg2_1copy+6], 0
mulargyloop: jmp mulargyhead

ifdef X64
mov dword ptr [mul32arg2_1copy + 2], checky1+6-mul32arg2_1copy-2-4-1
mov dword ptr [mul32arg2_2 + 2], checky2+6-mul32arg2_2-2-4-1
mov dword ptr [mul32arg2_3 + 2], checky3+6-mul32arg2_3-2-4-1
mov dword ptr [mul32arg2_4 + 2], checky4+6-mul32arg2_4-2-4-1
else
mov dword ptr [mul32arg2_1copy + 2], checky1+6
mov dword ptr [mul32arg2_2 + 2], checky2+6
mov dword ptr [mul32arg2_3 + 2], checky3+6
mov dword ptr [mul32arg2_4 + 2], checky4+6
endif
mov byte ptr [mularg2loop + 1], mularg2head-mularg2loop-2
jmp mul32arg2_1copy
mularg2head: mov byte ptr [mularg2loop+1], 0 ;exit loop
ifdef X64
mov dword ptr [mul32arg2_1copy + 2], shry1+6-mul32arg2_1copy-2-4-1
mov dword ptr [mul32arg2_2 + 2], shry2+6-mul32arg2_2-2-4-1
mov dword ptr [mul32arg2_3 + 2], shry3+6-mul32arg2_3-2-4-1
mov dword ptr [mul32arg2_4 + 2], shry4+6-mul32arg2_4-2-4-1
else
mov dword ptr [mul32arg2_1copy + 2], shry1+6
mov dword ptr [mul32arg2_2 + 2], shry2+6
mov dword ptr [mul32arg2_3 + 2], shry3+6
mov dword ptr [mul32arg2_4 + 2], shry4+6
endif
jmp mul32arg2_1copy ; branch after patching code before executing it
mul32arg2_1copy:: mov byte ptr [checky1+6], 0
mul32arg2_2:: mov byte ptr [checky2+6], 0
mul32arg2_3:: mov byte ptr [checky3+6], 0
mul32arg2_4:: mov byte ptr [checky4+6], 0
mularg2loop: jmp mularg2head

IRP val, <1, 2, 3, 4>
checky&val&: mov byte ptr [nzarg+2+4], 0
ifdef X64	
mov dword ptr [nzres+2], nzretval&val& + 2+4 - nzret
else
mov dword ptr [nzres+2], nzretval&val& + 2+4
endif
mov dword ptr [nzret+1], nzretval&val& - nzret - 5
jmp WriteExecNZ
nzretval&val&: mov byte ptr [shlarg+2], 0
ifdef X64
mov dword ptr [shlres+1+2], shlretval&val& + 1 - shlret
else
mov dword ptr [shlres+1+2], shlretval&val& + 1
endif
mov dword ptr [shlret+1], checkyret&val& - shlret - 5
jmp WriteExecSHL1
checkyret&val&:
ENDM

shlretval1: jmp $+8000h
jmp shlretval2
jmp continueloop
shlretval2: jmp $+8000h
jmp shlretval3
jmp continueloop
shlretval3: jmp $+8000h
jmp shlretval4
jmp continueloop
shlretval4: jmp $+8000h
jmp exitloop
jmp continueloop
exitloop: jmp exitmainloop
continueloop:

;;y and 1
yand: mov byte ptr [andarg1+6], 0
mov byte ptr [andarg2+6], 1
ifdef X64
mov dword ptr [andres+2], andretval + 2+4 - andret
else
mov dword ptr [andres+2], andretval + 2+4
endif
mov dword ptr [andret+1], andretval - andret - 5
jmp WriteExecAND
;;check zero
andretval: mov byte ptr [shlarg+2], 0
ifdef X64
mov dword ptr [shlres+1+2], shlretval + 1 - shlret
else
mov dword ptr [shlres+1+2], shlretval + 1
endif
mov dword ptr [shlret+1], shlretval - shlret - 5
jmp WriteExecSHL1
shlretval: jmp $+8000h
jmp noaddfar
jmp doadd
noaddfar: jmp noadd
doadd:
;;add result, copy result to next round, final
mulrest1: mov byte ptr [add64arg1_1+6], 0
mulrest2: mov byte ptr [add64arg1_2+6], 0
mulrest3: mov byte ptr [add64arg1_3+6], 0
mulrest4: mov byte ptr [add64arg1_4+6], 0
mulrest5: mov byte ptr [add64arg1_5+6], 0
mulrest6: mov byte ptr [add64arg1_6+6], 0
mulrest7: mov byte ptr [add64arg1_7+6], 0
mulrest8: mov byte ptr [add64arg1_8+6], 0
mulx1: mov byte ptr [add64arg2_1+6], 0
mulx2: mov byte ptr [add64arg2_2+6], 0
mulx3: mov byte ptr [add64arg2_3+6], 0
mulx4: mov byte ptr [add64arg2_4+6], 0
mulx5: mov byte ptr [add64arg2_5+6], 0
mulx6: mov byte ptr [add64arg2_6+6], 0
mulx7: mov byte ptr [add64arg2_7+6], 0
mulx8: mov byte ptr [add64arg2_8+6], 0
ifdef X64
mov dword ptr [add64res1+2], addretval1 + 2+4 - add64res2
mov dword ptr [add64res2+2], addretval2 + 2+4 - add64res3
mov dword ptr [add64res3+2], addretval3 + 2+4 - add64res4
mov dword ptr [add64res4+2], addretval4 + 2+4 - add64res5
mov dword ptr [add64res5+2], addretval5 + 2+4 - add64res6
mov dword ptr [add64res6+2], addretval6 + 2+4 - add64res7
mov dword ptr [add64res7+2], addretval7 + 2+4 - add64res8
mov dword ptr [add64res8+2], addretval8 + 2+4 - add64ret
else
mov dword ptr [add64res1+2], addretval1 + 2+4
mov dword ptr [add64res2+2], addretval2 + 2+4
mov dword ptr [add64res3+2], addretval3 + 2+4
mov dword ptr [add64res4+2], addretval4 + 2+4
mov dword ptr [add64res5+2], addretval5 + 2+4
mov dword ptr [add64res6+2], addretval6 + 2+4
mov dword ptr [add64res7+2], addretval7 + 2+4
mov dword ptr [add64res8+2], addretval8 + 2+4
endif
mov dword ptr [add64ret+1], addretval - add64ret - 5
jmp WriteExecADD64
addretval:
ifdef X64
mov dword ptr [addretval1 + 2], mulrest1+6-addretval1-2-4-1
mov dword ptr [addretval2 + 2], mulrest2+6-addretval2-2-4-1
mov dword ptr [addretval3 + 2], mulrest3+6-addretval3-2-4-1
mov dword ptr [addretval4 + 2], mulrest4+6-addretval4-2-4-1
mov dword ptr [addretval5 + 2], mulrest5+6-addretval5-2-4-1
mov dword ptr [addretval6 + 2], mulrest6+6-addretval6-2-4-1
mov dword ptr [addretval7 + 2], mulrest7+6-addretval7-2-4-1
mov dword ptr [addretval8 + 2], mulrest8+6-addretval8-2-4-1
else
mov dword ptr [addretval1 + 2], mulrest1+6
mov dword ptr [addretval2 + 2], mulrest2+6
mov dword ptr [addretval3 + 2], mulrest3+6
mov dword ptr [addretval4 + 2], mulrest4+6
mov dword ptr [addretval5 + 2], mulrest5+6
mov dword ptr [addretval6 + 2], mulrest6+6
mov dword ptr [addretval7 + 2], mulrest7+6
mov dword ptr [addretval8 + 2], mulrest8+6
endif
mov dword ptr [mulargloop + 1], mularghead-mulargloop-5
jmp addretval1
mularghead: mov dword ptr [mulargloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [addretval1 + 2], mulres1+6-addretval1-2-4-1
mov dword ptr [addretval2 + 2], mulres2+6-addretval2-2-4-1
mov dword ptr [addretval3 + 2], mulres3+6-addretval3-2-4-1
mov dword ptr [addretval4 + 2], mulres4+6-addretval4-2-4-1
mov dword ptr [addretval5 + 2], mulres5+6-addretval5-2-4-1
mov dword ptr [addretval6 + 2], mulres6+6-addretval6-2-4-1
mov dword ptr [addretval7 + 2], mulres7+6-addretval7-2-4-1
mov dword ptr [addretval8 + 2], mulres8+6-addretval8-2-4-1
else
mov dword ptr [addretval1 + 2], mulres1+6
mov dword ptr [addretval2 + 2], mulres2+6
mov dword ptr [addretval3 + 2], mulres3+6
mov dword ptr [addretval4 + 2], mulres4+6
mov dword ptr [addretval5 + 2], mulres5+6
mov dword ptr [addretval6 + 2], mulres6+6
mov dword ptr [addretval7 + 2], mulres7+6
mov dword ptr [addretval8 + 2], mulres8+6
endif
jmp addretval1 ; branch after patching code before executing it
addretval1: mov byte ptr [mulrest1+6], 0
addretval2: mov byte ptr [mulrest2+6], 0
addretval3: mov byte ptr [mulrest3+6], 0
addretval4: mov byte ptr [mulrest4+6], 0
addretval5: mov byte ptr [mulrest5+6], 0
addretval6: mov byte ptr [mulrest6+6], 0
addretval7: mov byte ptr [mulrest7+6], 0
addretval8: mov byte ptr [mulrest8+6], 0
mulargloop: jmp mularghead

noadd:
;;shift left
mov byte ptr [shl64arg2_1+6], 1
shlx1: mov byte ptr [shl64arg1_1+6], 0
shlx2: mov byte ptr [shl64arg1_2+6], 0
shlx3: mov byte ptr [shl64arg1_3+6], 0
shlx4: mov byte ptr [shl64arg1_4+6], 0
shlx5: mov byte ptr [shl64arg1_5+6], 0
shlx6: mov byte ptr [shl64arg1_6+6], 0
shlx7: mov byte ptr [shl64arg1_7+6], 0
shlx8: mov byte ptr [shl64arg1_8+6], 0
ifdef X64
mov dword ptr [shl64res1+2], mul32arg1_1 + 2+4 - shl64res2
mov dword ptr [shl64res2+2], mul32arg1_2 + 2+4 - shl64res3
mov dword ptr [shl64res3+2], mul32arg1_3 + 2+4 - shl64res4
mov dword ptr [shl64res4+2], mul32arg1_4 + 2+4 - shl64res5
mov dword ptr [shl64res5+2], mul32arg1_5 + 2+4 - shl64res6
mov dword ptr [shl64res6+2], mul32arg1_6 + 2+4 - shl64res7
mov dword ptr [shl64res7+2], mul32arg1_7 + 2+4 - shl64res8
mov dword ptr [shl64res8+2], mul32arg1_8 + 2+4 - shl64ret
else
mov dword ptr [shl64res1+2], mul32arg1_1 + 2+4
mov dword ptr [shl64res2+2], mul32arg1_2 + 2+4
mov dword ptr [shl64res3+2], mul32arg1_3 + 2+4
mov dword ptr [shl64res4+2], mul32arg1_4 + 2+4
mov dword ptr [shl64res5+2], mul32arg1_5 + 2+4
mov dword ptr [shl64res6+2], mul32arg1_6 + 2+4
mov dword ptr [shl64res7+2], mul32arg1_7 + 2+4
mov dword ptr [shl64res8+2], mul32arg1_8 + 2+4
endif
mov dword ptr [shl64ret+1], shl64retval - shl64ret - 5
jmp WriteExecSHL64
shl64retval:

mov byte ptr [shr32arg2_1+6], 1
shry1: mov byte ptr [shr32arg1_1+6], 0
shry2: mov byte ptr [shr32arg1_2+6], 0
shry3: mov byte ptr [shr32arg1_3+6], 0
shry4: mov byte ptr [shr32arg1_4+6], 0
ifdef X64
mov dword ptr [shr32res1+2], mul32arg2_1 + 2+4 - shr32res2
mov dword ptr [shr32res2+2], mul32arg2_2 + 2+4 - shr32res3
mov dword ptr [shr32res3+2], mul32arg2_3 + 2+4 - shr32res4
mov dword ptr [shr32res4+2], mul32arg2_4 + 2+4 - shr32ret
else
mov dword ptr [shr32res1+2], mul32arg2_1 + 2+4
mov dword ptr [shr32res2+2], mul32arg2_2 + 2+4
mov dword ptr [shr32res3+2], mul32arg2_3 + 2+4
mov dword ptr [shr32res4+2], mul32arg2_4 + 2+4
endif
mov dword ptr [shr32ret+1], mainloop - shr32ret - 5
jmp WriteExecSHR32

exitmainloop:

mulres1:: mov byte ptr [mulres1+6], 0
mulres2:: mov byte ptr [mulres2+6], 0
mulres3:: mov byte ptr [mulres3+6], 0
mulres4:: mov byte ptr [mulres4+6], 0
mulres5:: mov byte ptr [mulres5+6], 0
mulres6:: mov byte ptr [mulres6+6], 0
mulres7:: mov byte ptr [mulres7+6], 0
mulres8:: mov byte ptr [mulres8+6], 0
mul32ret:: jmp $+80000000h
WriteExecMUL32 ENDP

ifndef X64
WriteExecMUL32_C PROC mul32_1arg: DWORD, mul32_2arg: DWORD
mov ecx, dword ptr [mul32_1arg]
mov edx, dword ptr [mul32_2arg]
else
WriteExecMUL32_C PROC
endif
mov byte ptr [mul32arg1_1+6], cl
mov byte ptr [mul32arg2_1+6], dl
mov byte ptr [mul32arg1_2+6], ch
mov byte ptr [mul32arg2_2+6], dh
shr ecx, 16
shr edx, 16
mov byte ptr [mul32arg1_3+6], cl
mov byte ptr [mul32arg2_3+6], dl
mov byte ptr [mul32arg1_4+6], ch
mov byte ptr [mul32arg2_4+6], dh
ifdef X64
mov dword ptr [mulres1+2], mulretval + 2 - mulres2
mov dword ptr [mulres2+2], mulretval + 3 - mulres3
mov dword ptr [mulres3+2], mulretval + 4 - mulres4
mov dword ptr [mulres4+2], mulretval + 5 - mulres5
mov dword ptr [mulres5+2], mulretval + 6 - mulres6
mov dword ptr [mulres6+2], mulretval + 7 - mulres7
mov dword ptr [mulres7+2], mulretval + 8 - mulres8
mov dword ptr [mulres8+2], mulretval + 9 - mul32ret
else
mov dword ptr [mulres1+2], mulretval + 1
mov dword ptr [mulres2+2], mulretval + 2
mov dword ptr [mulres3+2], mulretval + 3
mov dword ptr [mulres4+2], mulretval + 4
mov dword ptr [mulres5+2], mulretval2 + 1
mov dword ptr [mulres6+2], mulretval2 + 2
mov dword ptr [mulres7+2], mulretval2 + 3
mov dword ptr [mulres8+2], mulretval2 + 4
endif
mov dword ptr [mul32ret+1], mulretval - mul32ret - 5
jmp WriteExecMUL32
ifndef X64
mulretval: mov eax, 80000000h
mulretval2: mov edx, 80000000h
else
mulretval: mov rax, 80000000h
endif
ret
WriteExecMUL32_C ENDP

WriteExecDIV32 PROC
mov byte ptr [divrem1+6], 0
mov byte ptr [divrem2+6], 0
mov byte ptr [divrem3+6], 0
mov byte ptr [divrem4+6], 0
mov byte ptr [shly1+6], 0
mov byte ptr [shly2+6], 0
mov byte ptr [shly3+6], 0
mov byte ptr [shly4+6], 0
mov byte ptr [ct+6], 64
ifdef X64
mov dword ptr [div32arg2_4 + 2], div32arg2_4copy+6-div32arg2_4-2-4-1
else
mov dword ptr [div32arg2_4 + 2], div32arg2_4copy+6
endif
mov byte ptr [ynotloop + 1], ynothead2-ynotloop-2
jmp div32arg2_4
ynothead2: mov byte ptr [ynotloop+1], ynothead-ynotloop-2
ifdef X64
mov dword ptr [div32arg2_4 + 2], ynot+6-div32arg2_4-2-4-1
else
mov dword ptr [div32arg2_4 + 2], ynot+6
endif
jmp div32arg2_4
ynothead: mov byte ptr [ynotloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [div32arg2_4 + 2], yxor2+6-div32arg2_4-2-4-1
else
mov dword ptr [div32arg2_4 + 2], yxor2+6
endif
jmp div32arg2_4 ; branch after patching code before executing it
div32arg2_4:: mov byte ptr [div32arg2_4copy+6], 0
ynotloop: jmp ynothead2

mainloop:

;; copy quot/x to shift left, low dword to result
ifdef X64
mov dword ptr [div32arg1_1 + 2], div32arg1_1copy+6-div32arg1_1-2-4-1
mov dword ptr [div32arg1_2 + 2], div32arg1_2copy+6-div32arg1_2-2-4-1
mov dword ptr [div32arg1_3 + 2], div32arg1_3copy+6-div32arg1_3-2-4-1
mov dword ptr [div32arg1_4 + 2], div32arg1_4copy+6-div32arg1_4-2-4-1
else
mov dword ptr [div32arg1_1 + 2], div32arg1_1copy+6
mov dword ptr [div32arg1_2 + 2], div32arg1_2copy+6
mov dword ptr [div32arg1_3 + 2], div32arg1_3copy+6
mov dword ptr [div32arg1_4 + 2], div32arg1_4copy+6
endif
mov byte ptr [divarglow1loop + 1], divarglow1head-divarglow1loop-2
jmp div32arg1_1
divarglow1head: mov byte ptr [divarglow1loop+1], 0 ;exit loop
ifdef X64
mov dword ptr [div32arg1_1 + 2], divres1+6-div32arg1_1-2-4-1
mov dword ptr [div32arg1_2 + 2], divres2+6-div32arg1_2-2-4-1
mov dword ptr [div32arg1_3 + 2], divres3+6-div32arg1_3-2-4-1
mov dword ptr [div32arg1_4 + 2], divres4+6-div32arg1_4-2-4-1
else
mov dword ptr [div32arg1_1 + 2], divres1+6
mov dword ptr [div32arg1_2 + 2], divres2+6
mov dword ptr [div32arg1_3 + 2], divres3+6
mov dword ptr [div32arg1_4 + 2], divres4+6
endif
jmp div32arg1_1 ; branch after patching code before executing it
div32arg1_1:: mov byte ptr [div32arg1_1copy+6], 0
div32arg1_2:: mov byte ptr [div32arg1_2copy+6], 0
div32arg1_3:: mov byte ptr [div32arg1_3copy+6], 0
div32arg1_4:: mov byte ptr [div32arg1_4copy+6], 0
divarglow1loop: jmp divarglow1head

ifdef X64
mov dword ptr [div32arg1_1copy + 2], divx1+6-div32arg1_1copy-2-4-1
mov dword ptr [div32arg1_2copy + 2], divx2+6-div32arg1_2copy-2-4-1
mov dword ptr [div32arg1_3copy + 2], divx3+6-div32arg1_3copy-2-4-1
mov dword ptr [div32arg1_4copy + 2], divx4+6-div32arg1_4copy-2-4-1
mov dword ptr [div32arg1_5 + 2], divx5+6-div32arg1_5-2-4-1
mov dword ptr [div32arg1_6 + 2], divx6+6-div32arg1_6-2-4-1
mov dword ptr [div32arg1_7 + 2], divx7+6-div32arg1_7-2-4-1
mov dword ptr [div32arg1_8 + 2], divx8+6-div32arg1_8-2-4-1
else
mov dword ptr [div32arg1_1copy + 2], divx1+6
mov dword ptr [div32arg1_2copy + 2], divx2+6
mov dword ptr [div32arg1_3copy + 2], divx3+6
mov dword ptr [div32arg1_4copy + 2], divx4+6
mov dword ptr [div32arg1_5 + 2], divx5+6
mov dword ptr [div32arg1_6 + 2], divx6+6
mov dword ptr [div32arg1_7 + 2], divx7+6
mov dword ptr [div32arg1_8 + 2], divx8+6
endif
mov dword ptr [divarg1loop + 1], divarg1head-divarg1loop-5
jmp div32arg1_1copy
divarg1head: mov dword ptr [divarg1loop+1], 0 ;exit loop
ifdef X64
mov dword ptr [div32arg1_1copy + 2], shlx1+6-div32arg1_1copy-2-4-1
mov dword ptr [div32arg1_2copy + 2], shlx2+6-div32arg1_2copy-2-4-1
mov dword ptr [div32arg1_3copy + 2], shlx3+6-div32arg1_3copy-2-4-1
mov dword ptr [div32arg1_4copy + 2], shlx4+6-div32arg1_4copy-2-4-1
mov dword ptr [div32arg1_5 + 2], shlx5+6-div32arg1_5-2-4-1
mov dword ptr [div32arg1_6 + 2], shlx6+6-div32arg1_6-2-4-1
mov dword ptr [div32arg1_7 + 2], shlx7+6-div32arg1_7-2-4-1
mov dword ptr [div32arg1_8 + 2], shlx8+6-div32arg1_8-2-4-1
else
mov dword ptr [div32arg1_1copy + 2], shlx1+6
mov dword ptr [div32arg1_2copy + 2], shlx2+6
mov dword ptr [div32arg1_3copy + 2], shlx3+6
mov dword ptr [div32arg1_4copy + 2], shlx4+6
mov dword ptr [div32arg1_5 + 2], shlx5+6
mov dword ptr [div32arg1_6 + 2], shlx6+6
mov dword ptr [div32arg1_7 + 2], shlx7+6
mov dword ptr [div32arg1_8 + 2], shlx8+6
endif
jmp div32arg1_1copy ; branch after patching code before executing it
div32arg1_1copy: mov byte ptr [divx1+6], 0
div32arg1_2copy: mov byte ptr [divx2+6], 0
div32arg1_3copy: mov byte ptr [divx3+6], 0
div32arg1_4copy: mov byte ptr [divx4+6], 0
div32arg1_5:: mov byte ptr [divx5+6], 0
div32arg1_6:: mov byte ptr [divx6+6], 0
div32arg1_7:: mov byte ptr [divx7+6], 0
div32arg1_8:: mov byte ptr [divx8+6], 0
divarg1loop: jmp divarg1head

;;copy counter to zero check, next round decrement
ifdef X64
mov dword ptr [ct + 2], decval+6-ct-2-4-1
else
mov dword ptr [ct + 2], decval+6
endif
mov byte ptr [ctrloop + 1], ctrhead-ctrloop-2
jmp ct
ctrhead: mov byte ptr [ctrloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [ct + 2], ctrchk+6-ct-2-4-1
else
mov dword ptr [ct + 2], ctrchk+6
endif
jmp ct ; branch after patching code before executing it
ct: mov byte ptr [decval+6], 0
ctrloop: jmp ctrhead

;;check counter 0
ctrchk: mov byte ptr [nzarg+2+4], 0
ifdef X64
mov dword ptr [nzres+2], nzretval + 2+4 - nzret
else
mov dword ptr [nzres+2], nzretval + 2+4
endif
mov dword ptr [nzret+1], nzretval - nzret - 5
jmp WriteExecNZ
nzretval: mov byte ptr [shlarg+2], 0
ifdef X64
mov dword ptr [shlres+1+2], shlretval + 1 - shlret
else
mov dword ptr [shlres+1+2], shlretval + 1
endif
mov dword ptr [shlret+1], shlretval - shlret - 5
jmp WriteExecSHL1

shlretval: jmp $+8000h
jmp exitloop
jmp continueloop
exitloop: jmp exitmainloop
continueloop:

;; decrement counter
decval: mov byte ptr [decarg+2+4], 0
ifdef X64
mov dword ptr [decres+2], ct + 2+4 - decres2
mov dword ptr [decres2+2], deccarry + 2+4 - decret
else
mov dword ptr [decres+2], ct + 2+4
mov dword ptr [decres2+2], deccarry + 2+4
endif
mov dword ptr [decret+1], deccarry - decret - 5
jmp WriteExecDEC
deccarry: mov byte ptr [deccarry+2+4], 0

;;shift quot left
mov byte ptr [shl64arg2_1+6], 1
shlx1: mov byte ptr [shl64arg1_1+6], 0
shlx2: mov byte ptr [shl64arg1_2+6], 0
shlx3: mov byte ptr [shl64arg1_3+6], 0
shlx4: mov byte ptr [shl64arg1_4+6], 0
shlx5: mov byte ptr [shl64arg1_5+6], 0
shlx6: mov byte ptr [shl64arg1_6+6], 0
shlx7: mov byte ptr [shl64arg1_7+6], 0
shlx8: mov byte ptr [shl64arg1_8+6], 0
ifdef X64
mov dword ptr [shl64res1+2], div32shl1_1 + 2+4 - shl64res2
mov dword ptr [shl64res2+2], div32shl1_2 + 2+4 - shl64res3
mov dword ptr [shl64res3+2], div32shl1_3 + 2+4 - shl64res4
mov dword ptr [shl64res4+2], div32shl1_4 + 2+4 - shl64res5
mov dword ptr [shl64res5+2], div32shl1_5 + 2+4 - shl64res6
mov dword ptr [shl64res6+2], div32shl1_6 + 2+4 - shl64res7
mov dword ptr [shl64res7+2], div32shl1_7 + 2+4 - shl64res8
mov dword ptr [shl64res8+2], div32shl1_8 + 2+4 - shl64ret
else
mov dword ptr [shl64res1+2], div32shl1_1 + 2+4
mov dword ptr [shl64res2+2], div32shl1_2 + 2+4
mov dword ptr [shl64res3+2], div32shl1_3 + 2+4
mov dword ptr [shl64res4+2], div32shl1_4 + 2+4
mov dword ptr [shl64res5+2], div32shl1_5 + 2+4
mov dword ptr [shl64res6+2], div32shl1_6 + 2+4
mov dword ptr [shl64res7+2], div32shl1_7 + 2+4
mov dword ptr [shl64res8+2], div32shl1_8 + 2+4
endif
mov dword ptr [shl64ret+1], shl64retval - shl64ret - 5
jmp WriteExecSHL64
shl64retval:

;;copy result to comparison and next round, low byte to adjustment
ifdef X64
mov dword ptr [div32shl1_1 + 2], div32shl1_1copy+6-div32shl1_1-2-4-1
else
mov dword ptr [div32shl1_1 + 2], div32shl1_1copy+6
endif
mov byte ptr [divshlloop + 1], divshlhead-divshlloop-2
jmp div32shl1_1
divshlhead: mov byte ptr [divshlloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [div32shl1_1 + 2], quotxor+6-div32shl1_1-2-4-1
else
mov dword ptr [div32shl1_1 + 2], quotxor+6
endif
jmp div32shl1_1 ; branch after patching code before executing it
div32shl1_1: mov byte ptr [div32shl1_1copy+6], 0
divshlloop: jmp divshlhead

ifdef X64
mov dword ptr [div32shl1_1copy + 2], divrest1+6-div32shl1_1copy-2-4-1
mov dword ptr [div32shl1_2 + 2], divrest2+6-div32shl1_2-2-4-1
mov dword ptr [div32shl1_3 + 2], divrest3+6-div32shl1_3-2-4-1
mov dword ptr [div32shl1_4 + 2], divrest4+6-div32shl1_4-2-4-1
mov dword ptr [div32shl1_5 + 2], divrest5+6-div32shl1_5-2-4-1
mov dword ptr [div32shl1_6 + 2], divrest6+6-div32shl1_6-2-4-1
mov dword ptr [div32shl1_7 + 2], divrest7+6-div32shl1_7-2-4-1
mov dword ptr [div32shl1_8 + 2], divrest8+6-div32shl1_8-2-4-1
else
mov dword ptr [div32shl1_1copy + 2], divrest1+6
mov dword ptr [div32shl1_2 + 2], divrest2+6
mov dword ptr [div32shl1_3 + 2], divrest3+6
mov dword ptr [div32shl1_4 + 2], divrest4+6
mov dword ptr [div32shl1_5 + 2], divrest5+6
mov dword ptr [div32shl1_6 + 2], divrest6+6
mov dword ptr [div32shl1_7 + 2], divrest7+6
mov dword ptr [div32shl1_8 + 2], divrest8+6
endif
mov dword ptr [divshl1loop + 1], divshl1head-divshl1loop-5
jmp div32shl1_1copy
divshl1head: mov dword ptr [divshl1loop+1], 0 ;exit loop
ifdef X64
mov dword ptr [div32shl1_1copy + 2], div32arg1_1+6-div32shl1_1copy-2-4-1
mov dword ptr [div32shl1_2 + 2], div32arg1_2+6-div32shl1_2-2-4-1
mov dword ptr [div32shl1_3 + 2], div32arg1_3+6-div32shl1_3-2-4-1
mov dword ptr [div32shl1_4 + 2], div32arg1_4+6-div32shl1_4-2-4-1
mov dword ptr [div32shl1_5 + 2], div32arg1_5+6-div32shl1_5-2-4-1
mov dword ptr [div32shl1_6 + 2], div32arg1_6+6-div32shl1_6-2-4-1
mov dword ptr [div32shl1_7 + 2], div32arg1_7+6-div32shl1_7-2-4-1
mov dword ptr [div32shl1_8 + 2], div32arg1_8+6-div32shl1_8-2-4-1
else
mov dword ptr [div32shl1_1copy + 2], div32arg1_1+6
mov dword ptr [div32shl1_2 + 2], div32arg1_2+6
mov dword ptr [div32shl1_3 + 2], div32arg1_3+6
mov dword ptr [div32shl1_4 + 2], div32arg1_4+6
mov dword ptr [div32shl1_5 + 2], div32arg1_5+6
mov dword ptr [div32shl1_6 + 2], div32arg1_6+6
mov dword ptr [div32shl1_7 + 2], div32arg1_7+6
mov dword ptr [div32shl1_8 + 2], div32arg1_8+6
endif
jmp div32shl1_1copy ; branch after patching code before executing it
div32shl1_1copy: mov byte ptr [divrest1+6], 0
div32shl1_2: mov byte ptr [divrest2+6], 0
div32shl1_3: mov byte ptr [divrest3+6], 0
div32shl1_4: mov byte ptr [divrest4+6], 0
div32shl1_5: mov byte ptr [divrest5+6], 0
div32shl1_6: mov byte ptr [divrest6+6], 0
div32shl1_7: mov byte ptr [divrest7+6], 0
div32shl1_8: mov byte ptr [divrest8+6], 0
divshl1loop: jmp divshl1head

;; shift rem left
ifdef X64
mov dword ptr [shly4 + 2], shly4copy+6-shly4-2-4-1
else
mov dword ptr [shly4 + 2], shly4copy+6
endif
mov byte ptr [shlyloop + 1], shlyhead-shlyloop-2
jmp shly4
shlyhead: mov byte ptr [shlyloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [shly4 + 2], shlof+6-shly4-2-4-1
else
mov dword ptr [shly4 + 2], shlof+6
endif
jmp shly4 ; branch after patching code before executing it
shly4: mov byte ptr [shly4+6], 0
shlyloop: jmp shlyhead

mov byte ptr [shl32arg2_1+6], 1
shly1: mov byte ptr [shl32arg1_1+6], 0
shly2: mov byte ptr [shl32arg1_2+6], 0
shly3: mov byte ptr [shl32arg1_3+6], 0
shly4copy: mov byte ptr [shl32arg1_4+6], 0
ifdef X64
mov dword ptr [shl32res1+2], div32rem2_1 + 2+4 - shl32res2
mov dword ptr [shl32res2+2], div32rem2_2 + 2+4 - shl32res3
mov dword ptr [shl32res3+2], div32rem2_3 + 2+4 - shl32res4
mov dword ptr [shl32res4+2], div32rem2_4 + 2+4 - shl32ret
else
mov dword ptr [shl32res1+2], div32rem2_1 + 2+4
mov dword ptr [shl32res2+2], div32rem2_2 + 2+4
mov dword ptr [shl32res3+2], div32rem2_3 + 2+4
mov dword ptr [shl32res4+2], div32rem2_4 + 2+4
endif
mov dword ptr [shl32ret+1], shlafter - shl32ret - 5
jmp WriteExecSHL32
shlafter:

ifdef X64
mov dword ptr [divx8 + 2], divx8copy+6-divx8-2-4-1
mov dword ptr [divrest8 + 2], divrest8copy+6-divrest8-2-4-1
else
mov dword ptr [divx8 + 2], divx8copy+6
mov dword ptr [divrest8 + 2], divrest8copy+6
endif
mov byte ptr [lxorloop + 1], lxorhead2-lxorloop-2
jmp divx8
lxorhead2: mov byte ptr [lxorloop+1], lxorhead-lxorloop-2
ifdef X64
mov dword ptr [divx8 + 2], lnot+6-divx8-2-4-1
mov dword ptr [divrest8 + 2], land+6-divrest8-2-4-1
else
mov dword ptr [divx8 + 2], lnot+6
mov dword ptr [divrest8 + 2], land+6
endif
jmp divx8
lxorhead: mov byte ptr [lxorloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [divx8 + 2], lxor+6-divx8-2-4-1
mov dword ptr [divrest8 + 2], lxor2+6-divrest8-2-4-1
else
mov dword ptr [divx8 + 2], lxor+6
mov dword ptr [divrest8 + 2], lxor2+6
endif
jmp divx8 ; branch after patching code before executing it
divx8: mov byte ptr [divx8copy+6], 0
divrest8: mov byte ptr [divrest8copy+6], 0
lxorloop: jmp lxorhead2

divrest1: mov byte ptr [sub64arg1_1+6], 0
divrest2: mov byte ptr [sub64arg1_2+6], 0
divrest3: mov byte ptr [sub64arg1_3+6], 0
divrest4: mov byte ptr [sub64arg1_4+6], 0
divrest5: mov byte ptr [sub64arg1_5+6], 0
divrest6: mov byte ptr [sub64arg1_6+6], 0
divrest7: mov byte ptr [sub64arg1_7+6], 0
divrest8copy: mov byte ptr [sub64arg1_8+6], 0
divx1: mov byte ptr [sub64arg2_1+6], 0
divx2: mov byte ptr [sub64arg2_2+6], 0
divx3: mov byte ptr [sub64arg2_3+6], 0
divx4: mov byte ptr [sub64arg2_4+6], 0
divx5: mov byte ptr [sub64arg2_5+6], 0
divx6: mov byte ptr [sub64arg2_6+6], 0
divx7: mov byte ptr [sub64arg2_7+6], 0
divx8copy: mov byte ptr [sub64arg2_8+6], 0
ifdef X64
mov dword ptr [sub64res1+2], subretval1 + 2+4 - sub64res2
mov dword ptr [sub64res2+2], subretval2 + 2+4 - sub64res3
mov dword ptr [sub64res3+2], subretval3 + 2+4 - sub64res4
mov dword ptr [sub64res4+2], subretval4 + 2+4 - sub64res5
mov dword ptr [sub64res5+2], subretval5 + 2+4 - sub64res6
mov dword ptr [sub64res6+2], subretval6 + 2+4 - sub64res7
mov dword ptr [sub64res7+2], subretval7 + 2+4 - sub64res8
mov dword ptr [sub64res8+2], subretval8 + 2+4 - sub64ret
else
mov dword ptr [sub64res1+2], subretval1 + 2+4
mov dword ptr [sub64res2+2], subretval2 + 2+4
mov dword ptr [sub64res3+2], subretval3 + 2+4
mov dword ptr [sub64res4+2], subretval4 + 2+4
mov dword ptr [sub64res5+2], subretval5 + 2+4
mov dword ptr [sub64res6+2], subretval6 + 2+4
mov dword ptr [sub64res7+2], subretval7 + 2+4
mov dword ptr [sub64res8+2], subretval8 + 2+4
endif
mov dword ptr [sub64ret+1], subretval1 - sub64ret - 5
jmp WriteExecSUB64
subretval1: mov byte ptr [subretval1+6], 0
subretval2: mov byte ptr [subretval2+6], 0
subretval3: mov byte ptr [subretval3+6], 0
subretval4: mov byte ptr [subretval4+6], 0
subretval5: mov byte ptr [subretval5+6], 0
subretval6: mov byte ptr [subretval6+6], 0
subretval7: mov byte ptr [subretval7+6], 0
;; quot < t -> !(quot - t >= 0)
;; unsigned so high bits: 0 0 0, 1 1 0, 1 0 - !(a & !b ^ (a ^ b) | c) vs 0 0 1, 1 1 1, 0 1 -

lxor: mov byte ptr [xorarg1+6], 0
lxor2: mov byte ptr [xorarg2+6], 0
ifdef X64
mov dword ptr [xorres+2], lxor3 + 2+4 - xorret
else
mov dword ptr [xorres+2], lxor3 + 2+4
endif
mov dword ptr [xorret+1], lnot - xorret - 5
jmp WriteExecXOR
lnot: mov byte ptr [notarg+6], 0
ifdef X64
mov dword ptr [notres+2], land2 + 2+4 - notret
else
mov dword ptr [notres+2], land2 + 2+4
endif
mov dword ptr [notret+1], land - notret - 5
jmp WriteExecNOT
land: mov byte ptr [andarg1+6], 0
land2: mov byte ptr [andarg2+6], 0
ifdef X64
mov dword ptr [andres+2], lxor4 + 2+4 - andret
else
mov dword ptr [andres+2], lxor4 + 2+4
endif
mov dword ptr [andret+1], lxor3 - andret - 5
jmp WriteExecAND
lxor3: mov byte ptr [xorarg1+6], 0
lxor4: mov byte ptr [xorarg2+6], 0
ifdef X64
mov dword ptr [xorres+2], lor + 2+4 - xorret
else
mov dword ptr [xorres+2], lor + 2+4
endif
mov dword ptr [xorret+1], lor - xorret - 5
jmp WriteExecXOR
lor: mov byte ptr [orarg1+6], 0
subretval8: mov byte ptr [orarg2+6], 0
ifdef X64
mov dword ptr [orres+2], lorretval + 2+4 - orret
else
mov dword ptr [orres+2], lorretval + 2+4
endif
mov dword ptr [orret+1], lorretval - orret - 5
jmp WriteExecOR

;;check zero
lorretval: mov byte ptr [shlarg1+2+4], 0
mov byte ptr [shlarg2+2+4], 1
ifdef X64
mov dword ptr [shlbres+2], shlpreretval + 2+4 - shlbres2
mov dword ptr [shlbres2+2], lxorres + 2+4 - shlbret
else
mov dword ptr [shlbres+2], shlpreretval + 2+4
mov dword ptr [shlbres2+2], lxorres + 2+4
endif
mov dword ptr [shlbret+1], lxorres - shlbret - 5
jmp WriteExecSHL

;;xor low byte
lxorres: mov byte ptr [xorarg1+6], 0
div32rem2_1: mov byte ptr [xorarg2+6], 0
ifdef X64
mov dword ptr [xorres+2], div32rem2_1final + 2+4 - xorret
else
mov dword ptr [xorres+2], div32rem2_1final + 2+4
endif
mov dword ptr [xorret+1], remy - xorret - 5
jmp WriteExecXOR
remy:

;;rem-y >= 0
ifdef X64
mov dword ptr [div32rem2_4 + 2], div32rem2_4copy+6-div32rem2_4-2-4-1
else
mov dword ptr [div32rem2_4 + 2], div32rem2_4copy+6
endif
mov byte ptr [yxorloop + 1], yxorhead2-yxorloop-2
jmp div32rem2_4
yxorhead2: mov byte ptr [yxorloop+1], yxorhead-yxorloop-2
ifdef X64
mov dword ptr [div32rem2_4 + 2], yand+6-div32rem2_4-2-4-1
else
mov dword ptr [div32rem2_4 + 2], yand+6
endif
jmp div32rem2_4
yxorhead: mov byte ptr [yxorloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [div32rem2_4 + 2], yxor+6-div32rem2_4-2-4-1
else
mov dword ptr [div32rem2_4 + 2], yxor+6
endif
jmp div32rem2_4 ; branch after patching code before executing it
div32rem2_4: mov byte ptr [div32rem2_4copy+6], 0
yxorloop: jmp yxorhead2

ifdef X64
mov dword ptr [div32rem2_1final + 2], div32rem2_1sub+6-div32rem2_1final-2-4-1
mov dword ptr [div32rem2_2 + 2], div32rem2_2sub+6-div32rem2_2-2-4-1
mov dword ptr [div32rem2_3 + 2], div32rem2_3sub+6-div32rem2_3-2-4-1
mov dword ptr [div32rem2_4copy + 2], div32rem2_4sub+6-div32rem2_4copy-2-4-1
else
mov dword ptr [div32rem2_1final + 2], div32rem2_1sub+6
mov dword ptr [div32rem2_2 + 2], div32rem2_2sub+6
mov dword ptr [div32rem2_3 + 2], div32rem2_3sub+6
mov dword ptr [div32rem2_4copy + 2], div32rem2_4sub+6
endif
mov byte ptr [divsubloop + 1], divsubhead-divsubloop-2
jmp div32rem2_1final
divsubhead: mov byte ptr [divsubloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [div32rem2_1final + 2], div32_2_1+6-div32rem2_1final-2-4-1
mov dword ptr [div32rem2_2 + 2], div32_2_2+6-div32rem2_2-2-4-1
mov dword ptr [div32rem2_3 + 2], div32_2_3+6-div32rem2_3-2-4-1
mov dword ptr [div32rem2_4copy + 2], div32_2_4+6-div32rem2_4copy-2-4-1
else
mov dword ptr [div32rem2_1final + 2], div32_2_1+6
mov dword ptr [div32rem2_2 + 2], div32_2_2+6
mov dword ptr [div32rem2_3 + 2], div32_2_3+6
mov dword ptr [div32rem2_4copy + 2], div32_2_4+6
endif
jmp div32rem2_1final ; branch after patching code before executing it
div32rem2_1final: mov byte ptr [div32rem2_1sub+6], 0
div32rem2_2: mov byte ptr [div32rem2_2sub+6], 0
div32rem2_3: mov byte ptr [div32rem2_3sub+6], 0
div32rem2_4copy: mov byte ptr [div32rem2_4sub+6], 0
divsubloop: jmp divsubhead

div32rem2_1sub: mov byte ptr [sub32arg1_1+6], 0
div32rem2_2sub: mov byte ptr [sub32arg1_2+6], 0
div32rem2_3sub: mov byte ptr [sub32arg1_3+6], 0
div32rem2_4sub: mov byte ptr [sub32arg1_4+6], 0
div32arg2_1:: mov byte ptr [sub32arg2_1+6], 0
div32arg2_2:: mov byte ptr [sub32arg2_2+6], 0
div32arg2_3:: mov byte ptr [sub32arg2_3+6], 0
div32arg2_4copy: mov byte ptr [sub32arg2_4+6], 0
ifdef X64
mov dword ptr [sub32res1+2], subremval1 + 2+4 - sub32res2
mov dword ptr [sub32res2+2], subremval2 + 2+4 - sub32res3
mov dword ptr [sub32res3+2], subremval3 + 2+4 - sub32res4
mov dword ptr [sub32res4+2], subremval4 + 2+4 - sub32ret
else
mov dword ptr [sub32res1+2], subremval1 + 2+4
mov dword ptr [sub32res2+2], subremval2 + 2+4
mov dword ptr [sub32res3+2], subremval3 + 2+4
mov dword ptr [sub32res4+2], subremval4 + 2+4
endif
mov dword ptr [sub32ret+1], subafter - sub32ret - 5
jmp WriteExecSUB32
subafter:

ifdef X64
mov dword ptr [subremval4 + 2], subremval4copy+6-subremval4-2-4-1
else
mov dword ptr [subremval4 + 2], subremval4copy+6
endif
mov byte ptr [yxor2loop + 1], yxor2head-yxor2loop-2
jmp subremval4
yxor2head: mov byte ptr [yxor2loop+1], 0 ;exit loop
ifdef X64
mov dword ptr [subremval4 + 2], subremval4chk+6-subremval4-2-4-1
else
mov dword ptr [subremval4 + 2], subremval4chk+6
endif
jmp subremval4 ; branch after patching code before executing it
subremval4: mov byte ptr [subremval4copy+6], 0
yxor2loop: jmp yxor2head

;;check >= 0
shlof: mov byte ptr [shlarg1+2+4], 0
mov byte ptr [shlarg2+2+4], 1
ifdef X64
mov dword ptr [shlbres+2], shlpretval + 2+4 - shlbres2
mov dword ptr [shlbres2+2], shlxretval + 2+4 - shlbret
else
mov dword ptr [shlbres+2], shlpretval + 2+4
mov dword ptr [shlbres2+2], shlxretval + 2+4
endif
mov dword ptr [shlbret+1], shlpretval - shlbret - 5
jmp WriteExecSHL

shlpretval: mov byte ptr [shlpretval+6], 0
shlxretval: mov byte ptr [shlarg+2], 0
ifdef X64
mov dword ptr [shlres+1+2], shlnzrretval + 1 - shlret
else
mov dword ptr [shlres+1+2], shlnzrretval + 1
endif
mov dword ptr [shlret+1], shlnzrretval - shlret - 5
jmp WriteExecSHL1
shlnzrretval: jmp $+8000h
jmp chksub
jmp dosub
chksub:

yxor: mov byte ptr [xorarg1+6], 0
yxor2: mov byte ptr [xorarg2+6], 0
ifdef X64
mov dword ptr [xorres+2], yxor3 + 2+4 - xorret
else
mov dword ptr [xorres+2], yxor3 + 2+4
endif
mov dword ptr [xorret+1], ynot - xorret - 5
jmp WriteExecXOR
ynot: mov byte ptr [notarg+6], 0
ifdef X64
mov dword ptr [notres+2], yand2 + 2+4 - notret
else
mov dword ptr [notres+2], yand2 + 2+4
endif
mov dword ptr [notret+1], yand - notret - 5
jmp WriteExecNOT
yand: mov byte ptr [andarg1+6], 0
yand2: mov byte ptr [andarg2+6], 0
ifdef X64
mov dword ptr [andres+2], yxor4 + 2+4 - andret
else
mov dword ptr [andres+2], yxor4 + 2+4
endif
mov dword ptr [andret+1], yxor3 - andret - 5
jmp WriteExecAND
yxor3: mov byte ptr [xorarg1+6], 0
yxor4: mov byte ptr [xorarg2+6], 0
ifdef X64
mov dword ptr [xorres+2], yor + 2+4 - xorret
else
mov dword ptr [xorres+2], yor + 2+4
endif
mov dword ptr [xorret+1], yor - xorret - 5
jmp WriteExecXOR
yor: mov byte ptr [orarg1+6], 0
subremval4chk: mov byte ptr [orarg2+6], 0
ifdef X64
mov dword ptr [orres+2], orretval + 2+4 - orret
else
mov dword ptr [orres+2], orretval + 2+4
endif
mov dword ptr [orret+1], orretval - orret - 5
jmp WriteExecOR

;;check zero
orretval: mov byte ptr [shlarg1+2+4], 0
mov byte ptr [shlarg2+2+4], 1
ifdef X64
mov dword ptr [shlbres+2], shlpreretval + 2+4 - shlbres2
mov dword ptr [shlbres2+2], shlxorretval + 2+4 - shlbret
else
mov dword ptr [shlbres+2], shlpreretval + 2+4
mov dword ptr [shlbres2+2], shlxorretval + 2+4
endif
mov dword ptr [shlbret+1], shlpreretval - shlbret - 5
jmp WriteExecSHL

shlpreretval: mov byte ptr [shlpreretval+6], 0
shlxorretval: mov byte ptr [shlarg+2], 0
ifdef X64
mov dword ptr [shlres+1+2], shlnzretval + 1 - shlret
else
mov dword ptr [shlres+1+2], shlnzretval + 1
endif
mov dword ptr [shlret+1], shlnzretval - shlret - 5
jmp WriteExecSHL1
shlnzretval: jmp $+8000h
jmp dosub
jmp nosub
dosub:

subremval1: mov byte ptr [div32_2_1+6], 0
subremval2: mov byte ptr [div32_2_2+6], 0
subremval3: mov byte ptr [div32_2_3+6], 0
subremval4copy: mov byte ptr [div32_2_4+6], 0

quotxor: mov byte ptr [xorarg1+6], 0
mov byte ptr [xorarg2+6], 1
ifdef X64
mov dword ptr [xorres+2], div32arg1_1 + 2+4 - xorret
else
mov dword ptr [xorres+2], div32arg1_1 + 2+4
endif
mov dword ptr [xorret+1], nosub - xorret - 5
jmp WriteExecXOR
nosub:

;; copy rem to shift left, low dword to result
ifdef X64
mov dword ptr [div32_2_1 + 2], shly1+6-div32_2_1-2-4-1
mov dword ptr [div32_2_2 + 2], shly2+6-div32_2_2-2-4-1
mov dword ptr [div32_2_3 + 2], shly3+6-div32_2_3-2-4-1
mov dword ptr [div32_2_4 + 2], shly4+6-div32_2_4-2-4-1
else
mov dword ptr [div32_2_1 + 2], shly1+6
mov dword ptr [div32_2_2 + 2], shly2+6
mov dword ptr [div32_2_3 + 2], shly3+6
mov dword ptr [div32_2_4 + 2], shly4+6
endif
mov byte ptr [divremlow1loop + 1], divremlow1head-divremlow1loop-2
jmp div32_2_1
divremlow1head: mov byte ptr [divremlow1loop+1], 0 ;exit loop
ifdef X64
mov dword ptr [div32_2_1 + 2], divrem1+6-div32_2_1-2-4-1
mov dword ptr [div32_2_2 + 2], divrem2+6-div32_2_2-2-4-1
mov dword ptr [div32_2_3 + 2], divrem3+6-div32_2_3-2-4-1
mov dword ptr [div32_2_4 + 2], divrem4+6-div32_2_4-2-4-1
else
mov dword ptr [div32_2_1 + 2], divrem1+6
mov dword ptr [div32_2_2 + 2], divrem2+6
mov dword ptr [div32_2_3 + 2], divrem3+6
mov dword ptr [div32_2_4 + 2], divrem4+6
endif
jmp div32_2_1 ; branch after patching code before executing it
div32_2_1: mov byte ptr [shly1+6], 0
div32_2_2: mov byte ptr [shly2+6], 0
div32_2_3: mov byte ptr [shly3+6], 0
div32_2_4: mov byte ptr [shly4+6], 0
divremlow1loop: jmp divremlow1head

jmp mainloop

exitmainloop:

divres1:: mov byte ptr [divres1+6], 0
divres2:: mov byte ptr [divres2+6], 0
divres3:: mov byte ptr [divres3+6], 0
divres4:: mov byte ptr [divres4+6], 0
divrem1:: mov byte ptr [divrem1+6], 0
divrem2:: mov byte ptr [divrem2+6], 0
divrem3:: mov byte ptr [divrem3+6], 0
divrem4:: mov byte ptr [divrem4+6], 0
div32ret:: jmp $+80000000h
WriteExecDIV32 ENDP

ifndef X64
WriteExecDIV32_C PROC div32_1arg: QWORD, div32_2arg: DWORD
mov ecx, dword ptr [div32_1arg]
mov edx, dword ptr [div32_2arg]
else
WriteExecDIV32_C PROC
endif
mov byte ptr [div32arg1_1+6], cl
mov byte ptr [div32arg2_1+6], dl
mov byte ptr [div32arg1_2+6], ch
mov byte ptr [div32arg2_2+6], dh
shr gcx, 16
shr edx, 16
mov byte ptr [div32arg1_3+6], cl
mov byte ptr [div32arg2_3+6], dl
mov byte ptr [div32arg1_4+6], ch
mov byte ptr [div32arg2_4+6], dh
ifndef X64
mov ecx, dword ptr [div32_1arg+4]
else
shr gcx, 16
endif
mov byte ptr [div32arg1_5+6], cl
mov byte ptr [div32arg1_6+6], ch
shr gcx, 16
mov byte ptr [div32arg1_7+6], cl
mov byte ptr [div32arg1_8+6], ch
ifdef X64
mov dword ptr [divres1+2], divretval + 1 - divres2
mov dword ptr [divres2+2], divretval + 2 - divres3
mov dword ptr [divres3+2], divretval + 3 - divres4
mov dword ptr [divres4+2], divretval + 4 - divrem1
else
mov dword ptr [divres1+2], divretval + 1
mov dword ptr [divres2+2], divretval + 2
mov dword ptr [divres3+2], divretval + 3
mov dword ptr [divres4+2], divretval + 4
endif
mov dword ptr [div32ret+1], divretval - div32ret - 5
jmp WriteExecDIV32
divretval: mov eax, 80000000h
ret
WriteExecDIV32_C ENDP

ifndef X64
WriteExecMOD32_C PROC div32_1arg: QWORD, div32_2arg: DWORD
mov ecx, dword ptr [div32_1arg]
mov edx, dword ptr [div32_2arg]
else
WriteExecMOD32_C PROC
endif
mov byte ptr [div32arg1_1+6], cl
mov byte ptr [div32arg2_1+6], dl
mov byte ptr [div32arg1_2+6], ch
mov byte ptr [div32arg2_2+6], dh
shr gcx, 16
shr edx, 16
mov byte ptr [div32arg1_3+6], cl
mov byte ptr [div32arg2_3+6], dl
mov byte ptr [div32arg1_4+6], ch
mov byte ptr [div32arg2_4+6], dh
ifndef X64
mov ecx, dword ptr [div32_1arg+4]
else
shr gcx, 16
endif
mov byte ptr [div32arg1_5+6], cl
mov byte ptr [div32arg1_6+6], ch
shr gcx, 16
mov byte ptr [div32arg1_7+6], cl
mov byte ptr [div32arg1_8+6], ch
ifdef X64
mov dword ptr [divrem1+2], divretval + 1 - divrem2
mov dword ptr [divrem2+2], divretval + 2 - divrem3
mov dword ptr [divrem3+2], divretval + 3 - divrem4
mov dword ptr [divrem4+2], divretval + 4 - div32ret
else
mov dword ptr [divrem1+2], divretval + 1
mov dword ptr [divrem2+2], divretval + 2
mov dword ptr [divrem3+2], divretval + 3
mov dword ptr [divrem4+2], divretval + 4
endif
mov dword ptr [div32ret+1], divretval - div32ret - 5
jmp WriteExecDIV32
divretval: mov eax, 80000000h
ret
WriteExecMOD32_C ENDP

WriteExecMODEXP32 PROC
mov byte ptr [modexpres1+6], 1
mov byte ptr [modexpres2+6], 0
mov byte ptr [modexpres3+6], 0
mov byte ptr [modexpres4+6], 0
mov byte ptr [modexprest1+6], 1
mov byte ptr [modexprest2+6], 0
mov byte ptr [modexprest3+6], 0
mov byte ptr [modexprest4+6], 0

ifdef X64
mov dword ptr [modexp32arg3_1 + 2], divmod1+6-modexp32arg3_1-2-4-1
mov dword ptr [modexp32arg3_2 + 2], divmod2+6-modexp32arg3_2-2-4-1
mov dword ptr [modexp32arg3_3 + 2], divmod3+6-modexp32arg3_3-2-4-1
mov dword ptr [modexp32arg3_4 + 2], divmod4+6-modexp32arg3_4-2-4-1
else
mov dword ptr [modexp32arg3_1 + 2], divmod1+6
mov dword ptr [modexp32arg3_2 + 2], divmod2+6
mov dword ptr [modexp32arg3_3 + 2], divmod3+6
mov dword ptr [modexp32arg3_4 + 2], divmod4+6
endif
mov byte ptr [divmodloop + 1], divmodhead-divmodloop-2
jmp modexp32arg3_1
divmodhead: mov byte ptr [divmodloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [modexp32arg3_1 + 2], divmod1copy+6-modexp32arg3_1-2-4-1
mov dword ptr [modexp32arg3_2 + 2], divmod2copy+6-modexp32arg3_2-2-4-1
mov dword ptr [modexp32arg3_3 + 2], divmod3copy+6-modexp32arg3_3-2-4-1
mov dword ptr [modexp32arg3_4 + 2], divmod4copy+6-modexp32arg3_4-2-4-1
else
mov dword ptr [modexp32arg3_1 + 2], divmod1copy+6
mov dword ptr [modexp32arg3_2 + 2], divmod2copy+6
mov dword ptr [modexp32arg3_3 + 2], divmod3copy+6
mov dword ptr [modexp32arg3_4 + 2], divmod4copy+6
endif
jmp modexp32arg3_1 ; branch after patching code before executing it
modexp32arg3_1:: mov byte ptr [divmod1+6], 0
modexp32arg3_2:: mov byte ptr [divmod2+6], 0
modexp32arg3_3:: mov byte ptr [divmod3+6], 0
modexp32arg3_4:: mov byte ptr [divmod4+6], 0
divmodloop: jmp divmodhead

mainloop:

ifdef X64
mov dword ptr [modexp32arg1_1 + 2], modbase1+6-modexp32arg1_1-2-4-1
mov dword ptr [modexp32arg1_2 + 2], modbase2+6-modexp32arg1_2-2-4-1
mov dword ptr [modexp32arg1_3 + 2], modbase3+6-modexp32arg1_3-2-4-1
mov dword ptr [modexp32arg1_4 + 2], modbase4+6-modexp32arg1_4-2-4-1
else
mov dword ptr [modexp32arg1_1 + 2], modbase1+6
mov dword ptr [modexp32arg1_2 + 2], modbase2+6
mov dword ptr [modexp32arg1_3 + 2], modbase3+6
mov dword ptr [modexp32arg1_4 + 2], modbase4+6
endif
mov byte ptr [baseloop + 1], basehead2-baseloop-2
jmp modexp32arg1_1
basehead2: mov byte ptr [baseloop+1], basehead-baseloop-2
ifdef X64
mov dword ptr [modexp32arg1_1 + 2], modbase1copy+6-modexp32arg1_1-2-4-1
mov dword ptr [modexp32arg1_2 + 2], modbase2copy+6-modexp32arg1_2-2-4-1
mov dword ptr [modexp32arg1_3 + 2], modbase3copy+6-modexp32arg1_3-2-4-1
mov dword ptr [modexp32arg1_4 + 2], modbase4copy+6-modexp32arg1_4-2-4-1
else
mov dword ptr [modexp32arg1_1 + 2], modbase1copy+6
mov dword ptr [modexp32arg1_2 + 2], modbase2copy+6
mov dword ptr [modexp32arg1_3 + 2], modbase3copy+6
mov dword ptr [modexp32arg1_4 + 2], modbase4copy+6
endif
jmp modexp32arg1_1
basehead: mov byte ptr [baseloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [modexp32arg1_1 + 2], modbase1copy2+6-modexp32arg1_1-2-4-1
mov dword ptr [modexp32arg1_2 + 2], modbase2copy2+6-modexp32arg1_2-2-4-1
mov dword ptr [modexp32arg1_3 + 2], modbase3copy2+6-modexp32arg1_3-2-4-1
mov dword ptr [modexp32arg1_4 + 2], modbase4copy2+6-modexp32arg1_4-2-4-1
else
mov dword ptr [modexp32arg1_1 + 2], modbase1copy2+6
mov dword ptr [modexp32arg1_2 + 2], modbase2copy2+6
mov dword ptr [modexp32arg1_3 + 2], modbase3copy2+6
mov dword ptr [modexp32arg1_4 + 2], modbase4copy2+6
endif
jmp modexp32arg1_1 ; branch after patching code before executing it
modexp32arg1_1:: mov byte ptr [modbase1+6], 0
modexp32arg1_2:: mov byte ptr [modbase2+6], 0
modexp32arg1_3:: mov byte ptr [modbase3+6], 0
modexp32arg1_4:: mov byte ptr [modbase4+6], 0
baseloop: jmp basehead

ifdef X64
mov dword ptr [modexp32arg2_1 + 2], modexp32arg2_1copy+6-modexp32arg2_1-2-4-1
else
mov dword ptr [modexp32arg2_1 + 2], modexp32arg2_1copy+6
endif
mov byte ptr [exp1loop + 1], exp1head-exp1loop-2
jmp modexp32arg2_1
exp1head: mov byte ptr [exp1loop+1], 0 ;exit loop
ifdef X64
mov dword ptr [modexp32arg2_1 + 2], yand+6-modexp32arg2_1-2-4-1
else
mov dword ptr [modexp32arg2_1 + 2], yand+6
endif
jmp modexp32arg2_1 ; branch after patching code before executing it
modexp32arg2_1:: mov byte ptr [modexp32arg2_1copy+6], 0
exp1loop: jmp exp1head

ifdef X64
mov dword ptr [modexp32arg2_1copy + 2], expshr1+6-modexp32arg2_1copy-2-4-1
mov dword ptr [modexp32arg2_2 + 2], expshr2+6-modexp32arg2_2-2-4-1
mov dword ptr [modexp32arg2_3 + 2], expshr3+6-modexp32arg2_3-2-4-1
mov dword ptr [modexp32arg2_4 + 2], expshr4+6-modexp32arg2_4-2-4-1
else
mov dword ptr [modexp32arg2_1copy + 2], expshr1+6
mov dword ptr [modexp32arg2_2 + 2], expshr2+6
mov dword ptr [modexp32arg2_3 + 2], expshr3+6
mov dword ptr [modexp32arg2_4 + 2], expshr4+6
endif
mov byte ptr [exploop + 1], exphead-exploop-2
jmp modexp32arg2_1copy
exphead: mov byte ptr [exploop+1], 0 ;exit loop
ifdef X64
mov dword ptr [modexp32arg2_1copy + 2], checky1+6-modexp32arg2_1copy-2-4-1
mov dword ptr [modexp32arg2_2 + 2], checky2+6-modexp32arg2_2-2-4-1
mov dword ptr [modexp32arg2_3 + 2], checky3+6-modexp32arg2_3-2-4-1
mov dword ptr [modexp32arg2_4 + 2], checky4+6-modexp32arg2_4-2-4-1
else
mov dword ptr [modexp32arg2_1copy + 2], checky1+6
mov dword ptr [modexp32arg2_2 + 2], checky2+6
mov dword ptr [modexp32arg2_3 + 2], checky3+6
mov dword ptr [modexp32arg2_4 + 2], checky4+6
endif
jmp modexp32arg2_1copy ; branch after patching code before executing it
modexp32arg2_1copy: mov byte ptr [expshr1+6], 0
modexp32arg2_2:: mov byte ptr [expshr2+6], 0
modexp32arg2_3:: mov byte ptr [expshr3+6], 0
modexp32arg2_4:: mov byte ptr [expshr4+6], 0
exploop: jmp exphead

IRP val, <1, 2, 3, 4>
checky&val&: mov byte ptr [nzarg+2+4], 0
ifdef X64	
mov dword ptr [nzres+2], nzretval&val& + 2+4 - nzret
else
mov dword ptr [nzres+2], nzretval&val& + 2+4
endif
mov dword ptr [nzret+1], nzretval&val& - nzret - 5
jmp WriteExecNZ
nzretval&val&: mov byte ptr [shlarg+2], 0
ifdef X64
mov dword ptr [shlres+1+2], shlretval&val& + 1 - shlret
else
mov dword ptr [shlres+1+2], shlretval&val& + 1
endif
mov dword ptr [shlret+1], checkyret&val& - shlret - 5
jmp WriteExecSHL1
checkyret&val&:
ENDM

shlretval1: jmp $+8000h
jmp shlretval2
jmp continueloop
shlretval2: jmp $+8000h
jmp shlretval3
jmp continueloop
shlretval3: jmp $+8000h
jmp shlretval4
jmp continueloop
shlretval4: jmp $+8000h
jmp exitloop
jmp continueloop
exitloop: jmp exitmainloop
continueloop:

;;y and 1
yand: mov byte ptr [andarg1+6], 0
mov byte ptr [andarg2+6], 1
ifdef X64
mov dword ptr [andres+2], andretval + 2+4 - andret
else
mov dword ptr [andres+2], andretval + 2+4
endif
mov dword ptr [andret+1], andretval - andret - 5
jmp WriteExecAND
;;check zero
andretval: mov byte ptr [shlarg+2], 0
ifdef X64
mov dword ptr [shlres+1+2], shlretval + 1 - shlret
else
mov dword ptr [shlres+1+2], shlretval + 1
endif
mov dword ptr [shlret+1], shlretval - shlret - 5
jmp WriteExecSHL1
shlretval: jmp $+8000h
jmp noaddfar
jmp doadd
noaddfar: jmp noadd
doadd:

modexprest1: mov byte ptr [mul32arg1_1+6], 0
modexprest2: mov byte ptr [mul32arg1_2+6], 0
modexprest3: mov byte ptr [mul32arg1_3+6], 0
modexprest4: mov byte ptr [mul32arg1_4+6], 0
modbase1: mov byte ptr [mul32arg2_1+6], 0
modbase2: mov byte ptr [mul32arg2_2+6], 0
modbase3: mov byte ptr [mul32arg2_3+6], 0
modbase4: mov byte ptr [mul32arg2_4+6], 0
ifdef X64
mov dword ptr [mulres1+2], mulretval1 + 2+4 - mulres2
mov dword ptr [mulres2+2], mulretval2 + 2+4 - mulres3
mov dword ptr [mulres3+2], mulretval3 + 2+4 - mulres4
mov dword ptr [mulres4+2], mulretval4 + 2+4 - mulres5
mov dword ptr [mulres5+2], mulretval5 + 2+4 - mulres6
mov dword ptr [mulres6+2], mulretval6 + 2+4 - mulres7
mov dword ptr [mulres7+2], mulretval7 + 2+4 - mulres8
mov dword ptr [mulres8+2], mulretval8 + 2+4 - mul32ret
else
mov dword ptr [mulres1+2], mulretval1 + 2+4
mov dword ptr [mulres2+2], mulretval2 + 2+4
mov dword ptr [mulres3+2], mulretval3 + 2+4
mov dword ptr [mulres4+2], mulretval4 + 2+4
mov dword ptr [mulres5+2], mulretval5 + 2+4
mov dword ptr [mulres6+2], mulretval6 + 2+4
mov dword ptr [mulres7+2], mulretval7 + 2+4
mov dword ptr [mulres8+2], mulretval8 + 2+4
endif
mov dword ptr [mul32ret+1], mulretval1 - mul32ret - 5
jmp WriteExecMUL32
mulretval1: mov byte ptr [div32arg1_1+6], 0
mulretval2: mov byte ptr [div32arg1_2+6], 0
mulretval3: mov byte ptr [div32arg1_3+6], 0
mulretval4: mov byte ptr [div32arg1_4+6], 0
mulretval5: mov byte ptr [div32arg1_5+6], 0
mulretval6: mov byte ptr [div32arg1_6+6], 0
mulretval7: mov byte ptr [div32arg1_7+6], 0
mulretval8: mov byte ptr [div32arg1_8+6], 0
divmod1: mov byte ptr [div32arg2_1+6], 0
divmod2: mov byte ptr [div32arg2_2+6], 0
divmod3: mov byte ptr [div32arg2_3+6], 0
divmod4: mov byte ptr [div32arg2_4+6], 0
ifdef X64
mov dword ptr [divrem1+2], divretval1 + 2+4 - divrem2
mov dword ptr [divrem2+2], divretval2 + 2+4 - divrem3
mov dword ptr [divrem3+2], divretval3 + 2+4 - divrem4
mov dword ptr [divrem4+2], divretval4 + 2+4 - div32ret
else
mov dword ptr [divrem1+2], divretval1 + 2+4
mov dword ptr [divrem2+2], divretval2 + 2+4
mov dword ptr [divrem3+2], divretval3 + 2+4
mov dword ptr [divrem4+2], divretval4 + 2+4
endif
mov dword ptr [div32ret+1], divafter - div32ret - 5
jmp WriteExecDIV32
divafter:

ifdef X64
mov dword ptr [divretval1 + 2], modexpres1+6-divretval1-2-4-1
mov dword ptr [divretval2 + 2], modexpres2+6-divretval2-2-4-1
mov dword ptr [divretval3 + 2], modexpres3+6-divretval3-2-4-1
mov dword ptr [divretval4 + 2], modexpres4+6-divretval4-2-4-1
else
mov dword ptr [divretval1 + 2], modexpres1+6
mov dword ptr [divretval2 + 2], modexpres2+6
mov dword ptr [divretval3 + 2], modexpres3+6
mov dword ptr [divretval4 + 2], modexpres4+6
endif
mov byte ptr [resloop + 1], reshead-resloop-2
jmp divretval1
reshead: mov byte ptr [resloop+1], 0 ;exit loop
ifdef X64
mov dword ptr [divretval1 + 2], modexprest1+6-divretval1-2-4-1
mov dword ptr [divretval2 + 2], modexprest2+6-divretval2-2-4-1
mov dword ptr [divretval3 + 2], modexprest3+6-divretval3-2-4-1
mov dword ptr [divretval4 + 2], modexprest4+6-divretval4-2-4-1
else
mov dword ptr [divretval1 + 2], modexprest1+6
mov dword ptr [divretval2 + 2], modexprest2+6
mov dword ptr [divretval3 + 2], modexprest3+6
mov dword ptr [divretval4 + 2], modexprest4+6
endif
jmp divretval1 ; branch after patching code before executing it
divretval1: mov byte ptr [modexpres1+2+4], 0
divretval2: mov byte ptr [modexpres2+2+4], 0
divretval3: mov byte ptr [modexpres3+2+4], 0
divretval4: mov byte ptr [modexpres4+2+4], 0
resloop: jmp reshead

noadd:

mov byte ptr [shr32arg2_1+6], 1
expshr1: mov byte ptr [shr32arg1_1+6], 0
expshr2: mov byte ptr [shr32arg1_2+6], 0
expshr3: mov byte ptr [shr32arg1_3+6], 0
expshr4: mov byte ptr [shr32arg1_4+6], 0
ifdef X64
mov dword ptr [shr32res1+2], modexp32arg2_1 + 2+4 - shr32res2
mov dword ptr [shr32res2+2], modexp32arg2_2 + 2+4 - shr32res3
mov dword ptr [shr32res3+2], modexp32arg2_3 + 2+4 - shr32res4
mov dword ptr [shr32res4+2], modexp32arg2_4 + 2+4 - shr32ret
else
mov dword ptr [shr32res1+2], modexp32arg2_1 + 2+4
mov dword ptr [shr32res2+2], modexp32arg2_2 + 2+4
mov dword ptr [shr32res3+2], modexp32arg2_3 + 2+4
mov dword ptr [shr32res4+2], modexp32arg2_4 + 2+4
endif
mov dword ptr [shr32ret+1], modbase1copy - shr32ret - 5
jmp WriteExecSHR32

modbase1copy: mov byte ptr [mul32arg1_1+6], 0
modbase2copy: mov byte ptr [mul32arg1_2+6], 0
modbase3copy: mov byte ptr [mul32arg1_3+6], 0
modbase4copy: mov byte ptr [mul32arg1_4+6], 0
modbase1copy2: mov byte ptr [mul32arg2_1+6], 0
modbase2copy2: mov byte ptr [mul32arg2_2+6], 0
modbase3copy2: mov byte ptr [mul32arg2_3+6], 0
modbase4copy2: mov byte ptr [mul32arg2_4+6], 0
ifdef X64
mov dword ptr [mulres1+2], bmulretval1 + 2+4 - mulres2
mov dword ptr [mulres2+2], bmulretval2 + 2+4 - mulres3
mov dword ptr [mulres3+2], bmulretval3 + 2+4 - mulres4
mov dword ptr [mulres4+2], bmulretval4 + 2+4 - mulres5
mov dword ptr [mulres5+2], bmulretval5 + 2+4 - mulres6
mov dword ptr [mulres6+2], bmulretval6 + 2+4 - mulres7
mov dword ptr [mulres7+2], bmulretval7 + 2+4 - mulres8
mov dword ptr [mulres8+2], bmulretval8 + 2+4 - mul32ret
else
mov dword ptr [mulres1+2], bmulretval1 + 2+4
mov dword ptr [mulres2+2], bmulretval2 + 2+4
mov dword ptr [mulres3+2], bmulretval3 + 2+4
mov dword ptr [mulres4+2], bmulretval4 + 2+4
mov dword ptr [mulres5+2], bmulretval5 + 2+4
mov dword ptr [mulres6+2], bmulretval6 + 2+4
mov dword ptr [mulres7+2], bmulretval7 + 2+4
mov dword ptr [mulres8+2], bmulretval8 + 2+4
endif
mov dword ptr [mul32ret+1], bmulretval1 - mul32ret - 5
jmp WriteExecMUL32
bmulretval1: mov byte ptr [div32arg1_1+6], 0
bmulretval2: mov byte ptr [div32arg1_2+6], 0
bmulretval3: mov byte ptr [div32arg1_3+6], 0
bmulretval4: mov byte ptr [div32arg1_4+6], 0
bmulretval5: mov byte ptr [div32arg1_5+6], 0
bmulretval6: mov byte ptr [div32arg1_6+6], 0
bmulretval7: mov byte ptr [div32arg1_7+6], 0
bmulretval8: mov byte ptr [div32arg1_8+6], 0
divmod1copy: mov byte ptr [div32arg2_1+6], 0
divmod2copy: mov byte ptr [div32arg2_2+6], 0
divmod3copy: mov byte ptr [div32arg2_3+6], 0
divmod4copy: mov byte ptr [div32arg2_4+6], 0
ifdef X64
mov dword ptr [divrem1+2], modexp32arg1_1 + 2+4 - divrem2
mov dword ptr [divrem2+2], modexp32arg1_2 + 2+4 - divrem3
mov dword ptr [divrem3+2], modexp32arg1_3 + 2+4 - divrem4
mov dword ptr [divrem4+2], modexp32arg1_4 + 2+4 - div32ret
else
mov dword ptr [divrem1+2], modexp32arg1_1 + 2+4
mov dword ptr [divrem2+2], modexp32arg1_2 + 2+4
mov dword ptr [divrem3+2], modexp32arg1_3 + 2+4
mov dword ptr [divrem4+2], modexp32arg1_4 + 2+4
endif
mov dword ptr [div32ret+1], mainloop - div32ret - 5
jmp WriteExecDIV32

exitmainloop:

modexpres1:: mov byte ptr [modexpres1+6], 0
modexpres2:: mov byte ptr [modexpres2+6], 0
modexpres3:: mov byte ptr [modexpres3+6], 0
modexpres4:: mov byte ptr [modexpres4+6], 0
modexp32ret:: jmp $+80000000h
WriteExecMODEXP32 ENDP

; Precondition: modulus >= 2 (the result register is initialised to 1 and never reduced,
; so a modulus of 1 yields 1 instead of 0). RSA moduli satisfy this.
ifndef X64
WriteExecMODEXP32_C PROC modexp32_1arg: DWORD, modexp32_2arg: DWORD, modexp32_3arg: DWORD
mov ecx, dword ptr [modexp32_1arg]
mov edx, dword ptr [modexp32_2arg]
mov eax, dword ptr [modexp32_3arg]
else
WriteExecMODEXP32_C PROC
mov rax, r8
endif
mov byte ptr [modexp32arg1_1+6], cl
mov byte ptr [modexp32arg2_1+6], dl
mov byte ptr [modexp32arg3_1+6], al
mov byte ptr [modexp32arg1_2+6], ch
mov byte ptr [modexp32arg2_2+6], dh
mov byte ptr [modexp32arg3_2+6], ah
shr ecx, 16
shr edx, 16
shr eax, 16
mov byte ptr [modexp32arg1_3+6], cl
mov byte ptr [modexp32arg2_3+6], dl
mov byte ptr [modexp32arg3_3+6], al
mov byte ptr [modexp32arg1_4+6], ch
mov byte ptr [modexp32arg2_4+6], dh
mov byte ptr [modexp32arg3_4+6], ah
ifdef X64
mov dword ptr [modexpres1+2], modexpretval + 1 - modexpres2
mov dword ptr [modexpres2+2], modexpretval + 2 - modexpres3
mov dword ptr [modexpres3+2], modexpretval + 3 - modexpres4
mov dword ptr [modexpres4+2], modexpretval + 4 - modexp32ret
else
mov dword ptr [modexpres1+2], modexpretval + 1
mov dword ptr [modexpres2+2], modexpretval + 2
mov dword ptr [modexpres3+2], modexpretval + 3
mov dword ptr [modexpres4+2], modexpretval + 4
endif
mov dword ptr [modexp32ret+1], modexpretval - modexp32ret - 5
jmp WriteExecMODEXP32
modexpretval: mov eax, 80000000h
ret
WriteExecMODEXP32_C ENDP






WriteExecTe0 PROC
te0arg:: mov byte ptr [shlarg6+2], 0
ifdef X64
mov dword ptr [shlres6+1+2], te0argshl + 1 - shlret6
else
mov dword ptr [shlres6+1+2], te0argshl + 1
endif
mov dword ptr [shlret6+1], te0argshl - shlret6 - 5
jmp WriteExecSHL6

te0argshl: jmp $+5+08000h
IRP t, <0c66363a5h, 0f87c7c84h, 0ee777799h, 0f67b7b8dh,\
	0fff2f20dh, 0d66b6bbdh, 0de6f6fb1h, 091c5c554h,\
	060303050h, 002010103h, 0ce6767a9h, 0562b2b7dh,\
	0e7fefe19h, 0b5d7d762h, 04dababe6h, 0ec76769ah>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <08fcaca45h, 01f82829dh, 089c9c940h, 0fa7d7d87h,\
	0effafa15h, 0b25959ebh, 08e4747c9h, 0fbf0f00bh,\
	041adadech, 0b3d4d467h, 05fa2a2fdh, 045afafeah,\
	0239c9cbfh, 053a4a4f7h, 0e4727296h, 09bc0c05bh>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <075b7b7c2h, 0e1fdfd1ch, 03d9393aeh, 04c26266ah,\
	06c36365ah, 07e3f3f41h, 0f5f7f702h, 083cccc4fh,\
	06834345ch, 051a5a5f4h, 0d1e5e534h, 0f9f1f108h,\
	0e2717193h, 0abd8d873h, 062313153h, 02a15153fh>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <00804040ch, 095c7c752h, 046232365h, 09dc3c35eh,\
	030181828h, 0379696a1h, 00a05050fh, 02f9a9ab5h,\
	00e070709h, 024121236h, 01b80809bh, 0dfe2e23dh,\
	0cdebeb26h, 04e272769h, 07fb2b2cdh, 0ea75759fh>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <01209091bh, 01d83839eh, 0582c2c74h, 0341a1a2eh,\
	0361b1b2dh, 0dc6e6eb2h, 0b45a5aeeh, 05ba0a0fbh,\
	0a45252f6h, 0763b3b4dh, 0b7d6d661h, 07db3b3ceh,\
	05229297bh, 0dde3e33eh, 05e2f2f71h, 013848497h>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <0a65353f5h, 0b9d1d168h, 000000000h, 0c1eded2ch,\
	040202060h, 0e3fcfc1fh, 079b1b1c8h, 0b65b5bedh,\
	0d46a6abeh, 08dcbcb46h, 067bebed9h, 07239394bh,\
	0944a4adeh, 0984c4cd4h, 0b05858e8h, 085cfcf4ah>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <0bbd0d06bh, 0c5efef2ah, 04faaaae5h, 0edfbfb16h,\
	0864343c5h, 09a4d4dd7h, 066333355h, 011858594h,\
	08a4545cfh, 0e9f9f910h, 004020206h, 0fe7f7f81h,\
	0a05050f0h, 0783c3c44h, 0259f9fbah, 04ba8a8e3h>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <0a25151f3h, 05da3a3feh, 0804040c0h, 0058f8f8ah,\
	03f9292adh, 0219d9dbch, 070383848h, 0f1f5f504h,\
	063bcbcdfh, 077b6b6c1h, 0afdada75h, 042212163h,\
	020101030h, 0e5ffff1ah, 0fdf3f30eh, 0bfd2d26dh>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <081cdcd4ch, 0180c0c14h, 026131335h, 0c3ecec2fh,\
	0be5f5fe1h, 0359797a2h, 0884444cch, 02e171739h,\
	093c4c457h, 055a7a7f2h, 0fc7e7e82h, 07a3d3d47h,\
	0c86464ach, 0ba5d5de7h, 03219192bh, 0e6737395h>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <0c06060a0h, 019818198h, 09e4f4fd1h, 0a3dcdc7fh,\
	044222266h, 0542a2a7eh, 03b9090abh, 00b888883h,\
	08c4646cah, 0c7eeee29h, 06bb8b8d3h, 02814143ch,\
	0a7dede79h, 0bc5e5ee2h, 0160b0b1dh, 0addbdb76h>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <0dbe0e03bh, 064323256h, 0743a3a4eh, 0140a0a1eh,\
	0924949dbh, 00c06060ah, 04824246ch, 0b85c5ce4h,\
	09fc2c25dh, 0bdd3d36eh, 043acacefh, 0c46262a6h,\
	0399191a8h, 0319595a4h, 0d3e4e437h, 0f279798bh>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <0d5e7e732h, 08bc8c843h, 06e373759h, 0da6d6db7h,\
	0018d8d8ch, 0b1d5d564h, 09c4e4ed2h, 049a9a9e0h,\
	0d86c6cb4h, 0ac5656fah, 0f3f4f407h, 0cfeaea25h,\
	0ca6565afh, 0f47a7a8eh, 047aeaee9h, 010080818h>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <06fbabad5h, 0f0787888h, 04a25256fh, 05c2e2e72h,\
	0381c1c24h, 057a6a6f1h, 073b4b4c7h, 097c6c651h,\
	0cbe8e823h, 0a1dddd7ch, 0e874749ch, 03e1f1f21h,\
	0964b4bddh, 061bdbddch, 00d8b8b86h, 00f8a8a85h>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <0e0707090h, 07c3e3e42h, 071b5b5c4h, 0cc6666aah,\
	0904848d8h, 006030305h, 0f7f6f601h, 01c0e0e12h,\
	0c26161a3h, 06a35355fh, 0ae5757f9h, 069b9b9d0h,\
	017868691h, 099c1c158h, 03a1d1d27h, 0279e9eb9h>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <0d9e1e138h, 0ebf8f813h, 02b9898b3h, 022111133h,\
	0d26969bbh, 0a9d9d970h, 0078e8e89h, 0339494a7h,\
	02d9b9bb6h, 03c1e1e22h, 015878792h, 0c9e9e920h,\
	087cece49h, 0aa5555ffh, 050282878h, 0a5dfdf7ah>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <0038c8c8fh, 059a1a1f8h, 009898980h, 01a0d0d17h,\
	065bfbfdah, 0d7e6e631h, 0844242c6h, 0d06868b8h,\
	0824141c3h, 0299999b0h, 05a2d2d77h, 01e0f0f11h,\
	07bb0b0cbh, 0a85454fch>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 31 dup (090h)
ENDM
IRP t, <06dbbbbd6h, 02c16163ah>
	mov byte ptr [te0res1 + 2 + 4], t and 0ffh
	mov byte ptr [te0res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te0res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te0res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te0res1
	db 34 dup (090h)
ENDM

te0res1:: mov byte ptr [te0res1 + 2 + 4], 0
te0res2:: mov byte ptr [te0res2 + 2 + 4], 0
te0res3:: mov byte ptr [te0res3 + 2 + 4], 0
te0res4:: mov byte ptr [te0res4 + 2 + 4], 0
te0ret:: jmp $+80000000h
WriteExecTe0 ENDP

ifndef X64
WriteExecTe0_C PROC te0_1arg: BYTE
mov cl, byte ptr [te0_1arg]
else
WriteExecTe0_C PROC
endif
mov byte ptr [te0arg+2+4], cl
ifdef X64
mov dword ptr [te0res1+2], te0retval + 1 - te0res2
mov dword ptr [te0res2+2], te0retval + 2 - te0res3
mov dword ptr [te0res3+2], te0retval + 3 - te0res4
mov dword ptr [te0res4+2], te0retval + 4 - te0ret
else
mov dword ptr [te0res1+2], te0retval + 1
mov dword ptr [te0res2+2], te0retval + 2
mov dword ptr [te0res3+2], te0retval + 3
mov dword ptr [te0res4+2], te0retval + 4
endif
mov dword ptr [te0ret+1], te0retval - te0ret - 5
jmp WriteExecTe0
te0retval: mov eax, 80000000h
ret
WriteExecTe0_C ENDP

WriteExecTe1 PROC
te1arg:: mov byte ptr [shlarg6+2], 0
ifdef X64
mov dword ptr [shlres6+1+2], te1argshl + 1 - shlret6
else
mov dword ptr [shlres6+1+2], te1argshl + 1
endif
mov dword ptr [shlret6+1], te1argshl - shlret6 - 5
jmp WriteExecSHL6

te1argshl: jmp $+5+08000h
IRP t, <0a5c66363h, 084f87c7ch, 099ee7777h, 08df67b7bh,\
	00dfff2f2h, 0bdd66b6bh, 0b1de6f6fh, 05491c5c5h,\
	050603030h, 003020101h, 0a9ce6767h, 07d562b2bh,\
	019e7fefeh, 062b5d7d7h, 0e64dababh, 09aec7676h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <0458fcacah, 09d1f8282h, 04089c9c9h, 087fa7d7dh,\
	015effafah, 0ebb25959h, 0c98e4747h, 00bfbf0f0h,\
	0ec41adadh, 067b3d4d4h, 0fd5fa2a2h, 0ea45afafh,\
	0bf239c9ch, 0f753a4a4h, 096e47272h, 05b9bc0c0h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <0c275b7b7h, 01ce1fdfdh, 0ae3d9393h, 06a4c2626h,\
	05a6c3636h, 0417e3f3fh, 002f5f7f7h, 04f83cccch,\
	05c683434h, 0f451a5a5h, 034d1e5e5h, 008f9f1f1h,\
	093e27171h, 073abd8d8h, 053623131h, 03f2a1515h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <00c080404h, 05295c7c7h, 065462323h, 05e9dc3c3h,\
	028301818h, 0a1379696h, 00f0a0505h, 0b52f9a9ah,\
	0090e0707h, 036241212h, 09b1b8080h, 03ddfe2e2h,\
	026cdebebh, 0694e2727h, 0cd7fb2b2h, 09fea7575h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <01b120909h, 09e1d8383h, 074582c2ch, 02e341a1ah,\
	02d361b1bh, 0b2dc6e6eh, 0eeb45a5ah, 0fb5ba0a0h,\
	0f6a45252h, 04d763b3bh, 061b7d6d6h, 0ce7db3b3h,\
	07b522929h, 03edde3e3h, 0715e2f2fh, 097138484h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <0f5a65353h, 068b9d1d1h, 000000000h, 02cc1ededh,\
	060402020h, 01fe3fcfch, 0c879b1b1h, 0edb65b5bh,\
	0bed46a6ah, 0468dcbcbh, 0d967bebeh, 04b723939h,\
	0de944a4ah, 0d4984c4ch, 0e8b05858h, 04a85cfcfh>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <06bbbd0d0h, 02ac5efefh, 0e54faaaah, 016edfbfbh,\
	0c5864343h, 0d79a4d4dh, 055663333h, 094118585h,\
	0cf8a4545h, 010e9f9f9h, 006040202h, 081fe7f7fh,\
	0f0a05050h, 044783c3ch, 0ba259f9fh, 0e34ba8a8h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <0f3a25151h, 0fe5da3a3h, 0c0804040h, 08a058f8fh,\
	0ad3f9292h, 0bc219d9dh, 048703838h, 004f1f5f5h,\
	0df63bcbch, 0c177b6b6h, 075afdadah, 063422121h,\
	030201010h, 01ae5ffffh, 00efdf3f3h, 06dbfd2d2h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <04c81cdcdh, 014180c0ch, 035261313h, 02fc3ecech,\
	0e1be5f5fh, 0a2359797h, 0cc884444h, 0392e1717h,\
	05793c4c4h, 0f255a7a7h, 082fc7e7eh, 0477a3d3dh,\
	0acc86464h, 0e7ba5d5dh, 02b321919h, 095e67373h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <0a0c06060h, 098198181h, 0d19e4f4fh, 07fa3dcdch,\
	066442222h, 07e542a2ah, 0ab3b9090h, 0830b8888h,\
	0ca8c4646h, 029c7eeeeh, 0d36bb8b8h, 03c281414h,\
	079a7dedeh, 0e2bc5e5eh, 01d160b0bh, 076addbdbh>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <03bdbe0e0h, 056643232h, 04e743a3ah, 01e140a0ah,\
	0db924949h, 00a0c0606h, 06c482424h, 0e4b85c5ch,\
	05d9fc2c2h, 06ebdd3d3h, 0ef43acach, 0a6c46262h,\
	0a8399191h, 0a4319595h, 037d3e4e4h, 08bf27979h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <032d5e7e7h, 0438bc8c8h, 0596e3737h, 0b7da6d6dh,\
	08c018d8dh, 064b1d5d5h, 0d29c4e4eh, 0e049a9a9h,\
	0b4d86c6ch, 0faac5656h, 007f3f4f4h, 025cfeaeah,\
	0afca6565h, 08ef47a7ah, 0e947aeaeh, 018100808h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <0d56fbabah, 088f07878h, 06f4a2525h, 0725c2e2eh,\
	024381c1ch, 0f157a6a6h, 0c773b4b4h, 05197c6c6h,\
	023cbe8e8h, 07ca1ddddh, 09ce87474h, 0213e1f1fh,\
	0dd964b4bh, 0dc61bdbdh, 0860d8b8bh, 0850f8a8ah>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <090e07070h, 0427c3e3eh, 0c471b5b5h, 0aacc6666h,\
	0d8904848h, 005060303h, 001f7f6f6h, 0121c0e0eh,\
	0a3c26161h, 05f6a3535h, 0f9ae5757h, 0d069b9b9h,\
	091178686h, 05899c1c1h, 0273a1d1dh, 0b9279e9eh>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <038d9e1e1h, 013ebf8f8h, 0b32b9898h, 033221111h,\
	0bbd26969h, 070a9d9d9h, 089078e8eh, 0a7339494h,\
	0b62d9b9bh, 0223c1e1eh, 092158787h, 020c9e9e9h,\
	04987ceceh, 0ffaa5555h, 078502828h, 07aa5dfdfh>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <08f038c8ch, 0f859a1a1h, 080098989h, 0171a0d0dh,\
	0da65bfbfh, 031d7e6e6h, 0c6844242h, 0b8d06868h,\
	0c3824141h, 0b0299999h, 0775a2d2dh, 0111e0f0fh,\
	0cb7bb0b0h, 0fca85454h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 31 dup (090h)
ENDM
IRP t, <0d66dbbbbh, 03a2c1616h>
	mov byte ptr [te1res1 + 2 + 4], t and 0ffh
	mov byte ptr [te1res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te1res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te1res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te1res1
	db 34 dup (090h)
ENDM
te1res1:: mov byte ptr [te1res1 + 2 + 4], 0
te1res2:: mov byte ptr [te1res2 + 2 + 4], 0
te1res3:: mov byte ptr [te1res3 + 2 + 4], 0
te1res4:: mov byte ptr [te1res4 + 2 + 4], 0
te1ret:: jmp $+80000000h
WriteExecTe1 ENDP

ifndef X64
WriteExecTe1_C PROC te1_1arg: BYTE
mov cl, byte ptr [te1_1arg]
else
WriteExecTe1_C PROC
endif
mov byte ptr [te1arg+2+4], cl
ifdef X64
mov dword ptr [te1res1+2], te1retval + 1 - te1res2
mov dword ptr [te1res2+2], te1retval + 2 - te1res3
mov dword ptr [te1res3+2], te1retval + 3 - te1res4
mov dword ptr [te1res4+2], te1retval + 4 - te1ret
else
mov dword ptr [te1res1+2], te1retval + 1
mov dword ptr [te1res2+2], te1retval + 2
mov dword ptr [te1res3+2], te1retval + 3
mov dword ptr [te1res4+2], te1retval + 4
endif
mov dword ptr [te1ret+1], te1retval - te1ret - 5
jmp WriteExecTe1
te1retval: mov eax, 80000000h
ret
WriteExecTe1_C ENDP

WriteExecTe2 PROC
te2arg:: mov byte ptr [shlarg6+2], 0
ifdef X64
mov dword ptr [shlres6+1+2], te2argshl + 1 - shlret6
else
mov dword ptr [shlres6+1+2], te2argshl + 1
endif
mov dword ptr [shlret6+1], te2argshl - shlret6 - 5
jmp WriteExecSHL6

te2argshl: jmp $+5+08000h
IRP t, <063a5c663h, 07c84f87ch, 07799ee77h, 07b8df67bh,\
	0f20dfff2h, 06bbdd66bh, 06fb1de6fh, 0c55491c5h,\
	030506030h, 001030201h, 067a9ce67h, 02b7d562bh,\
	0fe19e7feh, 0d762b5d7h, 0abe64dabh, 0769aec76h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <0ca458fcah, 0829d1f82h, 0c94089c9h, 07d87fa7dh,\
	0fa15effah, 059ebb259h, 047c98e47h, 0f00bfbf0h,\
	0adec41adh, 0d467b3d4h, 0a2fd5fa2h, 0afea45afh,\
	09cbf239ch, 0a4f753a4h, 07296e472h, 0c05b9bc0h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <0b7c275b7h, 0fd1ce1fdh, 093ae3d93h, 0266a4c26h,\
	0365a6c36h, 03f417e3fh, 0f702f5f7h, 0cc4f83cch,\
	0345c6834h, 0a5f451a5h, 0e534d1e5h, 0f108f9f1h,\
	07193e271h, 0d873abd8h, 031536231h, 0153f2a15h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
	;db 6 dup (090h)
	;db 0e9h
	;dd offset te2res-4-$
ENDM
IRP t, <0040c0804h, 0c75295c7h, 023654623h, 0c35e9dc3h,\
	018283018h, 096a13796h, 0050f0a05h, 09ab52f9ah,\
	007090e07h, 012362412h, 0809b1b80h, 0e23ddfe2h,\
	0eb26cdebh, 027694e27h, 0b2cd7fb2h, 0759fea75h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <0091b1209h, 0839e1d83h, 02c74582ch, 01a2e341ah,\
	01b2d361bh, 06eb2dc6eh, 05aeeb45ah, 0a0fb5ba0h,\
	052f6a452h, 03b4d763bh, 0d661b7d6h, 0b3ce7db3h,\
	0297b5229h, 0e33edde3h, 02f715e2fh, 084971384h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <053f5a653h, 0d168b9d1h, 000000000h, 0ed2cc1edh,\
	020604020h, 0fc1fe3fch, 0b1c879b1h, 05bedb65bh,\
	06abed46ah, 0cb468dcbh, 0bed967beh, 0394b7239h,\
	04ade944ah, 04cd4984ch, 058e8b058h, 0cf4a85cfh>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <0d06bbbd0h, 0ef2ac5efh, 0aae54faah, 0fb16edfbh,\
	043c58643h, 04dd79a4dh, 033556633h, 085941185h,\
	045cf8a45h, 0f910e9f9h, 002060402h, 07f81fe7fh,\
	050f0a050h, 03c44783ch, 09fba259fh, 0a8e34ba8h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <051f3a251h, 0a3fe5da3h, 040c08040h, 08f8a058fh,\
	092ad3f92h, 09dbc219dh, 038487038h, 0f504f1f5h,\
	0bcdf63bch, 0b6c177b6h, 0da75afdah, 021634221h,\
	010302010h, 0ff1ae5ffh, 0f30efdf3h, 0d26dbfd2h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <0cd4c81cdh, 00c14180ch, 013352613h, 0ec2fc3ech,\
	05fe1be5fh, 097a23597h, 044cc8844h, 017392e17h,\
	0c45793c4h, 0a7f255a7h, 07e82fc7eh, 03d477a3dh,\
	064acc864h, 05de7ba5dh, 0192b3219h, 07395e673h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <060a0c060h, 081981981h, 04fd19e4fh, 0dc7fa3dch,\
	022664422h, 02a7e542ah, 090ab3b90h, 088830b88h,\
	046ca8c46h, 0ee29c7eeh, 0b8d36bb8h, 0143c2814h,\
	0de79a7deh, 05ee2bc5eh, 00b1d160bh, 0db76addbh>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <0e03bdbe0h, 032566432h, 03a4e743ah, 00a1e140ah,\
	049db9249h, 0060a0c06h, 0246c4824h, 05ce4b85ch,\
	0c25d9fc2h, 0d36ebdd3h, 0acef43ach, 062a6c462h,\
	091a83991h, 095a43195h, 0e437d3e4h, 0798bf279h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <0e732d5e7h, 0c8438bc8h, 037596e37h, 06db7da6dh,\
	08d8c018dh, 0d564b1d5h, 04ed29c4eh, 0a9e049a9h,\
	06cb4d86ch, 056faac56h, 0f407f3f4h, 0ea25cfeah,\
	065afca65h, 07a8ef47ah, 0aee947aeh, 008181008h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <0bad56fbah, 07888f078h, 0256f4a25h, 02e725c2eh,\
	01c24381ch, 0a6f157a6h, 0b4c773b4h, 0c65197c6h,\
	0e823cbe8h, 0dd7ca1ddh, 0749ce874h, 01f213e1fh,\
	04bdd964bh, 0bddc61bdh, 08b860d8bh, 08a850f8ah>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <07090e070h, 03e427c3eh, 0b5c471b5h, 066aacc66h,\
	048d89048h, 003050603h, 0f601f7f6h, 00e121c0eh,\
	061a3c261h, 0355f6a35h, 057f9ae57h, 0b9d069b9h,\
	086911786h, 0c15899c1h, 01d273a1dh, 09eb9279eh>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <0e138d9e1h, 0f813ebf8h, 098b32b98h, 011332211h,\
	069bbd269h, 0d970a9d9h, 08e89078eh, 094a73394h,\
	09bb62d9bh, 01e223c1eh, 087921587h, 0e920c9e9h,\
	0ce4987ceh, 055ffaa55h, 028785028h, 0df7aa5dfh>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <08c8f038ch, 0a1f859a1h, 089800989h, 00d171a0dh,\
	0bfda65bfh, 0e631d7e6h, 042c68442h, 068b8d068h,\
	041c38241h, 099b02999h, 02d775a2dh, 00f111e0fh,\
	0b0cb7bb0h, 054fca854h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 31 dup (090h)
ENDM
IRP t, <0bbd66dbbh, 0163a2c16h>
	mov byte ptr [te2res1 + 2 + 4], t and 0ffh
	mov byte ptr [te2res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te2res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te2res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te2res1
	db 34 dup (090h)
ENDM
te2res1:: mov byte ptr [te2res1 + 2 + 4], 0
te2res2:: mov byte ptr [te2res2 + 2 + 4], 0
te2res3:: mov byte ptr [te2res3 + 2 + 4], 0
te2res4:: mov byte ptr [te2res4 + 2 + 4], 0
te2ret:: jmp $+80000000h
WriteExecTe2 ENDP

ifndef X64
WriteExecTe2_C PROC te2_1arg: BYTE
mov cl, byte ptr [te2_1arg]
else
WriteExecTe2_C PROC
endif
mov byte ptr [te2arg+2+4], cl
ifdef X64
mov dword ptr [te2res1+2], te2retval + 1 - te2res2
mov dword ptr [te2res2+2], te2retval + 2 - te2res3
mov dword ptr [te2res3+2], te2retval + 3 - te2res4
mov dword ptr [te2res4+2], te2retval + 4 - te2ret
else
mov dword ptr [te2res1+2], te2retval + 1
mov dword ptr [te2res2+2], te2retval + 2
mov dword ptr [te2res3+2], te2retval + 3
mov dword ptr [te2res4+2], te2retval + 4
endif
mov dword ptr [te2ret+1], te2retval - te2ret - 5
jmp WriteExecTe2
te2retval: mov eax, 80000000h
ret
WriteExecTe2_C ENDP

WriteExecTe3 PROC
te3arg:: mov byte ptr [shlarg6+2], 0
ifdef X64
mov dword ptr [shlres6+1+2], te3argshl + 1 - shlret6
else
mov dword ptr [shlres6+1+2], te3argshl + 1
endif
mov dword ptr [shlret6+1], te3argshl - shlret6 - 5
jmp WriteExecSHL6

te3argshl: jmp $+5+08000h
IRP t, <06363a5c6h, 07c7c84f8h, 0777799eeh, 07b7b8df6h,\
	0f2f20dffh, 06b6bbdd6h, 06f6fb1deh, 0c5c55491h,\
	030305060h, 001010302h, 06767a9ceh, 02b2b7d56h,\
	0fefe19e7h, 0d7d762b5h, 0ababe64dh, 076769aech>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <0caca458fh, 082829d1fh, 0c9c94089h, 07d7d87fah,\
	0fafa15efh, 05959ebb2h, 04747c98eh, 0f0f00bfbh,\
	0adadec41h, 0d4d467b3h, 0a2a2fd5fh, 0afafea45h,\
	09c9cbf23h, 0a4a4f753h, 0727296e4h, 0c0c05b9bh>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <0b7b7c275h, 0fdfd1ce1h, 09393ae3dh, 026266a4ch,\
	036365a6ch, 03f3f417eh, 0f7f702f5h, 0cccc4f83h,\
	034345c68h, 0a5a5f451h, 0e5e534d1h, 0f1f108f9h,\
	0717193e2h, 0d8d873abh, 031315362h, 015153f2ah>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <004040c08h, 0c7c75295h, 023236546h, 0c3c35e9dh,\
	018182830h, 09696a137h, 005050f0ah, 09a9ab52fh,\
	00707090eh, 012123624h, 080809b1bh, 0e2e23ddfh,\
	0ebeb26cdh, 02727694eh, 0b2b2cd7fh, 075759feah>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <009091b12h, 083839e1dh, 02c2c7458h, 01a1a2e34h,\
	01b1b2d36h, 06e6eb2dch, 05a5aeeb4h, 0a0a0fb5bh,\
	05252f6a4h, 03b3b4d76h, 0d6d661b7h, 0b3b3ce7dh,\
	029297b52h, 0e3e33eddh, 02f2f715eh, 084849713h>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <05353f5a6h, 0d1d168b9h, 000000000h, 0eded2cc1h,\
	020206040h, 0fcfc1fe3h, 0b1b1c879h, 05b5bedb6h,\
	06a6abed4h, 0cbcb468dh, 0bebed967h, 039394b72h,\
	04a4ade94h, 04c4cd498h, 05858e8b0h, 0cfcf4a85h>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <0d0d06bbbh, 0efef2ac5h, 0aaaae54fh, 0fbfb16edh,\
	04343c586h, 04d4dd79ah, 033335566h, 085859411h,\
	04545cf8ah, 0f9f910e9h, 002020604h, 07f7f81feh,\
	05050f0a0h, 03c3c4478h, 09f9fba25h, 0a8a8e34bh>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <05151f3a2h, 0a3a3fe5dh, 04040c080h, 08f8f8a05h,\
	09292ad3fh, 09d9dbc21h, 038384870h, 0f5f504f1h,\
	0bcbcdf63h, 0b6b6c177h, 0dada75afh, 021216342h,\
	010103020h, 0ffff1ae5h, 0f3f30efdh, 0d2d26dbfh>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <0cdcd4c81h, 00c0c1418h, 013133526h, 0ecec2fc3h,\
	05f5fe1beh, 09797a235h, 04444cc88h, 01717392eh,\
	0c4c45793h, 0a7a7f255h, 07e7e82fch, 03d3d477ah,\
	06464acc8h, 05d5de7bah, 019192b32h, 0737395e6h>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <06060a0c0h, 081819819h, 04f4fd19eh, 0dcdc7fa3h,\
	022226644h, 02a2a7e54h, 09090ab3bh, 08888830bh,\
	04646ca8ch, 0eeee29c7h, 0b8b8d36bh, 014143c28h,\
	0dede79a7h, 05e5ee2bch, 00b0b1d16h, 0dbdb76adh>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <0e0e03bdbh, 032325664h, 03a3a4e74h, 00a0a1e14h,\
	04949db92h, 006060a0ch, 024246c48h, 05c5ce4b8h,\
	0c2c25d9fh, 0d3d36ebdh, 0acacef43h, 06262a6c4h,\
	09191a839h, 09595a431h, 0e4e437d3h, 079798bf2h>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <0e7e732d5h, 0c8c8438bh, 03737596eh, 06d6db7dah,\
	08d8d8c01h, 0d5d564b1h, 04e4ed29ch, 0a9a9e049h,\
	06c6cb4d8h, 05656faach, 0f4f407f3h, 0eaea25cfh,\
	06565afcah, 07a7a8ef4h, 0aeaee947h, 008081810h>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <0babad56fh, 0787888f0h, 025256f4ah, 02e2e725ch,\
	01c1c2438h, 0a6a6f157h, 0b4b4c773h, 0c6c65197h,\
	0e8e823cbh, 0dddd7ca1h, 074749ce8h, 01f1f213eh,\
	04b4bdd96h, 0bdbddc61h, 08b8b860dh, 08a8a850fh>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <0707090e0h, 03e3e427ch, 0b5b5c471h, 06666aacch,\
	04848d890h, 003030506h, 0f6f601f7h, 00e0e121ch,\
	06161a3c2h, 035355f6ah, 05757f9aeh, 0b9b9d069h,\
	086869117h, 0c1c15899h, 01d1d273ah, 09e9eb927h>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <0e1e138d9h, 0f8f813ebh, 09898b32bh, 011113322h,\
	06969bbd2h, 0d9d970a9h, 08e8e8907h, 09494a733h,\
	09b9bb62dh, 01e1e223ch, 087879215h, 0e9e920c9h,\
	0cece4987h, 05555ffaah, 028287850h, 0dfdf7aa5h>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <08c8c8f03h, 0a1a1f859h, 089898009h, 00d0d171ah,\
	0bfbfda65h, 0e6e631d7h, 04242c684h, 06868b8d0h,\
	04141c382h, 09999b029h, 02d2d775ah, 00f0f111eh,\
	0b0b0cb7bh, 05454fca8h>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 31 dup (090h)
ENDM
IRP t, <0bbbbd66dh, 016163a2ch>
	mov byte ptr [te3res1 + 2 + 4], t and 0ffh
	mov byte ptr [te3res2 + 2 + 4], (t shr 8) and 0ffh
	mov byte ptr [te3res3 + 2 + 4], (t shr 16) and 0ffh
	mov byte ptr [te3res4 + 2 + 4], (t shr 24) and 0ffh
	jmp te3res1
	db 34 dup (090h)
ENDM
te3res1:: mov byte ptr [te3res1 + 2 + 4], 0
te3res2:: mov byte ptr [te3res2 + 2 + 4], 0
te3res3:: mov byte ptr [te3res3 + 2 + 4], 0
te3res4:: mov byte ptr [te3res4 + 2 + 4], 0
te3ret:: jmp $+80000000h
WriteExecTe3 ENDP

ifndef X64
WriteExecTe3_C PROC te3_1arg: BYTE
mov cl, byte ptr [te3_1arg]
else
WriteExecTe3_C PROC
endif
mov byte ptr [te3arg+2+4], cl
ifdef X64
mov dword ptr [te3res1+2], te3retval + 1 - te3res2
mov dword ptr [te3res2+2], te3retval + 2 - te3res3
mov dword ptr [te3res3+2], te3retval + 3 - te3res4
mov dword ptr [te3res4+2], te3retval + 4 - te3ret
else
mov dword ptr [te3res1+2], te3retval + 1
mov dword ptr [te3res2+2], te3retval + 2
mov dword ptr [te3res3+2], te3retval + 3
mov dword ptr [te3res4+2], te3retval + 4
endif
mov dword ptr [te3ret+1], te3retval - te3ret - 5
jmp WriteExecTe3
te3retval: mov eax, 80000000h
ret
WriteExecTe3_C ENDP

WriteExecTe4 PROC
te4arg:: mov byte ptr [shlarg4+2], 0
ifdef X64
mov dword ptr [shlres4+1+2], te4argshl + 1 - shlret4
else
mov dword ptr [shlres4+1+2], te4argshl + 1
endif
mov dword ptr [shlret4+1], te4argshl - shlret4 - 5
jmp WriteExecSHL4

te4argshl: jmp $+5+08000h
IRP t, <063636363h, 07c7c7c7ch, 077777777h, 07b7b7b7bh,\
	0f2f2f2f2h, 06b6b6b6bh, 06f6f6f6fh, 0c5c5c5c5h,\
	030303030h, 001010101h, 067676767h, 02b2b2b2bh,\
	0fefefefeh, 0d7d7d7d7h, 0ababababh, 076767676h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <0cacacacah, 082828282h, 0c9c9c9c9h, 07d7d7d7dh,\
	0fafafafah, 059595959h, 047474747h, 0f0f0f0f0h,\
	0adadadadh, 0d4d4d4d4h, 0a2a2a2a2h, 0afafafafh,\
	09c9c9c9ch, 0a4a4a4a4h, 072727272h, 0c0c0c0c0h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <0b7b7b7b7h, 0fdfdfdfdh, 093939393h, 026262626h,\
	036363636h, 03f3f3f3fh, 0f7f7f7f7h, 0cccccccch,\
	034343434h, 0a5a5a5a5h, 0e5e5e5e5h, 0f1f1f1f1h,\
	071717171h, 0d8d8d8d8h, 031313131h, 015151515h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <004040404h, 0c7c7c7c7h, 023232323h, 0c3c3c3c3h,\
	018181818h, 096969696h, 005050505h, 09a9a9a9ah,\
	007070707h, 012121212h, 080808080h, 0e2e2e2e2h,\
	0ebebebebh, 027272727h, 0b2b2b2b2h, 075757575h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <009090909h, 083838383h, 02c2c2c2ch, 01a1a1a1ah,\
	01b1b1b1bh, 06e6e6e6eh, 05a5a5a5ah, 0a0a0a0a0h,\
	052525252h, 03b3b3b3bh, 0d6d6d6d6h, 0b3b3b3b3h,\
	029292929h, 0e3e3e3e3h, 02f2f2f2fh, 084848484h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <053535353h, 0d1d1d1d1h, 000000000h, 0ededededh,\
	020202020h, 0fcfcfcfch, 0b1b1b1b1h, 05b5b5b5bh,\
	06a6a6a6ah, 0cbcbcbcbh, 0bebebebeh, 039393939h,\
	04a4a4a4ah, 04c4c4c4ch, 058585858h, 0cfcfcfcfh>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <0d0d0d0d0h, 0efefefefh, 0aaaaaaaah, 0fbfbfbfbh,\
	043434343h, 04d4d4d4dh, 033333333h, 085858585h,\
	045454545h, 0f9f9f9f9h, 002020202h, 07f7f7f7fh,\
	050505050h, 03c3c3c3ch, 09f9f9f9fh, 0a8a8a8a8h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <051515151h, 0a3a3a3a3h, 040404040h, 08f8f8f8fh,\
	092929292h, 09d9d9d9dh, 038383838h, 0f5f5f5f5h,\
	0bcbcbcbch, 0b6b6b6b6h, 0dadadadah, 021212121h,\
	010101010h, 0ffffffffh, 0f3f3f3f3h, 0d2d2d2d2h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <0cdcdcdcdh, 00c0c0c0ch, 013131313h, 0ecececech,\
	05f5f5f5fh, 097979797h, 044444444h, 017171717h,\
	0c4c4c4c4h, 0a7a7a7a7h, 07e7e7e7eh, 03d3d3d3dh,\
	064646464h, 05d5d5d5dh, 019191919h, 073737373h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <060606060h, 081818181h, 04f4f4f4fh, 0dcdcdcdch,\
	022222222h, 02a2a2a2ah, 090909090h, 088888888h,\
	046464646h, 0eeeeeeeeh, 0b8b8b8b8h, 014141414h,\
	0dedededeh, 05e5e5e5eh, 00b0b0b0bh, 0dbdbdbdbh>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <0e0e0e0e0h, 032323232h, 03a3a3a3ah, 00a0a0a0ah,\
	049494949h, 006060606h, 024242424h, 05c5c5c5ch,\
	0c2c2c2c2h, 0d3d3d3d3h, 0acacacach, 062626262h,\
	091919191h, 095959595h, 0e4e4e4e4h, 079797979h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <0e7e7e7e7h, 0c8c8c8c8h, 037373737h, 06d6d6d6dh,\
	08d8d8d8dh, 0d5d5d5d5h, 04e4e4e4eh, 0a9a9a9a9h,\
	06c6c6c6ch, 056565656h, 0f4f4f4f4h, 0eaeaeaeah,\
	065656565h, 07a7a7a7ah, 0aeaeaeaeh, 008080808h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <0babababah, 078787878h, 025252525h, 02e2e2e2eh,\
	01c1c1c1ch, 0a6a6a6a6h, 0b4b4b4b4h, 0c6c6c6c6h,\
	0e8e8e8e8h, 0ddddddddh, 074747474h, 01f1f1f1fh,\
	04b4b4b4bh, 0bdbdbdbdh, 08b8b8b8bh, 08a8a8a8ah>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <070707070h, 03e3e3e3eh, 0b5b5b5b5h, 066666666h,\
	048484848h, 003030303h, 0f6f6f6f6h, 00e0e0e0eh,\
	061616161h, 035353535h, 057575757h, 0b9b9b9b9h,\
	086868686h, 0c1c1c1c1h, 01d1d1d1dh, 09e9e9e9eh>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <0e1e1e1e1h, 0f8f8f8f8h, 098989898h, 011111111h,\
	069696969h, 0d9d9d9d9h, 08e8e8e8eh, 094949494h,\
	09b9b9b9bh, 01e1e1e1eh, 087878787h, 0e9e9e9e9h,\
	0cecececeh, 055555555h, 028282828h, 0dfdfdfdfh>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <08c8c8c8ch, 0a1a1a1a1h, 089898989h, 00d0d0d0dh,\
	0bfbfbfbfh, 0e6e6e6e6h, 042424242h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 4 dup (090h)
ENDM
IRP t, <068686868h,\
	041414141h, 099999999h, 02d2d2d2dh, 00f0f0f0fh,\
	0b0b0b0b0h, 054545454h, 0bbbbbbbbh, 016161616h>
	mov byte ptr [te4res + 2 + 4], t and 0ffh
	jmp te4res
	db 7 dup (090h)
ENDM
te4res:: mov byte ptr [te4res + 2 + 4], 0
te4ret:: jmp $+80000000h
WriteExecTe4 ENDP

ifndef X64
WriteExecTe4_C PROC te4_1arg: BYTE
mov cl, byte ptr [te4_1arg]
else
WriteExecTe4_C PROC
endif
mov byte ptr [te4arg+2+4], cl
ifdef X64
mov dword ptr [te4res+2], te4retval + 1 - te4ret
else
mov dword ptr [te4res+2], te4retval + 1
endif
mov dword ptr [te4ret+1], te4retval - te4ret - 5
jmp WriteExecTe4
te4retval: mov al, 0
ret
WriteExecTe4_C ENDP

AESINIT macro val, nval, rval
aesinp&val&:: mov byte ptr [xorarg1+6], 0
aeskey1_&rval&:: mov byte ptr [xorarg2+6], 0
ifdef X64
mov dword ptr [xorres+2], aesr2_&nval& + 2+4 - xorret
else
mov dword ptr [xorres+2], aesr2_&nval& + 2+4
endif
mov dword ptr [xorret+1], aesnarg&val& - xorret - 5
jmp WriteExecXOR
aesnarg&val&:
ENDM

AESXORMIX macro val, kval, roval, bval, nval, rval, krval, remval, keyval
aesr&val&te&kval&_&roval&_&remval&: mov byte ptr [xorarg1+6], 0
if kval EQ 0
aeskey&val&_&keyval&::
else
aesr&val&mix&roval&_&bval&:
endif
mov byte ptr [xorarg2+6], 0
ifdef X64
if kval EQ 3
mov dword ptr [xorres+2], aesr&rval&_&nval& + 2+4 - xorret
else
mov dword ptr [xorres+2], aesr&val&mix&roval&_&krval& + 2+4 - xorret
endif
else
if kval EQ 3
mov dword ptr [xorres+2], aesr&rval&_&nval& + 2+4
else
mov dword ptr [xorres+2], aesr&val&mix&roval&_&krval& + 2+4
endif
endif
mov dword ptr [xorret+1], aesnarg&val&_&roval&_&bval& - xorret - 5
jmp WriteExecXOR
aesnarg&val&_&roval&_&bval&:
ENDM

AESTABLE macro val, kval, rval, mval
aesr&val&_&mval&: mov byte ptr [te&kval&arg+2+4], 0
ifdef X64
mov dword ptr [te&kval&res1+2], aesr&val&te&kval&_&rval&_1 + 2+4 - te&kval&res2
mov dword ptr [te&kval&res2+2], aesr&val&te&kval&_&rval&_2 + 2+4 - te&kval&res3
mov dword ptr [te&kval&res3+2], aesr&val&te&kval&_&rval&_3 + 2+4 - te&kval&res4
mov dword ptr [te&kval&res4+2], aesr&val&te&kval&_&rval&_4 + 2+4 - te&kval&ret
else
mov dword ptr [te&kval&res1+2], aesr&val&te&kval&_&rval&_1 + 2+4
mov dword ptr [te&kval&res2+2], aesr&val&te&kval&_&rval&_2 + 2+4
mov dword ptr [te&kval&res3+2], aesr&val&te&kval&_&rval&_3 + 2+4
mov dword ptr [te&kval&res4+2], aesr&val&te&kval&_&rval&_4 + 2+4
endif
mov dword ptr [te&kval&ret+1], _&val&te&mval&retval - te&kval&ret - 5
jmp WriteExecTe&kval&
_&val&te&mval&retval:
ENDM

AESFIN macro val, rval
aeskey11_&rval&:: mov byte ptr [xorarg1+6], 0
aesr11te4_&val&:: mov byte ptr [xorarg2+6], 0
ifdef X64
mov dword ptr [xorres+2], aesres&val& + 2+4 - xorret
else
mov dword ptr [xorres+2], aesres&val& + 2+4
endif
mov dword ptr [xorret+1], res&val& - xorret - 5
jmp WriteExecXOR
res&val&:
ENDM

WriteExecAESLookup PROC

;;mapping: 3, 6, 9, 12, 7, 10, 13, 0, 11, 14, 1, 4, 15, 2, 5, 8
;;formula: (1+((val * 3 - ((val / 4) mod 2) * 8) mod 16))
;;also could view as: 0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11
;;formula (1+(((val-1) * 5) mod 16))
IRP val, <1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16>
AESINIT val, %(1+(((17-val) * 3) mod 16)), %((((val-1) / 4) * 4) + 5-(((val - 1) mod 4) + 1))
ENDM

IRP val, <2, 3, 4, 5, 6, 7, 8, 9, 10>

IRP rval, <1, 2, 3, 4>
IRP kval, <0, 1, 2, 3>
AESTABLE val, kval, rval, %((rval-1)*4+kval+1)
ENDM

IRP bval, <1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16>
q = (((rval - 1) * 4) + ((bval - 1) mod 4) + 1)
qq = (((rval - 1) * 4) + 5-(((bval - 1) mod 4) + 1))
;;inverse mapping: 0, 13, 10, 7, 4, 1, 14, 11, 8, 5, 2, 15, 12, 9, 6, 3
;;formula: (1+(((17-val) * 3) mod 16))
AESXORMIX val, %((bval - 1) / 4), rval, bval, %(1+(((17-qq) * 3) mod 16)), %(val+1), %(bval + 4), %(((bval - 1) mod 4) + 1), %q
ENDM
ENDM

ENDM

IRP val, <1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16>
aesr11_&val&: mov byte ptr [te4arg+2+4], 0
ifdef X64
mov dword ptr [te4res+2], aesr11te4_&val& + 2+4 - te4ret
else
mov dword ptr [te4res+2], aesr11te4_&val& + 2+4
endif
mov dword ptr [te4ret+1], r11te4_&val& - te4ret - 5
jmp WriteExecTe4
r11te4_&val&:
ENDM

IRP val, <1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16>
AESFIN val, %((((val-1) / 4) * 4) + 5-(((val - 1) mod 4) + 1))
ENDM

IRP val, <1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16>
aesres&val&:: mov byte ptr [aesres&val&+6], 0
ENDM

aesret:: jmp $+80000000h
WriteExecAESLookup ENDP

ifndef X64
WriteExecAESLookup_C PROC aes1arg: DWORD, aes2arg: DWORD, aes3arg: DWORD
mov ecx, dword ptr [aes1arg]
mov edx, dword ptr [aes3arg]
gcx textequ <ecx>
gdx textequ <edx>
_aes3arg textequ <edx>
else
WriteExecAESLookup_C PROC
;aes1arg textequ <rcx>
;aes2arg textequ <rdx>
_aes3arg textequ <r8>
gcx textequ <rcx>
gdx textequ <rdx>
endif
IRP val, <1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11>
IRP rval, <1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16>
mov al, byte ptr [_aes3arg+(val-1)*16+rval-1]
mov byte ptr [aeskey&val&_&rval&+2+4], al
ENDM
ENDM

ifndef X64
mov edx, dword ptr [aes2arg]
endif

IRP val, <1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16>
mov al, byte ptr [gcx+val-1]
mov byte ptr [aesinp&val&+2+4], al
ENDM
ifdef X64
mov dword ptr [aesres1+2], aesretval1 + 2 - aesres2
mov dword ptr [aesres2+2], aesretval1 + 3 - aesres3
mov dword ptr [aesres3+2], aesretval1 + 4 - aesres4
mov dword ptr [aesres4+2], aesretval1 + 5 - aesres5
mov dword ptr [aesres5+2], aesretval2 + 3 - aesres6
mov dword ptr [aesres6+2], aesretval2 + 4 - aesres7
mov dword ptr [aesres7+2], aesretval2 + 5 - aesres8
mov dword ptr [aesres8+2], aesretval2 + 6 - aesres9
mov dword ptr [aesres9+2], aesretval3 + 3 - aesres10
mov dword ptr [aesres10+2], aesretval3 + 4 - aesres11
mov dword ptr [aesres11+2], aesretval3 + 5 - aesres12
mov dword ptr [aesres12+2], aesretval3 + 6 - aesres13
mov dword ptr [aesres13+2], aesretval4 + 3 - aesres14
mov dword ptr [aesres14+2], aesretval4 + 4 - aesres15
mov dword ptr [aesres15+2], aesretval4 + 5 - aesres16
mov dword ptr [aesres16+2], aesretval4 + 6 - aesret
else
mov dword ptr [aesres1+2], aesretval1 + 2
mov dword ptr [aesres2+2], aesretval1 + 3
mov dword ptr [aesres3+2], aesretval1 + 4
mov dword ptr [aesres4+2], aesretval1 + 5
mov dword ptr [aesres5+2], aesretval2 + 3
mov dword ptr [aesres6+2], aesretval2 + 4
mov dword ptr [aesres7+2], aesretval2 + 5
mov dword ptr [aesres8+2], aesretval2 + 6
mov dword ptr [aesres9+2], aesretval3 + 3
mov dword ptr [aesres10+2], aesretval3 + 4
mov dword ptr [aesres11+2], aesretval3 + 5
mov dword ptr [aesres12+2], aesretval3 + 6
mov dword ptr [aesres13+2], aesretval4 + 3
mov dword ptr [aesres14+2], aesretval4 + 4
mov dword ptr [aesres15+2], aesretval4 + 5
mov dword ptr [aesres16+2], aesretval4 + 6
endif
mov dword ptr [aesret+1], aesretval1 - aesret - 5
jmp WriteExecAESLookup
aesretval1: mov dword ptr [gdx], 80000000h
aesretval2: mov dword ptr [gdx+4], 80000000h
aesretval3: mov dword ptr [gdx+8], 80000000h
aesretval4: mov dword ptr [gdx+12], 80000000h
ret
WriteExecAESLookup_C ENDP

END
