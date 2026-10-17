# Writes a copy of a MASM source adjusted for UASM (invoked with -DIN=<source> -DOUT=<copy> -P). The repository's
# source stays byte-identical to the original; the adjustments only make two byte-sized operand expressions explicit,
# which ml/ml64 already accept as such:
#   - DEFINENOT: "not Index" is a byte value, but UASM evaluates it as a wider constant;
#   - the displacement "basehead2-baseloop-2" (a forward label difference) is not known to fit a byte in UASM's
#     first pass.
file(READ ${IN} text)
string(REPLACE "mov byte ptr [Lbl+6], not Index" "mov byte ptr [Lbl+6], (not Index) and 0ffh" text "${text}")
string(REPLACE "mov byte ptr [baseloop + 1], basehead2-baseloop-2" "mov byte ptr [baseloop + 1], (basehead2-baseloop-2) and 0ffh" text "${text}")
# spectrecode.asm (x64): "and <64-bit register>, 0ff000000h" is encoded by ml64 as the sign-extended imm32; UASM wants
# that 64-bit value written out.
if(WE_X64)
  string(REPLACE "and acmltr, 0ff000000h" "and acmltr, 0ffffffffff000000h" text "${text}")
endif()
file(WRITE ${OUT} "${text}")
