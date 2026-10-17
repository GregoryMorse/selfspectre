# Writes a copy of a MASM source adjusted for UASM (invoked with -DIN=<source> -DOUT=<copy> -P). The repository's
# source stays byte-identical to the original; the adjustments only make two byte-sized operand expressions explicit,
# which ml/ml64 already accept as such:
#   - DEFINENOT: "not Index" is a byte value, but UASM evaluates it as a wider constant;
#   - the displacement "basehead2-baseloop-2" (a forward label difference) is not known to fit a byte in UASM's
#     first pass.
file(READ ${IN} text)
string(REPLACE "mov byte ptr [Lbl+6], not Index" "mov byte ptr [Lbl+6], (not Index) and 0ffh" text "${text}")
string(REPLACE "mov byte ptr [baseloop + 1], basehead2-baseloop-2" "mov byte ptr [baseloop + 1], (basehead2-baseloop-2) and 0ffh" text "${text}")
file(WRITE ${OUT} "${text}")
