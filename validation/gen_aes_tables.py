"""Recompute the AES S-box algebraically and check it against lean/WriteExecute/Spec/AESData.lean.

Usage: python validation/gen_aes_tables.py   (exit 1 on mismatch)
The Te0..Te4 literals in AESData.lean were extracted from writeexc.asm (IRP lists) and compared with
the static tables of spectreopt.c; here they are re-derived from the S-box and MixColumns constants.
"""
import re, sys, pathlib

def xtime(x): return ((x << 1) ^ (0x1b if x & 0x80 else 0)) & 0xff
def gmul(a, b):
    r = 0
    for _ in range(8):
        if b & 1: r ^= a
        a = xtime(a); b >>= 1
    return r
def sbox(x):
    b = 1
    for _ in range(254): b = gmul(x, b)
    rot = lambda v, n: ((v << n) | (v >> (8 - n))) & 0xff
    return b ^ rot(b, 1) ^ rot(b, 2) ^ rot(b, 3) ^ rot(b, 4) ^ 0x63

src = (pathlib.Path(__file__).parent.parent / "lean/WriteExecute/Spec/AESData.lean").read_text(encoding="utf-8")
def lst(name):
    m = re.search(r"def %s : List Nat :=\s*\[([^\]]*)\]" % name, src)
    return [int(v) for v in m.group(1).split(",")]

S = [sbox(x) for x in range(256)]
ok = lst("sboxTab") == S
col = [2, 1, 1, 3]
mul = lambda c, a: a if c == 1 else xtime(a) if c == 2 else xtime(a) ^ a
for k in range(4):
    te = [sum(mul(col[(r + 4 - k) % 4], S[x]) << (8 * (3 - r)) for r in range(4)) for x in range(256)]
    ok &= lst("litTe%d" % k) == te
ok &= lst("litTe4") == [s * 0x01010101 for s in S]
print("AES tables", "OK" if ok else "MISMATCH")
sys.exit(0 if ok else 1)
