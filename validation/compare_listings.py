"""Evidence (not proof): the bytes the Lean byte model assigns to the NOT/NZ/SHL4 table entries and to the
fixed `iX`/`i3`/`iN` instructions equal the `.text` bytes of the COFF objects assembled by ml/ml64 from
the published (`lst`, tags x86/x64) and the corrected (`lstc`, tags x86c/x64c) `writeexc.asm`.
Run: python validation/limited_run.py -- python validation/compare_listings.py
Requires validation/.build/{lst,lstc}/{x86,x64}.obj (see validation/README.md) and built oleans."""
import json, subprocess, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import build_modules as B
import struct
from extract_layout import text_bytes

def relocated_text(obj):
    """`.text` of a COFF object with the x86 absolute relocations (DIR32) applied for B0 = 0:
    the stored addend plus the section offset of the target symbol (all targets are in `.text`)."""
    d = Path(obj).read_bytes(); n = struct.unpack_from("<H", d, 2)[0]; opt = struct.unpack_from("<H", d, 16)[0]
    symptr, nsym = struct.unpack_from("<II", d, 8)
    text = None
    for i in range(n):
        o = 20 + opt + 40 * i; name = d[o:o+8].rstrip(b"\0")
        size, ptr = struct.unpack_from("<II", d, o + 16); relptr, _, nrel = struct.unpack_from("<IIH", d, o + 24)
        if name == b".text" or name.startswith(b".text"):
            text = bytearray(d[ptr:ptr+size]); rel = (relptr, nrel); sect = i + 1
            if struct.unpack_from("<I", d, o + 36)[0] & 0x01000000:   # IMAGE_SCN_LNK_NRELOC_OVFL: real count in the first record
                rel = (relptr + 10, struct.unpack_from("<I", d, relptr)[0] - 1)
            break
    machine = struct.unpack_from("<H", d, 0)[0]
    for k in range(rel[1]):
        va, si, ty = struct.unpack_from("<IIH", d, rel[0] + 10 * k)
        sym = symptr + 18 * si; value, secnum = struct.unpack_from("<IH", d, sym + 8)
        if machine == 0x14c and ty == 6:      # I386 DIR32
            assert secnum == sect, "relocation target outside .text"
            cur = struct.unpack_from("<I", text, va)[0]; struct.pack_into("<I", text, va, (cur + value) & 0xFFFFFFFF)
        elif machine == 0x8664 and 4 <= ty <= 9:   # AMD64 REL32, REL32_1 .. REL32_5: distance to the end of the instruction
            assert secnum == sect, "relocation target outside .text"
            cur = struct.unpack_from("<I", text, va)[0]
            struct.pack_into("<I", text, va, (cur + value - (va + 4 + (ty - 4))) & 0xFFFFFFFF)
        elif machine == 0x14c and ty == 20:   # I386 REL32 (not expected)
            raise SystemExit("unexpected REL32 relocation")
    return bytes(text), rel[1]
ROOT = B.ROOT
def main():
    src = ROOT / "validation/compare_dump.lean"
    r = subprocess.run([str(B.BIN / "lean.exe"), str(src)], cwd=B.LEAN, capture_output=True, text=True, encoding="utf-8", errors="replace",
                       env={**__import__("os").environ, "LEAN_PATH": str(B.OUT)})
    if r.returncode: print(r.stdout[-3000:], r.stderr[-3000:]); sys.exit("lean failed")
    objs = {}
    for tag, d, arch in (("x86", "lst", "x86"), ("x64", "lst", "x64"), ("x86c", "lstc", "x86"), ("x64c", "lstc", "x64")):
        objs[tag], nrel = relocated_text(ROOT / "validation/.build" / d / f"{arch}.obj"); print(tag, "text bytes", len(objs[tag]), "relocations applied", nrel)
    n = bad = 0; per = {}
    for line in r.stdout.splitlines():
        parts = line.split()
        if len(parts) != 4: continue
        tag, kind, addr, hexs = parts[0], parts[1], int(parts[2]), parts[3]
        want = bytes.fromhex(hexs); got = objs[tag][addr:addr + len(want)]
        n += 1; per[(tag, kind)] = per.get((tag, kind), 0) + 1
        if got != want:
            bad += 1
            if bad <= 12: print("MISMATCH", tag, kind, addr, "lean", hexs, "coff", got.hex())
    print(json.dumps({f"{t}/{k}": c for (t, k), c in sorted(per.items())}))
    print(f"compared {n} Lean-encoded byte strings with the COFF .text; mismatches: {bad}")
    sys.exit(1 if bad or n == 0 else 0)
main()
