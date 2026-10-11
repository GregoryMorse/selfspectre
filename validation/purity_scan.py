"""Purity scan: linear-sweep decode of every non-'_C' WriteExec* PROC from the COFF .text bytes using
only the forms {C6 05 d32 i8, 66 C7 05 d32 i16, C7 05 d32 i32, E9 rel32, EB rel8, 90}.
Anything else (registers, stack, ret, calls, reads) is reported. Needs validation/.build/lst from extract_layout setup."""
import json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from extract_layout import text_bytes, B, ROOT
BODY = re.compile(r"^\s*([0-9A-F]{8})\s+(WriteExec\w+)\s+(PROC|ENDP)")
def procs(lst):
    """name -> (start, length) from PROC/ENDP lines of the listing body (the symbol table's Length= wraps at 64K)."""
    starts, out = {}, {}
    with open(lst, encoding="latin-1") as f:
        for line in f:
            m = BODY.match(line)
            if not m: continue
            if m.group(3) == "PROC": starts[m.group(2)] = int(m.group(1), 16)
            elif m.group(2) in starts: out[m.group(2)] = (starts[m.group(2)], int(m.group(1), 16) - starts[m.group(2)])
    return out
def decode(t, o):
    b = t[o]
    if b == 0x90: return 1, "nop"
    if b == 0xE9: return 5, "jmp32"
    if b == 0xEB: return 2, "jmp8"
    if b == 0xC6 and t[o+1] == 0x05: return 7, "mov8"
    if b == 0x66 and t[o+1] == 0xC7 and t[o+2] == 0x05: return 9, "mov16"
    if b == 0xC7 and t[o+1] == 0x05: return 10, "mov32"
    return 0, None
def main():
    report = {}; ok = True
    for arch in ("x86", "x64"):
        t = text_bytes(B / f"{arch}.obj"); ps = procs(B / f"{arch}.lst")
        core = {n: r for n, r in ps.items() if not n.endswith("_C")}
        counts = {}; bad = []
        for n, (start, length) in sorted(core.items(), key=lambda kv: kv[1][0]):
            o, end = start, start + length
            while o < end:
                size, kind = decode(t, o)
                if not size: bad.append((n, hex(o), t[o:o+4].hex())); break
                counts[kind] = counts.get(kind, 0) + 1; o += size
            else:
                if o != end: bad.append((n, hex(o), "overran proc end"))
        report[arch] = {"core_procs": len(core), "wrapper_procs": len(ps) - len(core), "instructions": counts, "violations": bad[:20], "n_violations": len(bad)}
        ok &= not bad
    (ROOT / "validation/layout/purity.json").write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps(report, indent=1)); sys.exit(0 if ok else 1)
if __name__ == "__main__": main()
