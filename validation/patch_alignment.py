"""Report MASM code patches that cross a 64-byte line in a linked MSVC harness.

Usage: python validation/patch_alignment.py <writeexc.obj> <edge_vectors.map>
The report is diagnostic, not a pass/fail test: crossing a line does not prove
that an observed transient result came from a torn instruction fetch.
"""
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def find_dumpbin():
    explicit = os.environ.get("DUMPBIN")
    if explicit:
        return explicit
    on_path = shutil.which("dumpbin")
    if on_path:
        return on_path
    vswhere = Path(os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")) / "Microsoft Visual Studio/Installer/vswhere.exe"
    install = subprocess.check_output([str(vswhere), "-latest", "-property", "installationPath"], text=True).strip()
    candidates = sorted(Path(install).glob("VC/Tools/MSVC/*/bin/Hostx64/x64/dumpbin.exe"))
    if not candidates:
        raise FileNotFoundError("dumpbin.exe was not found; set DUMPBIN")
    return str(candidates[-1])


def patch_sites():
    source = (ROOT / "src/writeexc.asm").read_text(encoding="utf-8")
    sites = {}
    for size_name, width in (("byte", 1), ("word", 2), ("dword", 4)):
        for expr in re.findall(r"\bmov\s+" + size_name + r"\s+ptr\s+\[([^]]+)\]", source, re.I):
            parts = [part.strip() for part in expr.split("+")]
            if len(parts) < 2 or not re.fullmatch(r"[A-Za-z_]\w*", parts[0]):
                continue
            if not all(re.fullmatch(r"\d+", part) for part in parts[1:]):
                continue
            sites[(parts[0], sum(map(int, parts[1:])), width)] = expr
    return sites


def analyze(obj, map_file):
    symbol_text = subprocess.check_output([find_dumpbin(), "/symbols", str(obj)], text=True, errors="replace")
    symbols = {}
    for line in symbol_text.splitlines():
        match = re.search(r"\b([0-9A-F]{8}) SECT1\s+.*\|\s+(\w+)\s*$", line)
        if match:
            symbols[match.group(2)] = int(match.group(1), 16)

    anchor = "_WriteExecDIV32_C" if "_WriteExecDIV32_C" in symbols else "WriteExecDIV32_C"
    map_text = map_file.read_text(errors="replace")
    match = re.search(r"\b0001:([0-9a-fA-F]{8})\s+" + re.escape(anchor) + r"\b", map_text)
    if not match or anchor not in symbols:
        raise ValueError("DIV32_C anchor missing from object or linker map")
    text_shift = int(match.group(1), 16) - symbols[anchor]

    matched, crossing = 0, []
    for (label, offset, width), expr in patch_sites().items():
        if label not in symbols:
            continue
        matched += 1
        linked_offset = symbols[label] + offset + text_shift
        if linked_offset % 64 + width > 64:
            crossing.append((expr, linked_offset, width))
    print(f"{obj.name}: {matched} statically resolved patch fields; {len(crossing)} cross a 64-byte line in this link")
    for expr, linked_offset, width in crossing:
        print(f"  {expr}: RVA 0x{linked_offset:08x}, {width} bytes, line offset {linked_offset % 64}")
    print("Crossing is a linked-layout fact, not a diagnosis of a transient mismatch.")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    analyze(Path(sys.argv[1]), Path(sys.argv[2]))
