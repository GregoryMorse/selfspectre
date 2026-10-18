"""Audit expanded MASM code stores against a linked image's 64-byte boundaries.

Usage: python validation/listing_patch_alignment.py <writeexc.lst> <writeexc.obj> <edge_vectors.map>
Generate the listing with /Sa (validation/run_listings.py). The listing and object
must come from identical assembly source; the anchor check rejects stale pairs.
This is layout evidence, not a diagnosis of any native mismatch.
"""
import re
import subprocess
import sys
from pathlib import Path

from patch_alignment import find_dumpbin


def main(listing: Path, obj: Path, map_file: Path) -> None:
    symbols = {}
    output = subprocess.check_output([find_dumpbin(), "/symbols", str(obj)], text=True, errors="replace")
    symbol_re = re.compile(r"\b([0-9A-F]{8}) SECT1\s+.*\|\s+(\w+)\s*$")
    for line in output.splitlines():
        match = symbol_re.search(line)
        if match:
            symbols[match.group(2)] = int(match.group(1), 16)

    anchor = "_WriteExecDIV32_C" if "_WriteExecDIV32_C" in symbols else "WriteExecDIV32_C"
    map_text = map_file.read_text(errors="replace")
    map_match = re.search(r"\b0001:([0-9A-Fa-f]{8})\s+" + re.escape(anchor) + r"\b", map_text)
    if not map_match or anchor not in symbols:
        raise ValueError("DIV32_C anchor missing from object or linker map")
    shift = int(map_match.group(1), 16) - symbols[anchor]

    address_re = re.compile(r"\s*([0-9A-Fa-f]{8})\b")
    store_re = re.compile(r"\bmov\s+(byte|word|dword)\s+ptr\s+\[\s*([A-Za-z_]\w*)((?:\s*\+\s*\d+)*)\s*\]", re.I)
    sites = {}
    instructions = 0
    listing_anchor = None
    with listing.open(errors="replace") as lines:
        for line in lines:
            address = address_re.match(line)
            if not address:
                continue
            if re.search(r"\bWriteExecDIV32_C PROC\b", line):
                listing_anchor = int(address.group(1), 16)
            store = store_re.search(line)
            if not store:
                continue
            instructions += 1
            offset = sum(map(int, re.findall(r"\d+", store.group(3))))
            width = {"byte": 1, "word": 2, "dword": 4}[store.group(1).lower()]
            sites[(store.group(2), offset, width)] = line.strip()

    if listing_anchor != symbols[anchor]:
        raise ValueError(f"stale listing: DIV32_C offset {listing_anchor!r} differs from object {symbols[anchor]:#x}")
    unresolved = sorted({label for label, _, _ in sites if label not in symbols})
    if unresolved:
        raise ValueError(f"{len(unresolved)} patch targets not found in object symbols: {unresolved[:10]}")

    crossing = []
    for (label, offset, width), source in sites.items():
        rva = symbols[label] + offset + shift
        if rva % 64 + width > 64:
            crossing.append((rva, label, offset, width, source))
    print(f"{obj.name}: {instructions} expanded stores, {len(sites)} distinct fields; "
          f"{len(crossing)} cross a 64-byte line in this link")
    for rva, label, offset, width, _ in sorted(crossing):
        print(f"  {label}+{offset}: RVA 0x{rva:08x}, {width} bytes, line offset {rva % 64}")
    print("Crossing is a linked-layout fact, not a diagnosis of a transient mismatch.")


if __name__ == "__main__":
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    main(*(Path(arg) for arg in sys.argv[1:]))
