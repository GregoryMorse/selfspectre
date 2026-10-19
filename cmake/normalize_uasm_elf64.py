"""Remove UASM's duplicated in-place addends from ELF64 RELA PC32 fields.

UASM 2.57 writes the expression offset into both the relocation addend and
the four bytes being relocated. GNU ld applies both, so `[label+N]` reaches
`label+2*N`. This is fatal for Write-Execute's code-patch destinations.
ELF32 uses REL relocations with an in-place addend and must not be changed.
"""

import argparse
import struct
from pathlib import Path


ELF_HEADER = struct.Struct("<16sHHIQQQIHHHHHH")
SECTION_HEADER = struct.Struct("<IIQQQQIIQQ")
RELA = struct.Struct("<QQq")
SHT_RELA = 4
SHT_NOBITS = 8
R_X86_64_PC32 = 2


def normalize(path: Path) -> tuple[int, int]:
    data = bytearray(path.read_bytes())
    if len(data) < ELF_HEADER.size:
        raise ValueError("truncated ELF header")
    (ident, e_type, machine, _version, _entry, _phoff, shoff, _flags,
     _ehsize, _phentsize, _phnum, shentsize, shnum, _shstrndx) = ELF_HEADER.unpack_from(data)
    if ident[:6] != b"\x7fELF\x02\x01" or e_type != 1 or machine != 62:
        raise ValueError("expected a little-endian x86-64 relocatable ELF object")
    if shentsize != SECTION_HEADER.size or shnum == 0 or shoff + shnum * shentsize > len(data):
        raise ValueError("invalid ELF section table")
    sections = [SECTION_HEADER.unpack_from(data, shoff + i * shentsize) for i in range(shnum)]
    seen = changed = 0
    for section in sections:
        (_name, kind, _flags, _addr, offset, size, _link, target_index,
         _align, entsize) = section
        if kind != SHT_RELA:
            continue
        if entsize != RELA.size or size % entsize or offset + size > len(data):
            raise ValueError("invalid ELF RELA section")
        if target_index >= shnum:
            raise ValueError("invalid ELF relocation target section")
        target = sections[target_index]
        target_kind, target_offset, target_size = target[1], target[4], target[5]
        if target_kind == SHT_NOBITS or target_offset + target_size > len(data):
            raise ValueError("invalid ELF relocation target bytes")
        for pos in range(offset, offset + size, entsize):
            relative_offset, info, _addend = RELA.unpack_from(data, pos)
            if info & 0xFFFFFFFF != R_X86_64_PC32:
                continue
            if relative_offset + 4 > target_size:
                raise ValueError("PC32 relocation outside target section")
            seen += 1
            field = target_offset + relative_offset
            if data[field:field + 4] != b"\0" * 4:
                data[field:field + 4] = b"\0" * 4
                changed += 1
    if not seen:
        raise ValueError("no x86-64 PC32 relocations found")
    if changed:
        path.write_bytes(data)
    return seen, changed


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("object", type=Path)
    args = parser.parse_args()
    seen, changed = normalize(args.object)
    print(f"Normalized {changed}/{seen} ELF64 PC32 relocation fields in {args.object}")
