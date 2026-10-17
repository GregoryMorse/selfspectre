"""Turns the ELF64 object that UASM writes for a MASM source into a position-independent code blob plus a GNU-assembler
file that places it, with the global symbols as labels, in __TEXT,__text. Used on macOS, where UASM's own Mach-O writer
cannot express the relocations of this code (byte-sized and non-extern pc-relative fixups).

    python elf2blob.py <input.o> <output.bin> <output.s>

Relocations against symbols of the same .text section are resolved here. A 32-bit pc-relative reference to a symbol defined
elsewhere (a C global) is left to the system assembler as ".long (_symbol + addend) - .". Anything else stops the conversion
instead of producing a wrong blob."""
import struct, sys

SHT_SYMTAB, SHT_RELA, SHT_REL = 2, 4, 9
R_PC32, R_PLT32, R_PC8, R_PC16 = 2, 4, 15, 13


def main(src, out_bin, out_s):
    data = bytearray(open(src, "rb").read())
    if data[:4] != b"\x7fELF" or data[4] != 2:
        sys.exit("not an ELF64 object")
    shoff, = struct.unpack_from("<Q", data, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 0x3A)
    secs = []
    for i in range(shnum):
        name, typ, flags, addr, off, size, link, info, align, entsize = struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shentsize)
        secs.append(dict(name=name, type=typ, off=off, size=size, link=link, info=info, entsize=entsize))
    shstr = secs[shstrndx]

    def cstr(base, o):
        s = base + o
        return bytes(data[s:data.index(0, s)]).decode()

    for s in secs:
        s["sname"] = cstr(shstr["off"], s["name"])
    text = next((i for i, s in enumerate(secs) if s["sname"] == ".text"), None)
    if text is None:
        sys.exit("no .text section")
    symtab = next(s for s in secs if s["type"] == SHT_SYMTAB)
    strtab = secs[symtab["link"]]
    syms = []
    for k in range(symtab["size"] // 24):
        nm, info, other, shndx, value, size = struct.unpack_from("<IBBHQQ", data, symtab["off"] + k * 24)
        syms.append(dict(name=cstr(strtab["off"], nm), bind=info >> 4, typ=info & 15, shndx=shndx, value=value))
    blob = bytearray(data[secs[text]["off"]:secs[text]["off"] + secs[text]["size"]])

    count = 0
    ext = []
    for s in secs:
        if s["type"] == SHT_REL:
            sys.exit("REL relocations are not supported")
        if s["type"] != SHT_RELA or s["info"] != text:
            continue
        for k in range(s["size"] // 24):
            offset, info, addend = struct.unpack_from("<QQq", data, s["off"] + k * 24)
            sym, typ = syms[info >> 32], info & 0xFFFFFFFF
            if sym["shndx"] == 0 and typ in (R_PC32, R_PLT32):
                ext.append((offset, sym["name"], addend))
                continue
            if sym["shndx"] != text:
                sys.exit(f"relocation against {sym['name']!r} outside .text (section {sym['shndx']})")
            value = sym["value"] + addend - offset
            if typ in (R_PC32, R_PLT32):
                struct.pack_into("<i", blob, offset, value)
            elif typ == R_PC8:
                struct.pack_into("<b", blob, offset, value)
            elif typ == R_PC16:
                struct.pack_into("<h", blob, offset, value)
            else:
                sys.exit(f"unsupported relocation type {typ} against {sym['name']!r}")
            count += 1
    for s in secs:
        if s["sname"] in (".data", ".bss", ".rodata") and s["size"]:
            sys.exit(f"{s['sname']} is not empty ({s['size']} bytes)")

    open(out_bin, "wb").write(blob)
    glob = sorted((x for x in syms if x["bind"] in (1, 2) and x["shndx"] == text and x["name"]), key=lambda x: x["value"])
    events = [(x["value"], 0, x) for x in glob] + [(o, 1, (n, a)) for o, n, a in ext]
    events.sort(key=lambda e: (e[0], e[1]))
    lines = ["	.text", "	.p2align 4"]
    pos = 0

    def upto(p):
        nonlocal pos
        if p > pos:
            lines.append(f'	.incbin "{out_bin}", {pos}, {p - pos}')
            pos = p

    for offset, kind, x in events:
        upto(offset)
        if kind == 0:
            lines += [f"	.globl _{x['name']}", f"_{x['name']}:"]
        else:
            lines.append(f"	.long (_{x[0]} + {x[1]}) - .")
            pos += 4
    upto(len(blob))
    open(out_s, "w").write("\n".join(lines) + "\n")
    print(f"{src}: {len(blob)} bytes, {count} relocations resolved, {len(glob)} global symbols, {len(ext)} external references")


main(*sys.argv[1:4])
