"""Find direct fallthrough into instruction bytes patched in the same assembly block.

This is a source-level check for the branch-after-store sequence in Intel SDM
Vol. 3A, Handling Self- and Cross-Modifying Code. It is not a control-flow proof:
computed patch targets, macro expansions and runtime fetch behavior are outside
its scope.
"""

import re
from pathlib import Path

SOURCE = Path(__file__).resolve().parents[1] / "src/writeexc.asm"
LABEL = re.compile(r"^\s*([A-Za-z_]\w*)\s*:{1,2}")
STORE = re.compile(r"^mov\s+(?:byte|word|dword)\s+ptr\s*\[\s*([A-Za-z_]\w*)", re.I)
TRANSFER = re.compile(r"^(?:jmp|ret|iret)\b|\b(?:PROC|ENDP)\b", re.I)


def main() -> None:
    lines = SOURCE.read_text(encoding="utf-8").splitlines()
    violations = []
    for index, raw in enumerate(lines):
        label = LABEL.match(raw)
        if not label:
            continue
        target = label.group(1).lower()
        stores = []
        for prior in range(index - 1, -1, -1):
            code = lines[prior].split(";", 1)[0].strip()
            if TRANSFER.search(code):
                break
            store = STORE.match(code)
            if store and store.group(1).lower() == target:
                stores.append(prior + 1)
        if stores:
            violations.append((index + 1, label.group(1), sorted(stores)))
    for line, label, stores in violations:
        print(f"{SOURCE.name}:{line}: fallthrough into patched {label}; stores at {stores}")
    if violations:
        raise SystemExit(1)
    print("SMC fallthrough audit: no direct patched-label fallthrough")


if __name__ == "__main__":
    main()
