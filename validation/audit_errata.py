"""Errata audit. --inventory: every `before` occurs in the published text (whitespace/hyphenation/ligature-normalized)."""
import json, re, sys, unicodedata
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]


def norm(s):
    s = unicodedata.normalize("NFKC", s).replace("­", "")
    s = re.sub(r"-\s*\n\s*", "", s)
    s = re.sub(r"\s+", "", s)  # compare with all whitespace removed: tolerant of pdftotext spacing in code
    return s


def main():
    data = json.loads((ROOT / "lean/errata/edits.json").read_text(encoding="utf-8"))
    pages = (ROOT / "validation/reference/tmmp-2019-0010.txt").read_text(encoding="utf-8").split("\f")
    normed = [norm(p) for p in pages]
    bad = 0
    for e in data["edits"]:
        want = norm(e["before"])
        hit = [131 + i for i, p in enumerate(normed) if want in p]
        ok = bool(hit)
        bad += not ok
        print("ok  " if ok else "FAIL", e["id"], "claimed p%s found %s" % (e["page"], hit))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
