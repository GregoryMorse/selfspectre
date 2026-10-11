# Validation tooling

- `limited_run.py` — runs a command under a 1.5 GB aggregate memory cap (Windows Job Object). Always use it.
- `build_modules.py` — guarded module-by-module Lean build (Lake exceeds the cap). Mathlib modules are CI-only.
- `axiom_audit.py` — checks locally buildable `WriteExecute` declarations use only the three standard axioms.
- `native.py` — builds/runs the legacy `writeexec` harness in the four configurations.
- Listings (needed by `extract_layout.py`/`purity_scan.py`): copy `writeexc.asm` and `asm_listings.bat` into
  `validation/.build/lst/`, run `asm_listings.bat` there (x86 + x64 listings, ~170 MB each, never committed),
  then `python validation/extract_layout.py` and `python validation/purity_scan.py`.
- `layout/{x86,x64}.json`, `layout/purity.json` — committed outputs.
- `reference/` — published TMMP PDF (SHA-256 `8d9b4072…1940`) and its `pdftotext -layout` text.
