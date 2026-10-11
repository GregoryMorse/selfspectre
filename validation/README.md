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
- `run_listings.py <name> [asm]` — assembles a copy of `writeexc.asm` (x86 + x64, with listings) into `validation/.build/<name>/`.
  `lst` = the published source (git history before L04), `lstc` = the current corrected source.
  `extract_layout.py [lst|lstc]` writes `layout/{x86,x64}.json` (published) or `layout/{x86c,x64c}.json` (corrected);
  `gen_x86_layout.py` turns all four into `lean/WriteExecute/X86/LayoutData.lean`.
- `compare_listings.py` + `compare_dump.lean` — evidence: the bytes the Lean byte model assigns to the NOT/NZ/SHL4 table entries
  and fixed instructions equal the relocated COFF `.text` (needs the four objects and built oleans).
- `make_challenge.py [--check]` — generates `lean/Challenge.lean` from the Spec modules (plan D6).
- `palomar/` — pinned policy assets (`refresh_policy.py`, `fetch_policy_assets.py`) and `validate_metadata.py`
  (`lean/formalization.yaml` against the pinned v0.4 schema and the registry taxonomies).
- `ci/` — `linux.sh` (cold build, Challenge/Solution, `axioms.py`, generated-file and errata checks) used by `.github/workflows/proof.yml`.
- `native_vectors.py` — exact Python-generated vectors for the corrected C `mulmod`/`fastmodexp`/`modexp` (L02, L03).
