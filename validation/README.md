# Validation tooling

- `limited_run.py` — runs a command under a 1.5 GB aggregate memory cap (Windows Job Object). Always use it.
- `build_modules.py` — guarded module-by-module Lean build (Lake exceeds the cap). Mathlib modules are CI-only.
- `axiom_audit.py` — checks locally buildable `WriteExecute` declarations use only the three standard axioms.
- `native.py` — builds/runs the legacy `writeexec` harness in the four configurations (`vs/` projects, output in `build/msbuild`).
- `cmake_local.py [x86|x64]` — local MSVC build and ctest of the CMake targets (`build/msvc-<arch>`); `msbuild_local.py [Config|Platform ...]` — builds `vs/selfspectre.sln` (output in `build/msbuild`). The portable grid (Windows, Linux x86/x64, macOS x64) runs in `.github/workflows/portable.yml`.
- Listings (needed by `extract_layout.py`/`purity_scan.py`): copy `src/writeexc.asm` and `asm_listings.bat` into
  `validation/.build/lst/`, run `asm_listings.bat` there (x86 + x64 listings, ~170 MB each, never committed),
  then `python validation/extract_layout.py` and `python validation/purity_scan.py`.
- `layout/{x86,x64}.json`, `layout/purity.json` — committed outputs.
- `reference/` — published TMMP PDF (SHA-256 `8d9b4072…1940`) and its `pdftotext -layout` text.
- `run_listings.py <name> [asm]` — assembles a copy of `src/writeexc.asm` (x86 + x64, with listings) into `validation/.build/<name>/`.
  `lst` = the published source (git history before L04), `lstc` = the current corrected source.
  `extract_layout.py [lst|lstc]` writes `layout/{x86,x64}.json` (published) or `layout/{x86c,x64c}.json` (corrected);
  `gen_x86_layout.py` turns all four into `lean/WriteExecute/X86/LayoutData.lean`.
- `compare_listings.py` + `compare_dump.lean` — evidence: the bytes the Lean byte model assigns to the NOT/NZ/SHL4 table entries
  and fixed instructions equal the relocated COFF `.text` (needs the four objects and built oleans).
- `make_challenge.py [--check]` — generates `lean/Challenge.lean` from the Spec modules (plan D6).
- `palomar/` — pinned policy assets (`refresh_policy.py`, `fetch_policy_assets.py`) and `validate_metadata.py`
  (`lean/formalization.yaml` against the pinned v0.4 schema and the registry taxonomies).
- `ci/` — `linux.sh` (cold build, Challenge/Solution, `axioms.py`, generated-file and errata checks) used by `.github/workflows/proof.yml`.
- `native_edge.py` — assembles `src/writeexc.asm` (x86, x64) and runs `native/edge_vectors.c`: deterministic boundary vectors (232,081 checks: all 8-bit pairs, every shift count, carry/borrow boundaries, MUL32/DIV32/MOD32/MODEXP32, FIPS-197 C.1) against the assembled entry points. Evidence, not proof.
- `native_vectors.py` — exact Python-generated vectors for the corrected C `mulmod`/`fastmodexp`/`modexp` (L02, L03).

## Intermittent mismatch on Windows runners (open, not understood)

Twice in CI (GitHub `windows-2022`, native test step) a Write-Execute call returned a wrong result once, and passed on rerun:
`edge_vectors` Win32 printed `DIV32 mismatch ... got 1fe want 1fe` (the old macro called the procedure again to print, so the
first call was wrong and the repeat right: the result is not a function of the arguments alone), and the legacy `writeexec`
harness on x64 printed seven wrong 32/64-bit results in one burst. Not reproduced in 26 local runs of `edge_vectors` (x86) or
in 80 runs on `windows-2022` (`.github/workflows/flake-hunt.yml`, with and without `WE_PIN=1` CPU pinning, 40 each); Linux and
macOS runs have shown none. The edge macro now prints a repeat call on mismatch to tell a transient result from a
deterministic one. The cause is undetermined (candidates: self-modifying code interacting with the virtualized host; a compiler
or runtime effect is not indicated, since the same binary gives the right result on the repeated call). The Windows ctest steps
therefore allow up to three attempts (`--repeat until-pass:3`); a persistent failure still fails the job. This is native
evidence only and does not enter any Lean statement.

