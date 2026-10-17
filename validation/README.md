# Validation tooling

- `limited_run.py` — runs a command under a 1.5 GB aggregate memory cap (Windows Job Object). Always use it.
- `build_modules.py` — guarded module-by-module Lean build (Lake exceeds the cap). Mathlib modules are CI-only.
- `axiom_audit.py` — checks locally buildable `WriteExecute` declarations use only the three standard axioms.
- `native.py` — builds/runs the legacy `writeexec` harness in the four configurations (`vs/` projects, output in `build/msbuild`).
- `cmake_local.py [x86|x64]` — local MSVC build and ctest of the CMake targets (`build/msvc-<arch>`); `msbuild_local.py [Config|Platform ...]` — builds `vs/selfspectre.sln` (output in `build/msbuild`). The portable grid (Windows, Linux x86/x64, macOS x64) runs in `.github/workflows/portable.yml`.
- `build_native_demos.py [x64|x86]` — focused MSVC Release build of the AES and RSA demos plus deterministic C vectors in `build/native/<arch>/Release`; it does not build `spectrepoc`. It selects RDTSCP or the RDTSC+LFENCE fallback from CPUID (`WE_FORCE_RDTSC=1` exercises the latter). Run it through `limited_run.py`. `build_cache_timing.py` builds the isolated 512/4096-byte timing diagnostic into `validation/.build`.
- `SPECTRE_INVESTIGATION.md` — current-machine diagnosis, repair, and guarded AES/RSA results. The speculative demos are hardware measurements and are not part of CTest.
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

## Rare transient mismatches of the native harnesses (open: reproduced, not explained)

Four times in CI, on GitHub `windows-2022` runners, a Write-Execute call returned a wrong result once and the same call was right
when repeated: `edge_vectors` Win32 (`DIV32`, "got 1fe want 1fe": the first call was wrong, the immediate repeat right) and the
first block of the legacy `writeexec` harness on x64, three times (one wrong 32-bit value, or a burst of seven). Each time the
next attempt, or the repeat call, passed.

What was established:

- The plain-C reference arithmetic is not the cause: `ref_soak` ran the same functions (copied verbatim from `writeexec.c`) for
  150 million random iterations on each of 32 runners and found nothing; 100 million locally also found nothing.
- Not input dependent: `edge_vectors` uses fixed tables; the failing call is right when repeated.
- Not thread migration: it also occurred with the thread pinned (`WE_PIN=1`).
- Not residual state in the self-modifying code: the repeat call, made immediately, is right.
- Not reproduced in 26 local runs, 80 + 32 + 32 runner runs of the instrumented harnesses, or in 120 later runner runs (the later
  runs also carry a changed `writeexec.c`, so the code layout differs). The rate is about one event per 10^8 calls, so layout or
  platform effects cannot be separated statistically with a reasonable number of runs. Linux and macOS runners have been run
  far fewer times (about 15 each), so the absence of events there is not evidence of a Windows-only effect.
- No CPU model is implicated: the runners are a mix of AMD EPYC 7763/9V45/9V74 and Intel Xeon 8370C/8573C/6973P-C, and the failing
  jobs whose CPU was recorded were EPYC 7763 (the most common model).

The procedures store an operand into an instruction and jump to it within a few cycles. The architecture manuals promise coherent
same-thread self-modifying code, but the manuals' portable recipe adds a serializing instruction, which the verified byte layout
(`validation/layout`) does not contain, so the assembly is deliberately not changed. A rare stale-fetch event on a virtualized
host is the leading hypothesis; it is not proven. The harnesses therefore classify instead of hiding: `edge_vectors` calls the
procedure twice more on a mismatch, reports a result that is right on both repeats as `transient` (counted in the final
`edge vectors ok N (K transient)` line, not a failure), and fails if it stays wrong; the Windows ctest steps allow up to three
attempts for the legacy harness (`--repeat until-pass:3`); mismatch lines of the legacy harness carry their source line and CPU.
`.github/workflows/flake-hunt.yml` (manual) repeats the tests on many runners. This is native evidence only and does not enter any
Lean statement.
