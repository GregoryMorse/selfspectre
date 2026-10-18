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
- `edge_vectors modexp N [seed]` — focused assembled `MODEXP32` versus an independent 64-bit C reference for the captured Debug|x64 CI triple followed by `N-1` random triples; prints the seed and exact operands on the first failure and fails even if immediate repeats pass. The Windows CMake suite runs 100 calls per job.
- `patch_alignment.py <writeexc.obj> <edge_vectors.map>` — resolves simple byte/word/dword code-patch sites against the *linked* MSVC image and reports stores that span a 64-byte cache line. The Windows CMake harnesses emit linker maps and CI prints this diagnostic. Object-file offsets alone are insufficient because the linker shifts the assembly section relative to the cache-line grid.
- `audit_smc_fallthrough.py` — checks that a straight-line assembly block does not store into a labeled instruction and then fall through to that label. This is a source check of one self-modifying-code sequencing rule, not a proof of runtime behavior.
- `native_vectors.py` — exact Python-generated vectors for the corrected C `mulmod`/`fastmodexp`/`modexp` (L02, L03).

## Rare native mismatches (open: reproduced; Intel portability gap repaired)

Four times in CI, on GitHub `windows-2022` runners, a native check returned a wrong result once and a repeat passed. One was
an assembled Write-Execute call: `edge_vectors` Win32 `DIV32` ("got 1fe want 1fe": the first call was wrong, the immediate
repeat right). The other three were in the **plain-C first block** of the legacy `writeexec` harness on x64 (one wrong 32-bit
value, or a burst of seven). That block ends before the first `WriteExec*` call in `src/writeexec.c`, so those three events
cannot be attributed to a stale fetch inside the Write-Execute assembly during the failing check. Each subsequent attempt
passed. The two classes of event may have different causes.

A fifth event occurred on 2026-10-18 in the `writeexec` Debug|Win32 `WriteExecMODEXP32_C` check at
`src/writeexec.c:822`: `0D2366D8` versus C reference `11E52FFA`. The old check recorded neither
inputs nor same-input repeats. Passing other configurations with fresh random inputs does not show
whether this was transient or input-specific. The check now records inputs and repeats the same
assembled call twice on mismatch. Two matching repeats are labelled `transient`; every wrong first
result now fails `validation/native.py` and CTest.

A sixth event occurred on 2026-10-18 in the push-triggered [proof/native run #46](https://github.com/GregoryMorse/selfspectre/actions/runs/39151226301), `writeexec` Debug|x64 `WriteExecMODEXP32_C` at `src/writeexec.c:833`. For base `2997D078`, exponent `4C815A47`, modulus `2A94AE94`, the first call returned `122C3628` instead of `1D3A89A8`; two immediate same-input repeats returned `1D3A89A8` on CPU 0. The independent modular-exponentiation reference also returns `1D3A89A8`. This event occurred after the earlier alignment changes and disproves closure based on the prior negative stress runs.

What was established:

- `ref_soak` found no mismatch in 150 million random iterations on each of 32 runners or 100 million locally. It copies the
  plain-C functions but uses nonzero odd divisors, its own random generator and a separate binary; this negative result does
  not rule out a first-block C, optimizer or input-dependent cause in `writeexec`.
- The first block's expected signed remainder formerly contained `((int64_t)num1 << 32 | num2)`:
  for `num1 >= 0x80000000`, that C expression has undefined behavior. The signed multiplication
  and division helpers also negated the minimum signed values. These reference defects are repaired
  in both the legacy harness and `ref_soak`; none is proven to have caused an observed CI event.
- The assembled `edge_vectors` case is not input dependent in the usual deterministic sense: it uses fixed tables and its
  repeat call was right. The three plain-C legacy events used random inputs.
- At least one earlier event occurred with the thread pinned (`WE_PIN=1`), so migration alone cannot explain all events.
- For the one assembled `DIV32` event, an immediate repeat call was right, but that does not isolate which code patch or fetch failed.
- The first four events were not reproduced in 26 local runs, 80 + 32 + 32 runner runs of the instrumented harnesses, or in 120 later runner runs (the later
  runs also carry a changed `writeexec.c`, so the code layout differs). They were sparse enough that layout or
  platform effects cannot be separated statistically with a reasonable number of runs. Linux and macOS runners have been run
  far fewer times (about 15 each), so the absence of events there is not evidence of a Windows-only effect.
- No CPU model is implicated: the runners are a mix of AMD EPYC 7763/9V45/9V74 and Intel Xeon 8370C/8573C/6973P-C, and the failing
  jobs whose CPU was recorded were EPYC 7763 (the most common model).

The source audit after that event found 29 straight-line paths in `src/writeexc.asm` where a store patched an instruction later executed by fallthrough. Intel SDM Vol. 3A §8.1.3 recommends a jump to the new or intermediate code, or a serializing instruction, for portable same-thread self-modifying code; the existing wrapper jumps did not cover these internal paths. Each path now branches to its first patched instruction, and `audit_smc_fallthrough.py` guards the source pattern in CI. This closes a documented Intel portability gap, but the one-off `DIV32` and `MODEXP32` events have not been causally traced to any specific path. AMD APM Vol. 2 §7.6.1 explicitly says its processors detect in-flight self-modification, flush and refetch, with no special software action. A hardware machine clear and the Intel source-level recommendation describe different layers, so observing a machine clear would not itself establish that every earlier modified fetch is covered. `native.py` now records the host CPU and Windows version for future correlations. `edge_vectors` and the focused `edge_vectors modexp N seed` mode record the first wrong result,
exact operands in the focused mode, and two same-input repeats. Any wrong first result now fails the run, even if the
repeats pass; CI no longer retries the Windows CTest step. Mismatch lines in the legacy harness carry their source line
and CPU. Intel: https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-3a-part-1-manual.pdf ;
AMD: https://docs.amd.com/v/u/en-US/24593_3.44_APM_Vol2 .
`.github/workflows/flake-hunt.yml` (manual) repeats the tests on many runners. This is native evidence only and does not enter any
Lean statement.

Follow-up alignment audit (2026-10-18): the local linked `edge_vectors` images had 12 (x86) and 10 (x64) statically resolved 32-bit patch fields that span a 64-byte line. Some occur in helpers reached by division (for example x86 `shr32arg1_3+2`, x64 `xorret+1` and `divshl1loop+1`). The initially suspected `divres4+2` crossing in the x86 *object* did **not** cross in the linked vector binary. Relinked x86 and x64 vector binaries each passed 232,081 checks with zero transients. A crossing is a measured layout fact, not evidence that it caused a mismatch. The diagnostic does not turn a crossing into a failure; eliminating one crossing would shift other code and could create another elsewhere. A fix requires a controlled linked-layout comparison with enough repeated calls to distinguish it from the observed low event rate.

On the local Debug|Win32 MSBuild image, `cdb` with the matching PDB disassembled `WriteExecMODEXP32_C`: it loads three 32-bit stack arguments, writes all twelve operand bytes, patches four result destinations and the return jump, then jumps to `WriteExecMODEXP32`. Its `modexpres3+2` destination patch starts at cache-line offset 63. In the separate linked CMake Release|Win32 vector image, `patch_alignment.py` finds different hot crossings: `modexp32arg3_1+2` at offset 63, `divretval2+2` at 62, and `shr32arg1_3+2` at 62. The links differ, so padding one location does not remove the others or establish a cause. The wrapper disassembly cannot establish correctness of the internal `MODEXP32`/`DIV32` trace or diagnose the earlier CI value without its operands. A focused 1,000-call differential run on each local assembled architecture and a subsequent 100-call mixed-operation run on each passed with no mismatch; the Windows CMake focus test passed 100 fresh triples and the legacy Debug|Win32 harness passed once. These are negative samples, not closure of the rare event.
