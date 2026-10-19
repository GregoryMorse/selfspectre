# Self-Spectre, Write-Execute and the Hidden State

[![DOI](https://img.shields.io/badge/DOI-10.2478%2Ftmmp--2019--0010-blue)](https://doi.org/10.2478/tmmp-2019-0010)
[![Journal](https://img.shields.io/badge/Journal-Tatra%20Mt.%20Math.%20Publ.%2C%20Vol.%2073-green)](https://doi.org/10.2478/tmmp-2019-0010)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Code supplement to the peer-reviewed paper published in **Tatra Mountains Mathematical Publications**, Vol. 73 (2019):

> Gregory Morse, *Self-spectre, write-execute and the hidden state*,  
> Tatra Mountains Mathematical Publications, Vol. 73, 2019.  
> https://doi.org/10.2478/tmmp-2019-0010

Presented at the **18th Central European Conference on Cryptology (CECC'18)**, June 6, 2018, Smolenice, Slovakia.

## Overview

This repository demonstrates two novel computation-hiding techniques applied to the AES-128 and RSA algorithms:

1. **Speculative execution side-channel** — attempting to perform arithmetic on a mispredicted path and recover the result through cache timing. If the path is squashed, its architectural register and memory changes do not commit; whether the cache trace is observable is processor and build dependent.

2. **Write-execute self-modifying code** — performing arbitrary computations by writing operands directly into instruction opcodes in the executable `.text` section and jumping to them, so that at no point during computation are operands present in registers or addressable memory — only encoded within the instructions themselves.

The paper proposes these as computation-hiding techniques. The demos and formalization do not establish resistance to static analysis or debugging on a modern platform.

## Repository Structure

```
src/                     <- native sources
    spectre.c            Original Spectre v1 PoC (spectrepoc)
    spectreopt.c         Spectre victim/helper functions (shared)
    spectrecode.asm      MASM speculative-execution wrappers (x86/x64)
    spectreaes.c         AES-128 Spectre attack demo (selfspectre)
    spectrersa.c         RSA modular-exponentiation Spectre demo (spectrersa)
    writeexec.c          Write-execute framework test harness (writeexec)
    writeexc.asm         MASM write-execute arithmetic/crypto primitives
    tables.asm           Stub assembly (placeholder)
    portable/            Small headers that make the sources build with GCC/Clang (Linux, macOS)
CMakeLists.txt, cmake/   CMake build (Windows, Linux, macOS); MASM source assembled by ml/ml64 or by UASM
vs/                      Visual Studio solution and projects (convenience; output goes to build/msbuild)
build/                   all build output (CMake trees: build/cmake, Visual Studio: build/msbuild); not tracked
lean/                    the Lean development
validation/              checks, scripts and native test harnesses (evidence, not proof)
output/pdf/              errata PDF
```

## Projects

### `selfspectre` — AES-128 Spectre Demo
Demonstrates hidden AES-128 computation in the speculative pipeline and reads its result through cache timing. The AES executable uses `spectreaes.c` and `spectreopt.c`; it does not link `spectrecode.asm` or `writeexc.asm`.

### `spectrersa` — RSA Spectre Demo
Demonstrates hidden modular-exponentiation steps at varying depths, including C and assembly implementations. It uses `spectrersa.c`, `spectreopt.c`, and `spectrecode.asm`. The example modulus is the small, fixed product `61 * 53`; this is a research workload, not a production RSA implementation.

### `writeexec` — Write-Execute Arithmetic Framework
Standalone test harness for `writeexc.asm`. Exercises all write-execute primitives: bitwise operations (SHL, SHR, NOT, XOR, OR, AND), arithmetic (ADD, SUB, INC, DEC, MUL, DIV, MODEXP), and AES-128 table lookups (Te0–Te4, full AES round). Results are verified against standard C implementations and timed for performance comparison.

### `spectrepoc` — Original Spectre v1 Proof-of-Concept
The original Spectre v1 PoC from the paper by Kocher et al. attempts to recover a string through branch-predictor training and cache timing. Its output is an experimental observation, not a mitigation-status test. In particular, low scores or `Unclear` do not identify a CPU, microcode, OS, compiler, or timing cause.

Accepts optional command-line arguments: `[cache_hit_threshold] [address] [length]`. The default timing threshold is a fixed value of 80, not a calibrated property of the machine.

## Building

### CMake (Windows, Linux, macOS)

```
cmake -S . -B build/cmake -DCMAKE_BUILD_TYPE=Release
cmake --build build/cmake
ctest --test-dir build/cmake --output-on-failure
```

The Write-Execute procedures are x86/x86-64 machine code that rewrites itself, so the targets are Windows (MSVC, x86 and
x64), Linux (x86 and x64) and macOS (x64). With MSVC the MASM sources are assembled by `ml`/`ml64`; on Linux and macOS
by [UASM](https://github.com/Terraspace/UASM) (a MASM-compatible assembler), which CMake downloads and builds from a
pinned revision (needs `git`, `make` and a C compiler; 32-bit Linux builds need `gcc-multilib`). The tests are the
deterministic vector checks (`code_vectors`, `edge_vectors`) and the legacy randomized `writeexec` harness (several
minutes). The Spectre programs are built but never run by the tests; `-DSELFSPECTRE_BUILD_SPECTRE=OFF` skips them.
The workflow `.github/workflows/portable.yml` runs this grid, plus the Visual Studio solution, on GitHub Actions.
The Linux x64 build normalizes UASM's ELF64 PC-relative relocation fields
before linking. On EPYC 7513, the native vector suite passes some runs and
fails others with rare wrong first results in MUL32, DIV32, MOD32, MODEXP32, and
focused SHR32 checks; see the [bare-metal investigation](validation/EPYC_7513.md).
Native Write-Execute reliability on that processor remains unresolved.
The [Gigabyte EPYC 7542 cross-host check](validation/EPYC_7542.md) passed the
full native suite and 160 million focused XOR calls, so the failure has not
been reproduced on every AMD generation.
For a focused manual check, build the `we_xor_branchless` target and run it
repeatedly; it reports the number of wrong XOR bytes and exits nonzero when it
finds one. See [the diagnostic instructions](validation/README.md#focused-write-execute-diagnostic).

### Status of the speculative demos

A passing build and native vector test run establish that the programs compile and that the tested arithmetic agrees with its reference. CTest never runs `selfspectre_aes`, `selfspectre_rsa`, or `spectrepoc`; a native demo run is needed to check speculative behavior on a particular processor. The Lean Self-Spectre results assume an abstract predictor, speculation window, and cache-leak contract; [the selected-statement notes](lean/PALOMAR_SEMANTICS.md) explicitly model no processor.

The build requests no MSVC Spectre v1 instrumentation (`/Qspectre-` in CMake; `SpectreMitigation=false` in the Visual Studio projects). This removes one possible software barrier in these binaries, but does not establish that a given CPU will run the victim body far enough to leave a detectable cache trace. Intel describes bounds-check-bypass mitigation as primarily a software problem, and Microsoft documents both the effect and the limits of `/Qspectre` ([Intel guidance](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/technical-documentation/analysis-speculative-execution-side-channels.html), [MSVC documentation](https://learn.microsoft.com/en-us/cpp/build/reference/qspectre?view=msvc-170)). A low score alone cannot attribute failure to microcode or to a runtime library.

The AES and RSA demos use 4,096-byte probe spacing, shuffled reload order, and a measured cache threshold at startup. AES measures both isolated lines and a full shuffled probe sweep. RSA keeps its validated isolated-line calibration and then checks a full flushed sweep for background hits; changing its compiled decoder layout measurably changed its results. Windows and Linux pin the thread to its starting logical CPU. Pass a numeric first argument to override the threshold; set `WE_CPU=<logical-index>` to select a CPU or `WE_CPU=any` to disable pinning. `spectrersa --depth-sweep [threshold]` checks individual one-, two-, four-, five-, six-, and eight-step computations in C and assembly where available. The demos report score-based `Success` separately from a `Correct` reference comparison; read both labels together. Their inputs and AES key are fixed in source.

At startup the demos print CPUID feature bits and reject missing timing/flush instructions before using them. AES-NI modes are skipped when AES-NI is absent. The focused Windows build script and native CMake configure select RDTSCP or the RDTSC+LFENCE fallback from CPUID. `WE_FORCE_RDTSC=1` tests that fallback in the focused script; cross builds can select it with `-DSELFSPECTRE_FORCE_RDTSC=ON`. On 32-bit MSVC, the fallback keeps the timed load inside one assembly block so the compiler cannot move it outside the timestamps. Automatic calibration needs CLFLUSH; the legacy `NOCLFLUSH` path needs an explicitly measured threshold. Non-MSVC CMake builds now target SSE2 generally and enable AES instructions only in AES-NI functions.

`src/portable/we_spectre_params.h` names the experimental training settings: 30 calls per attempt, a six-call period, 100 delay spins, and up to 999 attempts. Cache calibration measures the timing cut, not these branch-predictor settings or the speculation window. CPUID likewise identifies instructions, not whether a particular Intel or AMD processor will speculatively complete a chosen AES/RSA depth. The run's `Correct` and confidence counts are the platform check. The RSA training loop retains its original macro form because a seemingly equivalent refactor changed generated code and reduced recovery on this machine.

The [native reproducibility investigation](validation/SPECTRE_INVESTIGATION.md) compares the paper's cases with old and repaired x64/x86 runs on an i9-14900HX. The old 512-byte probe layout classified thousands of flushed lines as hits. With automatic pinning and calibration, ten-round AES-NI returned 10/10 correct in each build; the latest complete RSA chain returned 160/160 correct groups in both, while earlier runs varied slightly. The [bare-metal EPYC 7513 replication](validation/EPYC_7513.md) recovered the AES-NI cases and the complete RSA chain on both sockets, with every tested direct RSA depth through eight operations at 10/10. These are native measurements, not Lean proofs or cross-machine guarantees.

For a focused Windows MSVC build and run, without the separate `spectrepoc` target:

```powershell
python validation/limited_run.py -- python validation/build_native_demos.py x64
python validation/limited_run.py -- build/native/x64/Release/selfspectre.exe
python validation/limited_run.py -- build/native/x64/Release/spectrersa.exe --depth-sweep
```

Use `x86` in the build command and path to check the 32-bit cases. `validation/limited_run.py` applies this repository's 1.5 GB aggregate memory limit.

### Visual Studio

Requirements: Visual Studio 2022 or later with the C++ workload (MASM `ml.exe`/`ml64.exe` included) and the Windows 10 SDK.

1. Open `vs/selfspectre.sln`, select **Build -> Batch Build**, tick all configurations and **Build**
   (or `msbuild vs\selfspectre.sln /p:Configuration=Release /p:Platform=x64`, `Platform` being `x86` or `x64`).
2. Everything is written to `build/msbuild/<Win32|x64>/<Debug|Release>/` (see `vs/Directory.Build.props`).

The PreLinkEvent in each project invokes `ml.exe` (x86) or `ml64.exe /DX64` (x64) to assemble `writeexc.asm` and
`spectrecode.asm` before linking.

| Configuration | Platform | Notes |
|---------------|----------|-------|
| Debug         | x86      | No optimisation; `/safeseh` not applied to ASM |
| Debug         | x64      | No optimisation; `ml64.exe /DX64` |
| Release       | x86      | `/O2`, COMDAT folding, `/safeseh` on ASM |
| Release       | x64      | `/O2`, COMDAT folding |

> **Note:** `spectreopt.c` is compiled with `MaxSpeed` optimisation even in Debug|x64 builds so that the victim function is not trivially defeated by the compiler.

## Lean formalization

The Write-Execute part of the paper is formalized in Lean 4 (`lean/`, toolchain `leanprover/lean4:v4.35.0-rc3`,
Mathlib pinned in `lean/lakefile.toml`). Registered in the Palomar registry as [PALOMAR-2026-10-14-000007](https://palomar-registry.org/entry?id=PALOMAR-2026-10-14-000007&version=1) (version 1, 2026-10-14, commit `fe72073`).
The selected statement `PalomarWE.mathematical_result`
(`lean/Challenge.lean`, proved in `lean/Solution.lean`) covers read-freedom of the ideal word-level machine,
Turing-completeness (with the finite-image caveat), confinement, the jump-table lookup and 8-bit tables,
wide arithmetic, division, modular reduction and exponentiation, AES-128 (T-tables and the Write-Execute
procedure against FIPS-197) and Self-Spectre as a conditional result under an abstract speculation contract
(mistraining schedule, victim leak, speculation-depth boundary, hidden computation; no processor is modeled). Supporting byte-level x86/x64 models of Figs. 5, 6 and 7
(including the Fig. 6 XOR copy loop, 35 and 38 steps) are checked against the assembled objects.

* `lean/PAPER_MAP.md` - every claim with its status; `lean/PALOMAR_SEMANTICS.md` - the selected statement and its model boundaries.
* `lean/errata/selfspectre-2019-errata.tex` (PDF in `output/pdf/`) - corrections W01-W10 to the published text, quoted from the
  published PDF; `lean/errata/minimal.diff` - code fixes L01-L05 (already applied to `src/writeexec.c`, `src/spectreopt.c`, `src/writeexc.asm`).
* Build: `cd lean && lake exe cache get && lake build WriteExecute Challenge Solution`. CI: `.github/workflows/proof.yml`
  (Linux proof job and Windows native acceptance); `.github/workflows/palomar-full.yml` is the Palomar mechanical preflight.
* Development process and rules: `FORMALIZATION_PLAN.md`, `CLAUDE.md`, `lean/ROUNDS.md`. The formalization was produced with
  AI assistance (see `lean/formalization.yaml`); it has not had independent human mathematical review.

## Third-Party Code

`spectre.c` is the original Spectre v1 proof-of-concept from the paper:

> Paul Kocher et al., *Spectre Attacks: Exploiting Speculative Execution*,  
> IEEE Symposium on Security & Privacy 2019.  
> https://spectreattack.com/spectre.pdf

It is compiled as-is into the `spectrepoc` project with no modifications beyond what was required to fix compilation errors (as noted in the file header).

## Security Notice

This code is a research proof-of-concept published alongside a peer-reviewed academic paper. It is provided for educational and research purposes. The Spectre-variant techniques require a vulnerable CPU microarchitecture and specific timing conditions; their reliability varies with hardware, OS scheduler behaviour, and mitigation status.

## Author

Gregory Morse  
gregory.morse@live.com  
https://github.com/GregoryMorse

## Citation

```bibtex
@article{morse2019selfspectre,
  author  = {Gregory Morse},
  title   = {Self-spectre, write-execute and the hidden state},
  journal = {Tatra Mountains Mathematical Publications},
  volume  = {73},
  year    = {2019},
  doi     = {10.2478/tmmp-2019-0010},
  url     = {https://doi.org/10.2478/tmmp-2019-0010}
}
```

## License

Original source code in this repository is released under the MIT License — see [LICENSE](LICENSE).  
`spectre.c` retains its original authorship and is reproduced here as a reference document; see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
