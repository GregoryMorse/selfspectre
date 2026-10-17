# Native Self-Spectre reproducibility and repair, 2026-10-17

The AES and RSA programs demonstrate white-box hidden computation on fixed inputs in the author's own process. This report checks whether those computations still leave measurable cache traces on the current machine.

## What the published result establishes

The published paper, pp. 137-138 (`reference/tmmp-2019-0010.pdf`), reports these selected outcomes. The entries are historical measurements, not a guarantee for another processor or binary.

| Workload | 32-bit correct | 64-bit correct |
| --- | ---: | ---: |
| AES-128, ten rounds, AES-NI intrinsics | 0% | 100% |
| AES-128, ten rounds, C reference | 0% | 0% |
| AES-128, one round, AES-NI intrinsics | 100% | 100% |
| AES-128, one round, C reference | 0% | 0% |
| RSA, two modular multiplications, C | 100% | 100% |
| RSA, four modular multiplications, assembly | 100% | 100% |
| RSA, four modular multiplications, C | 0% | 100% |
| RSA, five modular multiplications, assembly | 100% | 0% |
| RSA, five modular multiplications, C | 0% | 0% |

Figure 4 prints a 32-bit AES-NI sample with many early output bytes recovered but later bytes missing; its caption and final line report zero completely correct runs in that sample. The paper does not give the old CPU model, OS version, compiler version, binary, raw run log, or per-core results. No separate historical Spectre run log was found among tracked files or current untracked build/output files.

## Facts about the available current build

* The local machine reports `Intel(R) Core(TM) i9-14900HX`, 32 logical processors, and Windows build `26200` / version `25H2`. Microsoft identifies build 26200 as Windows 11 25H2; the registry's legacy `ProductName` string says `Windows 10 Education`. Intel identifies this CPU as 8 performance cores plus 16 efficiency cores ([Intel product brief](https://www.intel.com/content/www/us/en/products/docs/processors/core/core-14th-gen-mobile-brief.html), [Microsoft release notes](https://learn.microsoft.com/en-us/windows-insider/release-notes/release-preview-24h2-25h2/build-26100-9539-26200-9539)).
* The surviving `build/msbuild` artifacts are x64 Release binaries and compiler/linker command logs from 2026-10-17. Their compiler command has `/O2` and no `/Qspectre`; `vs/Directory.Build.props` sets `SpectreMitigation=false`. CMake explicitly requests `/Qspectre-` for MSVC. The AES binary links only `spectreaes.obj` and `spectreopt.obj`, not either assembly core.
* Disassembly of the local x64 Release `spectreopt.obj` shows the guarded full AES-NI victim, its ten AES round instructions, and its probe-array reads. It contains no `lfence`. A simple instruction count for that symbol is 137, against 133 reported for the paper's 64-bit AES-NI build; different compiler and counting conventions may account for the difference. The local compiler has therefore not removed the AES victim or inserted an obvious Spectre barrier.
* `WE_PIN=1` reaches `we_pin_if_requested()` through `we_make_code_writable()` in the Write-Execute harness. Neither `spectreaes.c` nor `spectrersa.c` calls it, so that setting does not pin the speculative demos. This matters because the available CPU has two core types, but it is not evidence that migration caused the reported failures.
* CTest builds but never executes the speculative demos. Lean proves a conditional speculation contract, not the behavior of this CPU. Before this investigation the repository had no saved AES/RSA console output or cache-timing distribution from this machine.

The investigation used the published PDF, source, build command logs, object disassembly, and guarded local runs of `selfspectre` and `spectrersa`. It did not run `spectrepoc`, which the author identified as blocked by Windows Defender.

## Supplied current AES run

The author supplied the console output of `build/msbuild/x64/Release/selfspectre` at its default cache-hit threshold of 80. It contains ten runs for each of the four AES modes. All 40 runs say `Incorrect`, including the full x64 AES-NI mode that succeeded in the paper.

The immediate observable failure is **score saturation**. For every one of the 640 output-byte positions, both the highest-scoring and second-highest-scoring candidate received 994-999 hits out of 999 attempts. Both median scores are 999; the median gap is zero, and every gap is at most two. By contrast, Figure 4's historical sample has leading scores in the hundreds with runner-up scores near zero. The current `readMemory128` rule counts a timing sample as a hit when it is at or below the supplied threshold, but these aggregate scores cannot distinguish true probe touches from background classifications. The tie-breaking rule favors later byte values on equal scores, accounting for the frequent `FF`-like guesses without implying an `FF` computation.

This output identifies the *measurement/classification stage* as non-discriminating. It does not distinguish an inappropriate timing threshold from ineffective flushing, other cache effects, timer behavior, or a missing speculative probe trace. The console output does not contain raw timing distributions or per-core observations, so it cannot attribute the cause to Windows 11, microcode, or P/E-core scheduling.

## Isolated cause

There is a definite interpretation error: the paper did **not** report general success for full AES or for all RSA depths. Failures of the C AES paths and the deeper RSA paths are consistent with the published results. The present claim of a regression is specific to cases that historically worked, especially **x64 ten-round AES-NI** and short RSA paths.

For those cases, object code rules out two simple explanations in this build: MSVC `/Qspectre` instrumentation and removal of the AES victim by optimization. A controlled timing diagnostic (`validation/native/cache_timing.c`) then tested the old reload layout. With a single line, the original `RDTSCP` timing sequence separated hot from flushed memory: medians of 27 and 161 cycles. The old 80-cycle threshold lay between them. Adding an `LFENCE` did not cure the full-array failure.

The **512-byte probe layout and deterministic mixed reload order** produced background cache hits. In one guarded diagnostic run, 3,788 of 4,096 flushed lines measured at or below 80 cycles in the old mixed order; a shuffled order still gave 809/4,096 false hits. With 4,096-byte spacing, the same diagnostic gave **0/4,096** false hits in both mixed and shuffled orders. This directly reproduces the saturation without AES, RSA, or speculation. Hardware prefetch is a plausible mechanism, but the experiment establishes the cache-layout effect rather than identifying a particular prefetch engine. The original paper's 512-byte layout was therefore a poor fit for this machine. Windows 11 or microcode is not required to explain the observed regression.

The repair gives each candidate one page of spacing in the C victims, RSA assembly, flush loops, and reload loops. It shuffles reload order, calibrates a hot/cold threshold at startup, and pins the Windows thread to its starting logical CPU so calibration and measurement stay on one core. `WE_CPU=<index>` selects a logical CPU explicitly; `WE_CPU=any` disables pinning. An explicit numeric threshold still overrides calibration.

## Results after repair

The focused x64 and x86 Release builds were produced by `validation/build_native_demos.py` under `validation/limited_run.py`. The table gives guarded runs per architecture with automatic pinning and calibration. Correctness compares the output with the fixed reference computation; it is distinct from the score confidence rule.

| Case | x64 correct / confident | x86 correct / confident |
| --- | ---: | ---: |
| AES, ten-round C | 0/10 / 0/10 | 0/10 / 0/10 |
| AES, ten-round AES-NI | **10/10 / 10/10** | **10/10 / 10/10** |
| AES, one-round C | 10/10 / 10/10 | 10/10 / 10/10 |
| AES, one-round AES-NI | **10/10 / 10/10** | **10/10 / 10/10** |
| RSA, complete chained run | **160/160 / 160/160** | **160/160 / 160/160** |

The separate RSA `--depth-sweep` mode measures one hidden operation from a known input, matching the paper's depth question without compounding errors from a chain. In x64, pinned to logical CPU 0, two C multiplications, four C, four assembly, five C, and five assembly each returned **10/10 correct and confident**. Pinned to CPU 31, all five cases again returned 10/10. In x86, all five cases returned 10/10 with automatic pinning. Before pinning, depth results varied substantially between runs, so CPU migration was a second source of instability. These observations do not establish that Windows or firmware caused the regression. The x86 ten-round AES-NI result differs from the paper's zero complete successes, showing that the paper's rates do not transfer directly to this newer machine and build.

The original repair output is in ignored `validation/.build/final-default-{aes,rsa}.txt` and `validation/.build/final-x86-{aes,rsa}.txt`; the portability follow-up output is in `validation/.build/final-{aes,rsa}-chain-{x64,x86}.txt` and `validation/.build/final-universal-*.txt`. Reproduce the hardware diagnostic with `python validation/limited_run.py -- python validation/build_cache_timing.py` followed by `python validation/limited_run.py -- validation/.build/cache_timing.exe`. The x64 and x86 `code_vectors.exe` programs passed. All reported successful runs stayed under the repository's 1.5 GB memory guard. The results are measurements on one i9-14900HX and Windows 11 25H2 system; the published percentages remain historical measurements from a different machine.

The verified x64 executables were also copied to the existing `build/msbuild/x64/Release/selfspectre.exe` and `spectrersa.exe` paths used by the author. The original binaries remain in ignored `validation/.build/original-{selfspectre,spectrersa}.exe`. The copied files were compiled by the focused MSVC script, because this sandbox blocked MSBuild's SDK discovery in `C:\Users\Gregory\AppData\Local\Microsoft SDKs`. A normal Visual Studio project rebuild will compile the changed sources; that exact build path was not rerun here.

## Portability follow-up (2026-10-18)

The focused Windows builder now checks CPUID before compiling the demos and selects RDTSCP or an RDTSC+LFENCE fallback. The executables report RDTSC, RDTSCP, CLFLUSH, SSE2, and AES-NI support before using the probe timer; AES skips its AES-NI modes when unsupported. Windows and Linux pin the sampling thread by default. The training parameters are named in `src/portable/we_spectre_params.h` (30 calls, six-call period, 100 delay spins, 999 attempts). They describe the experiment rather than cache geometry. AES calibrates against a shuffled full-array sweep as well as isolated hot/cold lines. RSA keeps its original single-line timing function and training macro shape, and a separate startup sweep rejects excessive background hits without changing the decoder's compiled layout. This check guards against the original 512-byte saturation but cannot establish speculative depth.

The non-MSVC CMake build now uses an SSE2 baseline and a compiler target attribute on AES-NI functions instead of enabling AES/SSE4.2 for every function. Native CMake configure probes CPUID for its timer choice; cross builds may set `SELFSPECTRE_FORCE_RDTSC`. A GCC 16 MinGW build of `spectreopt.c` and the deterministic `code_vectors` harness passed with `-msse2` and no global AES/SSE4.2 flag. An isolated CMake `try_run` of the portable timer probe also passed with GCC. The full Visual Studio CMake configure was blocked by this sandbox's denied read of `C:\Users\Gregory\AppData\Local\Microsoft SDKs`; a Linux speculative run and a CPU without AES-NI remain untested.

That restraint is empirical: a refactor of RSA timing changed the `readMemoryDword` position in the x64 image from RVA `0x1AC0` to `0x1AB0`; its depth results varied or failed on the same pinned CPU. Rebuilding with the exact earlier timing header returned all five short-depth cases to 10/10 correct and confident. This is evidence that generated code layout matters here, not a proof that this particular 16-byte shift is the sole mechanism. A cache threshold cannot calibrate the branch predictor or available speculation window. No Intel/AMD model whitelist can be inferred from the CPUID feature bits alone.

In new guarded default-timer runs pinned to logical CPU 0, x64 and x86 AES each returned 10/10 correct and confident for ten-round AES-NI and both one-round modes; the ten-round C mode remained 0/10. The RSA short-depth sweep returned 10/10 correct and confident in all five cases in both builds. One complete chained RSA run returned 158/160 correct groups on x64 and 159/160 on x86, illustrating run variation even on this machine; later runs with the startup sweep returned 160/160 in each width. Forced RDTSC builds passed the same five RSA depth cases and the three successful AES modes on x64 and x86. The first 32-bit fallback version failed because MSVC moved a C load outside the RDTSC pair; one x86 assembly block for both timestamps and the load restored the hot/cold split (28 versus 169 cycles in one run). These fallback tests were forced on an RDTSCP-capable i9-14900HX; a CPU that actually lacks RDTSCP and an AMD processor have not been measured here. Raw outputs are in ignored `validation/.build/{final-*,rsa-preflight-*,rsa-rdtsc-asm-x86,aes-rdtsc-asm-x86,rsa-rdtsc-fallback-x64,aes-rdtsc-fallback-x64}.txt`.
