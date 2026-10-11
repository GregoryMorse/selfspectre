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

1. **Speculative execution side-channel** — performing arithmetic inside the CPU's speculative execution pipeline using Spectre-style branch-predictor training, with results recovered via cache timing. The program itself carries no conventionally observable data in registers or memory during the computation.

2. **Write-execute self-modifying code** — performing arbitrary computations by writing operands directly into instruction opcodes in the executable `.text` section and jumping to them, so that at no point during computation are operands present in registers or addressable memory — only encoded within the instructions themselves.

Either technique can support strong white-box cryptography: in binary form, both approaches are highly resistant to static analysis and conventional debugging.

## Repository Structure

```
selfspectre.sln          ← Visual Studio solution (all four projects)
spectre.c                ← Original Spectre v1 PoC (spectrepoc project)
spectreopt.c             ← Spectre victim/helper functions (shared)
spectrecode.asm          ← MASM speculative-execution wrappers (x86/x64)
spectreaes.c             ← AES-128 Spectre attack demo (selfspectre project)
spectrersa.c             ← RSA modular-exponentiation Spectre demo (spectrersa project)
writeexec.c              ← Write-execute framework test harness (writeexec project)
writeexc.asm             ← MASM write-execute arithmetic/crypto primitives
tables.asm               ← Stub assembly (placeholder)

selfspectre/             ← VS project: AES Spectre demo
spectrersa/              ← VS project: RSA Spectre demo
writeexec/               ← VS project: write-execute framework
spectrepoc/              ← VS project: original Spectre v1 PoC
```

## Projects

### `selfspectre` — AES-128 Spectre Demo
Demonstrates recovering AES-128 encryption round results via speculative execution and cache-timing side-channels. Uses `spectreaes.c` (entry point) and `spectreopt.c` (shared victim helpers), with the Spectre wrappers in `spectrecode.asm` and the write-execute arithmetic core in `writeexc.asm`.

### `spectrersa` — RSA Spectre Demo
Demonstrates speculative recovery of RSA modular-exponentiation intermediate values using varying exponentiation depths (1–8 squarings). Uses `spectrersa.c` (entry point) and `spectreopt.c` (shared helpers).

### `writeexec` — Write-Execute Arithmetic Framework
Standalone test harness for `writeexc.asm`. Exercises all write-execute primitives: bitwise operations (SHL, SHR, NOT, XOR, OR, AND), arithmetic (ADD, SUB, INC, DEC, MUL, DIV, MODEXP), and AES-128 table lookups (Te0–Te4, full AES round). Results are verified against standard C implementations and timed for performance comparison.

### `spectrepoc` — Original Spectre v1 Proof-of-Concept
The unmodified Spectre v1 PoC from the original paper by Kocher et al. Reads an arbitrary secret string from process memory using branch-predictor training and cache-timing side-channels. Useful as a baseline to verify whether your CPU/OS has hardware or software mitigations in place: if it prints `Success` and recovers the secret, Spectre v1 is exploitable on your system; if scores are low or results are `Unclear`, mitigations are active.

Accepts optional command-line arguments: `[cache_hit_threshold] [address] [length]`. The default threshold is 80; lower values may help on CPUs with fast caches, higher values on systems with mitigation overhead.

## Building

### Requirements
- Visual Studio 2017 or later (v141/v145 platform toolset)
- MASM (`ml.exe` / `ml64.exe`) — included with Visual Studio C++ workload
- Windows 10 SDK
- x86 and x64 C++ build tools

### Steps
1. Open `selfspectre.sln` in Visual Studio.
2. Select **Build → Batch Build**, tick all configurations, and click **Build**.
3. Alternatively use the Configuration Manager to select a specific project and platform.

The PreLinkEvent in each project automatically invokes `ml.exe` (x86) or `ml64.exe /DX64` (x64) to assemble `writeexc.asm` and `spectrecode.asm` before linking.

### Configurations

| Configuration | Platform | Notes |
|---------------|----------|-------|
| Debug         | x86      | No optimisation; `/safeseh` not applied to ASM |
| Debug         | x64      | No optimisation; `ml64.exe /DX64` |
| Release       | x86      | `/O2`, COMDAT folding, `/safeseh` on ASM |
| Release       | x64      | `/O2`, COMDAT folding |

> **Note:** `spectreopt.c` is compiled with `MaxSpeed` optimisation even in Debug|x64 builds so that the victim function is not trivially defeated by the compiler.

## Lean formalization

The Write-Execute part of the paper is formalized in Lean 4 (`lean/`, toolchain `leanprover/lean4:v4.35.0-rc3`,
Mathlib pinned in `lean/lakefile.toml`). The selected statement `PalomarWE.mathematical_result`
(`lean/Challenge.lean`, proved in `lean/Solution.lean`) covers read-freedom of the ideal word-level machine,
Turing-completeness (with the finite-image caveat), confinement, the jump-table lookup and 8-bit tables,
wide arithmetic, division, modular reduction and exponentiation, AES-128 (T-tables and the Write-Execute
procedure against FIPS-197) and the Spectre index arithmetic. Supporting byte-level x86/x64 models of Figs. 5, 6 and 7
(including the Fig. 6 XOR copy loop, 35 and 38 steps) are checked against the assembled objects.

* `lean/PAPER_MAP.md` - every claim with its status; `lean/PALOMAR_SEMANTICS.md` - the selected statement and its model boundaries.
* `lean/errata/selfspectre-2019-errata.tex` (PDF in `output/pdf/`) - corrections W01-W10 to the published text, quoted from the
  published PDF; `lean/errata/minimal.diff` - code fixes L01-L05 (already applied to `writeexec.c`, `spectreopt.c`, `writeexc.asm`).
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
