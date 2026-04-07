# Self-Spectre, Write-Execute and the Hidden State

Code supplement to the peer-reviewed paper published in **Tatra Mountains Mathematical Publications**, Vol. 73 (2019):

> Gregory Morse, *Self-spectre, write-execute and the hidden state*,  
> Tatra Mountains Mathematical Publications, Vol. 73, 2019.  
> https://www.mat.savba.sk/ojs/index.php/TATRA/article/view/576

## Overview

This repository demonstrates two novel computation-hiding techniques applied to the AES-128 and RSA algorithms:

1. **Speculative execution side-channel** — performing arithmetic inside the CPU's speculative execution pipeline using Spectre-style branch-predictor training, with results recovered via cache timing. The program itself carries no conventionally observable data in registers or memory during the computation.

2. **Write-execute self-modifying code** — performing arbitrary computations by writing operands directly into instruction opcodes in the executable `.text` section and jumping to them, so that at no point during computation are operands present in registers or addressable memory — only encoded within the instructions themselves.

Either technique can support strong white-box cryptography: in binary form, both approaches are highly resistant to static analysis and conventional debugging.

## Repository Structure

```
selfspectre.sln          ← Visual Studio solution (all three projects)
spectre.c                ← Original Spectre v1 PoC (reference, not built)
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
```

## Projects

### `selfspectre` — AES-128 Spectre Demo
Demonstrates recovering AES-128 encryption round results via speculative execution and cache-timing side-channels. Uses `spectreaes.c` (entry point) and `spectreopt.c` (shared victim helpers), with the Spectre wrappers in `spectrecode.asm` and the write-execute arithmetic core in `writeexc.asm`.

### `spectrersa` — RSA Spectre Demo
Demonstrates speculative recovery of RSA modular-exponentiation intermediate values using varying exponentiation depths (1–8 squarings). Uses `spectrersa.c` (entry point) and `spectreopt.c` (shared helpers).

### `writeexec` — Write-Execute Arithmetic Framework
Standalone test harness for `writeexc.asm`. Exercises all write-execute primitives: bitwise operations (SHL, SHR, NOT, XOR, OR, AND), arithmetic (ADD, SUB, INC, DEC, MUL, DIV, MODEXP), and AES-128 table lookups (Te0–Te4, full AES round). Results are verified against standard C implementations and timed for performance comparison.

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

## Third-Party Code

`spectre.c` is the original Spectre v1 proof-of-concept from the paper:

> Paul Kocher et al., *Spectre Attacks: Exploiting Speculative Execution*,  
> IEEE Symposium on Security & Privacy 2019.  
> https://spectreattack.com/spectre.pdf

It is included for reference only and is not compiled into any project.

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
  url     = {https://www.mat.savba.sk/ojs/index.php/TATRA/article/view/576}
}
```

## License

Original source code in this repository is released under the MIT License — see [LICENSE](LICENSE).  
`spectre.c` retains its original authorship and is reproduced here as a reference document.
