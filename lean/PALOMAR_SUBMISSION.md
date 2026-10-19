# Palomar submission sheet (registered: PALOMAR-2026-10-14-000007 v1)

| Field | Value |
|---|---|
| Repository | GregoryMorse/selfspectre |
| Exact commit | fe720739a11adeb1e9e2b2b13948cc6a7586920d (registered; docs-only on top of 62e20ac83c2e6903c9d2bb3793253c59c99c0d17, which passed CI run 38375370566 and full preflight run 38376642196) |
| project_path | lean |
| Comparator config | lean/comparator.json |
| Metadata | lean/formalization.yaml |
| Selected statement | PalomarWE.mathematical_result (Write-Execute and Self-Spectre under an abstract speculation contract, C23-C26) |
| Registry entry | PALOMAR-2026-10-14-000007, version 1, registered 2026-10-14 by the author (https://palomar-registry.org/entry?id=PALOMAR-2026-10-14-000007&version=1); status registered, trust level high |

Notes: AI assistance (Claude) is disclosed in formalization.yaml. The model is ideal (unbounded). Warning: Challenge.lean is 851 lines / ~60 KB (hard limit 1000 / 100 KiB; preferred 300 / 32 KiB).
Closed since the first sheet: C18 (Fig. 6 byte-level proof, `X86/Fig6.lean`) and the WE-entry edge vectors (`validation/native_edge.py`).
Unverified: renderer on the new pin, Comparator/NanoDa run records, author errata review, research-interest review of the Self-Spectre results (an earlier submission of abb8273 was reviewed with a separately selected Spectre index-arithmetic result and flagged; that result was dropped and the contract-level Self-Spectre results added in R9).
Mathlib re-pinned 302343bb -> 5e043698 (same Lean v4.35.0-rc3) so that Plausible is fb13df7, the revision Verso pins; Mathlib 302343bb (Plausible afc2695) is rejected by the renderer's manifest merge (PalomarSubmission #166 / #131). Full preflight passed on the final commit.
Known: the legacy Debug|Win32 harness (`writeexec.c`, random checks) failed once in CI at the MODEXP32 check without recording operands. The same-input repeat telemetry and a focused modular exponentiation differential runner were added; the original cause remains open. Legacy signed-reference undefined behavior was repaired separately (legacy code is outside the proof).
Outcome: four submissions by the author (private records kept outside the repository). Automated reviews 1-3 requested
changes, each addressed in the Lean statement or the prose: (1) the separately selected Spectre index arithmetic was dropped;
(2) `VictimLeak` reload result stated from a cleared probe array; (3) the source note separates the unconditional Write-Execute
results from the conditional Self-Spectre results, `WindowDepth` states the observable leak from a cleared probe array and names
the touch-trace boundary, and `Mistraining` follows the PoC's descending loop. The fourth submission was registered as PALOMAR-2026-10-14-000007 v1.

## Candidate update after the native repairs

The registered version 1 above remains pinned to `fe720739a11adeb1e9e2b2b13948cc6a7586920d`.
For an ordinary version 2, submit the full SHA of the new, green commit on `master`, retain project
path `lean` and comparator path `lean/comparator.json`, and enter the existing Palomar ID
`PALOMAR-2026-10-14-000007`. The metadata title is "Write-Execute Computation and Self-Spectre".
The Lean statements
remain about the published PoC and an abstract speculation contract; the current calibrated native
demos use a different physical probe stride and reload order, as described in
`PALOMAR_SEMANTICS.md`. A new exact-commit Palomar preflight and review are required before the
author registers version 2. The author reviews the errata PDF separately.

The native Write-Execute assembly now branches after internal code patches at the 29 direct
fallthrough sites identified in `validation/README.md`. These are still Write-Execute jumps. The
selected Lean statement does not assert a CPU's store-to-fetch behavior, and its specifications and
proofs have not changed. The supporting `X86/LayoutData.lean` offsets for Fig. 7 were regenerated
from the new assembled objects and the affected modules were rebuilt. This source-level response to Intel's
sequencing recommendation is not a new paper claim or a demonstrated explanation of the rare native
mismatches.

The exact-commit full mechanical preflights for [`8f08771`](https://github.com/GregoryMorse/selfspectre/actions/runs/39156987622) and the later [`9451e72`](https://github.com/GregoryMorse/selfspectre/actions/runs/39159265367) passed. The [60-job Windows hunt #7](https://github.com/GregoryMorse/selfspectre/actions/runs/39156169406) found five transient MODEXP32 failures on virtualized AMD EPYC 7763 runners in both Win32 and x64. A pinned [control hunt #9](https://github.com/GregoryMorse/selfspectre/actions/runs/39160281020) failed in 4/60 jobs, and an exact-commit pinned [page-materialization hunt #10](https://github.com/GregoryMorse/selfspectre/actions/runs/39160318195) failed in 6/60 jobs, all on the EPYC 7763 runners. The latter included a `SHR32` mismatch after code-page copy-on-write had been removed from the measured calls. A subsequent [telemetry hunt #11](https://github.com/GregoryMorse/selfspectre/actions/runs/39161931493) failed in 11/60 jobs, again all on EPYC 7763 guests, with first-result errors in `MUL32`, `DIV32`, and `MODEXP32`. The [direct `SHR32` hunt #12](https://github.com/GregoryMorse/selfspectre/actions/runs/39162890255) captured an x64 shift-zero call returning exactly the current input shifted by seven, matching the preceding call's low three shift bits, although its entry patch byte read back as zero. The [extended hunt #13](https://github.com/GregoryMorse/selfspectre/actions/runs/39164051241) captured a Win32 shift-15 call returning exactly the input shifted by eight, with the entry patch byte at 15. The [four-field hunt #14](https://github.com/GregoryMorse/selfspectre/actions/runs/39164845425) failed in 7/60 jobs and captured a Win32 low-byte handoff missing after a shift-30 entry and an x64 wrong shift-11 output despite correct post-call count fields.

A separate deterministic Debug|x64 MSBuild crash was traced with `cdb` to an incremental-link jump thunk: a code patch targeting `WriteExecSHL6+2` was relocated to its ILT thunk, while execution entered the function body. Disabling incremental linking redirected the patch to the body, and the full local pinned Debug|x64 harness passed. This changes native build configuration, not a Lean statement or the Write-Execute model. The CMake Release links already disabled incremental linking.

The [bare-metal EPYC investigation](../validation/EPYC_7513.md) then found a
separate Linux ELF64 UASM relocation fault, repaired in CMake by normalizing
PC32 fields before linking. This object transformation does not change the
assembled algorithm or a selected Lean theorem. The same EPYC host reproduced
the rare first-result `SHR32` error while pinned to one CPU; the final result
used the preceding call's low shift bits. A one-site serialization experiment
and equal-length jump/NOP controls all failed, so no speculative SMC fix was
retained. A later final-image CTest run failed four native vectors across
MUL32, DIV32, and MODEXP32, while the same suite had passed twice earlier.
The calibrated AES/RSA demos did reproduce the paper's successful
cases on both sockets, with direct RSA depth eight also successful. Native
Write-Execute reliability on Zen 3 remains open; passing formal preflight
does not resolve it. The author should defer v2 registration until this
limitation is resolved or explicitly disclosed. A final exact-commit
preflight will be needed for whichever commit is submitted.
