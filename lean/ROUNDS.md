# Rounds

State machine for `FORMALIZATION_PLAN.md`. Update at every round close.

| Round | Deliverable | State |
| --- | --- | --- |
| R0 | Bootstrap, vendoring, baselines | DONE (CI check of MathlibTM0 pending, user-run) |
| R1 | Errata inventory and claim map | todo |
| R2 | WE machine, read-freedom, confinement | todo |
| R3 | Turing-completeness (TC-U must; TC-B should) | todo |
| R4 | Arithmetic, division, modexp, Spectre arithmetic | todo |
| R5 | AES (should) | todo |
| R6 | Byte-level x86/x64 model, Figs. 5–7 (should) | todo |
| R7 | Legacy corrections, native acceptance, errata TeX | todo |
| R8 | Palomar package, CI, handoff | todo |

## Handoff notes

### R0 (done by Sonnet 5.5, 2026-10-11)

- Authorizations: local commits on `master` yes; **push / GitHub Actions: no** (user does these).
- **Local builds:** Lake and any Mathlib import exceed the 1.5 GB commit cap (`failed to read file …olean.private`).
  Use `python validation/build_modules.py <Module>|all` (direct `lean.exe` under the guard, output in
  `lean/.lake/proof-build`). It skips modules that import Mathlib (CI-only): currently
  `WriteExecute.Base.MathlibTM0` and the root `WriteExecute`. `python validation/axiom_audit.py`
  audits all locally buildable modules (uses minimal `Lean.*` imports; `import Lean` also exceeds the cap).
- Vendored base: `WriteExecute/Base/{Memory,Turing}.lean` build and pass the audit; `MathlibTM0.lean` is
  unverified until the user runs CI (copied verbatim; namespace `WriteExecute.MathlibTM0`).
- Layout facts (x86 and x64 identical): **W10 confirmed.** `notres_247` and `nzres_247` occupy 19 bytes
  (all other NOT/NZ entries 16), shifting entries 248–255 by +3; lookups still work because landing
  3 bytes early falls in the preceding NOP tail. Fix L04: threshold `0f6h` → `0f7h` (re-extract to confirm
  stride 16 everywhere after the fix). SHLc tables stride 256, XOR/OR/AND group bases 8192: uniform.
- Purity: 28 core `WriteExec*` PROCs (x86 and x64) contain only `C6 05`, `66 C7 05`, `C7 05`, `E9`, `EB`, `90`
  (≈11.2 M instructions, 0 violations) — `validation/layout/purity.json`.
- `validation/extract_layout.py` needs the listings from `validation/.build/lst` (assemble with
  `ml /c /Fl /Sa` and `ml64 /c /DX64 /Fl /Sa`; see `asm.bat` recipe in `validation/README.md`). MASM's
  `Length=` wraps at 64 K, so use PROC/ENDP offsets from the listing body.
- Native baseline: see `validation/rounds/R0.json`.
