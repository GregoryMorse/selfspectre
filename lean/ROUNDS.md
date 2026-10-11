# Rounds

State machine for `FORMALIZATION_PLAN.md`. Update at every round close.

| Round | Deliverable | State |
| --- | --- | --- |
| R0 | Bootstrap, vendoring, baselines | DONE (CI check of MathlibTM0 pending, user-run) |
| R1 | Errata inventory and claim map | DONE |
| R2 | WE machine, read-freedom, confinement | DONE |
| R3 | Turing-completeness (TC-U must; TC-B should) DONE (Mathlib composition with `MathlibTM0` deferred to CI, optional) |
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

### R1 (done, 2026-10-11)

- Author unavailable; per the user, items were adjudicated on code, period architecture and published text.
  `lean/errata/edits.json` has W01-W10 (all excerpts verified on their pages by `validation/audit_errata.py --inventory`)
  and L01-L05. `lean/PAPER_MAP.md` is the ledger (C01-C22). MODEXP32 gets the documented precondition mod >= 2
  (asm initialises the result to 1); the C reference `fastmodexp` is fixed.
- W05 confirmed against the asm loop (square every iteration). W10 mechanically confirmed in R0.
- pdftotext must use `-enc UTF-8`; run python with `PYTHONIOENCODING=utf-8`.

### R2 (done)

- `Spec/Machine.lean`: `WE.State/Instr/Status/decode/step/run/Halts/Faults/Diverges/effect`
  (encodings MOV=[1,rel,val], JMP=[2,rel], HLT=[3]; displacements from the next instruction).
- `Model/Run.lean` (run_add, run_stop, trichotomy, exclusivity), `Model/ReadFree.lean` (C01),
  `Model/Confinement.lean` (C04, Mathlib-free list form). Audit: 219 declarations, 0 violations.
- Interfaces for R3: `run_add`, `run_succ_right`, `run_stop`, `trichotomy`; `write` from `Base.Memory`.

### R3 (done)

- `Spec/Universal.lean`: cell layout (`handlerSize`, `cellSize`, `handlerAt`, `entryDisp`, `cellWord`, `layout`),
  `encode`/`initial`, and the finite image `bounded`/`encodeB`. Handlers are never written; only the Q entry
  displacements of the current cell are (so every store targets a jump-displacement field).
- `Universal/Layout.lean`, `Step.lean` (generic over the base memory `L`; `cell_step_some_gen`: Q+2 steps),
  `Unbounded.lean` (C02: `simulate`, `halts_iff`, `diverges_iff`, `never_faults`),
  `Bounded.lean` (C03: `bounded_simulate`, `bounded_halts`, `bounded_faults` at the guard).
- Audit: 382 declarations, 0 violations. Not attempted: growth from a finite image; composition with
  `MathlibTM0` (CI-only, optional).
- Hazards for later rounds: `by_contra`, `push_neg`, `ring` are Mathlib-only; use `Classical.byContradiction`, `omega`.
  Build several modules in one `build_modules.py` call; bash heredocs with odd quoting fail, use the Write tool.

