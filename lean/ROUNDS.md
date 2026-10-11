# Rounds

State machine for `FORMALIZATION_PLAN.md`. Update at every round close.

| Round | Deliverable | State |
| --- | --- | --- |
| R0 | Bootstrap, vendoring, baselines | DONE (CI check of MathlibTM0 pending, user-run) |
| R1 | Errata inventory and claim map | DONE |
| R2 | WE machine, read-freedom, confinement | DONE |
| R3 | Turing-completeness (TC-U must; TC-B should) DONE (Mathlib composition with `MathlibTM0` deferred to CI, optional) |
| R4 | Arithmetic, division, modexp, Spectre arithmetic | DONE (vectors deferred to R7) |
| R5 | AES (should) | DONE (C21 AES-NI closed in R8) |
| R6 | Byte-level x86/x64 model, Figs. 5–7 (should) | DONE (C18 open; NZ, corrected layout, COFF comparison closed in R8) |
| R7 | Legacy corrections, native acceptance, errata TeX | DONE (author review pending) |
| R8 | Palomar package, CI, handoff | package done; CI and Palomar full preflight pending (push authorized, preflight dispatch not) |

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

### R4 (done)

- Scope (D1): the wide operations are proved at the *algorithm* level, over little-endian base-256 digit lists,
  with the 8-bit tables transcribed literally from the MASM macros (`Spec/Arith.lean`). The asm control flow
  (self-modifying jump tables, ADDBYTE/SUBBYTE/SHLBYTE macros) is tied to these algorithms by native vectors
  (R7), not proved; the byte-level jump-table behaviour is R6.
- The carry scheme modelled is the one in ADDBYTE: INC on the next first operand, with the second-level
  carry (`carry&Idx&_2`); the two carries are shown exclusive. SHL/SHR combine the shifted halves with XOR,
  proved equal to `+` by disjointness of bits (table facts).
- Proofs are Mathlib-free. Kernel `decide` over thousands of cases needs `List.all` checks in pieces of at most
  ~4,000 cases (`all1/all2/all3d` in `Arith/Tables.lean`); 65,536-case checks run out of the 768 MB cap.
- W03/W04/W05 proved: quotient overflow iff high word >= divisor; two-step reduction needs `%` (L03);
  multiplications = `log2 e + 1 + popcount e`. Legacy `mulmod` shown wrong at `65536*65536 mod 3`.
- Audit: 895 declarations, 0 violations.
- Open: test vectors (R7, generated from the specs with python); `could` items (left-to-right modexp) skipped.

### R5 (done)

- `Spec/AES.lean` (FIPS-197 spec + the WE procedure as position functions `weInit/weRound/weFinal`),
  `Spec/AESData.lean` (Te0..Te4 literals from writeexc.asm == spectreopt.c; `validation/gen_aes_tables.py`
  re-derives them). `AES/Checks.lean` is generated by `validation/gen_aes_chunks.py` (exhaustive 256-case checks).
- `AES/Equiv.lean`: `weCipher_eq` (WE procedure = FIPS cipher, invariant `sw (nval (f+1)) = state f`),
  with the asm key-byte order (`keyMem`) tied to FIPS round keys (`keyRel`). Level: algorithm (D1); the
  asm bytes themselves are R6/R7. C21 (AES-NI) not attempted.
- Audit: 1573 declarations, 0 violations. Pitfall: python `open()` defaults to cp1252 on Windows; pass `encoding='utf-8'`.

### R6 (done; C18 open)

- `Spec/X86.lean`: byte memory `Nat → Nat`, instruction subset (`C6 05`, `66 C7 05`, `C7 05`, `EB`, `E9`, `90`),
  fetch from the current bytes, x86 absolute / x64 RIP-relative effective address (`fld`, `ea`), `runN`.
  Addresses are assumed below `2^30` (text is 15 MB). Not vendored from smcTuring: a smaller own
  byte model fit the one-opcode-subset machine better (deviation from plan D4, recorded here).
- `X86/Basic` (decode round trip, step lemmas), `Patch` (operand patch lemmas), `Lookup` (`shl_lookup`: five steps,
  `table16_lookup`: NOP slide + entry), `Fig5` (`not_exec`, 14+ steps, writes confined to instruction fields),
  `NotTable` (published layout with the 3-byte shift from entry 248, corrected layout, W10 size theorems),
  `LayoutData` (generated by `validation/gen_x86_layout.py`: label and table offsets of both builds checked by
  `decide`), `Fig5Final` (`fig5_x86`, `fig5_x64`), `Fig7` (`carry_branch`).
- Image hypotheses (`NotImg`, `hEnt`) say the assembled bytes are the model's encodings; that they are is the
  R7 comparison (COFF bytes vs the Lean encodings), evidence not proof.
- Open: C18 (Fig. 6), the NZ table analogue (layout checked by data only), `compare_listings.py`.
- Audit: see validation/rounds/R6.json.

### R7 (done; author review of the errata PDF pending)

- L01-L05 applied as minimal diffs (commit fd49944, `lean/errata/minimal.diff`). L04 re-links the layout:
  the corrected threshold gives stride 16 for all NOT/NZ entries (Lean: `X86.w10_corrected_sizes`, `fig5_corrected`).
  The layout JSON in `validation/layout/` is still the *published* (pre-L04) extraction; re-extract with the
  listings workflow (validation/README.md) to confirm 16 B strides in the objects.
- Native acceptance: `python validation/limited_run.py -- python validation/native.py` builds and runs the legacy
  `writeexec` harness in Debug/Release x Win32/x64 with the corrected asm: all four print no mismatch.
  `native.py` previously looked for executables in stale directories; it now uses `writeexec/<cfg>` and
  rejects executables older than the sources. Release|Win32 can fail under the cap with `LNK1158 rc.exe`; rerun it alone.
- Vectors (`validation/gen_vectors.py` -> `validation/native/vectors.h`, `code_vectors.c`, `native_vectors.py`): exact
  Python vectors for the corrected C `mulmod`/`fastmodexp`/`modexp` (4029 + 1332 cases incl. mod 1 and the
  65536*65536 mod 3 counterexample) pass. WE entry points are tested by the existing randomized differential harness;
  edge-case vectors against the assembled WE procedures are not added (evidence only).
- Errata: `lean/errata/selfspectre-2019-errata.tex` (generated by `validation/make_errata.py` from `edits.json`),
  PDF `output/pdf/selfspectre-2019-errata.pdf` (1 page). `audit_errata.py`: inventory (all `before` found in the
  published text), `--pdf` (<= 3 pages), `--refs` (writes `lean/ErrataRefs.lean`; builds, so every Lean reference exists).
- Open: author review (the user); COFF-vs-Lean byte comparison (`compare_listings.py`) not done.

### R8 (package built; CI pending)

Gap closing before the package:
- C21: `AES/AesNi.lean` (`aesNi_eq`). NZ analogue: `Fig5`/`NotTable` generalized over the table function `F`; `fig5_nz_x86/x64`.
- L04 confirmed on the assembled objects: `run_listings.py lstc` + `extract_layout.py lstc` give `validation/layout/{x86,x64}c.json`;
  `LayoutData` now has the `x86c`/`x64c` layouts (`*c_geometry`, `*c_notres_offsets`), `Fig5Final` has `fig5c_*` (14 steps for every `k`).
- `compare_listings.py`: 3092 Lean-encoded byte strings equal the relocated COFF `.text` (published and corrected, x86 and x64).
- Still open: C18 (Fig. 6, `WriteExecXOR` copy loop; the arithmetic is C08), WE-entry edge vectors against the assembled procedures,
  author review of the errata PDF.

Package:
- `Spec/Paper.lean` (eight results) and `Paper.lean` (proofs); `Spec/Confinement.lean` holds the C04 vocabulary moved out of `Model/Confinement`.
- `validation/make_challenge.py` -> `lean/Challenge.lean` (706 lines, 50 KB: over the preferred 300 lines/32 KiB, under the hard 1,000/100 KiB limits;
  AES tables are 17 KB of it - disclosed warning). `Solution.lean`, `comparator.json` (one theorem, eight definitions, standard axioms),
  `formalization.yaml` (validated by `validation/palomar/validate_metadata.py` against the pinned v0.4 schema and taxonomies: pass),
  `PALOMAR_SEMANTICS.md`, `LICENSE_AUDIT.md` (root `LICENSE` is now pure MIT; the spectre.c notice moved to `THIRD_PARTY_NOTICES.md`).
- Local verification: all Mathlib-free modules, `Challenge` and `Solution` build under the guard; `axiom_audit.py Solution`: 1590 declarations, 0 violations.
  CI-only (never built locally): `Base/MathlibTM0`, root `WriteExecute`, the Mathlib cache.
- `.github/workflows/proof.yml` (Linux cold build + audits; Windows native acceptance) and `palomar-full.yml` (`request_id: selfspectre001`).
- Palomar policy refresh 2026-10-11: PalomarPolicy `96b034cc31a72a63d4f4041911dce337a85c9a04`, PalomarSubmission
  `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, formalization.yaml schema `99c678e569c7c4c0772db297c5ddd5e4c9b6322e` (unchanged pins).
- Next: run `proof.yml` on the pushed commit; fix failures; record in `FINAL_ACCEPTANCE.json`; then, only on the user's instruction,
  dispatch `palomar-full.yml` with the exact commit. Never submit or register without a separate instruction.
