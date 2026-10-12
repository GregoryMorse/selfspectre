# Write-Execute formalization plan

Planner: Claude Opus 5.5, 2026-10-11. Executor: Claude Sonnet 5.5 (medium effort), one
round per session. Reviewer and decision owner: Gregory Morse (author of the paper).

**How to use this file.** At the start of every session, read §0–§4 once (they are short) and then
**only the section of the current round** (state is in `lean/ROUNDS.md`). Do not re-derive
decisions recorded in §2; if one blocks you, stop and ask the user. Do not browse smcTuring beyond
the exact paths named here — it has 1,150 Lean files and reading them wastes the budget.

---

## 0. Target

**Paper.** G. Morse, *Self-Spectre, Write-Execute and the Hidden State*, Tatra Mt. Math. Publ.
73 (2019) 131–144, DOI 10.2478/tmmp-2019-0010. Published PDF:
`https://sciendo.com/pdf/10.2478/tmmp-2019-0010` (219,605 bytes, SHA-256
`8d9b4072ed8e1a9dca8b7a304af917020f9f1f72d7894710dbe2e903056c1940`). The PDF itself states
CC BY-NC-ND 4.0; the publisher page says 3.0 — record both, cite the PDF.
The pre-final draft `D:\OneDrive\Documents\Projects\ELTE\cecc2018\SelfSpectreWriteExecuteTheHiddenStateJournalPaper.tex`
is reference only (read in place, never commit it). **Errata always quote the published PDF.**

**Published numbering differs from the draft.** Use these labels everywhere:

| Published | Content | Page |
|---|---|---|
| Fig. 1 | branch-predictor mistraining (branchless select) | 134 |
| Fig. 2 | victim function | 136 |
| Fig. 3 | AES-128 via AES-NI intrinsics | 137 |
| Fig. 4 | depth sample output | 138 |
| Fig. 5 | `not` via jump table (`DEFINENOT`) | 140 |
| Fig. 6 | `xor` copy loop / double lookup | 141 |
| Fig. 7 | 32-bit `add` carry conditional jump | 142 |
| Tables 1–4 | speculative results / timings | 137–142 |

**In scope (formalize):** the Write-Execute (WE) model and everything mathematical or algorithmic
in the paper: the model's read-freedom, Turing-completeness (corrected statement), jump-table
primitives, multi-byte arithmetic, division/overflow statements, modular exponentiation and its
multiplication count, AES T-table math, and the small arithmetic facts inside the Self-Spectre
section (Fig. 1 select, p.134 `mix_i` permutation, Fig. 3 AES-NI sequence as a stretch goal).

**Out of scope:** speculative execution, cache timing, branch-predictor behaviour, measured
tables/timings, microarchitecture. These are recorded in the errata only when a statement is
verifiably wrong against a primary source, never "proved".

**Final deliverables (definition of done).**
1. `lean/` Lake project: zero `sorry` outside `Challenge.lean`, only the axioms `propext`,
   `Quot.sound`, `Classical.choice`; cold CI build + axiom audit passing on GitHub.
2. Palomar package: `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`;
   the official Palomar full mechanical preflight passing on an exact public commit;
   `lean/PALOMAR_SUBMISSION.md` with form values. The user performs the actual submission.
3. Errata: `lean/errata/selfspectre-2019-errata.tex` → reviewed PDF (≤ 2 pages target, 3 max),
   `edits.json`, `minimal.diff`, every item with a Lean reference or an explicit
   "editorial (not formalizable)" class and a primary-source citation.
4. Legacy code corrections applied to the repo sources with a passing native validation on all four
   configurations (Debug/Release × Win32/x64).
5. README section describing the formalization, with links.

---

## 1. Facts established during planning (do not re-verify unless a gate fails)

* **WE core is register- and stack-free.** Every `WriteExec*` PROC in `writeexc.asm` uses only
  `mov byte/word/dword ptr [m], imm` (`C6 05`, `66 C7 05`, `C7 05`), `jmp rel8/rel32` (`EB`, `E9`)
  and `nop` padding (`90`). Registers, `ret` and stack use occur only in the `*_C` C-ABI wrappers
  (they patch argument immediates from `cl/dl/...` and `ret`). The paper's "stack exception"
  (call/push/pop) is never used. R0's purity scan turns this into checked evidence.
* **Data lives in instruction fields.** Arguments are patched into `imm8` fields; a lookup patches a
  byte/word of an `E9` rel32 (e.g. `jmp shlres_0+08000h` = `E9 00 80 00 00`; writing byte `k` at
  `+2` gives `rel32 = 256k`), landing on a fixed-stride table entry that writes its constant result
  and jumps on. Copying re-executes one `mov` after retargeting its address field (Fig. 6 loop).
  x86 uses absolute `disp32`; x64 uses RIP-relative `disp32` (hence the `ifdef X64` forms).
* **Strides:** SHLc tables 256 B/entry; NOT/NZ 16 B; AND/OR/XOR/ADD/SUB groups 8192 B with 16 B
  entries; SHL/SHR general 32 B; Te0–Te4 64 B (`SHL6`). The asm Te tables are literal constants.
* **Possible layout defect (Fig. 5):** `DEFINENOT`/`DEFINENZ` pad 7 NOPs when `Index GT 0f6h`
  (assuming a 2-byte `EB`), else 4. By distance arithmetic the short form only reaches `notres`
  from index ≥ 0xF8, so entry 0xF7 is likely 19 bytes, shifting later entries by 3; lookups for
  k ≥ 0xF8 then land in the previous entry's NOP tail and slide into the right entry. Functionally
  correct, stride violated. **Unconfirmed — R0 extracts the real MASM layout and decides.**
* **Arithmetic edge cases found:** `fastmodexp(b,0,1)` and WE `MODEXP32` return 1, but
  `b^0 mod 1 = 0` (result initialised to 1, never reduced). `spectreopt.c` `mulmod` uses `/` where
  the two-step reduction needs `%` (dead code, wrong). `writeexec.c` diagnostics for Te1–Te4 print
  `Te0[i]` (and Te4 prints the stale `result32`); comparisons themselves are correct.
* **smcTuring reuse:** its x86 byte machine (`Appendix/ByteCode.lean`, `Native/Execution.lean`) is
  tailored to its own opcodes (`C7 05` imm32, `E8`, `xchg`...) and carries accumulator/stack
  state — do **not** reuse it. Reuse the generic layers only (§2 D4). The full smcTuring proof
  infrastructure (remote servers, 180 KB `run_lean.py`, evidence JSON) is deliberately **not** copied.

---

## 2. Decisions (made; ask the user before deviating)

**D1 — Two-level model.** Principal results use an *ideal word-level WE machine* (§R2). The real
x86/x64 encodings are a *supporting byte-level model* (§R6) used for Figs. 5–7. Arithmetic and AES
are proved at the *algorithm level* (functions transcribed from the asm macros), tied to the actual
asm by native differential testing (evidence, disclosed as such).

**D2 — What "Turing-complete" means (the key scope decision).** Without reads, data can only move
by executing instructions whose immediates hold it. A write instruction is larger than what it
writes (word model: 3 words to write 1), so a cell of code cannot write a full copy of itself, and
control can never return to a fixed location from an unbounded distance using only relative
displacements. A WE program therefore cannot grow a fresh tape from a finite image by any
straightforward construction, and with absolute addressing it cannot address beyond the finitely
many addresses in its own immediates. We prove, and the errata state:
* **(TC-U, must)** With RIP-relative writes/jumps and an unbounded code memory pre-initialised
  with a periodic blank-cell template (the WE analogue of a blank tape), one finite construction
  per TM simulates it exactly: halting ↔ halting, divergence ↔ divergence, never faults, and every
  simulated configuration is observable on the same trace.
* **(TC-B, should)** For every `n`, a *finite* image (cells −n..n plus fault guards) with **arbitrary
  background memory** simulates the TM exactly while the head stays in [−n, n] and faults exactly
  when it leaves. Hence TM halts ↔ ∃ n, image n halts.
* **(CONF, should)** Any WE run that never fetches outside a finite address set has finitely many
  reachable states (all written values and addresses come from its finite image). This is why an
  unbounded idealisation is needed, exactly as for every physical computer.
* **Not attempted:** growth-based universality from a finite image with arbitrary background
  (open; no claim either way). Do not spend effort on it.

**D3 — Fidelity standard.** Formal = Lean kernel. Mechanical evidence = MASM objects, purity scan,
byte comparison, native tests (CI). Editorial = errata with citation. Never present evidence as
proof. Every `PAPER_MAP.md` row names its class.

**D4 — Reuse by vendoring, not a subproject.** Only ~1,000 lines of smcTuring are useful; a Lake
dependency would couple toolchains and confuse Palomar review. Copy from the audited smcTuring
commit `1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4` (`git -C ../smcTuring show 1ab379c:<path>`),
rename namespaces `SmcTuring.*` → `WriteExecute.*`, change nothing else unless required to compile,
and record source path, source SHA-256, target path and edits in `lean/VENDORED.md`. smcTuring is
CC0, compatible with this repo's MIT license.

| smcTuring source (lean/SmcTuring/…) | Target (lean/WriteExecute/Base/…) | Use |
|---|---|---|
| `Memory.lean` (55 lines) | `Memory.lean` | `write` + frame lemmas |
| `Turing.lean` (120) | `Turing.lean` | `TM.Machine`, `Configuration`, `step/run`, `Halts`, `Diverges`, `diverges_iff_not_halts` |
| `MathlibTM0/Compiler.lean` (186) | `MathlibTM0.lean` | Mathlib `Turing.TM0` → `TM.Machine` compiler + `Rep` |
| `MathlibTM0/Simulation.lean` lines 1–83 only | append to `MathlibTM0.lean` | `source_halts_eval`, `compiler_respects`, `standard_halts_iff`; drop/re-prove anything importing `SMC.*` |
| `Native/LittleEndian.lean`, `Native/Encoding.lean`, `Native/ByteMemory.lean` | same names | byte memory, `putBytes`, `bytesAt`, `patch_payload`, `put_frame` (R6) |
| lemmas `put_bytes_back`, `put_bytes_commute` (`Native/Writes.lean`), `bytes_at_take` (`Native/Fetch.lean`), `put_bytes_append`, `patch_middle` (`Appendix/ByteCode.lean`) | `ByteLemmas.lean` | cherry-pick statements+proofs; re-prove if their imports drag in `Native.Execution` |

Infrastructure copied (adapt paths/names, keep behaviour): `validation/limited_run.py`,
`validation/memory_budget.py`, `validation/lean_build.py`, `validation/prepare_mathlib.py`,
`validation/palomar/{fetch_policy_assets,refresh_policy,validate_metadata}.py`,
`.github/workflows/palomar-full.yml`, and as *templates only*: `lean/errata/morse-2018-errata.tex`
(two-column compact layout), `lean/errata/POLICY.md`, `lean/errata/edits.json` schema,
`lean/formalization.yaml`, `lean/comparator.json`, `lean/Challenge.lean` header style,
`lean/PALOMAR_{SUBMISSION,SEMANTICS,AUDIT}.md`, `lean/LICENSE_AUDIT.md`.

**D5 — Pins.** Lean `leanprover/lean4:v4.35.0-rc3` (commit `470d5ce1400764999581fd26d5d72b00d990b0f4`),
Mathlib `5e043698502894993991089b2dd893867c0db5c2` — identical to smcTuring, so vendored code
compiles unchanged and the Palomar pipeline is known to accept them. Palomar reusable workflow
`PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`,
profile `palomar-standard-v1`, schema rev `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`; re-check for
newer required pins in R8 only.

**D6 — Spec modules are the Challenge surface.** Every definition that appears in a selected
statement lives in `lean/WriteExecute/Spec/*.lean`: core/Mathlib imports only, `@[expose] def`,
compact, no lemmas. R8 generates `Challenge.lean` from them mechanically
(`validation/make_challenge.py`), so Challenge and development cannot drift. Proofs live elsewhere.
Use smcTuring's file header style: `module` / `public import …` / `public section`.

**D7 — Tactic and axiom policy.** Forbidden: `sorry`/`admit` (outside Challenge), `axiom`,
`native_decide`, `bv_decide`, `Lean.ofReduceBool`, `implemented_by` in Spec, `unsafe`. `decide` is
fine for ≤ 256-case kernel checks over `Nat`/`Fin`/`BitVec 8` with GMP-accelerated `Nat` ops; for
65,536-case facts use a structural proof (`BitVec` extensionality, `Nat.testBit`) or 256 lemmas of
256 cases. `maxHeartbeats` above 400000 only with a one-line justification comment.

**D8 — Compute.** Local builds run serially through the 1.5 GB guard (`validation/limited_run.py`).
No SSH/remote servers (the smcTuring authorisation does not carry over). Cold full builds,
axiom audit and the Palomar preflight run on GitHub Actions. Most modules import only `Init`;
only `Base/MathlibTM0.lean`, `Universal/Mathlib.lean` and `Challenge.lean` import Mathlib.

---

## 3. Target layout

```
CLAUDE.md                          standing rules (auto-loaded)
FORMALIZATION_PLAN.md              this file
lean/
  lean-toolchain  lakefile.toml  lakefile.proof.toml  lake-manifest.json
  WriteExecute.lean                root import
  WriteExecute/Base/*.lean         vendored (D4)
  WriteExecute/Spec/{Machine,Universal,Arith,AES,Spectre,Paper}.lean   Challenge surface (D6)
  WriteExecute/Model/{Run,ReadFree,Confinement}.lean
  WriteExecute/Universal/{Layout,Cell,Step,Unbounded,Bounded,Mathlib}.lean
  WriteExecute/Arith/{Tables,Add,Sub,Shift,Xor,Mul,Div,Reduce,ModExp,Count}.lean
  WriteExecute/AES/{GF,SBox,Cipher,TTable,Lookup,Vectors,AesNi}.lean
  WriteExecute/Spectre/{Mix,Select}.lean
  WriteExecute/X86/{ISA,ReadFree,Jump,LayoutData,Fig5,Fig6,Fig7,Export}.lean
  WriteExecute/Paper.lean          proofs of the Spec/Paper Props
  Challenge.lean  Solution.lean  comparator.json  formalization.yaml        (R8)
  ROUNDS.md  VENDORED.md  PAPER_MAP.md (PAPER_MAP doubles as the proof ledger)
  errata/{POLICY.md, edits.json, minimal.diff, selfspectre-2019-errata.tex}
  PALOMAR_{SEMANTICS,SUBMISSION}.md  LICENSE_AUDIT.md  FINAL_ACCEPTANCE.json
validation/
  limited_run.py memory_budget.py lean_build.py prepare_mathlib.py
  axiom_audit.lean  axiom_audit.py  make_challenge.py  audit_errata.py
  native.py  extract_layout.py  purity_scan.py  compare_listings.py  Vectors.lean
  native/we_vectors.c              vector-driven harness linking writeexc.asm
  layout/{x86,x64}.json  reference/tmmp-2019-0010.{pdf,txt}  rounds/R*.json
  palomar/…
.github/workflows/{proof.yml, palomar-full.yml}
```

Add `lean/.lake/`, `validation/.build/`, `validation/.cache/` to `.gitignore`.

---

## 4. Global rules

**Economy.**
1. One round per session. Read only the current round. Build only touched modules
   (`lean_build.py WriteExecute.Arith.Div`), full build once at round close.
2. Modules ≤ ~300 lines. State the theorem first, then prove; commit compiling increments.
3. A proof obstacle gets at most three focused attempts. Then: weaken or split the statement with an
   explicit hypothesis, note it in `PAPER_MAP.md` as an open obligation, and move on. Only a named
   obstacle (one specific lemma) justifies raising effort. Scope changes go to the user.
4. Evidence is minimal: one `validation/rounds/Rk.json` per round (commit, commands, pass/fail,
   peak memory from the guard report). No other evidence bureaucracy.
5. Prefer `simp`, `omega`, `decide` (small), structural induction; avoid giant `simp` sets and
   unfolding long runs — prove `run_add`/composition lemmas and use them.

**Process.**
* All build/test commands: `python validation/limited_run.py -- <cmd>` (serial, 1.5 GB cap).
  A capped failure is a failed check; never retry without the guard.
* Once authorised (recorded in `CLAUDE.md`), commit at every green increment on `master` with a
  clear message ending with the attribution line from the system prompt; push only if pushes were
  authorised too.
* Round close: full `lean_build.py WriteExecute`, `axiom_audit.py`, round gate, update
  `lean/ROUNDS.md` (state + 5-line handoff: what's done, what's next, open obligations),
  `PAPER_MAP.md`, `edits.json` `lean_refs`, `validation/rounds/Rk.json`, commit.
* Batch user questions: at most one `AskUserQuestion` per round, at the start, only for decisions.

**Errata policy** (copy to `lean/errata/POLICY.md` in R1): preserve the published algorithm and
make the smallest local correction that states its intended, provable result; quote the published
PDF exactly (verify against the PDF, not the text extraction, for hyphenation/ligatures); never
attribute extraction artifacts to the paper; each formal item cites ≥ 1 Lean declaration, each
editorial item cites a primary source; code fixes are minimal diffs with a native re-test.

---

## 5. Seed inventory (verify in R1; IDs are stable)

Paper (W) — confirmed present in the published PDF unless marked:

| ID | Location (approx. page) | Published text → correction | Class |
|---|---|---|---|
| W01 | §4 end, p.142 | "Turing-completeness could be readily proven from the model as already presented" → precise statement per D2 (TC-U, TC-B, CONF) | formal |
| W02 | §1 p.132 and §4 opening | Model definition made precise: executed core instructions are immediate stores or direct jumps; operands come only from the fetched encoding; C-ABI wrappers are host interface, outside the model; stack exception unnecessary | formal + mechanical |
| W03 | §4 primitives list, ~p.139 | "division with a 64-bit divisor, and 32-bit dividend, quotient and remainder" → "division of a 64-bit dividend by a 32-bit divisor, giving the 32-bit remainder and the quotient modulo 2^32 (exact iff the dividend's high half is less than the divisor)" | formal |
| W04 | §3 p.136 | "a 64-bit divisor divided by a 32-bit dividend … the quotient cannot overflow 32-bits of output, the remainder potentially can" → dividend/divisor swapped; the remainder always fits; the quotient overflows unless high half < divisor, which holds when both factors are reduced mod the divisor; two-step reduction avoids overflow | formal |
| W05 | §3 p.136 | "log2 E + count_bits(E) modular multiplications" → exact count of the implemented right-to-left method, ⌊log₂E⌋ + 1 + popcount(E) for E ≥ 1 (naive: E) — confirm the asm squares on the last iteration | formal |
| W06 | §3 discussion, ~p.139 | "6 rounds … 93+5*44 or 70 instructions" → likely "93+6*44" (Table 2 pattern 53+2·44, 73+4·44, 83+5·44) | editorial — **ask author** |
| W07 | p.131 | MSC 2010 "62K05" (optimal statistical designs; template residue) → author's choice, e.g. 68M25 / 94A60 | editorial — **ask author** |
| W08 | §2 ~p.134 | `_mm_stream_ps` "flushes the cache 4 bytes at a time" → it is a 16-byte non-temporal store (MOVNTPS), not a flush; cite Intel SDM | editorial — **ask author** |
| W09 | §2 p.133 | Meltdown "256 local 512-byte pages" → Meltdown uses 4096-byte pages; 512 is the Spectre PoC stride; cite Lipp et al. | editorial — **ask author** |
| W10 | Fig. 5 p.140 | `IF Index GT 0f6h` → `GT 0f7h` **only if** R0 layout shows entry 0xF7 is 19 bytes; otherwise drop. Even then the original is functionally correct via NOP slide (prove it) | formal/mechanical, conditional |
| W11 | §4 p.139; Figs. 6–7 | `ONLY64` is presentation notation; source uses `ifdef X64` with the RIP-relative term | editorial, optional |
| W12 | §2 p.133 | "RSRE" → "RSRR" (Rogue System Register Read) | editorial, optional |

Keep the published errata compact: drop optional items if the PDF would exceed two pages.

Legacy code (L):

| ID | File | Fix | Test |
|---|---|---|---|
| L01 | `writeexec.c` ~680–706 | diagnostics print `Te1/Te2/Te3/Te4[i]` and `result`; `%04X` for 9-bit values | harness |
| L02 | `spectreopt.c` `fastmodexp` | `uint32_t result = 1 % mod;` | vectors incl. `mod = 1` |
| L03 | `spectreopt.c` `mulmod` | `/` → `%` in the high-half reduction (matches the Lean two-step lemma) | unit vectors |
| L04 | `writeexc.asm` `DEFINENOT`, `DEFINENZ` | threshold `0f6h` → `0f7h` (conditional on W10) | layout + harness |
| L05 | `writeexc.asm` `WriteExecMODEXP32` | precondition comment `mod >= 2` (RSA moduli), harness excludes `mod = 1` for the WE call — unless the author prefers a code fix | vectors |

Paper claims to formalize (seed for `PAPER_MAP.md`): C01 read-freedom (W02); C02 TC-U; C03 TC-B;
C04 CONF; C05 generic jump-table lookup; C06 8-bit primitive tables NOT, NZ, SHL1/4/5/6/7, INC, DEC,
AND, OR, XOR, ADD (9-bit), SUB (9-bit borrow), SHL/SHR general; C07 ADD/SUB 32/64; C08 SHL/SHR 32/64,
XOR32; C09 MUL 32×32→64; C10 DIV/MOD 64/32 (W03); C11 overflow facts + two-step reduction (W04);
C12 MODEXP (m ≥ 2) + count (W05); C13 AES T-tables = algebraic definition and = literal tables;
C14 T-table round = FIPS-197 round, final round with Te4; C15 WE AES lookup procedure = AES-128
encryption given round keys (+ FIPS-197 C.1 vector); C16 Fig. 5 byte-level; C17 Fig. 7
byte-level; C18 Fig. 6 byte-level + re-executability ("safely re-executable", p.141); C19 Fig. 1
select; C20 `mix_i` is a permutation of 0..255; C21 Fig. 3 AES-NI sequence (stretch); C22 asm
ShiftRows index formulas (asm comments) = FIPS ShiftRows.

---

## Rounds

Sizing: one session each unless noted. Priority tags: **must** / should / could. If budget runs
short, the **must** items alone still give a Palomar-ready result (§ "MVP path").

### R0 — Bootstrap, vendoring, baselines (must)

1. **Authorisation question (only question this round):** may the agent make local commits on
   `master` at green increments, push to `origin` at round close, and run GitHub Actions? Record the
   answer in `CLAUDE.md`.
2. Create the Lake project (D5): `lean/lean-toolchain`, `lakefile.toml` (package `selfspectre`,
   `defaultTargets = ["WriteExecute"]`, `[leanOptions] autoImplicit = false`, mathlib `require` at
   the pinned rev, `[[lean_lib]] name = "WriteExecute"`), `lakefile.proof.toml` identical plus
   `buildDir = ".lake/proof-build"`. Start `lake-manifest.json` from smcTuring's (same pin; rename
   package). Fetch the Mathlib cache with the adapted `prepare_mathlib.py`.
3. Copy and adapt infra (D4). Check `limited_run.py` on a trivial command and confirm its report.
4. Vendor Base files (D4 table) + `lean/VENDORED.md`; root `WriteExecute.lean` imports them. Build.
5. Write `validation/axiom_audit.lean` (~40 lines): a `#eval` meta-program that walks the
   environment for constants with prefix `WriteExecute` (and later `PalomarWE`), runs
   `Lean.collectAxioms`, and fails on anything outside the standard three or on `sorryAx`;
   `axiom_audit.py` wraps it via `lake env lean` and writes a summary.
6. Reference PDF: download (URL §0), check size+SHA-256, `pdftotext -layout` (MiKTeX's
   `pdftotext` is installed) → `validation/reference/tmmp-2019-0010.{pdf,txt}`; commit both.
7. `validation/native.py`: locate MSBuild via `vswhere`; build `writeexec` (and compile-check the other
   three projects) for Debug/Release × Win32/x64; allow `--toolset v143` override for CI runners
   (projects use v145); run `writeexec.exe`; pass = no mismatch lines (the harness prints only on
   mismatch, then timings). Record in `validation/rounds/R0.json`.
8. `validation/extract_layout.py`: assemble `writeexc.asm` with `ml /c /Fl /Sa` and
   `ml64 /c /DX64 /Fl /Sa` into `validation/.build/`; parse the listings (they give offsets for
   local labels, which COFF does not) and the COFF `.text` bytes. Emit `validation/layout/{x86,x64}.json`
   with: offsets of the labels used by Figs. 5–7 and their helpers (`notarg`, `notargshl`,
   `notres_0`, `notres`, `notret`, `shlarg4`, `shlres4_0`, `shlres4`, `shlret4`, `shlarg`,
   `shlres_0`, `shlres`, `shlret`, the XOR labels of Fig. 6, and one `ADDBYTE` instance's
   `carry1/carry1retval/nocry1/hascarry1`); for NOT, NZ, SHL1/4/5, XOR group 0 and the XOR group
   bases: each entry's start offset and jump form (`EB`/`E9`). Settle W10 here.
9. `validation/purity_scan.py`: linear-sweep decode every non-`_C` `WriteExec*` PROC range from the
   COFF bytes with a decoder for exactly `{C6 05, 66 C7 05, C7 05, E9, EB, 90}`; report unknown
   bytes with listing line. Expect pass (§1). Commit the report.
10. Create `lean/ROUNDS.md` (R0–R8 table, state, handoff notes).

**Gate:** vendored Base builds under the guard; `axiom_audit.py` passes; native baseline passes in
all four configurations; layout JSON and purity report committed; W10 decided.

### R1 — Errata inventory and claim map (must; text work, short)

1. One `AskUserQuestion` batch: W06, W07, W08/W09 wording, L05 (precondition vs code fix), and any
   new author-judgement item found below.
2. For each W item: find the exact published excerpt (PDF page/line), confirm or reject, fix the
   page number. Scan §§3–4 of the published text once for further *mathematical/algorithmic*
   errors only (no typo hunting).
3. Write `lean/errata/edits.json` (fields: `id, page, location, kind (replace|insert_after|clarify),
   before, after, class (formal|mechanical|editorial), status, lean_refs[], code_refs[], source`),
   `lean/errata/POLICY.md` (§4 text), and `lean/PAPER_MAP.md` (C01–C22 + any new: paper location,
   intended declaration, class, round, status).
4. `validation/audit_errata.py --inventory`: every `before` occurs in the reference text after
   normalising whitespace, hyphenation and ligatures.

**Gate:** inventory audit passes; every W/L item has a class and planned evidence.

### R2 — The WE machine, read-freedom, confinement (must; CONF should)

`Spec/Machine.lean` (all `@[expose]`):

```lean
namespace WriteExecute.WE
structure State where
  pc  : Int
  mem : Int → Int
-- encodings: MOV = [1, r, v] (3 words), JMP = [2, r] (2 words), HLT = [3]; anything else faults.
-- Displacements are relative to the NEXT instruction (x64 RIP-relative convention).
inductive Instr | mov (rel val : Int) | jmp (rel : Int) | hlt
def decode (m : Int → Int) (pc : Int) : Option Instr := …      -- reads m pc, m (pc+1), m (pc+2) only
inductive Status | running | halted | faulted
def step (s : State) : Status × State :=
  -- mov r v : (running, ⟨s.pc+3, write s.mem (s.pc+3+r) v⟩)
  -- jmp r   : (running, ⟨s.pc+2+r, s.mem⟩)
  -- hlt     : (halted, s);  none : (faulted, s)
def run : Nat → State → Status × State      -- stops at the first non-running status
def Halts (s) : Prop := ∃ n t, run n s = (.halted, t)
def Faults (s) : Prop := ∃ n t, run n s = (.faulted, t)
def Diverges (s) : Prop := ∀ n, (run n s).1 = .running
```

`Model/Run.lean`: `run_add`, determinism, `Halts`/`Faults`/`Diverges` pairwise exclusive and
exhaustive.

`Model/ReadFree.lean` (C01): an explicit `effect : Int → Int → Int → Int → Option (…)` of
`(pc, m pc, m (pc+1), m (pc+2))` with `step s` determined by `effect` applied to `s` — i.e. the only
memory the machine reads is its fetch window and it has no other state; every executed instruction
is a write into memory or a control transfer; `step_congr`: equal pc and equal window ⇒ equal
written address, written value and next pc.

`Model/Confinement.lean` (C04): if every reached state of a run from `s₀` has `pc ∈ A` for a finite
`A : Finset Int`, then every written value lies in `V := s₀.mem '' W` with `W = A ∪ (A+1) ∪ (A+2)`,
every write address lies in `T := {a + 3 + v | a ∈ A, v ∈ V}`, memory off `T` never changes, and
`{s | ∃ n, run n s₀ = (.running, s)}` is `Set.Finite`. Prove the invariant first (must); the
finiteness wrapper is should (Mathlib `Set.Finite.subset` over `A × (T → V ∪ s₀.mem '' T)`).

**Gate:** builds; axiom audit clean; C01 (and C04 if done) recorded in PAPER_MAP.

### R3 — Turing-completeness of the WE machine (must for TC-U; TC-B should) — two sessions

Use vendored `TM.Machine alphabet states` (`blank`, `start`, `transition : Fin states → Fin alphabet
→ Option (Fin alphabet × Bool × Fin states)`, `true` = move right). Write `A = alphabet`,
`Q = states` (both ≥ 1 because `blank`/`start` exist).

**Construction** (`Universal/Layout.lean`, definitions mirrored in `Spec/Universal.lean`):

* Handler size `K = 3Q + 2`; cell size `S = 2Q + Q·A·K`; cell `c ∈ ℤ` occupies `[c·S, c·S + S)`.
* Entry for state `q`: offset `e q = 2q`, a `JMP` whose displacement word (offset `2q+1`) encodes the
  cell's symbol: `disp q s = h q s − (e q + 2)`.
* Handler `(q,s)` at offset `h q s = 2Q + (q·A + s)·K`:
  * if `transition q s = some (s', right, q')`: for `i < Q`, a `MOV` at `h q s + 3i` with
    `rel = (e i + 1) − (h q s + 3i + 3)` and `val = disp i s'` (rewrites all `Q` entry displacements
    of *this* cell to symbol `s'`); then a `JMP` at `h q s + 3Q` with
    `rel = (±S + e q') − (h q s + 3Q + 2)` (`+` iff `right`);
  * if `none`: `HLT` at `h q s`, remaining handler words `0` (never fetched).
* `cellWord (s : Fin A) (j : Nat) : Int` = the template word at offset `j` for a cell holding `s`.
  Only the `Q` entry-displacement words depend on `s`; handlers are never written.
* `layout tape a := cellWord (tape (a / S)) (a % S)` (Int `ediv`/`emod`);
  `encode cfg := ⟨cfg.head·S + e cfg.state, layout cfg.tape⟩`;
  `initial M input := encode (TM.initialConfiguration M input)`.

**Proof plan.**
* `Universal/Cell.lean`: offset arithmetic (`(c*S + j) / S = c`, `% S = j` for `0 ≤ j < S`), decode
  lemmas: at `c·S + e q` the fetch is `jmp (disp q (tape c))`; inside handlers the fetch is the
  template `MOV`/`JMP`/`HLT`; entry-field offsets `2q+1 < 2Q ≤` every handler offset (writes never
  touch handler code).
* `Universal/Step.lean` — the local one-step lemma (the heart; state it once, use it for both
  theorems): if `mem` agrees with `cellWord (tape c)` on cell `c` and `pc = c·S + e q`, then
  * `transition q (tape c) = none` ⇒ `run 2` ends `halted` (JMP then HLT);
  * `= some (s', right, q')` ⇒ after exactly `Q + 2` steps, status running,
    `pc = (c ± 1)·S + e q'`, memory = `mem` with only cell `c`'s `Q` entry fields rewritten, and
    cell `c` now agrees with `cellWord s'`. Do the `Q` MOVs by induction on `i` with invariant
    "fields `< i` hold `disp _ s'`, all other words unchanged". Avoid unfolding `run` beyond
    `run_add` + single-step lemmas.
* `Universal/Unbounded.lean` (C02): with `layout` agreeing everywhere, `step` of the TM is simulated
  by `Q + 2` WE steps with `encode` as an exact equality (`funext` on memory); induction on TM steps
  gives `observe`: `TM.run M n cfg₀ = some cfg → ∃ k, run k (initial M input) = (.running, encode cfg)`.
  Derive `halts_iff : Halts (initial M input) ↔ TM.Halts M (TM.initialConfiguration M input)`,
  `diverges_iff`, `never_faults`, and `writes_target_jump_fields` (every executed `MOV` writes the
  displacement field of a `JMP` — i.e. it modifies code).
* `Universal/Bounded.lean` (C03, should): `imageN n background a` = `layout tape₀` on cells in
  `[−n, n]`, `0` on the guard cells `±(n+1)` (fetching `0` faults), `background a` elsewhere. Using
  the *local* lemma: while the head stays in `[−n, n]` the run matches the TM; leaving faults at the
  guard; outside words are never read or written. Theorems: for all `background`,
  `Halts (imageN …) ↔` TM halts with every visited head in `[−n, n]`; `Faults (imageN …) ↔` the head
  reaches `±(n+1)` before halting; corollary `TM.Halts ↔ ∃ n, ∀ bg, Halts (imageN n bg)`.
* `Universal/Mathlib.lean` (should): compose the vendored `MathlibTM0` compiler: for every Mathlib
  `Turing.TM0.Machine (Fin A) (Fin Q)` and input, WE halts iff `(Turing.TM0.eval …).Dom`.

R3a = Layout + Cell + Step (gate: step lemma proved). R3b = Unbounded + Bounded + Mathlib.
**Gate:** C02 proved with no hypotheses beyond the construction; C03/Mathlib or open obligations recorded.

### R4 — Arithmetic, division facts, modular exponentiation, Spectre arithmetic (must)

Work over `BitVec`/`Nat`. Define in `Spec/Arith.lean` compact algorithm functions that **transcribe
the asm structure** (cite asm line ranges in docstrings); prove them equal to the specs. Keep each
algorithm's definition short — it is copied into Challenge.

* `Arith/Tables.lean` (C06): each 8-bit table as the *literal MASM macro expression* (e.g.
  `DEFINESHLGEN`: low = `(Index shl Orig) and 0ffh`, high = `Index shr (8−Orig)`; `DEFINENZ`:
  `(Index NE 0) and 1`; SUB's 9-bit borrow form; SHR = `a << (8−c)` as the harness expects) and the
  theorem table = spec for all inputs (`decide` for unary/`Fin 8` shift amounts; binary ops are the
  spec by definition or by `BitVec` lemmas).
* C05 generic lookup (word model): a computed `JMP` whose displacement is `base + stride·k` lands on
  entry `k`; with table entries `[MOV result-field f(k); JMP back]` the lookup writes `f k`. State it
  for the WE word machine of R2 (a reusable lemma also used by R6's byte version as the template).
* `Arith/Add.lean`, `Sub.lean` (C07): byte-wise ADD with the `ADDBYTE` carry scheme (carry into the
  next byte is applied by `INC` on its first operand, with the second-level carry `carry&Idx&_2`
  when that `INC` overflows) = `(a + b) mod 2^32` and `2^64`; SUB analogously.
* `Arith/Shift.lean`, `Xor.lean` (C08): byte-move rotation plus bit shift with carry XOR as in
  `WriteExecSHL32/64`, `SHR32/64`; `XOR32` bytewise.
* `Arith/Mul.lean` (C09): shift-and-add as in `WriteExecMUL32` (checks bytes of `y` with `NZ`, low bit
  via `SHL1`) = `x·y` as 64-bit.
* `Arith/Div.lean` (C10): 64-iteration restoring division with the remainder-overflow bit (as
  `doDivision` in `writeexec.c`; transcribe what `WriteExecDIV32` actually does) gives
  `q = (n / d) mod 2^32` and `r = n % d` for `d ≠ 0`.
* `Arith/Reduce.lean` (C11): `n % d < 2^32` always; `n / d < 2^32 ↔ n / 2^32 < d`; for
  `a, b < d`, `a·b / d < 2^32`; two-step reduction
  `((hi % m)·2^32 + lo) % m = (hi·2^32 + lo) % m` with `(hi % m)·2^32 + lo < m·2^32` (the second
  division never overflows) — this backs W03/W04 and L03.
* `Arith/ModExp.lean`, `Count.lean` (C12): right-to-left square-and-multiply as in
  `WriteExecMODEXP32` (result initialised to 1, unreduced base) = `b^e % m` for `m ≥ 2`; the
  `m = 1, e = 0` value is `1` (documents L02/L05); instrumented count = `Nat.log2 e + 1 + popcount e`
  for `e ≥ 1` (confirm against the asm loop), naive loop count = `e`. could: left-to-right variant
  with `⌊log₂e⌋ + popcount e − 1`.
* `Spectre/Mix.lean` (C20): `fun i : Fin 256 => (i·167 + 13) % 256` bijective (`decide`).
* `Spectre/Select.lean` (C19): Fig. 1 for `BitVec 32` and `BitVec 64` `size_t`:
  `x := ((j % 6) − 1) &&& ~~~0xFFFF; x := x ||| (x >>> 16); x := t ^^^ (x &&& (m ^^^ t))` yields `m`
  if `j % 6 = 0` and `t` otherwise (case split on the six residues; no `bv_decide`).
* `validation/Vectors.lean` (`lake env lean --run`): writes JSON test vectors from the *specs*:
  exhaustive 8-bit unary/binary, 10,000 seeded random + edge cases per wide op (0, 1, 2^31−1, 2^31,
  2^32−1, divisor with top bit set, quotient-overflow cases, `mod = 1` cases), FIPS-197 vectors.

**Gate:** C05–C12, C19, C20 proved; vectors generated; PAPER_MAP updated.

### R5 — AES (should; C13–C15, C22; C21 could)

* `AES/GF.lean`: `xtime`, `gmul` on `BitVec 8` (or `Fin 256` via `Nat` ops); `xtime_xor` linearity
  (structural proof preferred; fallback: 256 lemmas × 256-case `decide`).
* `AES/SBox.lean`: S-box = affine ∘ inverse (inverse as `x^254`); `sbox` equals the literal FIPS table
  (`decide`, 256 cases); use the literal table for evaluation.
* `AES/Cipher.lean` (`Spec/AES.lean`): FIPS-197 state (16 bytes, column-major), `AddRoundKey`,
  `SubBytes`, `ShiftRows`, `MixColumns`, `cipher (rk : Fin 11 → 16 bytes)`; `KeyExpansion` for the
  test vector.
* `AES/TTable.lean` (C13–C14): `Te0..Te3` defined from `sbox`/`gmul`, `Te4 x = replicate (sbox x)`;
  each equals the literal asm/`writeexec.c` tables (extract with a script into
  `AES/TableData.lean`, record the source SHA-256 in a comment; `decide`); round identity: per column,
  `MixColumns ∘ ShiftRows ∘ SubBytes` then key = `Te0 ⊕ Te1 ⊕ Te2 ⊕ Te3 ⊕ rk` (linearity of
  MixColumns); final round = Te4 bytes ⊕ rk.
* `AES/Lookup.lean` (C15, C22): the WE AES procedure as transcribed from `AESINIT/AESXORMIX/
  AESTABLE/AESFIN` (byte order of `rd_key` as stored by `AES_set_encrypt_key` on little-endian x86)
  = `cipher`; the asm ShiftRows index formulas in comments equal FIPS ShiftRows (`decide`).
* `AES/Vectors.lean`: FIPS-197 Appendix C.1 known-answer by kernel evaluation.
* `AES/AesNi.lean` (C21, could): AESENC/AESENCLAST per the Intel SDM pseudocode; Fig. 3 sequence =
  `cipher` given the intrinsic key layout. Disclose the SDM-based semantics.

**Gate:** C13–C15 proved (or open obligations recorded with a narrowed statement).

### R6 — Byte-level x86/x64 model and Figs. 5–7 (should; Fig. 6 could) — up to two sessions

* `X86/ISA.lean`: forms `movB/movW/movD (disp32) (imm)` = `C6 05 d32 i8` (7 B), `66 C7 05 d32 i16`
  (9 B), `C7 05 d32 i32` (10 B); `jmpS rel8` = `EB` (2 B); `jmpN rel32` = `E9` (5 B); `nop` = `90`.
  Two modes: x86 effective address = `disp32` (mod 2^32); x64 = next pc + sext(disp32) (mod 2^64).
  encode/decode round trip, length from the first ≤ 3 bytes, fetch from *current* bytes (use vendored
  `ByteMemory`/`ByteLemmas`). `X86/ReadFree.lean`: the step depends only on ≤ 10 fetched bytes.
* `X86/Jump.lean`: patched-displacement lemmas (byte `k` at `+2` ⇒ `rel32 = 256k` when the other
  bytes are `00 ?? 00 00`; word `w` at `+1` ⇒ `rel32 = w`; word at `+2` ⇒ `256w`), NOP-slide lemma
  (landing inside a `90` run reaches the next instruction), generic table-entry lemma.
* `X86/LayoutData.lean`: generated from `validation/layout/*.json` (script, deterministic); layout
  side conditions (strides, jump forms, short-jump reach, NOP padding) proved by `decide` on these
  small lists.
* `X86/Fig5.lean` (C16): for every `k : BitVec 8`, both modes: from `notarg` with the wrapper-patched
  state, execution goes through SHL4 and the NOT table and reaches the patched `notret` target with
  `~~~k` written to the destination field; all writes are to instruction fields; if W10 holds, also
  prove the original `0f6h` layout correct via NOP slide and the corrected layout with exact stride.
* `X86/Fig7.lean` (C17): carry `c ∈ {0,1}`: `SHL1` writes `2c` into `carryNretval`'s rel32, landing on
  `nocryN` (`EB`, 2 B) or `hascarryN`.
* `X86/Fig6.lean` (C18, could): XOR double lookup; the copy loop executes `xorargshl1` exactly twice
  with retargeted address and exits with `xorloop+1 = 0` ("safely re-executable": the post-state
  satisfies the pre-condition of another invocation).
* `X86/Export.lean` + `validation/compare_listings.py`: Lean-emitted bytes for the Fig. 5/7 regions
  and table entries vs COFF bytes (relocated fields compared as symbol+addend). Evidence.
* could: x64 byte realisation of the R3 cell template when `S` fits rel32.

**Gate:** C16, C17 proved for both modes on the actual layout data; comparison passes.

### R7 — Legacy corrections, native acceptance, errata TeX (must)

1. Apply L01–L05 (as decided in R1/R0) as minimal diffs; update asm/C comments; no refactors.
2. `validation/native/we_vectors.c`: links the assembled `writeexc.asm` (both archs) and checks every
   `*_C` entry point against the R4/R5 vectors (respecting the `mod ≥ 2` precondition if chosen).
   Extend `native.py`: build 4 configs, run legacy `writeexec.exe` (must print no mismatch), run
   vectors, purity scan, `compare_listings.py`. Record `validation/rounds/R7.json`.
3. Errata TeX: `lean/errata/selfspectre-2019-errata.tex` from the smcTuring two-column template;
   title "Errata and model clarifications — Self-Spectre, Write-Execute and the Hidden State",
   citation, then W items (exact before/after, one-line Lean reference or source), then a short
   "Code supplement" paragraph listing L items with commit hashes. `minimal.diff` generated from
   `edits.json`. Build with `pdflatex` (MiKTeX installed) → `output/pdf/selfspectre-2019-errata.pdf`.
4. `audit_errata.py` (full): inventory checks + every `lean_refs` name exists (via a generated
   `#check` file) + PDF builds, ≤ 3 pages (target 2).
5. Ask the user to review the errata PDF (they are the author) — the only question this round.

**Gate:** native acceptance passes in all 4 configs; errata audit passes; author review requested.

### R8 — Palomar package, CI, preflight, handoff (must)

1. `WriteExecute/Spec/Paper.lean`: the selected result `Prop`s — `ReadFree`, `TuringComplete`
   (TC-U incl. observation), `FiniteRealization` (TC-B, if proved), `Confinement` (if proved),
   `Primitives` (C05–C06), `Arithmetic` (C07–C12), `AES` (C13–C15, if proved), `SpectreArithmetic`
   (C19–C20). `WriteExecute/Paper.lean` proves each from existing theorems.
2. `validation/make_challenge.py` → `lean/Challenge.lean` (Spec modules verbatim + module doc +
   theorem `PalomarWE.mathematical_result : ReadFree ∧ TuringComplete ∧ …` with `sorry`);
   `Solution.lean` proves it from the development; `comparator.json` lists the theorem(s) and the
   definitions, permitted axioms the standard three, `enable_nanoda: true`. Size: hard limit
   1,000 lines/100 KiB; preferred 300 lines/32 KiB — if over, disclose the warning (smcTuring passed
   with it) or drop optional Props after asking the user.
3. `formalization.yaml` (schema v0.4, copy smcTuring's structure): license `MIT` (root `LICENSE`);
   sources: the TMMP paper (`adapts`, author participated), FIPS-197 and Kocher et al. (background),
   Intel SDM if C21 done; `related_formalizations`: smcTuring at commit `1ab379c…` (`builds-on`,
   vendored base) and the pinned Mathlib computability tree; classification from the policy taxonomy
   files (suggest `cs.CR`, `cs.LO`; MSC `68M25`, `03D10`, `94A60` — confirm the user's W07 choice);
   honest `status.scope` (ideal model per D2, supporting byte/native material not selected);
   `automation`: agent, models Claude Opus 5.5 (planning) and Claude Sonnet 5.5 (execution),
   framework Claude Code; fidelity divergences = W items; review status agent-reviewed.
   Validate with the adapted `validate_metadata.py` against the fetched policy assets.
4. Docs: `PALOMAR_SEMANTICS.md` (each selected name, meaning, model boundaries), `PAPER_MAP.md`
   final, `LICENSE_AUDIT.md` (MIT detected by GitHub; vendored CC0; publisher PDF license as stated
   in the PDF), README "Lean formalization" section.
5. CI `.github/workflows/proof.yml`: Linux job (pinned action SHAs from smcTuring's workflow, cgroup
   `MemoryMax=7500000000` via `systemd-run`, elan with the pinned toolchain, Mathlib cache, cold
   `lake build` of `WriteExecute`, `Challenge`, `Solution`, axiom audit, `make_challenge.py --check`,
   `audit_errata.py`); Windows job (`windows-2022`, `--toolset v143`, `native.py --all`).
   `palomar-full.yml` with `request_id: selfspectre001`, `project_path: lean`.
6. With push authorisation: push, run `proof.yml`, then dispatch `palomar-full.yml` on the exact
   commit. Fix and repeat until both pass. Record run URLs and report hashes in
   `lean/FINAL_ACCEPTANCE.json` (compact) and form values in `lean/PALOMAR_SUBMISSION.md`
   (repository, commit, project dir `lean`, comparator/metadata paths, first submission, notes
   disclosing AI assistance and the ideal-model scope). Mark all rounds accepted in `ROUNDS.md`.

**Gate (= definition of done, §0):** cold CI green, Palomar full preflight pass on the recorded
commit, errata PDF reviewed, native acceptance green.

---

## MVP path (if budget is tight)

R0 → R1 → R2 (no CONF wrapper) → R3a/R3b (TC-U only) → R4 → R7 → R8 with selected Props
`ReadFree ∧ TuringComplete ∧ Primitives ∧ Arithmetic ∧ SpectreArithmetic`. Then R5, R6 and the
should-items as follow-up rounds; each later addition is a new Palomar *update*, not a blocker.

## Risks and fallbacks

| Risk | Fallback |
|---|---|
| Int `ediv/emod` offset arithmetic bogs down R3 | Work with `Nat` cell offsets and a separate `Int` cell index; prove the two decode lemmas once and never unfold `layout` again |
| `Q` MOV induction in R3 is slow to elaborate | Generalise over an arbitrary list of distinct field offsets; prove the fold lemma for lists, instantiate once |
| 65,536-case facts too heavy for `decide` | 256 lemmas × 256 cases generated by a tiny script, or structural `BitVec` proof |
| Transcribed asm algorithm subtly differs from the asm | R7 vectors catch input/output mismatches; fix the transcription, not the spec |
| Mathlib-importing modules exceed the 1.5 GB guard locally | Build those only in CI; keep them few (D8) |
| MASM listing parse fragile or huge (the `/Sa` expansion of the 2 MB lookup tables can exceed 100 MB) | Stream-parse, never commit the listing; listing for label offsets, COFF for bytes; cross-check 3 labels by hand |
| Palomar pins moved since smcTuring | `refresh_policy.py`; update only the workflow pin and schema rev, never the Lean/Mathlib pins without asking |
| Challenge > 1,000 lines | Move auxiliary definitions out of selected statements; select fewer Props (ask user) |

## Round-close checklist (copy into each `ROUNDS.md` entry)

- [ ] full `lean_build.py WriteExecute` green under the guard
- [ ] `axiom_audit.py` clean
- [ ] round gate commands green; `validation/rounds/Rk.json` written
- [ ] `PAPER_MAP.md`, `edits.json` (`lean_refs`), `ROUNDS.md` handoff updated
- [ ] committed (and pushed if authorised)
