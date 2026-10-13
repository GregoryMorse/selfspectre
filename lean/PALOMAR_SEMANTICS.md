# Selected Palomar statement

`PalomarWE.mathematical_result` (Challenge: one deliberate `sorry`; Solution: no holes) is the
conjunction of twelve result definitions (the Write-Execute half and the Self-Spectre half under an abstract speculation contract) in `WriteExecute/Spec/Paper.lean`. They formalize the
**Write-Execute** half and, under an explicit leakage contract, the **Self-Spectre** half of Gregory Morse, *Self-Spectre, Write-Execute and the Hidden State*,
Tatra Mt. Math. Publ. 73 (2019) 131-144, as corrected by the errata in `errata/` (W01-W10 text, L01-L05 code).

`Challenge.lean` is generated mechanically by `validation/make_challenge.py` from the Spec modules
(`WriteExecute/Spec/*.lean`) and the two vendored definition modules (`Base/Memory`, `Base/Turing`),
with proofs and `theorem` blocks removed. It imports nothing (Lean core only), so Challenge and development
cannot drift; CI runs `make_challenge.py --check`. `Solution.lean` imports `WriteExecute.Paper`, which proves
each result definition from the development's individual theorems. All proofs use only `propext`,
`Quot.sound`, `Classical.choice` (`validation/ci/axioms.py` audits every `WriteExecute.*` declaration).

| Selected declaration | Meaning and scope | Paper / ledger |
| --- | --- | --- |
| `PalomarWE.mathematical_result` | Conjunction of the definitions below. | all |
| `WriteExecute.Paper.ReadFree` | One step of the ideal machine equals the effect determined by the three words at the program counter: status, next program counter and at most one store. No data read, register or stack. | §4 p.139, C01 (W02) |
| `WriteExecute.Paper.TuringComplete` | For every finite-alphabet two-sided Turing machine and configuration, the unbounded blank-cell image encodes it; `n` source steps are `n (Q+2)` machine steps; halting, divergence and the tape are preserved; the image never reaches an undecodable opcode; the same for the initial image of a finite input. | §4 p.141, C02 (W01) |
| `WriteExecute.Paper.FiniteRealization` | The finite image of `N` cells is exact while the head stays inside it, halting inside is faithful, and the first step leaving the image faults at the guard. | §4 p.141, C03 (W01) |
| `WriteExecute.Paper.Confinement` | A run whose program counters stay in a finite list `A` changes no memory outside the finite target list and keeps all fetched and stored values in finite lists. | §4, C04 |
| `WriteExecute.Paper.Primitives` | The jump-table lookup `[JMP e] ... [e: MOV res f; JMP ret]` computes the table function in three steps; the 8-bit tables NOT, NZ, SHL (SHLGEN), SHR (SHRGEN), INC, DEC, SUB and ADD (with the carry expression) are what their names say. | §4 p.139-140, C05-C06 |
| `WriteExecute.Paper.Arithmetic` | Any-width ADD, SUB, SHL, SHR, XOR; 32x32 to 64-bit multiplication; 64/32 division and modulo including the remainder-overflow bit; the two-step modular reduction and the failure of the published `mulmod`; modular exponentiation (`m >= 2` for the assembler, `m >= 1` for the corrected C) and the multiplication count. | §3-4 p.136, 139, C07-C12 (W03-W05, L02, L03, L05) |
| `WriteExecute.Paper.AESResult` | The S-box is the GF(2^8) inverse plus affine map; `Te4` repeats it in every byte; the Write-Execute AES lookup procedure computes the FIPS-197 cipher for every expanded key and plaintext; the FIPS-197 Appendix C.1 known answer holds for the specification. | §3-4, C13-C15, C22 |
| `WriteExecute.Paper.Mistraining` | For any branch predictor (an abstract parameter) that guesses "taken" after `k <= 5` consecutive "taken" outcomes, the schedule of Fig. 1 (five in-bounds calls, then the malicious call when `j mod 6 = 0`) makes the predictor guess "taken" for a false guard; Fig. 1's branch-free select makes the guard true exactly off that schedule for 32- and 64-bit `size_t`; the textbook 2-bit counter satisfies the assumption. | §2 Fig. 1, C19, C23 |
| `WriteExecute.Paper.VictimLeak` | A mispredicted victim whose body is the probe `temp &= array2[array1[x]*512]` leaves the architectural state unchanged and adds the page of the secret byte to the cache. **From a cleared probe array** (the paper flushes all 256 pages first) the reload phase (pages timed in the order `mix_i`) finds exactly that one page, so two runs have the same reload hits exactly when the secret bytes agree mod 256. From an initially populated cache only the first part (state unchanged, page added) is claimed. | §3 Fig. 2, C20, C24 |
| `WriteExecute.Paper.WindowDepth` | A hidden computation of `k` steps followed by one probe leaks exactly when the speculation window covers all `k+1` steps (else the cache is untouched); a larger window only adds pages, so a short window leaves a prefix of the results. | §3 Tables 1-2, Fig. 4, C25 |
| `WriteExecute.Paper.HiddenComputation` | A mispredicted body running `n` Write-Execute steps without a probe computes exactly the ideal Write-Execute run, touches no cache page and is squashed without trace; every Turing computation is carried out step for step inside the window. | §3-§4, C26 |
| `WriteExecute.Paper.SelfSpectre` | The conjunction of the four Self-Spectre results above. | §3 |

## Model boundaries (read before relying on the statement)

* The **machine is ideal**: unbounded integer addresses and values, instruction words `[1, rel, val]`
  (store at `pc + 3 + rel`), `[2, rel]` (jump to `pc + 2 + rel`), `[3]` (halt), any other opcode faults.
  Finite hardware is not claimed to have unbounded memory; `FiniteRealization` is the finite-image statement.
  This is the correction W01 to the published universality claim.
* `TuringComplete` is **TC-U**: the encoding is the construction of `Spec/Universal.lean`; the statement is
  about every machine in `TM.Machine A Q` (a blank symbol and a start state, so `A, Q >= 1`).
  Halting is a reached missing transition; divergence is "every finite prefix exists".
* `Primitives`/`Arithmetic` are **algorithm-level** specifications transcribing the MASM macro
  expressions; they are proved, not tested. The assembled `writeexc.asm` is tied to them by native test
  vectors and by the byte-level model (below), which are **evidence, not part of the selected statement**.
* `AESResult` takes the expanded key `w` as given (the key schedule `keyWords` is specified and checked
  against FIPS-197 C.1 but the WE procedure does not expand keys).
* **Not selected** (proved or checked in the development, listed in `PAPER_MAP.md`): the byte-level x86/x64
  model of Figs. 5, 6 and 7 (`X86/`), the layout geometry of the assembled objects, the AES-NI sequence (C21),
  the native harnesses (including the edge vectors against the assembled entry points).
* **The Self-Spectre results are conditional on an abstract leakage contract** (`Spec/Speculation.lean`), in the
  style of hardware-software contracts: a branch predictor (a parameter), a speculation window `W` (a
  parameter), rollback of the architectural state on a misprediction, and persistence of the cache pages
  touched on the wrong path. The contract machine extends the ideal Write-Execute machine by one probe opcode
  `[4, rel]` that brings page `mem[..] mod 256` of the probe array into the cache. **No processor is modeled**:
  the pipeline, real predictors, cache geometry, timing, store-to-fetch behavior of self-modifying code, the
  size of `W` on any CPU and the measured tables are not formalized and no theorem says that a given CPU
  satisfies the contract. The measured results (Tables 1-2, Fig. 4) and the compiled instruction counts are
  native evidence only.
