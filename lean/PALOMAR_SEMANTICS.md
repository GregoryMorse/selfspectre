# Selected Palomar statement

`PalomarWE.mathematical_result` (Challenge: one deliberate `sorry`; Solution: no holes) is the
conjunction of eight result definitions in `WriteExecute/Spec/Paper.lean`. They formalize the
**Write-Execute** half of Gregory Morse, *Self-Spectre, Write-Execute and the Hidden State*,
Tatra Mt. Math. Publ. 73 (2019) 131-144, as corrected by the errata in `errata/` (W01-W10 text, L01-L05 code).

`Challenge.lean` is generated mechanically by `validation/make_challenge.py` from the Spec modules
(`WriteExecute/Spec/*.lean`) and the two vendored definition modules (`Base/Memory`, `Base/Turing`),
with proofs and `theorem` blocks removed. It imports nothing (Lean core only), so Challenge and development
cannot drift; CI runs `make_challenge.py --check`. `Solution.lean` imports `WriteExecute.Paper`, which proves
each result definition from the development's individual theorems. All proofs use only `propext`,
`Quot.sound`, `Classical.choice` (`validation/ci/axioms.py` audits every `WriteExecute.*` declaration).

| Selected declaration | Meaning and scope | Paper / ledger |
| --- | --- | --- |
| `PalomarWE.mathematical_result` | Conjunction of the eight definitions below. | all |
| `WriteExecute.Paper.ReadFree` | One step of the ideal machine equals the effect determined by the three words at the program counter: status, next program counter and at most one store. No data read, register or stack. | §4 p.139, C01 (W02) |
| `WriteExecute.Paper.TuringComplete` | For every finite-alphabet two-sided Turing machine and configuration, the unbounded blank-cell image encodes it; `n` source steps are `n (Q+2)` machine steps; halting, divergence and the tape are preserved; the image never reaches an undecodable opcode; the same for the initial image of a finite input. | §4 p.141, C02 (W01) |
| `WriteExecute.Paper.FiniteRealization` | The finite image of `N` cells is exact while the head stays inside it, halting inside is faithful, and the first step leaving the image faults at the guard. | §4 p.141, C03 (W01) |
| `WriteExecute.Paper.Confinement` | A run whose program counters stay in a finite list `A` changes no memory outside the finite target list and keeps all fetched and stored values in finite lists. | §4, C04 |
| `WriteExecute.Paper.Primitives` | The jump-table lookup `[JMP e] ... [e: MOV res f; JMP ret]` computes the table function in three steps; the 8-bit tables NOT, NZ, SHL (SHLGEN), SHR (SHRGEN), INC, DEC, SUB and ADD (with the carry expression) are what their names say. | §4 p.139-140, C05-C06 |
| `WriteExecute.Paper.Arithmetic` | Any-width ADD, SUB, SHL, SHR, XOR; 32x32 to 64-bit multiplication; 64/32 division and modulo including the remainder-overflow bit; the two-step modular reduction and the failure of the published `mulmod`; modular exponentiation (`m >= 2` for the assembler, `m >= 1` for the corrected C) and the multiplication count. | §3-4 p.136, 139, C07-C12 (W03-W05, L02, L03, L05) |
| `WriteExecute.Paper.AESResult` | The S-box is the GF(2^8) inverse plus affine map; `Te4` repeats it in every byte; the Write-Execute AES lookup procedure computes the FIPS-197 cipher for every expanded key and plaintext; the FIPS-197 Appendix C.1 known answer holds for the specification. | §3-4, C13-C15, C22 |
| `WriteExecute.Paper.SpectreArithmetic` | Fig. 1's branch-free select yields the malicious index exactly when `j mod 6 = 0` (32- and 64-bit `size_t`); `mix_i = (i*167+13) & 255` permutes `0 .. 255`. | §2, C19-C20 |

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
  model of Figs. 5 and 7 (`X86/`), the layout geometry of the assembled objects, the AES-NI sequence (C21),
  the native harnesses. **Open**: the XOR copy loop of Fig. 6 (C18).
* No claim about caches, speculation, a real CPU or operating system is made. The Spectre half of the paper
  is not formalized except the index arithmetic of its figures.
