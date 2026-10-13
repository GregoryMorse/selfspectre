# Paper map and proof ledger

Class: **F** = Lean-formal, **M** = mechanical evidence (listing/native), **E** = editorial erratum.
Status: todo / proved / open (with note). Paper locations are the published TMMP numbering.

| ID | Paper location | Claim | Class | Round | Status | Declaration / evidence |
|---|---|---|---|---|---|---|
| C01 | §4 p.139 | Write-Execute reads nothing but its fetch window; every instruction is a store or a transfer (W02) | F+M | R2 | proved | `WE.step_eq_effect`, `WE.effect_congr`, `WE.store_from_window`; purity scan |
| C02 | §4 p.141 | Turing-completeness, unbounded blank-cell template (W01) | F | R3 | proved | `Universal.halts_iff`, `diverges_iff`, `never_faults`, `simulate` (Q+2 WE steps per TM step); construction in `Spec/Universal.lean` |
| C03 | §4 p.141 | Finite image: exact while in range, faults at the guard (W01) | F | R3 | proved | `Universal.bounded_simulate`, `bounded_halts`, `bounded_faults` |
| C04 | §4 | A run confined to finitely many fetch addresses has finitely many reachable states | F | R2 | proved (invariant form) | `WE.confinement`: pc in A, memory off the target list unchanged, all values in finite lists. A `Set.Finite` wrapper (Mathlib) is optional and not done |
| C05 | §4 p.139-140 | Generic jump-table lookup computes the table function | F | R4 | proved | `WE.lookup_correct`, `WE.lookup_table` (word model; byte version in R6) |
| C06 | §4 | 8-bit tables NOT, NZ, SHL1/4/5/6/7, INC, DEC, AND, OR, XOR, ADD, SUB, SHL, SHR | F | R4 | proved | `Arith.Tables`: `shl_split`, `shl_xor`, `shr_split`, `shr_xor`, `inc_spec`, `dec_spec`, `sub_spec`, `addLo_spec`, `addCry_spec`, `tNot_spec` (kernel evaluation, `decide +kernel`) |
| C07 | §4 | 32/64-bit ADD, SUB with carry chain | F | R4 | proved | `Arith.addDigits_spec`, `addN_spec`, `subDigits_spec`, `subN_spec` (INC/DEC carry scheme, any width) |
| C08 | §4 | 32/64-bit SHL, SHR, XOR32 | F | R4 | proved | `Arith.shlN_spec`, `shrN_spec`, `xorN_spec` (any width and count) |
| C09 | §4 | 32x32 -> 64 multiplication | F | R4 | proved | `Arith.mulLoop_spec`, `mul32_exact` |
| C10 | §4 p.139 | 64/32 division and modulo (W03) | F | R4 | proved | `Arith.doDivision_spec` (invariant `DivInv` over the 64 iterations, remainder-overflow bit included) |
| C11 | §3 p.136 | Division overflow facts and two-step reduction (W04) | F | R4 | proved | `Arith.div_lt_word_iff`, `mulmod_div_lt`, `two_step`, `mulmodFixed_spec`, `mulmodLegacy_wrong` (L03) |
| C12 | §3 p.136 | Modular exponentiation (mod >= 2) and multiplication count (W05) | F | R4 | proved | `Arith.modexpAsm_spec` (m >= 2), `modexpRef_spec` (m >= 1), `modexp_m1_e0`, `mulCount_log2`, `modexpNaive_spec` |
| C13 | §3 | AES T-tables equal the algebraic definition and the literal tables | F | R5 | proved | `AES.sbox_alg` (S-box = GF inverse + affine, all 256), `te4_lit`, `te0_bytes`..`te3_bytes` (generated exhaustive checks, `AES/Checks.lean`) |
| C14 | §3 | T-table round = FIPS-197 round; final round uses Te4 | F | R5 | proved | `AES.round_step`, `te_byte`, `sbox_and255` |
| C15 | §4 | WE AES lookup procedure = AES-128 encryption (FIPS-197 C.1) | F | R5 | proved (algorithm level) | `AES.weCipher_eq` against the FIPS spec; `fips197_c1`, `fips197_b` check the spec itself. Asm bytes: R6/R7 vectors |
| C16 | Fig. 5 p.140 | `not` and `nz` through SHL4 and the 256-entry table, byte level (W10, L04) | F+M | R6/R8 | proved (model); bytes checked against COFF | `X86.fig5_x86`, `fig5_x64`, `fig5_nz_x86`, `fig5_nz_x64` (published layout incl. NOP slide for k >= 248), `fig5c_*` (corrected layout, uniform 16-byte entries, exactly 14 steps), `fig5_original`/`fig5_corrected` (generic in the table function), `w10_original_sizes` (entry 247 = 19 B), `w10_corrected_sizes`, `*_notres_offsets`/`*_nzres_offsets` (layout data); `validation/compare_listings.py`: 3092 Lean-encoded byte strings (NOT/NZ/SHL4 entries, `iX`, `i3`, `iN`) equal the COFF `.text` of the published (x86, x64) and corrected (x86c, x64c) objects, relocations applied (evidence) |
| C17 | Fig. 7 p.142 | Carry conditional jump, byte level | F+M | R6 | proved (model) | `X86.carry_branch` (lands on nocry + 2c), `x86_carry_geometry`, `x64_carry_geometry`; SHL1 word store = `shl_lookup` with c = 1 |
| C18 | Fig. 6 p.141 | XOR double lookup and re-executable copy loop | F+M | R6/R8 | proved (supporting) | `X86.xor_exec_x64` (35 steps) and `xor_exec_x86` (38 steps) in `X86/Fig6.lean`: from `xorarg1`, the two argument stages, the three patches, the `xorloop` copy loop executed twice (through `xorhead`), the patched `xorj` jump through the 8192-byte group stride, the group jump and the 16-byte entry reach `Dd - 1` with `k1 xor k2` at `Dd`; every write is to an instruction field (`XorW64`/`XorW86`), and every stale field value is allowed, so the procedure is re-executable. Concrete section offsets of all four assembled layouts: `Fig6Final.fig6_{x86,x64,x86c,x64c}` (geometry in `LayoutData`). Evidence: `compare_listings.py` equates the Lean-encoded image (7,778 byte strings incl. all 65,536 entries) with the COFF `.text`. The arithmetic content is C08 (`Arith.xorN_spec`) |
| C19 | Fig. 1 p.134 | Branchless select yields the malicious index iff j mod 6 = 0 | F | R4 | proved | `Spectre.select_32`, `select_64` |
| C20 | §2 p.134 | `mix_i = (i*167+13) & 255` permutes 0..255 | F | R4 | proved | `Spectre.mix_perm`, `mix_injective`, `mix_surjective` |
| C21 | Fig. 3 | AES-NI sequence = AES-128 | F | R5/R8 | proved (given the round keys) | `AES.aesNi_eq` (pxor + 9 aesenc + aesenclast with the SDM operation order equals `cipher`), `subBytes_shiftRows`; `aeskeygenassist` key expansion not modeled |
| C23 | Fig. 1 / §2 | Mistraining: the predictor guesses taken at the malicious call after the five training calls (abstract predictor, 2-bit counter instance) | F (contract) | R9 | proved | `Speculation.mistrain`, `counter2_trains`, `select_guard_32/64` |
| C24 | Fig. 2 | Victim leak: the wrong path touches exactly the secret byte's page; the architectural state is restored; reload in `mix_i` order recovers the page | F (contract) | R9 | proved | `Speculation.branch_one`, `probe_hits` |
| C25 | §3, Tables 1-2, Fig. 4 | Speculation depth: leak iff the window covers the hidden steps; a larger window only adds pages | F (contract) | R9 | proved | `Speculation.leak_after`, `branch_mono` |
| C26 | §3-§4 | Hidden computation: the wrong path runs the ideal Write-Execute run (and every Turing computation) with no cache trace and no architectural effect | F (contract) | R9 | proved | `Speculation.trun_run`, `hidden` |
| C22 | asm comments | ShiftRows index formulas = FIPS-197 ShiftRows | F | R5 | proved | `AES.nvalInv_nval`, `nval_nvalInv`, `pos_src`, `src_pos` |

## Errata (see `errata/edits.json`)

| ID | Page | Class | Status | Evidence |
|---|---|---|---|---|
| W01 | 141 | F | confirmed; proved (R3) | C02, C03 |
| W02 | 139 | M | confirmed | `validation/layout/purity.json` (28 core procs, 0 violations) |
| W03 | 139 | F | confirmed; proved (R4) | C10 |
| W04 | 136 | F | confirmed; proved (R4) | C11 |
| W05 | 136 | F | confirmed against C and asm; proved (R4) | C12 |
| W06 | 137 | E | confirmed (Table 2 pattern) | |
| W07 | 131 | E | confirmed | |
| W08 | 134 | E | confirmed | Intel SDM |
| W09 | 133 | E | confirmed | Lipp et al. |
| W10 | 140 | M | confirmed; proof R6 | `validation/layout/{x86,x64}.json` |

Dropped as unneeded or uncertain: `ONLY64` notation (presentation only), "RSRE" (abbreviation varies by vendor).

Code fixes L01-L05: applied in R7. L04 is additionally confirmed by assembling the corrected source: the NOT and NZ
tables have uniform 16-byte entries and `notres = notarg + 37 + 4096` (x86 and x64, `validation/layout/{x86,x64}c.json`,
theorems `x86c_geometry`, `x64c_geometry`, `*c_notres_offsets`).

## Selected statement (R8)

`WriteExecute/Spec/Paper.lean` defines twelve results (R9: the Self-Spectre contract results were added); `WriteExecute/Paper.lean` proves them; `Challenge.lean` is generated from the Spec.

| Result definition | Claims | Proof |
|---|---|---|
| `ReadFree` | C01 | `Paper.readFree` |
| `TuringComplete` | C02 | `Paper.turingComplete` |
| `FiniteRealization` | C03 | `Paper.finiteRealization` |
| `Confinement` | C04 | `Paper.confinement` |
| `Primitives` | C05, C06 | `Paper.primitives` |
| `Arithmetic` | C07-C12 | `Paper.arithmetic` |
| `AESResult` | C13-C15 (C22 inside the proof) | `Paper.aesResult` |
| `Mistraining` | C19, C23 | `Paper.mistraining` |
| `VictimLeak` | C20, C24 | `Paper.victimLeak` |
| `WindowDepth` | C25 | `Paper.windowDepth` |
| `HiddenComputation` | C26 | `Paper.hiddenComputation` |
| `SelfSpectre` | C19, C20, C23-C26 | `Paper.selfSpectre` |

Not selected (supporting): C16, C17, C18 (byte-level model and COFF evidence), C21. Open: none; the `aeskeygenassist` key expansion is not modeled (C21 is given the round keys).

## Whole-paper coverage (R9)

| Paper part | Disposition |
|---|---|
| Sec. 1 Introduction, conclusion | prose; not formalizable |
| Sec. 2 Background (Meltdown/Spectre taxonomy, CLFLUSH/RDTSC, Fig. 1) | Fig. 1 and `mix_i`: C19, C20, C23 (proved); taxonomy and instruction facts: editorial (W07-W09) |
| Sec. 3 Self-Spectre method (speculation depth, Fig. 2, hidden computation, AES/RSA primitives, Fig. 3) | C12-C15, C21, C24-C26 (proved under the abstract contract); Tables 1-2 and Fig. 4 are measurements, native evidence only; compiled instruction counts (e.g. 93+5*44) are compiler output |
| Sec. 4 Write-Execute (model, primitives, arithmetic, Figs. 5-7) | C01-C11, C16-C18 (proved; assembled objects compared with COFF bytes) |
| Real processor behavior (pipeline, predictor, cache, timing) | not formalized: the vendors do not publish it; only the abstract contract is stated, never claimed for a CPU |
