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
| C13 | §3 | AES T-tables equal the algebraic definition and the literal tables | F | R5 | todo | |
| C14 | §3 | T-table round = FIPS-197 round; final round uses Te4 | F | R5 | todo | |
| C15 | §4 | WE AES lookup procedure = AES-128 encryption (FIPS-197 C.1) | F | R5 | todo | |
| C16 | Fig. 5 p.140 | `not` through SHL4 and the NOT table, byte level (W10) | F+M | R6 | todo | |
| C17 | Fig. 7 p.142 | Carry conditional jump, byte level | F+M | R6 | todo | |
| C18 | Fig. 6 p.141 | XOR double lookup and re-executable copy loop | F+M | R6 | todo | |
| C19 | Fig. 1 p.134 | Branchless select yields the malicious index iff j mod 6 = 0 | F | R4 | proved | `Spectre.select_32`, `select_64` |
| C20 | §2 p.134 | `mix_i = (i*167+13) & 255` permutes 0..255 | F | R4 | proved | `Spectre.mix_perm`, `mix_injective`, `mix_surjective` |
| C21 | Fig. 3 | AES-NI sequence = AES-128 (stretch) | F | R5 | todo | |
| C22 | asm comments | ShiftRows index formulas = FIPS-197 ShiftRows | F | R5 | todo | |

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

Code fixes L01-L05: applied in R7.
