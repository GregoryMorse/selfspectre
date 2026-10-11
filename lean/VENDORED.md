# Vendored code

Source: smcTuring (CC0-1.0), audited commit `1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4`
(`git -C ../smcTuring show 1ab379c:<path>`). Namespaces `SmcTuring.*` → `WriteExecute.*`.

| Source (lean/SmcTuring/…) | Target | Edits |
|---|---|---|
| `Memory.lean` | `WriteExecute/Base/Memory.lean` | namespace rename only |
| `Turing.lean` | `WriteExecute/Base/Turing.lean` | namespace + import rename only |
| `MathlibTM0/Compiler.lean` + `MathlibTM0/Simulation.lean` lines 9–81 | `WriteExecute/Base/MathlibTM0.lean` | merged into one file in namespace `WriteExecute.MathlibTM0`; the `SMC.*` import and the final SMC-specific theorems (`fixed_smc_mathlib_simulation`, `standard_terminal_output`) dropped |

Byte-memory modules (`Native/LittleEndian`, `Encoding`, `ByteMemory`, selected lemmas) are vendored in R6.
`WriteExecute/Base/MathlibTM0.lean` imports Mathlib and is built in CI only (local 1.5 GB cap).
