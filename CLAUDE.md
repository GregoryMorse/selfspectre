# selfspectre — Lean formalization of Write-Execute

Goal: Lean-verify the Write-Execute part of Morse, *Self-Spectre, Write-Execute and the Hidden
State*, TMMP 73 (2019) 131–144, with errata, legacy-code corrections and a Palomar-ready package.

**Every session:** read `FORMALIZATION_PLAN.md` §0–§4, then only the current round's section
(current round and handoff notes: `lean/ROUNDS.md`). Decisions in plan §2 are settled; ask the
user before deviating. Do not browse `../smcTuring` beyond the paths the plan names.

**Current round: R3** (Turing-completeness; R0-R2 done, see lean/ROUNDS.md). Update this line at each round close.

## Hard rules

- Run every build/test serially through `python validation/limited_run.py -- <cmd>` (1.5 GB
  aggregate cap, Lean `-M768 -j1`). A capped failure is a failed check; never bypass the guard
  or retry without it. Do not kill unrelated processes.
- No SSH/remote servers. Cold full builds and Palomar runs use GitHub Actions.
- Pins: Lean `leanprover/lean4:v4.35.0-rc3`, Mathlib `302343bb9a029d4edab4f736703f0736896c1b64`.
  Do not change them without asking.
- No `sorry`/`admit` (except `lean/Challenge.lean`), no `axiom`, `native_decide`, `bv_decide`,
  `Lean.ofReduceBool`, `unsafe`. Only `propext`, `Quot.sound`, `Classical.choice` may appear.
- Statement-level definitions live in `lean/WriteExecute/Spec/` (core/Mathlib imports only,
  `@[expose]`); `Challenge.lean` is generated from them.
- Errata quote the published PDF (`validation/reference/tmmp-2019-0010.pdf`), never the draft.
  Evidence (native tests, layout comparison) is never described as proof.
- Economy: one round per session; build only touched modules until round close; three focused
  attempts per obstacle, then narrow the statement and record an open obligation in
  `lean/PAPER_MAP.md`; at most one batched question to the user per round.

## Authorizations

- Local commits to `master` at green increments: authorized (2026-10-11).
- Pushes to `origin` and GitHub Actions runs: **not authorized**; the user does these.
