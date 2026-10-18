# selfspectre — Lean formalization of Write-Execute

Goal: Lean-verify the Write-Execute part of Morse, *Self-Spectre, Write-Execute and the Hidden
State*, TMMP 73 (2019) 131–144, with errata, legacy-code corrections and a Palomar-ready package.

**Every session:** read `FORMALIZATION_PLAN.md` §0–§4, then only the current round's section
(current round and handoff notes: `lean/ROUNDS.md`). Decisions in plan §2 are settled; ask the
user before deviating. Do not browse `../smcTuring` beyond the paths the plan names.

**Current round: none** (R0-R9 done; registered as PALOMAR-2026-10-14-000007 v1; candidate v2 native investigation in progress, see lean/ROUNDS.md). Update this line at each round close.

## Hard rules

- Run every build/test serially through `python validation/limited_run.py -- <cmd>` (1.5 GB
  aggregate cap, Lean `-M768 -j1`). A capped failure is a failed check; never bypass the guard
  or retry without it. Do not kill unrelated processes.
- No SSH/remote servers, except 157.181.172.78 (user-authorized 2026-10-17, for portability tests in a `selfspectre` folder; the
  permission classifier blocked the attempt, so the grid is tested in GitHub Actions). Cold full builds and Palomar runs use GitHub Actions.
- Layout: native sources in `src/`, Visual Studio files in `vs/`, all build output under `build/` (CMake `build/cmake`, MSBuild
  `build/msbuild`). Keep the root clean; never build in place.
- Pins: Lean `leanprover/lean4:v4.35.0-rc3`, Mathlib `5e043698502894993991089b2dd893867c0db5c2`.
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
- Pushes to `origin` (branch `master`) once CI is ready: authorized (2026-10-11, R8). The push triggers `proof.yml`. Dispatching `palomar-full.yml`, any Palomar submission, registration, proof tag or gist: **not authorized** without a separate explicit user instruction.
