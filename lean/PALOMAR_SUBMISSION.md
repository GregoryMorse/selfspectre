# Palomar submission sheet (registered: PALOMAR-2026-10-14-000007 v1)

| Field | Value |
|---|---|
| Repository | GregoryMorse/selfspectre |
| Exact commit | fe720739a11adeb1e9e2b2b13948cc6a7586920d (registered; docs-only on top of 62e20ac83c2e6903c9d2bb3793253c59c99c0d17, which passed CI run 38375370566 and full preflight run 38376642196) |
| project_path | lean |
| Comparator config | lean/comparator.json |
| Metadata | lean/formalization.yaml |
| Selected statement | PalomarWE.mathematical_result (Write-Execute and Self-Spectre under an abstract speculation contract, C23-C26) |
| Registry entry | PALOMAR-2026-10-14-000007, version 1, registered 2026-10-14 by the author (https://palomar-registry.org/entry?id=PALOMAR-2026-10-14-000007&version=1); status registered, trust level high |

Notes: AI assistance (Claude) is disclosed in formalization.yaml. The model is ideal (unbounded). Warning: Challenge.lean is 851 lines / ~60 KB (hard limit 1000 / 100 KiB; preferred 300 / 32 KiB).
Closed since the first sheet: C18 (Fig. 6 byte-level proof, `X86/Fig6.lean`) and the WE-entry edge vectors (`validation/native_edge.py`).
Unverified: renderer on the new pin, Comparator/NanoDa run records, author errata review, research-interest review of the Self-Spectre results (an earlier submission of abb8273 was reviewed with a separately selected Spectre index-arithmetic result and flagged; that result was dropped and the contract-level Self-Spectre results added in R9).
Mathlib re-pinned 302343bb -> 5e043698 (same Lean v4.35.0-rc3) so that Plausible is fb13df7, the revision Verso pins; Mathlib 302343bb (Plausible afc2695) is rejected by the renderer's manifest merge (PalomarSubmission #166 / #131). Full preflight passed on the final commit.
Known: the legacy Debug|Win32 harness (`writeexec.c`, random checks) failed once in CI on a rare random mismatch near the MODEXP32 check, passed on rerun, and could not be reproduced in ~1.2M local random checks; it is preserved unmodified (legacy code, not part of the proof).
Outcome: four submissions by the author (private records kept outside the repository). Automated reviews 1-3 requested
changes, each addressed in the Lean statement or the prose: (1) the separately selected Spectre index arithmetic was dropped;
(2) `VictimLeak` reload result stated from a cleared probe array; (3) the source note separates the unconditional Write-Execute
results from the conditional Self-Spectre results, `WindowDepth` states the observable leak from a cleared probe array and names
the touch-trace boundary, and `Mistraining` follows the PoC's descending loop. The fourth submission was registered as PALOMAR-2026-10-14-000007 v1.
Follow-up for a later version (author): revise the title wording ("... with errata").
