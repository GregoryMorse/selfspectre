# Palomar submission sheet (prepared, NOT submitted)

| Field | Value |
|---|---|
| Repository | GregoryMorse/selfspectre |
| Exact commit | the final `master` HEAD recorded in the handoff (code CI-verified at aeb4e9e44e13eb79c2d0d54e8875730846fb8559, run 38245193701; docs-only commits after it) |
| project_path | lean |
| Comparator config | lean/comparator.json |
| Metadata | lean/formalization.yaml |
| Selected statement | PalomarWE.mathematical_result |
| First submission / existing id | first submission; id blank |

Notes: AI assistance (Claude) is disclosed in formalization.yaml. The model is ideal (unbounded). Warning: Challenge.lean is 706 lines / ~50 KB (hard limit 1000 / 100 KiB; preferred 300 / 32 KiB).
Closed since the first sheet: C18 (Fig. 6 byte-level proof, `X86/Fig6.lean`) and the WE-entry edge vectors (`validation/native_edge.py`).
Unverified: official full preflight, Comparator/NanoDa run records, author errata review.
Mathlib re-pinned 302343bb -> 5e043698 (same Lean v4.35.0-rc3) so that Plausible is fb13df7, the revision Verso pins; Mathlib 302343bb (Plausible afc2695) is rejected by the renderer's manifest merge (PalomarSubmission #166 / #131). Full preflight (mechanical) passed on 3dfbf63 with the old pin and is re-run on the final commit.
Known: the legacy Debug|Win32 harness (`writeexec.c`, random checks) failed once in CI on a rare random mismatch near the MODEXP32 check, passed on rerun, and could not be reproduced in ~1.2M local random checks; it is preserved unmodified (legacy code, not part of the proof).
