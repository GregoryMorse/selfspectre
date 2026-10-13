# Palomar submission sheet (submitted by the author; record kept in a private file)

| Field | Value |
|---|---|
| Repository | GregoryMorse/selfspectre |
| Exact commit | ab6dfb149e382cacbff684a32217535636809d29 (CI run 38326421670; full preflight run 38327159704; docs-only commits after it) |
| project_path | lean |
| Comparator config | lean/comparator.json |
| Metadata | lean/formalization.yaml |
| Selected statement | PalomarWE.mathematical_result (Write-Execute and Self-Spectre under an abstract speculation contract, C23-C26) |
| First submission / existing id | first submission; id blank |

Notes: AI assistance (Claude) is disclosed in formalization.yaml. The model is ideal (unbounded). Warning: Challenge.lean is 833 lines / ~58 KB (hard limit 1000 / 100 KiB; preferred 300 / 32 KiB).
Closed since the first sheet: C18 (Fig. 6 byte-level proof, `X86/Fig6.lean`) and the WE-entry edge vectors (`validation/native_edge.py`).
Unverified: renderer on the new pin, Comparator/NanoDa run records, author errata review, research-interest review of the Self-Spectre results (an earlier submission of abb8273 was reviewed with a separately selected Spectre index-arithmetic result and flagged; that result was dropped and the contract-level Self-Spectre results added in R9).
Mathlib re-pinned 302343bb -> 5e043698 (same Lean v4.35.0-rc3) so that Plausible is fb13df7, the revision Verso pins; Mathlib 302343bb (Plausible afc2695) is rejected by the renderer's manifest merge (PalomarSubmission #166 / #131). Full preflight passed on the final commit.
Known: the legacy Debug|Win32 harness (`writeexec.c`, random checks) failed once in CI on a rare random mismatch near the MODEXP32 check, passed on rerun, and could not be reproduced in ~1.2M local random checks; it is preserved unmodified (legacy code, not part of the proof).
