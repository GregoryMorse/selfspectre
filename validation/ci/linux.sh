#!/usr/bin/env bash
# Linux proof job body (run inside a bounded cgroup by .github/workflows/proof.yml):
# Mathlib cache, cold build of the library, the Challenge and the Solution, axiom audit, generated-file
# and errata checks.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/../.."
ROOT="$PWD"
cd lean
lean --version
lake exe cache get || echo "Mathlib cache unavailable; building from source"
lake build WriteExecute Challenge Solution 2>&1 | tee "$ROOT/lake-build.log"
cd "$ROOT"
python3 validation/ci/axioms.py
python3 validation/make_challenge.py --check
python3 validation/audit_errata.py
python3 validation/audit_errata.py --pdf
python3 validation/audit_errata.py --refs
python3 validation/audit_smc_fallthrough.py
(cd lean && lake env lean ErrataRefs.lean)
python3 validation/gen_aes_tables.py
echo "linux-proof: OK"
