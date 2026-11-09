#!/usr/bin/env bash
# audit/icall/run-preserves64.sh: the amd64 rows of the `preserves` audit rule (U-ICALL-PRESERVES); fails on any wrongly accepted or rejected form.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
lake env lean audit/icall/PreservesAudit64.lean && echo "ICALL PRESERVES AUDIT (amd64): ok" || { echo "ICALL PRESERVES AUDIT (amd64): FAILED"; exit 1; }
