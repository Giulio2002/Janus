#!/usr/bin/env bash
# audit/icall/run64.sh EXTRACTED_DIR: the amd64 rows 3 and 4 against an extraction of example.com/basic.WriteTo (amd64).
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
d="${1:?extracted dir}"
mkdir -p "$d/olean"
LEAN_PATH="$root/.lake/build/lib/lean" lake env lean -R "$d" -o "$d/olean/Extracted.olean" "$d/Extracted.lean"
LEAN_PATH="$root/.lake/build/lib/lean:$d/olean" lake env lean "$root/audit/icall/WriteToRedTeam64.lean" >/dev/null 2>&1 && echo "ICALL RED TEAM (amd64): ok (every variant refused)" || { echo "ICALL RED TEAM (amd64): FAILED"; exit 1; }
