#!/usr/bin/env bash
# audit/icall/run.sh: compile the U-ICALL red-team rows 3 and 4 against an extraction of WriteTo (arm64).
# Usage: audit/icall/run.sh EXTRACTED_DIR   (a `janus extract … example.com/basic.WriteTo` output directory)
# The file passes when it compiles (every `fail_if_success` saw the tactic refuse); it fails when a variant is
# accepted ("fail_if_success" error) or does not compile.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
d="${1:?extracted dir}"
mkdir -p "$d/olean"
LEAN_PATH="$root/.lake/build/lib/lean" lake env lean -R "$d" -o "$d/olean/Extracted.olean" "$d/Extracted.lean"
LEAN_PATH="$root/.lake/build/lib/lean:$d/olean" lake env lean "$root/audit/icall/WriteToRedTeam.lean" 2>&1 | grep -v '^warning' || true
LEAN_PATH="$root/.lake/build/lib/lean:$d/olean" lake env lean "$root/audit/icall/WriteToRedTeam.lean" >/dev/null 2>&1 && echo "ICALL RED TEAM: ok (every variant refused)" || { echo "ICALL RED TEAM: FAILED"; exit 1; }
