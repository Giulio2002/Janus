#!/usr/bin/env bash
# Regression test: row scripts must select a verdict by pattern, never by position, so a stderr banner
# (janus: memory guard: ..., janus-memguard: ..., memguard[...]) before or after the verdict cannot turn a row BROKEN.
# (A nightly lost 8 rows of the 'all' round and a cachekeys check to exactly that.)
#   - scripts/lib/verdict.sh on injected banners (before, after, none, no verdict at all);
#   - the real janus binary with the guard forced to "none" (notice must come AFTER the verdict), with
#     JANUS_MEMGUARD_LOG=1 and JANUS_MEMGUARD_VERBOSE=1 (banner first): the verdict is the same in every mode.
# Seconds (one go build); scratch in a mktemp directory on disk.
#   scripts/lib/test-verdict-banner.sh
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
mkdir -p "$root/artifacts"
t=$(mktemp -d "${TMPDIR:-$root/artifacts}/test-verdict-banner.XXXXXX")
trap 'rm -rf "$t"' EXIT
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }
# shellcheck source=verdict.sh
. "$root/scripts/lib/verdict.sh"
export PATH=/usr/local/go/bin:$PATH

B1='janus: memory guard: cgroup, limit 16.0 GiB per job (default), no swap, under /x'
B2='janus-memguard: lake env lean                          peak 1.0 GiB / limit 16.0 GiB'
B3='memguard[slot]: peak 1.0 GiB / limit 4.0 GiB (cgroup)'
V='Invalid: statement identity'
chk() { [ "$2" = "$3" ] && ok "$1" || bad "$1: got '$2', want '$3'"; }
chk "no banner"            "$(printf '%s\n' "$V" | verdict_line)" "$V"
chk "banner before"        "$(printf '%s\n%s\n%s\n' "$B1" "$B2" "$V" | verdict_line)" "$V"
chk "banner after"         "$(printf '%s\n%s\n' "$V" "$B1" | verdict_line)" "$V"
chk "banners around"       "$(printf '%s\n%s\n%s\n%s\n' "$B1" "$V" "$B2" "$B3" | verdict_line)" "$V"
chk "Verified wins by order among verdicts" "$(printf '%s\n%s\n' 'Verified: T' "$V" | verdict_line)" 'Verified: T'
case "$(printf '%s\n%s\n' "$B1" "$B3" | verdict_line)" in NOVERDICT*) ok "no verdict at all: NOVERDICT" ;; *) bad "no verdict not detected" ;; esac
case "$(: | verdict_line)" in NOVERDICT*) ok "empty output: NOVERDICT" ;; *) bad "empty not detected" ;; esac
chk "lean_first skips banners" "$(printf '%s\n%s\n%s\n' "$B1" "$B2" "'X' depends on axioms: [propext]" | lean_first)" "'X' depends on axioms: [propext]"

# ---- the real binary
bin="$t/janus"
( cd "$root" && CGO_ENABLED=0 go build -o "$bin" ./cmd/janus ) || { bad "go build"; exit 1; }
missing="$t/absent"
run() { env -u JANUS_MEMGUARD_LOG -u JANUS_MEMGUARD_VERBOSE -u JANUS_MEMGUARD "$@" "$bin" verify "$missing" --janus-root "$root" 2>&1; }
base="$(run | verdict_line)"
case "$base" in Invalid:*|Error:*) ok "baseline verdict: $base" ;; *) bad "baseline has no verdict: $base" ;; esac
for mode in "JANUS_MEMGUARD=forced-none" "JANUS_MEMGUARD_LOG=1" "JANUS_MEMGUARD_VERBOSE=1" "JANUS_MEMGUARD=forced-none JANUS_MEMGUARD_LOG=1"; do
  # shellcheck disable=SC2086
  out="$(run $mode)"
  chk "$mode: same verdict" "$(printf '%s\n' "$out" | verdict_line)" "$base"
done
out="$(run JANUS_MEMGUARD=forced-none)"
case "$(printf '%s\n' "$out" | head -1)" in Invalid:*|Error:*) ok "guard none: the first output line is the verdict" ;; *) bad "guard none: first line is not the verdict: $(printf '%s\n' "$out" | head -1)" ;; esac
case "$(printf '%s\n' "$out" | tail -1)" in 'janus: memory guard: NONE available'*) ok "guard none: the notice is printed, after the verdict" ;; *) bad "guard none: notice missing/misplaced: $out" ;; esac
exit $fail
