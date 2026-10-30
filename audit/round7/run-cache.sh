#!/usr/bin/env bash
# Round 7 cache rows (docs/AUDIT-ROUND7.md §7, docs/SOUNDNESS.md, "Verification-result cache"): attempts to poison or misuse the
# trusted verification-result cache. Exits 1 if a row regresses (BROKEN).
# Usage: audit/round7/run-cache.sh [-j N]   (-j: rows at once, scripts/lib/parallel.sh)
# Writes only under audit/round7/work/ and a temporary janus cache (removed at the end).
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=../../scripts/lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
par_init "$@"
J="$root/audit/round7/bin/janus"; mkdir -p "$(dirname "$J")"
# audit/run-rounds.sh builds janus and the framework once for every lane (JANUS_AUDIT_BIN,
# JANUS_AUDIT_PREBUILT=1).
if [ -n "${JANUS_AUDIT_BIN:-}" ]; then J="$JANUS_AUDIT_BIN"; else CGO_ENABLED=0 go build -o "$J" ./cmd/janus || exit 1; fi
[ "${JANUS_AUDIT_PREBUILT:-}" = 1 ] || lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
W=audit/round7/work; rm -rf "$W"; mkdir -p $W
C="$(mktemp -d "${TMPDIR:-/tmp}/janus-round7-cache.XXXXXX")"
trap 'rm -rf "$C"' EXIT
export JANUS_CACHE_DIR="$C"
for n in Add Add2 Add3 Add4 Add5; do "$J" extract artifacts/examples-arm64 example.com/basic.Add $W/$n >/dev/null || exit 1; done
broken=()

# row NAME RESULT OK: prints the row; OK is "yes" when the attack was blocked.
row() {
  local mark=""
  [ "$3" = yes ] || { mark="   <-- BROKEN"; broken+=("$1"); }
  printf '  %-34s %s%s\n' "$1" "$2" "$mark"
}
v() { "$J" verify --janus-root "$root" "$@" 2>&1; }
cached() { grep -q '^  Cached:' <<<"$1"; }
verdict() { grep -m1 -E '^(Verified|Invalid)' <<<"$1" | cut -c1-100; }

echo "== priming: an honest verification records its result (the cache now has a key and an entry)"
out="$(v $W/Add --proof examples/proofs/Add.lean)"; again="$(v $W/Add --proof examples/proofs/Add.lean)"
if cached "$again" && ! cached "$out"; then echo "  ok: the second run is a cache hit"
else echo "  >>> priming failed (first: $(verdict "$out"), second cached: $(cached "$again" && echo yes || echo no))"; broken+=(priming); fi

# RC1: a sandboxed proof probes the cache (key, entries) and plants a file. It must see an empty
# directory (the proof then compiles and verifies) and nothing may reach the host.
rc1() { # rc1 NAME DIR [env…]
  local name=$1 dir=$2; shift 2
  local out; out="$(env "$@" "$J" verify --janus-root "$root" "$dir" --proof audit/round7/attacks/RC1_proof_probe.lean 2>&1)"
  local ok=yes
  [ -e "$C/v1/result/planted-by-proof" ] && ok=no
  grep -q 'RC1: the result cache' <<<"$out" && ok=no
  grep -q 'Stage: sandbox' <<<"$out" && { printf '  %-34s %s\n' "$name" "skipped (sandbox mode unavailable here)"; return 0; }
  row "$name" "$(verdict "$out") [cache invisible: $([ $ok = yes ] && echo yes || echo NO)]" "$([ "$(verdict "$out" | cut -c1-8)" = Verified ] && echo $ok || echo no)"
}
par_run 'echo "== RC1: a proof cannot read the key or the entries, nor plant a file"; rc1 RC1_proof_probe_bwrap $W/Add2'
par_run 'rc1 RC1_proof_probe_unshare $W/Add5 JANUS_SANDBOX=unshare'

# RC2: a consumer lakefile (elaborated by the sandboxed Lake) probes and plants the same way.
par_run '
echo "== RC2: a lakefile cannot read or plant into the cache"
P=$W/R1; rm -rf "$P"; cp -r audit/attacks/R1_pkg "$P"
sed -i "s|@JANUS@|$root|; s|-- @EXTRA_REQUIRE@||" "$P/lakefile.lean"
echo "-- run $(date +%s%N)" >> "$P/lakefile.lean"
printf "{\"version\":\"1.2.0\",\"packagesDir\":\".lake/packages\",\"name\":\"r1\",\"lakeDir\":\".lake\",\"fixedToolchain\":false,\"packages\":[{\"type\":\"path\",\"scope\":\"\",\"name\":\"janus\",\"manifestFile\":\"lake-manifest.json\",\"inherited\":false,\"dir\":\"%s\",\"configFile\":\"lakefile.toml\"}]}\n" "$root" > "$P/lake-manifest.json"
out="$(JANUS_R1_MODE=resultcache "$J" verify --janus-root "$root" $W/Add3 --proof "$P/R1/Plain.lean" --proof-root "$P" --theorem R1.Plain.claim 2>&1)"
ok=yes; [ -e "$C/v1/result/planted-by-lakefile" ] && ok=no; grep -q "RC2-VISIBLE" <<<"$out" && ok=no
row RC2_lakefile_probe "$(verdict "$out") [cache invisible: $([ $ok = yes ] && echo yes || echo NO)]" "$([ "$(verdict "$out" | cut -c1-8)" = Verified ] && echo $ok || echo no)"'

# RC3: an entry modified on disk (its report claims multiplication) is not authentic: the next
# verification ignores it, runs, and prints the real statement.
par_run '
echo "== RC3: a tampered entry is ignored"
mkdir -p $W/RC3; cp examples/proofs/Add.lean $W/RC3/Add.lean
out="$(v $W/Add4 --proof $W/RC3/Add.lean)"
f=$(grep -rl "RC3/Add.lean" "$C/v1/result" --include=*.json | head -1)
if [ -n "$f" ]; then
  sed -i "s/x.toNat + y.toNat/x.toNat * y.toNat/" "$f"
  out="$(v $W/Add4 --proof $W/RC3/Add.lean)"
  ok=yes; cached "$out" && ok=no; grep -q "x.toNat \* y.toNat" <<<"$out" && ok=no
  row RC3_tampered_entry "$(verdict "$out") [cached: $(cached "$out" && echo YES || echo no), statement: $(grep -qF "x.toNat + y.toNat" <<<"$out" && echo honest || echo WRONG)]" $ok
else row RC3_tampered_entry "no entry was recorded for Add4" no; fi'

# RC4: an entry recorded with one framework is not used with another (a --janus-root copy whose
# GoABI.lean then changes by a comment: the framework hash differs, so the key differs).
par_run '
echo "== RC4: a stale framework never hits"
F=$W/janus-root-copy; rm -rf "$F"; mkdir -p "$F/.lake"
cp -a lakefile.toml lake-manifest.json lean-toolchain Janus.lean Janus "$F/"; cp -a .lake/build "$F/.lake/"
"$J" extract artifacts/examples-arm64 example.com/basic.Add $W/AddF >/dev/null
"$J" verify --janus-root "$F" $W/AddF --proof examples/proofs/Add.lean >/dev/null 2>&1
hit="$("$J" verify --janus-root "$F" $W/AddF --proof examples/proofs/Add.lean 2>&1)"
echo "-- round 7: a framework change" >> "$F/Janus/GoABI.lean"
out="$("$J" verify --janus-root "$F" $W/AddF --proof examples/proofs/Add.lean 2>&1)"
ok=yes; cached "$out" && ok=no; cached "$hit" || ok=no
row RC4_stale_framework "$(verdict "$out") [before the change cached: $(cached "$hit" && echo yes || echo NO); after: $(cached "$out" && echo YES || echo no)]" $ok
rm -rf "$F"'

# RC5/RC6: --fresh and --unsafe-no-sandbox never use the cache.
par_run '
echo "== RC5/RC6: --fresh and --unsafe-no-sandbox bypass the cache"
out="$(v $W/Add --proof examples/proofs/Add.lean --fresh)"
row RC5_fresh_bypasses "$(verdict "$out") [cached: $(cached "$out" && echo YES || echo no)]" "$(cached "$out" && echo no || echo yes)"
out="$(v $W/Add --proof examples/proofs/Add.lean --unsafe-no-sandbox)"
row RC6_unsandboxed_bypasses "$(verdict "$out") [cached: $(cached "$out" && echo YES || echo no)]" "$(cached "$out" && echo no || echo yes)"'
par_wait

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-7 rows as expected."
