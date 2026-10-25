#!/usr/bin/env bash
# Round-8 regression rows (docs/AUDIT-ROUND8.md). Exits 1 if a blocked attack prints Verified (or
# is blocked without the expected diagnostic), a control stops verifying, or a cache row
# regresses. G3a (fixed by stub code pins) must be rejected at extraction.
# Every attack verification passes --fresh (the cold path) and uses a private temporary cache;
# the M1/C1 rows use their own temporary caches. All are removed at the end.
# Writes only under audit/round8/work/rows/, audit/round8/bin/ and those temporary caches.
# Usage: audit/round8/run-round8.sh
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
J="$root/audit/round8/bin/janus"; mkdir -p "$(dirname "$J")"
# audit/run-rounds.sh builds janus and the framework once for every lane (JANUS_AUDIT_BIN,
# JANUS_AUDIT_PREBUILT=1).
if [ -n "${JANUS_AUDIT_BIN:-}" ]; then J="$JANUS_AUDIT_BIN"; else go build -o "$J" ./cmd/janus || exit 1; fi
[ "${JANUS_AUDIT_PREBUILT:-}" = 1 ] || lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
[ -d artifacts/amd64/HexDigit ] && [ -d artifacts/amd64/Add ] || bash scripts/build-examples-amd64.sh >/dev/null 2>&1
W=audit/round8/work/rows; rm -rf "$W"; mkdir -p $W
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-round8.XXXXXX")" || exit 1   # 0700: the caches' parent
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/fresh"; export JANUS_CACHE_DIR="$T/fresh"
for f in Add HashWith AddThree; do
  mapfile -t tg < <(scripts/example-targets.sh "$f")   # HashWith: its two static itabs
  "$J" extract artifacts/examples-arm64 "example.com/basic.$f" "$W/$f" ${tg[@]+"${tg[@]}"} >/dev/null || exit 1
done
broken=()
A=audit/round8/attacks

# row NAME EXPECT [PATTERN...]: verdict of $out. EXPECT "blocked" (must not print Verified; if a
# PATTERN is given the output must contain it) or "Verified" (must print Verified and contain
# every PATTERN).
row() {
  local name=$1 expect=$2 verdict status="" pat
  shift 2
  verdict="$(grep -m1 -E '^(Verified|Invalid|Error)' <<<"$out" | cut -c1-150)"
  [ -n "$verdict" ] || verdict="(no verdict) $(head -1 <<<"$out" | cut -c1-120)"
  case $expect in
    blocked) case $verdict in Verified*) status=BROKEN ;; esac ;;
    Verified) case $verdict in Verified*) ;; *) status=BROKEN ;; esac ;;
  esac
  for pat in "$@"; do grep -qF -- "$pat" <<<"$out" || status=BROKEN; done
  printf '  %-36s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
# v PROOF ARTIFACT [THEOREM]
v() { out="$("$J" verify --fresh --janus-root "$root" --proof "$1" "$2" ${3:+--theorem "$3"} 2>&1)"; }

echo "== I1: every object name in the statement resolves in Extracted.program"
nodata='but the extracted program has no data object of that name'
v $A/I1a_itab_name_lookalike.lean $W/HashWith;   row I1a_itab_name_lookalike blocked "$nodata" "MulHаsher"
v $A/I1b_itab_name_absent.lean $W/HashWith;      row I1b_itab_name_absent blocked "$nodata"
v $A/I1c_segaddr_absent.lean $W/Add;             row I1c_segaddr_absent blocked 'but the extracted program has no function of that name'
v $A/I1d_itab_other_data.lean $W/HashWith;       row I1d_itab_other_data blocked 'which is not Extracted.program.data'
v $A/I1e_itab_name_via_def.lean $W/HashWith;     row I1e_itab_name_via_def blocked "$nodata"
v $A/I1f_amd64_database_absent.lean artifacts/amd64/Add; row I1f_amd64_database_absent blocked 'the lookup would silently return 0'
echo "   controls (real names: literal, through an abbrev, segAddr, amd64 dataBase)"
v examples/proofs/HashWith.lean $W/HashWith;     row I1_ctl_HashWith_itab_abbrev Verified 'ItabIs' 'mulItab'
v examples/proofs/AddThree.lean $W/AddThree Proof.add_summary
row I1_ctl_AddThree_segAddr Verified 'segAddr Extracted.program "example.com/basic.Add"'
v examples/proofs-amd64/HexDigit/Proof.lean artifacts/amd64/HexDigit Proof.correctness
row I1_ctl_amd64_HexDigit_dataBase Verified

echo "== N1: native reduction (Lean.reduceBool + implemented_by)"
v $A/N1a_reducebool_implemented_by.lean $W/Add;  row N1a_reducebool_implemented_by blocked 'Lean.trustCompiler'

echo "== G3: a go1.25 binary labelled go1.26 (audit/round8/govers; fixed: stubs pinned by code, cmd/janus/stubpin.go)"
if ( cd audit/round8/govers && GOTOOLCHAIN=go1.25.5 CGO_ENABLED=0 GOOS=linux GOARCH=arm64 \
     go build -trimpath -buildvcs=false -ldflags=-X=runtime.buildVersion=go1.26.0 -o "$root/$W/govers" ./cmd ) 2>/dev/null; then
  if out="$("$J" extract $W/govers main.Add $W/GvAdd 2>&1)"; then
    printf '  %-36s %-8s %s   <-- BROKEN\n' G3a_spoofed_goversion_stub blocked "extraction ACCEPTED the spoofed stub"; broken+=(G3a)
  else
    printf '  %-36s %-8s %s\n' G3a_spoofed_goversion_stub blocked "$(grep -m1 -iE 'stub|pin|pclntab' <<<"$out" | cut -c1-110)"
  fi
else
  printf '  %-36s %-8s %s\n' G3a_spoofed_goversion_stub skipped "fixture not built here (go1.25.5 unavailable); audit/round7 G3a rows cover the committed extraction"
fi

echo "== L1/M1/C1: unit rows (go test; L1 is covered here: a changed lib/lean file changes every key)"
for t in TestRound8ToolchainCacheID TestRound8TrustedManifestMAC TestRound8CacheRootPrivate; do
  if (cd cmd/janus && go test -count=1 -timeout 10m -run "^$t\$" . >/dev/null 2>&1); then
    printf '  %-36s ok\n' "$t"
  else printf '  %-36s FAILED   <-- BROKEN\n' "$t"; broken+=("$t"); fi
done

# The rest run janus without --fresh (with the sandbox), each with its own cache.
vc() { "$J" verify --janus-root "$root" "$@" 2>&1; }
cachedT() { grep -q 'janus-timing: trusted compile (cached)' <<<"$1"; }

mkdir -m 700 "$T/m1"; C="$T/m1"
echo "== M1: trusted-compile manifests carry a MAC under the cache's key"
# The result cache is off so that every run reaches the trusted compile.
m1() { out="$(JANUS_CACHE_DIR="$C" JANUS_TIMINGS=1 JANUS_RESULT_CACHE=off vc $W/Add --proof examples/proofs/Add.lean)"; }
m1; m1
if grep -q '^Verified' <<<"$out" && cachedT "$out" && ls "$C"/v1/trusted/*/*/manifest.json >/dev/null 2>&1 &&
   grep -q '"mac":"[0-9a-f]\{64\}"' "$C"/v1/trusted/*/*/manifest.json; then
  printf '  %-36s ok       authentic entry: trusted compile (cached)\n' M1_authentic_hit
else printf '  %-36s not a hit   <-- BROKEN\n' M1_authentic_hit; broken+=(M1-hit); fi
for kind in missing bad; do
  for mf in "$C"/v1/trusted/*/*/manifest.json; do
    python3 -I - "$mf" "$kind" <<'EOF'
import json, sys
p, kind = sys.argv[1], sys.argv[2]
m = json.load(open(p))
if kind == "missing": m.pop("mac", None)
else: m["mac"] = "0" * 64
json.dump(m, open(p, "w"))
EOF
  done
  m1
  if grep -q '^Verified' <<<"$out" && ! cachedT "$out"; then
    printf '  %-36s ok       %s MAC: a miss, compiled again\n' "M1_${kind}_mac" "$kind"
  else printf '  %-36s %s   <-- BROKEN\n' "M1_${kind}_mac" "$(cachedT "$out" && echo "the entry was USED" || grep -m1 -E '^(Invalid|Error)' <<<"$out")"; broken+=("M1-$kind"); fi
  m1
  if cachedT "$out"; then printf '  %-36s ok       the entry was replaced and hits again\n' "M1_${kind}_replaced"
  else printf '  %-36s not replaced   <-- BROKEN\n' "M1_${kind}_replaced"; broken+=("M1-$kind-replace"); fi
done

echo "== C1: the cache root is private"
c1() { # c1 NAME CACHE PATTERN...
  local name=$1 c=$2 pat st=""; shift 2
  out="$(JANUS_CACHE_DIR="$c" vc $W/Add --proof examples/proofs/Add.lean)"
  grep -q '^Invalid: The Janus cache' <<<"$out" || st=BROKEN
  for pat in "$@"; do grep -qF -- "$pat" <<<"$out" || st=BROKEN; done
  printf '  %-36s %-8s %s%s\n' "$name" blocked "$(grep -m1 -E '^(Verified|Invalid|Error)' <<<"$out" | cut -c1-110)" "${st:+   <-- BROKEN}"
  [ -n "$st" ] && broken+=("$name")
  return 0
}
mkdir -m 770 "$T/g"; chmod 770 "$T/g"
c1 C1a_group_writable_root "$T/g" 'is writable by group or others (mode 770)' 'round 8 C1'
mkdir -m 700 "$T/s" "$T/s/v1" "$T/elsewhere"; ln -s "$T/elsewhere" "$T/s/v1/trusted"
c1 C1b_symlinked_subdir "$T/s" 'v1/trusted is a symbolic link' 'round 8 C1'
chmod 644 "$C/v1/result/.key"
c1 C1c_key_0644 "$C" '.key is unsafe: its mode is 0644' 'round 8 C1'
chmod 600 "$C/v1/result/.key"
out="$(JANUS_CACHE_DIR="$C" vc $W/Add --proof examples/proofs/Add.lean)"; row C1_ctl_private_cache Verified

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-8 rows as expected."
