#!/usr/bin/env bash
# Round-10 regression rows (docs/AUDIT-ROUND10.md). Exits 1 if a blocked attack verifies, a
# control stops verifying, a kernel-checked model row changes verdict, or a real-runtime probe
# contradicts what the fixed statements assume.
# Every janus verification uses --fresh and a private temporary cache. Writes only under
# audit/round10/work/, audit/round10/bin/ and a mktemp directory (removed at the end).
# Needs: go1.26.0 (GOTOOLCHAIN), qemu-aarch64 (arm64 probe rows); the amd64 oracle rows run on an
# x86-64 host only.
# Usage: audit/round10/run-round10.sh
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
. "$root/scripts/lib/tmark.sh"
export PATH=/usr/local/go/bin:$PATH
R=audit/round10
J="$root/$R/bin/janus"; mkdir -p "$(dirname "$J")"
go build -o "$J" ./cmd/janus || exit 1
lake build Janus Janus.Tools.Audit janus-audit janus-decode janus-oracle-amd64 >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
[ -d artifacts/amd64/Box ] || bash scripts/build-examples-amd64.sh >/dev/null 2>&1
W=$R/work/rows; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-round10.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
for f in NewPair Insert Box; do
  mapfile -t tg < <(scripts/example-targets.sh "$f")
  "$J" extract artifacts/examples-arm64 "example.com/basic.$f" "$W/$f" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
done
mapfile -t tg < <(scripts/example-targets.sh MapAccess1Small)
"$J" extract artifacts/examples-arm64 runtime.mapaccess1_fast64 "$W/MapAccess1Small" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
broken=()
A=$R/attacks

# row NAME EXPECT [PATTERN...] on $out: EXPECT "blocked" (no Verified; patterns must appear) or
# "Verified" (Verified and every pattern).
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
  printf '  %-40s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
# check NAME OK-CONDITION-EXIT-STATUS MESSAGE
check() {
  if [ "$2" = 0 ]; then printf '  %-40s ok       %s\n' "$1" "$3"
  else printf '  %-40s FAILED   %s   <-- BROKEN\n' "$1" "$3"; broken+=("$1"); fi
}
v() { out="$("$J" verify --fresh --janus-root "$root" --proof "$1" "$2" ${3:+--theorem "$3"} 2>&1)"; }

echo "== V1: a runtime-contract hypothesis must quantify the runtime (auditor)"
type tmark >/dev/null 2>&1 && tmark "== V1: a runtime-contract hypothesis must quantify"
v $A/V1a_contract_H_true.lean "$W/NewPair";     row V1a_readiness_fun_true blocked 'round 10 V1' 'fun x x_1 x_2 x_3 => True'
v $A/V1b_contract_rt_nil.lean "$W/NewPair";     row V1b_runtime_ranges_nil blocked 'round 10 V1'
v $A/V1c_contract_rt_premise.lean "$W/NewPair"; row V1c_ranges_pinned_by_premise blocked 'round 10 V1' 'rt = []'
v $A/V1d_contract_unlinked.lean "$W/NewPair";   row V1d_contract_on_unlinked_prog blocked 'round 10 V1' 'Extracted.program.link impl'
v $A/V1e_iface_model_closed.lean "$W/NewPair";  row V1e_iface_model_R0 blocked 'round 10 V1' 'R0'
v $A/V1f_contract_in_precondition.lean "$W/NewPair"; row V1f_contract_in_precondition blocked 'round 10 V1'
v examples/proofs/NewPair.lean "$W/NewPair";    row V1_ctl_NewPair Verified 'RtReady'
v examples/proofs/MapAccess1Small.lean "$W/MapAccess1Small"; row V1_ctl_contract_in_conclusion Verified

echo "== V2: Assign/MakeSmall were unsatisfiable with MapModel.Laws (kernel-checked)"
type tmark >/dev/null 2>&1 && tmark "== V2: Assign/MakeSmall were unsatisfiable with Ma"
o="$(lake env lean $R/model/MapUnsat.lean 2>&1)"; check V2_model_pre_fix_contracts_unsat $? "old Assign and MakeSmall + Laws + one call state => False ${o:+($o)}"
lake env lean $R/model/MapUnsatFixed.lean >/dev/null 2>&1; rc=$?
[ $rc -ne 0 ]; check V2_model_fixed_contracts_unsat_attempt $? "the same chaining argument against the fixed contracts does not compile"
v $A/V2a_map_assign_vacuous.lean "$W/Insert";   row V2a_insert_stores_v_plus_1 blocked
v examples/proofs/Insert.lean "$W/Insert";      row V2_ctl_Insert Verified 'RtReady' 'rtView M.priv s.mem'
o="$(lake env lean $R/model/Arity.lean 2>&1)"; rc=$?; o="$(grep -i error <<<"$o" | head -3)"
check V2_V3_allocating_contracts_take_H $rc "Assign, MakeSmall, convT*, typeAssert, interfaceSwitch (both ISAs) take H : RtReady ${o:+($o)}"
v examples/proofs/Box.lean "$W/Box";            row V3_ctl_Box Verified 'RtReady'

echo "== SAT: witnesses (round 9 row, with the round-10 check that the witness names its contract)"
type tmark >/dev/null 2>&1 && tmark "== SAT: witnesses (round 9 row, with the round-10 "
o="$(python3 -I audit/round9/sat_check.py "$root")"; rc=$?
for c in "Assign                 Map.lean" "MakeSmall              Map.lean" "Assign                 MapAmd64.lean" "MakeSmall              MapAmd64.lean"; do
  grep -qF "SAT ok      $c" <<<"$o" || rc=1
done
check SAT_contract_witnesses $rc "$(tail -n 1 <<<"$o"); Assign/MakeSmall witnessed on both ISAs"
S9="$T/satcopy"; mkdir -p "$S9/audit/round9"; cp -r Janus Janus.lean "$S9/"; cp audit/round9/sat-pending.txt "$S9/audit/round9/"
python3 - "$S9/Janus/Contracts/MapSat.lean" <<'EOF'
import re, sys
p = sys.argv[1]; s = open(p).read()
s = re.sub(r"theorem assign_satisfiable :.*?:=\n", "theorem assign_satisfiable : True :=\n", s, count=1, flags=re.S)
open(p, "w").write(s)
EOF
python3 -I audit/round9/sat_check.py "$S9" >/dev/null 2>&1; rc=$?
[ $rc -ne 0 ]; check SAT_selftest_witness_must_name_contract $? "a theorem assign_satisfiable : True does not count as a witness"
# the check reads only the tree under test: a contract file linked in from elsewhere is an error
S10="$T/satlink"; mkdir -p "$S10/audit/round9" "$T/elsewhere"; cp -r Janus Janus.lean "$S10/"; cp audit/round9/sat-pending.txt "$S10/audit/round9/"
printf 'def EvilContract (p : Nat) : Prop :=\n  Summary p 0 (fun _ => True) (fun _ _ => True)\n' > "$T/elsewhere/Evil.lean"
ln -s "$T/elsewhere/Evil.lean" "$S10/Janus/Contracts/Evil.lean"
o="$(python3 -I audit/round9/sat_check.py "$S10" 2>&1)"; rc=$?
[ $rc -ne 0 ] && grep -q 'SAT ERROR.*Janus/Contracts/Evil.lean is not a regular file of the tree under test' <<<"$o"
check SAT_reads_only_the_tree_under_test $? "a Janus/Contracts file linked from outside the tree is refused: $(grep -m1 -o 'SAT ERROR.\{0,60\}' <<<"$o")"
o="$(python3 -I audit/round9/sat_check.py "$root" | head -1)"
[ "$o" = "SAT tree    $(cd "$root" && pwd -P) ($(git -C "$root" ls-files --cached --others --exclude-standard -- Janus Janus.lean | while read -r f; do [ -e "$f" ] && echo; done | wc -l) files)" ]
check SAT_scans_tracked_tree $? "$o"

echo "== real-runtime probes (audit/round10/probe; go1.26.0)"
type tmark >/dev/null 2>&1 && tmark "== real-runtime probes (audit/round10/probe; go1.2"
P="$T/probe"; mkdir -p "$P"
( cd $R/probe && export GOTOOLCHAIN=go1.26.0 CGO_ENABLED=0 &&
  GOARCH=amd64 GOAMD64=v1 go build -ldflags=-checklinkname=0 -trimpath -o "$P/p10-amd64" . &&
  GOARCH=arm64 go build -ldflags=-checklinkname=0 -trimpath -o "$P/p10-arm64" . ) || { echo "probe build failed"; exit 1; }
o1="$("$P/p10-amd64" tanil 200000)"; o2="$(qemu-aarch64 "$P/p10-arm64" tanil 200000)"
n1="$(sed -n 's/.*panicked=\([0-9]*\).*/\1/p' <<<"$o1")"; n2="$(sed -n 's/.*panicked=\([0-9]*\).*/\1/p' <<<"$o2")"
[ "${n1:-0}" -gt 0 ] && [ "${n2:-0}" -gt 0 ]
check I1a_typeassert_nil_faults $? "typeAssert(desc{CanFail}, nil): faults in ${n1:-?} (amd64) and ${n2:-?} (arm64) of 200000 calls"
o="$(lake env lean $R/model/TypeAssertNil.lean 2>&1)"; check I1b_contract_requires_non_nil_type $? "TypeAssert's precondition implies t ≠ 0 (both ISAs) ${o:+($o)}"
o1="$("$P/p10-amd64" convt 100000)"; o2="$(qemu-aarch64 "$P/p10-arm64" convt 100000)"
[ "$o1" = "CONVT static=256/256 fresh=100000/100000" ] && [ "$o2" = "$o1" ]
check V3a_convT64_allocates_per_call $? "convT64: $o1 (amd64), the same on arm64: every v >= 256 takes a fresh box"

echo "== A1: the ABI convention warning recognises linked programs"
type tmark >/dev/null 2>&1 && tmark "== A1: the ABI convention warning recognises linke"
o="$(go test -count=1 -run 'TestABIMismatch$' ./cmd/janus/ 2>&1)"; check A1_abi_warning_linked_program $? "$(tail -n 1 <<<"$o" | cut -c1-80)"

echo "== F1: an in-place framework build whose sources change while Lake runs is not stamped"
type tmark >/dev/null 2>&1 && tmark "== F1: an in-place framework build whose sources c"
o="$(go test -count=1 -run 'TestFrameworkSourcesChangeDuringBuild$' ./cmd/janus/ 2>&1)"; check F1_framework_sources_change_during_build $? "$(tail -n 1 <<<"$o" | cut -c1-80)"

echo "== G: cache eviction (holds)"
type tmark >/dev/null 2>&1 && tmark "== G: cache eviction (holds)"
G="$T/gc"; mkdir -m 700 "$G"; mkdir -m 700 "$G/cache"; mkdir -p "$G/victim/dir"; echo keep > "$G/victim/file"; echo keep > "$G/victim/dir/f"
for d in v1 v1/result v1/trusted v1/replay v1/framework v1/consumer v1/tmp v1/run v1/result/ab v1/consumer/fam v1/trusted/cd; do mkdir -p -m 700 "$G/cache/$d"; done
ln -s "$G/victim/file" "$G/cache/v1/result/ab/x.json"; ln -s "$G/victim/dir" "$G/cache/v1/consumer/fam/ws"
ln -s "$G/victim/dir" "$G/cache/v1/trusted/cd/key"; ln -s "$G/victim/dir" "$G/cache/v1/tmp/junk"
for l in $(find "$G/cache" -type l); do touch -h -d '3 days ago' "$l"; done
head -c 100000 /dev/urandom > "$G/cache/v1/result/ab/real.json"
o="$(JANUS_CACHE_DIR="$G/cache" "$J" cache gc --max 0 --grace 0s --all 2>&1)"
[ -f "$G/victim/file" ] && [ -f "$G/victim/dir/f" ] && [ -z "$(find "$G/cache" -type l)" ]
check G1_gc_removes_links_not_targets $? "planted links in result/consumer/trusted/tmp removed, their targets kept ($(tail -n 1 <<<"$o" | cut -c1-60))"
# collections that delete the temporary trees of a running verification (no grace, 0.036 s age)
( for i in $(seq 1 400); do JANUS_CACHE_TMP_HOURS=0.00001 "$J" cache gc --grace 0s --max off >/dev/null 2>&1; sleep 0.2; done ) &
gcpid=$!
out="$("$J" verify --janus-root "$root" --proof $A/V1a_contract_H_true.lean "$W/NewPair" 2>&1)"; row G2_attack_under_gc_hammer blocked
out="$("$J" verify --janus-root "$root" --proof examples/proofs/NewPair.lean "$W/NewPair" 2>&1)"
grep -qE '^(Verified|Cached: Verified|Invalid|Error)' <<<"$out"; check G2_ctl_verdict_under_gc_hammer $? "a verification with its run trees deleted ends with a verdict: $(grep -m1 -E '^(Verified|Cached|Invalid|Error)' <<<"$out" | cut -c1-70)"
kill "$gcpid" 2>/dev/null; wait "$gcpid" 2>/dev/null
v examples/proofs/NewPair.lean "$W/NewPair"; row G2_ctl_after_hammer Verified

echo "== holds: amd64 v3/SSE boundary encodings, arm64 crypto decode"
type tmark >/dev/null 2>&1 && tmark "== holds: amd64 v3/SSE boundary encodings, arm64 c"
if [ "$(uname -m)" = x86_64 ]; then
  O="$T/oracle"; mkdir -p "$O"
  ( cd oracle-amd64 && CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -buildmode=pie -o "$O/runner" ./cmd/runner &&
    CGO_ENABLED=0 go build -o "$O/oracle" ./cmd/oracle ) || { echo "oracle build failed"; exit 1; }
  { python3 -I $R/x86/genC.py 40 "$O/c.jsonl" && python3 -I $R/x86/genF.py 1 20000 "$O/f.jsonl" &&
    python3 -I $R/x86/genP.py 1 20000 "$O/p.jsonl"; } >/dev/null
  GODEBUG=asyncpreemptoff=1 "$O/oracle" run -runner "$O/runner" -model .lake/build/bin/janus-oracle-amd64 -j 8 \
    -cases "$O/c.jsonl,$O/f.jsonl,$O/p.jsonl" -out "$O/out" >/dev/null 2>&1
  mm="$(sed -n 's/^\*\*\([0-9]*\) MISMATCH\*\*.*/\1/p' "$O/out/summary.md")"
  nc="$(sed -n 's/^\([0-9]*\) cases in.*/\1/p' "$O/out/summary.md")"
  [ -n "$mm" ] && [ "$mm" = 0 ] && [ "${nc:-0}" -gt 40000 ]
  check X1_v3_sse_boundary_encodings $? "prefix/VEX/#UD/MXCSR/FMA boundary cases vs this CPU: ${nc:-?} cases, MISMATCH ${mm:-?}"
fi
o="$(python3 -I $R/crypto/decodecmp.py $R/crypto/clauses.json .lake/build/bin/janus-decode "$T" 2>&1)"
bad="$(grep -c '^BAD\|^GAP' "$T/decodecmp.txt" 2>/dev/null)"; words="$(sed -n 's/^words //p' "$T/decodecmp.txt" 2>/dev/null)"
[ "${words:-0}" -gt 2000000 ] && [ "${bad:-1}" = 0 ]
check C1_arm64_crypto_decode_vs_asl $? "janus-decode vs the sail-arm v9.4 decode clauses on ${words:-?} words of the SIMD/FP and register groups: ${bad:-?} disagreements"

echo "== holds: the ASL sqrt_real substitution (agent/asl, JanusASL/sail/fakereal_sqrt.py)"
type tmark >/dev/null 2>&1 && tmark "== holds: the ASL sqrt_real substitution (agent/as"
o="$(python3 -I $R/asl/half_only.py $R/asl 2>&1 | head -1)"
grep -q 'MISMATCHES 0 ' <<<"$o"; check ASL1_sqrt_real_half_exhaustive $? "$(cut -c1-60 <<<"$o")"
# single and double precision: python3 -I audit/round10/asl/sqrt_model.py 4000 (hours; see the doc)

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-10 rows as expected."
