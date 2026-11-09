#!/usr/bin/env bash
# Self-test of scripts/lib/theorems.sh (verify_theorems), with a stub `bin/janus` that checks its
# extraction directory exists before and after a delay (as `janus verify` re-checks the artifacts
# at its end) and that the relative binary path in identity.json resolves, and that takes every
# theorem in ONE run and writes the --results file as the real one does. Run by go test
# (TestTheoremsLib). Everything happens in a mktemp directory.
#   1. two items with three theorems each, verified concurrently: every theorem passes, the stub
#      ran once per item (one run for all its theorems), and each theorem's log holds its own block;
#   2. a second run on the same extraction while the first holds it fails at once, loudly (every
#      theorem marked failed with the lock message), and the first run is not disturbed;
#   3. one theorem failing in the run fails exactly that theorem (rc and log), the others pass;
#   4. a run that exits 0 but writes no results file passes nothing; a results file claiming a
#      verified theorem of another name does not pass this one.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-theorems.XXXXXX")"
trap 'rm -rf "$t"' EXIT
cd "$t"
mkdir -p bin artifacts
cat > bin/janus <<'EOF'
#!/usr/bin/env bash
# stub: janus verify DIR --proof P --theorem T... --results FILE
dir=$2; shift 2
thms=(); res=""
while [ $# -gt 0 ]; do
  case "$1" in
    --theorem) thms+=("$2"); shift 2 ;;
    --results) res=$2; shift 2 ;;
    *) shift ;;
  esac
done
[ -f "$dir/identity.json" ] || { echo "Invalid: $dir/identity.json does not exist"; exit 1; }
bin=$(sed -n 's/^  "binary": "\(.*\)",$/\1/p' "$dir/identity.json")
[ -f "$dir/$bin" ] || { echo "Invalid: binary $dir/$bin missing"; exit 1; }
sleep "${STUB_SLEEP:-0.5}"
[ -f "$dir/identity.json" ] || { echo "Invalid: Artifacts changed during verification: $dir/identity.json does not exist"; exit 1; }
echo "$dir ${thms[*]}" >> "${STUB_DIRS:?}"
echo "stub preamble line"
rc=0; items=""
for thm in "${thms[@]}"; do
  if [ "$thm" = "${FAIL_THM:-}" ]; then
    echo "=== $thm: FAILED ==="; echo "Invalid: boom in $thm"; rc=1
    items="$items{\"theorem\":\"$thm\",\"status\":\"failed\"},"
  else
    echo "=== $thm: verified ==="; echo "Verified: $thm"; echo "  Axioms: propext"
    items="$items{\"theorem\":\"${CLAIM_THM:-$thm}\",\"status\":\"verified\"},"
  fi
done
echo "{\"theorem\":\"${thms[0]}\"}" > "$dir/verified.json"
[ -n "${STUB_NORESULTS:-}" ] || echo "{\"schema\":1,\"results\":[${items%,}]}" > "$res"
exit $rc
EOF
chmod +x bin/janus
echo binary > artifacts/examples
for n in A B; do
  mkdir -p "artifacts/$n"
  printf '{\n  "binary": "../examples",\n  "symbol": "%s"\n}\n' "$n" > "artifacts/$n/identity.json"
  echo "-- $n" > "artifacts/$n/Extracted.lean"
done
# shellcheck source=theorems.sh
. "$here/theorems.sh"
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }
thms=(Proof.correctness Proof.Witness.nonvacuous Proof.Witness.returns)
export STUB_DIRS="$t/dirs"; : > "$STUB_DIRS"

# 1. two items at once
mkdir -p sA sB
( verify_theorems artifacts/A proof.lean sA "${thms[@]}" ) & pa=$!
( verify_theorems artifacts/B proof.lean sB "${thms[@]}" ) & pb=$!
wait $pa $pb || true
all=0
for s in sA sB; do for i in 0 1 2; do [ "$(cat $s/$i.rc)" = 0 ] || { all=1; cat "$s/$i.log"; }; done; done
[ $all = 0 ] && ok "two items with three theorems each, verified concurrently: all pass" || bad "a theorem failed"
[ "$(wc -l < "$STUB_DIRS")" = 2 ] && ok "one run per item (all its theorems in it)" || bad "runs: $(cat "$STUB_DIRS")"
{ grep -q 'Verified: Proof.Witness.nonvacuous' sA/1.log && ! grep -q 'Verified: Proof.correctness' sA/1.log && grep -q 'Axioms: propext' sA/2.log; } &&
  ok "each theorem's log holds its own block" || bad "log split: $(cat sA/1.log)"
grep -q 'Proof.correctness' artifacts/A/verified.json && ok "the item's own directory keeps its correctness report" || bad "artifacts/A/verified.json: $(cat artifacts/A/verified.json)"

# 2. a second run on the same extraction while the first holds it
mkdir -p s1 s2
( STUB_SLEEP=3 verify_theorems artifacts/A proof.lean s1 "${thms[@]}" ) & p1=$!
sleep 1
rc=0; verify_theorems artifacts/A proof.lean s2 "${thms[@]}" 2> s2.err || rc=$?
wait $p1 || true
[ $rc != 0 ] && grep -q "in use by another run" s2.err && [ "$(cat s2/0.rc)" != 0 ] && [ "$(cat s2/2.rc)" != 0 ] &&
  grep -q "refusing to race" s2/1.log && ok "a concurrent second run on the same extraction fails at once, loudly" ||
  bad "second run: rc $rc, $(cat s2.err 2>/dev/null) $(cat s2/*.rc 2>/dev/null | tr '\n' ' ')"
[ "$(cat s1/0.rc) $(cat s1/1.rc) $(cat s1/2.rc)" = "0 0 0" ] && ok "the first run is not disturbed" || bad "the first run failed: $(cat s1/*.log)"

# 3. one theorem fails: exactly that one
mkdir -p s3
FAIL_THM=Proof.Witness.nonvacuous verify_theorems artifacts/A proof.lean s3 "${thms[@]}" || true
{ [ "$(cat s3/0.rc)" = 0 ] && [ "$(cat s3/1.rc)" != 0 ] && [ "$(cat s3/2.rc)" = 0 ]; } &&
  grep -q 'boom in Proof.Witness.nonvacuous' s3/1.log && ! grep -q 'boom' s3/0.log s3/2.log && grep -q 'Verified: Proof.Witness.returns' s3/2.log &&
  ok "a failing theorem fails alone and does not mask the others" || bad "failure isolation: $(cat s3/*.rc | tr '\n' ' ')"
mkdir -p s3b
FAIL_THM=Proof.correctness verify_theorems artifacts/A proof.lean s3b "${thms[@]}" || true
{ [ "$(cat s3b/0.rc)" != 0 ] && [ "$(cat s3b/1.rc)" = 0 ] && [ "$(cat s3b/2.rc)" = 0 ]; } &&
  ok "a failing first theorem does not fail the others" || bad "first failing: $(cat s3b/*.rc | tr '\n' ' ')"

# 4. no results file, or one that names another theorem: nothing passes
mkdir -p s4 s5
STUB_NORESULTS=1 verify_theorems artifacts/A proof.lean s4 "${thms[@]}" || true
[ "$(cat s4/0.rc s4/1.rc s4/2.rc | grep -vc '^0$')" = 3 ] && ok "exit 0 without a results file passes no theorem" || bad "no results file: $(cat s4/*.rc | tr '\n' ' ')"
CLAIM_THM=Other.name verify_theorems artifacts/A proof.lean s5 Proof.correctness || true
[ "$(cat s5/0.rc)" != 0 ] && ok "a results file naming another theorem does not pass this one" || bad "claimed: $(cat s5/0.rc)"
[ $fail = 0 ] && echo "all checks passed"
exit $fail
