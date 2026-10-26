#!/usr/bin/env bash
# Self-test of scripts/lib/theorems.sh (verify_theorems), with a stub `bin/janus` that checks its
# extraction directory exists before and after a delay (as `janus verify` re-checks the artifacts
# at its end) and that the relative binary path in identity.json resolves. Run by go test
# (TestTheoremsLib). Everything happens in a mktemp directory.
#   1. two items with three theorems each, verified concurrently: every theorem passes, each extra
#      theorem ran in a copy of its own (unique name), and no copy is left behind;
#   2. a second run on the same extraction while the first holds it fails at once, loudly (every
#      theorem marked failed with the lock message), and the first run is not disturbed.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-theorems.XXXXXX")"
trap 'rm -rf "$t"' EXIT
cd "$t"
mkdir -p bin artifacts
cat > bin/janus <<'EOF'
#!/usr/bin/env bash
# stub: janus verify DIR --proof P --theorem T
dir=$2; thm=$6
[ -f "$dir/identity.json" ] || { echo "Invalid: $dir/identity.json does not exist"; exit 1; }
bin=$(sed -n 's/^  "binary": "\(.*\)",$/\1/p' "$dir/identity.json")
[ -f "$dir/$bin" ] || { echo "Invalid: binary $dir/$bin missing"; exit 1; }
sleep "${STUB_SLEEP:-0.5}"
[ -f "$dir/identity.json" ] || { echo "Invalid: Artifacts changed during verification: $dir/identity.json does not exist"; exit 1; }
echo "$dir" >> "${STUB_DIRS:?}"
echo "{\"theorem\":\"$thm\"}" > "$dir/verified.json"
echo "Verified: $thm"
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
[ "$(sort -u "$STUB_DIRS" | wc -l)" = 6 ] && ok "each theorem ran in a directory of its own" || bad "shared directories: $(sort "$STUB_DIRS" | uniq -d)"
[ -z "$(ls -A artifacts | grep '^\.thm-' || true)" ] && ok "no copy is left behind" || bad "leftover copies: $(ls -A artifacts)"
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
[ $fail = 0 ] && echo "all checks passed"
exit $fail
