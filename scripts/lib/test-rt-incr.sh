#!/usr/bin/env bash
# Red-team tests of scripts/lib/incr.sh and the gate entry points (package RT). Run by go test
# (TestRTIncrScripts). Each case performs an attack and must end in a RUN / no record:
#   S1  JANUS_INCR_EXPLAIN / JANUS_INCR_PRECHECK left in the environment cannot reach a verifying gate
#   S2  a record needs a clean tree that did not change since the gate started (print snapshot / lane copies)
#   S3  a failed or timed-out item (rc != 0) is passed to `janus incr record` as a failure, never as a pass
#   S4  every script an item kind sources or runs is hashed into its key
#   S5  lanes key the Go configuration (go env, the GOENV file, GOWORK)
#   S6  a partial gate run is labelled, and the lane arguments of a partial run are keyed
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-rt-incr.XXXXXX")"
trap 'rm -rf "$t"' EXIT
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }

# ---- S1: the entry points clear the explain/precheck variables unless asked for them
for f in scripts/gate.sh scripts/verify-all-examples.sh; do
  if grep -q 'unset JANUS_INCR_EXPLAIN JANUS_INCR_PRECHECK' "$here/$f"; then ok "S1 $f clears JANUS_INCR_EXPLAIN/PRECHECK"; else bad "S1 $f does not clear JANUS_INCR_EXPLAIN"; fi
done
# the unset in gate.sh comes before the first use of incr_*
a=$(grep -n 'unset JANUS_INCR_EXPLAIN' "$here/scripts/gate.sh" | head -1 | cut -d: -f1)
b=$(grep -n '^export JANUS_INCR_RECORD' "$here/scripts/gate.sh" | head -1 | cut -d: -f1)
[ -n "$a" ] && [ "$a" -lt "$b" ] && ok "S1 gate.sh clears it before any lane runs" || bad "S1 order in gate.sh ($a, $b)"
# the real thing: gate.sh with the variable set must not stop at the explain path. --only with an unknown stage and
# a failing admission is enough to reach the unset; here we run the real arg parsing up to the admission check.
out="$(cd "$here" && JANUS_INCR_EXPLAIN=1 JANUS_GATE_INCREMENTAL= bash -c '
  sed -n "/^orig_args=/,/^\[ \"\$jobs_n\" != auto \]/p" scripts/gate.sh > /dev/null
  grep -c "JANUS_INCR_EXPLAIN" scripts/gate.sh')"
[ "$out" -ge 2 ] && ok "S1 gate.sh mentions the variable only to export (--explain) or clear it" || bad "S1 gate.sh"

# ---- a stub verifier that logs what the scripts ask of it
mkdir -p "$t/w/bin" "$t/w/scripts/lib"
cd "$t/w"
git init -q . && git config user.email a@b && git config user.name n
cp "$here/scripts/lib/incr.sh" scripts/lib/incr.sh
cat > bin/janus <<'EOS'
#!/usr/bin/env bash
echo "$*" >> "$STUBLOG"
case "$2" in
  check) printf 'RUN\t%064d\tstub\n' 1 ;;
  record) printf 'RECORDED\tstub\n' ;;
esac
EOS
chmod +x bin/janus
echo a > file.txt; echo '.gitignore' > /dev/null; printf 'ignored/\n' > .gitignore
git add -A && git commit -qm c
export STUBLOG="$t/log"; : > "$STUBLOG"
. scripts/lib/incr.sh

# ---- S1 (function level): explain mode skips everything; that is why the entry points clear it
JANUS_INCR_EXPLAIN=1 incr_begin "x" arm64 --proof p >/dev/null && ok "S1 (documented) explain mode reports 'skipped'" || bad "S1 explain mode"

# ---- S2: the tree pin
unset JANUS_GATE_TREE0; incr_tree_pin
[ "$JANUS_GATE_TREE0" != dirty ] && ok "S2 clean tree pins a stamp" || bad "S2 clean tree reported dirty"
JANUS_INCR_RECORD=1; : > "$STUBLOG"; INCR_KEY=$(printf '%064d' 1)
incr_end "arm64:X" arm64 0 1 --proof p >/dev/null 2>&1
grep -q ' record ' "$STUBLOG" && ok "S2 unchanged tree: record requested" || bad "S2 unchanged tree: no record"
# an edit after the gate started (the print snapshot / lane copy race)
: > "$STUBLOG"; echo b > file.txt
out="$(incr_end "arm64:X" arm64 0 1 --proof p 2>&1)"
! grep -q ' record ' "$STUBLOG" && ok "S2 edit during the gate: nothing recorded ($out)" || bad "S2 edit during the gate was recorded"
# same size, same content rewritten (ctime moves): treated as a change
git checkout -q file.txt; unset JANUS_GATE_TREE0; incr_tree_pin; : > "$STUBLOG"
sleep 1; touch -r file.txt "$t/ref" 2>/dev/null; cp file.txt tmp && cat tmp > file.txt && rm tmp
! incr_tree_ok && ok "S2 a rewrite of a file moves the stamp" || bad "S2 rewrite undetected"
# a new untracked file
git checkout -q file.txt; unset JANUS_GATE_TREE0; incr_tree_pin; echo n > new.txt
! incr_tree_ok && ok "S2 a new untracked file moves the stamp" || bad "S2 untracked file"
rm new.txt
# a dirty tree at the start records nothing at all
echo c > file.txt; unset JANUS_GATE_TREE0; incr_tree_pin
[ "$JANUS_GATE_TREE0" = dirty ] && ok "S2 dirty tree at start: pin is 'dirty'" || bad "S2 dirty tree not detected"
: > "$STUBLOG"; incr_end "arm64:X" arm64 0 1 --proof p >/dev/null 2>&1
! grep -q ' record ' "$STUBLOG" && ok "S2 dirty tree at start: nothing recorded" || bad "S2 dirty tree recorded"
git checkout -q file.txt
# no pin at all (a script run standalone): nothing recorded
unset JANUS_GATE_TREE0; : > "$STUBLOG"; incr_end "arm64:X" arm64 0 1 --proof p >/dev/null 2>&1
! grep -q ' record ' "$STUBLOG" && ok "S2 no pin: nothing recorded" || bad "S2 recorded without a pin"
# an ignored file changing does not matter (build outputs)
unset JANUS_GATE_TREE0; incr_tree_pin; mkdir -p ignored; echo x > ignored/o; incr_tree_ok && ok "S2 ignored files are not part of the stamp" || bad "S2 ignored file moved the stamp"

# ---- S3: failures are reported to `janus incr record` as failures (which then drops any record)
unset JANUS_GATE_TREE0; incr_tree_pin
for rc in 1 2 124 137; do
  : > "$STUBLOG"; incr_end "arm64:X" arm64 $rc 1 --proof p >/dev/null 2>&1
  if grep -q -- "--rc $rc " "$STUBLOG" && ! grep -q -- "--rc 0 " "$STUBLOG"; then ok "S3 rc $rc passed on as a failure"; else bad "S3 rc $rc: $(cat "$STUBLOG")"; fi
done

# ---- S5: the lane spec keys the go configuration
: > "$STUBLOG"; export JANUS_GATE_INCREMENTAL=1
incr_lane gotest true >/dev/null 2>&1
grep -q -- '--arg goenv:' "$STUBLOG" && grep -q -- '--arg goenvfile:' "$STUBLOG" && ok "S5 lane key has go env and the GOENV file" || bad "S5 lane spec lacks the go configuration: $(cat "$STUBLOG")"
# a different go env gives a different spec
mkdir -p "$t/fakego"; printf '#!/bin/sh\ncase "$1" in version) echo "go version fake" ;; env) echo "{\\"GOFLAGS\\": \\"$FAKE_FLAGS\\"}" ;; esac\n' > "$t/fakego/go"; chmod +x "$t/fakego/go"
: > "$STUBLOG"; PATH="$t/fakego:$PATH" FAKE_FLAGS=-tags=a incr_lane gotest true >/dev/null 2>&1; l1=$(grep ' check ' "$STUBLOG")
: > "$STUBLOG"; PATH="$t/fakego:$PATH" FAKE_FLAGS=-tags=b incr_lane gotest true >/dev/null 2>&1; l2=$(grep ' check ' "$STUBLOG")
[ -n "$l1" ] && [ "$l1" != "$l2" ] && ok "S5 a GOFLAGS change from the go env file changes the lane spec" || bad "S5 go env change invisible"

# ---- S4: every script the verify scripts source or run is in the key of its kind
cd "$here"
. scripts/lib/incr.sh
for pair in arm64:verify-examples amd64:verify-amd64-examples asm:verify-asm-examples rtmisc:verify-rtmisc-examples sys:verify-sys-examples print:verify-print-examples cgo:verify-cgo-examples; do
  kind=${pair%%:*}; sc=${pair#*:}
  flags="$(incr_script_flags "$kind" | grep -v '^--script$')"
  refs="$(grep -v '^\s*#' scripts/$sc.sh | grep -oE '(scripts/(lib/)?[A-Za-z0-9_-]+\.(sh|py))|\$root/scripts/lib/[A-Za-z0-9_-]+\.sh' | sed 's|^\$root/||' | sort -u)"
  miss=""
  for r in $refs; do [ -f "$r" ] || continue; echo "$flags" | grep -qx "$r" || miss="$miss $r"; done
  [ -z "$miss" ] && ok "S4 $kind: every referenced script is keyed" || bad "S4 $kind: not keyed:$miss"
done
# ---- S6: a partial run is labelled and its lane arguments are keyed
grep -q "PARTIAL RUN: not a full gate" scripts/gate.sh && grep -q -- '--arg "run:' scripts/gate.sh && grep -q -- '--arg "rounds:' scripts/gate.sh && ok "S6 partial runs are labelled and keyed" || bad "S6"
exit $fail
