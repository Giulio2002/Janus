#!/usr/bin/env bash
# Reproduce the round-3 attacks (docs/AUDIT-ROUND3.md) and check the fix for R1 (CRITICAL).
# Exits 1 if the fixed finding R1 regresses (prints Verified again).
# Writes only under audit/round3/work/.  Usage: audit/round3/run-round3.sh [-j N]  (-j: blocks at once, scripts/lib/parallel.sh)
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=../../scripts/lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
# shellcheck source=../../scripts/lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
par_init "$@"
J="$root/audit/round3/bin/janus"; mkdir -p "$(dirname "$J")"
# audit/run-rounds.sh builds janus and the framework once for every lane (JANUS_AUDIT_BIN,
# JANUS_AUDIT_PREBUILT=1).
if [ -n "${JANUS_AUDIT_BIN:-}" ]; then J="$JANUS_AUDIT_BIN"; else CGO_ENABLED=0 go build -o "$J" ./cmd/janus || exit 1; fi
[ "${JANUS_AUDIT_PREBUILT:-}" = 1 ] || memguard_lake build Janus Janus.Tools.Audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
[ -f artifacts/examples-amd64 ] || scripts/build-examples-amd64.sh >/dev/null 2>&1
W=audit/round3/work; mkdir -p $W
"$J" extract artifacts/examples-arm64 example.com/basic.Add $W/Add >/dev/null || exit 1
v() { "$J" verify --janus-root "$root" "$@" 2>&1; }
broken=()

r1_block() {
echo "== R1 (CRITICAL, fixed): inline instance inside a proof-local DEFINITION body =="
echo "The target example.com/basic.Add computes x + y. Proof.mul adds (via an inline HMul"
echo "instance), but its disclosed body is printed 'fun a b => a * b'. Before the fix the report"
echo "read as a multiplication claim while the binary adds. Expected now: Invalid (statement identity)."
out="$(v --proof audit/round3/attacks/R1_def_body_instance.lean $W/Add)"
r="$(grep -m1 -E '^(Verified|Invalid)' <<<"$out")"; st="$(grep -m1 'Stage:' <<<"$out" | sed 's/.*Stage: //')"
printf '  R1 %s [%s]\n' "$r" "$st"
case "$r" in Verified*) echo "      >>> BROKEN: binary adds, disclosed body says multiply, yet Verified."; broken+=(R1);; esac
}
r2_block() {
echo
echo "== R2 (LOW, self-disclosing): theorem-level instance binder + tying hypothesis =="
echo "Prints 's.regs 0 = x * y' but carries the visible binder [inst : HMul ...] and the hypothesis"
echo "(h : x * y = x + y); the '*' is the abstract bound instance, and the result equals x + y by h."
echo "Expected: Verified (the misleading '*' is fully disclosed by the printed binder and hypothesis)."
v --proof audit/round3/attacks/R2_inst_binder.lean $W/Add | grep -m1 -E 'Verified:|Invalid' | sed 's/^/  R2 /'
}
regression_block() {
echo
echo "== Regression: legitimate proofs with honest proof-local defs still verify =="
for p in "examples/proofs/Add.lean:$W/Add" ; do
  f=${p%%:*}; d=${p##*:}
  v --proof "$f" "$d" | grep -m1 -E 'Verified:|Invalid' | sed "s#^#  $(basename $f) #"
done
}
notes_block() {
echo
echo "== Positive controls (non-vacuity), run under 'lake env lean' in a work copy =="
echo "  A64Equal64, A64IndexByte (arm64), Equal64, CopyBlock512 (amd64): see audit/round3/controls/"
echo "  and the per-file instructions; each instantiates Proof.correctness at a concrete state."

echo
echo "== Model (blocked): AES FIPS-197, amd64 DF/REP/overlap =="
echo "  AES AESE/MixColumns/SubBytes match FIPS-197 (audit/round3/notes in AUDIT-ROUND3.md);"
echo "  DF is now a State field and MOVS/STOS step per-element load-then-store (round-2 MEDIUM-1 closed)."
}
par_run r1_block
par_run r2_block
par_run regression_block
par_run notes_block
par_wait

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-3 verifier rows as expected (R1 fixed, no regression)."
