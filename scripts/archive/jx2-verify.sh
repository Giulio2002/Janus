#!/usr/bin/env bash
# jx2-verify.sh ISA Name [extra janus args]  : full verify of one example (correctness + witness), keeps workspace; prints time
set -u
root=/srv/janus-jx2; cd $root; export PATH=/usr/local/go/bin:$PATH JANUS_FRAMEWORK_STORE=/srv/janus-ops/fwstore
isa=$1; n=$2; shift 2
out=$root/.sw; mkdir -p $out/cache; export JANUS_CACHE_DIR=$out/cache
. scripts/example-contracts.sh
if [ $isa = arm64 ]; then proof=examples/proofs/$n.lean; art=$out/art/arm64-$n
  [ -d $art ] || { sym=$(example_symbol $n); mapfile -t tg < <(scripts/example-targets.sh $n); bin/janus extract artifacts/examples-arm64 "$sym" $art ${tg[@]+"${tg[@]}"} >/dev/null 2>&1; }
else proof=examples/proofs-amd64/$n/Proof.lean; art=artifacts/amd64/$n; fi
th=(--theorem Proof.correctness); grep -q '^namespace Witness' $proof && th+=(--theorem Proof.Witness.nonvacuous)
t0=$(date +%s)
HEAVY_PRIORITY=1 LEAN_NUM_THREADS=8 JANUS_JOBS=2 /srv/janus-ops/bin/heavy-run -- timeout 3000 memcap -m 24G bin/janus verify $art --proof $proof "${th[@]}" --janus-root $root --no-result-cache "$@" > $out/logs/full-$isa-$n.log 2>&1
echo "$isa $n rc=$? $(( $(date +%s)-t0 ))s $(grep -E '^Verified|^Invalid' $out/logs/full-$isa-$n.log | head -3 | cut -c1-200 | tr '\n' '|')"
