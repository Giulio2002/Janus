#!/usr/bin/env bash
# jx1_do.sh FUNC Name arm64|amd64...: regenerate (from committed file) and verify
cd /srv/janus-jx1; f=$1; n=$2; shift 2
for i in "$@"; do
  if [ $i = arm64 ]; then p=examples/proofs/$n.lean; else p=examples/proofs-amd64/$n/Proof.lean; fi
  git checkout -q HEAD -- $p
  (cd scripts && python3 -c "import jx1_iface as I; I.$f('$i')") || exit 1
  scripts/archive/jx1-verify.sh $i $n
  grep -m1 -A14 "Lean errors" .sw/logs/full-$i-$n.log | cut -c1-400
  grep -m1 -o "Invalid: The audit.\{0,700\}" .sw/logs/full-$i-$n.log
done
