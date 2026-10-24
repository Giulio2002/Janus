Positive controls for round-2. Each proves a shipped example's precondition is satisfiable
(non-vacuous) by building a concrete state and instantiating `Proof.correctness`.

To run (from a copy of the repo; do not build inside the shared worktree):
  cp -a <repo> /tmp/j && cd /tmp/j
  lake build Janus
  W=audit/round2/work; mkdir -p $W/AtomicAdd $W/CopyBlock
  bin/janus extract artifacts/examples-arm64 example.com/basic.AtomicAdd $W/AtomicAdd
  bin/janus extract artifacts/examples-arm64 example.com/basic.CopyBlock $W/CopyBlock
  for n in AtomicAdd CopyBlock; do
    LP=$PWD/.lake/build/lib/lean
    cp examples/proofs/$n.lean $W/$n/Proof.lean
    (cd $W/$n && LEAN_PATH=$LP:. lean --root=. -o Extracted.olean Extracted.lean
                 LEAN_PATH=$LP:. lean --root=. -o Proof.olean Proof.lean
                 cp ../../controls/${n}_witness.lean W.lean
                 LEAN_PATH=$LP:. lean --root=. W.lean && echo "$n witness OK")
  done
