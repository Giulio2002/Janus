Positive controls for round 3 (non-vacuity). Each proves a shipped example's precondition is
satisfiable by building a concrete call state and instantiating Proof.correctness, so the
theorem is not vacuous. All four were checked and compile cleanly.

Run (from a work copy; do not build inside the shared worktree):
  root=$(pwd); LP=$root/.lake/build/lib/lean; W=audit/round3/work; J=audit/round3/bin/janus
  CGO_ENABLED=0 go build -o $J ./cmd/janus; lake build Janus
  # arm64:
  for n in A64Equal64 A64IndexByte; do
    $J extract artifacts/examples-arm64 example.com/basic.$n $W/$n
    cp examples/proofs/$n.lean $W/$n/Proof.lean
    cp audit/round3/controls/${n}_witness.lean $W/$n/W.lean
    (cd $W/$n && LEAN_PATH=$LP:. lean --root=. -o Extracted.olean Extracted.lean
                 LEAN_PATH=$LP:. lean --root=. -o Proof.olean Proof.lean
                 LEAN_PATH=$LP:. lean --root=. W.lean && echo "$n witness OK")
  done
  # amd64 (Proof.lean is examples/proofs-amd64/<n>/Proof.lean):
  for n in Equal64 CopyBlock512; do
    $J extract artifacts/examples-amd64 example.com/basic.$n $W/$n
    cp examples/proofs-amd64/$n/Proof.lean $W/$n/Proof.lean
    cp audit/round3/controls/${n}_witness.lean $W/$n/W.lean
    (cd $W/$n && LEAN_PATH=$LP:. lean --root=. -o Extracted.olean Extracted.lean
                 LEAN_PATH=$LP:. lean --root=. -o Proof.olean Proof.lean
                 LEAN_PATH=$LP:. lean --root=. W.lean && echo "$n witness OK")
  done
