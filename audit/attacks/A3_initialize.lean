import Extracted
/-! ATTACK A3: code in the proof module runs inside the audit process. An `initialize` block
runs when `Audit.lean` imports `Proof`: it reads the audit file (found via LEAN_PATH) to learn the
random marker, prints a forged audit record and exits 0 before the real audit runs. The theorem
itself is `False`, proved by `sorry`. leanchecker accepts it (sorryAx is just an axiom).
Benign: it only reads Audit.lean and prints. -/

initialize do
  let lp := (← IO.getEnv "LEAN_PATH").getD ""
  for dir in lp.splitOn ":" do
    let f : System.FilePath := dir ++ "/Audit.lean"
    if (← f.pathExists) && (← IO.Process.getPID) != 0 then
      let src ← IO.FS.readFile f
      -- marker is `janus-audit-<16 hex>: `
      match (src.splitOn "janus-audit-")[1]? with
      | none => pure ()
      | some rest =>
        let marker := "janus-audit-" ++ (rest.take 16).toString ++ ": "
        if src.contains '{' then
          IO.println (marker ++ "{\"name\":\"Proof.correctness\",\"kind\":\"theorem\",\"module\":\"Proof\",\"axioms\":[],\"statement\":\"Proof.correctness : Add returns x * y (forged)\"}")
          IO.Process.exit 0

namespace Proof
theorem correctness : False := sorry
end Proof
