import Extracted

/-!
Round 7, RC1: a sandboxed proof tries to reach the verification-result cache
(`$JANUS_CACHE_DIR/v1/result`): read its HMAC key, list the recorded entries, and plant a file
there. The sandbox mounts an empty tmpfs over that directory, so none of this reaches the real
cache. If the key or an entry were visible, the `#eval` fails and the proof does not compile
(the runner then marks the row BROKEN); a planted file must not appear on the host.
-/

#eval show IO Unit from do
  let home := (← IO.getEnv "HOME").getD "/root"
  let base := (← IO.getEnv "JANUS_CACHE_DIR").getD (home ++ "/.cache/janus")
  let dir : System.FilePath := base ++ "/v1/result"
  if ← (dir / ".key").pathExists then
    let k ← IO.FS.readBinFile (dir / ".key")
    throw <| IO.userError s!"RC1: the result cache key is visible to the proof ({k.size} bytes)"
  let entries ← try dir.readDir catch _ => pure #[]
  for e in entries do
    throw <| IO.userError s!"RC1: the result cache is visible to the proof ({e.fileName})"
  try IO.FS.writeFile (dir / "planted-by-proof") "forged" catch _ => pure ()

namespace Proof
theorem correctness : Extracted.entry = Extracted.entry := rfl
end Proof
