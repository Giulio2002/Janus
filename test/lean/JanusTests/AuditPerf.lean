import Janus.Tools.Audit
import Janus  -- build-order edge: the #eval below imports `Janus` at elaboration time

/-!
# The auditor's whole-environment passes stay linear (regression)

`Environment.header.moduleNames` rebuilds the array of every module name on EACH call. The data-symbol
identity pass (`JanusAudit.checkDataSymIdentities`) called it once per constant of the environment
(hundreds of thousands, in a few hundred modules): the audit of a tiny proof took ~9 s instead of ~1.5 s.
This builds the environment the auditor sees for any proof (`Janus` and its closure) and requires the
pass to finish quickly.
-/

open Lean

#eval show IO Unit from do
  let env ← importModules #[{ module := `Janus }] {} (loadExts := false)
  let t0 ← IO.monoMsNow
  match ← (JanusAudit.checkDataSymIdentities env).run with
  | .error _ => throw (IO.userError "checkDataSymIdentities rejected the plain framework environment")
  | .ok () => pure ()
  let dt := (← IO.monoMsNow) - t0
  if dt > 3000 then
    throw (IO.userError s!"checkDataSymIdentities took {dt} ms on the framework environment (it must be linear in the number of constants)")
