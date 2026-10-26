import Janus.Contracts.LiveToy
import Janus.Contracts.AllocSat

namespace Janus.Contracts.LiveSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy
open Janus.Contracts.AllocSat (toy A0 at0 link_at0)

def bumpCode (K : Nat) : List Nat := [0xd2a00809, 0xf9400120, 0x9100000a + K * 1024, 0xf900012a, 0xd65f03c0]

set_option maxRecDepth 20000 in
example (tys : Tys) (ok : Nat → List Nat → Prop) : NewobjectLiveContract (toy.link (at0 (bumpCode 16))) A0 (toyRt tys) 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, hroom, hok, hinv, hcost, hLs, hWs⟩ := pre
  janus_run
  trace_state
  sorry

end Janus.Contracts.LiveSat
