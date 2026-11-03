import Janus.Contracts.LiveSatAmd64
import Janus.Contracts.LiveStub

/-!
# Live runtime contracts, satisfied at a program's own contract addresses (amd64)

The amd64 twin of `LiveStub.lean`: stub segments (`newobjectSeg`, `makesliceSeg`, `mallocgcSeg`,
`wbSeg`) and the tactics `janus64_live_newobject`, `janus64_live_makeslice`,
`janus64_live_mallocgc`, `janus64_live_wb n`, each proving the corresponding `…LiveContract64`
of `linked = P.link [stub segments]` (a closed constant) with the toy runtime
`toyR [] ok`. See `LiveStub.lean` for the recipe.
-/

namespace Janus.Contracts.LiveStubAmd64

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64

def newobjectSeg (addr : Nat) : Janus.Amd64.Segment := ⟨"live-stub.newobject", addr, newobjectCodeD⟩
def makesliceSeg (addr : Nat) : Janus.Amd64.Segment := ⟨"live-stub.makeslice", addr, makesliceCodeD⟩
def mallocgcSeg (addr : Nat) : Janus.Amd64.Segment := ⟨"live-stub.mallocgc", addr, mallocgcCodeD⟩
def wbSeg (addr : Nat) : Janus.Amd64.Segment := ⟨"live-stub.gcWriteBarrier", addr, wbCode⟩

/-- The stub segments for every live allocation contract `P` lists, each at its contract address
(as `LiveStub.stubSegs`). -/
def stubSegs (P : Janus.Amd64.Program) : List Janus.Amd64.Segment :=
  P.contracts.filterMap fun (n, a) =>
    if n = "runtime.newobject" then some (newobjectSeg a)
    else if n = "runtime.makeslice" then some (makesliceSeg a)
    else if n = "runtime.mallocgc" then some (mallocgcSeg a)
    else if (List.range 8).any (fun i => n = s!"runtime.gcWriteBarrier{i + 1}") then some (wbSeg a)
    else none

end Janus.Contracts.LiveStubAmd64

syntax "janus64_live_newobject" : tactic
macro_rules
  | `(tactic| janus64_live_newobject) => `(tactic| (
      intro L b s hpc pre
      have hacB' := Janus.Contracts.LiveSat.bump_acc pre.2.2.2.1
      have ⟨⟨hra, hal, h3, h4, h5⟩, hq6, hq7⟩ := pre.1
      obtain ⟨hT1, hT2⟩ := hq6
      have hap := Janus.Contracts.LiveSatAmd64.bump_apart64 pre.2.2.2.2.2.2
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 in
        exact finish_newobjectD (by intro t ht; simp at ht) _ (by simp [retAddrOf]) (by simp [setRegF])
          (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl
          (by simp [setRegF, BUMP]) (by simp [BUMP]) pre))

syntax "janus64_live_makeslice" : tactic
macro_rules
  | `(tactic| janus64_live_makeslice) => `(tactic| (
      intro L b s hpc pre
      have hacB' := Janus.Contracts.LiveSat.bump_acc pre.2.2.2.1
      have ⟨⟨hra, hal, h3, h4, h5⟩, hq6, hq7⟩ := pre.1
      obtain ⟨hT1, hT2⟩ := hq6
      have hap := Janus.Contracts.LiveSatAmd64.bump_apart64 pre.2.2.2.2.2.2
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 in
        exact finish_makesliceD (by intro t ht; simp at ht) _ (by simp [retAddrOf]) (by simp [setRegF])
          (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl
          (by simp [setRegF, BUMP]) (by simp [BUMP]) pre))

syntax "janus64_live_mallocgc" : tactic
macro_rules
  | `(tactic| janus64_live_mallocgc) => `(tactic| (
      intro L b s hpc pre
      have hacB' := Janus.Contracts.LiveSat.bump_acc pre.2.2.2.1
      have ⟨⟨hra, hal, h3, h4, h5⟩, hq6, hq7⟩ := pre.1
      have hap := Janus.Contracts.LiveSatAmd64.bump_apart64 pre.2.2.2.2.2.2
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 in
        exact finish_mallocgcD (by intro t ht; simp at ht) _ (by simp [retAddrOf]) (by simp [setRegF])
          (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl
          (by simp [setRegF, BUMP]) (by simp [BUMP]) pre))

syntax "janus64_live_wb " term : tactic
macro_rules
  | `(tactic| janus64_live_wb $n) => `(tactic| (
      intro L b s hpc pre
      have ⟨hra, hal, h3, h4, h5⟩ := pre.1
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 in
        exact wb_post64 (n := $n) (by intro t ht; simp at ht) (by omega) pre.2.2.1 pre.2.2.2.2
          (by simp [retAddrOf])
          (by intro i; simp only [setRegF]; by_cases h4 : i = 4 <;> by_cases h11 : i = 11 <;> simp [h4, h11])
          (by simp) rfl rfl (by simp) rfl rfl rfl))
