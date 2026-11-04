import Janus.Contracts.LiveSat

/-!
# Live runtime contracts, satisfied at a program's own contract addresses (arm64)

`LiveSat.lean` shows that the live contracts (`NewobjectLiveContract`, `MakesliceLiveContract`,
`MallocgcLiveContract`, `WbLiveContract`, …) are satisfiable, but only for the toy program
`toy.link (at0 code)` with the code at `A0`. A **Witness** for a theorem about an extracted
function `P` needs them for `P.link impl` at the addresses `P.contractAddr "runtime.newobject"`,
… So the stub code has to run where `P` says the runtime function is.

This file packages the proofs of `LiveSat` (the "D" toys: the allocation size is read from the
type descriptor, `64·size` bump advance; the write barrier returns `WBUF`) so a consumer states a
contract and calls one tactic:

```lean
def implAt : List Segment :=
  [LiveStub.newobjectSeg newA, LiveStub.wbSeg wbA]          -- code at the contract addresses
def R : RtInv := toyR [] ok                                  -- `ok`: the requests served
def linked : Program := Extracted.program.link implAt
theorem model_new : NewobjectLiveContract linked newA 4096 R := by janus_live_newobject
theorem model_wb  : WbLiveContract linked wbA 4096 R 1       := by janus_live_wb 1
```

`janus_live_*` expand to `intro; janus_run; exact (the LiveSat finishing lemma)`: the proof is an
ordinary kernel-checked proof of the contract statement by running the stub code; nothing here is
trusted and no axiom is added. The program must be a closed constant (a `def`, as above) so the
executor can evaluate its code; the stub must fit in the gap before the next function (the
contract addresses of `gcWriteBarrier1`/`2` are 16 bytes apart on arm64, `wbSeg` is 12 bytes).
The runtime is the toy bump allocator `toyR tys ok` of `LiveToy.lean` with `tys = []` (type
descriptors are read from memory, outside the runtime's own ranges).
-/

namespace Janus.Contracts.LiveStub

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat

/-- The stub code of `runtime.newobject` placed at `addr`. -/
def newobjectSeg (addr : Nat) : Segment := ⟨"live-stub.newobject", addr, newobjectCodeD⟩
/-- The stub code of `runtime.makeslice` placed at `addr`. -/
def makesliceSeg (addr : Nat) : Segment := ⟨"live-stub.makeslice", addr, makesliceCodeD⟩
/-- The stub code of `runtime.mallocgc` placed at `addr`. -/
def mallocgcSeg (addr : Nat) : Segment := ⟨"live-stub.mallocgc", addr, mallocgcCodeD⟩
/-- The stub code of `runtime.gcWriteBarrier{1,2,…}` placed at `addr`. -/
def wbSeg (addr : Nat) : Segment := ⟨"live-stub.gcWriteBarrier", addr, wbCode⟩

/-- The stub segments for every live allocation contract `P` lists (`runtime.newobject`,
`makeslice`, `mallocgc`, `gcWriteBarrier1`…`8`), each at its contract address. -/
def stubSegs (P : Program) : List Segment :=
  P.contracts.filterMap fun (n, a) =>
    if n = "runtime.newobject" then some (newobjectSeg a)
    else if n = "runtime.makeslice" then some (makesliceSeg a)
    else if n = "runtime.mallocgc" then some (mallocgcSeg a)
    else if (List.range 8).any (fun i => n = s!"runtime.gcWriteBarrier{i + 1}") then some (wbSeg a)
    else none

end Janus.Contracts.LiveStub

/-- Prove `NewobjectLiveContract linked a 4096 (toyR [] ok)` for `linked` with
`LiveStub.newobjectSeg a` linked in. -/
syntax "janus_live_newobject" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_newobject) => `(tactic| (
      intro L b s hpc pre
      have hacB' := Janus.Contracts.LiveSat.bump_acc pre.2.2.2.1
      have ⟨⟨h30a, h30b, hq1, hq2, hq3, hq4, hq5⟩, hq6, hq7⟩ := pre.1
      obtain ⟨hT1, hT2⟩ := hq6
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      exact Janus.Contracts.LiveSat.finish_newobjectD (by intro t ht; simp at ht) pre))

/-- `MakesliceLiveContract` against `LiveStub.makesliceSeg`. -/
syntax "janus_live_makeslice" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_makeslice) => `(tactic| (
      intro L b s hpc pre
      have hacB' := Janus.Contracts.LiveSat.bump_acc pre.2.2.2.1
      have ⟨⟨h30a, h30b, hq1, hq2, hq3, hq4, hq5⟩, hq6, hq7⟩ := pre.1
      obtain ⟨hT1, hT2⟩ := hq6
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      exact Janus.Contracts.LiveSat.finish_makesliceD (by intro t ht; simp at ht) pre))

/-- `MallocgcLiveContract` against `LiveStub.mallocgcSeg`. -/
syntax "janus_live_mallocgc" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_mallocgc) => `(tactic| (
      intro L b s hpc pre
      have hacB' := Janus.Contracts.LiveSat.bump_acc pre.2.2.2.1
      have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩ := pre.1
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      exact Janus.Contracts.LiveSat.finish_mallocgcD (by intro t ht; simp at ht) pre))

/-- `WbLiveContract linked a 4096 (toyR [] ok) n` against `LiveStub.wbSeg`, for `n ≤ 8` slots. -/
syntax "janus_live_wb " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_wb $n) => `(tactic| (
      intro L b s hpc pre
      have ⟨⟨h30a, h30b, _⟩, _⟩ := pre
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      have h := Janus.Contracts.LiveSat.wb_post (n := $n) (by intro t ht; simp at ht) (by omega)
        (b := b) (L := L) (s := s) pre.2.2.1 pre.2.2.2.2
      open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
        Janus.Contracts.LiveSat in
        simp only [wbFinal, wbRetX, apartAll_cons, apartAll_nil, and_true, Nat.reduceMul] at h
      exact h))
