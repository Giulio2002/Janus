import Janus.Contracts.Live

/-!
# Live `runtime.convTstring` / `runtime.convT64` (arm64 and amd64)

The single-call `ConvTstring`/`ConvT64` (`Janus.Contracts.Iface`) need their own readiness `H` and an
`IfaceModel`, and hand the environment back without a budget, so they cannot sit on a path after live
calls (`growslice`, `mallocgc`, `memmove`). These are the live forms: two `RtSpec`s and two `LiveSpec`s
for `RtLiveContract`/`RtLiveContract64`, over the one `R : RtInv` that the other live contracts use. The
box is a new object when the call allocates (`convTstring` of a non-empty string, `convT64` of `v ≥ 256`);
otherwise it is a static object of the runtime (`&zeroVal`, `&staticuint64s[v]`), inside `R.rt`, so
nothing is added to the live set.

```lean
RtLiveContract p (contractAddr "runtime.convTstring") stack R convTstringSpec convTstringLive
RtLiveContract p (contractAddr "runtime.convT64")     stack R convT64Spec     convT64Live
```
-/

namespace Janus.Contracts

open Janus Janus.Arm64 Janus.Spec

/-- The box at `ptr` lies in the runtime's ranges `rt`, is readable, below `2^48`, and holds the words
`ws` (at `ptr`, `ptr + 8`, …): `BoxWords` over the runtime ranges of a live contract. -/
def BoxWords' (rt : List (Nat × Nat)) (m : Memory) (ptr : Nat) (ws : List Nat) : Prop :=
  ptr + 8 * ws.length ≤ 2 ^ 48 ∧ m.accessible ptr (8 * ws.length) false = true ∧
    InRanges ptr (8 * ws.length) rt ∧ ∀ i (h : i < ws.length), m.readLE (ptr + 8 * i) 8 = ws[i]

/-- The box at `ptr` lies in `rt`, is readable, below `2^48`, and holds the `n`-byte value `v`. -/
def BoxHolds' (rt : List (Nat × Nat)) (m : Memory) (ptr n v : Nat) : Prop :=
  ptr + n ≤ 2 ^ 48 ∧ m.accessible ptr n false = true ∧ InRanges ptr n rt ∧ m.readLE ptr n = v

/-- **`runtime.convTstring(s)`** (`X0 = ptr`, `X1 = len`; amd64 `RAX`, `RBX`): a box holding the string
header; the empty string's box is `&zeroVal[0]` (both words `0`). The string's bytes are not read. -/
def convTstringSpec : RtSpec where
  nargs := 2
  pre _ _ := True
  post rt a _ r0 _ _ m :=
    BoxWords' rt m r0 [if arg a 1 = 0 then 0 else arg a 0, arg a 1]

/-- `convTstring` allocates a 16-byte pointerful box (`mallocgc(16, stringType, false)`) unless the
string is empty; the box is a new object, the string's bytes stay the caller's own. -/
def convTstringLive : LiveSpec where
  cost a _ := if arg a 1 = 0 then 0 else blockSize 16 false
  fresh a _ r0 _ _ := if arg a 1 = 0 then [] else [(r0, r0 + 16)]

/-- **`runtime.convT64(v)`**: a box holding `v` (for `v < 256`, `&staticuint64s[v]`). -/
def convT64Spec : RtSpec where
  nargs := 1
  pre _ _ := True
  post rt a _ r0 _ _ m := BoxHolds' rt m r0 8 (arg a 0)

/-- `convT64` allocates a pointer-free 8-byte box (`mallocgc(8, uint64Type, false)`, the tiny
allocator) unless `v < 256`. -/
def convT64Live : LiveSpec where
  cost a _ := if arg a 0 < 256 then 0 else blockSize 8 true
  fresh a _ r0 _ _ := if arg a 0 < 256 then [] else [(r0, r0 + 8)]

/-- The allocating branches cost at least one byte (a chain of boxes is bounded by the budget). -/
theorem convTstringLive_cost_pos (a : List Nat) (m : Memory) (h : arg a 1 ≠ 0) :
    0 < convTstringLive.cost a m := by
  simp only [convTstringLive, if_neg h]; decide

theorem convT64Live_cost_pos (a : List Nat) (m : Memory) (h : ¬ arg a 0 < 256) :
    0 < convT64Live.cost a m := by
  simp only [convT64Live, if_neg h]; decide

/-- The static branches allocate nothing and add nothing to the live set. -/
theorem convTstringLive_empty (a : List Nat) (m : Memory) (r0 r1 r2 : Nat) (h : arg a 1 = 0) :
    convTstringLive.cost a m = 0 ∧ liveAdds convTstringLive a m r0 r1 r2 = [] := by
  have h' := h; simp [arg] at h'
  simp [convTstringLive, liveAdds, arg, h']

theorem convT64Live_small (a : List Nat) (m : Memory) (r0 r1 r2 : Nat) (h : arg a 0 < 256) :
    convT64Live.cost a m = 0 ∧ liveAdds convT64Live a m r0 r1 r2 = [] := by
  have h' := h; simp [arg] at h'
  simp [convT64Live, liveAdds, arg, h']

/-- The precondition of both boxing specs is `True`, and they read and write nothing besides `rt`: pre-lemmas (`↓`), so that a callee-precondition proof does not
first normalise the (large) call-site state in the argument words (the step budget of `janus64_run` ran out on the
third call of `examples/proofs-amd64/BoxAfterNew`). -/
@[janus_exec ↓, janus_post ↓, janus64_exec ↓, janus64_post ↓] theorem convTstringSpec_pre (a : List Nat) (m : Memory) :
    convTstringSpec.pre a m = True := eq_true trivial

@[janus_exec ↓, janus_post ↓, janus64_exec ↓, janus64_post ↓] theorem convT64Spec_pre (a : List Nat) (m : Memory) :
    convT64Spec.pre a m = True := eq_true trivial

@[janus_exec ↓, janus_post ↓, janus64_exec ↓, janus64_post ↓] theorem convTstringSpec_reads (a : List Nat) (m : Memory) :
    convTstringSpec.reads a m = [] := rfl

@[janus_exec ↓, janus_post ↓, janus64_exec ↓, janus64_post ↓] theorem convTstringSpec_writes (a : List Nat) (m : Memory) :
    convTstringSpec.writes a m = [] := rfl

@[janus_exec ↓, janus_post ↓, janus64_exec ↓, janus64_post ↓] theorem convT64Spec_reads (a : List Nat) (m : Memory) :
    convT64Spec.reads a m = [] := rfl

@[janus_exec ↓, janus_post ↓, janus64_exec ↓, janus64_post ↓] theorem convT64Spec_writes (a : List Nat) (m : Memory) :
    convT64Spec.writes a m = [] := rfl

/-- Closed forms of the argument words at the specs' own counts, as pre-lemmas (`↓`): the state in the argument is then never
visited. (`argWords64 s convT64Spec.nargs` is otherwise unfolded after its large call-site state argument has been simplified:
on the third live call of `examples/proofs-amd64/BoxAfterNew` the `R.ok addr (argWords64 …)` part of the callee
precondition took 200 s and ran out of the simp step budget; with these lemmas it takes 5 ms.) -/
@[janus_exec ↓, janus_post ↓] theorem argWords_convT64 (s : Janus.Arm64.State) :
    argWords s convT64Spec.nargs = [(s.regs 0).toNat] := rfl
@[janus_exec ↓, janus_post ↓] theorem argWords_convTstring (s : Janus.Arm64.State) :
    argWords s convTstringSpec.nargs = [(s.regs 0).toNat, (s.regs 1).toNat] := rfl
@[janus64_exec ↓, janus64_post ↓] theorem argWords64_convT64 (s : Janus.Amd64.State) :
    argWords64 s convT64Spec.nargs = [(s.regs 0).toNat] := rfl
@[janus64_exec ↓, janus64_post ↓] theorem argWords64_convTstring (s : Janus.Amd64.State) :
    argWords64 s convTstringSpec.nargs = [(s.regs 0).toNat, (s.regs 3).toNat] := rfl

attribute [janus_exec, janus_post, janus64_exec, janus64_post] convTstringSpec convT64Spec
  convTstringLive convT64Live BoxWords' BoxHolds'

end Janus.Contracts
