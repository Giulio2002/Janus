import Janus.Contracts.Misc

/-!
# Instrumented builds: coverage counters (both ISAs)

`go build -cover` (Go 1.20+ coverage, `cmd/cover` and `internal/coverage`) rewrites every
function of a covered package so that it starts by writing its **counter block** and then
bumps one counter per basic block it runs. The block is a slice of the package's counter
variable (a writable `[]uint32` in `.noptrbss`, listed by the linker between
`runtime.covctrs` and `runtime.ecovctrs`):

| word | contents | written |
| --- | --- | --- |
| `ctr[0]` | the number of counters `n` of the function | at every entry |
| `ctr[1]` | the package id, read from the package's `goCover_<hash>_P` variable | at every entry |
| `ctr[2]` | the function's index in the package | at every entry |
| `ctr[3 + i]` | the counter of basic block `i` | `-covermode=set`: `= 1`; `count`: `+= 1` (32-bit, wrapping); `atomic`: `atomic.AddUint32` |

All of this is ordinary code of the function itself (stores, no runtime call), so a theorem
about a covered function simply states the counter updates as part of its postcondition, with
the counter variable's bytes writable in its precondition (`CovBlock`). The registration of the
package's metadata (`runtime.addCovMeta`, in the package's `init`) and the writing of the
counter files at exit (`runtime/coverage`) happen outside the verified functions.

The other instrumentation modes are in `Janus.Contracts.InstrumentCalls` (`-d=checkptr`,
`-msan`, `-asan`) and docs/CLI.md ("Build modes").
-/

namespace Janus.Contracts.Instrument

open Janus Janus.Arm64 Janus.Spec

/-- Coverage counter word `i` of the block at `ctr` (32-bit little-endian). -/
def covWord (m : Memory) (ctr i : Nat) : Nat := m.readLE (ctr + 4 * i) 4

/-- The counter block at `ctr` holds the header `(cs.length, pkg, fn)` and the counters `cs`. -/
def CovBlock (m : Memory) (ctr pkg fn : Nat) (cs : List Nat) : Prop :=
  covWord m ctr 0 = cs.length ∧ covWord m ctr 1 = pkg ∧ covWord m ctr 2 = fn ∧
    ∀ i (h : i < cs.length), covWord m ctr (3 + i) = cs[i]

/-- A `-covermode=count` increment: `c + 1` wrapping at `2^32`. -/
def bump (c : Nat) : Nat := (c + 1) % 2 ^ 32

/-- The counters a run of a covered function leaves: `before` with the counters of the blocks
it ran (`ran i`) incremented once. -/
def bumped (before : List Nat) (ran : Nat → Bool) : List Nat :=
  (List.range before.length).map fun i => if ran i then bump (before.getD i 0) else before.getD i 0

theorem bumped_length (before : List Nat) (ran : Nat → Bool) :
    (bumped before ran).length = before.length := by simp [bumped]

/-- A block of three counters, word by word. -/
theorem CovBlock.mk3 {m : Memory} {ctr pkg fn c₀ c₁ c₂ : Nat} (h0 : covWord m ctr 0 = 3)
    (h1 : covWord m ctr 1 = pkg) (h2 : covWord m ctr 2 = fn) (h3 : covWord m ctr 3 = c₀)
    (h4 : covWord m ctr 4 = c₁) (h5 : covWord m ctr 5 = c₂) : CovBlock m ctr pkg fn [c₀, c₁, c₂] := by
  refine ⟨h0, h1, h2, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact h3
  | 1, _ => exact h4
  | 2, _ => exact h5

/-- `bumped` of three counters. -/
theorem bumped3 (c₀ c₁ c₂ : Nat) (ran : Nat → Bool) :
    bumped [c₀, c₁, c₂] ran = [if ran 0 then bump c₀ else c₀, if ran 1 then bump c₁ else c₁,
      if ran 2 then bump c₂ else c₂] := by
  simp [bumped, List.range_succ]

end Janus.Contracts.Instrument
