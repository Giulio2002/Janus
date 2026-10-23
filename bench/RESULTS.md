# Proof-automation benchmarks

`bench/go` is a small Go module of self-written functions, separate from `examples/basic`, so
that adding or changing a benchmark never moves an address an example proof mentions. Every
function is proved on both ISAs (`bench/proofs-arm64/<F>.lean`, `bench/proofs-amd64/<F>.lean`).
`scripts/bench.sh` builds the module for both ISAs (`GOAMD64=v1`), extracts the functions listed
in `bench/functions.txt`, and times each proof.

```sh
scripts/bench.sh                         # examples-arm64 examples-amd64 bench-arm64 bench-amd64
JOBS=3 scripts/bench.sh bench-arm64 bench-amd64
FILTER=Chain scripts/bench.sh bench-amd64
```

The time reported is the **CPU time** (user + system) of `lean` on the proof file against a
pre-compiled `Extracted.olean`: tactic execution plus kernel checking. Wall time is printed too,
but the machine these numbers come from was shared with other jobs (load average 15 to 70 on 48
cores), so only CPU time is comparable between runs. `janus verify` adds about 25 s per proof
(building, the axiom audit, `leanchecker`).

## The benchmarks

| function | what it stresses | arm64 | amd64 |
|---|---|---|---|
| `MulAdd8(z, x *[8]uint64, y, c)` | straight line: 8-limb multiply-add, carries | 92 instructions | 98 instructions |
| `MulAdd8x3(z0, z1, z2, x, y0, y1, y2)` | **~300-instruction** straight line: three 8-limb multiply-adds, 48 loads resolved past 24 stores | 268 instructions | 291 instructions |
| `Nested(n, m)` | doubly nested loop, nested induction over two loop heads | 16 instructions | 18 instructions |
| `Chain1(x)` → `Chain2` → … → `Chain5` | call chain **5 levels deep**, every level a callee `Summary` proved with the next level's summary (`calls [...]` on `ReachesRet` goals), memory frames (`MemFrame`, `janus_frame`) | 5 summaries | 5 summaries |
| `Alias4(a, b, c, d *uint64)` | **four possibly aliasing pointers**: 64 equal/disjoint combinations, 49 refuted by `omega`, 15 executed | 15 runs × 16 | 15 runs × 10 |
| `BigFrame(x, k)` | **large frame** (528 / 520 bytes, the big-frame stack-guard prologue), constant-count zeroing and fill loops unrolled (~400 instructions, ~100 stores in one memory chain), a load at a symbolic index split into 64 cases | ~400 instructions | ~390 instructions |

## Results (CPU seconds)

`before` is the automation at the start of this work (`main` before the changes) on the same
proof file. `—` means the old automation cannot run the proof: it has no `Summary` support on
amd64, no `janus64_simp`/`janus64_cases`/`janus_frame`, and on `BigFrame` (arm64) it stops with
`maximum recursion depth has been reached`.

| benchmark | arm64 before | arm64 after | amd64 after |
|---|---:|---:|---:|
| `MulAdd8` | 40.6 | 37.4 | 135.9 |
| `MulAdd8x3` | 126.7 | 121.5 | 843.9 |
| `Nested` | 2.1 | 1.9 | 6.2 |
| `Chain1` (5 levels) | — | 12.8 | 11.4 |
| `Alias4` (15 runs) | 26.2 | 18.9 | 25.2 |
| `BigFrame` | fails | 172.8 | 131.4 |

(Binaries built with Go 1.26.0, `JOBS=4`; the "before" column was measured with `JOBS=3` on the
same machine, so small differences are noise. The arithmetic-bound benchmarks barely move,
because their time is `omega` after the run, not the run.)

Where the time goes (from `-Dprofiler=true` / `-Dtrace.profiler=true`):

* **`MulAdd8`, `MulAdd8x3`.** Most of the time is the final `omega` on the carry arithmetic
  (24 products
  named as atoms with their bounds, and hundreds of nested `div`/`mod` terms), not the symbolic
  run. On amd64 the carry chains are longer (the `SBBQ`/`SUBQ` carry materialisation becomes
  `2^64 - (2^64-1)·[c]` terms), and the final arithmetic is correspondingly slower.
* **`BigFrame`.** The 400-instruction run takes about 20 s (arm64). The 64 index cases after it
  take about 50 s of tactic time, and checking their `omega` proofs (the disjointness of a
  stack slot from every earlier store) dominates the kernel time.
* **`Alias4`.** Each `omega` call in a side condition sees the six aliasing facts, so they are
  split into atomic `Nat` facts before the run.

## The examples, before and after

The same 31 proofs, run back to back on the same machine (`JOBS=4`), before and after the
changes. The four proofs added later on `main` (`AtomicAdd`, `AtomicMax`, `CopyBlock`,
`ClearWords`) have no "before" number in this run.

| proof | arm64 before | arm64 after | amd64 before | amd64 after |
|---|---:|---:|---:|---:|
| `Add` | 1.51 | 1.00 | 1.26 | 0.82 |
| `Max` | 1.57 | 0.90 | 1.08 | 0.90 |
| `Add128` | 1.82 | 0.79 | 1.66 | 1.00 |
| `Mul64` | 1.51 | 0.83 | 1.10 | 0.92 |
| `Add256` | 11.88 | 5.76 | 4.43 | 2.73 |
| `Div` | 3.69 | 1.85 | 7.68 | 6.51 |
| `Get` | 5.79 | 2.94 | 2.43 | 2.04 |
| `AddThree` | 4.03 | 2.18 | 10.18 | 2.19 (with summaries) |
| `Sum` | 3.14 | 1.72 | 1.97 | 1.87 |
| `SetOne256` | 2.09 | 1.13 | 1.33 | 1.15 |
| `HexDigit` | 2.60 | 1.44 | 6.75 | 6.35 |
| `AddLimbs` | 35.27 | 12.38 | 7.36 | 3.77 |
| `CopyWords` | 4.36 | 2.42 | 3.77 | 2.52 |
| `SumSquares` | 4.84 | 2.77 | 7.68 | 2.74 (with summaries) |
| `Table` | — | — | 4.99 | 4.36 |
| `GlobalTable` | — | — | 1.15 | 1.02 |
| `Bump` | — | — | 1.35 | 0.87 |
| **total** | **84.1** | **38.1** | **66.2** | **41.8** |

All 31 together go from 150 s to 80 s of CPU time. No proof got slower. On `main` with the new
proofs (`JOBS=6`, so a little slower), the four added proofs take 1.4 / 1.7 / 19.0 / 435 s on
arm64 and 1.4 / 2.0 / 15.3 / 92 s on amd64 (`AtomicAdd` / `AtomicMax` / `CopyBlock` /
`ClearWords`).

## What changed, and what each change bought

Found with these benchmarks and the profiler (`set_option trace.janus true` prints the time of
every step):

1. **No `whnf` of the goal.** `MVarId.apply` puts the target in weak head normal form to count
   the lemma's arguments. On `ExecThen p (if c then … else …) Q` that unfolds `ExecThen` and
   runs the decision procedure of the symbolic branch condition, down to `Memory.readLE` of the
   stack guard: 5 s for the one stack-guard branch of amd64 `AddThree` and `SumSquares` (and the
   old amd64 `goalKind` did the same `whnfR` on every goal). The step lemmas are now applied
   by unification only (`Common.applyFast`), and goal shapes are recognised syntactically.
   amd64 `AddThree` 10.2 s → 2.2 s, `SumSquares` 7.7 s → 2.7 s.
2. **The `simp` cache and context persist across steps** (keyed by the local context, so a new
   branch hypothesis starts a fresh cache). A symbolic state is mostly values that earlier steps
   already simplified; re-simplifying them made each step slower than the one before (in arm64
   `AddLimbs`, 11 ms for the first step, up to 100 ms per step at the end). Total `simp` time of
   `AddLimbs` 15.9 s → 8.7 s; `AddLimbs` 35 s → 12 s overall.
3. **Closed side conditions are evaluated**, not proved by `decide +kernel` (which added and
   kernel-checked one auxiliary declaration per side condition: about 10 per step, most of them
   `setReg_comm`'s `27 < 4` or a bitmask range, half of them false).
4. **Each pc is decoded and its `stepOK` fact proved once per run** (loops and branches revisit
   pcs).
5. **Reducible transparency for callee preconditions.** Closing them by `rfl`/`assumption` at
   default transparency unfolded `Memory.accessible` of a symbolic memory (3 s per call).
6. **Kernel-friendly normal forms.** `x + 2^64-k` is rewritten to `x - k` on amd64 as on arm64
   (`bv_add_neg64`): with the big literal in the state, the kernel unfolded `Nat.add` along it
   and the amd64 `BigFrame` proof failed with "deep recursion". Callee-saved registers reloaded
   from the stack (`setReg f r (s.regs r)`) are dropped from the register chain.
7. **Budgets instead of silent timeouts.** Not a speed-up, but every heartbeat timeout now says
   where the run was (see `docs/PROOFS.md`, *Troubleshooting*), which is how the expensive spots
   above were found.

Not done: `stepOK` facts are not cached across `janus_run` calls (`mkAuxLemma` already reuses an
identical lemma), and the simp sets were not split; the remaining per-step cost is mostly the
discharger's `omega` calls on large states.
