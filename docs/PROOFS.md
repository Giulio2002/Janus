# Writing proofs

This guide shows how to state and prove a theorem about a compiled Go function with Janus,
using the proof automation in `Janus/Tactic` and the specification vocabulary in
`Janus/Spec`. Every proof in `examples/proofs/` is verified end to end by
`scripts/verify-examples.sh`; they are the reference examples for each technique below.

Nothing in the automation is trusted. The tactics only build proofs, and the Lean kernel checks
them (`janus verify` replays them with `leanchecker`). A tactic bug can make a proof fail. It
cannot make a false theorem verify. What you must get right is the **statement**: see
[SOUNDNESS.md](SOUNDNESS.md).

## The workflow

```sh
go build -o bin/janus ./cmd/janus
scripts/build-examples.sh                                   # artifacts/examples-arm64
bin/janus extract artifacts/examples-arm64 example.com/basic.Add artifacts/Add
bin/janus verify artifacts/Add --proof examples/proofs/Add.lean
```

The proof file imports `Extracted` (the generated `Extracted.lean`, which imports `Janus`) and
declares `theorem Proof.correctness`. While writing a proof, compile it against the extraction
directly to see goals:

```sh
mkdir -p /tmp/b && LEAN_PATH=/tmp/b lake env lean -o /tmp/b/Extracted.olean artifacts/Add/Extracted.lean
LEAN_PATH=/tmp/b lake env lean examples/proofs/Add.lean
```

Look at the disassembly first (`aarch64-linux-gnu-objdump -d artifacts/examples-arm64`,
or `janus list`): it tells you the stack footprint, whether there is a stack-growth prologue,
which runtime stubs are reachable, and where loop heads are.

## Walkthrough: `Add`

`func Add(x, y uint64) uint64 { return x + y }` compiles to `add x0, x0, x1; ret`.

```lean
import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
```

**The statement.** `GoABI.Ensures p entry args pre post` says: for every admissible return
address `ret` (`GoABI.RetAddr p ret`: 4-aligned, below `2^48`, outside the extracted code and
the stubs) and every machine state `s` that is a Go call of `entry` with integer arguments
`args` in `X0, X1, …` and `ret` in `X30` (`GoABI.CallSetup (p.withExit ret)`) and satisfies
`pre s`, the program returns to `ret` after finitely many instructions, restores `SP`, `X18`,
`X28` and `X29` (`GoABI.ABIReturn`), and `post s s'` holds of the final state `s'`. Everything
not mentioned (other registers, flags, `SP`, all of memory) is arbitrary. Faults (an
undecodable word, a memory access outside the caller's regions, a jump outside the extracted
code) and panics are not returns, so `Ensures` rules them out. Quantifying over `ret` means
that only a branch to the caller's `X30` counts as a return (see SOUNDNESS.md).

**The proof.**

1. `intro ret hret s hs _` takes an arbitrary return address `ret` with `hret : RetAddr p ret`,
   an arbitrary call state `s`, the `CallSetup` hypothesis and the precondition.
2. `janus_intro hs` turns `hs` into rewrite rules the executor uses:
   `h_pc : s.pc = 602304#64`, `h_lr : s.regs 30 = BitVec.ofNat 64 ret` and
   `h_x0 : s.regs 0 = x`, `h_x1 : s.regs 1 = y`.
3. `janus_run` turns `Ensures`/`Returns` into the goal `Reaches p s Q` and executes:
   * at `pc = 0x930c0` it fetches the word `0x8b010000`, decodes it (`add x0, x0, x1`) and
     proves "this address is ordinary code holding this word, and it decodes to this
     instruction" as one Boolean fact checked by the kernel;
   * it simplifies `exec (add …) s` to the next symbolic state
     `{ regs := setReg s.regs 0 (x + y), pc := 602308#64, … }`;
   * `ret` jumps to `s.regs 30 = BitVec.ofNat 64 ret`. The executor sees that the symbolic pc is
     the return address and the goal becomes the postcondition of the final state, which
     `janus_run` simplifies with the `janus_post` simp set. Here that closes it: `ABIReturn` holds because `SP`, `X18`, `X28`, `X29` are untouched,
     and `(x + y).toNat = (x.toNat + y.toNat) % 2^64`.

That is the whole proof. Most straight-line functions need nothing more, or a final
`janus_arith` (`omega` with range facts) for the arithmetic left over.

## Tactics

| Tactic | What it does |
|---|---|
| `janus_intro hs` | From `hs : CallSetup p entry [a₀, …] s`: `h_pc`, `h_lr`, `h_x<i> : s.regs i = aᵢ` (literal addresses; `h_lr : s.regs 30 = BitVec.ofNat 64 ret` for `p = p₀.withExit ret`). |
| `janus_run [lemmas]` | Symbolic execution until every branch reaches the exit address (goal: the postcondition), a stub (goal: `Q` of the stub outcome, e.g. `False` for `Returns`), or the return address (`ReachesRet`). Works on `Returns`, `Panics`, `GrowsStack`, `Reaches`, `ReachesRet`. Extra `lemmas` are added to the simp set of every step. |
| `janus_run until [a, …]` | Stop (without executing) when a branch arrives at one of the addresses. The starting state is always stepped. Used at loop heads. |
| `janus_run calls [h, …]` | Use callee summaries `h : Summary p entry pre post` at calls to `entry` instead of executing the callee. |
| `janus_step [lemmas]` | Exactly one instruction. |
| `janus_simp [lemmas]` | The post-processing simp set `janus_post` plus the state hypotheses and `lemmas`. Closes invariant side goals (`S'.regs 2 = i + 1`, …). |
| `janus_arith` | `omega` after adding `readLE m a n < 256^n` for every memory read, and normalising carry terms. For the arithmetic left after execution. Does nothing if there is no goal. |
| `janus_data hd` | From `hd : p.DataLoaded m`: readability of each `.rodata` object, and a rewrite rule that evaluates loads from it at literal addresses. |
| `janus_cases h` | From `h : k < N` (`N` a literal): `N` goals with `k` replaced by `0, …, N-1`. For table lookups at a symbolic index. |
| `janus_disch` | The discharger used inside every simp call (see below). |

`set_option trace.janus true in janus_run` prints every step (pc, decoded instruction, simp time),
every branch condition, and the time spent on final goals.

### Return addresses

Goals about a call are stated on `p.withExit ret` with `ret` a variable, and the context must
contain `hret : RetAddr p ret` (it comes from `intro ret hret …`, or is a hypothesis of a loop
lemma). The executor then

* evaluates the program facts (`stepOK`, `stubOK`) on the closed program `p`, as before, and
  derives `pc ≠ ret` from `hret` (`RetAddr.ne_of_fetch`: there is no code at `ret`;
  `RetAddr.ne_of_stubAt`: no stub). No arithmetic is involved, so this costs nothing per step;
* installs the rewrite rules `(BitVec.ofNat 64 ret).toNat = ret`, `ret % 2^64 = ret`,
  `(ret % 4 = 0) = True` and `(2^56 ≤ ret) = False`, which evaluate the checks of `ret`
  (`branchReg`) on the return address. They are rewrite rules rather than hypotheses so that
  `omega` does not see an extra `%` term in every side condition;
* recognises the return when the symbolic pc is `BitVec.ofNat 64 ret` (or a literal equal to a
  concrete `ret`).

Callee summaries are proved on the extracted program and moved to `p.withExit ret` by
`Summary.withExit` automatically.

### How a step works, and what the goals look like

**The symbolic state** is `State.mk regs sp pc flags mem` with

* `regs` a chain `setReg (setReg s.regs 1 v₁) 3 v₃`: sorted by register number, each register at
  most once, so a read `S.regs 3` simplifies to `v₃` and `S.regs 28` to `s.regs 28`;
* `pc` a literal `602308#64`;
* `flags` the flags of the last flag-setting instruction, e.g. `(addSub x y true).snd` after
  `cmp x, y`, kept opaque;
* `mem` a chain `(s.mem.writeLE a 8 v).writeLE b 8 w` of stores;
* `vregs` (the SIMD&FP registers) a chain `setVReg (setVReg s.vregs 0 v₀) 4 v₄`, like `regs`.

**Values** are `BitVec 64` terms over the initial registers (rewritten to your argument names) and
memory reads `BitVec.ofNat 64 (s.mem.readLE a 8)`. **Addresses** are normalised to `Nat`:
`(x + 8#64).toNat` becomes `x.toNat + 8` when `omega` shows it does not wrap; `sp - 16` becomes
`s.sp.toNat - 16` when `16 ≤ s.sp.toNat`. **Reads after writes** are resolved by `omega`: a read
whose range is disjoint from a write skips it, a read at the same address returns the stored value.

**Branch conditions** become arithmetic: after `cmp x, y`, `b.hs` is `y.toNat ≤ x.toNat`,
`b.lt` is `x.toInt < y.toInt` (and `x.toNat < y.toNat` when both are below `2^63`), `cbz x` is
`x.toNat = 0`. At a branch `janus_run` splits the goal and adds the condition as a hypothesis
`hbr` (`¬ …` on the other side). A side whose condition contradicts the hypotheses (by `omega`)
is dropped immediately: preconditions like `y ≠ 0` or `i < len` prune the panic paths.

**Side conditions** of the simp lemmas are proved by `janus_disch`:

* closed goals (`3 ≠ 31`, literal comparisons) by kernel evaluation (`decide +kernel`) only;
* `m.accessible a n w = true` from a hypothesis `m.accessible b k w' = true` about the same
  memory (after stripping writes, and anything tagged `janus_acc`), with `b ≤ a`,
  `a + n ≤ b + k` by `omega`;
* everything else by `omega` (which knows `x.toNat < 2^64` for every 64-bit `x`), after an
  arithmetic normalisation if needed.

So **the hypotheses you need are the arithmetic facts about addresses and the accessibility facts
about regions**, stated with `toNat` on the argument variables. Destructure the spec predicates
(`Ptr`, `StackOK`, `GuardOK`, `Disjoint`, …) into hypotheses before `janus_run`
(`intro s hs ⟨⟨hz, hz'⟩, …⟩`, `simp only [Disjoint] at *`).

**When a step gets stuck**, `janus_run` stops with

```text
janus: could not evaluate the instruction to `.ok s'` or a branch (…); stuck at
  match load s.mem ((x.toNat + 8) % 18446744073709551616) 8 with …
```

The printed term shows what is missing. Here, `x.toNat + 8 < 2^64` could not be proved, so the
precondition lacks `x.toNat + 32 ≤ 2^48` (part of `Ptr`).
A `load`/`store` that stays unevaluated means an
`accessible` fact is missing. A `readLE (writeLE …)` means the aliasing of two addresses is
unknown.

## Specification vocabulary (`Janus.Spec`)

| Name | Meaning |
|---|---|
| `Ptr m p n w` | `n` bytes at `p` lie in one region of `m` (writable if `w`, then overlapping no read-only region), and `p + n ≤ 2^48`. `Ptr32` for `n = 32`. |
| `Disjoint p n q k`, `Disjoint32 p q` | The byte ranges do not overlap. |
| `Aliasing p q` | `p = q ∨ Disjoint32 p.toNat q.toNat`: what two Go `*[4]uint64` can be. |
| `OnlyWrites m m' p n` | `m'` equals `m` outside `[p, p+n)`, same regions. `Unchanged m m'`. |
| `val256 m p`, `limb m p i` | The 32 bytes at `p` little-endian (`= Σ limbᵢ·2^(64i)`, `val256_limbs`). |
| `toInt256`, `ofInt256` | Two's complement. |
| `sumWords m p n` | Sum of the `n` words at `p`. |
| `copyWords m dst src i` | `m` after copying the first `i` words (a copy loop's memory). |
| `StackOK s below above` | `SP` 16-aligned, `[SP-below, SP+above)` writable, below `2^48`. |
| `GuardOK s adj` | The stack-growth prologue falls through (`= GoABI.StackGuardOK`). |

The outcome predicates (`Janus.GoABI`): `Returns`, `Panics` (a panic stub), `Faults` (a fault
other than running out of fuel), `NeverPanics` (no panic stub and no fault), `GrowsStack`; the
contract `Ensures` / `EnsuresResults`; `RetAddr p ret` (an admissible return address;
`RetAddr.of_check (by decide)` proves it for a concrete `ret`).

The goal predicates (`Janus.Tactic`): `Reaches p s Q` (the run ends in an outcome satisfying
`Q`; `IsReturn post`, `IsPanic`, `IsMorestack`), `ReachesRet p ret s Q` (ordinary steps reach
`pc = ret`, for callees) and `Summary p entry pre post` (a callee contract).

## Techniques

### Memory and aliasing (`Add256`, `AddLimbs`)

State aliasing as "equal or disjoint" and split on it before running. In each case the read and
write addresses become comparable by `omega`:

```lean
  rcases hzx with rfl | hzx <;> rcases hzy with rfl | hzy <;> rcases hxy with h | hxy
  all_goals try subst h
  all_goals simp only [Disjoint] at *
  all_goals first | (exfalso; omega) | (janus_run; janus_arith)
```

Inconsistent combinations (`z = x`, `z = y`, `x` disjoint from `y`) are closed by `omega`. The
postcondition uses the values **before** the call (`val256 s.mem x.toNat`), so the theorem
covers `z.Add(z, z)`.

### Stack frames, the stack-growth prologue and panics (`Div`, `Get`)

A function with a frame begins with `ldr x16, [x28, #16]; cmp sp, x16; b.ls morestack`.
`GuardOK s 0` (or `GuardOK s k` for the `sub x17, sp, #k` form) makes the prologue fall
through: its `b.ls` branch is pruned. Read the stack footprint off the disassembly.
`str x30, [sp, #-16]!; stur x29, [sp, #-8]` touches `[SP-24, SP)`, and spills like
`str x0, [sp, #24]` (after the push) touch the caller's frame above `SP`. Then require
`StackOK s 24 16` or the like. Buffers the function reads must be disjoint from that window.

A theorem that is not an `Ensures` states the return address itself: take `(ret : Nat)
(hret : RetAddr Extracted.program ret)` and `hs : CallSetup (Extracted.program.withExit ret) …`,
and conclude `Returns (Extracted.program.withExit ret) s …` or `Panics (…withExit ret) s` (see
`Div.lean`, `Get.lean`). For panics, prove `Panics p s` with `janus_run` (the path ends at the
stub), and combine "panics iff" from both directions with `Returns.not_panics`:

```lean
  refine ⟨⟨fun hp => ?_, hpan⟩, hret⟩
  by_cases hy : y = 0
  · exact hy
  · exact absurd hp (hret hy).not_panics
```

### Loops (`Sum`, `CopyWords`, `JanusTests/Tactic.lean`)

1. Find the loop head in the disassembly (for Go: the `cmp` before the backward branch) and name
   it relative to the entry: `abbrev head : Nat := Extracted.entry + 0x1c`.
2. State the invariant at the head as a lemma about an arbitrary state `S`, by equations on its
   components, quantified over the number `n` of iterations left:

   ```lean
   theorem loop … : ∀ n (S : State) (i acc : BitVec 64), i.toNat + n = len.toNat →
       S.pc = BitVec.ofNat 64 head → S.regs 2 = i → S.regs 3 = acc →
       acc.toNat = sumWords s.mem ptr.toNat i.toNat % 2 ^ 64 → … →
       S.regs 30 = BitVec.ofNat 64 ret → …
       S.mem = s.mem.writeLE (s.sp.toNat + 8) 8 ptr.toNat →
       Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧ post)
   ```

   with `(ret : Nat) (hret : RetAddr Extracted.program ret)` among the lemma's parameters.

   Equations `S.regs k = v`, `S.pc = …`, `S.sp = …`, `S.mem = …` are used as rewrite rules by
   `janus_run`, so executing from the opaque `S` works like executing from the call state. Give
   the memory **exactly**, as a write chain or a recursive model such as `copyWords`.
3. Prove it by `induction n`. In each case `janus_run until [head]` executes one iteration (or
   the exit). Back at the head, `apply ih _ (i + 1#64) (acc + …)` and close the invariant
   obligations with `janus_simp` and `omega`.
4. In the main theorem, `janus_run until [head]` runs the prologue, then `exact loop … _ 0#64 0#64`
   with each equation closed by `janus_simp`.

A loop with a constant trip count needs none of this. The counter is a literal in every
iteration, so `janus_run` simply executes it (`AddLimbs`).

### Calls (`AddThree`, `SumSquares`)

Prove the callee once, from any state at its entry, as a `Summary`:

```lean
theorem add_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.Add")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56)
      (fun s s' => s' = { s with regs := setReg s.regs 0 (s.regs 0 + s.regs 1),
                                 pc := s.regs 30 }) := by
  intro s hpc ⟨h1, h2⟩
  janus_run
```

and use it with `janus_run calls [add_summary]`. At a `bl` to the callee, `janus_run` proves the
precondition for the current state, substitutes the postcondition if it is an equation
`s' = …` (otherwise it splits it into hypotheses) and continues after the call. The return
address must be well formed (`ret` checks it). Without `calls`, `janus_run` executes the callee
inline, which also works.

### Read-only data (`SetOne256`, `HexDigit`)

The extractor copies the `.rodata` objects the code loads into `Extracted.program.data`. Require
`Extracted.program.DataLoaded s.mem` and call `janus_data hd`. Loads from literal addresses then
evaluate to the bytes from the binary. For a load at a symbolic index (`t[i & 15]`), run first,
then split on the index:

```lean
  janus_run
  generalize hk : i.toNat % 16 = k
  have hlt : k < 16 := hk ▸ Nat.mod_lt _ (by decide)
  janus_cases hlt
  all_goals janus_simp [hexDigit]
```

### Atomics, writable globals and runtime memory routines (`AtomicAdd`, `AtomicMax`, `CopyBlock`, `ClearWords`)

`Janus/Tactic/Atomic.lean` adds the `exec` equations for the ordered, exclusive and LSE atomic
instructions, `PRFM`, `CLREX`, `MRS DCZID_EL0` and `DC ZVA` (see `docs/SOUNDNESS.md` for their
model). An alignment check of an atomic access is a branch (`p.toNat % 8 = 0`), pruned by a
precondition.

* **Writable globals named by the code.** `sync/atomic` tests `runtime.arm64HasATOMICS` and
  memclr caches the `DC ZVA` block size in `block_size`. The extractor does not copy writable
  data, so the precondition states the bytes at the address the code computes.
  `Spec.adrpLdTarget pc w1 w2 scale` recomputes that address from the extracted `ADRP` and
  `LDR` words (`segWord p name i`), so the statement contains no hand-copied literal.
  `janus_eval_nat h : c` evaluates such a closed constant and adds `h : c = <numeral>`, proved by
  `decide`. Rewrite with it before `janus_run`, so that `omega` sees the same literal the
  executor computes.
* **LSE vs LL/SC.** Preconditions select the LSE path (`readLE hasAtomics 1 % 2 = 1`). The
  store-exclusive fallback is undecodable, so it must be unreachable from `pre`.
* **Implementation-defined parameters.** `ClearWords` holds for every `State.dczid`. It splits
  on the 32 values with one theorem per value (`CaseStmt k`), so that Lean elaborates them in
  parallel, and it combines them with `janus_cases`. Long hardware loops (32 `DC ZVA`s of 4-byte
  blocks) go through an induction lemma (`zva_loop`) instead of straight-line execution. Zeroed
  ranges are tracked with interval lemmas (`ZeroOn`, `zeroOn_writeLE_zero`) rather than byte by
  byte.

### SIMD code (`A64Equal64`, `A64IndexByte`)

`Janus/Tactic/Vector.lean` adds the `exec` equations of the Advanced SIMD and SIMD&FP load/store
instructions, the V register normal form (`setVReg`, sorted like `setReg`) and element lemmas.
The vector operations themselves (`threeSameOp`, `acrossOp`, `twoMiscOp`, `ofElems`, `elem`, ...)
are **not** unfolded: after `ld1 {v0.2d-v3.2d}, [x0]` and `cmeq v8.2d, v4.2d, v0.2d`, register
`V8` holds `threeSameOp true 3 17 128 (readLE (b + 0) 16) (readLE a 16) 0`. What the code reads
back is evaluated by element lemmas tagged `janus_exec`: `elem_cmeq` (a CMEQ lane is all ones iff
the lanes are equal), `elem_and`/`elem_or`, `elem_readLE_64`/`elem_readLE_8` (a lane of a load is a
smaller load), `elem_ofElems`, `elem_mod_2_128`. So `umov x4, v8.d[0]` followed by `cbz x4`
branches on `readLE (b + 48) 8 = readLE (a + 48) 8 ∧ … ∧ readLE b 8 = readLE a 8` directly
(`A64Equal64.lean`; `readLE_64_eq_iff` turns the eight words back into the 64-byte
comparison).

When the code computes something less direct, state the fact once as a lemma whose left side is
the term the executor produces, and rewrite the branch hypotheses and the final goal with it.
`A64IndexByte.lean` does this for `internal/bytealg.IndexByteString`: `loopTest` (the
`ORR`/`ADDP .2D`/`UMOV` test is zero iff no byte of the 32-byte block matches) and `syndrome`
(`AND` with `0x40100401` and two `ADDP .16B` give `Σ 4^i·[byte i = c]`), proved by expanding
every lane to its bytes (`elem_64_bytes`), pushing the masks into `if`s (`ite_land_nat`,
`ite_add_ite_mod`, `ite4_mod`), turning each `if p then k else 0` into `k * (decide p).toNat`
(`ite_eq_mul_toNat`) and closing the linear identity with `omega`. The byte-mask arithmetic is in
`Janus.Tactic.Vector`: `synd`/`ctzN_synd`/`clzNat_rbitNat` (RBIT + CLZ find the first match),
`maskSum_add_mod` (two vectors of `0x00`/`0xFF` bytes add to `0 mod 2^64` only if both are zero),
`firstTrue`. Name the branch hypotheses (`rename_i`) instead of `‹_›`: an anonymous assumption
with metavariables is unified against every hypothesis, and these are large.

### Counterexamples (`WrongAdd`)

`scripts/break-demo.sh` changes `x + y` to `x - y` in a copy of the Go source, rebuilds,
re-extracts, and checks that `examples/proofs/Add.lean` is now **rejected**. It then verifies
`examples/proofs/WrongAdd.lean` on the broken binary: the negation of the spec, proved by running
one concrete call (built with `GoABI.setup`, with the concrete return address `0x1000`, shown
admissible by `RetAddr.of_check (by decide)`) and comparing its result with what the spec claims
(`Returns.unique`).

## Performance

Each instruction costs one `simp` call on the instruction and the current state (10 to 50 ms) plus
one kernel evaluation. Measured on the examples:

| Proof | Instructions executed | Time |
|---|---|---|
| `JanusTests.Tactic.straight_spec` | 51 | 2.6 s (`lean` on the test file) |
| `examples/proofs/Add256.lean` | 17 in each of 5 aliasing cases | 6 s (`lean`), 20 s (`janus verify`) |
| `examples/proofs/AddLimbs.lean` | 72 in each of 5 aliasing cases | 21 s (`lean`), 33 s (`janus verify`) |

(`janus verify` adds about 10 s for building, the axiom audit and `leanchecker`, more on a loaded
machine.) Tips:

* Keep facts about the initial state as equations on `s.regs i`, `s.pc`, `s.sp`, `s.mem`; they are
  the rewrite rules.
* Split cases (aliasing, table indices) as late as possible. Each case re-executes the code.
* Large extractions (the `seg<i>` form) cost nothing extra. The program is evaluated once per
  `janus_run`, and fetches are checked by the kernel.

## Extending the automation

* New memory models (like `copyWords`): prove `regions`/`accessible` frame lemmas and tag them
  `janus_exec, janus_post, janus_acc`. Prove read lemmas and tag them `janus_exec, janus_post`.
* Lemmas used only at the end: tag them `janus_post`, or pass them to `janus_simp [...]`.
* Avoid permutation lemmas (simp's ordering check is exponential on the shared terms of a
  symbolic state); see `setReg_comm`.
* Do not let the kernel evaluate `BitVec.signExtend` or `&&&` on projections of a literal state by
  `rfl`. State them as `Nat` arithmetic (see `sext64_eq`, `exec_adr`).
