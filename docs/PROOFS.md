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
| `janus_run calls [h, …]` | Use callee summaries `h : Summary p entry pre post` at calls to `entry` instead of executing the callee. Also inside a callee's own proof (`ReachesRet` goals), so summaries compose through call chains. |
| `janus_run (budget := N)` | Limit the run to `N` thousand heartbeats (the unit of `maxHeartbeats`), counted from its start. However the run ends, a timeout is reported as an error naming the pc, the instruction and the phase (see Troubleshooting). `(budget := N)` may also come first: `janus_run (budget := N) until [...]`. |
| `janus_step [lemmas]` | Exactly one instruction (`calls`/`budget` as for `janus_run`). |
| `janus_simp [lemmas]` | The post-processing simp set `janus_post` plus the state hypotheses and `lemmas`. Closes invariant side goals (`S'.regs 2 = i + 1`, …). |
| `janus_arith` | `omega` after adding `readLE m a n < 256^n` for every memory read, and normalising carry terms. For the arithmetic left after execution. Does nothing if there is no goal. |
| `janus_data hd` | From `hd : p.DataLoaded m`: readability of each `.rodata` object, and a rewrite rule that evaluates loads from it at literal addresses. |
| `janus_dyn h₁ h₂ …` | From dynamic-call hypotheses (`ItabIs`, `FuncvalIs`, `ClosureCtx`): the itab's literal address and words, the funcval's code word, the captured variables, as equations the executors use (both ISAs). See [Dynamic calls](#dynamic-calls-hashwith-hashtwice-mapsum-deferadd). |
| `janus_cases h` | From `h : k < N` (`N` a literal): `N` goals with `k` replaced by `0, …, N-1`. For table lookups at a symbolic index. |
| `janus_frame` | Proves `MemFrame m₀ m rs` (the memory part of a callee summary, see Calls): peels the stores of `m`, goes through the `MemFrame` hypotheses of called summaries, side conditions by `omega`. |
| `janus_eval% t` | A term: the closed natural number `t` (e.g. `segAddr Extracted.program "f" + 8`) evaluated to a numeral at elaboration time, for a lemma argument that must be a literal. |
| `janus_disch` | The discharger used inside every simp call (see below). |

`set_option trace.janus true in janus_run` prints every step (pc, the instruction disassembled,
simp time), every branch condition, and the time spent on final goals. The disassembler
(`Janus.Arm64.Disasm.disasm`, `Janus.Amd64.Disasm.disasm`) prints GNU/Intel syntax with branch
targets resolved; constructors it does not know (new instructions) print as their `Repr`.

**Addresses.** Proofs never contain addresses copied from a disassembly: they name everything
relative to the extraction, so adding a function to the Go package does not break them. Use
`Extracted.entry + off` for a loop head (`off` from `objdump`, relative to the function, so it
only changes when the function's own code changes) and `segAddr Extracted.program "pkg.f"` for a
callee's entry; `janus_run until [...]` and the state equations evaluate such closed terms.

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

* closed goals (`3 ≠ 31`, `Nat.blt c 2^64 = true`, literal comparisons) by evaluating the
  literals at tactic time (proof `of_decide_eq_true rfl`, checked by the kernel with the rest of
  the proof), and anything else closed by `decide +kernel`; a closed goal that is false is
  never proved from the hypotheses;
* `m.accessible a n w = true` from a hypothesis `m.accessible b k w' = true` about the same
  memory (after stripping writes, callee frames `MemFrame`, and anything tagged `janus_acc`),
  with `b ≤ a`, `a + n ≤ b + k` by `omega`;
* `Outside a n rs` (the side condition of a `MemFrame` read) by unfolding the ranges and `omega`;
* everything else by `omega` (which knows `x.toNat < 2^64` for every 64-bit `x`), after an
  arithmetic normalisation if needed.

So **the hypotheses you need are the arithmetic facts about addresses and the accessibility facts
about regions**, stated with `toNat` on the argument variables. Destructure the spec predicates
(`Ptr`, `StackOK`, `GuardOK`, `Disjoint`, …) into hypotheses before `janus_run`
(`intro s hs ⟨⟨hz, hz'⟩, …⟩`, `simp only [Disjoint] at *`).

**When a step gets stuck**, `janus_run` stops with an error that says where and why; see
[Troubleshooting](#troubleshooting) for the messages and what to do about each.

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
| `ItabIs ds m tab name` | `tab` is the static itab `name` (`"go:itab.*T,I"`) of the extracted data `ds`, which `m` holds read-only (`Janus.Spec.Dynamic`). |
| `FuncvalIs m fv fn` | The funcval at `fv` is readable and its code word is `fn`. |
| `ClosureCtx m fv vars` | The words after it hold the captured `vars` (`Janus.Spec.ClosureCtx`; `GoABI.ClosureCtx` is the context *register*). |

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
precondition for the current state (it splits conjunctions, unfolds named predicates such as
`GuardOK`/`StackOK` and structures such as `StackGuardOK`, simplifies each part with the state
hypotheses and closes it by `rfl`, an assumption, `omega` or `janus_disch`; what is left is
reported), then destructures the postcondition: conjunctions and existentials become
hypotheses, and an equation `s' = …` is substituted, so the run continues from a state literal.
Without `calls`, `janus_run` executes the callee inline, which also works.

**Callers of callers.** A summary can itself be proved with `janus_run calls [...]` (the goal
of a summary is `ReachesRet`), so a call chain is proved bottom-up, each function once
(`bench/proofs-arm64/Chain1.lean`: five levels). What a non-leaf summary must say:

* the registers it clobbers, as existentials: `∃ v1 v16 f m, s' = { s with regs :=
  setReg (setReg (setReg s.regs 0 r) 1 v1) 16 v16, pc := s.regs 30, flags := f, mem := m } ∧ …`;
  callee-saved registers reloaded from the stack disappear from the register chain
  (`setReg f r (s.regs r)` simplifies to `f`), so `X29`/`X30` need no mention;
* which memory it may change: `MemFrame s.mem m rs` with `rs` the list of byte ranges
  `[(lo, hi), …]` it writes (its frame record and, for a function that spills its arguments, the
  slots in its caller's frame). In the caller, `hf : MemFrame m₀ m rs` is used as two rewrite
  rules (`hf.readLE` for reads outside `rs`, `hf.accessible`), so the caller's own stack slots
  are still read through the callee. Prove it with `janus_frame`:

  ```lean
  janus_run calls [chain4]
  exact ⟨_, _, _, _, rfl, by janus_frame⟩
  ```

* the stack it needs: `StackOK s below above` with `below` covering the frames of every deeper
  level, `GuardOK s adj` with `adj` the extra depth of the deeper stack-guard checks, and the
  guard slot `[X28 + 16, +8)` disjoint from the stack window. The ranges are easy to get wrong;
  the stuck message names the store that is outside them.

### Dynamic calls (`HashWith`, `HashTwice`, `MapSum`, `DeferAdd`)

An interface method call, a call of a func value (closure or method value) and the call of a
deferred closure are indirect: `ldr x3, [x0, #24]; blr x3` (amd64: `MOVQ 24(AX), DX; CALL DX`)
jumps to whatever word memory holds. The executor follows such a call as soon as the target
register is a **literal**, and then treats it like a direct call: a summary passed with
`calls [...]` is applied at the target's entry, otherwise the target is executed (it must be in
the extraction). Two situations:

* **The code being proved builds the func value itself** (`HashTwice` passes the method value
  `h.Hash` to `ApplyTwice`; `DeferAdd` defers a closure). The funcval is a store in the frame,
  the code word is read back from it, and nothing has to be assumed: `janus_run` simply runs
  through the call. The extractor copies the target because the code computes its address
  (`dynamicTargets` with `via: "code-address"` in `identity.json`).
* **The func value or interface comes from the caller** (`HashWith(h Hasher, …)`,
  `MapSum(f func…, …)`). Which code it reaches is then a **hypothesis of the theorem**, stated with
  the vocabulary of `Janus.Spec.Dynamic`, and visible in the printed statement:

  ```lean
  theorem correctness (tab h x : BitVec 64) :
      Ensures Extracted.program Extracted.entry [tab, h, x]
        (fun s => ItabIs Extracted.program.data s.mem tab
                    "go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher" ∧ …)
        (fun s s' => s'.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) ∧ …
  ```

  `ItabIs ds m tab name` says `tab` is the address of the static itab `name` and that memory
  holds its bytes (copied from `.rodata`) read-only, so `Fun[k]` (offset `24 + 8k`) is the
  method address in the binary. For a closure, `FuncvalIs m f fn` gives its code word
  (`segAddr Extracted.program "example.com/basic.AffineSum.func1"`) and `ClosureCtx m f [a, b]`
  the captured variables after it, which the closure reads through the context register
  (`X26` on arm64, `RDX` on amd64).

  Extract the possible targets with `janus extract … --targets SYM,…` (an itab copies the itab
  as a data object named after its symbol, and the code of every method in it; a function or a
  static funcval `…·f` copies that function). `scripts/example-targets.sh` lists the ones the
  examples use.

In the proof, destructure the precondition (the stack window first), then `janus_dyn h₁ h₂ …`
turns the hypotheses into what the executor uses: `h_tab : tab = BitVec.ofNat 64 <addr>`
(substituted when `tab` is a variable), `h_dyn… : m.readLE <addr+8j> 8 = <word>` for every
word of the itab, `m.readLE f.toNat 8 = <code address>`, `m.readLE (f.toNat + 8 + 8i) 8 = vᵢ.toNat`,
the `accessible` facts and bounds, and for an itab its disjointness from every writable range
in the context (it is read-only, so stack stores cannot change it). Each fact is proved from the
hypothesis by a lemma of `Janus.Spec.Dynamic`, the literals by kernel-checked evaluations.
Equations named `h_dyn…` are rewrite rules of every step:

```lean
  intro ret hret s hs ⟨hi, ⟨hh, hhb⟩, hd, ⟨hg1, hg2, hg3⟩, hal, hb, ha, hw⟩
  janus_intro hs
  janus_dyn hi
  simp only [Disjoint] at hd
  janus_run calls [mul_summary, rot_summary]
```

The funcval and the captured variables of a closure argument are ordinary memory: state that
they are disjoint from the stack window, as for any buffer. A loop that calls a closure
(`MapSum`) keeps the closure hypotheses as parameters of its invariant lemma and calls
`janus_dyn` there; the stack slots it rewrites every iteration are described by a `MemFrame`
over the memory at the loop head (`MemFrame mem0 m [(lo, hi)]`, re-established with
`MemFrame.writeLE`), so the invariant does not have to spell out the growing store chain.

**`defer`.** Go 1.26 open-codes most defers: the deferred closure's funcval is built in the
frame, a `deferBits` byte in the frame tracks it, and each exit calls the closure inline
(`DeferAdd`). Such a function also contains a `bl runtime.deferreturn` block that only the panic
recovery path reaches; the extractor does not follow it (`omittedCalls` in `identity.json`), so it
faults if reached and a theorem shows it is not. Defers the compiler cannot open-code (in loops,
more than 8 per function) allocate defer records through `runtime.deferproc*` and call
`runtime.deferreturn` on every exit: these are not supported (the call faults), as are `recover`
and panics that unwind through defers (see SOUNDNESS.md).

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

Each instruction costs one `simp` call on the instruction and the current state plus one kernel
check of the program fact `stepOK`. `scripts/bench.sh` measures the elaboration time (CPU) of
every example and of the benchmarks in `bench/`; `bench/RESULTS.md` has the numbers, and the
before/after comparison of the optimisations below.

What the executor does to keep a step cheap:

* **No re-simplification of the state.** A symbolic state is mostly values that earlier steps
  already simplified. The `simp` cache is kept between the steps of a run (per local context,
  so a new branch hypothesis starts a fresh cache), and so is the simp context. Without this,
  the cost of a step grew with the length of the run (11 ms to 100 ms per step in `AddLimbs`).
* **No `whnf` of the goal.** `MVarId.apply` puts the goal in weak head normal form to count
  arguments; on `ExecThen p (if c then … else …) Q` that evaluates the decision procedure of
  the symbolic condition (5 s for one stack-guard branch on amd64). The step lemmas are applied
  by unification only (`Common.applyFast`), and goal shapes are recognised syntactically.
* **Closed side conditions evaluated, not kernel-checked one by one** (see the discharger).
* **Each pc is decoded and its `stepOK` fact proved once per run** (loops and branches revisit
  pcs).
* **Reducible transparency only** when a callee precondition is closed by `rfl`/`assumption`:
  unfolding `Memory.accessible`/`readLE` of a symbolic memory took seconds.

Tips:

* Keep facts about the initial state as equations on `s.regs i`, `s.pc`, `s.sp`, `s.mem`; they are
  the rewrite rules.
* Split cases (aliasing, table indices) as late as possible. Each case re-executes the code.
* Large extractions (the `seg<i>` form) cost nothing extra. The program is evaluated once per
  `janus_run`, and fetches are checked by the kernel.
* Long runs are not the problem; post-processing often is. In `bench/proofs-arm64/BigFrame.lean`
  the 400-instruction run takes 20 s and the 64 index cases after it 50 s, most of it checking
  `omega` proofs of the disjointness of stack slots. Prefer a spec that avoids the case split
  when you can.
* Each of `N` aliasing cases re-runs the code; `omega` side conditions see every disjunctive
  hypothesis in the context, so split them into atomic facts (`rcases`) before running.

## Troubleshooting

When symbolic execution cannot proceed, `janus_run` (and `janus64_run`) stops with an error that
names the pc (with `function+offset`), the instruction (disassembled), what failed and which
hypotheses would make it go through. It never ends in a bare `(deterministic) timeout`. The
messages below are real; they come from `JanusTests/Diagnostics.lean` (which checks them) and
from proofs with a hypothesis removed.

**A memory access that is not known to be allowed.** `examples/proofs/Get.lean` without the
`Ptr` fact about the slice:

```text
janus_run: stuck at pc 0x93164 (example.com/basic.Get+0x24): ldr x0, [x0, x3, lsl #3]
• cannot prove that the 8-byte read at `ptr.toNat + 8 * i.toNat` is allowed (the memory is `s.mem` after 3 stores, which do not change what is accessible):
  s.mem.accessible (ptr.toNat + 8 * i.toNat) 8 false = true
The `accessible` hypotheses about `s.mem`:
  hg2 : `s.mem.accessible (BitVec.toNat (s.regs 28) + 16) 8 false = true`
      `BitVec.toNat (s.regs 28) + 16 ≤ ptr.toNat + 8 * i.toNat` is not provable by omega; `ptr.toNat + 8 * i.toNat + 8 ≤ BitVec.toNat (s.regs 28) + 16 + 8` is not provable by omega
  hw : `s.mem.accessible (BitVec.toNat s.sp - 24) (24 + 16) true = true`
      `BitVec.toNat s.sp - 24 ≤ ptr.toNat + 8 * i.toNat` is not provable by omega; `ptr.toNat + 8 * i.toNat + 8 ≤ BitVec.toNat s.sp - 24 + (24 + 16)` is not provable by omega
It is discharged by a hypothesis `s.mem.accessible b k w = true` with `b ≤ ptr.toNat + 8 * i.toNat` and `ptr.toNat + 8 * i.toNat + 8 ≤ b + k` provable by omega: state the region in the precondition (`Ptr`, `Buffer`, `StackOK`, `StackWritable`) together with the arithmetic facts that bound the address (e.g. `i.toNat < len.toNat`).
```

For each `accessible` fact about the same memory the message says which of the two range
inequalities `omega` could not prove (here: the slice is in neither region). A fact that is
too short shows up as `` `p.toNat + 8 ≤ p.toNat + 4` is not provable by omega ``.

**An address that may wrap.** A stack store below the window `StackOK` grants
(`bench/proofs-arm64/Chain1.lean` with `StackOK s 32 0` where the frame needs 40 bytes):

```text
janus_run: stuck at pc 0x93820 (example.com/bench.Chain4+0x10): stur x29, [sp, #-0x8]
• cannot prove that the 8-byte write at `(18446744073709551576 + BitVec.toNat s.sp) % 18446744073709551616` is allowed (…)
…
The address is `BitVec.toNat s.sp` - 40 computed modulo 2^64: it could not be shown not to wrap below zero. This needs `40 ≤ BitVec.toNat s.sp` (for the stack: a larger `below` in `StackOK`/`StackWritable`, which covers `[SP - below, SP)`).
```

**A read over a store whose aliasing is unknown.** This does not stop the run (the read stays
as `(m.writeLE a n v).readLE b k` in the value), so the run reports it as information when the
remaining goals contain such a read (`set_option janus.aliasInfo false` turns this off).
`examples/proofs-amd64/Add256` without `Disjoint z 32 y 32`:

```text
janus64_run: the remaining goals contain reads over earlier stores whose aliasing is unknown (they stay as `(m.writeLE a n v).readLE b k` and usually make the goal unprovable):
• at pc 0x4892d0 (example.com/basic.Add256+0x10): mov rsi, qword ptr [rcx + 0x8]: an 8-byte read at `y.toNat + 8` follows an 8-byte store at `z.toNat`, and it is unknown whether they overlap. omega needs either
  `y.toNat + 8 + 8 ≤ z.toNat ∨ z.toNat + 8 ≤ y.toNat + 8`   (disjoint), or
  `z.toNat = y.toNat + 8`   (the same address).
Add `Disjoint`/aliasing facts to the precondition, or split on the aliasing before running (`rcases h with rfl | h`).
```

**A fault on a path that was not pruned.** The message lists the branch conditions of the path,
so you can see which fact would refute it (`br x5` with nothing known about `x5`):

```text
janus_run: the instruction at pc 0x10000 (indirect): br x5 faults:
  Fault.noCode (BitVec.toNat (s.regs 5))
(the branch target is not code; a register target at or above 2^56 (a tagged pointer, not modelled) also ends here: add a bound on the target register)
This path was taken under the branch conditions (most recent first):
  hbr : `72057594037927936 ≤ BitVec.toNat (s.regs 5)`
A path is pruned when omega refutes its branch condition from the hypotheses: add the fact that excludes it.
```

**A pc that is not concrete, or outside the code.**

```text
janus_run: stuck after 1 instructions: the pc of the current state is not a concrete address:
  s.regs 5
This is an indirect branch (`br`, `blr`, `ret`) to an address the hypotheses do not determine. For the return of the function being proved, run `p.withExit ret` with `hret : RetAddr p ret` in the context (`intro ret hret …`) and keep `h_lr`; for a callee, prove it as a `Summary` and pass it with `calls [...]`; otherwise add an equation `… = BitVec.ofNat 64 addr` for the target register.

janus_run: stuck after 1 instructions: pc 0x10100 is not in the extracted code (segments: nocode [0x10000, 0x10004)) and is no known stub.
If this is a call, extract the callee too or give its `Summary` with `calls [...]`; if it is the return, `X30` does not hold the return address of `p.withExit ret`.
```

**An instruction outside the model.**

```text
janus_run: stuck at pc 0x10004 (undec+0x4): the word 0x0 does not decode to a modelled instruction (see docs/SOUNDNESS.md for the supported subset). No proof can execute past it.
janus64_run: stuck at rip 0x1003 (undec+0x3): the bytes [0xf, 0x5] do not decode to a modelled instruction (see docs/AMD64.md, 'Supported instructions'). No proof can execute past it.
```

**A callee precondition that does not hold at the call site.**

```text
janus_run: at pc 0x50014, the entry of f+0x14: the precondition of its summary could not be proved. Remaining goals (after simplification):
  BitVec.toNat x = 0
Add the facts they need to the context, or weaken the summary's precondition.
```

**A heartbeat budget exceeded.** With `janus_run (budget := N)` the budget covers the run only;
without it, the declaration's `maxHeartbeats` (the message is logged before Lean's own timeout
error, which may follow because the declaration has no heartbeats left):

```text
janus_run: heartbeat budget exceeded at pc 0x933b4 (example.com/basic.AddLimbs+0x24): movn x8, #0 while evaluating the instruction (simp with the janus_exec set), after 11 instructions.
The limit was `maxHeartbeats` (2000), which covers the whole declaration: raise it with `set_option maxHeartbeats N in` before the theorem (or give this run its own budget with `janus_run (budget := N)`), or stop earlier (`until [...]`, a callee `Summary`) and split the proof.
```

Any other failure inside a step (`simp` running out of steps, an error in a user lemma) is
reported with the same location prefix (`janus_run: failed at pc … while …`).

## Extending the automation

* New memory models (like `copyWords`): prove `regions`/`accessible` frame lemmas and tag them
  `janus_exec, janus_post, janus_acc`. Prove read lemmas and tag them `janus_exec, janus_post`.
* Lemmas used only at the end: tag them `janus_post`, or pass them to `janus_simp [...]`.
* Avoid permutation lemmas (simp's ordering check is exponential on the shared terms of a
  symbolic state); see `setReg_comm`.
* Do not let the kernel evaluate `BitVec.signExtend` or `&&&` on projections of a literal state by
  `rfl`. State them as `Nat` arithmetic (see `sext64_eq`, `exec_adr`).
* The ISA-independent machinery (status and budget, stuck analysis, the simp cache,
  `applyFast`, callee preconditions and postconditions, `MemFrame`/`janus_frame`, `janus_cases`)
  is in `Janus/Tactic/Common.lean` and shared by both executors; the disassemblers are
  `Janus/Tactic/Disasm.lean` and `Janus/Amd64/Disasm.lean`.
