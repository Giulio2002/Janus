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
| `set_option janus.merge true in janus_run …` | Path merging (also `janus64_run`): the pending path with the smallest pc is stepped first, and two paths at the same pc whose goals differ only in branch hypotheses and in a few non-memory subterms (registers, flags) are merged into one goal that quantifies over the differing values (`jv…`); the branch hypotheses they do not share are dropped. A diamond (`if c { x++ }`, a `&&` test) is then executed once after its join instead of once per path. Opt-in: a proof that needs a dropped branch fact, or a register value that differed, fails with merging. |
| `janus_step [lemmas]` | Exactly one instruction (`calls`/`budget` as for `janus_run`). |
| `janus_simp [lemmas]` | The post-processing simp set `janus_post` plus the state hypotheses and `lemmas`. Closes invariant side goals (`S'.regs 2 = i + 1`, …). |
| `janus_arith` | The arithmetic left after execution. First `janus_carry` (below); if that does not apply, `omega` after adding `readLE m a n < 256^n` for every memory read and normalising carry terms. Does nothing if there is no goal. (`janus64_arith` on amd64.) |
| `janus_carry` | Carry chains by reflection: proves `a = b`, `a ≤ b`, `a < b` (or a conjunction of them) between `Nat` terms built from limbs, `+`, `*`, `-`, literals, `/ k`, `% k` and `(decide (k ≤ a)).toNat`. See *Multi-limb arithmetic* under Techniques. |
| `janus_ring` | Polynomial identities over `Int` (`+`, `*`, `-`, `^` with a literal exponent) by a verified normaliser; on `Nat`, `janus_carry`. |
| `janus_data hd` | From `hd : p.DataLoaded m`: readability of each `.rodata` object, and a rewrite rule that evaluates loads from it at literal addresses. |
| `janus_dyn h₁ h₂ …` | From dynamic-call hypotheses (`ItabIs`, `FuncvalIs`, `ClosureCtx`): the itab's literal address and words, the funcval's code word, the captured variables, as equations the executors use (both ISAs). See [Dynamic calls](#dynamic-calls-hashwith-hashtwice-mapsum-deferadd). |
| `janus_cases h` | From `h : k < N` (`N` a literal): `N` goals with `k` replaced by `0, …, N-1`. For table lookups at a symbolic index. |
| `janus_frame` | Proves `MemFrame m₀ m rs` (the memory part of a callee summary, see Calls): peels the stores of `m`, goes through the `MemFrame` hypotheses of called summaries, side conditions by `omega`. |
| `janus_eval% t` | A term: the closed natural number `t` (e.g. `segAddr Extracted.program "f" + 8`) evaluated to a numeral at elaboration time, for a lemma argument that must be a literal. |
| `janus_disch` | The discharger used inside every simp call (see below). |
| `janus_close` | Recommended closer for side goals: `with_reducible rfl`, `with_reducible assumption`, `janus_omega_sparse` (omega without the context's aliasing disjunctions, then with the relevant ones), then full `omega`. Use it instead of `first | rfl | assumption | omega` chains: those unfold at default transparency and let `omega` split on every disjunction. |

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
* linear address facts (`x + 8 + 8 ≤ z ∨ z + 8 ≤ x + 8`, `x + 8 = x + 8`) by literal arithmetic and
  at most one case split on an aliasing hypothesis (`Common.addrDisch`);
* carry bounds and equations (`… / 2^64 < 2^64`) by `janus_carry` (see
  *Multi-limb arithmetic* below);
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

**Faults (`LoadThird`).** A nil dereference is a hardware fault, not a stub call, so it is stated
at the machine level: for the call state `s` with `X0 = 0` (`RAX = 0`) and memory that maps nothing
below `4096` (`∀ r ∈ s.mem.regions, 4096 ≤ r.base`), the instruction at `s.pc` is ordinary code
(not the exit, no stub), its word decodes to the load, and `Arm64.step w s` (`Amd64.step`) is
`.error (.outsideAllocation a n)` with `a < 4096`; `Faults` follows (`faults_of_steps` on arm64,
`Program.run_succ_fault` on amd64). Prove the step by `step_of_decode` with the decoded
instruction (`decide`), then unfold the address computation and `load`, and refute
`accessible` from the region bound (`List.any_eq_false`). The shape is the panic library's
`FaultsAt` predicate, so the signal-to-panic step can lift it unchanged.

### Stack growth, the grown case (`BigLocal`, `SumRec`, `HoldPtr`)

The prologue's `morestack` branch — the grown case excluded by `GuardOK` above — is covered by
the `morestack` contract (`Janus/Contracts/Stack.lean`, docs/RUNTIME-CONTRACTS.md "Stack
growth"). A grown theorem is an `EnsuresGrow p reloc entry args pre post`: like `Ensures`, but
the conclusion is `GrownReturns` (a return after any number of stack growths) and `pre` does
**not** assume the frame fits. It takes a frame table `FT`, the stack pools, the runtime-owned
memory `rt`, a readiness `H` and the contract `hms : MorestackContract p FT pool rt H reloc` as
hypotheses.

The proof reuses the ordinary roomy `Summary`:

```lean
theorem correctness … (hms : MorestackContract Extracted.program FT pool rt H reloc) … :
    EnsuresGrow Extracted.program reloc Extracted.entry [x, i] (GPre FT pool rt H) post := by
  intro ret hret s hs hpre
  janus_intro hs
  …
  by_cases hroom : lo + stackGuard + 48 < s.sp.toNat
  · -- the frame fits: the prologue falls through, apply the roomy Summary
    exact .done (Summary.returns summary …)
  · -- the frame does not fit: run the prologue to the morestack stub …
    apply GrownReturns.of_reaches_stub
    janus_run
    -- … the contract resumes on a larger stack; the glue reloads the args; the Summary applies
    refine grow_branch … (hms …) …
```

`janus_run` runs the prologue; with room it reaches the return through the body, without room it
stops at the `.morestack` stub, leaving the concrete call state to the contract. The contract's
`Grown` promises a larger stack with room for the function's `funcMaxSPDelta + stackGuard`, so
the roomy `Summary` applies after the glue re-enters the function. The arguments survive the move
because the stack maps classify the spill slots as scalars (`Moved.readLE_scalar`); a pointer
argument would be adjusted instead (`Moved.readLE_ptr`). `BigLocal` keeps everything
layout-independent: it uses `Extracted.entry` and the glue offset `Extracted.entry + 0x6c`, never
a hard-coded address. `grow_rec` (well-founded recursion on the stack's distance from
`maxstacksize`) and the grown callee summaries `GrownRet`/`GSummary` (`bind`, `call`,
`GSummary.induction`) are there for functions that grow more than once, such as a deep recursion.

The non-vacuity witness (`Proof.Witness`) reuses the two-slot toy runtime of
`Janus/Contracts/StackSat.lean` for the real binary's `morestack` stub, exhibits a call state
whose frame does **not** fit (`Witness.no_room`), shows all hypotheses hold together
(`nonvacuous`) and that the conclusion is reached (`returns`).

**The frame table.** Extract with `--frames` (`scripts/example-targets.sh` adds it for the
stack-growth examples): `Extracted.frames` then lists the binary's frame records, and the theorem
assumes `hA : FT.Agrees Extracted.frames`. Read what you need at a pc into a small `TableOK`
predicate with `hA _ (List.mem_cons_self ..) pc (by decide) (by decide)` — never `rw`/`simp`
`Extracted.frames` (the auditor rejects a proof that declares its equation lemmas). The witness
table is `FrameTable.ofRecs Extracted.frames extraT` (`ofRecs_agrees`, and `ofRecs_laws`/
`ofRecs_laws_arm64`/`ofRecs_laws_amd64` check the records by `decide`).

**Growth inside a callee** (`SumRec`, `HoldPtr`). State the callee as a grown summary
`GSummary p reloc entry Pre Post` (`GSummary64` on amd64) whose `Post` says how the caller's
memory moved: `∀ fs, Chain … fs → Moved (framesCls … fs) pool lo hi hi' base ex s.mem s'.mem`
(the caller's walk, from the callee's argument area up, with the slots the callee may write in
`ex`), plus the moved `SP`/`FP` and the new `GStack`. Use it with `GrownRet.call`; after the call
read the caller's frame back through the move: a scalar slot with `Moved.readLE_scalar`, a slot the
stack maps mark as a pointer into the stack with `Moved.readLE_ptr` (the value is adjusted — this is
how `HoldPtr` finds `p` and `*p` on the moved stack), a return address with `Moved.readLE_word_out`
(code is outside the pools). For recursion prove the summary with `GSummary.induction`, the
induction hypothesis being the callee; when one level grows the stack itself, compose its move with
the callee's (`Moved.mono_base`, `mono_ex'`, `cls_congr`/`cls_congr'`, `trans'`, `congr_src`). On
amd64 the saved `RBP` is adjusted too (`adjustWord`); `Post` states it as `adjustWord lo hi hi' RBP`,
which two moves compose (`adjustWord_trans`, under `BPOK`: the caller's `RBP` points into the
stack or outside every stack). Every grown precondition carries `NoStackPtr s.mem pool rt` (no
pointer into a stack outside the stacks), which the contract's `MorestackPre.noptr` needs; a store
to the stack keeps it (`NoStackPtr.writeLE`), and so does a move (`NoStackPtr.of_frame`).

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

**Loops in a callee, through a closure (`SpanSum`).** A non-inlined range-over-func loop runs in
the iterator (`Span.All`), which calls the loop body closure (`SpanSum-range1`) once per element;
the body updates the caller's variables through captured pointers. State the invariant at the
iterator's loop head, about the call state `s` of the outer function: the register contents of the
head (`i`, `hi`, the funcval pointer), `SP` of the iterator's frame, the memory `m` as a `MemFrame`
of the memory at the first arrival (`mem0`, copied from the goal `janus_run until [head]`
leaves) outside the words the iterations write (the index slot, the body's frame, `#state` and
the sum), plus the two words the body reads as equations (`m.readLE stateAddr 8 = 1`,
`m.readLE sumAddr 8 = acc`). The induction runs on the number of iterations left; each step is
`janus_run until [head]` (it executes the call through `BLR`/`CALL BX`, the body, and the return),
then `ih` with the stores chained by `MemFrame.writeLE`. The closure needs no hypothesis: the
outer function builds the funcval itself and the extractor finds the body from the code address.

**Code addresses as values.** When an invariant mentions a code address as data (a saved return
address in a frame, a closure's code pointer in a funcval), write it as
`segAddr Extracted.program "pkg.F" + off`, never as a literal: literals break whenever the binary's
layout moves (a new runtime function linked in shifts every later address). Before running, turn
the terms into literals in the hypotheses the executor reads, with the kernel-checked simproc
`reduceSegAddr` (arm64 `Janus.Tactic`, amd64 `Janus.Amd64.Tactic`):
`simp only [mem0, reduceSegAddr, Nat.reduceAdd] at hfr`. Do not `simp` with `Extracted.entry` or
`Extracted.segments` (their equation lemmas would be declared in the proof module, which the audit
rejects as shadowing `Extracted`); use `segAddr` of the entry function instead.

### Recursion (`Fact`)

A recursive function calls its own entry, so its `Summary` is needed while it is being proved.
`Summary.induction μ` (`Janus/Tactic/Recursion.lean`; `Janus/Amd64/Recursion.lean` on amd64)
proves a summary by strong induction on a measure `μ` of the entry state: in the case `μ s = n`
the induction hypothesis `ih` is the summary itself for every state with `μ s < n`, and
`janus_run calls [ih]` uses it at the recursive call like any callee summary. There the executor
proves `ih`'s precondition for the call state, including `μ < n` (the argument decreased) and
the stack facts one frame down:

```lean
theorem summary : Summary Extracted.program Extracted.entry Pre Post := by
  apply Summary.induction (fun s => (s.regs 0).toNat)
  intro n ih s hpc ⟨⟨⟨h1, h2⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd⟩, hn⟩
  janus_step               -- the entry is the summary's own address: step past it first
  janus_run calls [ih]
  …                        -- one goal per path: `Post s s'`
```

* `Pre` and `Post` are stated in terms of the entry state, with the depth as a function of the
  argument: `StackOK s (32 * n + 40) 16`, `GuardOK s (32 * n)` (the deepest prologue check), and
  a `MemFrame` over exactly the bytes the recursion writes. The ranges must not cover the
  caller's own saved registers one frame up (for `Fact` the window ends at `SP - 16`, below the
  slot of the caller's `X29`), otherwise those reads are not resolved after the call.
* The callee summary is applied as soon as the pc is at its entry, so start the proof with one
  `janus_step`.
* `Summary.returns` applies the finished summary to the function's own call state
  (`Ensures`): `refine Summary.returns summary hret (by rw [h_pc]; rfl) h_lr ?_ ?_`.

The stack hypotheses say that the stack already has room for every frame; the grown-stack case
(`morestack`) is not covered.

### Mutual recursion (`IsEven`, `CycA`)

When functions call each other (a strongly connected component of the call graph: `IsEven` and
`IsOdd`, or a Karatsuba-style family where the multiplication entry calls the recursive kernel,
which calls the entry again on halves), no member's summary can be proved first.
`Summary.induction_mutual μ` (both ISAs, in the same files) proves all of them at once. The
members are indexed by any type (an inductive with one constructor per member), each with its
entry, `pre`, `post` and its own measure `μ i s : Nat` on a shared scale; in the case
`μ i s = n` the induction hypothesis `ih j` is the summary of **every** member `j` for the states
with `μ j s < n`:

```lean
inductive Member | even | odd
def entryOf : Member → Nat
  | .even => segAddr Extracted.program "example.com/basic.IsEven"
  | .odd => segAddr Extracted.program "example.com/basic.IsOdd"

theorem summary : ∀ i, Summary Extracted.program (entryOf i) Pre (Post i) := by
  apply Summary.induction_mutual (fun _ s => (s.regs 0).toNat)
  intro n ih i s hpc ⟨…, hn⟩
  -- the callee summaries, with their entries as the executor sees them
  have ihE : Summary Extracted.program (segAddr Extracted.program "example.com/basic.IsEven") _ _ := ih .even
  have ihO : Summary Extracted.program (segAddr Extracted.program "example.com/basic.IsOdd") _ _ := ih .odd
  cases i
  · simp only [entryOf] at hpc; janus_step; janus_run calls [ihO]; …
  · simp only [entryOf] at hpc; janus_step; janus_run calls [ihE]; …
```

* Every call inside the component must decrease the measure. When a member calls another with
  the same argument (`CycA(n)` → `CycB(n)` → `CycC(n, …)` → `CycA(n-1)`), weight the members:
  `μ` is `3n + 2`, `3n + 1`, `3n`. `Summary.induction_mutual_wf` takes any well-founded relation
  instead (a lexicographic measure, say).
* Per-member preconditions and frames (`below`, `adj`, `frame` in `CycA.lean`) are functions
  of the member; members with different frame sizes need different stack windows. Simplify the
  `ih` hypotheses with those definitions (`simp only [Pre, adj, below, …] at ihA ihB ihC`) and
  pass the frame and result functions to the executor (`janus_run [frame, result] calls [ihB]`)
  so that the callee's `MemFrame` and result are read at the call site.
* A statement must not mention the member type (the audit allows only plain definitions in a
  statement): state each member's `Ensures` with its own precondition (`PreA`, `PreB`, …), as
  `CycA.lean`'s `correctness` does, and prove it from the summary with `Summary.returns`.

### Go assembly and ABI0 calls (`examples/asm`)

An assembly function (`f.abi0`) takes its arguments from the caller's frame, so its theorem is
`GoABI0.Ensures0 p entry [a₀, …] nres pre post` (amd64: `Amd64.GoABI0.Ensures0`): start with
`intro ret hret s hs hpre; janus_intro0 hs` (`janus64_intro0`), which turns the frame words into
`h_rd_arg<i>` rewrite rules, then `janus_run` as usual; the result words are `results0 s s' n k`.
As a callee (a direct ABI0 call from Go, an ABI wrapper) the function is a
`Summary0 p entry pre Q`: from any state at its entry it returns with every register but the
reserved ones unspecified and memory satisfying `Q s` — typically
`MemFrame (s.mem.writeLE resultAddr 8 v) m [(scratch)]`, proved with `MemFrame.writeLE_congr`,
`MemFrame.writeLE_both` and `janus_frame`. `janus_run calls [h]` uses it; on amd64 the caller's
re-entry (`XORPS X15, X15; MOVQ FS:-8, R14`) then needs `TlsG s` in the precondition.
`Ensures0.of_summary0` gives the standalone contract from the summary. See
[ABI0.md](ABI0.md) and the ten proofs in `examples/asm/proofs/`.

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
* **LSE vs LL/SC.** `correctness` preconditions select the LSE path (`readLE hasAtomics 1 % 2 =
  1`). The LL/SC fallback is modelled too: a store-exclusive's outcome is `s.exclPass`, which the
  theorem quantifies over, so a retry loop is proved by induction on the index of the first
  passing attempt (`AtomicAdd.loop`, `AtomicMax.loop`: case-split on `S.exclPass 0`, pass the
  equation to `janus_run [h]` so the branch disappears, and for a failure run `until` the loop
  head and apply the hypothesis to the shifted stream). The theorem then assumes
  `∃ k, s.exclPass k = true` (`anyCPU`): without an eventual pass the loop does not terminate
  (docs/SOUNDNESS.md).
* **Implementation-defined parameters.** `ClearWords` holds for every `State.dczid`. It splits
  on the 32 values with one theorem per value (`CaseStmt k`), so that Lean elaborates them in
  parallel, and it combines them with `janus_cases`. Long hardware loops (32 `DC ZVA`s of 4-byte
  blocks) go through an induction lemma (`zva_loop`) instead of straight-line execution. Zeroed
  ranges are tracked with interval lemmas (`ZeroOn`, `zeroOn_writeLE_zero`) rather than byte by
  byte.

### Writable globals (`MulAlgo`, `Double`)

A package variable is writable, so its value at a call is whatever the program stored. A theorem
says which values it relies on, in one of three forms (`Janus/Spec/Globals.lean`, both ISAs),
about the globals `janus extract --global SYM` recorded with their link-time images
(`Extracted.program.globals`; see [CLI.md](CLI.md#extract), step 10):

* **The link-time value**: `GlobalsInit Extracted.program.globals s.mem ["pkg.x", …]` (every
  named global holds the bytes the ELF file gives it, `.bss` zero, in one writable region). Right
  for a tuning constant nobody writes, such as math/big's `karatsubaThreshold`. Wrong for a
  variable package initialisation sets (`internal/cpu.X86`, `hasADX`): its image is zero.
* **Every value**: `GlobalIs Extracted.program.globals s.mem "pkg.x" v` (the whole global reads
  `v`), or `GlobalBytesIs … "pkg.x" off k v` (bytes `[off, off+k)`, a field such as
  `X86.HasADX` or the flag word of `runtime.writeBarrier`), with `v` a parameter of the theorem.
  `GlobalsInit.globalIs` / `GlobalsInit.bytesIs` specialise such a theorem to the image, so the
  initial-value theorem follows (`MulAlgo.correctness` from `MulAlgo.forAllValues`).
* **The raw image** as a term: `globalImage Extracted.program.globals "pkg.x"` (the bytes),
  `globalInitVal` (their little-endian value), `globalAddr` (the address, e.g. of
  `runtime.zerobase`, which `[]byte{}` points to).

In the proof, `h.elim rfl` (or `h.accessible rfl w`) turns the hypothesis into the facts the
executor uses: the accessibility of the global's range and `s.mem.readLE base size = v`, with
the literal address of the extraction:

```lean
  obtain ⟨hca, hcr⟩ := hc.elim rfl          -- hc : GlobalIs … "example.com/basic.karatsubaCut" cut
  simp only at hca hcr                       -- s.mem.accessible 0x170448 8 true, s.mem.readLE 0x170448 8 = cut
  have hca' := Memory.accessible_read_of_write _ hca
  janus_run
```

A flag read by both paths of the code (`Double`: a shift when `useFast` is set, a loop when it
is clear) needs no case split of its own: the executor branches on the byte it loads, and the
theorem holds for every `v`. `GlobalBytesIs.flag_cases` gives the two cases explicitly when a
proof needs them. **Non-vacuity**: `globalsInit_image gs m names (by decide) (by decide)` proves
`GlobalsInit` for the memory `globalsImage gs m` (the image laid over `m`), so a witness state
built on it shows the precondition satisfiable; `Double`'s witness also stores the flag set
(`writeLE`) to show the other path is reachable.

### Multi-limb arithmetic (`Add256`, `AddLimbs`, `bench/…/MulAdd8*.lean`, `bench/…/Mul256.lean`)

After running a multi-limb routine (`bits.Add64`/`bits.Mul64` chains, `uint256`-style code), the
goal is an equation between limb terms such as

```text
(z₀ + p₀ % 2^64 + c) % 2^64 + 2^64·((p₀ / 2^64 + (z₀ + p₀ % 2^64) / 2^64 % 2^64 + …) % 2^64) + …
  = z₀ + 2^64·z₁ + … + y·(x₀ + 2^64·x₁ + …) + c
```

with every carry as a `/ 2^64`, every limb as a `% 2^64` and, on amd64, carry flags as
`(decide (2^64 ≤ a)).toNat`. `omega` proves these, but slowly (it has to rediscover each carry
bound, and it does not know `x·y ≤ (2^64-1)^2`, so products must be named and bounded by hand).
`janus_arith` now closes them with **`janus_carry`**, a decision procedure proved sound in Lean
(`Janus/Tactic/CarryDefs.lean`, `CarrySound.lean`):

* both sides are reflected into a term language over **atoms** (`x.toNat`, memory reads, any
  other subterm) and normalised into integer polynomials (`Janus/Tactic/Ring.lean`) over the
  atoms and **quotient atoms** `D = L / 2^64`, one per distinct carry: `t / k` and `t % k`
  split the normal form of `t` as `L + k·Y` and become `D + Y` and `L - k·D`. This merges the
  two halves of a carry (`p / 2^64 + (z + p % 2^64) / 2^64` becomes `(p + z) / 2^64`), so a
  whole add-with-carry chain collapses to `Σ 2^(64i)·limbᵢ` in one normalisation;
* every subterm and every atom also gets an interval (`x.toNat ≤ 2^w - 1`, `readLE m a n <
  256^n`, products of bounds, hypotheses `atom ≤ c` / `atom < c`), and a difference of two
  carries `(a + b)/k - a/k` is bounded by `b/k + 1`. A `% k` or `/ k` whose argument lies in
  `[0, k)` disappears: this is how `hi + c₁ + c₂ < 2^64` is shown for a multiply-add limb;
* the goal holds if the normal forms of the two sides are equal, or if they differ by a
  multiple `g·Z` (`g` the gcd of the difference) and both sides lie in `[0, g)`: this proves
  low-half statements like `Σ 2^(64i)·zᵢ = X·Y % 2^256` (`Mul256`).

The certificate (the quotient atoms and the atom intervals) is computed by the tactic and
checked by `check`, which the kernel evaluates (`Eq.refl true`, like `decide +kernel`); the
theorem `check_sound` turns it into the goal. Nothing is trusted and no axiom beyond Lean's is
used. If the normal forms do not match, `janus_carry` fails and `janus_arith` falls back to
`omega` (so goals that are not carry chains, or that need hypotheses other than bounds, still
work).

What this means for a proof:

* **No product needs naming.** The `generalize y.toNat * … = p₀` / `have hb₀ : p₀ ≤ …` blocks
  of older proofs can go; `janus_arith` knows the bound of a product from the bounds of its
  factors.
* **No `janus_simp [Nat.mul_add, …]` before the arithmetic.** Products of sums are expanded by
  the normaliser.
* The same procedure runs inside the dischargers (`janus_disch`, `janus64_disch`): side
  conditions such as `carry < 2^64` of `mod64_of_lt` are proved during the run, so the symbolic
  state keeps fewer `% 2^64`; and a carry bound it refutes, about atoms no hypothesis mentions,
  is not retried by `omega` (which cannot know more). `set_option janus.carry.disch false`
  turns this off; `janus.carry.dischMaxNodes` (default 64) limits the size of the side
  conditions it proves (each costs a kernel evaluation).
* `set_option trace.janus.carry true` prints, for each goal, the number of atoms and quotient
  atoms and whether the certificate was accepted; when it is not, the difference of the two
  normal forms and the table of quotient atoms (usually a carry whose bound it could not show:
  add the bound as a hypothesis `h : c ≤ …`).

A 256-bit multiplication (`bench/go`, `Mul256`, `z = x·y mod 2^256`, aliasing allowed) is
proved by `janus_run; janus_arith` on arm64; see `bench/proofs-amd64/Mul256.lean` for amd64,
where `janus64_run [readLE_32, BitVec.toNat_mul]` also splits the 32-byte values into limbs and
turns `IMULQ` into `Nat` multiplication.

**`janus_ring`** proves polynomial identities over `Int` by the same normal form (and on `Nat`
by `janus_carry`): `(a + b) * (a - b) = a ^ 2 - b ^ 2`.

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

**amd64 `IndexByte`.** `examples/proofs-amd64/A64IndexByte` proves the same function on the AVX2
path. Two facts do the work: `ctz_msb_cmpeq` (`BSF` of the `VPMOVMSKB` of `VPCMPEQB` against a
broadcast byte is `firstTrue` of the byte comparisons) and `cmpeq_msb_zero` (the mask is zero iff
no byte matched), passed to `janus64_run` as rewrite rules so that it prunes the `BSF`-of-zero
path. The SSE path is out of reach: it runs `BSF` on every chunk's mask before testing it, and the
model makes `BSF` of zero a fault (the destination is architecturally undefined).

### Auto-vectorised C code (`A64CountByte`)

`examples/basic/countbyte_arm64.s` embeds, word for word, what gcc 15.2.0 emits at cgo's default
`-O2` for the C loop `for (i = 0; i < n; i++) k += p[i] == c;` (`v_count` of
`scripts/coverage/ccorpus/vec.c`), behind an ABI0 shim that loads `X0`–`X2` from the Go argument
frame; `A64CountByte` calls it. The theorem holds for every length, so it has two loop
invariants, each proved by induction on the iterations left (the template of `Sum`):

* `vloop`, at the head of the 16-byte loop: the two 64-bit lanes of the accumulator `v26` add up,
  modulo `2^64`, to the count of the first `16 k` bytes. The registers that hold constants are
  stated as equations (`v23 = DUP c`, `v24 = MOVI #1`, `v29 = 0`) and passed to `janus_run`. One
  iteration leaves terms like `threeSameOp false 3 16 128 v26 (threeDiffOp true 32 2 1 1 …).1 0`;
  the `janus_exec` element lemmas of `Janus.Tactic.Neon` evaluate their lanes: `elem_add` (ADD),
  `elem_uaddw_64` (UADDW/UADDW2; `elem_hi64_32` for the high half), `elem_zip_zero_16/32/64`
  (ZIP1/ZIP2 with a zero vector, read at twice the element size, is a zero extension), with
  `elem_cmeq` and `elem_and` of `Janus.Tactic.Vector` below them. Each lane comes out as a sum of
  eight `if p[16k+i] = c then 1 else 0`, and `countOf_add16` states the count of sixteen more
  bytes with the same atoms, so the step is one `omega` (the lane sums are kept modulo `2^64`, so
  no bound on the lanes is needed). `threeDiffOp_snd` and its siblings say that a
  non-saturating operation leaves `FPSR.QC` alone, which keeps `qcCommit` from branching.
* `tail`, at the head of the scalar loop (`LDRB`, `CMP`, `CINC`): `X0` is the count of the
  first `i` bytes.

`correctness` runs to either loop head (`janus_run … until [vhead, thead]`): `len = 0` returns at
once, `len < 16` enters `tail` at 0, otherwise `vloop` at block 0; `vloop`'s last iteration
either returns (`len mod 16 = 0`, through `ADDP` and `FMOV`) or enters `tail` at `len - len mod 16`.

The same loop, compiled by cgo rather than embedded, is proved end to end through the FFI
layer: `examples/proofs-cgo/arm64/CCount.lean` is the `CEnsures` of `c_count` in
`examples/cgo/neon` (same two invariants, loop heads at `entry + 0x40` / `entry + 0xa4` of that
build), and `GoCount.lean` composes it with the `_cgo_…_Cfunc_c_count` wrapper and Go's
`neon.Count` under `CgoCall.refines` (see `docs/FFI.md`). The C function lives in its own
package so the `example.com/cgo` wrapper hash, and so `GoAdd`/`GoSum`, are unchanged.

### Runtime contracts and heap allocation (`NewPair`, `MakeSlice`, `AppendOne`, `SetNext`, `MallocFast`)

Extract with `--contract runtime.newobject` (see `scripts/example-contracts.sh`), state the theorem
about `Extracted.program.link impl` for every `impl` satisfying a contract hypothesis, and use the
hypothesis at the call with `calls [hnew.pos]` (docs/RUNTIME-CONTRACTS.md):

```lean
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (pre rt) post := by
  intro ret hret s hs ⟨…, hd, hout⟩
  janus_intro hs
  janus_data hd [hw]            -- also: the stack window is disjoint from the read-only data
  janus_run until [Extracted.entry + 0x34] calls [hnew.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 16 rt› hout   -- the object is fresh
  janus_run
  …
```

* After the call, the contract's postcondition is split into hypotheses and simplified: the
  returned pointer is a variable, with `InRanges ptr n rt`, alignment, `accessible` and
  `ZeroBytes` facts; memory is a `MemFrame` of the call-site memory.
* `Outside a n rt` side conditions (a read of the caller's stack through the contract's frame)
  are proved from the precondition's `Outside b k rt`; `janus_frame` peels stores into the fresh
  object (`InRanges`) and handles frames `rt ++ [ … ]`.
* Many disjointness facts make `omega` slow (it case-splits on every disjunction in the context).
  State them as `Apart a n b k` (or a `Spread` list of ranges): `omega` does not unfold `Apart`,
  and the dischargers try one relevant `Apart` hypothesis at a time (`janus_apart`).
  `MallocFast` relates eight objects (stack, `g`, `m`, `p`, `mcache`, `mspan`, the runtime
  globals, the slot) this way.

### Floating-point conversions and `min`/`max` (`I64ToF64`, `U64ToF64`, `F64ToI64`, `F64ToF32`, `MinF64`)

State results with the IEEE specifications of `Janus.Float.Convert` (`fromInt`, `convertFormat`,
`minimum`, `maximum`, and `truncInt`), and bridge the model with the per-ISA lemmas
(`Janus.Arm64.FP.fixedToFP_ieee`, `fpConvert_ieee`, `fpToFixed_rzs_*`, `fpMin_ieee`;
`Janus.Amd64.FP.ofInt_ieee`, `convert_ieee`, `toInt_rz64`, `minsd_seq`, `maxsd_seq`, `u64_big`).
After `janus_run`, the result register holds the model function's result under a few `% 2^k`;
bound it (`fromInt_lt`, the lemmas' `< 2^width` conjunct) and `omega` them away. Exactness facts
are separate theorems derived with `Ensures.mono` (`truncInt_fromInt`, `convertFormat_32_64`).
Rounding lemmas: `round_b64_normal` (exact rounding of a value with at most 53 bits),
`round_b64_bits` (the bits of a rounding in the normal range), `round_self64` (a finite encoding
rounds to itself). Two practical rules: never `unfold truncInt`/`classify` on a concrete format
inside a large context (state the fact for a generic `Fmt` and instantiate it, `truncInt_normal`),
and never `assumption`/`‹_›` for a branch hypothesis in a goal with large memory terms (the
defeq checks against every hypothesis can run for minutes): name it with `rename_i`.

### Contracts with satisfiability witnesses (`MinStr`)

A runtime function the code calls but the proof does not execute (`runtime.cmpstring`) becomes a
contract (`Janus/Contracts/Cmpstring.lean`, `…Amd64.lean`). Besides the contract, prove it
satisfiable (`Janus/Contracts/CmpstringSat*.lean`): write a small implementation in machine code
(assembled with `aarch64-linux-gnu-as`/`as` and copied as words/bytes), place it at a fixed
address of an otherwise empty program, and prove the `Summary` by the same symbolic execution
and loop induction as an example (the invariant is the state `{ s with regs := R, flags := F,
pc := head }`), then exhibit a call state satisfying the precondition. In the example, the
callee's read of memory written by the frames is shown unchanged with a frame lemma
(`strCmp_writeLE`, applied by `simp (disch := omega) only [...] at *`).
### Panics, defer and recover (`PanicIf`, `DeferInc`, `IndexAt`, `LoadField`, `DeferTwice`, `RecoverSet`)
### Panics, defer and recover (`PanicIf`, `DeferInc`, `IndexAt`, `LoadField`, `DeferTwice`, `RecoverSet`, `DeferOrder`, `DeferMix`, `GoexitDefer`, `RangeDefer`, `NestedPanic`, `NestedRecover`)

State a function that may panic as an `EnsuresGo` (docs/RUNTIME-CONTRACTS.md, "Panics, defer,
recover"): a postcondition for the return and one for the panic value, with the classification
`goClass P` for a panic-runtime model `P`:

```lean
theorem correctness (P : PanicRuntime) (x etyp edata : BitVec 64) :
    EnsuresGo Extracted.program Extracted.entry [x, etyp, edata]
      (fun s => GuardOK s 0 ∧ StackOK s 40 32) (fun _ => goClass P)
      (fun _ s' => x.toNat ≤ 10 → s'.regs 0 = x + 1)
      (fun _ v _ => 10 < x.toNat → v = ⟨etyp.toNat, edata.toNat⟩) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩⟩
  janus_intro hs
  refine GoReturns.of_reaches ?_      -- now an ordinary `Reaches` goal
  by_cases hx : x.toNat ≤ 10
  · janus_run; exact fun _ => trivial
  · janus_run                         -- ends at the gopanic stub; X0/X1 are the value
    refine ⟨⟨etyp.toNat, edata.toNat⟩, ?_, ?_⟩ …
```

* `GoReturns.of_reaches` turns the goal into `Reaches` whose stub/fault outcomes carry the
  `goClass` value: at `runtime.gopanic` the `any` in `X0`/`X1` (amd64 `RAX`/`RBX`), at a
  `runtime.panic*` stub `P.err k` (`IndexAt`: `P.boundsError`), at a memory fault below `0x1000`
  `P.err .mem` (`LoadField`: the run stops at the faulting load and the goal asks that the address
  is below `0x1000`). A function that never panics proves `fun _ _ _ => False` for the panic case,
  and every existing `Ensures` lifts with `Ensures.toGo`.
* **Heap defers** (`DeferTwice`): extract with `--contract 'runtime.deferproc*' --contract
  runtime.deferreturn` (`scripts/example-targets.sh`) and step over each `deferproc` call with
  `janus_run until [Extracted.program.contractAddr "runtime.deferproc"]` then
  `ReachesRet.call hdp rfl ⟨…⟩ ?_` (the precondition at a call site comes from
  `PanicCallerOK P s frame above` via `PanicPre.of_within`: the stack window and `P.Env` after the
  frame's own stores, by `janus_frame` and `hl.env_frame`). At the exit's `deferreturn`, name the
  call state (`ReachesRet.name`), compute the frame (`retFrame P S`) and its pending calls
  (`frameItems`: the records `deferproc` pushed, read off the `P.defers` facts the contracts gave),
  show `FrameOK` (the funcval readable, below `2^48`, outside the runtime's memory and the stack
  window), and `DeferreturnContract.apply hdr hpc ⟨hpre, hFO⟩` hands over the engine
  (`Engine_cons`): for each call take the `DeferCall` state, run the extracted closure to its
  return, turn that into `DeferReturned` (`DeferReturned.of_same` when the closure changed no
  memory) and continue with the engine's next clause until `Engine_nil` gives `RetFin`.
* **`recover`** (`RecoverSet`): the theorem takes the `gopanic`, `gorecover` and `deferreturn`
  contracts, the function table (`Extracted.funcs`, the funcdata the extractor read) and
  `¬ P.wrapper (pc)` for the closure's call to `gorecover`. At `gopanic`,
  `GopanicContract.apply hpan hpc hfind ⟨…⟩` hands over the engine for the frame
  (`frameOf fi sp m`, with the `deferBits` byte and slot of the open-coded defer); take the
  `DeferCall` state of the closure, run the extracted closure up to its call of `gorecover`
  (`ReachesRet.call hrec`), use the contract's panic-marking clause, finish the closure and feed
  its return state to the engine's `Recovers` clause; the resume state continues at the
  function's `deferreturn` call (a second `DeferreturnContract.apply`, with `P.saved` the
  defers `recovery` left pending).
* **Several defers, `Goexit`, nested panics** (`DeferOrder`, `DeferMix`, `GoexitDefer`,
  `RangeDefer`, `NestedPanic`, `NestedRecover`): the same engine; the order of the calls is
  `frameItems` (the open-coded defers' bits from the highest, then the records), proved by
  `simp [frameItems, openItems, recItems, fnItems]` after the memory facts are known. A closure
  that panics again takes `GopanicContract.apply` a second time inside its own `ReachesRet`: the
  inner engine ends in `LeftFrame` (`U`), which is the outer engine's nested clause's hypothesis
  (`hnest rfl d r2 …`). Split a long proof into lemma modules (the segment lemmas of a repeated
  closure are shared between `NestedPanic` and `NestedRecover`) to keep the compile loop short.
* **Code addresses as values** (the closure's entry, the return point after the call of `gorecover`,
  the resume site, the resume address a model `gopanic` loads) are written as
  `janus_eval% (segAddr Extracted.program "pkg.F.func1" + off)` / `janus_eval% (Extracted.entry +
  off)` (local macros in `RecoverSet`), never as literals, so a relinked binary needs no edit.
* **Opaque registers.** A contract's post state has an abstract register function `cr`; when the
  executor needs some of them concrete (the closure reads `X26`, the frame pointer), rewrite
  `cr` as `setReg` over itself with the known values first (`have : cr = fun i => if i = 26 then
  … else cr i`), so the executor sees them.
* The contract postconditions are curried in `ReachesRet.call` (`intro hpost _ hpanI`) but a
  conjunction in `Reaches.call` (`obtain ⟨⟨…⟩, h, -⟩`). Normalize stack addresses
  (`s.sp - 80 + 39 = s.sp - 41`) before `simp [Memory.readLE_writeLE_of_disjoint]`, and use
  `set_option maxHeartbeats 0 in` for the big recover proofs.
* **Non-vacuity**: `Proof.Witness.nonvacuous` instantiates every hypothesis at once (the model
  `PanicSat.P0`, model code at the contract addresses proved to meet each contract, a concrete
  call state) and `Proof.Witness.returns` applies the theorem to it; both are verified by
  `scripts/verify-examples.sh` when the proof has a `namespace Witness`.

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
* **Address side conditions without `omega`.** A read past a store asks whether the two byte
  ranges are disjoint or equal, a store whether its range is accessible. These are linear facts
  about `base + offset` with literal offsets. `Common.addrDisch` decides them directly (same
  base: a comparison of literals; different bases: one case split on an aliasing fact such as
  `z + 64 ≤ x ∨ x + 64 ≤ z`), with proofs from four small lemmas, and refutes the false ones
  (`x + 8 = x + 16`) without calling `omega` at all. An `omega` call and the kernel check of its
  proof cost 10-40 ms; a 300-instruction run asks for thousands of these facts.
* **Focused `omega`.** What `addrDisch` cannot decide goes to `omega` in the context restricted
  to the hypotheses that only mention variables of the goal, and only then to `omega` on the
  whole context (which also splits every unrelated aliasing disjunction).
* **Carry bounds by reflection.** The side conditions of `mod64_of_lt` on carry terms
  (`(… + p / 2^64) / 2^64 < 2^64`) are proved by `janus_carry` (`omega` cannot: it does not know
  the bound of a product), so the symbolic state keeps fewer `% 2^64`; bounds that do not hold
  for all limb values, about atoms no hypothesis mentions, are rejected without `omega`.
* **Accessibility hypotheses about the accessed pointer first.** `accessible` side conditions
  try the regions stated about the pointer of the access before the others.
* **`exec` unfolded definitionally, also when it is recursive.** `simp` unfolds a
  non-recursive definition in its simp set by delta reduction, with no proof term. A
  (structurally) recursive one is unfolded by rewriting with its equation lemmas `f.eq_<k>`,
  which Lean does not tag `@[defeq]`, so each unfolding is a propositional rewrite whose proof
  becomes part of the step proof. `janus_rfl_eqns f [simp_set]` (`Janus/Tactic/Common.lean`)
  restates every `f.eq_<k>` as `f.rfl_<k>` proved by `Eq.refl` (kernel-checked when it is
  added), tags it `@[defeq]` and puts it in the simp set; amd64 `exec` is unfolded that way.
  See the note below for what this cost.

* **Path merging (opt-in, `janus.merge`).** Each branch whose two sides survive doubles the
  work of every later instruction. With `set_option janus.merge true` the run waits for the
  paths of a forward diamond at the join and merges them (`Common.pickMerged`, `tryMerge`):
  the goals are anti-unified (register chains aligned by register, a register written on one
  side only becomes a variable whose other value is the base register, removed again by the
  register write-back simproc), memories must be identical, and the branch hypotheses not
  common to both are cleared. `MallocFast` goes from 12 paths to 2 (the preemption path stores
  `g.stackguard0`, so its memory differs), 433 steps to 167, and from 22.8 min to 2.5 min
  (with the `ldrsw` sign-extension lemmas of the proof).

**The amd64 post-processing regression (909b2ad, fixed).** The AVX/FS/DF merge made amd64
`exec` structurally recursive: `.locked i a size` checks the alignment and then executes `i`
with `exec` itself. Nothing else about the state or the step changed the cost (the extra
`State` fields, `ea`/`eaOff` and `h_df` were ruled out: a tree with `.locked` made
non-recursive and everything else as on `main` has the old cost). From then on the `simp` call
of every step unfolded `exec` by its equation lemmas instead of by delta reduction. The
resulting step proofs are not bigger as trees, but they lose sharing: the intermediate terms of
the rewrite chain (`Eq.trans`/`congrArg` over the `match` on the instruction's operands) carry
the current state as a separate copy that is not pointer-shared with the state in the goal, and
that copy grows with every step (measured with `Expr.numObjs` on amd64 `MulAdd8`: the proof of
step 84 had 250,732 distinct objects, of which a `State.mk` with 247,379, against 1,081 for
the state itself and 3,428 for the same proof with `exec` unfolded by delta; the step proofs
doubled about every 12 instructions). The `simp` of the run is not affected, but the final
`instantiateMVars` of the proof (abstracting the `intro`/`obtain` variables over it) and
`share common exprs` (hash-consing before the kernel) are linear in distinct objects, so they
grew exponentially with the length of the run: 0.035 s before the merge, 4-7 s for the 98
instructions of `MulAdd8`, ~240 s of the 292 s of `MulAdd8x3`, plus kernel time on the
unshared term, and memory: `lean` on `MulAdd8x3` peaked at 19.5 GB (2.35 GB with the fix, which
brings it from 281 s to 41 s; bench/RESULTS.md). With `exec.rfl_<k>` the unfolding carries no proof at all, the step proofs stay
at a few thousand objects, and the whole `MulAdd8` proof (run and arithmetic) spends 0.14 s in
`instantiate metavars` and 0.37 s in `share common exprs`, against 10.2 s and 17.5 s before
(same machine). To check for this kind of regression, compile the proof with
`set_option profiler true` and look at `instantiate metavars` and `share common exprs`: they
should be a small fraction of `simp` and `type checking`.

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
