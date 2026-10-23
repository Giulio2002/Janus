# Tutorial: your first Janus proof

This walks from an empty directory to a kernel-checked theorem about the arm64 machine code of a Go
function you wrote. Then it breaks the function and watches the proof fail, and finally proves two
functions that touch memory, one of which is only correct once you account for pointer aliasing.

Every command below was run, and every output is pasted as printed. Your SHA-256s and timings will
differ; addresses depend on what else is linked into the binary.

**You need:** Go 1.26, [elan](https://github.com/leanprover/elan) (it installs the Lean toolchain
Janus pins, 4.34.1), bubblewrap (`apt-get install -y bubblewrap`) for the proof sandbox, and
optionally `aarch64-linux-gnu-objdump` (package `binutils-aarch64-linux-gnu`) to read disassembly.

**Get `janus`.** Build it from a checkout and put it on your `PATH`:

```sh
git clone https://github.com/Giulio2002/Janus
cd Janus && go build -o bin/janus ./cmd/janus && export PATH=$PWD/bin:$PATH
```

The Janus Lean framework is embedded in the binary. The first `janus verify` builds it once under
`~/.cache/janus`; later runs reuse it.

---

## 1. Write a Go function

Make a fresh module, outside the Janus checkout:

```
clamp/
├── go.mod          module example.com/clamp
├── clamp.go
└── cmd/main.go
```

`clamp.go`:

```go
package clamp

// Clamp limits x to the range [lo, hi].
//
//go:noinline
func Clamp(x, lo, hi uint64) uint64 {
	if x < lo {
		return lo
	}
	if x > hi {
		return hi
	}
	return x
}
```

`//go:noinline` keeps `Clamp` a function of its own instead of being inlined into its callers. The Go
linker also drops functions nothing references, so `cmd/main.go` keeps it alive:

```go
// Command clamp keeps Clamp alive in the linked binary, so janus can find it.
package main

import (
	"os"

	"example.com/clamp"
)

var Keep = []any{clamp.Clamp}

func main() {
	n := uint64(len(os.Args))
	println(clamp.Clamp(n, 2, 5), len(Keep))
}
```

## 2. Build for arm64

Janus needs a non-PIE linux/arm64 executable. `CGO_ENABLED=0` gives you one on any host:

```console
$ CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -o clamp-arm64 ./cmd
$ janus list clamp-arm64 --filter example.com/clamp.
# clamp-arm64: example.com/clamp, go1.26.0, linux/arm64, functions from symtab
ADDRESS                SIZE  NAME
0x00000000000930c0       48  example.com/clamp.Clamp
```

## 3. Extract

```console
$ janus extract clamp-arm64 example.com/clamp.Clamp out/Clamp
Extracted example.com/clamp.Clamp: 1 function(s), 9 word(s), 0 stub(s), 0 data object(s) (0 bytes) into out/Clamp/Extracted.lean
  code  0x930c0    9 words  example.com/clamp.Clamp
```

`out/Clamp/Extracted.lean` is the program your theorem is about. It contains raw words, nothing
decoded:

```lean
def segments : List Segment := [
  { name := "example.com/clamp.Clamp", base := 0x930c0, words := [
      0xeb00003f, 0x540000c8, 0xeb00005f, 0x54000062, 0xaa0203e0, 0xd65f03c0, 0xd65f03c0, 0xaa0103e0,
      0xd65f03c0] } ]

def stubs : List Stub := []
...
def entry : Nat := 0x930c0
```

`out/Clamp/identity.json` records the binary's SHA-256 and the hash of `Extracted.lean`, so a stale or
edited extraction is caught. Before writing a proof, look at what the compiler actually emitted:

```console
$ aarch64-linux-gnu-objdump -d clamp-arm64 --disassemble=example.com/clamp.Clamp
00000000000930c0 <example.com/clamp.Clamp>:
   930c0:	eb00003f 	cmp	x1, x0
   930c4:	540000c8 	b.hi	930dc <example.com/clamp.Clamp+0x1c>  // b.pmore
   930c8:	eb00005f 	cmp	x2, x0
   930cc:	54000062 	b.cs	930d8 <example.com/clamp.Clamp+0x18>  // b.hs, b.nlast
   930d0:	aa0203e0 	mov	x0, x2
   930d4:	d65f03c0 	ret
   930d8:	d65f03c0 	ret
   930dc:	aa0103e0 	mov	x0, x1
   930e0:	d65f03c0 	ret
```

No stack frame, no stack-growth check, no calls, three exits. The arguments arrive in `X0`, `X1`,
`X2` (Go's register ABI) and the result leaves in `X0`.

## 4. State the specification

`proofs/Clamp.lean`:

```lean
import Extracted

/-!
# `Clamp(x, lo, hi uint64) uint64`

For all 64-bit `x`, `lo`, `hi` and every Go call of the compiled function, the code returns
(no fault, no panic, no infinite loop), obeys the ABI, and leaves in `X0` exactly what the Go
source says: `lo` if `x < lo`, otherwise `hi` if `x > hi`, otherwise `x` (unsigned).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (x lo hi : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, lo, hi] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat =
        if x.toNat < lo.toNat then lo.toNat
        else if hi.toNat < x.toNat then hi.toNat
        else x.toNat) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
```

Read the statement before the proof; it is the only part you have to trust.
`Ensures p entry args pre post` says: for **every** admissible return address `ret` and **every**
machine state `s` that is a Go call of `entry` with `args` in `X0, X1, …` and `ret` in `X30`, with
everything else (other registers, flags, `SP`, all of memory) arbitrary, and with `pre s` holding,
the code reaches `ret` after finitely many instructions, restores `SP`, `X18`, `X28` and `X29`, and
`post s s'` holds of the final state. A fault or a panic is not a return, so `Ensures` rules both out.

The postcondition is written on `toNat` (natural numbers), which is what `omega` reasons about. The
precondition is `True`: `Clamp` touches no memory, so it needs nothing from the caller.

## 5. Prove it with `janus_run`

The proof so far is three tactics:

* `intro ret hret s hs _` takes the return address, the call state and its hypotheses;
* `janus_intro hs` turns the call setup into rewrite rules (`h_pc : s.pc = 602304#64`,
  `h_x0 : s.regs 0 = x`, …);
* `janus_run` executes the code symbolically. At each `pc` it fetches the word, decodes it **in
  Lean**, and simplifies one step. At each conditional branch it splits the goal and records the
  condition as `hbr`. When a path reaches `ret`, the goal becomes the postcondition.

Ask `janus verify` what is left:

```console
$ janus verify out/Clamp --proof proofs/Clamp.lean
Invalid: Lean rejected the proof proofs/Clamp.lean.
Lean errors (1):
  proofs/Clamp.lean:20:25: error: unsolved goals
    case h₂.h₁
    x lo hi : BitVec 64
    ret : Nat
    hret : RetAddr Extracted.program ret
    s : State
    hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, lo, hi] s
    a✝ : True
    h_pc : s.pc = 602304#64
    h_lr : s.regs 30 = BitVec.ofNat 64 ret
    h_x0 : s.regs 0 = x
    h_x1 : s.regs 1 = lo
    h_x2 : s.regs 2 = hi
    hbr✝ : ¬x.toNat < lo.toNat
    hbr : x.toNat ≤ hi.toNat
    ⊢ x.toNat = if hi.toNat < x.toNat then hi.toNat else x.toNat
    
    case h₂.h₂
    ...
    hbr✝ : ¬x.toNat < lo.toNat
    hbr : ¬x.toNat ≤ hi.toNat
    ⊢ hi.toNat = if hi.toNat < x.toNat then hi.toNat else x.toNat
  Stage: proof checking
  Next: Fix the proof. It must import Extracted (and Janus) and prove Proof.correctness.
```

(The full output repeats the Lean messages under `Details:`.) This is what symbolic execution looks
like from the inside. The compiler's `cmp x1, x0; b.hi` became the hypothesis
`¬x.toNat < lo.toNat`, and `cmp x2, x0; b.cs` became `x.toNat ≤ hi.toNat` or its negation. The
`x < lo` path was closed automatically. Two paths remain, and each needs one `if` resolved by
arithmetic. Add one line after `janus_run`:

```lean
  janus_run
  all_goals split <;> omega
```

## 6. Verify

```console
$ janus verify out/Clamp --proof proofs/Clamp.lean
Verified: Proof.correctness
  Module: example.com/clamp (go1.26.0)
  Entry: example.com/clamp.Clamp at 0x930c0
  Binary: clamp-arm64 (SHA-256 c17609a1861edbea49171cfc27ad02d59f96e5c8cfa3d9f3b2705712b9050e79)
  Proof: proofs/Clamp.lean
  Framework: embedded (SHA-256 e9be8cd3d7116073ba456dd933bd277edd8d3ce37bf8acb842c28f43decccbba, 30 files, leanprover/lean4:v4.34.1)
  Sandbox: bubblewrap (no network, read-only filesystem, private build dir)
  Axioms: Classical.choice, Quot.sound, propext
  Kernel replay: leanchecker passed (Janus, Extracted, Proof)
  Lean: Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)
  Report: out/Clamp/verified.json
  Statement:
    Proof.correctness (x lo hi : BitVec 64) : Janus.GoABI.Ensures Extracted.program Extracted.entry [x, lo, hi] (fun x => True) fun x_1 s' => BitVec.toNat (s'.regs 0) = if x.toNat < lo.toNat then lo.toNat else if hi.toNat < x.toNat then hi.toNat else x.toNat
```

That took 26 s with a warm framework cache. In that time `janus verify`:

1. re-extracted the words from `clamp-arm64` (checked by SHA-256) and byte-compared them with
   `out/Clamp/Extracted.lean`;
2. compiled your proof in a bubblewrap sandbox (no network, read-only filesystem);
3. audited the theorem with the trusted `janus-audit` routine, which loads your compiled proof as data
   and never runs code from it: the
   theorem exists, the imported `Extracted` is the one just checked, the axioms are on the allow-list;
4. replayed `Janus`, `Extracted` and `Proof` through `leanchecker`;
5. printed the statement in a clean environment, so what you read is what was checked.

`janus explain` turns the report into prose and re-checks every hash against the files on disk:

<details>
<summary><code>janus explain out/Clamp</code></summary>

```console
$ janus explain out/Clamp
Verification report out/Clamp/verified.json

What was proved
  The Lean kernel accepted theorem Proof.correctness, declared in module Proof:

    Proof.correctness (x lo hi : BitVec 64) : Janus.GoABI.Ensures Extracted.program Extracted.entry [x, lo, hi] (fun x => True) fun x_1 s' => BitVec.toNat (s'.regs 0) = if x.toNat < lo.toNat then lo.toNat else if hi.toNat < x.toNat then hi.toNat else x.toNat

  The guarantee is exactly this statement, with its hypotheses and quantifiers. Its
  Extracted.* names denote the machine code copied from the binary below; nothing else
  about the program is claimed.

About which code
  Function: example.com/clamp.Clamp, entry address 0x930c0
  Program: Go module example.com/clamp, built with go1.26.0 for linux/arm64
  Binary: clamp-arm64
  Extracted code: 1 function(s): example.com/clamp.Clamp @ 0x930c0
  Read-only data copied: 0 object(s), 0 byte(s); writable data referenced but not copied: 0

How it was checked
  Axioms used: Classical.choice, Quot.sound, propext (allowed: propext, Quot.sound, Classical.choice)
  Kernel replay: leanchecker re-checked Janus, Extracted, Proof
  Lean: Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)
  Janus framework: embedded, 30 files, SHA-256 e9be8cd3d7116073ba456dd933bd277edd8d3ce37bf8acb842c28f43decccbba (665fb6962628efcaaa77d14cc431d09db5b5d0d1, modified)
  Extractor: janus 0.2.0
  Verified at: 2026-10-23T14:43:14Z

Hashes (SHA-256), and whether the files on disk still match
  binary          c17609a1861edbea49171cfc27ad02d59f96e5c8cfa3d9f3b2705712b9050e79  matches  clamp-arm64
  Extracted.lean  062484b0de0e98e71f5bca81c71519497a86989006a0901f377ab61e82ee3d66  matches  out/Clamp/Extracted.lean
  identity.json   79fe4b01db15296a2e880cb3c93ed93a4572505cc90f09473ac3a40edf1a168c  matches  out/Clamp/identity.json
  proof           40ceee8c5307691f7bad26f20eed0abc8d57197bc62d94a7b86fa93abf84a90c  matches  proofs/Clamp.lean

To re-establish the result, rerun janus verify; janus check out/Clamp re-checks the extraction alone.
```

The build is reproducible (`-trimpath`): rebuilding the same source gives the same SHA-256, so the
report keeps matching.
</details>

## 7. Break it and watch it fail

### A harmless edit still verifies

Change `if x > hi {` to `if x >= hi {`. When `x = hi` the function now returns `hi` instead of `x`,
which is the same value. Rebuild and re-extract. The compiler emits a different branch
(`54000068 b.hi` instead of `54000062 b.cs`), yet the **unchanged** proof still goes through,
because the theorem is about what the code computes, not how it is written:

```console
$ CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -o clamp-arm64 ./cmd
$ janus extract clamp-arm64 example.com/clamp.Clamp out/Clamp >/dev/null
$ janus verify out/Clamp --proof proofs/Clamp.lean 2>&1 | head -1
Verified: Proof.correctness
```

### A real bug does not

Now make a typo a reviewer could easily miss, comparing against `lo` instead of `hi`:

```go
func Clamp(x, lo, hi uint64) uint64 {
	if x < lo {
		return lo
	}
	if x > lo {
		return hi
	}
	return x
}
```

Rebuild, and first try to verify without re-extracting:

```console
$ CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -o clamp-arm64 ./cmd
$ janus verify out/Clamp --proof proofs/Clamp.lean
Invalid: Binary changed since extraction: clamp-arm64 has SHA-256 4a57c8d827eb00c651e72112584b3b8c7f0f771e7a6f12b929c18a563ad6aed6, identity.json records a64f4d7d25c1034f00d3d5fe95026602aa266953937218b647f30807998e5ace.
  Stage: binary identity
  Next: Rerun janus extract clamp-arm64 "example.com/clamp.Clamp" out/Clamp with the intended binary, then rerun this command.
```

An old proof never silently carries over to a new binary. The failed run also withdrew the previous
`verified.json`, so `out/Clamp` now holds only `Extracted.lean` and `identity.json`. Re-extract and
verify the same proof:

```console
$ janus extract clamp-arm64 example.com/clamp.Clamp out/Clamp
Extracted example.com/clamp.Clamp: 1 function(s), 8 word(s), 0 stub(s), 0 data object(s) (0 bytes) into out/Clamp/Extracted.lean
  code  0x930c0    8 words  example.com/clamp.Clamp
$ janus verify out/Clamp --proof proofs/Clamp.lean
Invalid: Lean rejected the proof proofs/Clamp.lean.
Lean errors (2):
  proofs/Clamp.lean:24:22: error: omega could not prove the goal:
    a possible counterexample may satisfy the constraints
      0 ≤ b ≤ 18446744073709551615
      0 ≤ a ≤ 18446744073709551615
      a - b ≥ 1
    where
     a := ↑lo.toNat
     b := ↑hi.toNat
  proofs/Clamp.lean:24:22: error: omega could not prove the goal:
    a possible counterexample may satisfy the constraints
      0 ≤ c ≤ 18446744073709551615
      0 ≤ b ≤ 18446744073709551615
      0 ≤ a ≤ 18446744073709551615
      a - b ≥ 1
      a - c ≤ -1
    where
     a := ↑x.toNat
     b := ↑lo.toNat
     c := ↑hi.toNat
  Stage: proof checking
  Next: Fix the proof. It must import Extracted (and Janus) and prove Proof.correctness.
```

`omega` hands you the counterexample. The second one reads `x > lo` and `x < hi`: a value strictly
inside the range, which the buggy code clamps to `hi`. The proof failed on exactly the path the bug
is on. (A failed proof alone is not a disproof. To show that a binary violates a spec, prove the
negation, as [`examples/proofs/WrongAdd.lean`](../examples/proofs/WrongAdd.lean) does for a
subtracting `Add`.)

Restore `if x > hi {` before going on.

## 8. Touching memory: pointers and aliasing

Add two functions to `clamp.go`:

```go
// AddTo adds *src to *dst. dst and src may point to the same word.
//
//go:noinline
func AddTo(dst, src *uint64) { *dst += *src }

// AddTwice adds *src to *dst twice.
//
//go:noinline
func AddTwice(dst, src *uint64) {
	*dst += *src
	*dst += *src
}
```

and keep them alive in `cmd/main.go`:

```go
var Keep = []any{clamp.Clamp, clamp.AddTo, clamp.AddTwice}

func main() {
	n := uint64(len(os.Args))
	a, b := n, n+1
	clamp.AddTo(&a, &b)
	clamp.AddTwice(&a, &b)
	println(clamp.Clamp(n, 2, 5), a, len(Keep))
}
```

```console
$ CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -o clamp-arm64 ./cmd
$ janus extract clamp-arm64 example.com/clamp.AddTo out/AddTo
Extracted example.com/clamp.AddTo: 1 function(s), 5 word(s), 0 stub(s), 0 data object(s) (0 bytes) into out/AddTo/Extracted.lean
  code  0x930f0    5 words  example.com/clamp.AddTo
$ janus extract clamp-arm64 example.com/clamp.AddTwice out/AddTwice
Extracted example.com/clamp.AddTwice: 1 function(s), 8 word(s), 0 stub(s), 0 data object(s) (0 bytes) into out/AddTwice/Extracted.lean
  code  0x93110    8 words  example.com/clamp.AddTwice
```

### Memory in the model

A Janus state's memory is a byte map plus the list of **regions** the caller owns. Every load and
store must lie entirely inside one region below `2^48` (and a writable one, for a store), or the step
faults. So a theorem about pointer code must say which memory the caller provides. The vocabulary is
in `Janus.Spec`:

* `Ptr m p n w`: the `n` bytes at `p` lie in one region of `m`, writable if `w`, below `2^48`;
* `Disjoint p n q k`: the byte ranges `[p, p+n)` and `[q, q+k)` do not overlap;
* `OnlyWrites m m' p n`: `m'` equals `m` outside `[p, p+n)`, with the same regions;
* `m.readLE a n`: the little-endian value of the `n` bytes at `a`.

There is no "nil" special case. A nil pointer is address 0, which lies in no region, so a
dereference faults, as it does on hardware, where it is a `SIGSEGV` that Go turns into a panic.
`Ptr` rules that out for the caller.

### `AddTo`: no aliasing assumption needed

```console
$ aarch64-linux-gnu-objdump -d clamp-arm64 --disassemble=example.com/clamp.AddTo
00000000000930f0 <example.com/clamp.AddTo>:
   930f0:	f9400002 	ldr	x2, [x0]
   930f4:	f9400021 	ldr	x1, [x1]
   930f8:	8b010041 	add	x1, x2, x1
   930fc:	f9000001 	str	x1, [x0]
   93100:	d65f03c0 	ret
```

Both loads happen before the store, so the result does not depend on whether `dst` and `src`
overlap. The theorem can say so: it has no aliasing hypothesis at all.

`proofs/AddTo.lean`:

```lean
import Extracted

/-!
# `AddTo(dst, src *uint64)` adds `*src` to `*dst`

For every Go call with `dst` pointing to 8 writable bytes and `src` to 8 readable bytes (the two
may be equal, overlap partially, or be disjoint), the code returns (no fault, no panic), and
afterwards the word at `dst` is the sum of the two words *before* the call, modulo `2^64`.
No other byte changes.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (dst src : BitVec 64) :
    Ensures Extracted.program Extracted.entry [dst, src]
      (fun s => Ptr s.mem dst 8 true ∧ Ptr s.mem src 8 false)
      (fun s s' =>
        s'.mem.readLE dst.toNat 8 = (s.mem.readLE dst.toNat 8 + s.mem.readLE src.toNat 8) % 2 ^ 64 ∧
        OnlyWrites s.mem s'.mem dst.toNat 8) := by
  intro ret hret s hs ⟨⟨hd, hd'⟩, ⟨hsrc, hsrc'⟩⟩
  janus_intro hs
  janus_run
  janus_arith

end Proof
```

The precondition is destructured into hypotheses (`hd : s.mem.accessible dst.toNat 8 true = true`,
`hd' : dst.toNat + 8 ≤ 2^48`, …): these are exactly the facts the executor needs to show each load
and store stays in bounds. `janus_arith` is `omega` with range facts about memory reads added.

```console
$ janus verify out/AddTo --proof proofs/AddTo.lean
Verified: Proof.correctness
  Module: example.com/clamp (go1.26.0)
  Entry: example.com/clamp.AddTo at 0x930f0
  Binary: clamp-arm64 (SHA-256 e50d52e33b73559f53723f55f77ef5015e3a8b9ddd20079ba03a4f127e1af4db)
  Proof: proofs/AddTo.lean
  Framework: embedded (SHA-256 e9be8cd3d7116073ba456dd933bd277edd8d3ce37bf8acb842c28f43decccbba, 30 files, leanprover/lean4:v4.34.1)
  Sandbox: bubblewrap (no network, read-only filesystem, private build dir)
  Axioms: Classical.choice, Quot.sound, propext
  Kernel replay: leanchecker passed (Janus, Extracted, Proof)
  Lean: Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)
  Report: out/AddTo/verified.json
  Statement:
    Proof.correctness (dst src : BitVec 64) : Janus.GoABI.Ensures Extracted.program Extracted.entry [dst, src] (fun s => Janus.Spec.Ptr s.mem dst 8 true ∧ Janus.Spec.Ptr s.mem src 8 false) fun s s' => s'.mem.readLE dst.toNat 8 = (s.mem.readLE dst.toNat 8 + s.mem.readLE src.toNat 8) % 2 ^ 64 ∧ Janus.Spec.OnlyWrites s.mem s'.mem dst.toNat 8
```

(The binary SHA-256 differs from section 6 because the binary now contains the new functions. The
proof for `Clamp` would have to be re-verified against it.)

### `AddTwice`: where aliasing matters

```console
$ aarch64-linux-gnu-objdump -d clamp-arm64 --disassemble=example.com/clamp.AddTwice
0000000000093110 <example.com/clamp.AddTwice>:
   93110:	f9400002 	ldr	x2, [x0]
   93114:	f9400023 	ldr	x3, [x1]
   93118:	8b020062 	add	x2, x3, x2
   9311c:	f9000002 	str	x2, [x0]
   93120:	f9400021 	ldr	x1, [x1]
   93124:	8b010041 	add	x1, x2, x1
   93128:	f9000001 	str	x1, [x0]
   9312c:	d65f03c0 	ret
```

The compiler **reloads** `*src` after storing to `*dst` (`ldr x1, [x1]` at `0x93120`), because the two
may be the same word. The obvious specification, "`*dst` becomes `d + 2·s`", forgets that. Try it:

```lean
theorem correctness (dst src : BitVec 64) :
    Ensures Extracted.program Extracted.entry [dst, src]
      (fun s => Ptr s.mem dst 8 true ∧ Ptr s.mem src 8 false)
      (fun s s' =>
        s'.mem.readLE dst.toNat 8 =
          (s.mem.readLE dst.toNat 8 + 2 * s.mem.readLE src.toNat 8) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hd, hd'⟩, ⟨hsrc, hsrc'⟩⟩
  janus_intro hs
  janus_run
  janus_arith
```

```console
$ janus verify out/AddTwice --proof proofs/AddTwice.lean
Invalid: Lean rejected the proof proofs/AddTwice.lean.
Lean errors (1):
  proofs/AddTwice.lean:16:2: error: omega could not prove the goal:
    a possible counterexample may satisfy the constraints
      0 ≤ e ≤ 18446744073709551615
      0 ≤ d ≤ 18446744073709551615
      0 ≤ c ≤ 18446744073709551615
      c - e - 18446744073709551616*f + 18446744073709551616*g ≥ 1
      0 ≤ c + d + e - 18446744073709551616*g ≤ 18446744073709551615
      0 ≤ 2*c + d - 18446744073709551616*f ≤ 18446744073709551615
      0 ≤ b ≤ 281474976710648
      0 ≤ a ≤ 281474976710648
    where
     a := ↑dst.toNat
     b := ↑src.toNat
     c := ↑(s.mem.readLE src.toNat 8)
     d := ↑(s.mem.readLE dst.toNat 8)
     e := ↑((s.mem.writeLE dst.toNat 8 (s.mem.readLE src.toNat 8 + s.mem.readLE dst.toNat 8)).readLE src.toNat 8)
     ...
  Stage: proof checking
  Next: Fix the proof. It must import Extracted (and Janus) and prove Proof.correctness.
```

Look at `e`: it is the second read of `src`, taken **after** the write to `dst`
(`(s.mem.writeLE dst …).readLE src …`). Nothing in the precondition says whether those two addresses
overlap, so the executor cannot simplify it, and the arithmetic does not close. The spec is in fact
wrong: when `dst = src = p` and `*p = d`, the first `+=` makes it `2d` and the second makes it `4d`,
not `3d`.

Two `*uint64` in Go are either the same pointer or do not overlap at all. Say that, give the honest
result for both cases, and split on it before running:

```lean
import Extracted

/-!
# `AddTwice(dst, src *uint64)`: `*dst += *src` twice, with aliasing

If `dst` and `src` are disjoint, `*dst` ends up as `d + 2·s`. If they are the same pointer, the
first addition doubles the shared word and the second doubles it again: `4·d`. (Partial overlap
of two `*uint64` is impossible in Go, so equal-or-disjoint is the honest precondition.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (dst src : BitVec 64) :
    Ensures Extracted.program Extracted.entry [dst, src]
      (fun s => Ptr s.mem dst 8 true ∧ Ptr s.mem src 8 false ∧
        (dst = src ∨ Disjoint dst.toNat 8 src.toNat 8))
      (fun s s' =>
        s'.mem.readLE dst.toNat 8 =
          (if dst = src then 4 * s.mem.readLE dst.toNat 8
           else s.mem.readLE dst.toNat 8 + 2 * s.mem.readLE src.toNat 8) % 2 ^ 64 ∧
        OnlyWrites s.mem s'.mem dst.toNat 8) := by
  intro ret hret s hs ⟨⟨hd, hd'⟩, ⟨hsrc, hsrc'⟩, halias⟩
  janus_intro hs
  -- one symbolic run per aliasing case
  rcases halias with rfl | hdis
  · janus_run
    janus_arith
  · have hne : dst ≠ src := by
      intro h; subst h; simp only [Disjoint] at hdis; omega
    simp only [Disjoint] at hdis
    janus_run [if_neg hne]
    janus_arith

end Proof
```

In the first case `rfl` substitutes `src := dst`, so the second read is a read of the word just
written, which simplifies to the stored value. In the second case `hdis` is plain arithmetic
(`dst + 8 ≤ src ∨ src + 8 ≤ dst`), and the executor uses it to step the read past the write.
`janus_run [if_neg hne]` adds one extra rewrite to the simp set, to resolve the `if`.

```console
$ janus verify out/AddTwice --proof proofs/AddTwice.lean
Verified: Proof.correctness
  Module: example.com/clamp (go1.26.0)
  Entry: example.com/clamp.AddTwice at 0x93110
  Binary: clamp-arm64 (SHA-256 18559cd7e317c002dddf3ce025ce3cde4fae22a4e929926b2da0dfd812e134a3)
  Proof: proofs/AddTwice.lean
  Framework: embedded (SHA-256 e9be8cd3d7116073ba456dd933bd277edd8d3ce37bf8acb842c28f43decccbba, 30 files, leanprover/lean4:v4.34.1)
  Sandbox: bubblewrap (no network, read-only filesystem, private build dir)
  Axioms: Classical.choice, Quot.sound, propext
  Kernel replay: leanchecker passed (Janus, Extracted, Proof)
  Lean: Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)
  Report: out/AddTwice/verified.json
  Statement:
    Proof.correctness (dst src : BitVec 64) : Janus.GoABI.Ensures Extracted.program Extracted.entry [dst, src] (fun s => Janus.Spec.Ptr s.mem dst 8 true ∧ Janus.Spec.Ptr s.mem src 8 false ∧ (dst = src ∨ Janus.Spec.Disjoint dst.toNat 8 src.toNat 8)) fun s s' => s'.mem.readLE dst.toNat 8 = (if dst = src then 4 * s.mem.readLE dst.toNat 8 else s.mem.readLE dst.toNat 8 + 2 * s.mem.readLE src.toNat 8) % 2 ^ 64 ∧ Janus.Spec.OnlyWrites s.mem s'.mem dst.toNat 8
```

The theorem now covers `AddTwice(&a, &a)` and pins down exactly what it does.

## Where to go next

* [PROOFS.md](PROOFS.md): every tactic, the stack-growth prologue and panics (`Div`, `Get`), loops
  by induction (`Sum`, `CopyWords`), callee summaries (`AddThree`), and `.rodata` (`HexDigit`).
* [SOUNDNESS.md](SOUNDNESS.md): what the statement you just read does and does not promise.
* [AMD64.md](AMD64.md): the same workflow for `GOARCH=amd64` (`janus64_intro`, `janus64_run`).
* [CONSUMERS.md](CONSUMERS.md): keep your proofs in a Lake package of their own (`janus init`).

**Tip, iterating faster.** `janus verify` re-does the whole pipeline every time (about 25 s here).
While developing, you can compile the extraction and your proof with Lean directly to see goals in
seconds, from the Janus checkout:

```sh
mkdir -p /tmp/b
LEAN_PATH=/tmp/b lake env lean --root=$HOME/clamp/out/Clamp -o /tmp/b/Extracted.olean $HOME/clamp/out/Clamp/Extracted.lean
LEAN_PATH=/tmp/b lake env lean --root=$HOME/clamp/proofs $HOME/clamp/proofs/Clamp.lean
```

`--root` is needed when the files live outside the checkout. Only `janus verify` produces a
`verified.json`.
