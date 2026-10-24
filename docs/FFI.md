# FFI: proving Go code that calls C (cgo)

Janus proves theorems about cgo programs on both arm64 and amd64. The C code is machine code in
the same ELF binary (compiled by gcc, linked by the external linker), and Janus verifies it
**directly**, like the Go code: it copies the bytes and runs them in the same Lean ISA model.
The only part taken on trust is the `runtime.cgocall` stack and scheduler switch, stated as an
explicit contract. This page covers the C calling conventions, extraction, the contract
semantics, the composition theorem and the examples. What exactly stays trusted is in
[SOUNDNESS.md](SOUNDNESS.md) ("FFI") and in [RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md)
("FFI (cgo)").

## 1. The C calling conventions (`Janus/CABI.lean`, `Janus/Amd64/CABI.lean`)

| | arm64 (AAPCS64, Linux) | amd64 (System V psABI) |
|---|---|---|
| integer arguments | `X0`–`X7` | `RDI RSI RDX RCX R8 R9` |
| results | `X0` (`X1`) | `RAX` (`RDX`) |
| callee-saved | `X19`–`X28`, `X29` (FP), `SP` | `RBX RBP R12 R13 R14 R15`, `RSP` (popped: entry `+ 8`) |
| return address | `X30` | `[RSP]` |
| stack alignment at the call | `SP mod 16 = 0` | `(RSP + 8) mod 16 = 0` |
| below the stack pointer | no red zone | 128-byte red zone |
| flags | — | `DF` clear at call and return |

`CCall p entry args s` is the C call state (as `GoABI.CallSetup` is for Go); `CReturn s₀ s₁` the
obligations on return (`SP`/`RSP` and the callee-saved registers, `DF` on amd64); and

```lean
def CEnsures (p : Program) (entry : Nat) (args : List W64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ ret, GoABI.RetAddr p ret → ∀ s, CCall (p.withExit ret) entry args s → pre s →
    GoABI.Returns (p.withExit ret) s (fun s' => CReturn s s' ∧ post s s')
```

is the analogue of `GoABI.Ensures`: for every admissible return address and every C call state
satisfying `pre`, the call returns (never faults), restores what AAPCS64 / System V require, and
satisfies `post`. `CStack s below above` is the C stack window. A C function is often easiest to
prove as a callee `Summary` (usable at the call sites of other C functions, like the cgo wrapper)
and turned into a `CEnsures` with `FFI.CEnsures.of_summary` (`examples/proofs-cgo/*/CSum.lean`).

The vector registers callee-saved by AAPCS64 (`V8`–`V15` low halves) and the x87/MXCSR control
state are not in `CReturn`: no supported instruction of integer C code touches them, and the
model has no floating point.

## 2. Extraction

`janus extract` works on a C symbol (`janus extract bin c_sum out`): cgo binaries are Go
executables (`buildinfo`, `ET_EXEC`: `go build` links non-PIE with `-no-pie`), and gcc's functions
are ordinary `STT_FUNC` symbols in `.text`. Reachability follows the C code's direct calls.

From a Go function, the extractor follows the cgo boundary:

* `runtime.cgocall`, `_cgo_topofstack` and `runtime.cgoUse` are **external stubs**
  (`Janus.StubKind.external`): not copied, and a run ends there unless a contract (below) says how
  it continues.
* The code `_Cfunc_f` loads the cgo function-pointer variable `pkg._cgo_<hash>_Cfunc_f` (in
  `.data`, initialised to the address of the C wrapper). The extractor follows that data
  reference to the wrapper `_cgo_<hash>_Cfunc_f`, and from there to `f`. So one extraction of a Go
  function contains the Go code, the C wrapper and the C function, which is what the end-to-end
  theorem needs. This is reachability, untrusted like branch following.
* The dead `if _Cgo_always_false` branch of every cgo wrapper calls `runtime.convT64` (an
  allocation). Pass `--contract runtime.convT64` (the runtime-contracts option) so it is not
  followed. The proofs show the branch is never taken, so no contract hypothesis is needed for it.
* libc functions called from C would be handled the same way: `--contract SYM` and a contract
  hypothesis (see [RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md)). The examples call none.

## 3. Contracts for external stubs (`Janus.FFI`, `Janus.Amd64.FFI`)

A `Contract` gives every external stub `f` a predicate `safe f s` ("calling `f` here returns")
and a relation `next f s s'` ("`s'` is a possible state after the return"). `ReturnsC p C post s`
is total correctness through contracts: every run from `s` reaches the exit address satisfying
`post` after finitely many steps; at an external stub, `C.safe` must hold and the run continues
from **every** state `C.next` allows. `EnsuresC p C entry args pre post` and
`CEnsuresC p C entry args pre post` are `Ensures` and `CEnsures` with `ReturnsC`.
`janus_run`/`janus64_run` drive these goals through `ReturnsC.of_reaches`. At an external stub
the goal becomes `C.safe f S ∧ ∀ s', C.next f S s' → ReturnsC …`; prove `safe`, introduce `s'`,
and continue with `apply ReturnsC.of_reaches; janus_run`.

`Contract.Refines C₁ C₂` (`C₁` allows at least the calls `C₂` allows, with fewer results) makes
every `ReturnsC`/`EnsuresC` under `C₂` hold under `C₁` (`EnsuresC.refine`).

**Why not a `Summary` hypothesis.** A `Summary p addr pre post` about the extracted program at
the address of `cgocall`, where there is no code, is false (or only vacuously true), so a theorem
assuming it could prove anything. The cgo contract has to *run the C code in the model*, which a
summary about unknown linked code cannot express either. So the boundary is a separate semantics,
and the only way to remove a Go-side assumption is a refinement proof.

## 4. The cgo contracts

* **`CgoSpec fn G E`, the Go-side assumption.** It appears in the statement of a Go-side
  theorem: "`cgocall` with `X0`/`RAX = fn` (the C wrapper), in a state satisfying `G`, returns to
  the caller (`GoResume`: return address; `SP`, `g` and `FP` restored, plus `X15 = 0`, `DF` clear
  and the TLS `g` slot on amd64; everything else arbitrary). The memory agrees with `E s`
  everywhere outside `cgoClobber s`." `cgoClobber s` is the goroutine stack below `SP`, the spill
  slots of `cgocall`'s arguments, the `g` struct and the TLS `g` slot.
* **`CgoCall p`, the trusted contract.** For every C call state `asmcgocall` may make
  (`CgoEntry`: the C ABI call of `fn` with `X0`/`RDI = arg`, on a system stack that is not Go
  memory, with the Go memory the runtime leaves alone unchanged and as accessible), every return
  address, and every value `T` of `_cgo_topofstack`: the C code at `fn`, **run by the model on
  `p`** under `TopOfStack T`, returns with `CReturn`. The possible results are the Go states
  resumed from the final C states (`CgoResumed`: the C code's writes to Go memory are kept; the
  clobbered bytes are arbitrary).
* **`TopOfStack T`.** `_cgo_topofstack` (Go assembly called by the cgo wrapper) returns `T`, the
  same value on every call of one cgo call. It preserves every other register and writes only its
  own frame.

**The composition theorem** `CgoCall.refines` (both ISAs) turns a proved C side into a refinement:

```lean
theorem CgoCall.refines
    (hC : ∀ T a, CEnsuresC p (TopOfStack T) fn [a] (pre a) (post a))   -- the C wrapper, proved
    (hpre : ∀ s t ret, G s → CgoEntry p s t ret → pre (s.regs 1) t)     -- G gives the C precondition
    (hE : ∀ s, G s → (E s).regions = s.mem.regions)
    (hacc : …post on Go memory is E…) (hna : …E leaves inaccessible bytes alone…) :
    (CgoCall p).Refines (CgoSpec fn G E)
```

so a Go-side theorem `EnsuresC p (CgoSpec fn G E) …` plus the wrapper's `CEnsuresC` gives
`EnsuresC p (CgoCall p) …`. In that theorem, every Go and C instruction is executed by the model,
and only `CgoCall`/`TopOfStack` remain assumed.

## 5. Examples (`examples/cgo`, `examples/proofs-cgo`)

`examples/cgo` is its own Go module. `cfuncs.c` defines `c_add`, `c_sum` (a loop over an array)
and `c_store` (a store through a pointer); `cgo.go` defines `Add`, `Sum` and `Store`, which call
them through cgo. `ccover.c` is a model-coverage corpus (not called).
`scripts/build-examples-cgo.sh` builds both ISAs with pinned compilers (Go 1.26.0; gcc 15.2.0
`Ubuntu 15.2.0-16ubuntu1`, native for amd64 and `aarch64-linux-gnu-gcc` for arm64;
`CGO_CFLAGS=-g -O2`). `scripts/verify-cgo-examples.sh` extracts and verifies every proof.

| Proof | Guarantee | arm64 | amd64 |
|---|---|:-:|:-:|
| `CAdd` | `c_add(a, b)` returns `a + b mod 2^64` (`CEnsures`) | ✓ | ✓ |
| `CSum` | `c_sum(p, n)` returns `Σ p[i] mod 2^64` for every `n`, memory unchanged (a loop) | ✓ | ✓ |
| `CStore` | `c_store(p, v)` writes `v` to `*p` and nothing else | ✓ | ✓ |
| `GoAdd` | Go `Add(x, y)` → cgo → `c_add` → Go returns `x + y mod 2^64`, under the trusted `CgoCall` only | ✓ | ✓ |
| `GoSum` | Go `Sum(xs)` → cgo → the C loop → Go returns `Σ xs[i] mod 2^64`, under `CgoCall` only | ✓ | ✓ |

The Go-side preconditions are explicit. They include the stack-growth checks of the Go function
and of its `_Cfunc_` wrapper, the stack window, and the two statically initialised cgo globals
(the function-pointer variable holds the wrapper's address; `runtime.cgoAlwaysFalse` is false),
whose addresses are recomputed from the extracted code. They also require that the `g` struct and
the TLS `g` slot are not on the stack.

## 6. Model coverage for compiler-generated C

`janus blockers` now also works on amd64 binaries: instruction starts come from an untrusted
x86asm sweep, and `Janus.Amd64.decode` judges the bytes through `janus-decode`'s `x86 <bytes>`
queries. On the gcc 15.2 `-O2` code of `cfuncs.c`, `ccover.c` (conditional selects and moves,
bitfield moves, multiply-add and high multiplies, 64-bit immediates, `LEA` forms, sign and zero
extension, rotates, byte swaps, division, `clz`, a VLA frame with `LEAVE`, `push`/`pop` of
callee-saved registers, byte and halfword accesses) and the cgo wrappers:

* **arm64:** every word was already decoded (`csel`/`csinc`/`csinv`/`cset`/`csetm`/`cneg`,
  `ubfiz`/`ubfx`/`sbfx`, `madd`/`msub`/`umulh`/`smulh`/`umaddl`, `udiv`/`sdiv`, `clz`, `rev`,
  `ror`, pre- and post-indexed `stp`/`ldp`, `bti`). Both oracles were run on all 205 distinct
  words of the corpus binary (`artifacts/ccover-c-arm64`, 200 random states each, 37,136
  cases): qemu 0 MISMATCH; Sail three-way 0 cases where Janus produced a result Sail does not.
  The only model gaps are `paciasp`/`autiasp`, which come from the C runtime start files and not
  from the compiled functions.
* **amd64:** the only missing instruction was `ENDBR64` (`F3 0F 1E FA`, at every gcc function
  entry with `-fcf-protection`, Ubuntu's default). It is now decoded as a NOP for exactly those
  bytes; every other `F3 0F 1E` form and prefix combination is still rejected. Oracle:
  `edge/endbr` (the exact bytes plus 21 prefix variants, 8,800 cases) in a 281,243-case quick
  run, 0 MISMATCH. A harvest of every distinct instruction of the gcc corpus binary
  (`artifacts/ccover-c-amd64`, 200 states each, 56,200 cases: `cmov`, `setcc`, `lea`, `imul`,
  `mul`, `div`/`idiv`, `movsx`/`movzx`/`movsxd`, `cqo`/`cdqe`, `bswap`, `bsr`, `ror`, `leave`,
  `push`/`pop`, `nop` forms, ...) also gave 0 MISMATCH.
