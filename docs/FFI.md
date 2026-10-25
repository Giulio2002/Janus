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

### 1.1 Registers, stack, and what a call preserves

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

`CCall`/`CEnsures` are the integer special case (at most eight / six integer arguments in
registers, an integer result). The general case, every argument and result class of both ABIs,
is the classified call of § 1.2; `cCallA_iff_cCall` shows that `CCall` is exactly `CCallA` for a
prototype of 64-bit integer arguments in registers with no memory result, so the two are one
model.

**What is preserved across a call.** Besides the general registers, `CReturn` requires the
floating-point state the ABIs make callee-saved:

| | arm64 | amd64 |
|---|---|---|
| vector registers | low 64 bits of `V8`–`V15` (`CReturn.v8` … `v15`; AAPCS64 6.1.2) | none (all `XMM` are caller-saved) |
| FP control | `FPCR` (`CReturn.fpcr`) | `MXCSR` control bits, bits 6 and up (`CReturn.mxcsr`), and the x87 control word (`CReturn.fpucw`, psABI 3.2.1) |
| not preserved | `FPSR` (sticky flags), `V0`–`V7`, `V16`–`V31`, the high halves of `V8`–`V15` | `MXCSR` bits 0–5 (sticky flags), the x87 status word |

The x87 control word is a new state field (`Janus.Amd64.State.fpucw`, reset value `0x037F`).
No decoded instruction reads or writes it yet, so every run keeps it; it is in the state so that
the obligation can be stated now and holds unchanged when the x87 instructions (WP-J) arrive.
The x87 register stack itself (empty at a call, holding a `long double` result on return) is not
modelled: an x87 result (`ST0`/`ST1`) cannot be stated (`PieceAt … (.x87 _)` is `False`), so a
proof about a function returning `long double` on amd64 is impossible today rather than wrong.
`GoResume` keeps `FPCR` and the `MXCSR` control bits and leaves `FPSR` and the `MXCSR` flags
arbitrary: a Go caller in the Go floating-point environment (`GoABI.GoMXCSR`) is still in it
after the call (`GoResume.goMXCSR`), with no claim about the flags. On the way in, the trusted
`CgoEntry` states that the C code starts with the Go caller's `FPCR` (arm64) and `MXCSR` control
bits and x87 control word (amd64): `asmcgocall` switches only the stack and `g`.

### 1.2 The classification (`Janus/CABI/{CType,AAPCS64,SysV}.lean`)

Where every argument and the result of a prototype go is a pure Lean function of the C types:

* **`Janus.C.CType`** (`CType.lean`): integers of 1–16 bytes (`__int128` included), pointers,
  `_Float16`, `float`, `double`, `long double`, `_Complex b`, 8- and 16-byte vectors, structs,
  unions and arrays, with their LP64 layout (`size`, `align`, member `offsets`, the scalar
  `leaves`) and the homogeneous-aggregate test `hfa` (1–4 members of one floating-point or
  short-vector base type). Bit-fields, packed/aligned attributes, flexible arrays, empty structs
  and 32/64-byte vectors are outside the model (no constructor).
* **`Janus.C.AAPCS64`**: `assign`/`assignAll` is the AAPCS64 §6.8.2 algorithm (`NGRN`, `NSRN`,
  `NSAA`): FP/SIMD scalars and HFA/HVA members in `V0`–`V7` (one member per register, all or
  none), integers, pointers and composites ≤ 16 bytes in `X0`–`X7` (16-byte-aligned ones from an
  even register; all doublewords or none), composites > 16 bytes by reference to a caller-made
  copy (rule B.4), everything else in 8-byte-aligned stack slots. `result`: the same registers,
  or a buffer whose address the caller passes in `X8` (`.indirect (.gpr 8)`). `long double` is
  IEEE binary128 in one `V` register (its arithmetic is libgcc calls such as `__multf3`, ordinary
  C calls); `_Complex double` is an HFA of two `double` (`D0`, `D1`).
* **`Janus.C.SysV`**: `classify` gives every eightbyte its class (INTEGER, SSE, SSEUP, X87,
  X87UP, COMPLEX_X87, MEMORY) by the psABI §3.2.3 merge, with the post-merger cleanup applied to
  every nested aggregate as gcc does (the probe found that a cleanup at the top only is wrong for
  a union containing a `long double`); `assign` hands out `RDI RSI RDX RCX R8 R9` and
  `XMM0`–`XMM7` per argument (all of an argument's eightbytes in registers, or the whole argument
  in the argument area at `RSP + 8`); `result` returns INTEGER eightbytes in `RAX`/`RDX`, SSE ones
  in `XMM0`/`XMM1`, MEMORY through the hidden first argument `RDI` (returned in `RAX`), X87 in
  `ST0` and COMPLEX_X87 in `ST0`/`ST1`. `_Complex double` is SSE, SSE (`XMM0`, `XMM1`); `long
  double` is X87, X87UP: passed in memory, returned in `ST0` (its execution is WP-J's).
* **Variadic calls.** Linux passes variadic arguments as named ones on both ABIs
  (`Sig.named` records how many are named). On amd64 `AL` must bound the number of vector
  registers used (`Sig.vecRegs`, at most 8). The callee's `va_list` is `VaList` in both models
  (AAPCS64: `__stack`, `__gr_top`, `__vr_top`, `__gr_offs`, `__vr_offs`; SysV: `gp_offset`,
  `fp_offset`, `overflow_arg_area`, `reg_save_area`), with `vaStart` (from the classification of
  the named parameters) and `vaArg` (the register save areas, then the stack / overflow area).
  `vaStart_vaArgs_int8` (both ABIs) proves that the walk agrees with the classification: for a
  variadic tail of `int64_t`, the `i`-th `va_arg` reads the save-area slot of the register
  `assign` put that argument in while there is one, and then exactly the stack slot `assign`
  put it in.

`decide` evaluates all of this on concrete prototypes (`sig.passing = … := by decide` in every
proof), and `#eval` prints it (`JanusTests/CABIProbe.lean`).

### 1.3 The differential test against gcc and clang (`scripts/cabi-probe.sh`)

The classification is checked against the real compilers, not against a reading of the ABI
documents. `scripts/cabi-probe.sh` (Go program `scripts/cabiprobe`) takes a corpus of prototypes
— the ABI functions of the C corpus (`scripts/coverage/ccorpus/abi.c`: `a_stackargs`, `a_fargs`,
`a_small`, `a_mixed`, `a_hfa`, `a_big`, `a_varargs`, …), the cgo examples (`k_*`), the classic
edge cases of both ABIs (HFA/HVA of 1–5 members, `float`/`double` mixes, unions, nested and
array members, `__int128` alignment, `_Complex`, `long double`, register exhaustion in each class,
variadic `double`s and structs) and seeded random prototypes — and asks Janus
(`lake env lean --run JanusTests/CABIProbe.lean`) for every argument's and the result's
locations, the layouts, `AL` and the `va_list` states. For each of 8 configurations (gcc and
clang, `-O0` and `-O2`, arm64 under qemu and amd64 native) it then compiles, per prototype,

1. a **caller** that calls an assembly stub recording every argument register, the
   stacked-argument area and the stack memory the registers point to (copies): each argument's
   bytes must be where Janus says, and `AL` must bound the vector registers used;
2. a **callee** called by an assembly loader that puts the arguments where Janus says (and a
   result buffer in `X8`/`RDI`): it must receive every argument intact, return the result where
   Janus says, and — for a variadic callee — its `va_list` after `va_start` and after every
   `va_arg` must be the `vaStart`/`vaArg` states, and Janus's `vaArg` evaluated on the callee's
   own register save areas must return the values its `va_arg` read;
3. a **layout** check: `sizeof`, `_Alignof` and the offset of every scalar leaf.

**Results** (gcc 15.2.0, clang 21.1.8; `scripts/cabi-probe.sh -random N -seed S`): 0 mismatches
in every configuration, for seed 1 (439 prototypes: 39 curated, 400 random; 9,706 checks per
arm64 and 9,899 per amd64 configuration), seed 2 (1,037 prototypes, 22,204 / 22,669 checks) and
seed 7 (1,039 prototypes, 22,053 / 22,525 checks), so about 220,000 checks per seed over the
8 configurations. Random prototypes with a type over 256 bytes or over 1 KiB of stacked
arguments are not generated (the stubs' capture buffers). The probe found an error in the
model while it was written (the SysV cleanup has to be applied per aggregate, see above), fixed
before these runs.

One compiler bug is excluded, not counted as a mismatch: **gcc 15.2 at `-O2` on arm64
miscompiles `va_arg` of an HFA/HVA of `_Float16` or of short vectors** (it reads the wrong save
slots; the same source is correct at `-O0` and with clang, and a standalone reproducer outside
the probe shows the miscompile). `knownBug` in `scripts/cabiprobe/main.go` excludes exactly those
tests (13, 24 and 35 for seeds 1, 2, 7, listed in `known-bugs.txt`); the caller side of those
prototypes and every other check still run.

### 1.4 Classified calls (`CCallA`, `CEnsuresR`)

`CCallA p entry sig vals s` is the general call state for a prototype `sig` and argument values
`vals` (each the little-endian bytes of the C object): `ArgsAt s sig.args vals sig.passing`
places every piece where the classification says (`PieceAt`: the low bytes of a general
register, bytes of a vector register, an argument-area slot, or for a by-reference argument a
pointer to a writable copy), `RetBuf` gives a MEMORY / `X8` result a writable buffer of its
size (on amd64 also disjoint from the return-address slot), and on amd64 `VarargAL` states the
`AL` bound for a variadic call. Register bytes above a piece and slot bytes above a value are
unspecified. `ResultAt`/`Returned` read the result back (from registers, or from the buffer,
whose address `RAX` returns on amd64), and

```lean
def CEnsuresR (p : Program) (entry : Nat) (sig : Sig) (vals : List Nat)
    (pre : State → Prop) (post : State → State → Nat → Prop) : Prop :=
  CEnsuresA p entry sig vals pre (fun s s' => ∃ v, Returned sig s s' v ∧ post s s' v)
```

is the contract (`CEnsuresA` is `CEnsures` over `CCallA`). The proofs follow one pattern
(`examples/proofs-cgo/*/K*.lean`): the callee's precondition `SPre` is stated *with the
classification* (`ArgsAt s sig.args vs sig.passing ∧ …`), `spre_iff` evaluates it to register
and stack equations, the C function is proved as a `Summary` and turned into a `CEnsuresR` by
`CEnsuresA.of_summary`. At a call site (the cgo wrapper, or `k_vsum8` calling `k_vsum`),
`janus_run [spre_iff, …] calls [summary …]` proves `SPre` in the caller's state, so the compiled
call site is checked against the classification. `argsAt_ints_gen` and `intLoc` give `ArgsAt`
for any number of integer arguments (registers, then stack), which the variadic `k_vsum` proof
uses for every argument count.

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
them through cgo. The package `example.com/cgo/cabi` (`cabi/kabi.c`, `cabi/kvcall.c`,
`cabi/cabi.go`) has the C functions of the classified ABI (`k_stack10`, `k_fp`, `k_pmix`,
`k_big`, `k_vsum`, `k_vsum8`) and their Go callers (`Stack10`, `FP`, `PMix`, `Big`, `VSum8`).
`ccover.c` is a model-coverage corpus (not called).
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
| `KStack10` | `k_stack10(a, …, h, i, j)`: ten arguments, two (arm64) / four (amd64) on the stack, one an `int32_t` in an 8-byte slot (`CEnsuresR`) | ✓ | ✓ |
| `KFP` | `k_fp(double a, float b, double c)` returns `(a - (double)b) * c` in `D0`/`XMM0`, IEEE round-to-nearest (`CEnsuresR`) | ✓ | ✓ |
| `KPMix` | `k_pmix(struct k_pt a, struct k_pt b, int64_t n)`: two `{double, double}` by value (HFA in `V0`–`V3` / SSE, SSE in `XMM0`–`XMM3`), returns the mixed `{double, int64_t}` (`X0`, `X1` / `XMM0`, `RAX`) | ✓ | ✓ |
| `KBig` | `k_big(x, y)` returns a 32-byte struct through the caller's buffer (`X8` / hidden `RDI`, returned in `RAX`), writing nothing else | ✓ | ✓ |
| `KVSum` | `k_vsum(int n, ...)` returns the sum of its `n` variadic `int64_t`, **for every `n`** (register save area, then the stack / overflow area; `VarargAL` on amd64) | ✓ | ✓ |
| `GoStack10` | Go `Stack10` → cgo → `k_stack10` → Go, under `CgoCall` only | ✓ | ✓ |
| `GoFP` | Go `FP(a, b, c)` → cgo → `k_fp` → Go returns the IEEE result (`FPCR = 0` / Go's `MXCSR`) | ✓ | ✓ |
| `GoPMix` | Go `PMix` → cgo → `k_pmix` (structs by value, mixed struct result) → Go | ✓ | ✓ |
| `GoBig` | Go `Big` → cgo → `k_big` (indirect result; the wrapper's stack protector) → Go returns the four words | ✓ | ✓ |
| `GoVSum8` | Go `VSum8(a, …, h)` → cgo → `k_vsum8` → the variadic `k_vsum(8, a, …, h)` → Go returns the sum; the variadic call site (and `AL = 0`) is checked against the classification | ✓ | ✓ |
| `CCount` | `c_count(p, n, c)` (package `example.com/cgo/neon`, auto-vectorised by gcc `-O2`: `CMEQ`/`ZIP`/`UADDW`/`ADDP` loop + scalar tail) returns the number of `i < n` with `p[i] = c`, memory unchanged | ✓ | – |
| `GoCount` | Go `neon.Count(xs, c)` → cgo → the NEON loop → Go returns the count, under `CgoCall` only | ✓ | – |

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
