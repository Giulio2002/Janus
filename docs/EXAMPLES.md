# Examples: break-it demo and what is proved

Moved out of the top-level README. The break-it demo shows a proof failing on a changed binary; the catalogue lists what the shipped examples prove.

## Break it and watch the proof fail

[`scripts/archive/break-demo.sh`](../scripts/archive/break-demo.sh) copies `examples/basic`, changes `x + y` to `x - y`,
rebuilds, re-extracts, and runs the **unchanged** `Add.lean` against the new binary. The only thing
that changed in the extraction is one word: `0x8b010000` (`add`) became `0xcb010000` (`sub`).

```console
$ scripts/archive/break-demo.sh
== edited Add in a copy of examples/basic:
6:func Add(x, y uint64) uint64 { return x - y }
Extracted example.com/basic.Add: 1 function(s), 2 word(s), 0 stub(s), 0 data object(s) (0 bytes) into artifacts/WrongAdd/Extracted.lean
  code  0x930c0    2 words  example.com/basic.Add
== verifying the unchanged Add proof against the subtracting binary (must be rejected):
Invalid: Lean rejected the proof examples/proofs/Add.lean.
Lean errors (1):
  examples/proofs/Add.lean:25:72: error: unsolved goals
  Stage: proof checking
examples/proofs/Add.lean:25:72: error: unsolved goals
   -> rejected, as it must be.
== verifying the counterexample examples/proofs/WrongAdd.lean on the subtracting binary:
Verified: Proof.correctness
  Axioms: Classical.choice, Quot.sound, propext
  Kernel replay: leanchecker passed (Extracted, Janus, …, Proof; 29 modules; 26 reused from the replay cache)
break-demo: ok
```

<details>
<summary>The goal Lean could not close (from <code>janus verify artifacts/WrongAdd --proof examples/proofs/Add.lean</code>)</summary>

After symbolically executing `sub x0, x0, x1; ret`, the proof is left needing `x - y ≡ x + y`:

```text
Invalid: Lean rejected the proof examples/proofs/Add.lean.
Lean errors (1):
  examples/proofs/Add.lean:25:72: error: unsolved goals
    x y : BitVec 64
    ret : Nat
    hret : RetAddr Extracted.program ret
    s : State
    hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s
    a✝ : True
    h_pc : s.pc = 602304#64
    h_lr : s.regs 30 = BitVec.ofNat 64 ret
    h_x0 : s.regs 0 = x
    h_x1 : s.regs 1 = y
    ⊢ (18446744073709551616 - y.toNat + x.toNat) % 18446744073709551616 = (x.toNat + y.toNat) % 18446744073709551616
  Stage: proof checking
  Next: Fix the proof. It must import Extracted (and Janus) and prove Proof.correctness.
```

The command exits `1` and leaves no `verified.json`.
</details>

A failed proof is not a disproof, so the demo goes one step further: `WrongAdd.lean` *proves the
negation* of the `Add` specification on the broken binary, by running one concrete call
(`x = 0`, `y = 1`, return address `0x1000`) and showing it returns `2^64 - 1`.

## What is proved in the examples

Every function in [`examples/basic/basic.go`](../examples/basic/basic.go) has an amd64 theorem and an arm64 one;
the dynamic-call examples in [`examples/basic/dynamic.go`](../examples/basic/dynamic.go)
(interface method, method value, closure in a loop, open-coded `defer`) have both; the atomics and memory-routine examples in
[`examples/basic/memory.go`](../examples/basic/memory.go) and the SIMD examples in
[`examples/basic/simd_arm64ex.go`](../examples/basic/simd_arm64ex.go) have arm64 theorems, and the
vector-path examples in [`examples/basic/simd.go`](../examples/basic/simd.go) amd64 ones; the
floating-point examples in [`examples/basic/float.go`](../examples/basic/float.go) and the language-construct
examples in [`examples/basic/zconstructs.go`](../examples/basic/zconstructs.go) have both. Each is verified end to end by `janus verify` (kernel check, axiom audit,
`leanchecker` replay) against the `GOARCH=arm64` or `GOARCH=amd64` build of the same source with
Go 1.26.0. Proofs:
[`examples/proofs/`](../examples/proofs) (arm64), [`examples/proofs-amd64/`](../examples/proofs-amd64) (amd64).

| Function | Guarantee | arm64 | amd64 |
|---|---|:-:|:-:|
| `Add` | returns `x + y mod 2^64` | ✓ | ✓ |
| `Max` | returns `max(x, y)` (unsigned) | ✓ | ✓ |
| `Add128` | `hi·2^64 + lo = (xh:xl + yh:yl) mod 2^128` | ✓ | ✓ |
| `Mul64` | `hi·2^64 + lo = x·y` (full 128-bit product) | ✓ | ✓ |
| `Add256` | `*z = (*x + *y) mod 2^256`; on arm64 any two pointers may be equal or disjoint, on amd64 `x` and `y` may alias | ✓ | ✓ |
| `AddLimbs` | the same as a 4-iteration carry loop | ✓ | ✓ |
| `Div` | returns `x / y` for `y ≠ 0`; **panics** (`runtime.panicdivide`) iff `y = 0` | ✓ | ✓ |
| `Get` | returns `xs[i]` for `i < len`; **panics** (`runtime.panicBounds`) for `i ≥ len` | ✓ | ✓ |
| `Sum` | returns `Σ xs[j] mod 2^64` (a loop, by induction) | ✓ | ✓ |
| `CopyWords` | copies `min(len(dst), len(src))` words and returns the count (a loop writing memory) | ✓ | ✓ |
| `AddThree` | `Add(Add(x, y), z)`: stack-growth prologue and two calls | ✓ | ✓ |
| `SumSquares` | `square(x) + square(y)`: prologue and two calls | ✓ | ✓ |
| `SetOne256` | `*z = 1`, from a 32-byte `.rodata` constant | ✓ | ✓ |
| `HexDigit` | byte `i & 15` of a `.rodata` string | ✓ | ✓ |
| `Table` | `t[i & 7]` of a constant `.rodata` table | ✓ | ✓ |
| `A64Equal64` | `bytes.Equal` of two 64-byte arrays, through `runtime.memequal`'s SIMD loop (`LD1`, `CMEQ`, `AND`, `UMOV`) | ✓ | |
| `A64IndexByte` | `bytes.IndexByte` on a 64-byte slice: the first index of `c`, or `-1`, through `internal/bytealg`'s SIMD scan (arm64: 32-byte-aligned data, `LD1`/`CMEQ`/`ADDP`; amd64: the AVX2 path, `VPCMPEQB`/`VPTEST`/`VPMOVMSKB`/`BSF`, given `HasAVX2`) | ✓ | ✓ |
| `A64CountByte` | the number of bytes of `b` equal to `c`, for every length, computed by the words gcc 15.2 `-O2` auto-vectorises a C loop into (`CMEQ`, `ZIP1`/`ZIP2`, `UADDW`/`UADDW2`, `ADDP`, then a scalar tail), behind an ABI0 shim | ✓ | |
| `GlobalTable` | `tbl[i & 7]` of a writable global, provided by the precondition | ✓ | ✓ |
| `Bump` | `counter += d` on a writable global, returns the new value | ✓ | ✓ |
| `MulAlgo` | a writable threshold global: `1` if `n < 40` else `2` when `karatsubaCut`/`mulBias` hold their link-time values (`GlobalsInit`, `--global`), and the parametric form for every value they may hold | ✓ | ✓ |
| `Double` | a flag global set at startup (like math/big's `hasADX`): `2x` for every value of the flag, both code paths | ✓ | ✓ |
| `AtomicAdd` | `atomic.AddUint64(p, d)`: `*p += d`, returns the new value (LSE `LDADDAL` path, given `runtime.arm64HasATOMICS`) | ✓ | |
| `AtomicMax` | `LDAR` + `CASAL` retry loop: returns the old `*p` and sets `*p = max(old, v)`; the loop runs once | ✓ | |
| `CopyBlock` | `copy(dst[:], src[:])` of a 128-byte array through `runtime.memmove` | ✓ | |
| `ClearWords` | `clear(b)` of a 16-word, 128-byte-aligned slice through `runtime.memclrNoHeapPointers` (its `DC ZVA` path), for every `DCZID_EL0` | ✓ | |
| `Equal64` | `bytes.Equal` of two `[64]byte` through `runtime.memequal`: true iff the bytes are equal, for every value of `internal/cpu.X86.HasAVX2` (the AVX2 `VPCMPEQB`/`VPMOVMSKB` loop and the SSE one) | | ✓ |
| `CopyBlock512` | `copy` of a 512-byte array through `runtime.memmove`'s AVX path (`VMOVDQU`/`VMOVDQA`, any `dst` alignment), given `memmoveBits & avxSupported` | | ✓ |
| `AddF64` | the IEEE 754 sum `a + b` rounded to nearest (or a NaN when that is a NaN), under the default `FPCR`/`MXCSR`; on arm64 also exactly Arm's `FPAdd` (and its `FPSR` flags) for every `FPCR` without trap enables | ✓ | ✓ |
| `Dot3` | `a0*b0 + a1*b1 + a2*b2`: on arm64 Go fuses it, `fma(a2, b2, fma(a1, b1, a0·b0))`; on amd64 (no FMA at `GOAMD64=v1`) `(a0·b0 + a1·b1) + a2·b2` with every operation rounded | ✓ | ✓ |
| `F64ToU64` | `uint64(x)` is the truncation of `x` whenever that is in `[0, 2^64)` (amd64: through the `UCOMISD`/`SUBSD`/`CVTTSD2SQ`/`BTSQ` sequence, `SUBSD` shown exact); arm64 also: saturation (`0` below, `2^64-1` above, `0` for NaN) and the exact `FPToFixed` for every `FPCR` without trap enables | ✓ | ✓ |
| `Abs` | `x` with its sign bit cleared, for every encoding including NaNs (integer and move instructions only) | ✓ | ✓ |
| `HashWith` | an interface call `h.Hash(x)`: `x·K` when `h`'s itab is `*MulHasher`'s, `rotl(x, 13) + K` when it is `*RotHasher`'s (the itab is a hypothesis) | ✓ | ✓ |
| `HashTwice` | `ApplyTwice(h.Hash, x)` through a method value: `x·K·K` | ✓ | ✓ |
| `MapSum` | a closure capturing `a`, `b` called in a loop: `Σ (a·xs[j] + b) mod 2^64` | ✓ | ✓ |
| `DeferAdd` | an open-coded `defer` that adds `y` to the named result: returns `x + y` | ✓ | ✓ |
| `NewPair` | `&Pair{a, b}`: a fresh 16-aligned heap object holding `a`, `b`, assuming the `runtime.newobject` contract | ✓ | ✓ |
| `MakeSlice` | `make([]uint64, n)`: length and capacity `n`, a fresh all-zero array, assuming the `runtime.makeslice` contract | ✓ | ✓ |
| `AppendOne` | `append(s, x)`, in place or through `runtime.growslice` (Go's growth rule, size-class rounding, old elements copied, zero tail), assuming its contract | ✓ | ✓ |
| `SetNext` | `n.Next = q` through the GC write barrier, whose fast path (buffer append) is executed | ✓ | ✓ |
| `MallocFast` | `runtime.mallocgc` itself: the small pointer-free fast path returns the free slot of the P's cached span (zeroed) and updates exactly the span/mcache fields, under `MCacheOK` | ✓ | |
| `Lookup` | `v, ok := m[k]` on a `map[uint64]uint64`, with `runtime.mapaccess2_fast64` as a stated contract ([RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md), "Maps") | ✓ | ✓ |
| `Insert`, `InsertGet`, `Delete`, `ClearMap`, `NewMap` | `m[k] = v` (then reading it back gives `v`), `delete`, `clear`, `make`, through their map contracts | ✓ | ✓ |
| `SumValues` | `for _, v := range m` sums the values, for **every** iteration order | ✓ | ✓ |
| `CountKeys`, `LookupKey16` | `len(m)` (the number of keys); lookup with `[16]byte` keys (generic `mapaccess2`) | ✓ | ✓ |
| `MapAccess1Small` | the machine code of `runtime.mapaccess1_fast64` itself meets its contract on small Swiss maps | ✓ | ✓ |
| `Concat`, `ToBytes`, `FromBytes` | `a + b`, `[]byte(s)`, `string(b)` through the `concatstring2`, `stringtoslicebyte`, `slicebytetostring` contracts ([RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md), "Strings, slices and the write barrier") | ✓ | ✓ |
| `SumRunes`, `RuneLen` | `for _, r := range s` (the sum of the runes) and `len([]rune(s))`, with Go's UTF-8 decoding; end to end, `runtime.decoderune` and `runtime.countrunes` proved from their code | ✓ | ✓ |
| `AppendPoint`, `CopyNodes` | `append` to a `[]Point` (24-byte struct, `growslice`) and `copy` of `[]*Node` (`typedslicecopy`) | ✓ | ✓ |
| `WriteBarrier` | the real `runtime.gcWriteBarrier1..8` meet the write-barrier contract when the P's buffer has room | ✓ | ✓ |
| `Triangle` | an expression switch with `fallthrough` (a `.rodata` jump table): `n·(n+1)/2` for `n ≤ 8`, else `0` | ✓ | ✓ |
| `GotoSum` | a loop built from labels and `goto`: `1 + … + n mod 2^64` | ✓ | ✓ |
| `Find2D` | nested loops left by a labeled `break`: the first row-major index of `x` in a `3×3` array, or `9` | ✓ | ✓ |
| `RowsWith` | a labeled `continue`: the number of rows of a `2×3` array containing `x` | ✓ | ✓ |
| `Log2` | a condition-only `for`: `⌊log₂ x⌋` (`2^r ≤ x < 2^(r+1)`), `0` for `x = 0` | ✓ | ✓ |
| `TotalMeters`, `TotalFeet` | two instantiations of one generic function sharing the GC-shape body `total[go.shape.uint64]`, each reaching its `Scale` method through its dictionary: `100·(a+b)`, `30·(a+b)` | ✓ | ✓ |
| `Fact` | recursion: `n! mod 2^64`, by induction over the recursive calls (given stack for `n + 1` frames) | ✓ | ✓ |
| `IsEven`, `IsOdd` | mutual recursion: `1` iff `n` is even (odd), by `Summary.induction_mutual` over both members | ✓ | ✓ |
| `CycA`, `CycB`, `CycC` | a 3-cycle of calls with three different frame sizes, by a weighted shared measure | ✓ | ✓ |
| `SumBelow` | range over an `int`: `0 + … + (n-1)`, nothing for `n ≤ 0` | ✓ | ✓ |
| `IterSum` | range over a function iterator (inlined, no runtime call): the same sum | ✓ | ✓ |
| `ReverseArray` | array value semantics and range over an array: `out[i] = in[3-i]`, also for `out = in` | ✓ | ✓ |
| `DivMod10` | named results, division by a constant (magic multiply): `x / 10`, `x % 10` for all `x` | ✓ | ✓ |
| `SwapBig` | struct assignment by value: swaps two 64-byte structs (equal or disjoint) | ✓ | ✓ |
| `Compose` | a non-escaping closure built in the frame: `f(f(x))` for `f(v) = a·v + b` | ✓ | ✓ |
| `DotBoth` | a method value and a method expression on a value receiver | ✓ | ✓ |
| `BitMerge` | `&^`, `&`, `\|`, `^`: two bit-merge formulas, bit `i` from `y` where `m` is set, else from `x` | ✓ | ✓ |
| `Shifts` | `<<`, `>>` (signed and unsigned) by a variable count with Go's semantics for counts `≥ 64` | ✓ | ✓ |
| `MinMax` | the `min`/`max` builtins (signed) and the exact distance `max - min` | ✓ | ✓ |
| `ClearArray` | `clear` of a 5-word array: all 40 bytes zero, nothing else written | ✓ | ✓ |
| `Sum3` | a variadic call (the argument slice in the caller's frame): `a + b + c` | ✓ | ✓ |
| `AlignUp` | `uintptr` arithmetic: rounds `p` up to a multiple of the power of two `a` | ✓ | ✓ |
| `Slice2` | `xs[i:j]`: the new header; **panics** iff not `0 ≤ i ≤ j ≤ cap` | ✓ | ✓ |
| `Mod` | `x % y` by a variable; **panics** (`runtime.panicdivide`) iff `y = 0` | ✓ | ✓ |
| `IncTwice` | two static calls of a pointer-receiver method: `c.N += d` twice, returns the sum of the results | ✓ | ✓ |
| `MakeAdder` | an escaping closure: a fresh funcval from `runtime.newobject` (contract) holding `MakeAdder.func1` and the captured `a` | ✓ | ✓ |
| `Slice3` | `xs[i:j:k]`: the new header; **panics** (`runtime.panicBounds`) iff not `0 ≤ i ≤ j ≤ k ≤ cap` | ✓ | ✓ |
| `I64ToF64`, `U64ToF64` | `float64(x)` of an `int64` / `uint64` is IEEE `convertFromInt` rounded to nearest-even (amd64 `uint64`: Go's sign-test, sticky-halving, `CVTSI2SDQ`, doubling sequence, shown exact); exact for `\|x\| < 2^53` (truncating gives `x` back) | ✓ | ✓ |
| `F64ToI64` | `int64(x)` is the truncation when it is in `[-2^63, 2^63)`; out of range as the hardware gives it: arm64 `FCVTZS` saturates (`-2^63`, `2^63-1`, `0` for NaN), amd64 `CVTTSD2SQ` returns the integer indefinite `0x8000000000000000` | ✓ | ✓ |
| `F64ToF32`, `F32ToF64` | `float32(x)`, `float64(x)` between float types are IEEE `convertFormat` (a NaN for a NaN); widening is exact in every rounding direction | ✓ | ✓ |
| `MinF64`, `MaxF64` | `min`/`max` of floats are IEEE 754-2019 `minimum`/`maximum`: a NaN if either is NaN, `min(-0, +0) = -0`, `max(-0, +0) = +0` (arm64 `FMIN`/`FMAX`; amd64 Go's `MINSD`/`MINSD`/`POR` sequence, `max` on the negations) | ✓ | ✓ |
| `MinStr` | `min(s, t)` of strings through `runtime.strmin` (executed): `t` if `t < s` bytewise, else `s`, assuming the `runtime.cmpstring` contract (satisfiable, witnessed by a verified byte loop) | ✓ | ✓ |
| `LoadThird` | `p[2]` for a non-nil `p`; for `p = nil` (nothing mapped below `4096`) the load **faults** at address `16 < 4096` (stated at the machine level: the faulting instruction and its `outsideAllocation` error) | ✓ | ✓ |
| `SpanSum` | range over a function iterator that stays a real call (`Span.All` with the loop body `SpanSum-range1` as a closure called through its funcval, `#state` checks): `lo + … + (hi-1)` | ✓ | ✓ |
| `Box` | `any(x)` for a `uint64`: `(type:uint64, ptr)` with a box holding `x`, assuming the `runtime.convT64` contract ([RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md), "Interfaces") | ✓ | ✓ |
| `AsHasher` | `h, ok := x.(Hasher)`: the itab `getitab` gives (or `0`), the data word and `ok`, for every state of the assertion cache (its probe loop executed), through the `runtime.typeAssert` contract; the static itab for a `*MulHasher` | ✓ | ✓ |
| `Classify` | a type switch over `nil`, `uint64`, `string`, `Hasher` and the rest: the case taken, through the type-hash compares, the switch-cache probe and the `runtime.interfaceSwitch` contract | ✓ | ✓ |
| `Equal` | `a == b` on `any`: different type words give `false`, two nils `true`, otherwise `runtime.efaceeq`'s answer (byte equality for `TFlagRegularMemory` types) | ✓ | ✓ |
| `Eq32` | `*a == *b` on `[32]byte`: `true` iff the 32 bytes agree, executing `runtime.memequal` | ✓ | ✓ |
| `StrEq` | `s == t`: equal lengths and bytes, through the `memequal` contract ([RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md), "Equality, hashing and typed memory") | ✓ | ✓ |
| `F64Eq` | `x == y` on `float64`: IEEE equality (`+0 == -0`, `NaN != NaN`) | ✓ | ✓ |
| `CopyTrees`, `ClearTrees` | copying / clearing pointerful memory through `typedmemmove` / `memclrHasPointers`, write barrier off | ✓ | ✓ |
| `LookupStr` | `m[k]` on a `map[string]uint64`, keyed by the string's content (`mapaccess2_faststr` contract) | ✓ | ✓ |
| `HashFKey`, `EqFKey` | the compiler-generated hash and `==` of a struct key: keys equal under `==` hash alike (the seeded hash as an uninterpreted function with its laws) | ✓ | ✓ |
| `ScratchSum` | a pooled scratch buffer: `Get`, `new` on a miss, `Put`; returns `a ^ b` (the buffer is scratch), the pool's owned object is caller-owned between the calls and the runtime's invariant holds again for the same live set, through the `sync.(*Pool).Get` / `Put` and `runtime.newobject` contracts ([RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md), "sync.Pool") | ✓ | ✓ |
| `StackGrow` | `math/big`'s pattern: `Get` a pooled stack, `new` on a miss, `slices.Grow` into it (`growslice`, `memclrNoHeapPointers`, the GC write barrier), deferred `Put`: returns the stack's capacity (`cap` if `n ≤ cap`, else Go's growth rule), no live object changed, the runtime's invariant again | ✓ | ✓ |
| `Alg*`, `Mbar*` | the runtime's own equality, hash and typed-memory functions (`memequal8`, `f64equal`, `strequal`, `f64hash`, `typedmemmove`, …) meet their contracts, from their machine code | ✓ | ✓ |
| `WrongAdd` | the subtracting `Add` **violates** the `Add` spec (a proved counterexample) | ✓ | |
| `BitMix` | `GOAMD64=v3` (`examples/basic/v3`): `(x &^ y) ^ (x & (x-1)) ^ (y << (n & 63))` through BMI `ANDN`, `SHLX`, `BLSR` | | ✓ |
| `Fma` | `GOAMD64=v3`: `math.FMA(a, b, c)` as one `VFMADD231SD` is IEEE 754 `fusedMultiplyAdd` rounded once (the arm64 `FMADD` specification), whenever the result is architecturally defined | | ✓ |
| `LoadBE` | `GOAMD64=v3`: `binary.BigEndian.Uint64` as one `MOVBE` is the big-endian value of the 8 bytes | | ✓ |
| `Memhash64`, `Memhash32` | std `runtime.memhash64`/`memhash32` (every 8-/4-byte map key, `examples/basic/xcrypto`): three FIPS-197 AES rounds (`AESENC`) keyed by `runtime.aeskeysched` when `useAeshash`, else `memhash*Fallback` | | ✓ |
| `EncryptBlock` | std `crypto/aes`'s `encryptBlockAsm` (AES-NI) writes FIPS-197 `Cipher` for AES-128/192/256; AES-128 for an expanded key; the FIPS-197 C.1 vector through the machine code | | ✓ |
| `AddMulVVWW` | std `math/big.addMulVVWW` (ADX `ADCX`/`ADOX` + `MULX`, and the `MULQ` path): `z + 2^(64n)·c = x + y·m + a` for **every** length `n` | | ✓ |

Each file starts with a plain-English summary of the theorem (the arm64 ones under **Guarantee** and
**What it rules out**). Every proof uses only axioms from the allow-list `propext`, `Quot.sound`,
`Classical.choice`. Reproduce with
`scripts/verify/verify-examples.sh` and `scripts/build/build-examples-amd64.sh && scripts/verify/verify-amd64-examples.sh`.

**Go calling C (cgo).** The C functions in [`examples/cgo`](../examples/cgo) (gcc 15.2, `-O2`) are
proved on both ISAs against the C calling conventions (`CEnsures`, [`Janus/CABI.lean`](../Janus/CABI.lean),
[`Janus/Amd64/CABI.lean`](../Janus/Amd64/CABI.lean)): `c_add`, the loop `c_sum` and the store
`c_store`. Go → C → Go is proved end to end for `Add` and `Sum`. The Go code, the cgo wrappers and
the C code are all executed by the model, and only the `runtime.cgocall` stack and scheduler switch
is a trusted contract, named in the statement (`EnsuresC … (CgoCall Extracted.program) …`). See
[docs/FFI.md](FFI.md) and `scripts/verify/verify-cgo-examples.sh`.

**Go talking to the kernel.** The functions in [`examples/sys`](../examples/sys) make system calls,
read the clocks and trap. Linux is the environment of the theorem (`Kernel.EnsuresK`): a kernel
state with an explicit I/O trace and input oracle, and a contract per system call (`write` may be
short or fail, the monotonic clock never goes back, ...). `WriteOut` (`syscall.Write(1, p)`): the
fd-1 trace gains exactly the bytes the kernel accepted and the call returns their count, or `-1`
with the trace unchanged; `NowNano` (`time.Now().UnixNano()`): the wall-clock reading of the vDSO,
in nanoseconds; `Pid` (`syscall.Getpid()`); `MustNonNeg`: the negative path ends in a breakpoint
trap (`Kernel.Traps`). All four on arm64 and amd64; see
[RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md) ("The kernel") and
`scripts/verify/verify-sys-examples.sh`.

**Go assembly (ABI0).** Hand-written `.s` functions are verified like compiled Go, against their
stack-based calling convention ABI0 (`Ensures0`, [`Janus/GoABI0.lean`](../Janus/GoABI0.lean),
[`Janus/Amd64/GoABI0.lean`](../Janus/Amd64/GoABI0.lean)). In [`examples/asm`](../examples/asm), on both
ISAs: `AddAsm` and the loop `XorSlice` (assembly), `Twice` (assembly calling a Go function through
the compiler's ABI0 → ABIInternal wrapper), `CallXor` (Go with a direct ABI0 call; on amd64 the
`R14 = g` / `X15 = 0` re-entry is executed) and the ABIInternal → ABI0 wrapper of `XorSlice`.
Callees compose through `Summary0`; nothing about assembly, wrappers or call sequences is assumed.
See [docs/ABI0.md](ABI0.md) and `scripts/verify/verify-asm-examples.sh`.

<!-- TODO(coordinator): the checkmarks come from a re-run on 2026-10-23 (14 arm64 proofs, 17 amd64
Proof.correctness + Div/Get Proof.panics, and scripts/archive/break-demo.sh: all Verified) with a janus binary
whose embedded framework has SHA-256 e9be8cd3…. Other agents were still editing Janus/Arm64/*.lean
afterwards; re-run scripts/verify/verify-examples.sh and scripts/verify/verify-amd64-examples.sh on the final tree. -->

