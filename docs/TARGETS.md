# Verification targets: `github.com/holiman/uint256`

The flagship target is the 256-bit integer type `uint256.Int` that go-ethereum's EVM uses
for every stack word. This document records what the compiler actually emitted for
`linux/arm64`, which functions can be proved first, and the exact theorem each one should
satisfy.

* Target source: `github.com/holiman/uint256 v1.3.2` (latest release; pinned in
  `targets/uint256/go.mod` / `go.sum`, `h1:a9EgMPSC1AAaj1SZL5zIQD3WbwTuHrMGOerLjGmM/TA=`).
  go-ethereum `master` (`1223cf3a`, 2026-10-23) and release `v1.17.9` both depend on this
  exact version.
* Toolchain: `go1.26.0`, `GOOS=linux GOARCH=arm64 GOARM64=v8.0 CGO_ENABLED=0 -trimpath
  -buildvcs=false`. The build is reproducible:
  `bin/uint256-arm64` SHA-256 `d70d4a6d3db7a0408eeb9d45918ddbdd02d004a462b4b980b4620fc323c5925f`.
* Files: `targets/uint256/main.go` (keeps the methods alive), `build.sh`, `inventory.py`
  (regenerates the data), `inventory.json` (per-function raw data, including transitive
  callees, memory footprints and alias checks).

Regenerate with:

```sh
targets/uint256/build.sh
cd targets/uint256 && python3 -I inventory.py > inventory.json
```

## How the methods are kept out of line

`main.go` stores **method expressions** (`(*uint256.Int).Add`, ...) in package-level
slices and calls them indirectly with inputs parsed from `os.Args`. An indirect call
cannot be inlined, and a function whose address is reachable from a live global cannot be
dead-code-eliminated, so the binary contains the real symbol
`github.com/holiman/uint256.(*Int).Add`, compiled exactly as for any other importer.

The EVM's `SIGNEXTEND` method is called `ExtendSign` in the library (there is no
`SignExtend`).

## Instruction subset

Over **all 39 target methods and their transitive callee closure** (including
`udivrem*`, `umul`, `Reciprocal`, `reduce4`, `squared`, `math/bits.Div64` and
`runtime.memmove`; only `Clone`'s allocator `runtime.mallocgc` was not inspected), there is
**no SIMD or FP instruction**. Every instruction belongs to the
integer subset. The mnemonics that occur (objdump aliases) are:

```
add adds sub subs cmp cmn neg ngc adc adcs sbcs
and orr eor bic mvn mov            (incl. MOVZ/MOVN/ORR-imm aliases)
lsl lsr asr                        (both immediate = UBFM/SBFM and register = LSLV/LSRV/ASRV)
ubfx ubfiz sxtb extr
csel cset cinc
mul madd msub umulh udiv
clz rev
adrp b b.cond bl cbz cbnz tbz tbnz ret
ldr ldur ldrb ldrsb ldp str stur strb stp   (incl. pre-index `[sp, #-N]!` and post-index `[sp], #N`)
nop
```

The decoder needs to handle these aliases in particular: `ngc` (SBC from XZR), `cset`/`cinc`
(CSINC), `mvn` (ORN), `neg` (SUB from XZR), register-amount `lsl`/`lsr`/`asr` (amount taken
mod 64; Go puts a `csel` guard after them where `n >= 64` must produce 0), `ubfiz`/`ubfx`/`sxtb`
(bitfield), `extr`, `ldrsb` and register-offset addressing `[x0, x1, lsl #3]` (`Byte`,
`ExtendSign`). Each function is followed by `udf #0` padding words up to 16-byte alignment;
execution never reaches them.

## Tier table

Columns: instruction count (excluding trailing padding); stack frame in bytes (`+chk` = has
the stack-growth prologue `ldr x16, [x28, #16]; cmp sp|x17, x16; b.ls morestack`); direct
callees other than `runtime.morestack_noctxt` (`rt.` = runtime); backward branches (loops,
not counting the morestack retry); memory touched (`args` = only the pointer arguments,
`stack` = its own frame and the caller's spill/result area, `g` = reads `g.stackguard0` at
`[x28+16]`, `global` = reads a 32-byte constant from `.rodata`, `heap` = writes a freshly
allocated object); non-integer instructions; the EVM opcodes in geth that run this code.

| Tier | Method | Instrs | Frame | Callees | Loops | Memory | SIMD/FP | geth opcodes |
|---|---|---|---|---|---|---|---|---|
| 1a | `Add` | 17 | - | - | - | args | none | ADD (inlined into `opAdd`) |
| 1a | `Sub` | 17 | - | - | - | args | none | SUB (inlined) |
| 1a | `AddOverflow` | 20 | - | - | - | args | none | - |
| 1a | `SubOverflow` | 21 | - | - | - | args | none | - |
| 1a | `Mul` | 43 | - | - | - | args | none | **MUL** (out-of-line call) |
| 1a | `And` | 17 | - | - | - | args | none | AND (inlined) |
| 1a | `Or` | 17 | - | - | - | args | none | OR (inlined) |
| 1a | `Xor` | 17 | - | - | - | args | none | XOR (inlined) |
| 1a | `Not` | 9 | - | - | - | args | none | NOT (inlined) |
| 1a | `Neg` | 15 | - | - | - | args | none | (inlined into `SDiv`/`SMod`) |
| 1a | `Set` | 5 | - | - | - | args | none | many (inlined) |
| 1a | `Clear` | 3 | - | - | - | args | none | many (inlined) |
| 1a | `SetUint64` | 3 | - | - | - | args | none | PC, MSIZE, GAS, ... (inlined) |
| 1a | `IsZero` | 8 | - | - | - | args | none | ISZERO, JUMPI (inlined) |
| 1a | `IsUint64` | 7 | - | - | - | args | none | - |
| 1a | `Lt` | 13 | - | - | - | args | none | LT (inlined) |
| 1a | `Gt` | 14 | - | - | - | args | none | GT (inlined) |
| 1b | `Eq` | 20 | - | - | - | args | none | EQ (inlined) |
| 1b | `Cmp` | 22 | - | - | - | args | none | - |
| 1b | `BitLen` | 26 | - | - | - | args | none | EXP gas (`gas_table.go`, inlined) |
| 1b | `Slt` | 47 | - | - | - | args | none | **SLT** |
| 1b | `Sgt` | 48 | - | - | - | args | none | **SGT** |
| 2 | `Lsh` | 77 | - | - | - | args | none | **SHL** |
| 2 | `Rsh` | 74 | - | - | - | args | none | **SHR** (and SAR via `SRsh`) |
| 2 | `Byte` | 24 | - | - | - | args (z by register index) | none | **BYTE** |
| 2 | `ExtendSign` | 44 | - | - | - | args (z by register index) | none | **SIGNEXTEND** |
| 2 | `Bytes32` | 28 | 48 | - | - | args, stack (result in caller frame) | none | SLOAD, SSTORE, CREATE2, LOGn (inlined) |
| 2 | `SetBytes32` | 33 | 16 +chk | rt.panicBounds | - | args, stack, g | none | PUSH32 (inlined) |
| 2 | `SRsh` | 116 | 48 +chk | `Rsh` | - | args, stack, g | none | **SAR** |
| 2 | `MulOverflow` | 42 | 112 +chk | `umul` | - | args, stack, g | none | - |
| 3 | `Div` | 80 | 112 +chk | `udivrem`, rt.panicdivide | - (in callees) | args, stack, g | none | **DIV**, SDIV |
| 3 | `Mod` | 86 | 144 +chk | `udivrem`, rt.panicdivide | - (in callees) | args, stack, g | none | **MOD**, SMOD, ADDMOD, MULMOD |
| 3 | `SDiv` | 181 | 176 +chk | `Div` ×4 | - (in callees) | args, stack, g | none | **SDIV** |
| 3 | `SMod` | 111 | 112 +chk | `Mod` | - (in callees) | args, stack, g | none | **SMOD** |
| 3 | `AddMod` | 216 | 368 +chk | `udivrem`, `Mod` | - (in callees) | args, stack, g, global | none | **ADDMOD** |
| 3 | `MulMod` | 109 | 320 +chk | `umul`, `Reciprocal`, `reduce4`, `Mod`, `udivrem` | - (in callees) | args, stack, g | none | **MULMOD** |
| 3 | `Exp` | 172 | 160 +chk | `Mul` ×4, `squared` ×4 | 8 | args, stack, g, global | none | **EXP** |
| 3 | `Sqrt` | 172 | 144 +chk | `Lsh`, `Rsh`, `udivrem`, rt.panicdivide | 2 | args, stack, g | none | - |
| X | `Clone` | 27 | 48 +chk | rt.newobject → mallocgc | - | args, heap, g | none | - |

Bold opcodes are the ones where geth executes **this exact out-of-line function body**; see
"Does geth run these bodies?" below. Transitive callees needed for Tier 3 (all integer-only):
`udivrem` (203 instrs, 7 loops, calls `runtime.memmove`), `udivremKnuth` (158, 5 loops),
`udivremBy1` (71, 2 loops), `math/bits.Div64` (89, loops; software 128/64 division that
panics through `runtime.panicdivide` and `runtime.gopanic(overflowError)`), `runtime.memmove`
(154), `umul` (109, straight-line), `squared` (36, straight-line), `Reciprocal` (507, calls
`Lsh`), `reduce4` (210, 1 loop).

Memory facts established by `inventory.py` (forward provenance dataflow, see the JSON):

* Every Tier 1 and Tier 2 function touches only `[p, p+32)` of its `*Int` arguments, and
  nothing else except (for frames) the stack. No Tier 1–3 function body touches memory
  through anything but its pointer arguments, the stack, `g` (stack-guard read) and, for
  `Exp`/`AddMod`, one 32-byte `.rodata` constant (`Int{1,0,0,0}` at `0xe2b40` and a zero
  `[5]uint64` template at `0xe2d40`).
* Go keeps the frame pointer **below** the new SP (`stur x29, [sp, #-8]` after
  `str x30, [sp, #-N]!`), and register arguments are spilled into the **caller's** frame
  (`[sp_entry + 8, ...)`); e.g. `Div` uses `[sp_entry - 120, sp_entry + 32)`. Tier 1 needs
  no stack at all.
* `Byte` and `ExtendSign` index `z` by a register (`ldr x1, [x0, x1, lsl #3]`); the index is
  bounded (`< 4`) by an earlier compare, which the proof has to carry.
* No Tier 1/2 method has explicit nil checks: a nil pointer simply faults on the first load,
  which in Janus is `Fault.outsideAllocation`, so the region precondition subsumes non-nil.

## Specs

Notation (on top of `Janus.Arm64.State`):

```lean
def val (m : Memory) (p : Nat) : Nat := m.readLE p 32
-- = z[0] + 2^64 z[1] + 2^128 z[2] + 2^192 z[3]: limb 0 least significant, each limb
--   stored little-endian, so the 32 bytes read little-endian are exactly toNat of the limbs.
def toInt (v : Nat) : Int := if v < 2^255 then v else v - 2^256      -- two's complement
def ofInt (i : Int) : Nat := (i % 2^256).toNat
def disjointOrEq (p q : Nat) : Prop := p = q ∨ p + 32 ≤ q ∨ q + 32 ≤ p
```

### Common pre/postcondition (Tier 1)

For a function with pointer arguments `z, x, y, m` in `X0, X1, X2, X3` (Go ABIInternal; for
Tier 1 these are the only inputs besides scalar `X1`/`X2` arguments of `SetUint64`/`Lsh`/...):

* **Pre**: `pc = entry`, `X30 = exitAddr`; for every *written* pointer `p`,
  `mem.accessible p 32 true`; for every *read* pointer, `mem.accessible p 32 false`;
  `p + 32 ≤ 2^64`; and for every pair of pointer arguments `disjointOrEq p q`
  (equality is allowed in **every** combination; partial overlap is not covered).
* **Post**: `Program.run P (n+1) s = .ok (.returned s')` for the function's path length `n`
  (e.g. `Add`: 17 instructions → fuel 18); `s'.mem.regions = s.mem.regions`;
  bytes outside `[z, z+32)` unchanged (read-only methods: all bytes unchanged);
  `s'.sp = s.sp`; `X28` (g) and `X29` (frame pointer) unchanged; and the functional result
  below. Return values: `*Int` results are `X0 = z` (the code leaves `X0` untouched);
  `bool` results are `0`/`1` in the full `X0` (or `X1` for the second result) because the
  compiler uses `cset`; `int` results are 64-bit two's complement in `X0`.
* **Never panics / never calls**: Tier 1 code contains no `bl`, so the outcome is always
  `.returned` (no stub outcome is reachable).

All values below are with `X := val s.mem x` etc. read **before** the call, so the statement
covers aliasing (`z = x`, `z = y`, `x = y`) directly.

### Tier 1a

| Method | Functional postcondition |
|---|---|
| `z.Add(x, y)` | `val z' = (X + Y) % 2^256` |
| `z.AddOverflow(x, y)` | `val z' = (X + Y) % 2^256`, `X1' = if X + Y ≥ 2^256 then 1 else 0` |
| `z.Sub(x, y)` | `val z' = (X + 2^256 - Y) % 2^256` |
| `z.SubOverflow(x, y)` | as `Sub`, `X1' = if X < Y then 1 else 0` |
| `z.Mul(x, y)` | `val z' = (X * Y) % 2^256` |
| `z.And/Or/Xor(x, y)` | `val z' = X &&& Y` / `X ||| Y` / `X ^^^ Y` (`Nat` bitwise) |
| `z.Not(x)` | `val z' = 2^256 - 1 - X` |
| `z.Neg(x)` | `val z' = (2^256 - X) % 2^256` |
| `z.Set(x)` | `val z' = X` |
| `z.Clear()` | `val z' = 0` |
| `z.SetUint64(v)` | `val z' = (X1).toNat` |
| `z.IsZero()` | `X0' = if Z = 0 then 1 else 0` (reads only `z`) |
| `z.IsUint64()` | `X0' = if Z < 2^64 then 1 else 0` (reads only `z[1..3]`) |
| `z.Lt(x)` | `X0' = if Z < X then 1 else 0` (receiver is the left operand) |
| `z.Gt(x)` | `X0' = if Z > X then 1 else 0` |

### Tier 1b

| Method | Functional postcondition |
|---|---|
| `z.Eq(x)` | `X0' = if Z = X then 1 else 0` |
| `z.Cmp(x)` | `X0' = if Z < X then 2^64-1 else if Z = X then 0 else 1` |
| `z.BitLen()` | `X0' = if Z = 0 then 0 else Nat.log2 Z + 1` |
| `z.Slt(x)` | `X0' = if toInt Z < toInt X then 1 else 0` |
| `z.Sgt(x)` | `X0' = if toInt Z > toInt X then 1 else 0` |

### Tier 2

| Method | Functional postcondition | Notes |
|---|---|---|
| `z.Lsh(x, n)` | `val z' = (X * 2^N) % 2^256`, `N = X2.toNat` (**all** `N`, incl. ≥ 256) | 6 paths by shift range; writes `z` and re-reads it |
| `z.Rsh(x, n)` | `val z' = X / 2^N` (all `N`) | same shape |
| `z.SRsh(x, n)` | `val z' = ofInt (toInt X / 2^N)` with floor division (`Int.fdiv`; `N ≥ 256` → `0` or `2^256-1`) | needs `Rsh` proved first; frame 48 + prologue |
| `z.Byte(n)` | `val z' = if NN < 32 then (Z / 256^(31-NN)) % 256 else 0` | **reads `z` as the value** and `n` as the index (EVM BYTE: `n`-th big-endian byte) |
| `z.ExtendSign(x, b)` | if `B ≤ 30`: with `k = 8B+8`, `t = X % 2^k`: `val z' = if t < 2^(k-1) then t else t + 2^256 - 2^k`; else `val z' = X` | EVM SIGNEXTEND with `b` = byte index |
| `z.Bytes32()` | bytes `[sp+8+i] = (Z / 256^(31-i)) % 256` for `i < 32` (big-endian, written into the caller's result slot) | `[32]byte` is not register-assignable, so the result goes to the stack |
| `z.SetBytes32(in)` | if `len < 32`: outcome `.stub "runtime.panicBounds"`; else `val z' = Σ_{i<32} in[i]·256^(31-i)` | `len` in `X2`; prologue reads `g` |
| `z.MulOverflow(x, y)` | `val z' = (X*Y) % 2^256`, `X1' = if X*Y ≥ 2^256 then 1 else 0` | needs `umul` (109-instr straight line) |

### Tier 3 (functional specs; proofs need callee extraction and loop invariants)

| Method | Functional postcondition |
|---|---|
| `z.Div(x, y)` | `val z' = if Y = 0 then 0 else X / Y`; never reaches `panicdivide` (the `udiv` path is guarded by `Y ≤ X < 2^64`, `Y ≠ 0`) |
| `z.Mod(x, y)` | `val z' = if Y = 0 then 0 else X % Y` |
| `z.SDiv(n, d)` | `val z' = if D = 0 then 0 else ofInt (Int.tdiv (toInt N) (toInt D))` (so `-2^255 / -1 = -2^255`) |
| `z.SMod(x, y)` | `val z' = if Y = 0 then 0 else ofInt (Int.tmod (toInt X) (toInt Y))` (sign of the dividend) |
| `z.AddMod(x, y, m)` | `val z' = if M = 0 then 0 else (X + Y) % M` (no 2^256 wrap) |
| `z.MulMod(x, y, m)` | `val z' = if M = 0 then 0 else (X * Y) % M` (full 512-bit product) |
| `z.Exp(b, e)` | `val z' = B^E % 2^256` |
| `z.Sqrt(x)` | `val z' = Nat.sqrt X` |

Tier 2/3 extra preconditions: a readable `g` region covering `[X28+16, X28+24)` whose
`stackguard0` is `≤ sp - frame` (otherwise the outcome is the `morestack` stub, which a spec
can also state); a writable stack region covering the footprint listed in
`inventory.json → memory_footprint.sp` (relative to entry SP, e.g. `Div`: `[-120, 32)`,
including callee frames for Tier 3); for `Exp`/`AddMod` a read-only region with the
32-byte `.rodata` constant.

### Aliasing

All 39 methods are **alias-safe for exact aliasing** (`z = x`, `z = y`, `z = m`, `x = y`):

* For every loop-free function, `inventory.py` enumerates all paths and checks that no
  limb of an input is loaded after the same bytes of `z` were stored (`alias_hazards` is
  empty for every loop-free target method; `Exp` and `Sqrt` have loops and were checked by
  reading the source). Typical shapes: `Add`/`Sub`/`And` interleave
  load-limb-i / store-limb-i, which is safe because limb `i` of `z` is only written after
  limb `i` of `x` and `y` are read; `Mul`, `Lt`, `Lsh`, `Rsh`, `ExtendSign` load all
  input limbs before the first store; `Byte` reads `n` fully before touching `z`.
* `Div`/`Mod`/`Sqrt`/`MulOverflow`/`Exp` write `z` only after the callee computed into a
  stack temporary; `AddMod` explicitly clones `m` on the stack when `z == m`
  (geth relies on this: `z.AddMod(x, y, z)`); `SDiv`/`SMod` negate into stack temporaries.

The only hazard reported is in `SetBytes32` when the byte slice partially overlaps `z`,
which never happens for an `Int`. geth's call patterns exercise aliasing
`z = y` (`y.Add(x, y)`), `z = x` (`x.Not(x)`, `value.Lsh(value, n)`, `num.ExtendSign(num, back)`),
`z = exponent` (`Exp`) and `z = m` (`AddMod`, `MulMod`), so the specs **must** be stated with
pre-call values as above, not as "`z` is fresh".

## Does geth run these bodies?

`core/vm/instructions.go` at go-ethereum `master` `1223cf3a` (fetched via
`gh api repos/ethereum/go-ethereum/contents/core/vm/instructions.go`) calls the methods
directly on stack slots (`x` = popped top, `y` = new top, result written in place):

```go
func opAdd(pc *uint64, evm *EVM, scope *ScopeContext) ([]byte, error) {      // L29
	x, y := scope.Stack.pop1Peek1()
	y.Add(x, y)
func opSub(...)        { x, y := scope.Stack.pop1Peek1(); y.Sub(x, y) }        // L35
func opMul(...)        { x, y := scope.Stack.pop1Peek1(); y.Mul(x, y) }        // L41
func opDiv(...)        { x, y := scope.Stack.pop1Peek1(); y.Div(x, y) }        // L47
func opSdiv(...)       { x, y := scope.Stack.pop1Peek1(); y.SDiv(x, y) }       // L53
func opMod(...)        { x, y := scope.Stack.pop1Peek1(); y.Mod(x, y) }        // L59
func opSmod(...)       { x, y := scope.Stack.pop1Peek1(); y.SMod(x, y) }       // L65
func opExp(...)        { base, exponent := scope.Stack.pop1Peek1(); exponent.Exp(base, exponent) } // L71
func opSignExtend(...) { back, num := scope.Stack.pop1Peek1(); num.ExtendSign(num, back) }        // L77
func opNot(...)        { x := scope.Stack.peek(); x.Not(x) }                   // L83
func opLt(...)         { x, y := scope.Stack.pop1Peek1(); if x.Lt(y) { y.SetOne() } else { y.Clear() } } // L89
func opGt(...)         { ... if x.Gt(y) ... }                                  // L99
func opSlt(...)        { ... if x.Slt(y) ... }                                 // L109
func opSgt(...)        { ... if x.Sgt(y) ... }                                 // L119
func opEq(...)         { ... if x.Eq(y) ... }                                  // L129
func opIszero(...)     { x := scope.Stack.peek(); if x.IsZero() { x.SetOne() } else { x.Clear() } } // L139
func opAnd(...)        { x, y := scope.Stack.pop1Peek1(); y.And(x, y) }        // L149
func opOr(...)         { x, y := scope.Stack.pop1Peek1(); y.Or(x, y) }         // L155
func opXor(...)        { x, y := scope.Stack.pop1Peek1(); y.Xor(x, y) }        // L161
func opByte(...)       { th, val := scope.Stack.pop1Peek1(); val.Byte(th) }    // L167
func opAddmod(...)     { x, y, z := scope.Stack.pop2Peek1(); z.AddMod(x, y, z) } // L173
func opMulmod(...)     { x, y, z := scope.Stack.pop2Peek1(); z.MulMod(x, y, z) } // L179
func opSHL(...) { shift, value := scope.Stack.pop1Peek1()                     // L188
	if shift.LtUint64(256) { value.Lsh(value, uint(shift.Uint64())) } else { value.Clear() } }
func opSHR(...) { ... if shift.LtUint64(256) { value.Rsh(value, uint(shift.Uint64())) } else { value.Clear() } } // L202
func opSAR(...) { shift, value := scope.Stack.pop1Peek1()                     // L216
	if shift.GtUint64(256) { if value.Sign() >= 0 { value.Clear() } else { value.SetAllOne() }; return }
	n := uint(shift.Uint64()); value.SRsh(value, n) }
func opPush32(...) { ... elem.SetBytes32(scope.Contract.Code[start:end]) ... }  // L1771
// opSload L493 / opSstore L504 / CREATE2 L696 / LOGn L1112: x.Bytes32()
```

(The quoted bodies are condensed one-liners of the real multi-line functions; the call
expressions are verbatim.) `gas_table.go` L371/L384 uses `stack.back(1).BitLen()` for EXP gas.

**Inlining matters.** `go build -gcflags=-m` on the library reports that `Add`, `Sub`,
`AddOverflow`, `SubOverflow`, `And`, `Or`, `Xor`, `Not`, `Neg`, `Lt`, `Gt`, `Eq`, `IsZero`,
`IsUint64`, `BitLen`, `Set`, `Clear`, `SetUint64`, `SetOne`, `Sign`, `Bytes32`, `SetBytes32` and
`Clone` are inlinable. To check what geth really runs, a probe binary importing
`github.com/ethereum/go-ethereum/core/vm@v1.17.9` was built with the same toolchain and
flags:

* `core/vm.opAdd`, `opSub`, `opNot`, `opLt`, `opGt`, `opEq`, `opIszero`, `opAnd`, `opOr`,
  `opXor` contain **no call** into uint256: the method body is inlined (for `opAdd`, the same
  `ldr/ldr/adds|adcs/str` ×4 pattern, but on registers computed from the stack slice, plus
  two `panicBounds` checks and a stack-growth prologue).
* `opMul`→`(*Int).Mul`, `opDiv`→`Div`, `opSdiv`→`SDiv`, `opMod`→`Mod`, `opSmod`→`SMod`,
  `opExp`→`Exp`, `opSignExtend`→`ExtendSign`, `opSlt`→`Slt`, `opSgt`→`Sgt`, `opByte`→`Byte`,
  `opAddmod`→`AddMod`, `opMulmod`→`MulMod`, `opSHL`→`Lsh`, `opSHR`→`Rsh`, `opSAR`→`SRsh`
  call the out-of-line symbol.
* The out-of-line bodies in the geth probe are **instruction-for-instruction identical** to
  ours: `Mul`, `IsZero`, `Lsh`, `Rsh`, `Byte`, `ExtendSign`, `Slt`, `Sgt`, `Cmp`, `umul`,
  `squared` are byte-identical; `Div`, `Mod`, `SDiv`, `SMod`, `SRsh`, `MulMod`, `udivrem`
  differ only in `bl`/`adrp` displacements; `Exp`/`AddMod` additionally only in the
  `add x27, x27, #lo12` of the `.rodata` address.

So a proof about `uint256.(*Int).Mul` in `bin/uint256-arm64` is a proof about the code geth
executes for **MUL** (likewise SHL, SHR, SAR, BYTE, SIGNEXTEND, SLT, SGT, and, once Tier 3 is
done, DIV/SDIV/MOD/SMOD/ADDMOD/MULMOD/EXP), given a relocation-aware identity check. For
**ADD, SUB, LT, GT, EQ, ISZERO, AND, OR, XOR, NOT** the code geth runs is the inlined copy
inside `core/vm.opX`; the out-of-line proof is then a lemma-level template, and the honest
geth-facing target is `core/vm.opAdd` itself (a Tier-2 function: stack slice bounds checks
→ `panicBounds`, `g` prologue, 16-byte frame).

## Recommendations

1. **First proofs: `Add`, `IsZero`, `Lt`** (Tier 1a, disassembly below). No calls, no stack,
   no `g`; `Add` exercises `ldr`/`str`, `adds`/`adcs` and the carry chain; `Lt` exercises
   `ldp`, `subs`/`sbcs`, `ngc`, `neg`, `cmp`, `cset`; `IsZero` is the smallest reader. Then
   the rest of Tier 1a (mechanically similar), then `Mul` (straight line, but needs
   `umulh`/`madd` lemmas and a 64×64→128 carry argument).
2. **Then the out-of-line geth opcodes in Tier 1b/2**: `Slt`, `Sgt`, `Lsh`, `Rsh`, `Byte`,
   `ExtendSign` — no calls, no stack, but case splits on data and register-amount shifts.
3. **Then `core/vm.opAdd`** in a geth-linked binary as the first end-to-end "EVM ADD is
   correct and never panics given a stack with ≥ 2 items" theorem; it needs the `g`
   region, a stack region, and `panicBounds` as a stub.
4. **Tier 3 later**: `Div`/`Mod` pull in `udivrem` + Knuth + `math/bits.Div64` (software
   128/64 division with loops) + `runtime.memmove`; `Exp` needs loop invariants over four
   word loops and `Mul`/`squared` as proved lemmas.
5. **Out of scope**: `Clone` (allocates through `runtime.newobject` → `mallocgc`).

## Blockers / requirements on the rest of Janus

* **`g` and the stack-growth prologue** (all Tier 2 functions with `+chk`, all Tier 3):
  the first instruction loads `[x28, #16]`, so the caller must supply a readable region for
  `g` and choose `stackguard0`; `runtime.morestack_noctxt.abi0` must be registered as a
  `morestack` stub. Frames use pre-index `str x30, [sp, #-N]!` or
  `sub x20, sp, #N; stp x29, x30, [x20, #-8]; mov sp, x20` (the large frames of `AddMod`,
  `MulMod`, `Reciprocal`), and save
  `x29` *below* the new SP.
* **Caller-frame accesses**: functions with frames spill register arguments to
  `[sp_entry+8, …)` and `Bytes32` writes its result there; the stack region in the
  precondition must extend above the entry SP.
* **`.rodata` reads** (`Exp`, `AddMod`): `Program` has only code segments; the extractor
  must also copy the referenced 32 bytes of `.rodata` (and the identity check must cover
  them) so the caller can supply them as a read-only region.
* **Panic stubs**: `runtime.panicBounds`, `runtime.panicdivide` and `runtime.gopanic`
  (reached from `math/bits.Div64`) must be registered as `panic` stubs. In Go 1.26
  `panicBounds` is a single entry for all bounds failures, so one stub covers every
  bounds check.
* **Decoder coverage**: the aliases listed under "Instruction subset", notably
  register-amount shifts, `ngc`, `cset/cinc`, `extr`, `ldrsb`, register-offset
  `[xn, xm, lsl #3]`, and the `orr xd, xzr, #imm` form of `mov`.
* **Inlining**: as described above, Tier 1 methods are not what geth executes for
  ADD/SUB/LT/...; plan a `core/vm` target binary for those opcodes.

## Disassembly of the first three targets

Raw words as copied by the extractor (`bin/uint256-arm64`, `.text`).

### `github.com/holiman/uint256.(*Int).Add` — `z = X0, x = X1, y = X2`

```
a8550: f9400023  ldr   x3, [x1]
a8554: f9400044  ldr   x4, [x2]
a8558: ab030083  adds  x3, x4, x3
a855c: f9000003  str   x3, [x0]
a8560: f9400423  ldr   x3, [x1, #8]
a8564: f9400444  ldr   x4, [x2, #8]
a8568: ba030083  adcs  x3, x4, x3
a856c: f9000403  str   x3, [x0, #8]
a8570: f9400823  ldr   x3, [x1, #16]
a8574: f9400844  ldr   x4, [x2, #16]
a8578: ba030083  adcs  x3, x4, x3
a857c: f9000803  str   x3, [x0, #16]
a8580: f9400c21  ldr   x1, [x1, #24]
a8584: f9400c42  ldr   x2, [x2, #24]
a8588: ba020021  adcs  x1, x1, x2
a858c: f9000c01  str   x1, [x0, #24]
a8590: d65f03c0  ret
```

17 instructions, no branch. `X0` (= the returned `z`) is never written. The stores are
interleaved with the loads, which is still alias-safe because the store to limb `i` comes
after both loads of limb `i`.

### `github.com/holiman/uint256.(*Int).Lt` — receiver `z = X0`, `x = X1`; returns `Z < X`

```
aa020: a9400c02  ldp   x2, x3, [x0]
aa024: a9401424  ldp   x4, x5, [x1]
aa028: a9411c06  ldp   x6, x7, [x0, #16]
aa02c: a9412021  ldp   x1, x8, [x1, #16]
aa030: eb040042  subs  x2, x2, x4
aa034: fa050062  sbcs  x2, x3, x5
aa038: fa0100c1  sbcs  x1, x6, x1
aa03c: fa0800e1  sbcs  x1, x7, x8
aa040: da1f03e1  ngc   x1, xzr        // x1 = -borrow  (0 or 2^64-1)
aa044: cb0103e1  neg   x1, x1         // x1 = borrow   (0 or 1)
aa048: f100003f  cmp   x1, #0x0
aa04c: 9a9f07e0  cset  x0, ne
aa050: d65f03c0  ret
```

### `github.com/holiman/uint256.(*Int).IsZero` — `z = X0`; returns `Z = 0`

```
aa140: a9400801  ldp   x1, x2, [x0]
aa144: aa020021  orr   x1, x1, x2
aa148: a9410c02  ldp   x2, x3, [x0, #16]
aa14c: aa020021  orr   x1, x1, x2
aa150: aa030021  orr   x1, x1, x3
aa154: f100003f  cmp   x1, #0x0
aa158: 9a9f17e0  cset  x0, eq
aa15c: d65f03c0  ret
```
