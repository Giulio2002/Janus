# Verification target: go-ethereum `core/vm` opcode functions

The EVM's arithmetic, comparison, bitwise and shift opcodes, as compiled into a real program
that imports `github.com/ethereum/go-ethereum/core/vm`. This records what the compiler emitted
for `linux/arm64`, what `janus extract` copies for each opcode function, whether the trusted
Lean decoder accepts every copied word, and the memory an opcode touches, so that a proof can
state its precondition.

* Source: `github.com/ethereum/go-ethereum v1.17.9` (pinned in `go.mod`/`go.sum`,
  `h1:p05tsTJyvqI1WKBZlBl9+wYQG1eo/qVwmz66owsp+yA=`), which depends on
  `github.com/holiman/uint256 v1.3.2` (the version of `targets/uint256`).
* Toolchain: `go1.26.0`, `GOOS=linux GOARCH=arm64 GOARM64=v8.0 CGO_ENABLED=0 -trimpath
  -buildvcs=false`, no PGO profile. The build is reproducible (same SHA-256 from two builds,
  the second with an empty Go build cache):
  `bin/geth-vm-arm64` SHA-256 `8a5d97fae19966ffc98c13fa04d3bf85d7e155c8a69debed2042aa9eca0e2292`.
* Files: `main.go` (keeps the opcodes alive), `build.sh`, `inventory.sh` (regenerates the
  table below with `janus extract` and `janus blockers`).

```sh
targets/geth/build.sh
targets/geth/inventory.sh      # prints the table; artifacts in artifacts/geth/<opcode>
janus extract targets/geth/bin/geth-vm-arm64 github.com/ethereum/go-ethereum/core/vm.opAdd artifacts/opAdd
```

## How the opcodes are kept

The opcode functions (`opAdd`, ..., `opExp`) are unexported. `main.go` calls the exported
`vm.LookupInstructionSet(params.Rules{...})` with every fork flag derived from `os.Args`, so
every per-fork constructor (`newFrontierInstructionSet` ... `newBogotaInstructionSet`) is
reachable. Those constructors store the opcode functions as `executionFunc` values in the
`JumpTable`, so the linker keeps each function body, compiled exactly as for any importer
(no `-ldflags=-X`, no `linkname`, no source changes). The symbols are
`github.com/ethereum/go-ethereum/core/vm.<name>`. In v1.17.9 the shift opcodes are spelled
`opSHL`, `opSHR`, `opSAR`; all others as in the list below. `vm.NewCancunInstructionSetForTesting`
does not exist in v1.17.9.

`core/vm/interpreter_gen.go` (the generated `execUntraced` fast path) calls the same functions by
name. Without a PGO profile they are not inlined there, so the out-of-line bodies are the code
that the interpreter actually runs.

## Inventory

Instrs = copied words (trailing `udf` padding excluded). Funcs = segments in the extraction
(entry + direct-branch callees). Stubs are recorded, not copied (`rt.` = `runtime.`). Read-only
data = `Program.data` objects copied from `.rodata`. Writable refs = addresses of writable globals
the code computes; they are reported and **not** copied, so any load from them faults unless the
precondition adds a region. Lean decode = `janus blockers`: every distinct copied word run through
`Janus.Arm64.decode`. All extractions are within the default `--max-functions 64`, and `janus check`
passes on each.

| Opcode fn | Instrs (entry) | Funcs | Instrs (total) | Callees | Stubs | Read-only data | Writable refs (not copied) | Lean decode | ≤ 64 funcs |
|---|---|---|---|---|---|---|---|---|---|
| `opAdd` | 59 | 1 | 59 | - | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opSub` | 59 | 1 | 59 | - | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opMul` | 44 | 2 | 87 | `uint256.(*Int).Mul` | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opLt` | 61 | 1 | 61 | - | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opGt` | 62 | 1 | 62 | - | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opEq` | 66 | 1 | 66 | - | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opIszero` | 46 | 1 | 46 | - | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opAnd` | 59 | 1 | 59 | - | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opOr` | 59 | 1 | 59 | - | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opXor` | 59 | 1 | 59 | - | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opNot` | 41 | 1 | 41 | - | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opByte` | 43 | 2 | 67 | `uint256.(*Int).Byte` | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opSHL` | 56 | 2 | 133 | `uint256.(*Int).Lsh` | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opSHR` | 56 | 2 | 130 | `uint256.(*Int).Rsh` | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opSAR` | 83 | 3 | 273 | `uint256.(*Int).SRsh`, `uint256.(*Int).Rsh` | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opSignExtend` | 44 | 2 | 88 | `uint256.(*Int).ExtendSign` | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opSlt` | 55 | 2 | 102 | `uint256.(*Int).Slt` | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opSgt` | 55 | 2 | 103 | `uint256.(*Int).Sgt` | rt.morestack_noctxt, rt.panicBounds | - | - | all ok | yes |
| `opDiv` | 44 | 7 | 799 | `uint256.(*Int).Div`, `uint256.udivrem`, `runtime.memmove`, `uint256.udivremKnuth`, `uint256.udivremBy1`, `math/bits.Div64` | rt.gopanic, rt.morestack_noctxt, rt.panicBounds, rt.panicdivide | - | `runtime.arm64UseAlignedLoads`, `runtime.divideError`, `runtime.overflowError` | all ok | yes |
| `opSdiv` | 44 | 8 | 980 | `uint256.(*Int).SDiv`, `uint256.(*Int).Div`, `uint256.udivrem`, `runtime.memmove`, `uint256.udivremKnuth`, `uint256.udivremBy1`, `math/bits.Div64` | rt.gopanic, rt.morestack_noctxt, rt.panicBounds, rt.panicdivide | - | `runtime.arm64UseAlignedLoads`, `runtime.divideError`, `runtime.overflowError` | all ok | yes |
| `opMod` | 44 | 7 | 805 | `uint256.(*Int).Mod`, `uint256.udivrem`, `runtime.memmove`, `uint256.udivremKnuth`, `uint256.udivremBy1`, `math/bits.Div64` | rt.gopanic, rt.morestack_noctxt, rt.panicBounds, rt.panicdivide | - | `runtime.arm64UseAlignedLoads`, `runtime.divideError`, `runtime.overflowError` | all ok | yes |
| `opSmod` | 44 | 8 | 916 | `uint256.(*Int).SMod`, `uint256.(*Int).Mod`, `uint256.udivrem`, `runtime.memmove`, `uint256.udivremKnuth`, `uint256.udivremBy1`, `math/bits.Div64` | rt.gopanic, rt.morestack_noctxt, rt.panicBounds, rt.panicdivide | - | `runtime.arm64UseAlignedLoads`, `runtime.divideError`, `runtime.overflowError` | all ok | yes |
| `opAddmod` | 49 | 8 | 1026 | `uint256.(*Int).AddMod`, `uint256.udivrem`, `uint256.(*Int).Mod`, `runtime.memmove`, `uint256.udivremKnuth`, `uint256.udivremBy1`, `math/bits.Div64` | rt.gopanic, rt.morestack_noctxt, rt.panicBounds, rt.panicdivide | 40 B at 0x4a1408 (.rodata) | `runtime.arm64UseAlignedLoads`, `runtime.divideError`, `runtime.overflowError` | all ok | yes |
| `opMulmod` | 49 | 12 | 1822 | `uint256.(*Int).MulMod`, `uint256.umul`, `uint256.(*Int).Mod`, `uint256.udivrem`, `uint256.Reciprocal`, `uint256.(*Int).reduce4`, `runtime.memmove`, `uint256.udivremKnuth`, `uint256.udivremBy1`, `uint256.(*Int).Lsh`, `math/bits.Div64` | rt.gopanic, rt.morestack_noctxt, rt.panicBounds, rt.panicdivide | - | `runtime.arm64UseAlignedLoads`, `runtime.divideError`, `runtime.overflowError` | all ok | yes |
| `opExp` | 44 | 4 | 295 | `uint256.(*Int).Exp`, `uint256.(*Int).squared`, `uint256.(*Int).Mul` | rt.morestack_noctxt, rt.panicBounds | 32 B at 0x4a0c00 (.rodata) | - | all ok | yes |

Summary: **25/25 extract cleanly, 25/25 are fully decoded by the Lean model, all within 64
functions** (max 12, `opMulmod`). 18 opcodes are single-function or call one leaf `uint256`
method; `opAdd`, `opSub`, `opAnd`, `opOr`, `opXor`, `opNot`, `opLt`, `opGt`, `opEq`, `opIszero` have
the `uint256` operation inlined. Only `opExp` (the constant `1`, `Int{1,0,0,0}`) and `opAddmod`
(a 32-byte zero constant; the window runs to the next symbol, 40 bytes) load `.rodata`.

The division family (`opDiv`, `opSdiv`, `opMod`, `opSmod`, `opAddmod`, `opMulmod`) reaches
`runtime.memmove` and `math/bits.Div64`:

* `runtime.memmove` reads the `.noptrbss` flag `runtime.arm64UseAlignedLoads` on its large-copy
  path. A proof either shows that path is not taken (udivrem copies at most 4/5 words) or adds a
  one-byte read-only region for the flag with its run-time value as a hypothesis.
* `math/bits.Div64` loads the `error` interfaces `runtime.overflowError` / `runtime.divideError`
  from `.data` right before `runtime.gopanic` (`panic(overflowError)`). These paths are dead when
  `uint256.udivrem` calls it with a normalised divisor and `hi < y`; a proof must show that.

## Memory layout an opcode touches (v1.17.9 source)

All 25 functions have the signature of `executionFunc`
(`core/vm/jump_table.go`):

```go
func opX(pc *uint64, evm *EVM, scope *ScopeContext) ([]byte, error)
```

ABIInternal arguments: `X0 = pc`, `X1 = evm`, `X2 = scope`. **None of the 25 reads `pc` or
`evm`** (source: `core/vm/instructions.go`; the machine code only spills `X0`/`X1` on the
`morestack` path). Results: `([]byte, error)` in `X0..X4` = `(ptr, len, cap, itab, data)`; every
one of these opcodes returns `nil, nil`, so all five are `0` on return.

Structures (offsets in bytes, 64-bit words, little-endian):

```text
ScopeContext (interpreter.go)        Stack (stack.go)              stackArena (stack.go)
 +0  Memory   *Memory                 +0  bottom int                +0  data.ptr  *uint256.Int
 +8  Stack    *Stack     ───────────▶ +8  size   int                +8  data.len  int
 +16 Contract *Contract               +16 inner  *stackArena ─────▶ +16 data.cap  int
                                                                    +24 top       int

data.ptr ──▶ [ uint256.Int ][ uint256.Int ] ...   each Int = [4]uint64, limb 0 least significant,
               32 bytes at data.ptr + 32*i          element i at data.ptr + 32*i
```

The stack top is tracked twice: `inner.top` (absolute index of the first free slot in the arena,
shared by nested call frames) and `bottom + size` (this frame's view). Release builds keep them
equal: `top = bottom + size`.

How each opcode reaches its operands:

* `pop1Peek1` (all binary opcodes: ADD ... EXP, BYTE, SHL/SHR/SAR, SIGNEXTEND, comparisons):
  `inner.top -= 1; size -= 1`, then `x = &data[top']`, `y = &data[top'-1]` with `top'` the new
  top. The result is written into `y` (`data[top'-1]`); `x` is only read. Go emits two bounds
  checks against `data.len`: `top' <u len` and `top'-1 <u len` (unsigned, so `top' = 0` panics);
  failing either reaches `runtime.panicBounds`. **The two decrements are stored before the bounds
  checks**, so the panic path has already modified `inner.top` and `size`.
* `pop2Peek1` (ADDMOD, MULMOD): `inner.top -= 2; size -= 2`; `x = &data[top'+1]`,
  `y = &data[top']`, `z = &data[top'-1]`; result into `z`. Three bounds checks.
* `peek` (NOT, ISZERO): `&data[bottom + size - 1]`, read and written in place; reads `bottom`
  and `size` but not `inner.top`; nothing is popped (no stores to the structs).

Loads/stores per opcode (`opAdd` as compiled, 59 words):

```text
ldr  x5, [x2, #8]        ; scope.Stack
ldr  x6, [x5, #16]       ; stack.inner
ldr/str [x6, #24]        ; inner.top -= 1
ldr/str [x5, #8]         ; stack.size -= 1
ldp  x6, x7, [x5']       ; data.ptr, data.len   (x5' = inner)
ldr  x5, [x5', #24]      ; top'
...  bounds checks, then 4 x (ldr, ldr, adds/adcs, str) on data[top'] / data[top'-1]
mov  x0..x4, xzr ; ret
```

So a precondition for a `pop1Peek1` opcode needs these regions (all disjoint unless noted):

1. `scope`: 24 bytes readable (only `+8` is read).
2. `*scope.Stack`: 24 bytes, writable (`size` is stored).
3. `*stack.inner`: 32 bytes, writable (`top` is stored).
4. The element array `[data.ptr, data.ptr + 32*data.len)`, writable (at least elements
   `top-2` and `top-1` for binary ops, `top-3..top-1` for ADDMOD/MULMOD). The arena is a Go
   heap object distinct from the three structs; Go never makes the structs alias the array.
5. Stack: the frame below `SP` writable, `GoABI.StackWritable` with the depth of the deepest
   call chain (entry frames: 16 bytes for the inlined opcodes, 48 for the rest; callee frames
   from `docs/TARGETS.md`, e.g. `(*Int).Exp` 160, `(*Int).AddMod` 368, `(*Int).MulMod` 320,
   `udivrem` 224, `Reciprocal` 272), plus `GoABI.StackGuardOK` on `g` (`X28`, reads
   `g.stackguard0` at `+16`) so that the `morestack` prologue falls through. On the
   `morestack` path the function also stores `X0..X2` into `[SP+8, SP+32)`.
6. Data: `Program.DataLoaded` for `opExp` / `opAddmod`.

and the hypotheses `1 ≤ top ≤ data.len` (`2 ≤` for the binary ones, `3 ≤` for
ADDMOD/MULMOD) for the `Returns` theorem, or `top = 0 ∨ top > data.len` for the panic theorem.
The interpreter guarantees the stack depth by checking `minStack` before the call
(`operation.minStack`, `execUntraced`'s `sp < k` checks); this is outside the function and becomes
a hypothesis. Note the interpreter's check is on `size`, while the function indexes with
`inner.top`, so the precondition must also state `top = bottom + size` (or reason about `top`
directly).

The functional postcondition, e.g. for ADD: the 32 bytes at `data.ptr + 32*(top-2)` hold
`(x + y) mod 2^256` where `x`, `y` are the initial values at `top-1`, `top-2`; `inner.top` and
`size` are each one less; no other memory changes; `X0..X4 = 0`.

## Decoder coverage of the uint256 inventory

`janus blockers targets/uint256/bin/uint256-arm64` over all 52 symbols of
`targets/uint256/inventory.json` (2194 distinct words): **48 fully decoded, 0 with rejected
words**; 4 exceed 64 functions (`(*Int).Hex`, `(*Int).Clone`, `runtime.newobject`,
`runtime.slicebytetostring`: allocator/formatting closures of 400+ functions). With
`--max-functions 2000` those 4 reach SIMD (`ld1`, `cmeq`, ... in `runtime.memequal`,
`internal/bytealg.IndexByteString`, `internal/chacha8rand.block`), FP (`fcvt`, `fmov` in
`internal/strconv.genericFtoa`) and `svc` words, which the model rejects by design.
