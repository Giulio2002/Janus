# The amd64 (x86-64) backend

Janus proves theorems about Go functions compiled with `GOARCH=amd64`, against the machine code
in the ELF binary. This document describes the model, what a theorem means on amd64 (the
differences from `docs/SOUNDNESS.md`, which otherwise applies unchanged), the tooling and the
proofs.

| piece | files |
|---|---|
| machine state, faults, checked memory | `Janus/Amd64/State.lean` |
| instruction AST | `Janus/Amd64/Instr.lean` |
| decoder (bytes → instruction, length) | `Janus/Amd64/Decode.lean` |
| semantics | `Janus/Amd64/Exec.lean` |
| programs, runner, run lemmas | `Janus/Amd64/Program.lean`, `Janus/Amd64/Run.lean` |
| Go ABIInternal on amd64, specs | `Janus/Amd64/GoABI.lean` |
| proof automation | `Janus/Amd64/Tactic.lean`, `Janus/Amd64/TacticAttr.lean`, `Janus/Amd64/TacticExt.lean` (string instructions, block copies and fills) |
| extractor | `cmd/janus/amd64.go` (plus small dispatch edits) |
| differential oracle | `oracle-amd64/`, `Oracle/Amd64Main.lean`, `docs/ORACLE-AMD64.md` |
| tests | `JanusTests/Amd64.lean`, `cmd/janus/amd64_test.go` |
| proofs | `examples/proofs-amd64/<Function>/Proof.lean` |

## The model

**State.** The state has the 16 GPRs (encoding order `RAX RCX RDX RBX RSP RBP RSI RDI
R8..R15`), `RIP`, the six status flags, `XMM0`–`XMM15` (128 bits) and memory. Memory is the
checked byte memory shared with arm64 (`Janus.Arm64.Memory`): every access must lie inside one
caller-provided region that ends at or below `2^48`, and a store needs a writable region and
must not touch any read-only one. The bound is shared with arm64 and is sound for amd64 too:
every real amd64 user mapping lies below `2^47` (4-level paging; Go never asks Linux for 5-level
addresses), so every real call state is representable, and an address in `[2^47, 2^48)` is
non-canonical (`#GP` on hardware); a precondition that granted memory there would describe a
state no process can be in, it cannot make a claim about a real one. Linear address masking
(LAM), the amd64 analogue of arm64 top-byte-ignore, is off unless a process enables it with
`arch_prctl`, which Go does not do. Each flag is `some b` or `none`
(architecturally undefined). An instruction that reads an undefined flag (`Jcc`, `SETcc`,
`CMOVcc`, `ADC`, `SBB`, `CMC`) faults with `undefinedFlag`, so no proof can depend on a value
the SDM does not define.

**Decoder.** `decode : List Nat → Option (Instr × Nat)` is plain `Nat`/`List` code with two
structurally recursive helpers, so `decide` and the kernel evaluate it on literal bytes. It
handles legacy prefixes, REX, the one- and two-byte opcode maps, ModRM, SIB, RIP-relative and
`disp8`/`disp32` addressing, immediates, and the 15-byte limit. It is strict and rejects:

* `LOCK` except on the lockable read-modify-write forms with a memory destination (`ADD ADC
  AND BTC BTR BTS CMPXCHG CMPXCHG8B/16B DEC INC NEG NOT OR SBB SUB XOR XADD XCHG`), and
  `LOCK` together with `F2`/`F3` (the HLE hints);
* `FS`/`GS` and address-size prefixes;
* duplicate prefix groups (except `66`), and a REX that is not immediately before the opcode
  (hardware ignores such a REX);
* `66` on branches, `CALL`, `RET`, `PUSH`, `POP` and `LEAVE` (Intel and AMD differ);
* `F2`/`F3` except where they select an instruction (`F3` is `REP` on `MOVS`/`STOS`; `F2`
  and segment overrides on string instructions are rejected);
* segment overrides on branches (hints and CET `NOTRACK`);
* VEX, EVEX and XOP;
* `RCL`/`RCR` and the `SAL /6` alias;
* `F6`/`F7 /1`, `MOVSXD` without `REX.W`, and 16-bit `BSWAP`;
* bit-string `BT*` with a register offset into memory, and memory `POP`;
* every opcode not listed below.

**Supported instructions** (all operand sizes 8/16/32/64 where they exist):
`ADD OR ADC SBB AND SUB XOR CMP` (all forms), `TEST`, `MOV` (r/m, reg, imm, imm64),
`MOVZX MOVSX MOVSXD`, `LEA`, `INC DEC NOT NEG`, `MUL IMUL` (1, 2 and 3 operands), `DIV IDIV`,
`ROL ROR SHL SHR SAR` (imm, 1, CL), `SHLD SHRD`, `BT BTS BTR BTC`, `BSF BSR TZCNT LZCNT POPCNT`,
`BSWAP`, `SETcc`, `CMOVcc`, `Jcc` (rel8/rel32), `JMP` (rel, r/m), `CALL` (rel, r/m),
`RET` / `RET imm16`, `PUSH` (r, r/m, imm), `POP r`, `LEAVE`, `NOP` / multi-byte `NOP` / `PAUSE`,
`XCHG`, `CBW/CWDE/CDQE`, `CWD/CDQ/CQO`, `CLC STC CMC`, the SSE moves Go uses: `MOVUPS MOVUPD
MOVDQU` (unaligned) and `MOVAPS MOVAPD MOVDQA` (fault unless 16-aligned), `XORPS XORPD PXOR`,
`MOVD/MOVQ` between GPRs and XMM, and `MOVQ xmm/m64`; the atomics: `LOCK`-prefixed
read-modify-write forms, `XADD` and `CMPXCHG` (memory destination, locked or not),
`CMPXCHG8B`/`CMPXCHG16B`, `LFENCE MFENCE SFENCE`; and the string instructions `MOVS` and
`STOS` (all widths) with and without `REP`. `MULX`, `ADCX` and `ADOX` are not
modelled: Go does not emit them at `GOAMD64=v1` (the default). Over the Go-compiled code of
the standard-library packages measured in `docs/ORACLE-AMD64.md`, the decoder accepts 99.6% of
instruction occurrences. The rest is floating point, TLS loads through FS, AVX, and a few
system instructions.

**Semantics** follow the SDM *Operation* and *Flags Affected* sections:

* A 32-bit result zero-extends into the full register. This includes 32-bit `CMOV` with a
  false condition and 32-bit shifts by a masked count of 0, a case the oracle found.
* 8/16-bit results merge into the low bits, and `AH`..`BH` are bits 15:8.
* Flags the SDM lists as undefined are `none`. Where vendors differ, or the SDM's pseudocode
  and prose disagree, the model takes the undefined side: `ZF` after `BT*`, SAR `CF` for an
  8/16-bit count at or above the width, ROL/ROR `OF` at masked count 0.
* Undefined results fault (`undefinedResult`): BSF/BSR of 0 at 16/32 bits, and 16-bit
  SHLD/SHRD by more than 16. 64-bit BSF/BSR of 0 keeps the destination, which AMD documents,
  Linux relies on, and the oracle confirms on Intel.
* `#DE` is a fault (`divideError`), and so is a misaligned 16-byte SSE operand
  (`misaligned`).
* A read-modify-write destination must be writable before it is read.
* Branch targets `≥ 2^47` fault (`badTarget`). This is conservative: on hardware those
  targets are either non-canonical, which is `#GP`, or kernel/5-level addresses, which fault
  at fetch.
* **Atomics.** The model is single-threaded (one goroutine, no other agent writes memory), so
  `LOCK` changes nothing: a locked instruction has exactly the semantics of the unlocked one,
  with all flags, and the fences are `NOP`s. `XADD`: `TEMP ← DEST + SRC; SRC ← DEST; DEST ←
  TEMP`, flags of the `ADD`. `CMPXCHG`: flags of `CMP accumulator, DEST`; equal: `DEST ← SRC`
  (a 32-bit success leaves the upper half of `RAX` alone); not equal: `rAX ← DEST`
  (zero-extending at 32 bits) and `DEST` is written back unchanged, so it must be writable
  either way. `CMPXCHG8B/16B` change only `ZF`; `CMPXCHG16B` faults (`misaligned`) unless its
  operand is 16-aligned. Register destinations of `XADD`/`CMPXCHG` are not modelled (Go
  never emits them). Theorems about atomics therefore say nothing about concurrent
  executions: they are the sequential semantics of the code.
* **String instructions.** `MOVS`/`STOS` move or store one element of `w/8` bytes at
  `[RSI]`/`[RDI]` and advance the pointers; `REP` repeats this `RCX` times and leaves `RCX = 0`
  (64-bit address size: `67` is rejected). A `REP` instruction is the sequential repetition of
  its element step, which is its architectural result also with fast strings (SDM Vol. 1
  §7.3.9.3). The direction flag is not in the state: Go ABIInternal keeps `DF = 0` at calls
  (`abi-internal.md`: "The direction flag (D) is always cleared (set to the 'forward'
  direction) at a call."), `GoABI.CallSetup` describes such a call state, and no modelled
  instruction sets `DF` (`STD`, `POPF`, `IRET` are not modelled), so `DF = 0` in every state
  the model reaches and the string instructions always step forward. The native oracle checks
  this: an executed case that leaves `DF` set is a mismatch. The one place Go sets `DF` is the
  overlapping backward copy in `runtime.memmove` (`STD; REP MOVSQ; CLD`); `STD` is rejected, so
  a proof cannot take that path (it needs `dst` above and overlapping `src`, and more than
  256 bytes).
* **CPU-feature globals.** `runtime.memmove` reads `runtime.memmoveBits` and
  `runtime.memclrNoHeapPointers` reads `internal/cpu.X86.HasERMS`/`HasAVX2`, which Go sets at
  start-up from `CPUID`. They live in `.noptrbss`, so the extractor does not copy them; a
  theorem that reaches them states them in its precondition (readable, and the value it
  assumes), or quantifies over them. The AVX paths are VEX code, which is not modelled, so
  theorems that can reach them assume the feature bit is off (`HasAVX2 ≠ 1`, `memmoveBits &
  1 = 0`); everything else (`HasERMS`, `repmovsPreferred`) is quantified.
* `RIP` arithmetic is done on naturals. This is equal to the `BitVec` sum, and it keeps proof
  terms kernel-friendly: `BitVec.reduceAdd` proofs on large literals send the kernel into deep
  recursion.

**Program and runner.** An `Amd64.Program` is byte segments (one per function, the symbol's
full range, `INT3` padding included), runtime stubs and read-only data, reusing `Janus.Stub`,
`Janus.StubKind` and `Janus.DataSegment`. `fetch` returns the at most 15 bytes from `RIP` to the
end of its segment. An instruction that would cross a segment end is undecodable: it is never
stitched together from two segments. `Program.run`, `Outcome`, `Steps` and the run lemmas in
`Janus/Amd64/Run.lean` mirror the arm64 ones.

## What a theorem means on amd64

`docs/SOUNDNESS.md` applies, with these differences:

* **Trusted:**
  - the Lean x86-64 model (`Decode`, `Exec`, `State`). It is differentially tested against the
    host CPU, with 0 mismatches over 1,011,430 cases, and its undefined-flag sets are
    cross-checked against the Sail/ACL2 X86isa model (`docs/ORACLE-AMD64.md`). It is not
    proved;
  - the ELF byte copy in `cmd/janus/amd64.go`;
  - the stub classification (unchanged);
  - the Lean kernel.
  Reachability uses `x86asm` linear sweeps of each function and is untrusted: a missed callee
  only causes `noCode`.
* **Calls.** `GoABI.CallSetup` says:
  - `RIP = entry`;
  - the return address `p.exitAddr` is stored at `[RSP]`, as the caller's `CALL` left it.
    Specifications use `p.withExit ret` for a universally quantified admissible `ret`
    (`GoABI.RetAddr`: below `2^47`, outside the extracted code and stubs); `Ensures` does this
    itself, and direct `Returns`/`Panics` theorems take `ret` and `hret : RetAddr p ret`;
  - `X15 = 0`;
  - integer argument `i` is in `GoABI.argReg i`, in the order `RAX RBX RCX RDI RSI R8 R9 R10 R11`.
  The `RET` reads the return address from memory, so the precondition must provide that slot:
  `StackWritable s below above` with `above ≥ 8`, which also includes the `2^48` bound.
  Reaching `ret` counts as returning; since `ret` is arbitrary, only a jump to the value the
  caller stored (the `RET`) can reach it for every `ret`, as on arm64.
* **Outcomes.** As on arm64: `Returns`, `Panics` (a panic stub), `Faults` (any fault but
  `outOfFuel`: nil or out-of-bounds access, `#DE`, undefined flag, bad branch target, ...),
  `NeverPanics` (no panic stub **and** no fault; on hardware `SIGSEGV`/`SIGFPE` become Go
  panics) and `GrowsStack`.
* **Return obligations** (`GoABI.ABIReturn`): `RSP' = RSP + 8` (the return address is
  popped), and `RBP`, `R14` (g) and `X15` are restored. There are no other callee-saved
  registers.
* **Stack-growth prologue.** `CMPQ SP, 16(R14); JLS morestack` (and the `LEAQ`/`SUBQ` forms for
  bigger frames) falls through under `GoABI.StackGuardOK s k`.
* **CPU assumptions.** The theorems describe an x86-64 CPU in 64-bit user mode under Linux:
  - `RFLAGS.AC` is clear, so there are no alignment checks except where an instruction
    demands one;
  - `DF` is clear (the Go ABI guarantees it at calls, and no modelled instruction sets it;
    `MOVS`/`STOS` depend on it, see "String instructions");
  - the CPU implements `CMPXCHG16B` (every x86-64-v2 CPU; Go's `GOAMD64=v1` code does not
    emit it, it is modelled for completeness);
  - the CPU implements `POPCNT`, `LZCNT` and `TZCNT` (BMI1): on older CPUs `F3 0F BC/BD`
    execute as `BSF`/`BSR`. Any x86-64-v3 CPU qualifies; `GOAMD64=v1` code uses them only
    behind run-time feature checks.
* **Vendor neutrality.** Where Intel and AMD document different results or flags, the model
  takes the undefined side (fault or `none`). A proof cannot depend on the vendor.
* **Not modelled:**
  - floating point;
  - x87/MMX/AVX state and the upper YMM/ZMM halves;
  - MXCSR;
  - segment registers;
  - concurrency (other threads, memory ordering), `STD`/the direction flag, string
    instructions other than `MOVS`/`STOS`;
  - every other system feature.
  Code that uses them faults (`undecodable`) and cannot be proved to return.

## Proof automation

`Janus.Amd64.Tactic` is the amd64 analogue of `Janus.Tactic`:

* `janus64_intro hs` turns `hs : GoABI.CallSetup p entry [a₀, …] s` into `h_rip`, `h_ret`
  (the return-address slot, `= ret` for `p = p₀.withExit ret`), `h_x15`, and
  `h_a<i> : s.regs r = aᵢ` with `r` the evaluated `argReg i`. Specs start with
  `intro ret hret s hs hpre`.
* With a symbolic return address the executor finds `hret : RetAddr p₀ ret` in the context. It
  evaluates the program facts on the closed `p₀`, derives `rip ≠ ret` from `hret` (there is no
  code and no stub at `ret`), installs `(BitVec.ofNat 64 ret).toNat = ret` and
  `(ret < 2^47) = True` as rewrite rules for the `RET`, and recognises the return when the
  symbolic `RIP` is `BitVec.ofNat 64 ret`.
* `janus64_run [lemmas] (until [addr, …])?` symbolically executes `Reaches`, `Returns`,
  `Panics` or `GrowsStack` goals one instruction at a time. For each step it computes the
  literal `RIP`, decodes the bytes at tactic time, and proves `stepOK p pc bytes i len = true`
  by `Eq.refl true`, checked by the kernel. It then simplifies `exec i len s` with the
  `janus64_exec` simp set and the local state equations. Branches split the goal (into `hbr`
  cases), and `omega` prunes infeasible branches. `janus64_step` performs one step.
  `until` stops at a loop head, so a loop is proved by induction over the iteration count,
  with `Reaches.mono` and the inductive hypothesis (see `examples/proofs-amd64/Sum`).
* The simp set keeps a symbolic state in a normal form. Registers form a sorted, deduplicated
  `setRegF` chain. The `ADD`/`SUB` flags stay folded, with per-field equations. Each condition
  code has its own equation, and signed comparisons after `CMP` become `toInt` comparisons.
  Memory reads over writes are split into disjoint, same-address and inside cases, and
  addresses and carries become `Nat` arithmetic for `omega`. Its side conditions are
  discharged by `janus64_disch`: `decide` on closed goals (never `omega` from a possibly
  contradictory context), memory accessibility from local `accessible` facts, and `omega`.
* `GoABI.DataLoaded.readLE` turns reads of copied `.rodata` into literals, through `listLE`
  of the data bytes, evaluated by `decide`.
* `Janus.Amd64.TacticExt` (imported by `Janus`) extends the simp sets and adds the pieces the
  atomics and memory routines need, all proved from the model:
  - `REP STOS`/`REP MOVS` with a symbolic count: stop in front of the instruction
    (`janus64_run until [addr]`) and apply `Reaches.repStos`/`Reaches.repMovs`, which take
    the addresses and the count explicitly and continue from the closed form (`fillLE`,
    `copyLE`; `stosIter_ok`, `movsIter_ok`);
  - block copies: `copy_first`/`copy_step` turn a chain of chunk stores of loaded values into
    `readLE dst n = readLE src n`; `readLE_writeLE_last` splits a read at its last write;
  - zero fills: `Zeroed M M' d n` (`[d, d + n)` zeroed, nothing else changed) with
    `Zeroed.trans`, `Zeroed.readLE`, `Zeroed.readLE_outside`, `zeroed_fillLE`, and the
    `zeroed_writes` tactic for a chain of overlapping zero stores;
  - `bv_add_add_neg`: negative displacements in indexed addresses (`-16(DI)(BX*1)`) are folded
    with the literal on the left. The generic folding produced `n + (2^64 - k)`, whose kernel
    check unfolded `Nat.add` along the literal (minutes, then deep recursion);
  - `setWidth8_merge`/`setWidth16_merge` (a `SETcc` byte read back by `TEST`),
    `bv8_sub_eq_zero` (`CMPB m8, $c` on a feature byte as a `Nat` equation), and `bvn`, which
    closes `register = BitVec.ofNat 64 k` goals by `omega`.

## Proved (verified end to end by `janus verify`)

Run `scripts/build-examples-amd64.sh`, then `scripts/verify-amd64-examples.sh`. All of these
are about `artifacts/examples-amd64` (`examples/basic`, `GOAMD64=v1`, Go 1.26.0, built
`-trimpath -buildvcs=false`, so the binary does not depend on the git state). Each proof that
mentions a binary-specific address (a loop head, a `.rodata` constant or a global) keeps it in
one `def` at the top of the file. Adding functions to `examples/basic` can move them. They use only `propext`, `Quot.sound` and
`Classical.choice`, and `leanchecker` replays each one.

| function | theorem |
|---|---|
| `Add` | returns `[x + y]` |
| `Max` | returns `[if y < x then x else y]` (unsigned) |
| `Add128` | `hi·2^64 + lo = (xh:xl + yh:yl) mod 2^128` |
| `Mul64` | `hi·2^64 + lo = x·y` |
| `Add256` | `*z = (*x + *y) mod 2^256`, with `z` overlapping neither operand nor the return slot (operands may alias) |
| `Div` | returns `[x / y]` for `y ≠ 0`; `Proof.panics`: panics (`runtime.panicdivide`) for `y = 0` |
| `Get` | returns `xs[i]` when `i < len` (slice disjoint from the frame); `Proof.panics`: `runtime.panicBounds` when `i ≥ len` |
| `Sum` | returns `Σ xs[j] mod 2^64` (a loop, by induction; spill slot disjoint from the slice) |
| `AddThree` | `Add(Add(x, y), z)`: through the stack-check prologue and two calls |
| `Table` | `t[i & 7]` of the constant table (64 bytes of `.rodata` copied through `X14`) |
| `HexDigit` | byte `i & 15` of the `.rodata` string |
| `SetOne256` | `*z = 1` (32 bytes of `.rodata` through `X14`) |
| `GlobalTable` | `tbl[i & 7]` of the writable global, provided by the precondition |
| `Bump` | `counter += d` on the writable global, returning the new value |
| `AddLimbs` | `*z = (*x + *y) mod 2^256` by the 4-iteration carry loop (unrolled; carries through `SBB`/`NEG`) |
| `CopyWords` | returns `n = min(len(dst), len(src))` and `dst[j] = src[j]` for `j < n` (a loop writing memory, by induction; slices disjoint from each other and the frame) |
| `SumSquares` | `square(x) + square(y)`: the stack-check prologue and two calls |
| `AtomicAdd` | `LOCK XADDQ`: `*p = old + d` and returns `old + d` |
| `AtomicMax` | the `LOCK CMPXCHGQ` retry loop: returns `old` and leaves `*p = max(old, v)` (single-threaded: the CAS succeeds the first time; the retry edge is proved infeasible) |
| `CopyBlock` | `copy(dst[:], src[:])` of `[16]uint64` through the real `runtime.memmove` (its 65–128-byte SSE path): the 128 bytes at `dst` equal the old 128 bytes at `src`, for any overlap |
| `ClearWords` | `clear(b)` through the real `runtime.memclrNoHeapPointers`, for **every** length: all `len(b)` words are 0 and no other byte outside the frame changes. Covers the straight-line cases, the 256-byte `MOVDQU` loop and the `REP STOSQ` path; quantifies over `internal/cpu.X86.HasERMS` and assumes `HasAVX2 ≠ 1` |

## Known gaps

* `RCL`/`RCR`, `MULX`, `ADCX`/`ADOX`, VEX/AVX, `STD`/`CLD`, `CMPS`/`SCAS`/`LODS`, FS/GS-relative
  accesses (the TLS load `MOVQ FS:-8, R14` of ABI wrappers), and all floating point are not
  modelled. Their encodings fault. FS was left out on purpose: none of the target routines
  (the inlined atomics, `memmove`, `memclrNoHeapPointers`) uses it; it would need the FS base
  as a state parameter.
* `SETcc` is accepted only with `ModRM.reg = 0`, and `66`-prefixed branches, `PUSH` and `POP`
  are rejected. These are model gaps in the oracle, conservative by design.
* The undefined-flag sets of BSF/BSR/TZCNT/LZCNT/POPCNT/BSWAP/BTS/BTR/BTC are not
  cross-checked: the formal model does not implement those instructions.
* The tactic has no callee-summary (`Summary`) support yet: calls are stepped through inline,
  which is fine for the examples. When an address or aliasing fact is missing it usually
  fails with a "stuck at" message, but it can also time out when an aliasing side condition
  is phrased with unnormalised literals (`(0x5751b8#64).toNat`). Normalise preconditions with
  `BitVec.toNat_ofNat` first, as `examples/proofs-amd64/Bump` does.
