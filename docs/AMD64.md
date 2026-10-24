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
| proof automation | `Janus/Amd64/Tactic.lean`, `Janus/Amd64/TacticAttr.lean`, `Janus/Amd64/TacticExt.lean` (string instructions, block copies and fills), `Janus/Amd64/TacticAVX.lean` (vector operands, byte-mask lemmas, overlapping copies) |
| extractor | `cmd/janus/amd64.go` (plus small dispatch edits) |
| differential oracle | `oracle-amd64/`, `Oracle/Amd64Main.lean`, `docs/ORACLE-AMD64.md` |
| tests | `JanusTests/Amd64.lean`, `cmd/janus/amd64_test.go` |
| proofs | `examples/proofs-amd64/<Function>/Proof.lean` |

## The model

**State.** The state has the 16 GPRs (encoding order `RAX RCX RDX RBX RSP RBP RSI RDI
R8..R15`), `RIP`, the six status flags, the direction flag `df`, `YMM0`–`YMM15` (256 bits, as two fields: `xmm n` is bits
127:0 and `ymmHi n` bits 255:128), the `FS` segment base `fsBase` and memory. `ymmHi`,
`fsBase` and `df` have defaults (`0`, `false`), so states written without them still mean what they did; every
specification quantifies over them like over any other field. Keeping the upper lanes in a
field of their own matches the architecture: a legacy-SSE instruction writes only `xmm`
(bits 255:128 preserved, SDM Vol. 1 §14.1.3), a VEX.128 instruction writes `xmm` and zeroes
`ymmHi` of its destination, a VEX.256 one writes both. The AVX-512 state (`ZMM` bits 511:256,
`ZMM16`–`31`, mask registers) is not modelled; no modelled instruction reads it, VEX instructions
only zero it. Memory is the
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
* `GS` and address-size prefixes, and `FS` everywhere except on the ModRM memory operand of
  `MOV`, the ALU group, `TEST`, `MOVZX`/`MOVSX`/`MOVSXD` (in particular `LEA`, which ignores
  segments, string instructions, branches, register-only forms and SSE/AVX);
* duplicate prefix groups (except `66`), and a REX that is not immediately before the opcode
  (hardware ignores such a REX);
* `66` on branches, `CALL`, `RET`, `PUSH`, `POP` and `LEAVE` (Intel and AMD differ);
* `F2`/`F3` except where they select an instruction (`F3` is `REP` on `MOVS`/`STOS`; `F2`
  and segment overrides on string instructions are rejected);
* segment overrides on branches (hints and CET `NOTRACK`);
* EVEX and XOP, and every VEX instruction except the eleven below; VEX after any other prefix
  (`66 F2 F3 F0 REX` make it `#UD`; segment overrides are rejected too); a VEX instruction with
  a field the SDM reserves set (`VEX.vvvv ≠ 1111` where it is unused, `VEX.W1` on
  `VPBROADCASTB`, `VEX.L1` on `VZEROUPPER`, which is `VZEROALL`), the memory form of
  `VPMOVMSKB` and the register form of `VMOVNTDQ`;
* `RCL`/`RCR` at 8 and 16 bits (the count is reduced modulo 9/17) and the `SAL /6` alias;
* prefixes on `CLD`/`STD`;
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
`MOVD/MOVQ` between GPRs and XMM, `MOVQ xmm/m64`, `MOVSS`/`MOVSD` (the scalar moves), the
packed-integer compares and logic `PCMPEQB PAND POR PMOVMSKB PSHUFD PSHUFLW PUNPCKLBW`; the AVX
and AVX2 instructions of Go's `memmove`, `memclrNoHeapPointers` and `internal/bytealg`:
`VMOVDQU VMOVDQA VMOVNTDQ VPXOR VPAND VPOR VPCMPEQB VPMOVMSKB VPTEST VPBROADCASTB VZEROUPPER`
(128 and 256 bits, 2- and 3-byte VEX); `RCL`/`RCR` at 32 and 64 bits; the hints
`PREFETCHNTA/T0/T1/T2` and `CLD` (no-ops in the model); `FS`-relative memory operands on the
integer forms above (the TLS load `MOVQ FS:-8, R14`); the atomics: `LOCK`-prefixed
read-modify-write forms, `XADD` and `CMPXCHG` (memory destination, locked or not),
`CMPXCHG8B`/`CMPXCHG16B`, `LFENCE MFENCE SFENCE`; and the string instructions `MOVS` and
`STOS` (all widths) with and without `REP`. `MULX`, `ADCX` and `ADOX` are not
modelled: Go does not emit them at `GOAMD64=v1` (the default). In the `sync/atomic`, `bytes`
and `strings` test binaries 97.9–98.1% of the Go-compiled functions and 53% of the assembly
functions decode completely (`docs/ORACLE-AMD64.md`); with the SSE scalar floating point
(`UCOMISD`, `CVT*`, arithmetic, `ROUNDSD`) now modelled, what is left is `SYSCALL`,
AES/SHA/CRC32, AVX-512, `VFMADD231SD` and `PCMPESTRI`.

**Semantics** follow the SDM *Operation* and *Flags Affected* sections:

* A 32-bit result zero-extends into the full register. This includes 32-bit `CMOV` with a
  false condition and 32-bit shifts by a masked count of 0, a case the oracle found.
* 8/16-bit results merge into the low bits, and `AH`..`BH` are bits 15:8.
* Flags the SDM lists as undefined are `none`. Where vendors differ, or the SDM's pseudocode
  and prose disagree, the model takes the undefined side: `ZF` after `BT*`, SAR `CF` for an
  8/16-bit count at or above the width, ROL/ROR `OF` at masked count 0.
* Undefined results fault (`undefinedResult`): BSF/BSR of 0 at every width (Intel leaves the
  destination undefined; AMD documents, and this Intel CPU shows, that it is kept — a vendor
  difference, so the model faults; audit round 2, LOW-2), and 16-bit SHLD/SHRD by more than 16.
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
  never emits them). **Split locks:** a locked access (every `LOCK` form, and `XCHG` with a
  memory operand, which is always locked) faults (`misaligned`) unless its operand is naturally
  aligned (`Instr.locked`). A locked access that straddles a cache line is a *split lock*:
  Linux with `split_lock_detect=fatal` sends `SIGBUS`, and in the default `warn` mode it traps
  and delays the thread. Natural alignment never splits a line of any size of 16 bytes or more,
  so the rule is independent of the line size; Go aligns every word it accesses atomically
  (audit round 2, LOW-1). On this host (`warn` mode) a misaligned locked access completes, so
  the oracle reports those cases as model gaps. Theorems about atomics therefore say nothing about concurrent
  executions: they are the sequential semantics of the code.
* **String instructions.** `MOVS`/`STOS` move or store one element of `w/8` bytes at
  `[RSI]`/`[RDI]` and advance the pointers; `REP` repeats this `RCX` times and leaves `RCX = 0`
  (64-bit address size: `67` is rejected). A `REP` instruction is the sequential repetition of
  its element step, which is its architectural result also with fast strings (SDM Vol. 1
  §7.3.9.3). **The direction flag** is the state field `df`: `CLD`/`STD` write it, and with
  `df = true` the element step decrements `RSI`/`RDI` instead (`movsIterB`, `stosIterB`;
  modelled exactly rather than faulting, so `runtime.memmove`'s overlapping backward copy
  `STD; REP MOVSQ; CLD` is decodable and provable). Go ABIInternal keeps `DF = 0` at calls
  (`abi-internal.md`: "The direction flag (D) is always cleared (set to the 'forward'
  direction) at a call."), so `GoABI.CallSetup` requires `s.df = false` and `janus64_intro`
  adds `h_df`. Before audit round 2 the state had no `DF` and string instructions always
  stepped forward; that was sound for call theorems, but a theorem about an arbitrary
  mid-function state (`DFRepro.memmove_backward_rep_copies_forward`, about the `REP MOVSQ` right
  after memmove's `STD`) could claim a forward copy that hardware never performs. With `df` in
  the state such a claim holds only for `df = false` states, and
  `JanusTests.Amd64.df_backward_not_forward` checks that from `df = true` the copy goes
  backward. The native oracle sets `DF` in a quarter of its cases and compares it.
* **CPU-feature globals.** `runtime.memmove` reads `runtime.memmoveBits` and
  `runtime.memclrNoHeapPointers` reads `internal/cpu.X86.HasERMS`/`HasAVX2`, which Go sets at
  start-up from `CPUID`. They live in `.noptrbss`, so the extractor does not copy them; a
  theorem that reaches them states them in its precondition (readable, and the value it
  assumes), or quantifies over them. The AVX paths are modelled: `Equal64` quantifies over
  `HasAVX2` (both the AVX2 and the SSE loop of `memeqbody` are proved), `CopyBlock512` assumes
  `memmoveBits` has `avxSupported` set and quantifies over `repmovsPreferred`. `ClearWords`,
  written before VEX was modelled, still assumes `HasAVX2 ≠ 1`.
* **Vector instructions.** Vector values are naturals `< 2^l` (`l = 128` or `256`), byte `i`
  being `v / 256^i % 256`; `PCMPEQB`, `PMOVMSKB`, `PUNPCKLBW` and `VPBROADCASTB` are byte-lane
  recursions (`cmpeqBytes`, `msbBytes`, `unpackLoBytes`, `replBytes`). Legacy-SSE memory operands
  of the packed-integer instructions must be 16-aligned (`misaligned` otherwise), VEX ones
  need no alignment except `VMOVDQA` and `VMOVNTDQ` (`l/8` bytes). `VMOVNTDQ`'s non-temporal
  hint changes only the memory ordering towards other agents, so it is an ordinary store in the
  single-threaded model. `VPTEST` sets `ZF = (a AND b = 0)`, `CF = (b AND NOT a = 0)` and clears
  `AF OF PF SF`. `VPMOVMSKB`/`PMOVMSKB` zero-extend the mask into the 64-bit register.
  `MOVSS`/`MOVSD` from memory zero bits 127:32/127:64, register to register they replace only
  the low lane. A `PREFETCHh` has no architectural effect and never faults, so it is a no-op.
* **FS.** An `FS`-relative operand is at `fsBase + ea (mod 2^64)` and goes through the same
  checked memory as every other access: Go's TLS (the `g` slot at `FS:-8`) is ordinary memory a
  precondition provides (`GoABI.TlsG s`: the slot is readable and holds `R14`; `TlsG.load`
  evaluates the TLS load). No modelled instruction changes `fsBase` (`WRFSBASE` and `arch_prctl`
  are not modelled).
* **RCL/RCR** (32/64 bits) rotate the `w + 1`-bit value `CF:dst`; they read `CF` (fault if it is
  undefined) unless the masked count is 0; `OF` is defined only for a count of 1 (a masked count
  of 0 makes it undefined, as for `ROL`/`ROR`: the SDM pseudocode's choice).
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
    host CPU, with 0 mismatches over 3,420,590 cases (the final runs of this model: `FS`, AVX, `DF`, split locks), and its undefined-flag sets are
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
  - the direction flag is clear (`df = false`);
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
  - Linux may enforce split-lock detection (`split_lock_detect=fatal`): the model's locked
    accesses must be naturally aligned (see "Atomics");
  - the CPU implements `CMPXCHG16B` (every x86-64-v2 CPU; Go's `GOAMD64=v1` code does not
    emit it, it is modelled for completeness);
  - the CPU implements `POPCNT`, `LZCNT` and `TZCNT` (BMI1): on older CPUs `F3 0F BC/BD`
    execute as `BSF`/`BSR`. Any x86-64-v3 CPU qualifies; `GOAMD64=v1` code uses them only
    behind run-time feature checks;
  - the CPU implements AVX and AVX2 and the OS has enabled the YMM state (Linux does whenever the
    CPU has AVX), whenever a VEX instruction executes. `GOAMD64=v1` code executes VEX only behind
    its CPU-feature globals (`internal/cpu.X86.HasAVX2`, `runtime.memmoveBits`), which Go sets at
    start-up from `CPUID`, so a theorem whose precondition states those globals describes a real
    process on a CPU that has the features. A theorem that quantifies over them (such as
    `Equal64`) also covers states in which they claim AVX2 on a CPU without it; such states do
    not occur in a Go process.
* **Vendor neutrality.** Where Intel and AMD document different results or flags, the model
  takes the undefined side (fault or `none`). A proof cannot depend on the vendor.
* **Not modelled:**
  - floating point other than the SSE scalar instructions (`docs/SOUNDNESS.md`, "Floating
    point"): packed SSE arithmetic, VEX/EVEX floating point, x87;
  - x87/MMX state, AVX-512 state (`ZMM` bits 511:256, `ZMM16`–`31`, masks);
  - writes of `MXCSR`'s control bits (`LDMXCSR`; `State.mxcsr` is read and its flags raised);
  - segment registers other than the `FS` base, and the `GS` base;
  - concurrency (other threads, memory ordering), string instructions other than
    `MOVS`/`STOS`;
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
  of the data bytes, evaluated by `decide`; `janus64_data hd` does the same as `janus_data`
  (readability of each data segment and a rewrite rule evaluating loads at literal addresses).
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
* `Janus.Amd64.TacticAVX` (imported by `Janus`) adds the vector instructions:
  - `readV`/`writeV`/`setV`/`getV` are unfolded and `ymmHi` gets the `setXmmF` normal form;
    `ymmJoin_ofNat` re-assembles a 256-bit value written by `setV`, and the `_mod` lemmas drop
    the `mod 2^256` for 32-byte reads and `PCMPEQB` masks;
  - mask lemmas: `msbBytes_cmpeq` (`PMOVMSKB (PCMPEQB a b)` is all ones iff the bytes are
    equal), `msbBytes_land` (all ones of an `AND` iff of both), `msbBytes_cmpeq_land`, and the
    branch forms `avx2_mask_eq` (`CMPL DX, $-1`) and `mask16_test` (`CMPL DX, $0xffff`);
    `readLE_eq_halves` splits an equality of reads;
  - address arithmetic: `land_align32` (`ANDQ $-32` as `x - x % 32`), `align32_add_mod`;
    `setWidth8_merge_bv`, `bv8_and_one_eq_zero` (`TESTB $1, AL` on a feature byte),
    `setWidth8_merge_ite` (a `SETcc` result in `AL`);
  - overlapping copies: `copied_writes` proves `M'.bytes x = M.bytes y` for a chain of chunk
    stores of `M`'s bytes in any order, overlapping, byte by byte (`cb_step`, `cb_skip`);
    `readLE_of_bytes` turns that into a `readLE` equality.

It has the same interface as the arm64 automation (`docs/PROOFS.md`, *Tactics*):

| arm64 | amd64 | notes |
|---|---|---|
| `janus_run [l] until [..] calls [..] (budget := N)` | `janus64_run [l] until [..] calls [..] (budget := N)` | |
| `janus_step`, `janus_simp [l]`, `janus_arith`, `janus_data h`, `janus_cases h` | `janus64_step`, `janus64_simp [l]`, `janus64_arith`, `janus64_data h`, `janus64_cases h` | `janus64_arith` turns `SBB`/`ADC` carries `(decide (2^64 ≤ t)).toNat` into `t / 2^64` (`janus64_arith_norm`) |
| `janus_frame` | `janus_frame` | shared (memory is the same type) |
| `segAddr p "f"` | `segAddr p "f"`, `dataBase p i`, `ripTarget p pc`, `janus64_addrs` | layout-independent addresses, see below |

**Callee summaries.** `Summary p entry pre post` says: from any state at `entry` satisfying
`pre`, ordinary steps reach a state whose `RIP` is the return address the caller's `CALL`
pushed, `retAddrOf s` (the word at `[RSP]` on entry), satisfying `post s`. Prove it with
`janus64_run` on the `ReachesRet` goal (also with `calls [...]` for its own callees), and use it
with `janus64_run calls [h, …]`: at the callee's entry (after the `CALL` instruction) the
precondition is proved for the current state and the postcondition is destructured
(existentials, conjunctions, `s' = …` substituted). A leaf callee:

```lean
theorem square_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.square")
      (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => ∃ f, s' = { s with regs := setRegF (setRegF s.regs 0 (s.regs 0 * s.regs 0)) 4
                                         (s.regs 4 + 8), rip := retAddrOf s, flags := f }) := by
  intro s hpc ⟨h1, h2⟩
  janus64_run
  exact ⟨_, rfl⟩
```

The precondition must provide the return-address slot (`RET` reads it and checks it is below
`2^47`). A non-leaf callee's postcondition also says which memory it may change,
`MemFrame s.mem m [(rsp - frame, rsp), …]` (its saved `RBP`, the return addresses of its own
calls, spills into its caller's frame), proved by `janus_frame`; `POP RBP` restoring the
caller's `RBP` disappears from the register chain. `examples/proofs-amd64/AddThree` and
`SumSquares` use summaries; `bench/proofs-amd64/Chain1.lean` is a five-level chain.

**Layout independence.** No proof contains an address copied from a disassembly, so adding
functions to `examples/basic` (which moves code, data and globals) does not break them:

* loop heads are `Extracted.entry + off` (the offset within the function);
* callee entries are `segAddr Extracted.program "pkg.f"`;
* `.rodata` objects are `dataBase Extracted.program i` (the base of the `i`-th copied data
  segment; the extractor names segments by offset, so the index is the stable handle);
* writable globals, which the extractor does not copy, are `ripTarget Extracted.program pc`:
  the address the RIP-relative operand of the instruction at `pc` (e.g. `Extracted.entry`)
  refers to, read off the extracted code.

`janus64_addrs` (or `simp only [reduceSegAddr, reduceDataBase, reduceRipTarget] at h`) evaluates
these terms to literals, each by a kernel-checked `rfl` lemma, so that `omega` sees the same
numbers as the executor; the executor evaluates them itself in `until [...]`, `calls [...]` and
state equations.

**Stuck diagnostics** are the same as on arm64 (`docs/PROOFS.md`, *Troubleshooting*), with the
instruction printed in Intel syntax (`Janus.Amd64.Disasm.disasm`), and fault explanations for
`#DE`, undefined flags, misaligned SSE operands and bad branch targets.

## Proved (verified end to end by `janus verify`)

Run `scripts/build-examples-amd64.sh`, then `scripts/verify-amd64-examples.sh`. All of these
are about `artifacts/examples-amd64` (`examples/basic`, `GOAMD64=v1`, Go 1.26.0, built
`-trimpath -buildvcs=false`, so the binary does not depend on the git state). No proof contains
a hard-coded address (see *Layout independence* above), so adding functions to
`examples/basic` does not break them. They use only `propext`, `Quot.sound` and
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
| `AddThree` | `Add(Add(x, y), z)`: through the stack-check prologue and two calls, with a callee `Summary` of `Add` |
| `Table` | `t[i & 7]` of the constant table (64 bytes of `.rodata` copied through `X14`) |
| `HexDigit` | byte `i & 15` of the `.rodata` string |
| `SetOne256` | `*z = 1` (32 bytes of `.rodata` through `X14`) |
| `GlobalTable` | `tbl[i & 7]` of the writable global, provided by the precondition |
| `Bump` | `counter += d` on the writable global, returning the new value |
| `AddLimbs` | `*z = (*x + *y) mod 2^256` by the 4-iteration carry loop (unrolled; carries through `SBB`/`NEG`) |
| `CopyWords` | returns `n = min(len(dst), len(src))` and `dst[j] = src[j]` for `j < n` (a loop writing memory, by induction; slices disjoint from each other and the frame) |
| `SumSquares` | `square(x) + square(y)`: the stack-check prologue and two calls, with a callee `Summary` of `square` |
| `AtomicAdd` | `LOCK XADDQ`: `*p = old + d` and returns `old + d` (`p` 8-aligned: no split lock) |
| `AtomicMax` | the `LOCK CMPXCHGQ` retry loop: returns `old` and leaves `*p = max(old, v)` (single-threaded: the CAS succeeds the first time; the retry edge is proved infeasible; `p` 8-aligned) |
| `CopyBlock` | `copy(dst[:], src[:])` of `[16]uint64` through the real `runtime.memmove` (its 65–128-byte SSE path): the 128 bytes at `dst` equal the old 128 bytes at `src`, for any overlap |
| `ClearWords` | `clear(b)` through the real `runtime.memclrNoHeapPointers`, for **every** length: all `len(b)` words are 0 and no other byte outside the frame changes. Covers the straight-line cases, the 256-byte `MOVDQU` loop and the `REP STOSQ` path; quantifies over `internal/cpu.X86.HasERMS` and assumes `HasAVX2 ≠ 1` |
| `Equal64` | `bytes.Equal` of two `[64]byte` through the real `runtime.memequal`/`memeqbody`: `AL = 1` iff the 64 bytes are equal, else `AL = 0`, for **every** value of `internal/cpu.X86.HasAVX2` (the AVX2 loop: `VMOVDQU`, `VPCMPEQB`, `VPAND`, `VPMOVMSKB`, `VZEROUPPER`; the SSE loop: `MOVDQU`, `PCMPEQB`, `PAND`, `PMOVMSKB`), including `a = b` |
| `CopyBlock512` | `copy(dst[:], src[:])` of `[64]uint64` (512 bytes) through `runtime.memmove`'s **AVX path** (`VMOVDQU` loads, 32-aligned `VMOVDQA` stores, `VZEROUPPER`), for every alignment of `dst`, disjoint arrays, given `memmoveBits & 1 = 1`: the 512 bytes at `dst` equal the old ones at `src`. (256 bytes or fewer never reach the AVX path: `memmove` copies them with SSE.) |

## Known gaps

* 8/16-bit `RCL`/`RCR`, `MULX`, `ADCX`/`ADOX`, VEX instructions other than the eleven above,
  EVEX (AVX-512), `CMPS`/`SCAS`/`LODS`, `PCMPESTRI`, AES/SHA/CRC32, `GS`-relative accesses and
  floating point beyond the SSE scalar instructions are not modelled. Their encodings fault.
* Proofs whose loop invariants describe intermediate states and step a string instruction must
  carry `t.df = false` in the invariant (`Reaches.repStos`/`repMovs` take it as `hdf`), as
  `examples/proofs-amd64/ClearWords`' `Inv` does.
* `simp only [d]` on a definition `d := segAddr Extracted.program "f" + k` can hit the
  recursion limit on a large extraction (`memmove`); `unfold d at h` and then
  `simp only [reduceSegAddr, Nat.reduceAdd] at h` does not (`examples/proofs-amd64/CopyBlock512`).
* `Janus.Amd64.TacticAVX` normalises register arithmetic of the AVX loop only when the proof
  passes `BitVec.ofNat_add_ofNat` and a `BitVec.ofNat` subtraction rule to `janus64_run`
  (`examples/proofs-amd64/CopyBlock512`); without them the symbolic registers of a 3-iteration
  loop grow until the kernel's recursion limit. Proofs that compare vector masks make
  `msbBytes`/`cmpeqBytes` locally irreducible (unfolding the 32-lane recursions during `whnf`
  is the expensive part).
* `SETcc` is accepted only with `ModRM.reg = 0`, and `66`-prefixed branches, `PUSH` and `POP`
  are rejected. These are model gaps in the oracle, conservative by design.
* The undefined-flag sets of BSF/BSR/TZCNT/LZCNT/POPCNT/BSWAP/BTS/BTR/BTC are not
  cross-checked: the formal model does not implement those instructions.
* Side conditions are discharged by `omega`, which needs addresses as `Nat` terms; normalise
  preconditions phrased with BitVec literals (`(0x5751b8#64).toNat`) with
  `BitVec.toNat_ofNat`/`janus64_addrs` first, as `examples/proofs-amd64/Bump` does. If a
  discharger call is expensive the run now reports a heartbeat diagnostic instead of timing out
  silently.
