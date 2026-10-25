# Go assembly: ABI0 and the ABI wrappers

Janus proves theorems about hand-written Go assembly (`.s` files) on arm64 and amd64, and about
Go code that calls it, the same way as about compiled Go: the bytes of the functions are copied
out of the ELF binary and executed by the Lean ISA model. What is new for assembly is the calling
convention, **ABI0**, and the wrappers the toolchain generates between it and Go's register-based
**ABIInternal**. This page covers the convention (`Janus/GoABI0.lean`,
`Janus/Amd64/GoABI0.lean`), the proof vocabulary (`Ensures0`, `Summary0`), the tactics
(`Janus/Tactic/ABI0.lean`), what the CLI does with assembly, and the examples (`examples/asm`).
What is trusted is in [SOUNDNESS.md](SOUNDNESS.md) ("Go assembly (ABI0)").

## 1. The convention

Every `TEXT ·f(SB)` in a Go assembly file is ABI0 unless it is declared `<ABIInternal>` (only the
runtime does that), and the linker names it `f.abi0`. Sources: `cmd/compile/abi-internal.md`
("ABI0", "Function call wrappers") and `doc/asm.html`, checked against the code Go 1.26.0 emits.

| | ABI0 arm64 | ABI0 amd64 | ABIInternal (for comparison) |
|---|---|---|---|
| arguments | caller's frame: word `i` at `8+8i(RSP)` (`x+0(FP)`); `0(RSP)` is the caller's saved-LR slot | caller's frame: word `i` at `8+8i(RSP)`; `0(RSP)` is the return address | registers (`R0`–`R15`; `RAX RBX RCX RDI RSI R8–R11`) |
| results | the frame words after the arguments (pointer-aligned) | same | the same registers |
| caller-saved | every register but the reserved ones, flags, all vector registers | every register but `RSP`/`RBP`, **including `R14` and `X15`**, flags, all vector registers | everything but the fixed registers |
| kept | `RSP`, `R28` (`g`), `R29` (frame pointer), `R18` | `RSP + 8` (popped), `RBP`, `FS` base, `DF` | arm64 the same; amd64 also `R14 = g`, `X15 = 0` |
| return | `X30` | `RET` pops `[RSP]` | same |

A frame is stated as a list of 64-bit **words**: an 8-byte argument or result is one word, a slice
header three, a string two, smaller fields that share a word are packed into it little-endian (the
Go struct layout). `args` are the argument words and `nres` the number of result words after them.

**Re-entry on amd64.** ABI0 code may leave anything in `R14` and `X15`, which ABIInternal code
relies on (`g`, zero). So after every ABI0 call, and before the Go call in an ABI0 → ABIInternal
wrapper, the compiler emits

```
XORPS X15, X15          // X15 := 0
MOVQ  FS:-8, R14        // R14 := g, from the TLS slot runtime.tlsg
```

`R14 = g` afterwards because the TLS slot holds `g`: `GoABI.TlsG s` (slot readable, holds `R14`)
is a **precondition** of every theorem whose run executes the reload, and the ABI0 code keeps the
`FS` base (`ABIReturn0.fs`; no modelled instruction writes it) and does not write the slot (its
memory postcondition). `Amd64.GoABI0.TlsG.reentry` and `TlsG.load_reentry` are that argument as
lemmas. On arm64 nothing is reloaded: `g` stays in `R28`, which ABI0 code must preserve (an
obligation in `ABIReturn0`, proved for each function, not assumed).

## 2. Specifications

Both ISAs have the same vocabulary (namespaces `Janus.GoABI0` and `Janus.Amd64.GoABI0`):

* `CallSetup0 p entry args nres s` — `s` has just called the ABI0 function at `entry`: `pc`/`RIP`
  at the entry, the return address in `X30` / at `[RSP]`, the argument words in the frame, the
  frame (`nres` result words included; on amd64 also the return slot) writable and below `2^48`
  (`FrameOK`); arm64 `RSP` 16-byte aligned, amd64 `DF` clear. Nothing else: no register
  arguments, `R14`/`X15` arbitrary. `setup_callSetup0` shows it is satisfiable.
* `ABIReturn0 s₀ s₁` — the obligations on return (table above). On arm64 it is `GoABI.ABIReturn`.
* `Ensures0 p entry args nres pre post` — for every admissible return address and every
  `CallSetup0` state satisfying `pre`, the call returns, obeys `ABIReturn0`, and `post s₀ s₁`.
  `EnsuresResults0 … post` states `post` on `results0 s₀ s₁ nargs nres`, the result words.
* `Ret0 s s' Q` / `retState0` — the shape of an ABI0 return: `s'` is `s` with every caller-saved
  register, the flags, the vector registers and the sticky FP status unspecified (existentially
  quantified), the kept registers as above, `pc` / `RIP` at the return address, and memory `m`
  with `Q m`. `ret0_iff` states it as equations (how a summary's postcondition is proved).
* `Summary0 p entry pre Q` — the **callee summary** of an ABI0 function: from any state at its
  entry satisfying `pre`, ordinary steps reach the return address in a `Ret0 s s' (Q s)` state.
  ABI0 returns results in memory, so `Q s m` says everything a caller may use. The idiom is a
  memory frame, `Q s m := MemFrame e m rs`: `m` agrees with the expected memory `e` (the call
  state's memory with the result words written) outside the scratch ranges `rs` the callee may
  clobber below `SP` (on arm64 below `SP - 8`: the caller's saved frame pointer is kept; for a
  leaf, the empty range `[(SP, SP)]` — not `[]`, whose read rule `simp` cannot apply).

Lemmas: `Ensures0.of_summary`/`of_summary0` (a summary proved once for callers is also the
standalone contract), `Summary0.call` (use at a direct call), `Summary0.mono`, `.withExit`,
`ABIReturn0.of_ret0`, `results0_getElem`, `CallSetup0.arg`/`frameWord_eq`/`frame_accessible`,
and `MemFrame.writeLE_congr` (with `MemFrame.writeLE_both` of `Janus.FFI` and `janus_frame`, the
tools for a summary's memory frame).

## 3. Calls and wrappers

All of this is ordinary machine code in the extraction, executed by the model; nothing about a
wrapper or a call sequence is assumed. A callee is composed through its summary with
`janus_run calls [h]` / `janus64_run calls [h]`, as for ABIInternal callees.

* **Direct ABI0 call from Go.** When the compiler knows the callee is assembly (same package, or
  through export data) it stores the arguments into its outgoing area, `BL`/`CALL f.abi0`, (amd64:
  the re-entry sequence,) and loads the results — no wrapper. Example: `CallXor`.
* **ABIInternal → ABI0 wrapper** `f` (`<autogenerated>`), for an assembly function used as a func
  value or from code that does not know its ABI: a frame, registers → frame words, the call,
  (re-entry,) result words → registers. Example: `XorWrapper` (the wrapper `example.com/asm.XorSlice`).
  Its theorem is an ordinary `Ensures`: the "wrapper lemma" for a function is its theorem,
  proved by composing the ABI0 body's `Summary0`.
* **ABI0 → ABIInternal wrapper** `g.abi0`, for a Go function `g` called from assembly: frame
  words → registers, (amd64: re-entry,) `BL`/`CALL g`, registers → result words. Example: `Twice`
  calls `double` through `double.abi0`; the wrapper is proved as a `Summary0` from `double`'s
  `Summary`, and `Twice` from the wrapper's.

## 4. Tactics

`janus_intro0 hs` (arm64) and `janus64_intro0 hs` (amd64) turn a `CallSetup0` hypothesis into
`h_pc`/`h_rip`, `h_lr`/`h_ret`, `h_al` (arm64) or `h_df` (amd64), the argument words
`h_rd_arg<i> : s.mem.readLE (SP + 8(i+1)) 8 = aᵢ.toNat` (named `h_rd…`, so `janus_run` uses them
as rewrite rules: the frame loads yield `aᵢ`), and the frame `h_fb`, `h_facc`. The post-processing
simp sets reduce `results0`/`wordsAt`, `Ret0`, `regs0`, `retState0` (and on amd64 `ABIReturn0`).

## 5. The CLI

Assembly needs no option: `janus extract` takes the linked name (`example.com/asm.XorSlice.abi0`
for the body, `example.com/asm.XorSlice` for its wrapper), follows direct calls into and out of
assembly, and records the entry's convention:

```text
$ janus extract artifacts/examples-asm-amd64 example.com/asm.Twice.abi0 artifacts/asm/amd64/Twice
Extracted example.com/asm.Twice.abi0: 3 function(s), 87 code byte(s), 0 stub(s), 0 data object(s) (0 bytes) into artifacts/asm/amd64/Twice/Extracted.lean
  entry: Go assembly, ABI0 (arguments and results in the caller's frame at 8(RSP)); state theorems with Janus.Amd64.GoABI0.Ensures0 (docs/ABI0.md)
  code  0x489300   41 bytes  example.com/asm.Twice.abi0
  code  0x489400   42 bytes  example.com/asm.double.abi0
  code  0x489200    4 bytes  example.com/asm.double
```

`identity.json` and `verified.json` record `entryABI` (`ABI0`/`ABIInternal`) and `entrySource`
(`assembly`: the pclntab file of the entry is a `.s` file; `abi-wrapper`: an `<autogenerated>`
`g.abi0`, or an `<autogenerated>` `f` next to an `f.abi0`) for such entries, and omit both for ordinary Go code (whose
identities are unchanged). `janus verify` prints the convention on its `Entry:` line, `janus
explain` on a `Calling convention:` line, and `janus verify` warns when the statement applies the
other convention's contract to `Extracted.entry` (`GoABI.Ensures` on an ABI0 function, or
`GoABI0.Ensures0` on Go code). A name that is missing while `name.abi0` exists (an assembly
function without a wrapper) gets a hint. The classification is informational: it never changes
what is extracted or what a theorem means.

## 6. The examples

`examples/asm` (`scripts/build-examples-asm.sh`, Go 1.26.0, `GOAMD64=v1`), proofs in
`examples/asm/proofs/{arm64,amd64}/`, verified by `scripts/verify-asm-examples.sh` (and
`scripts/verify-all-examples.sh`):

| Example | Entry | Statement | Shows |
|---|---|---|---|
| `AddAsm` | `AddAsm.abi0` | `EnsuresResults0`: result word `x + y` | a `Summary0` and `Ensures0.of_summary0` |
| `XorSlice` | `XorSlice.abi0` | `Ensures0`: result word `xs[0] ^ … ^ xs[len-1]`, only it written | a loop in assembly, for every length |
| `Twice` | `Twice.abi0` | `Ensures0`: result word `2x + 1`, memory frame | assembly with a frame calling Go through `double.abi0` (ABI0 → ABIInternal, re-entry on amd64) |
| `CallXor` | `CallXor` (Go) | `Ensures`: `xs[0] ^ … ^ 1` | a direct ABI0 call from Go; on amd64 the re-entry restores `R14 = g`, `X15 = 0` |
| `XorWrapper` | `XorSlice` (wrapper) | `Ensures`: the XOR in the result register | the ABIInternal → ABI0 wrapper |

Each holds on both ISAs; each file starts with the guarantee in plain English.

## 7. Limits

* ABI0 functions that read their arguments through the frame pointer of a caller, use the
  `NOFRAME` stack tricks of the runtime, switch stacks (`systemstack`, `mcall`, `gogo`), or write
  `g` are verified like any code, but their theorems need preconditions describing those states;
  the convention itself covers only the ordinary call/return.
* Floating-point and vector arguments are words of the frame like any other (ABI0 has no
  register arguments), so they need no extension; results in memory likewise.
* What decodes is limited by the ISA model ([COVERAGE.md](COVERAGE.md) §1.3): 90 of 145 ABI0
  assembly functions on arm64 and 91 of 170 on amd64 fully decode; the rest stop at an
  unsupported instruction (system calls, crypto and AVX-512 first), which faults in the model.
