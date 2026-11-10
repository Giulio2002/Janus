# How we know the ISA model is right

Moved out of the top-level README. Raw results and methods are in [validation/](validation/).

## How we know the model is right

The ISA models are trusted, so they are tested one instruction at a time against independent
references: an emulator, Arm's own specification, and real silicon. A **MISMATCH** is the only verdict that matters for soundness: the model claims a
successful step that the reference does not produce. A *model gap* (the model faults where hardware
succeeds) only costs coverage.

| Reference | What runs | Cases | MISMATCH | Details |
|---|---|---:|---:|---|
| qemu-aarch64 10.2.1 user mode (`-cpu max`) | arm64 model vs qemu, one instruction per case (whole ISA, plus a 1.13M-case scalar floating-point corpus with random `FPCR`/`FPSR`) | 766,650 + 1,131,099 | **0** | [ORACLE.md](validation/ORACLE.md) |
| Sail `arm-v9.4-a` (Arm's official ASL, translated) | arm64 model vs Arm's specification, same corpora | 766,650 + 1,131,099 | **0** | [ORACLE-SAIL.md](validation/ORACLE-SAIL.md) |
| Sail, misaligned-SP corpus | SP-alignment rule, which qemu cannot check | 102,460 | **0** | [ORACLE-SAIL.md](validation/ORACLE-SAIL.md) |
| Berkeley TestFloat 3e / SoftFloat 3e | the IEEE core and both floating-point wrappers vs SoftFloat (`ARM-VFPv2`, `-defaultNaN`, `8086-SSE`), every operation and rounding mode | 1,018,014,672 | **0** | [ORACLE.md](validation/ORACLE.md#testfloat-berkeley-testfloat-3e--softfloat-3e) |
| Native x86-64 (Xeon Gold 5412U, trap flag single-step) | amd64 model vs the host CPU, two seeds plus a vector harvest (incl. atomics, `REP` string ops in both directions, `FS`, YMM/AVX2, SSE, and 1.08M SSE scalar floating-point cases with random `MXCSR`) | 6,525,052 | **0** | [ORACLE-AMD64.md](validation/ORACLE-AMD64.md) |
| Sail/ACL2 X86isa | amd64 undefined-flag sets (sampled), and the `FS`/YMM/SSE-move/`RCL`/`RCR` classes it implements | 20,000 + 113,920 | 0 flags undefined there but defined by Janus | [ORACLE-AMD64.md](validation/ORACLE-AMD64.md#formal-x86-model-third-reference) |

Cases come from every distinct instruction word in real Go binaries (`math/big`, `crypto/sha256`,
`encoding/json`, `regexp`, …), targeted random encodings per instruction class, and fully random
words that check the decoder rejects what it does not understand. The amd64 oracle found one real model
bug before the final run (32-bit shifts by a masked count of 0 must still zero-extend); it is fixed
and pinned by a test.

<!-- TODO(coordinator): docs/design/ASL.md does not exist yet. JanusASL/ (a Sail slice of the Arm ASL) is in
progress; once there is an in-Lean ASL check with results, add it as a row here. -->

