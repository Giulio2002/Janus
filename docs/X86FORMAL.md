# JanusX86: the amd64 model checked against the Sail x86 model inside Lean

`docs/ORACLE-AMD64.md` checks `Janus.Amd64.step` against the host CPU. JanusX86 adds an
independent formal reference: the x86-64 ISA model of ACL2 X86isa, as translated to Sail by
rems-project/sail-x86-from-acl2, compiled to Lean by Sail's Lean backend and sliced to the
opcodes of the one- and two-byte maps (the whole of both maps since 2026-10-27, below). It is the amd64 counterpart of JanusASL (`docs/ASL.md`). Then:

* `lake exe janus-x86-check` runs the generated model and Janus `step` side by side in compiled
  Lean, on the whole amd64 oracle corpus, and compares both with the recorded hardware results.
  This is a **test**.
* `JanusX86.Proofs` holds Lean theorems, checked by the kernel, which state that the generated
  model and Janus agree on whole encoding classes, for all register, flag and memory values and
  every prefix sequence Janus accepts. These are **proofs**.

Everything lives in a separate Lake package, `JanusX86/` (`janus` by `path = ".."`, the Sail Lean
library lean-sail v7, as JanusASL). The main `Janus` library depends on neither, and JanusX86
does not use Mathlib.

```
scripts/x86formal.sh deps    # pinned toolchain: JanusASL's opam root (Sail 0.20.3 + patches), the slicing plugin, sail-x86-from-acl2
scripts/x86formal.sh gen     # slice the model, generate Lean, compare with the vendored copy
scripts/x86formal.sh build   # unpack the vendored model and build the package (X86Sail about 75 s)
scripts/x86formal.sh check   # build + janus-x86-check on artifacts/oracle-amd64/cases.jsonl
scripts/x86formal.sh prove   # build JanusX86.Proofs and audit their axioms
```

The local corpora under `artifacts/oracle-amd64/` and `artifacts/oracle-amd64-fp/` are kept
zstd-compressed (`*.jsonl.zst`, summaries uncompressed) to save disk. Run `zstd -d` on them
before rerunning `check`.

Every lake job runs under the memory guard (`scripts/lib/memguard.sh`), with `LEAN_NUM_THREADS`
set from the budget and a per-job peak of `JANUS_LAKE_JOB_MEM=3G` (measured with
`scripts/peak-mem.sh`: 2.6 GB for the largest model file, at most 1.9 GB for a proof file).
`.github/workflows/x86formal.yml` runs `build` and `prove` weekly, on demand, and on changes to
the amd64 model or JanusX86.

## Pins

| | |
|---|---|
| model | [rems-project/sail-x86-from-acl2](https://github.com/rems-project/sail-x86-from-acl2) `0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf` (the commit `oracle-amd64-formal/build.sh` uses) |
| Sail | 0.20.3 with JanusASL's patches (JanusASL's opam switch `sail-0.20.3-janus`, `scripts/asl.sh deps`) |
| Lean | 4.34.1 (`JanusX86/lean-toolchain`, as the main package) |
| lean-sail | v7, `8fc8e29d7a62f832346cc7548953e44ec17bc271` |
| vendored model | `JanusX86/vendor/X86Sail.tar.gz` (+ `.sha256`); `gen` reproduces it byte for byte |

## Results (2026-10-27, the slice of the whole one- and two-byte maps)

| corpus | cases | agree | gap | sail-defect | MISMATCH | `janus decodes, the slice excludes it` before |
|---|---:|---:|---:|---:|---:|---:|
| `full` | 505,715 | 389,933 | 111,815 | 3,967 | **0** | 787 |
| `sse` (SSE2/SSE3/SSSE3/SSE4 packed) | 863,656 | 54,326 | 806,921 | 2,409 | **0** | 351,786 |
| `x87` | 125,344 | 4,119 | 121,225 | 0 | **0** | 7,037 |
| `fp` (SSE scalar FP) | 551,478 | 0 | 551,478 | 0 | **0** | 0 |
| `v3` (BMI, FMA3, MOVBE, PSHUFB) | 217,698 | 0 | 217,698 | 0 | **0** | 14,249 |
| `crypto` (AES-NI, PCLMULQDQ, SHA-NI, ADX) | 98,745 | 0 | 98,745 | 0 | **0** | 42,311 |
| `avx` (VEX AVX/AVX2/FMA3) | 797,454 | 0 | 797,454 | 0 | **0** | 0 (VEX was already a gap) |
| `avx512` | 133,436 | 0 | 133,436 | 0 | **0** | 36,474 |
| **total** | 3,293,526 | 448,378 | 2,838,772 | 6,376 | **0** | **452,644** |

(The older 697,542-case corpus, which the previous run used, was the integer corpus of the first
decoder: it reported 162,406 such verdicts against the current decoder.) Before the change, the
`sse` corpus had 41 agreeing cases; with the whole maps in the slice, 95 SSE instruction
classes are checked against the Sail model state for state: `ADDSUBPS/PD HADDPS/PD HSUBPS/PD`,
`CVTDQ2PS/PD CVT(T)PS2DQ CVT(T)PD2DQ`, `LDDQU`, `MOVDDUP/MOVSLDUP/MOVSHDUP`
(D9), `MOVLPS/PD MOVHPS/PD MOVLHPS MOVHLPS`, `MOVMSKPS/PD`, `MOVNTDQ/PS/PD/I`, `MASKMOVDQU`,
`PACK*`, `PADD* PSUB*` (all widths, saturating), `PAVG* PCMPEQ* PCMPGT*`, `PEXTRW PINSRW`,
`PMADDWD PMAX* PMIN* PMUL*`, `PSADBW`, `PSHUFHW`, every `PSLL/PSRL/PSRA` form, `PUNPCK*`,
`RCPPS RSQRTPS`, `SHUFPS/PD`, `UNPCK*`. What stays a gap is what X86isa does not implement
(SSE4.1/4.2, SSSE3, SSE scalar FP, x87, crypto, BMI, FMA, VEX/EVEX); see below. Gap kinds on the
`sse` corpus: `Translation error: two-byte opcode … not translated` 455,568 (the `0F 38` and
`0F 3A` maps and the FP arms), `Opcode Unimplemented in x86isa!` 340,604, 10,749 other (Janus
refuses a misaligned or unmapped operand where the model runs, or the reverse).

### Summary

| | |
|---|---|
| corpora | `scripts/oracle-amd64.sh full` (505,715 cases) and the class runs `fp` (551,478), `v3` (217,698), `x87` (125,344), `sse` (863,656), `crypto` (98,745), `avx` (797,454) and `avx512` (133,436): 3,293,526 cases in all, each with the hardware results of the same run (`hw.jsonl`; native oracle: 0 MISMATCH) |
| `janus-x86-check` | **0 MISMATCH on every corpus**; `X86Config` holds on every case's pre- and post-state. Before the slice covered the whole maps: 452,644 `janus decodes, the slice excludes it` verdicts over these corpora (below). After: none |
| proofs | the audited class theorems listed below (an explicit list in `JanusX86/Audit.lean`, every statement printed); no `sorry`, no `native_decide`, no `bv_decide`; axioms: `propext`, `Classical.choice`, `Quot.sound` only |

The check runs the model twice per case, with the undefined-value source (`janus_undef`, below)
at 0 and at 1, and compares only what Janus defines (Janus' `Flags` are `Option Bool`; a flag
Janus leaves undefined is not compared). A verdict is:

* **agree**: both run and the final states agree on every GPR, `RIP`, the defined flags, `DF`,
  the vector registers Janus models and every byte of Janus' memory; or both reject (fault,
  divide error, non-canonical target).
* **gap**: Janus refuses (undecodable, outside its allocation, misaligned locked access,
  undefined result) or the model does (an opcode that X86isa does not implement, or a VEX/EVEX
  instruction). `janus decodes, the slice excludes it` is a MISMATCH: since 2026-10-27 no
  one- or two-byte arm is excluded, so it cannot occur for a legacy-encoded instruction. A gap never hides a wrong answer.
* **sail-defect**: Janus and the model disagree, **Janus agrees with the hardware result** of the
  same case, and the difference is one of the known model defects D1–D6 and D9 below (D7 and D8, found by proof, do not occur in the corpus).
* **MISMATCH**: anything else. `janus-x86-check` exits with code 1 if it finds any.

Check changes with the full-map slice: the EVEX stub (`janus-excluded: EVEX`) is a gap like the
VEX one; the Sail harness starts with `RFLAGS.IF` set (`0x202`, as a Linux user process and as
Janus' `rflagsImage`: `PUSHFQ` pushes it, and the hardware pushes it too, plus the `TF` the
single-stepping runner sets, which is why the verdict had been a MISMATCH on the 27 `PUSHFQ` cases
the newly kept `0x9C` arm exposed); and four `REP` string cases whose recorded hardware result was a
single iteration (`rcx` 0x7f of 0x80) were re-run natively (`oracle run` on the same cases: the
runner re-enters the instruction, `rcx = 0`, as Janus): the stored `hw.jsonl` was stale, so the
check was run with a fresh `hw.jsonl` of `cases.jsonl`. Every other newly reachable arm either
agrees, is unimplemented in the model, or is D9.

The counts below (D1–D8 and the gap kinds) are from the earlier 697,542-case run, before the
whole maps were sliced; the table above has the current ones.

Gaps by kind (`artifacts/x86formal/summary.txt`): `janus-undecodable/*` 128,941 (bytes outside
the Janus subset), `sail-unimplemented` 51,980 (opcodes X86isa does not implement, below),
`janus-outsideAllocation/*` 20,921, `janus-misaligned/*` 25,542, `janus-undefinedResult/*`
1,622, `janus-badTarget/sail-ok` 21.

### Model defects (Sail x86 against the hardware)

Each was found by the check, and in each the hardware result of the case (the native oracle's
`hw.jsonl`, the CPU executing the same bytes from the same state) equals Janus' result:

| | cases | encoding | the model | hardware (and Janus) | example (`verdicts.jsonl`) |
|---|---:|---|---|---|---|
| D1 cmpxchg-flags-operand-order | 2,149 | `CMPXCHG m, r` (`0F B0/B1`) | computes the flags of `m − rAX` (`gpr_arith_logic_spec` CMP with the operands swapped, `exchange.sail`) | the flags of `rAX − m` (SDM `CMPXCHG`: the accumulator compared with the destination) | `f0 0f b0 02`: flags janus 0x84, sail 0x11 |
| D2 rax-imm8-rexw | 2,270 | `op AL, imm8` (`04, 0C, …, 3C`, `A8`) with `REX.W` | operates on all of `RAX` (its `rax_size` honours `REX.W` on a byte opcode) | `REX.W` is ignored on byte operands: only `AL` | `66 4a 04 fa`: flags janus 0x95, sail 0x14 |
| D3 rotate-8-16-count-ge-width | 1,052 | `ROL/ROR r/m8, r/m16` with a masked count ≥ the width | rotates by the masked count (`rol/ror_spec_8/16` pass it to `rotate_left/right` unreduced), with a wrong result | rotate by `count mod width` | `4b c0 c2 29`: `r10` janus …53d, sail …53c |
| D4 movd-movq-to-xmm-no-zero-extension | 506 | `MOVD/MOVQ xmm, r/m` (`66 0F 6E`) | writes the low 32/64 bits and keeps the rest of the XMM register | zero-extends into the whole XMM register | `66 66 40 0f 6e 6e 00`: bits 32–127 of `xmm5` janus 0, sail kept |
| D5 rep-string | 4,785 | `REP MOVS/STOS` (`F3 A4/A5/AA/AB`) | executes one iteration per step and leaves `RIP` on the instruction | the whole repetition in one instruction (Janus' `step` semantics) | `f3 a4`: `rcx` janus 0, sail 2 |
| D6 ror-cf-from-bit-0 | 287 | `ROR` with count ≥ 2 | takes `CF` from bit 0 of the result (`ror_spec_*`, count ≥ 2 branch) | `CF` = the most significant bit of the result (SDM `ROR`) | `4a c0 cb 82`: flags janus 0xc0, sail 0xc1 |
| D7 noncanonical-rsp (found by proof) | 0 | `RET`/`RET imm16` (`C3/C2`), `POP r` (`58–5F`), `LEAVE` (`C9`) | the new `RSP` goes through `add_to_sptr`, which stops with the model error `:NON-CANONICAL-STACK-ADDRESS` when it is not canonical (`RSP + 8 + imm16`; `RSP + 8`; `RBP + 8`) | `RSP` takes the 64-bit value; a non-canonical stack pointer faults only at the next stack access | not in the corpus (needs `RSP`/`RBP` near `2^47`); `ret_agree` assumes `RSP + 8 + 2^16 ≤ 2^47`, `pop_agree` `RSP + 8 < 2^47`, `leave_agree` `RBP + 8 < 2^47` |
| D8 shld-shrd-cl-rip-relative (found by proof) | 0 | `SHLD/SHRD r/m, r, CL` (`0F A5/AD`) with a RIP-relative memory operand | `x86_shld_shrd` always tells the r/m decoder that one immediate byte follows (`num_imm_bytes = 1`), so a RIP-relative address is one byte too far for the `CL` forms | the address is relative to the end of the instruction, which has no immediate (SDM 2.2.1.6) | not in the corpus (Go emits only register forms); `shd_agree` excludes RIP-relative operands of `A5/AD` |

| D9 movddup-movsldup-dispatch-to-movlps | 2,411 | `MOVDDUP xmm, xmm/m64` (`F2 0F 12`), `MOVSLDUP xmm, xmm/m128` (`F3 0F 12`) | the `0F 12` dispatch arm calls `x86_movlps_movlpd_op_en_rm` for the `F2` and `F3` mandatory prefixes too (X86isa has no `MOVDDUP`/`MOVSLDUP` semantics): the low quadword of the destination is replaced by the memory quadword, nothing is duplicated | the low quadword duplicated into both halves (`MOVDDUP`), dwords `0 0 2 2` of the source (`MOVSLDUP`) | `f2 4b 0f 12 ea`: `ymm5` janus …ff00000008000000ff00000008, sail keeps the upper quadword; found by the full-map slice (the arm was excluded before) |

D5 is a difference of granularity rather than a wrong result (X86isa models one iteration);
the others are wrong results. D7 and D8 were found while proving the class theorems, not by the
corpus: D7 is unreachable with the stack in Janus' regions (below `2^47`), so the theorems carry
that bound, and D8 needs a RIP-relative `CL` double shift, which the theorem excludes. The class
theorems exclude exactly these encodings: D2 in `alu_ai_agree`; D3 (8/16-bit rotates by a masked
count ≥ the width) in `shift_agree` and `shift_agree_cf`; D6 in `shift_agree`, while
`shift_agree_cf` proves the `ROR` case with `CF` left unconstrained; D1 in `cmpxchg_agree`, which
proves every register and memory byte and `ZF` (the comparison's outcome) and leaves the other
status flags unconstrained; D7 and D8 as above.

**SSE scalar floating point** (`Decode.sseFp`: `ADD/SUB/MUL/DIV/MIN/MAX/SQRT SS/SD`, `(U)COMIS`,
`CVT*`, `CMPSS/SD`, `AND(N)/OR PS/PD`, `ROUNDSS/SD`, and `MXCSR`) is not covered by the formal
model: sail-x86-from-acl2 leaves every one of these two-byte opcodes (`0F 2A 2C–2F 3A 51 54–56
58–5A 5C–5F C2`) as `"Translation error: two-byte opcode … not translated"` (X86isa's
floating-point specification was not translated to Sail). The slice keeps their arms verbatim,
so the check reports them as `gap sail-unimplemented`: on the FP corpus of
`scripts/oracle-amd64.sh fp` (548,874 cases, native oracle 0 MISMATCH),
`artifacts/x86formal-fp/summary.txt` has **0 agree, 548,874 gap, 0 MISMATCH**. Janus' FP
semantics (`Janus/Amd64/Float.lean`) is checked against the hardware only.

X86isa (and so the Sail model) leaves unimplemented: `XORPS` (`0F 57`), `PXOR`, `PAND`, `POR`,
`PCMPEQB`, `PMOVMSKB`, `BSF`, `BSR`, `TZCNT`, `LZCNT`, `POPCNT`, `BSWAP`, `BTS/BTR/BTC`, `XADD`
(including `LOCK XADD`), `CMPXCHG8B/16B`, the fences, and every VEX encoding; these are
`gap sail-unimplemented` and are tested only by the native oracle. No class theorem is possible
for them, since the model's arm is `x86_model_error "Opcode Unimplemented in x86isa!"`.

**amd64 v3** (BMI1/BMI2 `ANDN BLSR BLSMSK BLSI BEXTR BZHI SHLX SHRX SARX RORX MULX PDEP PEXT`,
scalar FMA3, `MOVBE`, `PSHUFB`/`PSIGNB`) is not covered either. The pinned model leaves the
three-byte map `0F 38` (`MOVBE`, `PSHUFB`, `PSIGNB`) as `"Translation error: two-byte opcode 56
not translated"`. Every `VEX.0F38` arm (the BMI and FMA instructions) is `x86_model_error
"Opcode Unimplemented in x86isa!"` after the `#UD` checks, and `ext_vex_0f38_execute` is
`false`. These classes are tested only against the hardware. The model signals `#DE` as a model error
`:UNSIGNED-DIVIDE-ERROR-OVERFLOW`, which the check maps to Janus' divide-error fault (agree).

## What is proved

The theorems have one shape. For a Janus state `js` and a Sail state `s` with `Rel js s` and
`X86Config s`, when the memory at `RIP` holds `bytes` (`CodeAt`), Janus' prefix parser reads the
given opcode, and `Janus.Amd64.step bytes js = .ok js'`:

```
∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s'
```

so the model, run from `s`, completes the instruction and ends in a state related to Janus' final
state. The hypotheses never constrain register, flag or memory contents; they cover every ModRM,
SIB, displacement and RIP-relative form, every operand width, and every legacy/REX prefix
sequence Janus' decoder accepts.

`Rel js s` (`Proofs/Rel.lean`): the 16 GPRs, `RIP`, every status flag Janus defines (`FlagsRel`;
an undefined Janus flag is unconstrained), `DF`, `RFLAGS.AC = 0`, the `FS` base (`IA32_FS_BASE`),
and every byte Janus can read; Janus' regions lie below `2^47` (canonical lower half).
`X86Config s` (`Proofs/Config.lean`): 64-bit user mode as the harness sets it up (`EFER.LMA`, a
64-bit code segment, CPL 3, `CR0.AM = 0`, `CR4.OSFXSR`, the app-view memory model, no model or
fault state, register-write logging off, an undefined-value source present); `cfgOk_sound` shows
that a decidable check of it is sound, and the check verifies it on every case.

| class | theorem | status |
|---|---|---|
| ADD/OR/ADC/SBB/AND/SUB/XOR/CMP r/m, r (`00/01 … 38/39`), register destination | `alu_eg_reg_agree` | proved |
| … memory destination (every addressing form, `FS`) without `LOCK` | `alu_eg_mem_agree` | proved |
| … r, r/m (`02/03 … 3A/3B`), register and memory source | `alu_ge_agree` | proved |
| … AL/AX/EAX/RAX, imm (`04/05 … 3C/3D`) and TEST rAX, imm (`A8/A9`) | `alu_ai_agree` | proved except the byte forms with `REX.W` (D2) |
| … r/m, imm (`80/81/83 /0..7`) and TEST r/m, imm (`F6/F7 /0`), all destinations, without `LOCK` | `alu_ei_agree` | proved |
| TEST r/m, r (`84/85`) | `test_eg_agree` | proved |
| INC/DEC r/m (`FE/FF /0,/1`), NOT/NEG r/m (`F6/F7 /2,/3`), without `LOCK` | `unary_agree` | proved |
| MUL r/m (`F6/F7 /4`), all widths, CF/OF | `mul_agree` | proved |
| IMUL r/m one-operand (`F6/F7 /5`), all widths, CF/OF | `imul1_agree` | proved |
| MOV r/m, r and r, r/m (`88–8B`) | `mov_agree` | proved |
| MOV r/m, imm (`C6/C7 /0`) | `movi_agree` | proved |
| MOV r, imm (`B0–BF`, including the 64-bit `imm64` form) | `movoi_agree` | proved |
| LEA (`8D`), every addressing form and address/operand size | `lea_agree` | proved |
| MOVZX/MOVSX (`0F B6/B7/BE/BF`) | `movx_agree` | proved |
| SETcc r/m8 (`0F 90–9F`), every condition | `setcc_agree` | proved |
| CMOVcc (`0F 40–4F`), every condition and width (including the 32-bit zero-extension when the condition is false) | `cmov_agree` | proved |
| Jcc rel8 (`70–7F`) | `jcc8_agree` | proved |
| Jcc rel32 (`0F 80–8F`) | `jcc32_agree` | proved |
| JMP rel8/rel32 (`EB/E9`) | `jmp_agree` | proved |
| CALL rel32 (`E8`) | `call_agree` | proved |
| RET / RET imm16 (`C3/C2`) | `ret_agree` | proved, assuming `RSP + 8 + 2^16 ≤ 2^47` (D7) |
| PUSH r64 (`50–57`), POP r64 (`58–5F`) | `push_agree`, `pop_agree` | proved; POP assumes `RSP + 8 < 2^47` (D7) |
| LEAVE (`C9`) | `leave_agree` | proved, assuming `RBP + 8 < 2^47` (D7) |
| JMP r/m64, CALL r/m64 (`FF /4`, `FF /2`), every register and memory form | `jmp_ind_agree`, `call_ind_agree` | proved |
| SHL/SHR/SAR/ROL/ROR r/m, imm8/1/CL (`C0/C1/D0–D3 /0,1,4,5,7`), every width | `shift_agree`; `shift_agree_cf` for `ROR` by a count ≥ 2 | proved except 8/16-bit rotates by a masked count ≥ the width (D3); `ROR` count ≥ 2 up to `CF` (D6) |
| RCL/RCR r/m32/64, imm8/1/CL (`C1/D1/D3 /2,/3`; Janus decodes only 32/64 bits) | `rcx_agree` | proved |
| SHLD/SHRD r/m, r, imm8/CL (`0F A4/A5/AC/AD`), every width | `shd_agree` | proved except the `CL` forms with a RIP-relative operand (D8) |
| DIV/IDIV r/m (`F6/F7 /6,/7`), every width | `div_agree`, `idiv_agree`; `#DE` (zero divisor, quotient overflow): `div_de_agree`, `idiv_de_agree` | proved |
| IMUL r, r/m (`0F AF`) and IMUL r, r/m, imm (`69/6B`) | `imul2_agree`, `imul3_agree` | proved |
| MOVSXD r64, r/m32 (`REX.W 63`) | `movsxd_agree` | proved |
| CBW/CWDE/CDQE (`98`), CWD/CDQ/CQO (`99`) | `cbwcwd_agree` | proved |
| XCHG r/m, r (`86/87`; the memory form implicitly locked), XCHG rAX, r (`91–97`, `REX.B 90`) | `xchg_agree`, `xchg9_agree` | proved |
| BT r/m, imm8 (`0F BA /4`), BT r, r (`0F A3`, register destination) | `bt_ba_agree`, `bt_a3_agree` | proved |
| `LOCK` ADD/OR/ADC/SBB/AND/SUB/XOR m, r (`F0 00/01 … 30/31`) as one step | `alu_eg_mem_lock_agree` | proved |
| CMPXCHG m, r (`0F B0/B1`, with or without `LOCK`) | `cmpxchg_agree` | proved up to D1: every register and memory byte and `ZF` |
| NOP (`90`, `66 90`, `F3 90` PAUSE), NOP r/m (`0F 1F /0`) | `nop_agree`, `nop1f_agree` | proved |
| BTS/BTR/BTC, XADD and LOCK XADD | — | not provable: unimplemented in X86isa (gap) |
| `LOCK`ed r/m, imm and unary forms, PUSH imm, PUSH/POP r/m | — | tested only (Go emits none of them) |
| string instructions | — | tested only (D5) |
| SSE/AVX moves and logic | — | tested only (D4; most are unimplemented in X86isa) |
| SSE scalar floating point, `MXCSR` | — | tested only against hardware (not translated in the Sail model) |
| amd64 v3: BMI1/BMI2, scalar FMA3, MOVBE, PSHUFB/PSIGNB | — | tested only against hardware (not in the Sail model) |

### How the proofs are built

The proofs run the generated monadic code symbolically: each `run_*` lemma states what one
model function returns on a related state. The layers:

* `Monad`, `Gpr`, `Loop`: `SailM` bind/pure, register-file reads and writes (`gprVal`, `setGpr`),
  `foreach` loops.
* `Fetch`, `Prefix`, `Dispatch`, `Top`: fetching the instruction bytes through the model's
  memory (`rme08`, canonical checks), `get_prefixes` simulated against Janus' `parsePrefixes`
  (`PfxRel`), the dispatch up to `one_byte_opcode_execute` (`run_fetch_one`), and the harness
  entry (`run_janus_x86_step`).
* `Fields`, `Regs`, `EA`, `Mem`, `MemW`, `MemOp`: ModRM/SIB/REX fields, sized register reads and
  writes (including `AH…BH`), the effective address for every addressing form
  (`run_x86_effective_addr`), memory reads and writes against Janus' `readLE`/`writeLE`.
* `Arith`, `AluSpec`, `AluWidth` (generated by `tools/gen_aluspec.py`), `AluDispatch`, `Flags`:
  the model's `gpr_*_spec` functions at every width against Janus' `addFlags`/`subFlags`/
  `logicFlags`, and `write_user_rflags` against `FlagsRel`.
* `Frame`: `rm_operand` (the r/m operand: what the model reads and writes is Janus' `locVal`/
  `locWrite`) and `rm_frame`, which reduces a one-byte ModRM instruction to the semantics of its
  dispatch arm. New classes are proved by a decode lemma, a dispatch lemma and a `run_<arm>` lemma
  against abstract operand read/write hypotheses (see `Unary.lean`).
* `TwoByte`: the `0F` escape: `run_fetch_two` (dispatch up to `two_byte_opcode_execute`, with the
  mandatory-prefix computation `mpref`) and `rm_frame2`, the two-byte analogue of `rm_frame`, used
  by `Movx`, `Setcc` and `Jcc32`.
* Class files: `AluGE`, `AluAI`, `AluEI`, `TestEG`, `Unary`, `Mul`, `Imul1`, `Mov`, `MovOI`,
  `Movx`, `Setcc`, `Branch` (Jcc rel8, JMP), `Jcc32`, `Call` (CALL, RET), `Stack` (PUSH/POP),
  `Leave`, `CallInd`, `Shift` (with `ShiftSpec` and the generated `ShiftWidth`,
  `tools/gen_shiftspec.py`), `Rcx` (`RcxSpec`, generated `RcxWidth`, `tools/gen_rcxspec.py`),
  `Shd` (`ShdSpec`, generated `ShdWidth`, `tools/gen_shdspec.py`), `Div`, `Imul2`, `Movsxd`, `Cbw`,
  `Xchg`, `Xchg9`, `Bt`, `Bt3`, `Lock`, `CmpXchg`, `Nop`.

## Trust story

The proofs relate Janus to **the generated Lean**, not to X86isa's ACL2 text. Trusted:

1. **ACL2 X86isa → Sail** (sail-x86-from-acl2's translation), shared with every user of that
   model. Its defects D1–D8 are documented above; the check finds such defects by comparing with
   the hardware results.
2. **Sail → Lean** (Sail 0.20.3's Lean backend, JanusASL's patches), checked empirically by the
   check on 697,542 cases against Janus and the hardware.
3. **The slice and its edits** (`JanusX86/sail/slice.py`, `keep.txt`, `harness.sail`,
   `termination_measures.sail`, `JanusX86Extras.lean`). Kept dispatch arms are verbatim; every other
   arm of the one- and two-byte opcode maps becomes `x86_model_error "janus-excluded: …"`, so a
   byte sequence Janus decodes that lands on an excluded arm is reported, not hidden. The slice used to keep only the opcodes
   Janus decodes; since 2026-10-27 `keep.txt` is `one 00-FF` / `two 00-FF`: every arm of both maps
   is kept verbatim (each excluded arm of the old list was a `janus decodes, the slice excludes it`
   verdict on the SSE, SSSE3, SSE4, x87, crypto, BMI and AVX-512 cases, 452,644 in the corpora
   above), and an arm the model does not implement is its own `x86_model_error("Opcode Unimplemented
   in x86isa!")`. The generated Lean grows from 3.2 MB to 5.0 MB (`X86Sail/Part12` 2.8 MB to 4.6 MB,
   elaborated in 29 s, compiled in 69 s; no module exceeds 100 s). The edits:
   VEX/EVEX dispatch replaced by a model error (X86isa implements no VEX instruction anyway);
   `x86_fault` raises an `Efault` exception the harness maps to `Janus_Fault`; the model's
   undefined-value oracle (`undef_read_logic`) reads the `janus_undef` register, which the
   harness sets, instead of an uninterpreted function; the recursive `get_prefixes` takes
   `cnt - 1` as a termination measure; `JanusX86Extras.lean` provides the memory primitives
   (`read_mem`, `write_mem_ea`, `write_mem`) over the Sail state's byte map and termination
   helpers. None changes the semantics of a kept instruction.
4. **The harness** (`janus_x86_init`, `janus_x86_step`): one instruction from fetch, no
   interrupts, in 64-bit user mode. The proofs quantify over every Sail state related by `Rel`
   and satisfying `X86Config`, so they depend on `janus_x86_init` only through `X86Config`.
5. **lean-sail v7** and the Lean kernel.

Janus itself is not trusted: its `decode` and `step` are the objects under test and proof. The
check also trusts the Lean compiler; the proofs do not.

## Regenerating

```
scripts/x86formal.sh deps                # once (reuses JanusASL's opam switch)
scripts/x86formal.sh gen                 # fails if the result differs from vendor/X86Sail.tar.gz
GEN_UPDATE=1 scripts/x86formal.sh gen    # after changing slice.py/keep.txt/harness: replace it
scripts/x86formal.sh check && scripts/x86formal.sh prove
```

`gen` is deterministic (sorted tar members, mtime 0, `gzip -n`). To add an opcode to the slice,
list it in `JanusX86/sail/keep.txt` (and in `roots.txt` if nothing reaches its function). To
prove a new one-byte ModRM class, follow `Proofs/Unary.lean`: a decode lemma (Janus' `decode`
on the class), a dispatch lemma (`one_byte_opcode_execute` → the arm, by `simp` with `decide`),
the arm's `run_*` lemma against the abstract operand hypotheses, and `rm_frame`; then add the
theorem to `JanusX86/Audit.lean`.
