# JanusASL: the Lean model checked against Arm's ASL inside Lean

`docs/ORACLE.md` checks `Janus.Arm64.step` against qemu. `docs/ORACLE-SAIL.md` checks it against
Arm's ASL, run as the Sail arm-v9.4-a model compiled to C++. Both are harnesses outside Lean.
JanusASL brings the second check into Lean. Sail's Lean backend translates the same Sail model to
Lean, and the result is sliced to the instructions Janus decodes. Then:

* `lake exe janus-asl-check` runs the generated ASL and Janus `step` side by side in compiled
  Lean, on the whole oracle corpus. This is a **test**.
* `JanusASL.Proofs` holds Lean theorems, checked by the kernel, which state that the generated
  ASL and Janus agree on whole encoding classes, for all register and flag values. These are
  **proofs**.

Everything lives in a separate Lake package, `JanusASL/`. It depends on `janus` (`path = ".."`)
and on the Sail Lean library (`lean-sail`). The main `Janus` library depends on neither, and
neither package uses Mathlib.

```
scripts/asl.sh deps     # pinned toolchain (opam + Sail 0.20.3 + patches, sail-arm, slicing plugin)
scripts/asl.sh gen      # slice sail-arm, generate Lean, compare with the vendored copy
scripts/asl.sh build    # unpack the vendored model and build the package (about 75 min at 3 jobs, once)
scripts/asl.sh check    # build + janus-asl-check on artifacts/oracle/cases.jsonl
scripts/asl.sh prove    # build JanusASL.Proofs and audit their axioms
scripts/asl.sh replay   # kernel-replay JanusASL.Proofs with leanchecker, in batches
```

The build runs as many Lean processes at once as fit a 24 GiB budget (see "Memory" below).

## Results

| | |
|---|---|
| corpus | `artifacts/oracle/cases.jsonl` from `scripts/oracle.sh full`: 583,756 cases (qemu: 0 MISMATCH) |
| `janus-asl-check` | **562,288 agree, 21,468 gap, 0 MISMATCH**; `LinuxEL0Config` holds on the base state and on all 583,756 cases' pre- and post-states; `UserMapped` holds on the base sweep and on every case's pre-state points; about 7 min on 48 cores |
| proofs | **44 audited theorems** (an explicit list in JanusASL/Audit.lean, with every statement printed): 36 encoding-class `*_agree` theorems, `step_agree`, `run_agree`, `Ensures.toASL`, `StepOK.of_agree` and 4 example transfers (`*.correctness_asl`), no `sorry`, no `native_decide`, no `bv_decide`; axioms: `propext`, `Classical.choice`, `Quot.sound` only |

Agreement by corpus class (`agree` / `gap`):

| class | agree | gap |
|---|---:|---:|
| br | 155,058 | 551 |
| dpi (data processing, immediate) | 112,990 | 58 |
| dpr (data processing, register) | 100,499 | 2,920 |
| ls (integer loads/stores) | 93,325 | 4,769 |
| simd (AdvSIMD/FP data processing) | 50,638 | 4,947 |
| vls (SIMD loads/stores) | 40,986 | 879 |
| sys | 8,792 | 7,269 |
| reserved | 0 | 75 |

Gaps, by kind:

| kind | cases | meaning |
|---|---:|---|
| `janus-undecodable/asl-excluded` | 17,369 | Janus rejects the word; its ASL clause is outside the slice |
| `janus-undecodable` | 3,432 | Janus rejects the word; the ASL executes it (outside the Janus subset) |
| `unaligned/*`, `Fault.unaligned/asl-ok` | 551 | Janus faults on an unaligned access the ASL allows, or that faults there with another DFSC |
| `outsideAllocation/asl-ok` | 30 | the access is inside the identity map but outside Janus' allocation |
| `noCode .../asl-pc ...` | 86 | a branch to an address with no code (Janus faults now; the ASL faults on the next fetch, which is not modelled) |

A gap means Janus refused to run something (it never makes up a result), so a gap never hides a
wrong answer. A **MISMATCH** is anything else: Janus completes with a state the ASL does not
produce, Janus decodes a word the ASL treats as UNDEFINED/UNPREDICTABLE, or a word Janus decodes
reaches an excluded clause of the slice. `janus-asl-check` exits with code 1 if it finds any.

## What is proved and what is only tested

Each theorem has the same shape. For a 32-bit word `w` in the class (given by its fixed bits as
hypotheses on `w / 2^k % 2^n`), and Janus and Sail states related by `Rel`:

```lean
theorem madd_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b0011011000)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s'
```

`Rel js s` says that the Sail state holds Janus' X0–X30, SP (as `SP_EL0`), PC and NZCV, at EL0
with `PSTATE.SP = 0` and `PSTATE.nRW = 0`. All other Sail state is unconstrained: system
registers, features, memory, and so on. `janus_step` is the generated Sail entry point
(`JanusASL/sail/harness.sail`). It is sail-arm's `__DecodeA64` (decode, then execute), with SEE
retry and the PC update of `__InstructionExecute`, and it maps ASL exceptions to an outcome.

| class (Arm encoding group) | words | status | theorem (JanusASL/Proofs/…) |
|---|---|---|---|
| ADD/ADDS/SUB/SUBS (immediate) | 2^26 | **proved** | `addSubImm_agree` (AddSubImmClass) |
| ADD/ADDS/SUB/SUBS (shifted register) | all valid | **proved** | `addSubShifted_agree` (AddSubShifted) |
| ADD/ADDS/SUB/SUBS (extended register, all 8 extends, shift 0–4) | all valid | **proved** | `addSubExt_agree` (AddSubExt) |
| ADC/ADCS/SBC/SBCS | 2^18 | **proved** | `addSubCarry_agree` (AddSubCarry) |
| AND/BIC/ORR/ORN/EOR/EON/ANDS/BICS (shifted register) | all valid | **proved** | `logicalShifted_agree` (LogicalShifted) |
| AND/ORR/EOR/ANDS (immediate) | all valid | **proved** | `logicalImm_agree` (LogicalImm; `DecodeBitMasks` in Bitmask) |
| MOVN/MOVZ/MOVK | all valid | **proved** | `moveWide_agree` (MoveWide) |
| SBFM/BFM/UBFM (ASR/LSL/LSR imm, SXT*/UXT*, BFI/BFXIL, SBFX/UBFX, ...) | all valid | **proved** | `bitfield_agree` (Bitfield) |
| EXTR (ROR imm) | all valid | **proved** | `extr_agree` (Extr) |
| ADR/ADRP | 2^27 | **proved** | `pcrel_agree` (PcRel) |
| CSEL/CSINC/CSINV/CSNEG | 2^22 | **proved**¹ | `condSel_agree` (CondSel) |
| CCMN/CCMP (register) / (immediate) | 2^17 each | **proved**¹ | `condCmpReg_agree`, `condCmpImm_agree` (CondCmp) |
| MADD/MSUB | 2^22 | **proved** | `madd_agree` (Madd) |
| SMADDL/SMSUBL/UMADDL/UMSUBL | 2^22 | **proved** | `maddl_agree` (Maddl) |
| SMULH/UMULH | 2^16 | **proved** | `mulh_agree` (Mulh) |
| UDIV/SDIV (including ÷0 and `INT_MIN / -1`) | 2^17 | **proved** | `div_agree` (Div) |
| LSLV/LSRV/ASRV/RORV | 2^18 | **proved** | `shiftV_agree` (ShiftV) |
| RBIT, CLZ, CLS | 2^11 each | **proved** | `rbit_agree`, `clz_agree`, `cls_agree` (DP1) |
| REV16, REV32, REV (64) | 2^11 / 2^11 / 2^10 | **proved** | `rev16_agree`, `rev32_agree`, `rev64_agree` (Rev) |
| B, BL | 2^27 | **proved**² | `b_agree` (Branch) |
| B.cond | 2^23 | **proved**² | `bcond_agree` (Branch) |
| CBZ, CBNZ | 2^26 | **proved**² | `cb_agree` (Branch) |
| TBZ, TBNZ | 2^26 | **proved**² | `tb_agree` (Branch) |
| BR, BLR, RET | 2^5 each | **proved**² | `br_agree`, `blr_agree`, `ret_agree` (Branch) |
| branches to a tagged (≥ 2^56) or, for BR/BLR/RET, misaligned target | | tested (Janus faults, the ASL branches; `gap` verdicts) | |
| LDR/STR/LDRB/STRB/LDRH/STRH/LDRSB/LDRSH/LDRSW (unsigned immediate) | all valid | **proved**³ | `ldstUImm_agree` (LdStUImm) |
| LDUR/STUR… and LDR/STR… (pre-/post-index), same size/opc pairs | all valid | **proved**³ | `ldstImm9_agree` (LdStImm9) |
| LDR/STR… (register offset, all extends, `S` shift) | all valid | **proved**³ | `ldstReg_agree` (LdStReg) |
| LDR (literal) W/X, LDRSW (literal) | 2^24 each | **proved**³ | `ldrLit_agree` (LdStLit) |
| LDP/STP (W, X) and LDPSW, post-index / signed offset / pre-index | all valid | **proved**³ | `ldstPair_agree` (LdStPair; paired accesses in MemPair) |
| atomics, exclusives, ordered (LDAR/STLR), PRFM | | tested | |
| AdvSIMD/FP, AES, system (MRS/MSR TPIDR_EL0, DCZID_EL0, DC ZVA, HINT, barriers) | | tested | |

"All valid" means all words of the group that Janus decodes. The theorems carry the decode
conditions as hypotheses, for example `shift ≠ 11` and `imm6 < 32` when `sf = 0`. In those
excluded cases Janus' decoder rejects the word and the ASL raises UNDEFINED, which the test
checks.

¹ `condSel_agree` and the two CCMP/CCMN theorems also assume `SPESampleInFlight = false`. The
ASL's `ConditionHolds` records the condition for the Statistical Profiling Extension when a
sample is in flight. In the check's state it never is.

² Under `LinuxEL0Config s`, to an untagged target (and for BR/BLR/RET a 4-byte-aligned one).
The theorems also conclude `LinuxEL0Config s'`.

³ Under `LinuxEL0Config s`, `MemRel js.mem s` and `UserMapped js.mem s` (below), and for words
Janus steps successfully (`step w js = .ok js'`): the ASL step completes with `Janus_OK` in a
state `s'` with `Rel js' s'`, `MemRel js'.mem s'` and `LinuxEL0Config s'`. Where Janus faults
(outside its allocation, read-only, SP misaligned) nothing is claimed; the check compares those
cases with the ASL's exceptions.

### Loads and stores (Mem.lean, MemWrite.lean, LdSt*.lean)

The memory side of the relation is `MemRel m s`: every byte of every Janus region holds, in the
Sail memory, Janus' byte. A memory access in the ASL goes `Mem_read`/`Mem_set` →
`AArch64_MemSingle_read__1`/`_set__1` (alignment, LSE2 single-copy atomicity, MTE tag check,
`AArch64_TranslateAddress`, TME, SPE) → `PhysMemRead`/`PhysMemWrite` (GIC/UART windows) →
`sail_mem_read`/`sail_mem_write`. Everything but the translation is *proved* under the
configuration: the access descriptor `CreateAccDescGPR` builds (`gprAcc`, with the MPAM default
info), the alignment checks (SCTLR_EL1.A = 0), little-endian data (SCTLR_EL1.E0E = 0), MTE
(`AArch64_AccessIsTagChecked` is false: TCR_EL1.TCMA/TBI, SCTLR_EL1.ATA0), and both paths of
`Mem_read__2`/`Mem_set__2` under FEAT_LSE2: an access inside one 16-byte quantity is one
physical access, any other (unaligned, crossing) access is the byte loop, proved by a loop
invariant (`run_byteLoop_read`, `run_byteLoop_store`). LDP/STP go through `Mem_read__1`/`Mem_set__1`
with `ispair` (one access of `2 × dbytes`): one physical access inside a 16-byte quantity, two
half accesses when the address is aligned to the half size, the byte loop otherwise (MemPair.lean);
LDPSW takes the non-LSE2 path of two separate reads. `LinuxEL0Config` gains `_MPAM3_EL3`,
`MPAM2_EL2` (MPAM disabled) and `TSTATE.depth = 0`.

The translation itself (the stage-1 table walk, permission checks, GPC) is not proved. It is the
named hypothesis **`UserMapped m s`**: in every state an instruction started in `s` can reach
before its accesses (`TFrame`: only GPRs, SP, the step-entry registers and region bytes may
differ), `AArch64_TranslateAddress` maps every byte of `m`'s regions (as an EL0 load, and as a
store for writable regions) to the identity physical address, Normal write-back, without fault
and without changing the state; and no region byte lies in the model's GIC/UART windows. The
`TFrame` part is justified statically: the call graph of `AArch64_TranslateAddress` (1,067
generated functions) reads none of the registers `TFrame` lets change, and the regions do not hold
page tables. `janus-asl-check` evaluates the hypothesis on its tables: every byte of the data
buffer, as load and store, aligned and unaligned, sizes 1–16, on the base state (comparing every
register the translation code can write), and three bytes on every case's pre-state.

These theorems are per instruction; `UserMapped` is not yet carried through `run_agree`. Since
`UserMapped` is evaluated, not proved, there is no kernel-checked non-vacuity witness with non-empty
regions (only the trivial one, no regions, where every Janus access faults): that it holds for the
check's tables is the evaluated fact above.

### `LinuxEL0Config` (Config.lean)

In this build, the ASL branch path does more than set the PC. `BranchTo` and `BranchNotTaken`
run the BRBE branch-record path (`BRBEBranch`, `BranchRecordAllowed`), the SPE sampling path
(`SPEBranch__1`, about 100 lines, including `__IMPDEF_boolean` hooks), the GCS checks
(`GCSPCREnabled`, `AddGCSRecord` for BL/BLR) and TBI (`AArch64_BranchAddr`, `AddrTop`,
`EffectiveTBI`). The check's machine implements every feature except 10. `LinuxEL0Config s`
pins the state that this code reads to the values `janus_init` gives it:

* the FeatureImpl vector (features 1–3, 18, 19, 87, 88, 95, 96 and 258 off);
* SCR_EL3, SCR, HCR_EL2, HCRX_EL2, TCR_EL1, MDCR_EL3, MDCR_EL2;
* BRBFCR_EL1, BRBCR_EL1/2, PMSIDR_EL1, PMSCR_EL1/2, PMBLIMITR_EL1, PMBSR_EL1, GCSCRE0_EL1;
* `SPESampleInFlight = false`, `InGuardedPage = false`, SCTLR_EL1;
* `_MPAM3_EL3`, `MPAM2_EL2` (MPAM disabled), `TSTATE.depth = 0` (for the load/store access descriptor);
* PSTATE.EL = 0, PSTATE.nRW = 0, PSTATE.SP = 0.

HCR_EL2 has E2H = TGE = 0, so the configuration is Linux EL0 under an EL1 kernel (nVHE, or a
guest); a VHE host (E2H = TGE = 1, EL0 translated by TCR_EL2) does not satisfy the predicate.

The values are dumped by `janus-asl-check --cfg`. Under the predicate, Config.lean proves the
following (`run_BranchTo`, `run_BranchNotTaken`). `BranchTo` to an untagged target sets PC and
`__BranchTaken`, and writes only bookkeeping registers (`Branchtypetaken`, `__last_branch_valid`,
`SPESamplePreviousBranchAddressValid`), so GPRs, SP and PSTATE are untouched. `BranchNotTaken`
changes nothing. The IMPDEF hooks reached under the configuration evaluate to fixed answers in
the generated `ImpDefBool` and are proved like the rest. The predicate is preserved by every
branch theorem.

The predicate is also a checked fact. `cfgOk` is a `Bool` version, with
`cfgOk_sound : cfgOk s = true → LinuxEL0Config s`. `janus-asl-check` evaluates `cfgOk` on its
base state, and on every case's pre-state and (for completed steps) post-state: base true,
**0 violations** on 583,756 cases. Every class theorem also proves that the predicate is
preserved: the data-processing theorems conclude `LinuxEL0Config s → LinuxEL0Config s'`, and
the branch theorems conclude `LinuxEL0Config s'`. That is what lets the per-class theorems
compose.

### Whole programs (Run.lean, Examples.lean)

`StepOK w` is the per-word form every proved class gives (`stepOK_<class>`). From states related
under `LinuxEL0Config`, whenever Janus steps `w` to a state with an untagged PC, the generated
ASL step completes with `Janus_OK` in a related state that is again `LinuxEL0Config`.

`aslRun p fuel s` iterates `janus_step` on the words that `p.fetch` returns at the ASL's `_PC`.
Like `Program.run`, it stops at `p.exitAddr` or a stub. Note that the words are fetched with the
program's own `fetch`, not through the ASL's translated instruction fetch.

**`run_agree`** states the following. Suppose every word of `p` is `StepOK`, and the code,
stubs and exit address are untagged. Then for every fuel and every related `LinuxEL0Config`
starting state, the ASL run matches the Janus run. If `p.run fuel js = .ok (.returned js')`,
then `aslRun p fuel s = .returned s'` with `Rel js' s'` and `LinuxEL0Config s'`. If
`.ok (.stub name kind js')`, then `aslRun` ends at the same stub, related. PC tracking through
branches is part of `Rel`.

Not covered: `.error _` outcomes, that is faults and out of fuel. There Janus is conservative
and the ASL may continue.

**`Ensures.toASL`** turns any Janus `Ensures` specification of such a program into the same
statement about the ASL. From every ASL state related to the call state, the ASL run returns to
the caller in a state related to one satisfying the ABI and the postcondition. `Rel` relates only
X0–X30, SP, PC and NZCV, so this transfers exactly the register part of a postcondition: a
postcondition about memory, V registers, TPIDR_EL0 or DCZID_EL0 holds of the Janus state, and the
corollary says nothing about the corresponding ASL state (the four examples are register-only).

It is applied to four shipped examples. In each case the program is copied from
`artifacts/<name>/Extracted.lean`, the Janus proof is copied verbatim from
`examples/proofs/<name>.lean`, and every word is shown to be in the proved subset:

| example | instructions | ASL corollary |
|---|---|---|
| `Add` | ADD, RET | `JanusASL.Examples.Add.correctness_asl` |
| `Max` | CMP (SUBS), B.cs, MOV (ORR), RET, both sides of the branch | `JanusASL.Examples.Max.correctness_asl` |
| `Mul64` | MUL (MADD), UMULH, MOV, RET | `JanusASL.Examples.Mul64.correctness_asl` |
| `Add128` | ADDS, ADC, RET | `JanusASL.Examples.Add128.correctness_asl` |

So for these programs the shipped guarantee, for example "Add returns x + y", holds of Arm's ASL
(as translated) under `LinuxEL0Config`.

The other classes are covered by the corpus test. Loads and stores go through the full
translation table walk (next on the list), and AdvSIMD/AES and the system instructions are
pending.

### How the proofs work

The generated ASL is ordinary Lean: `SailM` is `EStateM` over Sail's sequential state. Each proof
evaluates it symbolically with `simp`, using one run lemma per primitive (`JanusASL/Proofs/Monad`,
`Basic`, `Gpr`). There are four layers:

1. **Dispatch.** `__DecodeA64` → `__DecodeA64_DataProcImm` / `_DataProcReg` (Step.lean). Each
   group function is an if-chain over sail-arm's decode clauses. `tools/chain.py` generates the
   lemma that a class's words reach their clause: for every earlier clause, one `have` with a
   conjunct that the fixed bits falsify, proved by `omega`. It also handles clauses guarded by
   should-be-one checks such as SMULH's `Ra`.
2. **Decode → execute.** The decode function unfolds to the execute function with the field
   values (`rfl`).
3. **Execute.** The ASL pseudocode functions are proved equal, as pure functions, to Janus' `Exec`
   helpers: `AddWithCarry` = `addWithCarry` (Arith.lean), `ShiftReg`, `ConditionHolds`,
   `integer_subrange` = `BitVec.ofInt`, `updateSubrange`, `asl_Int`, and `RoundTowardsZero` of a
   rational quotient = `Int.tdiv`. `DecodeBitMasks` (Bitmask.lean) is proved equal to Janus'
   `decodeBitMasks` on all 2·64·64 `(N, imms, immr)` inputs at both widths by `decide +kernel`.
   The Lean kernel evaluates both functions, in about 50 s; this is not `native_decide`, and no
   compiled code is trusted. A separate lemma lifts the result from the `default` state to any
   state. `X[]`/`SP[]` reads and writes go through `Rel` (Ops.lean).
   Loops: the generated `for` loops are `IntRange` well-founded recursions. `run_forIn_pure`
   (DP1.lean) and `run_forIn_inv` (Rev.lean) turn a loop whose body completes without touching the
   state, under an index invariant that discharges the ASL assertions, into a fold. `hsb_loop`
   handles `HighestSetBit`'s descending loop with early `return`. The folds are related to Janus'
   `rbitNat`/`clzNat`/`revContainersNat` bit by bit.
4. **Assembly.** `step_agree` (Step.lean) combines these with Janus' `decode` lemmas
   (JanusDecode.lean) and with the PC update of `janus_step`.

`scripts/asl.sh prove` builds the proofs and runs `JanusASL/Audit.lean`. That file walks the
environment and fails if any `JanusASL.Proofs.*_agree` theorem depends on an axiom other than
`propext`, `Classical.choice` and `Quot.sound`. This rules out `sorryAx`, and also
`Lean.ofReduceBool`, so no `native_decide` or `bv_decide`. Once the model is built (`scripts/asl.sh
build`), the proofs take about 80 CPU-minutes, about 30 min at 3 jobs. Most of that is the 22
decode-chain parts, at 2–5 min each.

## The pipeline: what is reused, at which versions

| component | version / pin | role |
|---|---|---|
| Lean | 4.34.1 (`lean-toolchain`, same as Janus) | |
| [sail-arm](https://github.com/rems-project/sail-arm) | `7d0581642d0e` (master; includes the Lean `MOD` = `Nat.mod` fix in `prelude.sail`) | Arm's ASL for v9.4-A, translated to Sail by Arm's asl_to_sail |
| [Sail](https://github.com/rems-project/sail) | tag `0.20.3` + `JanusASL/sail/sail-0.20.3-upstream-backports.patch` + `JanusASL/sail/sail-0.20.3-janus-lean-fixes.patch` | Lean backend |
| OCaml / opam | 5.2.1 / opam 2.x, own root `$DEPS/opam`, switch `sail-0.20.3-janus` | builds Sail |
| [lean-sail](https://github.com/rems-project/lean-sail) | tag v7, `8fc8e29d7a62` | Lean runtime library of the generated code (v6, Sail 0.20.3's default, does not build on 4.34.1) |
| generated model | `JanusASL/vendor/ArmASL.tar.gz` (sha256 in `.sha256`), 50 chained parts plus 4 support modules, 21 MB | unpacked into `JanusASL/ArmASL*` (ignored by git) |

Sail-master cannot be used: it removed `lib/trace.sail`, which sail-arm still includes.

### Sail patches

`sail-0.20.3-upstream-backports.patch` contains 8 upstream commits that came after 0.20.3:

* `2f5dcd138` Lean: avoid mixing vector pattern and bitvector literal patterns
* `e7da32cb1` Lean: fix file list mismatch
* `2ba321281` Apply `--lean-line-width` to all definition files
* `7e0e53d18` Lean: change assert function name (`sail_assert`)
* `f7a1fedbc` Lean: keep local variables updated in a let's body
* `e49821011` Lean: need parens around "real" literals
* `e55d89e79` Lean: support short-circuiting `&&` `||` with effects
* `9c10b069e` Rocq/Lean: fix top level value definitions with monadic bind

`sail-0.20.3-janus-lean-fixes.patch` holds JanusASL's own fixes: 3 files, about 90 lines, each
with a comment. Each one fixes a bug that sail-arm hits. They are written so that they could go
upstream (none has been filed):

1. **One-bit vectors.** `[b]` is printed as `(b : BitVec 1)`, not `BitVec.join1 [b]`. Lean 4.34
   otherwise tries to unify `[a].length =?= [b].length` by evaluating `a` and `b`, and hangs
   (`IncrementInstructionCounter`).
2. **Monadic struct fields.** These are printed as `f := (← do e)`. Before, `f := ← e` did not
   parse when `e` was a line-broken `if`.
3. **Monadic `if`.** This is printed as a parenthesised term with `(do …)` branches. As a
   `do`-statement followed by more code, Lean 4.34 builds a join point and fails with "Failed to
   assign join point RHS" when later types depend on let-bound variables (`Mem_set__2`).
4. **`rewrite_var_updates`.** This handles `let` where both the binding and the body update
   variables. Without it, the vector-concat assignment `(hi @ lo) = v` was dropped silently. The
   generated code compiled but computed the wrong value.
5. **Integer lets.** Effectful lets of integer type are now ascribed (`: SailM Int`). Without the
   ascription, Lean elaborated `asl_Int` at `Nat` from its first branch, and lean-sail's
   `CoeT Int x Nat` truncated every negative value to 0. This was the cause of the SDIV, SMULH
   and SMADDL mismatches below.
6. **Exact reals.** `FakeReal.lean` now uses `real := Rat` (exact) instead of `Float`. With `Float`,
   64-bit UDIV/SDIV (`RoundTowardsZero(Real(a)/Real(b))`) lost precision, and `round_down` was
   `toUInt64`, which mapped negative values to 0.

Bugs 4–6 each produced a model that compiled without complaint but gave wrong results. Only the
corpus comparison found them. That comparison is the reason the check exists alongside the
proofs.

### Slicing (JanusASL/sail/)

The whole arm-v9.4-a model does not fit in Lean: the full `BranchExcSys` decode alone came to
207 MB. Generation therefore runs in two stages:

* **`slice.py`** works on sail-arm's source files. It keeps every decode-clause *pattern* of the
  classes DataProcImm, BranchExcSys, LoadStore, DataProcReg and DataProcFPSIMD, so the decode
  if-chains stay exactly as Arm wrote them. It keeps the *bodies* of the decode functions in
  `keep.txt`, which lists 343 functions: the integer instructions, atomics, CAS/CASP, LDAR/STLR/LDAPR,
  exclusives, PRFM/PRFUM/RPRFM, CLREX, MRS, SYS, HINT and the SIMD set Janus decodes. Every other
  clause body becomes `throw(Error_ImplementationDefined("janus-excluded …"))`. The script also
  empties the AArch32, SVE and SME decoders, and turns 22 literal-pattern clauses into bit-list
  patterns. Literal patterns are what blew `BranchExcSys` up to 207 MB.
* **Splices.** `janus_splice.sail`: `AArch64_TakeException` records the exception type, syndrome
  and fault address, then throws `Error_ExceptionTaken`, so the harness can compare faults.
  `janus_pac_splice.sail`: the PAC nibble substitutions use `Slice` (the originals did not
  translate). `janus_sysreg_splice.sail`: the auto-generated system register read and SYS-op
  dispatch keep only DCZID_EL0, TPIDR_EL0 and DC ZVA. Every other register is janus-excluded.
* **`plugin/sail_plugin_janus.ml`** is a Sail plugin (`--janus-lean`). It slices the type-checked
  AST by call graph from the roots in `roots.txt` (the harness entry points), keeping the
  standard library, and then runs the normal Lean rewrites and printer.
  `--lean-partial-function Reduce__1` is the only `partial` function. No generated definition
  needs a termination proof, so nothing is `sorry`.
* **`split_lean.py`** splits the single output file into 50 chained modules of at most 150 kB
  (a larger declaration gets its own; see "Memory"), so that Lake
  elaborates them with bounded memory.

A janus-excluded clause is reachable only through a word that Janus does not decode. If a word
Janus decodes reaches one, the check reports a MISMATCH.

## The check (JanusASL/Check.lean)

Both sides start from the corpus case's registers, flags, V registers, TPIDR_EL0 and data buffer.
The ASL state is `sail_model_init` followed by `janus_init`. That is the Linux EL0 setup of
`oracle-sail/src/main.rs`: `__InitSystem`, EL0 AArch64 with the MMU on, and a 4-level identity
map of the code page and the 4 KiB data buffer, built from the same page tables. Janus' DCZID is
taken from the ASL's DCZID_EL0 (0x8). Each case is one `janus_step`, compared on X0–X30, SP, PC,
NZCV, V0–V31, memory (the data buffer, and no other ASL byte changed) and the fault class. An
alignment fault, DFSC 0x21, counts as agreeing with Janus' `unaligned`.

## Memory

Each Lean process of the pipeline must stay under 12 GiB, and `scripts/asl.sh build` followed by
`scripts/asl.sh prove` must fit in 24 GiB. Every number below is measured with
`JanusASL/tools/memprof.py`. It samples `/proc` every 0.2 s and reports each process's peak
resident set (`VmHWM`) and the peak of the whole process tree. With `--cap GB` it also runs the
command in a systemd scope with `MemoryMax=GB` and no swap, so the kernel kills a runaway build
instead of the host. `JanusASL/tools/memtable.py` prints the per-process table. All runs are on
this 48-core host. "Before" is main plus merge/asl3: 44 audited theorems, the 24-part model, and
the decode-chain files as single modules. "After" is this layout. The summed RSS counts the
mmapped `.olean` pages once per process, so the scope's `memory.peak` (anonymous memory plus page
cache) is the better total.

| run | before | after |
|---|---|---|
| `scripts/asl.sh build`: largest Lean process | **16.7 GiB** (`LdStDecode9`, 1148 s) | **8.3 GiB** (`ArmASL.Part49` = `__DecodeA64_DataProcFPSIMD` alone, 243 s) |
| `scripts/asl.sh build`: other processes over 5 GiB | `ArmASL.Part24` 9.0, `Part22` 7.4, `LdStDecodeR` 7.3, `LdStDecodeP` 7.0, `LdStDecode` 6.8, `Bitmask` 5.6, `Part15` 5.3, `Part17` 5.2, `Part19` 5.0 | `Part38` (`AArch64_AutoGen_SysRegWrite`) 6.6, `Bitmask` 5.6, `Part12` (`AArch32_AutoGen_ArchitectureReset`) 5.2 |
| `scripts/asl.sh build`: decode-chain proofs | 6.8–16.7 GiB per file (4 files) | 3.0–3.7 GiB per part (22 parts) |
| `scripts/asl.sh build`: whole tree | 48 Lake jobs; summed RSS 34.6 GiB, scope 35.6 GiB; 59 min (Janus library already built) | 3 Lake jobs; summed RSS 11.0 GiB, scope **9.8 GiB** under `MemoryMax=24G`; 75 min (Janus library included) |
| clang (C of the model, for the check executable) | 2.4 GiB | 2.4 GiB |
| `scripts/asl.sh prove` (Audit.lean) | 1.8 GiB, 2 s | 1.9 GiB, 2 s (same 44 theorems, same axioms, same statements) |
| kernel replay | `leanchecker JanusASL.Proofs`, `LEAN_NUM_THREADS=4`: **14.8 GiB**, 362 s | `scripts/asl.sh replay` (4 modules per process, `LEAN_NUM_THREADS=4`): **10.0 GiB**, 406 s |
| `janus-asl-check` on the 583,756-case corpus | 2.4 GiB, 551 s | **0.45 GiB**, 461 s (same verdicts file, byte for byte) |
| `scripts/asl.sh gen` (Sail, not Lean) | | 8.2 GiB, 748 s |

So `build` followed by `prove` peaks at 9.8 GiB (scope), and no Lean process exceeds 8.3 GiB.
On the after layout, the old monolithic `leanchecker JanusASL.Proofs` still takes 16.0 GiB,
because it imports one environment per module and runs 4 at a time. Use `scripts/asl.sh replay`
instead.

What was changed:

* **The model is split by size** (`split_lean.py --bytes 150000`, called by `scripts/asl.sh gen`).
  It now has 50 chained parts of at most 150 kB each, except that a larger declaration gets a
  part of its own. Elaboration memory follows the largest declarations, not the file size: the
  981 kB `ImpDefBool` takes 2.2 GiB, while the 157 kB `AArch64_AutoGen_ArchitectureReset` takes
  4.7 GiB. The old 24-part split, which cut by declaration count, put
  `__DecodeA64_DataProcFPSIMD`, `__DecodeA64_LoadStore` and the other decoders in one 10 MB part
  (9.0 GiB). The declarations, their order and their text are unchanged. Joining the 50 parts
  gives back, byte for byte, the single file that joining the 24 old parts gives, and
  `scripts/asl.sh gen` regenerates the new tarball byte for byte (sha256
  `aa1fa24372907b2785607f738191355818a3c193f49efe471faed16ddcfad60f`).
* **The decode-chain proofs are split** (`JanusASL/tools/split_proofs.py FILE 4`). `LdStDecode`,
  `LdStDecode9`, `LdStDecodeP` and `LdStDecodeR` are now import lists of `<File>/PartNN` modules
  with 4 lemmas each. Each part repeats the header, and the lemmas are copied byte for byte
  (`split_proofs.py --check FILE REV` compares them with the file at a git revision). As one
  module, a file keeps every finished proof until it ends, so its peak grew with its length
  (about 0.4 GiB per lemma). The parts also build in parallel. Split new generated chain files
  the same way.
* **Lake's job count comes from memory.** `scripts/asl.sh build`/`prove`/`replay` run Lake with
  `LEAN_NUM_THREADS=ASL_JOBS`. Lake has no `-j`. Its thread pool bounds the number of Lean
  processes it runs at once, and each Lean process then elaborates with as many threads. The
  default is `ASL_MEM_GB / ASL_JOB_GB`, with the budget the smaller of 24 GiB and 60% of
  `MemAvailable`, and 8 GiB per job (the largest process above). That gives 3 jobs on this host.
  Up to the last model part the build is a chain, so beside `Part49` only a clang compile runs.
* **`janus-asl-check` streams the corpus.** It reads, runs and writes batches of `48 × 256` cases,
  with one batch running while the next is read. It no longer holds the 1 GB corpus and every
  verdict at once.
* **The replay is batched** (`scripts/asl.sh replay`). It replays every module in the import
  closure of `JanusASL.Proofs` with `leanchecker`, `REPLAY_BATCH` (default 4) modules per
  process, one process at a time. Import lists that declare nothing are skipped: leanchecker
  takes name prefixes, so naming one would pull in all its parts.

Semantics check. `JanusASL/tools/Digest.lean` prints every declaration of the ArmASL and JanusASL
modules with structural hashes of its type and value. Before and after give the same 15,895
declarations, all with the same type hashes and the same value hashes. Auxiliary declarations
(matchers, equation lemmas, `_proof_N`) are hashed by content instead of by name, because Lean
numbers and shares them per module. The audit output (theorem list, axioms, printed
statements) is identical, and the check's verdicts file is identical.

<details><summary>Every ArmASL module, before (24 parts)</summary>

| module | size | largest declaration | peak RSS | wall |
|---|---:|---|---:|---:|
| `ArmASL.Defs` | 135 kB |  | 3.0 GiB | 59 s |
| `ArmASL.FakeReal` | 2 kB |  | 1.6 GiB | 1 s |
| `ArmASL.JanusExtras` | 0 kB |  | 1.6 GiB | 1 s |
| `ArmASL.Part01` | 77 kB | `InitFeatureImpl` (32 kB) | 2.2 GiB | 44 s |
| `ArmASL.Part02` | 44 kB | `write_gpr_bits` (2 kB) | 1.8 GiB | 4 s |
| `ArmASL.Part03` | 1016 kB | `ImpDefBool` (981 kB) | 2.2 GiB | 7 s |
| `ArmASL.Part04` | 63 kB | `SPEEvent` (14 kB) | 1.8 GiB | 7 s |
| `ArmASL.Part05` | 50 kB | `ImpDefBits` (15 kB) | 1.8 GiB | 5 s |
| `ArmASL.Part06` | 100 kB | `ELFromM32` (7 kB) | 1.9 GiB | 20 s |
| `ArmASL.Part07` | 57 kB | `Hint_WFE` (4 kB) | 1.8 GiB | 9 s |
| `ArmASL.Part08` | 93 kB | `EncodeLDFSC` (5 kB) | 1.9 GiB | 9 s |
| `ArmASL.Part09` | 158 kB | `FPRoundBase__1` (14 kB) | 1.9 GiB | 34 s |
| `ArmASL.Part10` | 168 kB | `CheckTransactionalSystemAccess` (12 kB) | 2.0 GiB | 19 s |
| `ArmASL.Part11` | 266 kB | `AArch64_S1IndirectBasePermissions` (17 kB) | 2.0 GiB | 22 s |
| `ArmASL.Part12` | 219 kB | `AArch64_S1Walk` (26 kB) | 2.0 GiB | 20 s |
| `ArmASL.Part13` | 33 kB | `ICC_CTLR_read` (0 kB) | 1.8 GiB | 10 s |
| `ArmASL.Part14` | 33 kB | `ICC_IGRPEN1_read` (0 kB) | 1.8 GiB | 10 s |
| `ArmASL.Part15` | 135 kB | `AArch32_AutoGen_ArchitectureReset` (103 kB) | 5.3 GiB | 223 s |
| `ArmASL.Part16` | 30 kB | `NMRR_read` (0 kB) | 1.8 GiB | 4 s |
| `ArmASL.Part17` | 318 kB | `AArch64_AutoGen_ArchitectureReset` (153 kB) | 5.2 GiB | 486 s |
| `ArmASL.Part18` | 52 kB | `__set_MDSCR_EL1` (3 kB) | 1.8 GiB | 9 s |
| `ArmASL.Part19` | 400 kB | `AArch64_AutoGen_SysRegRead` (243 kB) | 5.0 GiB | 217 s |
| `ArmASL.Part20` | 820 kB | `FPSR_SysRegWrite_d0a803d1b7d0c76d` (7 kB) | 2.4 GiB | 96 s |
| `ArmASL.Part21` | 962 kB | `PMXEVTYPER_EL0_SysRegWrite_1b2a1f5e5253d48b` (9 kB) | 2.5 GiB | 115 s |
| `ArmASL.Part22` | 5338 kB | `AArch64_AutoGen_SysRegWrite` (4162 kB) | 7.4 GiB | 163 s |
| `ArmASL.Part23` | 378 kB | `decode_yield_aarch64_instrs_system_hints` (10 kB) | 2.0 GiB | 26 s |
| `ArmASL.Part24` | 10455 kB | `__DecodeA64_DataProcFPSIMD` (7023 kB) | 9.0 GiB | 546 s |
| `ArmASL.SpecializationV1` | 4 kB |  | 1.7 GiB | 2 s |

</details>

<details><summary>Every ArmASL module, after (50 parts)</summary>

| module | size | largest declaration | peak RSS | wall |
|---|---:|---|---:|---:|
| `ArmASL.Defs` | 135 kB |  | 2.9 GiB | 60 s |
| `ArmASL.FakeReal` | 2 kB |  | 1.5 GiB | 0 s |
| `ArmASL.JanusExtras` | 0 kB |  | 1.6 GiB | 0 s |
| `ArmASL.Part01` | 141 kB | `InitFeatureImpl` (32 kB) | 2.2 GiB | 49 s |
| `ArmASL.Part02` | 982 kB | `ImpDefBool` (981 kB) | 2.1 GiB | 5 s |
| `ArmASL.Part03` | 147 kB | `ImpDefBits` (15 kB) | 1.9 GiB | 15 s |
| `ArmASL.Part04` | 152 kB | `ELFromM32` (7 kB) | 1.9 GiB | 29 s |
| `ArmASL.Part05` | 152 kB | `AArch64_FaultSyndrome` (7 kB) | 1.9 GiB | 31 s |
| `ArmASL.Part06` | 147 kB | `FPRoundBase__1` (14 kB) | 1.9 GiB | 13 s |
| `ArmASL.Part07` | 149 kB | `AArch64_BreakpointValueMatch` (15 kB) | 2.0 GiB | 19 s |
| `ArmASL.Part08` | 149 kB | `AArch64_S1IndirectBasePermissions` (17 kB) | 1.9 GiB | 12 s |
| `ArmASL.Part09` | 128 kB | `AArch64_S2Walk` (19 kB) | 1.9 GiB | 10 s |
| `ArmASL.Part10` | 152 kB | `AArch64_S1Walk` (26 kB) | 1.9 GiB | 18 s |
| `ArmASL.Part11` | 101 kB | `SDER_write` (0 kB) | 1.9 GiB | 29 s |
| `ArmASL.Part12` | 138 kB | `AArch32_AutoGen_ArchitectureReset` (103 kB) | 5.2 GiB | 230 s |
| `ArmASL.Part13` | 36 kB | `AArch32_IMPDEFResets` (23 kB) | 1.9 GiB | 12 s |
| `ArmASL.Part14` | 157 kB | `AArch64_AutoGen_ArchitectureReset` (153 kB) | 4.7 GiB | 405 s |
| `ArmASL.Part15` | 154 kB | `AArch64_IMPDEFResets` (76 kB) | 2.8 GiB | 124 s |
| `ArmASL.Part16` | 73 kB | `TakePendingInterrupts` (8 kB) | 1.8 GiB | 9 s |
| `ArmASL.Part17` | 244 kB | `AArch64_AutoGen_SysRegRead` (243 kB) | 4.8 GiB | 186 s |
| `ArmASL.Part18` | 151 kB | `AMAIR2_EL2_SysRegWrite_d6e02923e8c9c534` (4 kB) | 1.9 GiB | 25 s |
| `ArmASL.Part19` | 152 kB | `CNTP_TVAL_EL0_SysRegWrite_eccdee10d8c7f39e` (7 kB) | 1.9 GiB | 18 s |
| `ArmASL.Part20` | 148 kB | `DBGBVR_EL1_SysRegWrite_0ffea2b5aaa11a7e` (6 kB) | 1.9 GiB | 21 s |
| `ArmASL.Part21` | 152 kB | `DBGWCR_EL1_SysRegWrite_3550aa3a97d9acb5` (6 kB) | 1.9 GiB | 21 s |
| `ArmASL.Part22` | 150 kB | `DBGWVR_EL1_SysRegWrite_c2a564a92621de17` (6 kB) | 1.9 GiB | 20 s |
| `ArmASL.Part23` | 151 kB | `FPSR_SysRegWrite_d0a803d1b7d0c76d` (7 kB) | 1.9 GiB | 17 s |
| `ArmASL.Part24` | 152 kB | `ICC_CTLR_EL1_SysRegWrite_6b2222909cfe4181` (6 kB) | 1.9 GiB | 20 s |
| `ArmASL.Part25` | 151 kB | `MDSELR_EL1_SysRegWrite_96ef452973a846b6` (5 kB) | 1.9 GiB | 19 s |
| `ArmASL.Part26` | 149 kB | `PMEVCNTR_EL0_SysRegWrite_6fa8164f702c143b` (6 kB) | 1.9 GiB | 16 s |
| `ArmASL.Part27` | 150 kB | `PMEVTYPER_EL0_SysRegWrite_103d29a45c9a97d5` (7 kB) | 1.9 GiB | 15 s |
| `ArmASL.Part28` | 152 kB | `PMEVTYPER_EL0_SysRegWrite_c1033a183cde77b2` (7 kB) | 1.9 GiB | 15 s |
| `ArmASL.Part29` | 150 kB | `PMICFILTR_EL0_SysRegWrite_b4d38d797e58f97d` (9 kB) | 1.9 GiB | 17 s |
| `ArmASL.Part30` | 150 kB | `PMXEVTYPER_EL0_SysRegWrite_1b2a1f5e5253d48b` (9 kB) | 1.9 GiB | 18 s |
| `ArmASL.Part31` | 149 kB | `SPMEVCNTR_EL0_SysRegWrite_08629c5414f88eb2` (12 kB) | 1.9 GiB | 13 s |
| `ArmASL.Part32` | 143 kB | `SPMEVFILT2R_EL0_SysRegWrite_229ceb05708f41b3` (12 kB) | 1.9 GiB | 12 s |
| `ArmASL.Part33` | 143 kB | `SPMEVFILT2R_EL0_SysRegWrite_a4da6c90289f656a` (12 kB) | 1.9 GiB | 15 s |
| `ArmASL.Part34` | 150 kB | `SPMEVFILT2R_EL0_SysRegWrite_fc59638a1eed5ceb` (12 kB) | 1.9 GiB | 15 s |
| `ArmASL.Part35` | 143 kB | `SPMEVTYPER_EL0_SysRegWrite_ccaf15f0e189ded0` (12 kB) | 1.9 GiB | 15 s |
| `ArmASL.Part36` | 150 kB | `SPMEVTYPER_EL0_SysRegWrite_f79086ccec170944` (12 kB) | 1.9 GiB | 18 s |
| `ArmASL.Part37` | 98 kB | `AArch64_UnallocatedSysRegAccess` (7 kB) | 1.9 GiB | 12 s |
| `ArmASL.Part38` | 4163 kB | `AArch64_AutoGen_SysRegWrite` (4162 kB) | 6.6 GiB | 45 s |
| `ArmASL.Part39` | 151 kB | `AArch64_AutoGen_SysOpsWrite` (58 kB) | 2.0 GiB | 29 s |
| `ArmASL.Part40` | 141 kB | `decode_sev_aarch64_instrs_system_hints` (10 kB) | 1.9 GiB | 8 s |
| `ArmASL.Part41` | 151 kB | `decode_yield_aarch64_instrs_system_hints` (10 kB) | 1.9 GiB | 14 s |
| `ArmASL.Part42` | 149 kB | `execute_aarch64_instrs_memory_exclusive_single` (5 kB) | 1.9 GiB | 10 s |
| `ArmASL.Part43` | 150 kB | `decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned` (4 kB) | 1.9 GiB | 12 s |
| `ArmASL.Part44` | 152 kB | `decode_strh_reg_aarch64_instrs_memory_single_general_register` (5 kB) | 1.9 GiB | 12 s |
| `ArmASL.Part45` | 90 kB | `__DecodeA64_DataProcImm` (26 kB) | 1.9 GiB | 5 s |
| `ArmASL.Part46` | 126 kB | `__DecodeA64_BranchExcSys` (124 kB) | 1.9 GiB | 7 s |
| `ArmASL.Part47` | 2576 kB | `__DecodeA64_LoadStore` (2574 kB) | 3.4 GiB | 72 s |
| `ArmASL.Part48` | 189 kB | `__DecodeA64_DataProcReg` (187 kB) | 1.9 GiB | 9 s |
| `ArmASL.Part49` | 7027 kB | `__DecodeA64_DataProcFPSIMD` (7023 kB) | 8.3 GiB | 243 s |
| `ArmASL.Part50` | 83 kB | `initialize_registers` (58 kB) | 3.2 GiB | 168 s |
| `ArmASL.SpecializationV1` | 4 kB |  | 1.6 GiB | 2 s |

</details>

<details><summary>Every JanusASL module, before and after</summary>

| module | before | after |
|---|---:|---:|
| `JanusASL.Check` | 2.0 GiB, 41 s | 2.0 GiB, 21 s |
| `JanusASL.Proofs` | 1.7 GiB, 0 s | 1.8 GiB, 0 s |
| `JanusASL.Proofs.AddSubCarry` | 1.9 GiB, 13 s | 2.0 GiB, 9 s |
| `JanusASL.Proofs.AddSubExt` | 2.1 GiB, 57 s | 2.1 GiB, 36 s |
| `JanusASL.Proofs.AddSubImm` | 1.8 GiB, 4 s | 1.8 GiB, 3 s |
| `JanusASL.Proofs.AddSubImmClass` | 1.9 GiB, 13 s | 1.9 GiB, 8 s |
| `JanusASL.Proofs.AddSubShifted` | 2.0 GiB, 18 s | 2.0 GiB, 9 s |
| `JanusASL.Proofs.Arith` | 1.7 GiB, 1 s | 1.8 GiB, 1 s |
| `JanusASL.Proofs.Basic` | 1.8 GiB, 1 s | 1.8 GiB, 1 s |
| `JanusASL.Proofs.Bitfield` | 1.9 GiB, 14 s | 1.9 GiB, 5 s |
| `JanusASL.Proofs.Bitmask` | 5.6 GiB, 109 s | 5.6 GiB, 78 s |
| `JanusASL.Proofs.Branch` | 2.3 GiB, 93 s | 2.4 GiB, 23 s |
| `JanusASL.Proofs.CfgDef` | 1.8 GiB, 2 s | 1.9 GiB, 2 s |
| `JanusASL.Proofs.Cond` | 1.9 GiB, 3 s | 2.0 GiB, 3 s |
| `JanusASL.Proofs.CondCmp` | 2.1 GiB, 33 s | 2.2 GiB, 16 s |
| `JanusASL.Proofs.CondSel` | 2.1 GiB, 37 s | 2.1 GiB, 17 s |
| `JanusASL.Proofs.Config` | 2.5 GiB, 47 s | 2.6 GiB, 30 s |
| `JanusASL.Proofs.DP1` | 2.1 GiB, 31 s | 2.2 GiB, 17 s |
| `JanusASL.Proofs.Div` | 2.0 GiB, 25 s | 2.1 GiB, 14 s |
| `JanusASL.Proofs.Examples` | 1.8 GiB, 7 s | 1.9 GiB, 2 s |
| `JanusASL.Proofs.Extr` | 1.9 GiB, 5 s | 1.9 GiB, 4 s |
| `JanusASL.Proofs.Gpr` | 2.3 GiB, 51 s | 2.3 GiB, 48 s |
| `JanusASL.Proofs.JanusDecode` | 1.8 GiB, 3 s | 1.8 GiB, 3 s |
| `JanusASL.Proofs.LdSt` | 2.0 GiB, 101 s | 2.0 GiB, 15 s |
| `JanusASL.Proofs.LdStDecode` | 6.8 GiB, 747 s | 1.7 GiB, 1 s |
| `JanusASL.Proofs.LdStDecode9` | 16.7 GiB, 1148 s | 1.7 GiB, 1 s |
| `JanusASL.Proofs.LdStDecode9.Part01` | – | 3.6 GiB, 191 s |
| `JanusASL.Proofs.LdStDecode9.Part02` | – | 3.6 GiB, 195 s |
| `JanusASL.Proofs.LdStDecode9.Part03` | – | 3.6 GiB, 179 s |
| `JanusASL.Proofs.LdStDecode9.Part04` | – | 3.5 GiB, 179 s |
| `JanusASL.Proofs.LdStDecode9.Part05` | – | 3.5 GiB, 172 s |
| `JanusASL.Proofs.LdStDecode9.Part06` | – | 3.5 GiB, 174 s |
| `JanusASL.Proofs.LdStDecode9.Part07` | – | 3.5 GiB, 179 s |
| `JanusASL.Proofs.LdStDecode9.Part08` | – | 3.5 GiB, 177 s |
| `JanusASL.Proofs.LdStDecode9.Part09` | – | 3.5 GiB, 177 s |
| `JanusASL.Proofs.LdStDecode9.Part10` | – | 3.2 GiB, 164 s |
| `JanusASL.Proofs.LdStDecode.Part01` | – | 3.4 GiB, 306 s |
| `JanusASL.Proofs.LdStDecode.Part02` | – | 3.4 GiB, 306 s |
| `JanusASL.Proofs.LdStDecode.Part03` | – | 3.4 GiB, 285 s |
| `JanusASL.Proofs.LdStDecode.Part04` | – | 2.3 GiB, 190 s |
| `JanusASL.Proofs.LdStDecodeP` | 7.0 GiB, 723 s | 1.7 GiB, 1 s |
| `JanusASL.Proofs.LdStDecodeP.Part01` | – | 3.4 GiB, 143 s |
| `JanusASL.Proofs.LdStDecodeP.Part02` | – | 3.3 GiB, 140 s |
| `JanusASL.Proofs.LdStDecodeP.Part03` | – | 3.3 GiB, 144 s |
| `JanusASL.Proofs.LdStDecodeP.Part04` | – | 3.0 GiB, 134 s |
| `JanusASL.Proofs.LdStDecodeR` | 7.3 GiB, 784 s | 1.7 GiB, 1 s |
| `JanusASL.Proofs.LdStDecodeR.Part01` | – | 3.6 GiB, 188 s |
| `JanusASL.Proofs.LdStDecodeR.Part02` | – | 3.7 GiB, 183 s |
| `JanusASL.Proofs.LdStDecodeR.Part03` | – | 3.6 GiB, 178 s |
| `JanusASL.Proofs.LdStDecodeR.Part04` | – | 2.4 GiB, 136 s |
| `JanusASL.Proofs.LdStImm9` | 2.1 GiB, 4 s | 2.2 GiB, 4 s |
| `JanusASL.Proofs.LdStLit` | 3.0 GiB, 124 s | 3.1 GiB, 115 s |
| `JanusASL.Proofs.LdStPair` | 2.3 GiB, 6 s | 2.3 GiB, 6 s |
| `JanusASL.Proofs.LdStReg` | 2.0 GiB, 3 s | 2.1 GiB, 3 s |
| `JanusASL.Proofs.LdStUImm` | 1.9 GiB, 2 s | 2.0 GiB, 2 s |
| `JanusASL.Proofs.LogicalImm` | 1.9 GiB, 22 s | 1.9 GiB, 5 s |
| `JanusASL.Proofs.LogicalShifted` | 2.1 GiB, 25 s | 2.2 GiB, 16 s |
| `JanusASL.Proofs.Madd` | 2.0 GiB, 26 s | 2.0 GiB, 12 s |
| `JanusASL.Proofs.Maddl` | 2.2 GiB, 39 s | 2.3 GiB, 26 s |
| `JanusASL.Proofs.Mem` | 2.1 GiB, 90 s | 2.1 GiB, 21 s |
| `JanusASL.Proofs.MemPair` | 2.0 GiB, 58 s | 2.0 GiB, 8 s |
| `JanusASL.Proofs.MemWrite` | 1.9 GiB, 10 s | 1.9 GiB, 5 s |
| `JanusASL.Proofs.Monad` | 1.7 GiB, 1 s | 1.7 GiB, 1 s |
| `JanusASL.Proofs.MoveWide` | 1.9 GiB, 133 s | 2.0 GiB, 88 s |
| `JanusASL.Proofs.Mulh` | 2.1 GiB, 36 s | 2.1 GiB, 17 s |
| `JanusASL.Proofs.Ops` | 1.7 GiB, 1 s | 1.7 GiB, 1 s |
| `JanusASL.Proofs.PcRel` | 1.8 GiB, 9 s | 1.9 GiB, 3 s |
| `JanusASL.Proofs.Rel` | 2.5 GiB, 24 s | 2.6 GiB, 23 s |
| `JanusASL.Proofs.Rev` | 2.4 GiB, 48 s | 2.4 GiB, 27 s |
| `JanusASL.Proofs.Run` | 1.9 GiB, 7 s | 2.0 GiB, 2 s |
| `JanusASL.Proofs.Shift` | 1.7 GiB, 1 s | 1.7 GiB, 1 s |
| `JanusASL.Proofs.ShiftV` | 2.0 GiB, 16 s | 2.0 GiB, 11 s |
| `JanusASL.Proofs.Step` | 1.9 GiB, 3 s | 1.9 GiB, 3 s |

</details>

## Evidence for the mismatches found during development

Before patches 5 and 6, the check reported **440 MISMATCH**. All were register differences in
signed multiply and divide. For every one, the independent references agree with **Janus**: qemu
(`artifacts/oracle/hw.jsonl`) and the Sail C++ build of the same ASL
(`artifacts/oracle-sail/sail.jsonl`). The fault was in the Lean translation of the ASL (bugs 5
and 6), not in Janus.

| instruction | cases | Janus = qemu = Sail C++ | Janus ≠ qemu or Sail C++ |
|---|---:|---:|---:|
| SDIV (W) | 40 | 40 | 0 |
| SDIV (X) | 98 | 98 | 0 |
| UDIV (X) | 24 | 24 | 0 |
| SMULH | 62 | 62 | 0 |
| SMADDL | 103 | 103 | 0 |
| SMSUBL | 113 | 113 | 0 |
| **total** | **440** | **440** | **0** |

Sample rows (the full 440-row table is `artifacts/asl/evidence-iter11.md`, made by
`JanusASL/tools/evidence.py` from `artifacts/asl/verdicts-iter11.jsonl`):

| id | word | reg | Janus | Lean ASL (before fix) | qemu | Sail C++ |
|---:|---|---|---|---|---|---|
| 610 | 0x1ac00c42 (SDIV W) | X2 | 0x0 | 0xffffffff | 0x0 | 0x0 |
| 633 | 0x1ac30c44 (SDIV W) | X4 | 0xfdaee77d | 0xffffffff | 0xfdaee77d | 0xfdaee77d |
| 186745 | 0x9ac00c20 (SDIV X) | X0 | 0xfffffffff8000201 | 0x0 | 0xfffffffff8000201 | 0xfffffffff8000201 |
| 186817 | 0x9ac10801 (UDIV X) | X1 | 0x3de680db106ba48 | 0x3de680db106ba40 | 0x3de680db106ba48 | 0x3de680db106ba48 |
| 1157790 | 0x9b2e46a6 (SMADDL) | X6 | 0x2467ae81 | 0x2467ae83 | 0x2467ae81 | 0x2467ae81 |
| 1158386 | 0x9b3c58fc (SMADDL) | X28 | 0xf9f1c8ba4179c21d | 0xc47539be | 0xf9f1c8ba4179c21d | 0xf9f1c8ba4179c21d |

UDIV X 0x...a48 against 0x...a40 is the `Float` rounding of bug 6. The 0x0 and 0xffffffff rows
are the negative-to-0 truncation of bug 5. After the fixes the full corpus gives 0 MISMATCH. The
SMADDL/SMSUBL, SMULH and UDIV/SDIV classes are now also *proved* (`maddl_agree`, `mulh_agree`,
`div_agree`; `Div.rtz` shows that `RoundTowardsZero(Real(a)/Real(b))` over `Rat` is `Int.tdiv`).
A regression of bug 5 or bug 6 would therefore most likely break the proof build.

Earlier iterations found, and fixed in the harness or slice: TTBR0 register aliasing (an "Out of
Memory Range at 0" walk), encodings excluded by mistake, and RPRFM missing from `keep.txt`. None
of these was a Janus bug. No case so far has shown Janus disagreeing with the ASL.

## Trust story

The proofs relate Janus to **the generated Lean**, not to Arm's ASL text itself. These links in
the chain are trusted:

1. **Arm's ASL → Sail** (asl_to_sail, as published in sail-arm). This link is shared with the
   Sail C++ oracle and with every other user of sail-arm.
2. **Sail → Lean** (Sail 0.20.3's Lean backend with the patches above). It is checked
   empirically: on the 583,756-case corpus, the Lean model agrees with Janus on every case that
   both run, and Janus agrees with qemu and with the C++ build of the same Sail
   (`docs/ORACLE.md`, `docs/ORACLE-SAIL.md`). The development history shows why this link needs the test: bugs 4–6
   all produced code that compiled.
3. **The slice and splices.** Kept decode patterns are verbatim. A word that Janus decodes and
   that lands on an excluded body is reported by the check rather than hidden. The splices
   replace only exception entry, PAC nibble tables and system register dispatch. None of them is
   on the path of a proved class.
4. **The harness** (`janus_step`, `janus_init`). It covers one instruction from decode, with no
   fetch, no interrupts and no debug, at EL0. The proofs quantify over every Sail state related
   by `Rel`, so they depend on `janus_init` only through `Rel`'s EL0/SP_EL0 conditions (and the
   SPE flag for ¹).
5. **lean-sail v7** (the `SailM` monad, `BitVec` helpers) and the Lean kernel.

Janus itself is not trusted: its `decode` and `step` are the objects under test and proof. The
check compares against compiled code, so it also trusts the Lean compiler. The proofs do not.

## Regenerating

```
scripts/asl.sh deps        # once: about 20 min (opam switch, Sail build)
scripts/asl.sh gen         # about 15 min; fails if the result differs from vendor/ArmASL.tar.gz
GEN_UPDATE=1 scripts/asl.sh gen   # after changing slice.py/keep.txt/splices/harness: replace it
scripts/asl.sh check && scripts/asl.sh prove
```

`gen` is deterministic. The tarball is written with sorted names, mtime 0 and `gzip -n`, and the
slice paths in assertion messages are rewritten to `sail-arm/arm-v9.4-a/src/`. A rebuilt
toolchain therefore reproduces the vendored file byte for byte. After you change the Sail side,
rebuild the plugin with `cd JanusASL/sail/plugin && rm -rf _build && dune build
./sail_plugin_janus.cmxs` (inside the opam env). To add a decode function to the slice, list it
in `keep.txt`, and also in `roots.txt` if nothing reaches it. To prove a new class, generate its
dispatch lemma with
`python3 JanusASL/tools/chain.py JanusASL/ArmASL __DecodeA64_DataProcReg <name> 'lo:len:val,...'`
and follow `Madd.lean`.
A file of many such lemmas (as `LdStDecode*.lean`) should then be split with
`python3 JanusASL/tools/split_proofs.py JanusASL/JanusASL/Proofs/<File>.lean 4`, which keeps every
part near 3.5 GiB (see "Memory").
