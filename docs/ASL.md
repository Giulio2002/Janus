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
scripts/asl.sh build    # unpack the vendored model and build the package (about 40 min, once)
scripts/asl.sh check    # build + janus-asl-check on artifacts/oracle/cases.jsonl
scripts/asl.sh prove    # build JanusASL.Proofs and audit their axioms
scripts/asl.sh verify   # janus verify --asl on the shipped Add, Max, Mul64, Add128 proofs
```

`janus verify <outdir> --proof P.lean --asl` turns a verified theorem into the same statement
about the ASL, bound to the binary ([below](#janus-verify---asl-the-corollary-of-a-verified-theorem)).

## Results

| | |
|---|---|
| corpus | `artifacts/oracle/cases.jsonl` from `scripts/oracle.sh full`: 583,756 cases (qemu: 0 MISMATCH) |
| `janus-asl-check` | **562,288 agree, 21,468 gap, 0 MISMATCH**; `LinuxEL0Config` holds on the base state and on all 583,756 cases' pre- and post-states; about 3 min on 48 cores |
| proofs | **35 audited theorems** (`scripts/asl.sh prove`): 31 encoding-class `*_agree` theorems, `step_agree`, `run_agree`, `Ensures.toASL` and `StepOK.of_agree`, no `sorry`, no `native_decide`, no `bv_decide`; axioms: `propext`, `Classical.choice`, `Quot.sound` only. The theorems of `JanusASL.Verify` behind `janus verify --asl` (`classify_sound`, `covered_words`/`_code`/`_stubs`) are axiom-audited with every corollary |
| `janus verify --asl` | the ASL corollaries of the shipped `Add`, `Max`, `Mul64` and `Add128` proofs, derived from their artifacts, audited and kernel-replayed (`scripts/asl.sh verify`, `TestASLExamples`) |

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
| loads/stores, atomics, exclusives, PRFM | | tested | |
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
* `SPESampleInFlight = false`, `InGuardedPage = false`;
* PSTATE.EL = 0, PSTATE.nRW = 0, PSTATE.SP = 0.

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
the caller in a state related to one satisfying the ABI and the postcondition.

`janus verify --asl` applies it to any verified theorem of that shape, about the very
`Extracted.program` that was identity-checked against the binary
([below](#janus-verify---asl-the-corollary-of-a-verified-theorem)). For the shipped examples:

| example | instructions | ASL corollary (`janus verify artifacts/<name> --proof examples/proofs/<name>.lean --asl`) |
|---|---|---|
| `Add` | ADD, RET | `(js'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64` after `aslRun` returns |
| `Max` | CMP (SUBS), B.cs, MOV (ORR), RET, both sides of the branch | `js'.regs 0 = if y.toNat < x.toNat then x else y` |
| `Mul64` | MUL (MADD), UMULH, MOV, RET | the 128-bit product in `X0:X1` |
| `Add128` | ADDS, ADC, RET | the carry chain, modulo `2^128` |

So for these programs the shipped guarantee, for example "Add returns x + y", holds of Arm's ASL
(as translated) under `LinuxEL0Config`. Earlier versions copied the four programs by hand into
`JanusASL/Proofs/Examples.lean`; those copies are gone, and the corollaries now come from the
artifacts (`cmd/janus` test `TestASLExamples`, and `.github/workflows/asl.yml`).

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
build`), the proofs take about 2 min (most of it in Bitmask.lean).

## `janus verify --asl`: the corollary of a verified theorem

```sh
janus verify artifacts/Add --proof examples/proofs/Add.lean --asl
```

```text
Verified: Proof.correctness
  …
ASL corollary: Verified: JanusASLCorollary.correctness_asl (Arm's ASL, model 1ac61b021dc05f49…)
  Coverage: all 2 words in the proved subset (addSubShifted 1, ret 1)
  Axioms: Classical.choice, Quot.sound, propext
  Kernel replay: leanchecker passed (ArmASL, ArmASL.Defs, …; 116 modules; …)
  Statement:
    JanusASLCorollary.correctness_asl (x y : BitVec 64) {ret : Nat} (hret : Janus.GoABI.RetAddr Extracted.program ret)
      {js : Janus.Arm64.State} (hs : Janus.GoABI.CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] js)
      (hpre : True) {s : JanusASL.Proofs.SState} (h : JanusASL.Proofs.Rel js s) (hc : JanusASL.Proofs.LinuxEL0Config s) :
      ∃ fuel s' js', JanusASL.Proofs.aslRun (Extracted.program.withExit ret) fuel s = JanusASL.Proofs.AslOutcome.returned s' ∧
        JanusASL.Proofs.Rel js' s' ∧ JanusASL.Proofs.LinuxEL0Config s' ∧ Janus.GoABI.ABIReturn js js' ∧
        BitVec.toNat (js'.regs 0) = (x.toNat + y.toNat) % 2 ^ 64
  Assumptions (see janus explain):
    - Rel js s: …
    - LinuxEL0Config s: …
```

`--asl` works for single proof files, consumer packages (`--proof-root`) and `verify-batch`. It
runs after the main verification has passed, and **never changes its result**: when the ASL stage
fails, `verified.json` still records the verified theorem, its `asl` record says
`"status": "invalid"` with the failure, and janus prints `Invalid: ASL corollary: …` with the stage
and exits with status 1.

The theorem must be an arm64 `Ensures` specification about `Extracted.program` itself:
`∀ xs, Janus.GoABI.Ensures Extracted.program entry args pre post`, possibly behind definitions at
the head of its conclusion (`EnsuresResults`, a consumer's `Computes … spec`), which are unfolded.
The steps, each with its own stage:

1. **`ASL build`.** The JanusASL package (this directory: `JanusASL/`, its proofs, the vendored
   model `vendor/ArmASL.tar.gz`, checked against `ArmASL.tar.gz.sha256`) is embedded in the
   `janus` binary like the framework (with `--janus-root`, `<root>/JanusASL` is used). It is
   materialized in the trusted cache, `<cache>/v1/asl/<key>`, keyed by the framework's identity,
   every JanusASL source (with the model), the toolchain and the framework build it requires,
   and built there with Lake (`lake build ArmASL JanusASL`), trusted and unsandboxed: only Janus'
   own sources and the pinned lean-sail are involved. **The first build takes about an hour**
   (most of it elaborating the 24 ArmASL modules; about 40 min on 48 cores), needs about 1 GB of
   disk and fetches lean-sail from GitHub; later runs only check Lake's traces (well under a
   second). `janus framework` shows the build directory and whether it is built. Builds are
   kept for `$JANUS_ASL_RETENTION_DAYS` (default 30) after their last use. Lake reuses modules
   by content hash, so a build directory can be seeded from an in-tree build
   (`scripts/asl.sh verify` does so from `JanusASL/.lake`). The compiled modules of the build
   (JanusASL, ArmASL and lean-sail) are then **pinned** like the framework and re-checked after
   every later step.
2. **`ASL coverage`.** janus compiles, trusted (it imports only `Extracted` and
   `JanusASL.Classify`), the module `JanusASLWords`:
   `theorem JanusASLWords.covered : JanusASL.Classify.covered Extracted.program = true := by decide +kernel`.
   `classify` (Classify.lean) tests, for each word, exactly the hypotheses of one
   `stepOK_<class>` theorem of Run.lean; `JanusASL.Verify.classify_sound` proves that a
   classified word is `StepOK`, and `covered` also checks that the code and stubs are untagged.
   The kernel evaluates it on the identity-checked `Extracted.program`. If a word is not covered,
   the stage fails and lists each one with its address, what Janus decodes it to and its Arm
   encoding group, for example
   `word 0xf9400b90 at 0x8cdd0 (example.com/basic.Div): Janus.Arm64.Instr.ldstUImm, loads and stores`;
   `verified.json` has the list under `asl.coverage`, and the class counts.
3. **`ASL corollary`.** janus compiles, sandboxed (it imports the untrusted proof), the module
   `JanusASLCorollary`:
   `janus_asl_corollary JanusASLCorollary.correctness_asl of <theorem> using JanusASLWords.covered`.
   The command (Verify.lean) adds the theorem that `JanusAudit.aslCorollary` builds:
   `fun xs => Ensures.toASL (thm xs) (covered_words _ w) (covered_code _ w) (covered_stubs _ w)`,
   with the inferred, beta-reduced type. Lean rejects a proof that declares a name JanusASL or
   the two generated modules declare (they cannot be imported together).
4. **`ASL audit`.** The trusted auditor (`JanusAudit.runASL`, Janus/Tools/Audit.lean; no proof
   code runs) checks that the corollary is a theorem of `JanusASLCorollary` whose type is
   **exactly** `aslCorollary <theorem> JanusASLWords.covered`, recomputed by the same function
   from the user's theorem; that `Extracted.program`/`entry` are definitionally the trusted copy;
   that no untrusted module (the proof, a consumer or dependency module, the corollary module
   apart from the corollary) declares a name under `Extracted`, `JanusASL`, `ArmASL`, `Sail`,
   `JanusASLWords` or `JanusASLCorollary`; and it prints the statement in a clean environment
   (`Extracted`, `Janus` and `JanusASL.Verify`), with the same instance checks and round-trip as
   the main statement, and collects its axioms (only `propext`, `Quot.sound`,
   `Classical.choice`).
5. **Kernel replay.** `leanchecker` replays the corollary's whole non-core closure, the 24 ArmASL
   modules, lean-sail and JanusASL included (about 100 s the first time, then from the replay
   cache). Every JanusASL, ArmASL and Sail module must resolve from the pinned JanusASL build, and
   no other directory of the verification may hold a module under those roots or the two
   generated ones (`ASL module identity`).
6. **`verified.json`** gets an `asl` record: `status`, `of` (the verified theorem), `theorem`,
   `derivation`, `statement`, `statementExplicit`, `definitions`, `axioms`, `kernelReplay`,
   `coverage`, `model` (`armASLSha256` of the vendored model, `janusASLSha256` over the JanusASL
   sources, the sail-arm / Sail / lean-sail pins from `vendor/ArmASL.version`, the build
   directory) and `assumptions`, the hypotheses in plain words. `janus explain` prints them.

**What the corollary assumes.** Besides the user's own preconditions: `Rel js s` (the ASL state
holds the Janus call state's registers, SP, PC and flags, at EL0), `LinuxEL0Config s` (the Linux
EL0 configuration of `janus_init`, [above](#linuxel0config-configlean)), and the trust story below
(the generated Lean model; instructions fetched with the program's own `fetch`; only returning
runs transferred). When load/store classes are proved, their memory assumption (`UserMapped`: Janus'
regions are identity-mapped user memory under the ASL's own translation) appears in the
statement and in the plain-words list.

**Attacks** (`audit/asl/attacks`, rows in `audit/run-all.sh` with `JANUS_AUDIT_ASL=1`, Go test
`TestASLForgeryRejected`): a proof that declares `JanusASL.Proofs.Ensures.toASL` itself (X1),
proves its own fake "ASL" theorem with a proof-local `Ensures.toASL` and asks for it (X2), plants
`JanusASLWords.covered` (X3) or `JanusASLCorollary.correctness_asl` (X4), overrides the
`janus_asl_corollary` command to add `True` under the corollary's name (X5: rejected by the
auditor's type check), states its theorem about a `p` only assumed equal to `Extracted.program`
(X6), or declares a look-alike under a reserved root (X7: the auditor's namespace rule). Each
main theorem verifies; each ASL corollary is refused. A consumer package with a module under
`JanusASL` is refused (`ASL module identity`, `TestASLConsumer`).

## The pipeline: what is reused, at which versions

| component | version / pin | role |
|---|---|---|
| Lean | 4.34.1 (`lean-toolchain`, same as Janus) | |
| [sail-arm](https://github.com/rems-project/sail-arm) | `7d0581642d0e` (master; includes the Lean `MOD` = `Nat.mod` fix in `prelude.sail`) | Arm's ASL for v9.4-A, translated to Sail by Arm's asl_to_sail |
| [Sail](https://github.com/rems-project/sail) | tag `0.20.3` + `JanusASL/sail/sail-0.20.3-upstream-backports.patch` + `JanusASL/sail/sail-0.20.3-janus-lean-fixes.patch` | Lean backend |
| OCaml / opam | 5.2.1 / opam 2.x, own root `$DEPS/opam`, switch `sail-0.20.3-janus` | builds Sail |
| [lean-sail](https://github.com/rems-project/lean-sail) | tag v7, `8fc8e29d7a62` | Lean runtime library of the generated code (v6, Sail 0.20.3's default, does not build on 4.34.1) |
| generated model | `JanusASL/vendor/ArmASL.tar.gz` (sha256 in `.sha256`), 24 modules, 21 MB | unpacked into `JanusASL/ArmASL*` (ignored by git) |

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
* **`split_lean.py`** splits the single output file into 24 chained modules, so that Lake
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
