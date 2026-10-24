# Soundness audit of `janus verify` (arm64)

Date: 2026-10-23. Scope: `cmd/janus` (verify, identity, extract, binary, data), `Janus/**` except
`Janus/Amd64`, `examples/proofs`. Lean 4.34.1, go1.26.0, example binary
`artifacts/examples-arm64` (SHA-256 `86dcc5ab…e176`).

The claim under attack: *if `janus verify` prints `Verified` for a theorem, that theorem holds
for the actual bytes of this binary under the stated semantics, and the printed statement is
that theorem.*

**Post-fix status (re-run 2026-10-23 on `agent/deps-ci`, `audit/run-all.sh`):** every row of
the table below is now blocked, verified-honest, mitigated or fixed; no row prints `Verified`
for a false or misleading claim. The "Status after fixes" column has the per-row result and
[Fixes applied](#fixes-applied) maps F1–F7 to the code. Finding R1 (compiled framework modules
writable by the untrusted consumer build, and not bound to the framework sources) was found
after F1–F6 and is fixed by F7; see [R1](#r1-critical-follow-up-compiled-framework-modules-were-not-bound-to-the-framework). `audit/run-all.sh` exits non-zero if
any row regresses to BROKEN, and CI runs it. The rest of this document is the original audit
of the pre-fix code (commit `665fb69`), kept as written. A second audit round found that an
instance written inline in the statement could still make the printed statement lie (fixed: the
printed statement must round-trip and instance arguments must be registered instances) and that
the `unshare` fallback left non-root mounts writable (fixed); see [Round 2](#round-2-2026-10-23).

Result (pre-fix): **the claim did not hold.** A proof file can (a) execute arbitrary code during
verification and forge the audit result outright (a `False` theorem proved with `sorry` is
reported as Verified with no axioms), (b) make the printed statement differ from the checked
one with plain Lean features (instances, unexpanders), and (c) substitute a different
`Extracted` module than the checked one. The kernel, the axiom list and the model's
instruction semantics are fine. The holes are all in the verifier's handling of untrusted
Lean code. There are also two spec-level holes (`NeverPanics`, the `0` return sentinel) and
minor memory-model looseness.

All attack files are in `audit/`. `audit/run-all.sh` reproduces everything (it needs a
building `lake build Janus`; on 2026-10-23 that build was broken by the in-progress
`Janus/Amd64/Exec.lean`, unrelated to this audit). Every BROKEN result was reproduced twice:
with `audit/bin/janus` built from the working tree at audit start (commit `665fb69` with
the original `verify.go`), and with `audit/bin/janus-head` built later from the working tree,
which includes the uncommitted `verify.go` rewrite (framework root, `modules` in the audit
record).

## Severity-ranked summary

| # | Severity | Finding | Status (audit, pre-fix) | Status after fixes |
|---|----------|---------|--------|--------------------|
| A3 | **Critical** | `initialize` in the proof runs inside the audit process: it reads the nonce from `Audit.lean`, prints a forged audit record and exits 0. `theorem correctness : False := sorry` is reported as Verified, axioms "(none)". | **BROKEN** | **blocked**: janus-audit loads the proof with `importModules` and never enables initializers, so the `initialize` never runs; run-all: `Invalid` (statement does not mention Extracted) |
| A6 | **Critical** | `#eval` (also `run_cmd`, `elab`, …) runs arbitrary IO with the verifier's privileges while the proof compiles. That is enough to plant C1 permanently or start C2. | **BROKEN** | **blocked**: the proof compiles under bubblewrap (no network, read-only filesystem except a private work dir); run-all: `Invalid` (`read-only file system`) |
| C1 | **Critical** | The `Extracted` that the proof, the audit and leanchecker import is never confirmed to be the checked one. Lake's library dir precedes `.janus-build` on `LEAN_PATH`, so an `Extracted.olean` planted there wins: the statement reads exactly `Extracted.program`, the binary SHA matches, and the program is fake. | **BROKEN** | **blocked**: Extracted is compiled into a private trusted dir first on `LEAN_PATH`, a stray `Extracted.olean` elsewhere is rejected, and the audit checks `Extracted` is defeq to an independent `JanusTrusted` copy; run-all: `Invalid` (module identity) |
| C2 | **High** | TOCTOU on `.janus-build`: swapping `Extracted.olean`+`Proof.olean` after the proof-compile integrity check (when `Audit.lean` appears) makes the report show a different statement while recording the **honest** proof's path and SHA-256. | **BROKEN** | **mitigated**: fresh private work dir per run, sandbox with `--die-with-parent` in a new PID namespace, every olean hash-bound and re-checked; run-all: honest proof `Verified` |
| A1 | **High** | A proof-local `instance (priority := high) : HMul Nat Nat Nat := ⟨Nat.add⟩` makes a printed `x.toNat * y.toNat` mean `+`. "Add returns x*y" verifies. | **BROKEN** | **blocked**: proof-local class-valued defs and instances are rejected in the statement; run-all: `Invalid` (disguised instance `HMul`) |
| A2 | **High** | A proof-local `@[app_unexpander]` prints `Shown P Q` (meaning `Q`) as `P`. | **BROKEN** | **verified-honest**: still verifies, but the statement is printed in a clean environment without the proof's unexpander, so it shows `Shown (… = x.toNat * y.toNat) True` |
| A4 | **High** | Same with an unexpander for the *Janus* constant `Ensures`: the statement uses only Janus/Extracted constants, the post is `True`, and it prints as "x0 = x * y". | **BROKEN** | **verified-honest**: still verifies; the clean print shows the real post `fun x x_1 => True` |
| B1 | **High** | `NeverPanics` counts faults as "no panic". Go nil dereferences are hardware faults (SIGSEGV → `sigpanic`), not stub calls, so "Add256(z, nil, y) never panics" verifies although real Go panics. | **BROKEN** (spec) | **blocked** (spec fixed, F3): the attack no longer compiles (`NeverPanics` now also requires no fault); its negation `B1_refuted` verifies |
| A9 | Medium | `Proof.Extracted.program` (a fake program) is what `Extracted.program` resolves to inside `namespace Proof`. It prints qualified, but the "does not mention Extracted" warning stays silent. | **BROKEN** (weak) | **blocked**: a non-trusted module may not declare a name with an `Extracted` component, and the statement must mention `Extracted.program`/`entry`; run-all: `Invalid` |
| B2 | Medium | `exitAddr = 0` is a computable value: any computed branch to 0 (`BR X0` with X0 = 0, a zero code pointer loaded from a supplied region) counts as `Returns`. On hardware it is SIGSEGV. | **BROKEN** (design) | **blocked** (design fixed, F4): `Ensures` quantifies over every admissible return address (`RetAddr`); the attack does not compile, `B2_refuted` proves the 0-sentinel claim false |
| M2 | Low–Med | Model: no top-byte-ignore. Regions at `x` and `x + 2^56` are distinct in the model but alias on Linux EL0, so `Disjoint` does not imply non-aliasing on hardware. | mismatch | **fixed** (F5): accesses must end at or below `2^48`, so tagged addresses fault; `Model.lean` control faults |
| M1 | Low | Model: an access crossing 2^64 is `.ok` and touches nonexistent bytes ≥ 2^64 (hardware wraps or faults). Needs a region that extends past 2^64. | mismatch | **fixed** (F5): the `2^48` bound excludes accesses crossing `2^64`; `Model.lean` control faults |
| M3 | Low | Model: overlapping RO and RW regions let a store succeed on "read-only" (`DataLoaded`) bytes. | mismatch | **fixed** (F5): a store faults if any read-only region overlaps it; `Model.lean` control faults |
| E1 | Low | PIE (`ET_DYN`) binaries are accepted. The model uses link-time vaddrs, while real calls run at base + vaddr, and no translation-invariance argument covers that. No relocations target copied (read-only) ranges in Go PIE today. | informational | **fixed** (F6): `ET_DYN` is rejected at binary validation (checked: `janus list` on an arm64 `-buildmode=pie` build fails) |
| E2 | Info | `--theorem` accepts any Unicode letters (`\p{L}`), so lookalike names are possible. | informational | **fixed**: `theoremNameRE` is ASCII-only (checked: a Cyrillic-`е` name is rejected) |
| R1 | **Critical** (follow-up, found after F1–F6) | Compiled framework modules were not bound to the framework. In a consumer workspace the untrusted, sandboxed `lake build` could write the framework's build directory: a lakefile `#eval` that recompiles `Janus/GoABI.lean` with `Ensures := True` over `Janus/GoABI.olean` made "Add returns 42" verify (axioms none, replay passed: a well-formed substituted olean replays fine), and one that replaces `Janus/Tools/Audit.olean` made the auditor print an all-clear record for `False := sorry`. `JanusTrusted` was never replayed. | **BROKEN** (both reproduced with the `6fbaeba` verifier, under bubblewrap) | **blocked** (F7): framework build pinned by SHA-256 and read-only to every sandboxed process, closure resolved from trusted homes, whole non-core import closure kernel-replayed with a content-keyed cache; run-all rows `R1*`: `Invalid` |

Blocked (with mechanism): A5 `debug.skipKernelTC`+`addDecl`, A7 private shadowing, A8 renamed
axiom / sorry / `partial` / `opaque`, A10 `#exit`, theorem in another namespace or module,
TOCTOU on `Extracted.lean` and the binary, fuel tricks, empty `CallSetup`, exitAddr colliding with
code, `implemented_by` in the tactic, `native_decide`. All 14 example theorems have axioms
⊆ {propext, Quot.sound, Classical.choice}, and the Add, Add256 and Get preconditions are
satisfiable (concrete witnesses).

---

## 1. Verifier bypasses

Workspace for every run: `audit/work/<Fn>` = copies of `artifacts/<Fn>/{Extracted.lean,identity.json}`
plus `audit/work/examples-arm64` (same SHA). Command shape:
`janus verify --proof audit/attacks/X.lean audit/work/Add`.

### A3 (Critical, BROKEN): forged audit via `initialize`

`audit/probe/{P,Q}.lean` shows that `lean` runs `initialize` blocks of imported modules (and
`#eval` at compile time). The audit is `lake env lean Audit.lean` with `import Proof`, so proof
code runs inside the audit process before the audit's own `#eval`.
`audit/attacks/A3_initialize.lean` reads `$LEAN_PATH/Audit.lean`, extracts the
`janus-audit-<nonce>: ` marker, prints
`{"name":"Proof.correctness","kind":"theorem","module":"Proof","axioms":[],"statement":"…"}`
and calls `IO.Process.exit 0`. The theorem in the file is `theorem correctness : False := sorry`.
leanchecker accepts the environment (`sorryAx` is an ordinary axiom to the kernel), and the
nonce does not help because it is on disk in the file being run. Output:

```
Verified: Proof.correctness
  Axioms: (none)
  Kernel replay: leanchecker passed (Janus, Extracted, Proof)
  Statement:
    Proof.correctness : Add returns x * y (forged)
```

### A6 (Critical, BROKEN): arbitrary IO at proof compile time

`audit/attacks/A6_eval_io.lean` is the honest Add proof plus
`#eval IO.FS.writeFile "/srv/janus/audit/work/A6-written-during-verify.txt" …`. It verifies, and
the file appears. The check "Extracted.olean changed while the proof was being checked" only
covers one file at one moment. The same IO could plant C1 in the Janus library dir or the
framework cache (a persistent backdoor that affects every later verify), start the C2
watcher, or rewrite `bin/janus`.

### C1 (Critical, BROKEN): the imported `Extracted` is not the checked one

`lake env` builds `LEAN_PATH=<root>/.lake/build/lib/lean:<toolchain>:<.janus-build>`. Lake's
paths come **first** (the code comment says so). A file
`<root>/.lake/build/lib/lean/Extracted.olean` therefore shadows the freshly compiled
`.janus-build/Extracted.olean` for the proof, the audit and leanchecker. Repro, on a disposable
copy of the root (`audit/work/janus-root-copy`, built by `run-all.sh`): compile
`audit/attacks/C1_fake_Extracted.lean` (a program with `exitAddr := entry`) into the copy's lib
dir, then `janus verify --janus-root <copy> --proof audit/attacks/C1_proof.lean audit/work/Add`:

```
Verified: Proof.correctness
  Statement:
    Proof.correctness (x y : BitVec 64) :
      Janus.GoABI.Ensures Extracted.program Extracted.entry [x, y] (fun s => s.regs 0 = x * y) fun x_1 s' =>
        s'.regs 0 = x * y
```

The statement is textually what an honest reader expects, and identity, SHA and re-extraction
all pass. The same applies to `Proof.olean` and `Audit.olean` (none of these names may resolve
outside `.janus-build`).

### C2 (High, BROKEN): TOCTOU on `.janus-build`

`audit/attacks/C2_toctou_swap.sh` runs `janus verify` on the **honest**
`examples/proofs/Add.lean`. A concurrent shell loop waits for the build dir to be recreated and
for `Audit.lean` to appear, then copies a precompiled fake `(Extracted.olean, Proof.olean)`
pair into it. The audit and leanchecker load the swapped pair (Lean does not check import
hashes), and the final re-check only compares the *sources*. Report:
`Proof: examples/proofs/Add.lean` with that file's SHA-256, and the statement
`… (fun s => s.regs 0 = x * y) fun x_1 s' => s'.regs 0 = x * y`. A6 can start the same watcher
from inside the proof itself.

### A1, A2, A4 (High, BROKEN): the printed statement is not the checked statement

The statement is `ppSignature` run in an environment that includes the proof module's
instances, unexpanders, delaborators, notations and macros.

* `A1_instance.lean`: `instance (priority := high) evilMul : HMul Nat Nat Nat := ⟨Nat.add⟩`;
  `theorem correctness … (s'.regs 0).toNat = (x.toNat * y.toNat) % 2 ^ 64 := honest x y` (defeq).
  The printed statement reads "Add returns x*y mod 2^64".
* `A2_unexpander.lean`: `def Shown (_ : Prop) (actual : Prop) := actual` with an
  `app_unexpander` that prints the first argument. Post `Shown (x0 = x*y) True`.
* `A4_unexpand_janus.lean`: an `app_unexpander` for `Janus.GoABI.Ensures`, with
  `set_option hygiene false`. The checked post is `fun _ _ => True`; the printed one is
  `BitVec.toNat (s'.regs 0) = HMul.hMul (BitVec.toNat x) (BitVec.toNat y)`. Every constant in
  the statement is from Janus/Extracted, so a "no proof-local constants" rule alone would not
  catch this.

### A9 (Medium, BROKEN): namespace shadowing

`A9_namespace_shadow.lean` declares `Proof.Extracted.program` (empty code, `exitAddr := entry`).
Inside `namespace Proof`, `Extracted.program` resolves to it. It verifies with statement
`Ensures Proof.Extracted.program Extracted.entry …`. That is honest if read carefully, but the
substring warning (`strings.Contains(statement, "Extracted.")`) is satisfied, so nothing flags
it.

### Blocked

* **A5** `set_option debug.skipKernelTC true in run_cmd … addDecl (theorem : False := True.intro)`:
  leanchecker rejects it (`declaration type mismatch`), so the replay really covers the Proof
  module's declarations.
* **A7** `private def Extracted.program`: Lean rejects it ("a non-private declaration … has already
  been declared"). Defining a public `Extracted.program` without importing Extracted breaks the
  audit (duplicate import).
* **A8** renamed `axiom helperLemma : False` (reported as a disallowed axiom), `sorry` (sorryAx),
  `partial def` (opaque, so `rfl` fails and it falls back to sorry), `opaque … := 1` (not
  unfoldable). `implemented_by`/`@[extern]` affect only compiled code, never kernel reduction,
  so a `Decidable` instance trick with `decide` is checked by the kernel. `native_decide` brings
  in `Lean.ofReduceBool` (rejected).
* **A10** `#exit` before the theorem: "The proof does not define Proof.correctness."
* **Another namespace or module**: the audit looks up the exact `--theorem` name and requires
  `kind = theorem` and `module = Proof`.
* **TOCTOU on inputs**: `check` hashes the binary and regenerates `Extracted.lean` from the
  in-memory bytes. `.janus-build` receives the checked bytes, and step 7 re-checks the binary,
  `Extracted.lean` and the proof source. Swapping the binary or `Extracted.lean` and back during
  the run has no effect. Only the build *outputs* are exposed (C2).

## 2. Vacuous specs

* **B1 (High, BROKEN): `NeverPanics`.** `audit/specs/B1_neverpanics_fault.lean`, on the Add256
  artifact:
  `∀ z y s, CallSetup … [z, 0, y] s → s.mem.regions = [] → NeverPanics Extracted.program s`.
  It verifies (axioms propext, Quot.sound). The first instruction `ldr x3, [x1]` faults
  (`outsideAllocation 0 8`), and `NeverPanics` (`∀ fuel, run ≠ .ok (.stub _ .panic _)`) is
  satisfied by any fault, by `noCode` and by `undecodable`. In Go the nil check is implicit, so
  real execution panics with "invalid memory address or nil pointer dereference". README's
  "Go runtime panic stubs (bounds checks, nil, divide) are named outcomes" is wrong for nil.
* **B2 (Medium, BROKEN by design): return sentinel 0.** `audit/specs/B2_exit_sentinel.lean` is a
  synthetic one-word program `br x0` (`0xd61f0000`). `CallSetup … [0] s → Returns … (ABIReturn s ·)`
  is provable. `Program.run` treats *any* arrival at `pc = 0` as a return. A Go function that
  calls through a code pointer loaded from caller memory (closure, interface method table) is
  "proved to return" for every state where that word is 0, while hardware takes SIGSEGV. None of
  the 14 examples has an indirect call, so none is affected.
* **Fuel**: blocked. `Returns` is `∃ fuel s', run = .ok (.returned s')`, which `outOfFuel` cannot
  satisfy, and `run_mono` / `run_ok_unique` make the result fuel-independent.
* **Empty `CallSetup`**: `CallSetup` is satisfiable for any `args` of length ≤ 30
  (`setup_callSetup`). With ≥ 31 args, `args[30]` must equal `exitAddr`, otherwise the theorem is
  vacuous, but that is visible in the statement.
* **exitAddr collision with code**: 0 is outside `.text` and never a stub address, so the
  collision only comes from computed branches (B2).
* **Positive controls (all Verified)**, in `audit/controls/*_witness.lean`: the original example
  proof plus a concrete state.
  * `Add`: `s0 x y` satisfies `CallSetup`, and applying `Proof.correctness (-1) 2` gives
    `x0 = 1`.
  * `Add256`: one RW region `[0x1000, 0x1100)` with z, x, y = 0x1000, 0x1020, 0x1040 satisfies
    `Ptr32 ∧ Aliasing` (by `decide`), and the theorem's `Returns` conclusion is obtained for it.
  * `Get`: a stack window `[sp-24, sp+16)` RW, `g` at 0x2000 RO with stackguard0 = 0, and a
    4-word slice at 0x3000 RO satisfy `GuardOK s 0`, `StackOK s 24 16`, `Ptr`, `Disjoint`.
    Both conclusions are derived concretely: `Returns` for i = 1 and `Panics` for i = 5.

## 3. Model vs. reality

Details and runnable `#eval`/`decide` controls are in `audit/model/Model.lean`
(`lake env lean audit/model/Model.lean`). The decoder was compared with objdump over 600k random
words in the accepted classes (`audit/model/decoder_vs_objdump.sh`): no word was accepted by the
model and rejected by objdump.

**Matches ARM ARM** (each has a control in `Model.lean`):
* SP alignment: checked on the base SP before the access, not on the effective address, and
  not re-checked after writeback (`CheckSPAlignment`).
* Flags: 32-bit ADDS/SUBS/ADCS/SBCS flags computed at width 32; ANDS/BICS set N:Z:00.
* CCMP/CCMN: `nzcv` immediate maps to N=bit 3 … V=bit 0.
* TBZ/TBNZ: bit = b5:b40 on X.
* ADR/ADRP: ADRP wraps at 2^64.
* LDR literal: sign-extension for LDRSW.
* LDP/STP/LDPSW: imm7 scaling, second address wraps.
* The BFM family; EXTR concatenation; DecodeBitMasks; MOVK; ExtendReg; division by
  INT_MIN/−1; variable shifts mod the datasize; BLR reads the target before writing X30.

**Rejected as reserved or unpredictable**:
* writeback with Rt = Rn;
* LDP with Rt = Rt2, and LDP writeback with Rt or Rt2 = Rn;
* W forms with shift ≥ 32; ROR in add/sub shifted; extended register with shift > 4;
* EXTR or BFM with sf ≠ N, and W forms with immr/imms ≥ 32;
* MOVZ/MOVK with hw ≥ 2 in the W form;
* logical immediate with N = 1 in the W form, or an all-ones pattern;
* register-offset option<1> = 0;
* PRFM, and the unprivileged, atomic, exclusive and pointer-auth forms.

**Mismatches** (all need a precondition that admits regions hardware cannot have; a real Go
call has a faithful model state, all regions below 2^48 and none overlapping, on which the model
matches hardware):

* **M1** `Memory.accessible` (`Janus/Arm64/State.lean`) compares in `Nat`, with no upper bound on
  regions. `ldr x0, [x1]` with x1 = 2^64−4 and region `[2^64−4, 2^64+4)` returns bytes from
  addresses ≥ 2^64 (model `0x5555555511111111`, ARM wraps to `0xAAAAAAAA11111111`).
  `Spec.Ptr` and `StackOK` bound regions by 2^64, but `StackWritable`, `DataLoaded` and raw
  `accessible` hypotheses do not.
* **M2** No top-byte-ignore: `str x2, [x0]` (x0 = 0x1000) then `ldr x3, [x1]`
  (x1 = 2^56 + 0x1000) gives 0 in the model and 0xdeadbeef on Linux EL0. Also
  `Spec.Disjoint 0x1000 8 (2^56+0x1000) 8` is provable.
* **M3** `store` succeeds if *any* writable region covers the address, so an overlapping RW
  region defeats a read-only `DataLoaded` region.

## 4. Extractor

* Bytes are taken from `.text` by section vaddr (`text.Addr`) with `Section.Data()` (file
  offset), so the offset/vaddr mapping is correct. Overlapping symbols or a size that crosses
  into the next function only duplicate true bytes at their true addresses (`fetchIn` returns
  the same word from either segment). Two symbols at one address go through the same
  `containing` choice on every path. The symbol lookup requires a unique name. Trailing-zero
  removal turns `udf #0` into `noCode` (still a fault). Nothing here makes the program differ
  from the binary.
* Identity: `check` binds `Extracted.lean` and `identity.json` to the binary SHA-256 by
  regeneration, both before and after verification. What is **not** bound is the compiled
  module that is actually imported (C1, C2). `verified.json` is a plain report (unsigned), so
  anyone can write one by hand. Consumers must re-run verify.
* Stub classification by name prefix is trusted. A binary built with `-checklinkname=0` could
  push an ordinary function to `runtime.panicX`, making `Panics` true of code that returns. The
  binary is the subject, not the adversary, so this is outside the threat model. Documented in
  SOUNDNESS item 3.
* **E1** PIE: `go build -buildmode=pie` extracts fine (HexDigit plus 256 bytes of `.rodata`).
  `readelf -r` shows 6315 `R_AARCH64_RELATIVE` relocations, none into a non-writable section
  (Go puts relocated data in `.data.rel.ro`, which is `WA` and so skipped). The model states
  link-time addresses, but the process runs at `base + vaddr`.

## 5. Tactic and axioms

* `Janus/Tactic/Core.lean` uses `unsafe` + `@[implemented_by]` (`evalProgDataImpl`, `evalNatImpl`)
  only to *compute* candidate values. Every fact used in a proof is an aux lemma whose value is
  `Eq.refl` (`kernelDecide`, `reduceDataReadD`, `evalClosedNat`), so the kernel re-checks it. A
  wrong interpreter result only makes the tactic fail.
* No `native_decide`, `ofReduceBool`, `trustCompiler`, `bv_decide`, `@[extern]` or
  `debug.skipKernelTC` in `Janus/**` (outside Amd64) or `examples/proofs`.
* Fresh verify of all 14 examples (Add, Add128, Add256, AddLimbs, AddThree, CopyWords, Div, Get,
  HexDigit, Max, Mul64, SetOne256, Sum, SumSquares): all Verified, axioms exactly
  {Classical.choice, Quot.sound, propext}, and leanchecker passed. (WrongAdd uses the other binary
  and was not re-run.)

---

## Proposed fixes

### F1 (A3, A6, C1, C2): treat the proof as untrusted code and bind the imported modules

1. **Sandbox every Lean process that loads the proof** (proof compile, audit, leanchecker) in
   `cmd/janus/verify.go` `leanRunner.run`. Run it under `bwrap` (or Landlock), with the
   filesystem read-only except a fresh private build dir, no network and a private `/tmp`.
   Without a sandbox, refuse to verify unless `--unsafe-no-sandbox` is passed, and print that in
   the report.
2. **Private, ordered build dir.** Use `os.MkdirTemp` (mode 0700) outside the artifact
   directory instead of `outdir/.janus-build`. Invoke `lean` directly (not via `lake env`) with
   `LEAN_PATH=<buildDir>:<janus lib>:<toolchain lib>`, `buildDir` **first**. Fail if `Extracted`,
   `Proof` or `Audit` resolve to any `.olean` outside `buildDir` (check every `LEAN_PATH` entry
   for `Extracted.olean`, `Proof.olean`, `Audit.olean`).
3. **Hash-bind the oleans.** Record the SHA-256 of `Extracted.olean` right after step 3 and of
   `Proof.olean` right after step 4. Re-hash them after the audit and after leanchecker, and fail
   on any change. Also add an identity check to the audit: write the checked `Extracted.lean`
   definitions into `Audit.lean` under `namespace JanusAuditCopy` (the Go side has the bytes),
   then `example : Extracted.program = JanusAuditCopy.program := rfl` and the same for `entry`
   (and `data`).
4. **Audit without running proof code.** Replace `lake env lean Audit.lean` with a trusted
   compiled Lean executable (`lean_exe janus-audit`, root `Janus.Tools.Audit`). It calls
   `importModules #[{module := `Extracted}, {module := `Proof}]` and never calls
   `enableInitializersExecution`, so no `initialize` from Proof runs. From that one in-memory
   environment it computes `collectAxioms`, kind and module, and runs the kernel replay
   (`Environment.replay` of Proof's constants), so leanchecker no longer reads the files a
   second time. It prints the record to a pipe or fd that the proof cannot see: no marker in a
   file on disk.
5. Defence in depth: a syntactic pre-check of the proof source in `verify.go`, rejecting
   `#eval`, `#exec`, `run_cmd`, `run_elab`, `run_meta`, `initialize`, `builtin_initialize`,
   `elab`, `elab_rules`, `macro`, `macro_rules`, `syntax`, `notation`, `infix`/`infixl`/`infixr`/`prefix`/`postfix`,
   `declare_syntax_cat`, `@[app_unexpander`, `@[delab`, `@[implemented_by`, `@[extern`,
   `@[init`, `unsafe`, `set_option debug.`, and any `import` other than `Janus`, `Janus.*` and
   `Extracted`. This is not sufficient alone, because imported macros could expand to these
   commands.

### F2 (A1, A2, A4, A9): print the statement that was checked

In the audit executable (F1.4):

1. Collect the constants of the theorem's type. Reject any constant from module `Proof` that is
   an instance, a class, `opaque`, an axiom, or `partial`/`unsafe` (blocks A1). Allow plain
   proof-local `def`s (CopyWords uses `M₀`), but print each one transitively with its body in
   the report's `definitions` field.
2. Pretty-print in a **clean environment** that imports only `Janus` and `Extracted`, with the
   allowed proof-local defs re-added by `addDecl` from their already-checked declarations. No
   unexpander, delaborator, notation or instance from Proof exists there (blocks A2 and A4).
   Also pass `pp.fullNames true` (blocks A9-style surprises).
3. Replace the warning in `cmdVerify` (`strings.Contains(r.Statement, "Extracted.")`) with an
   error: the type must contain the constant `Extracted.program` from module `Extracted`, and
   Proof may not declare any name with a component `Extracted`.
4. Allow only ASCII in `theoremNameRE` (E2).

### F3 (B1): `NeverPanics` must not be satisfiable by a fault (`Janus/GoABI.lean`)

```lean
/-- Execution never reaches a Go panic stub and never faults (a fault is a hardware trap, which
Go turns into a panic or a crash). Running out of fuel is allowed (non-termination). -/
def NeverPanics (p : Program) (s : State) : Prop :=
  ∀ fuel, match p.run fuel s with
    | .ok (.stub _ .panic _) => False
    | .error .outOfFuel => True
    | .error _ => False
    | .ok _ => True
```

`Returns.neverPanics` is still provable: below the return fuel the run is `outOfFuel` (by
`run_error_mono` / `run_ok_unique`), and from there on it is `.returned`. If the old meaning is
wanted, rename it `NoPanicStub` and say "faults are not counted". Fix the README sentence "Go
runtime panic stubs (bounds checks, nil, divide)": nil checks are hardware faults, not stubs.

### F4 (B2): do not use a computable sentinel (`Janus/GoABI.lean`, `Janus/Program.lean`)

Make the return address universally quantified. `Ensures p entry args pre post :=
∀ ra, ra % 4 = 0 → ra < 2^64 → (∀ seg ∈ p.segments, ra ∉ seg range) → (ra ∉ stub addrs) →
∀ s, CallSetup {p with exitAddr := ra} entry args s → pre s → Returns {p with exitAddr := ra} s …`.
A computed branch to a fixed value then reaches `ra` only if the code really computes from X30.
Existing proofs keep working with `ra` symbolic: the tactic already handles `h_lr`, and
`exitAddr` comparisons become `pc ≠ ra` side conditions discharged from the segment-range
hypothesis.

### F5 (M1, M2, M3): bound the address space and region permissions (`Janus/Arm64/State.lean`)

* `Memory.accessible`: add `&& addr + size ≤ 2 ^ 48` (Linux user VA, which also excludes tagged
  and wrapping accesses), i.e.
  `m.regions.any fun r => r.base ≤ addr && addr + size ≤ r.base + r.size && addr + size ≤ 2 ^ 48 && (!write || r.writable)`.
  This only adds faults (conservative). Change `Spec.Ptr` to `p.toNat + n ≤ 2 ^ 48` to match.
* `store`: also require `m.regions.all fun r => r.writable || r.base + r.size ≤ addr || addr + n ≤ r.base`
  (no read-only region overlaps the store), or require pairwise-disjoint regions in `DataLoaded`.

### F6 (E1): `cmd/janus/binary.go`

In `loadBinary`, reject `f.Type == elf.ET_DYN` ("PIE binaries are not supported: the model uses
link-time addresses"). Alternatively accept it, state in SOUNDNESS.md that addresses are
link-time, and in `collectData` refuse any copied range that a `.rela*` entry targets.

## Fixes applied

All six proposed fixes are implemented (F7, for the later finding R1, is described in its own section below). `audit/run-all.sh` output on `agent/deps-ci`:

```
A1_instance                  blocked  Invalid: The audit rejected the proof: the statement uses the proof-local evilMul, whose type is the class HMul (a disguised instance)
A3_initialize                blocked  Invalid: The audit rejected the proof: the statement does not mention Extracted.program or Extracted.entry, so it says nothing about the extracted code
A6_eval_io                   blocked  Invalid: Lean rejected the proof audit/attacks/A6_eval_io.lean.   (read-only file system)
A9_namespace_shadow          blocked  Invalid: The audit rejected the proof: a non-trusted module declares Proof.Extracted.program._closed_0, whose name shadows the Extracted namespace
A5_skipkernel                blocked  Invalid: The audit rejected the proof: the statement does not mention Extracted.program or Extracted.entry, so it says nothing about the extracted code
A7_private_shadow            blocked  Invalid: Lean rejected the proof audit/attacks/A7_private_shadow.lean.
A10_exit                     blocked  Invalid: the proof does not define Proof.correctness
A2_unexpander                Verified-honest Verified: Proof.correctness
A4_unexpand_janus            Verified-honest Verified: Proof.correctness
A8_classic.t1/t3/t4          blocked  Invalid: The audit rejected the proof: the statement does not mention Extracted.program or Extracted.entry, …
B1_neverpanics_fault         blocked  Invalid: Lean rejected the proof audit/specs/B1_neverpanics_fault.lean.
B1_refuted                   Verified Verified: Proof.correctness
B2_exit_sentinel             blocked  rejected (does not compile)
B2_refuted                   ok       'br_zero_not_ensures' depends on axioms: [propext, Quot.sound]
control:Add/Add256/Get_witness Verified Verified: Proof.correctness
C1_shadow_library            blocked  Invalid: a second Extracted.olean is on the search path (…), which could shadow the checked one.
C2_toctou_swap               mitigated Verified: Proof.correctness
Model.lean: all decide controls pass, including M1-M3 now faulting (blocked by F5)
```

| Fix | Findings | Implemented in |
|-----|----------|----------------|
| F1 | A3, A6, C1, C2 | `cmd/janus/sandbox.go` (bubblewrap/unshare sandbox, refusal without one unless `--unsafe-no-sandbox`, mode recorded in `verified.json`); `cmd/janus/leanjob.go` (direct `lean` with a private, ordered `LEAN_PATH`, `noForeignModule`, `JanusTrusted` copy, nonce marker, `auditScript`); `cmd/janus/verify.go` (private trusted and work dirs under the cache run base, olean hash-binding and re-checks, sandboxed leanchecker replay, stale-input checks); `Janus/Tools/Audit.lean` (`importModules` without initializers, `checkIdentity` of `Extracted` against `JanusTrusted`); `cmd/janus/consumer.go` (the same for `--proof-root` packages) |
| F2 | A1, A2, A4, A9 | `Janus/Tools/Audit.lean` (trusted-module constant rule, plain proof-local defs only, class-valued defs rejected, no `Extracted`-component names, statement must mention `Extracted.program`/`entry`, clean-environment `pp.fullNames` print with disclosed `definitions`); `cmd/janus/verify.go` (`theoremNameRE` ASCII-only, E2) |
| F3 | B1 | `Janus/GoABI.lean` (`NeverPanics` also requires every non-fuel error to be absent) |
| F4 | B2 | `Janus/GoABI.lean` (`Ensures` over every `RetAddr`), `Janus/Program.lean` (`withExit`) |
| F5 | M1, M2, M3 | `Janus/Arm64/State.lean` (`Memory.accessible`: region end ≤ `2^48`, no read-only overlap for stores) |
| F6 | E1 | `cmd/janus/binary.go` (`ET_DYN` rejected; test `TestRejectPIE` in `cmd/janus/hardening_test.go`) |
| F7 | R1 | `cmd/janus/replay.go` (framework olean pins, `closureCheck`, content-keyed replay cache, chunked `leanchecker` replay of the whole non-core closure, `--replay-fresh`); `cmd/janus/sandbox.go` (`commandOverlay`: protected trees re-mounted read-only over writable ones, bubblewrap and `unshare`); `cmd/janus/consumer.go` (workspace framework build re-seeded from the trusted base when it differs from the pins, trusted `Extracted`/`JanusTrusted` build before any untrusted code, `janus/` read-only to the Lake build, pins re-checked after the build, every `lake query`, the audit and the replay); `cmd/janus/verify.go` (the same pins and closure replay for single-file proofs, audit in its own directory with the proof build read-only); `Janus/Tools/Audit.lean` (`imports`: the import graph of every non-core module, for the cache keys); tests `cmd/janus/replay_test.go` |

`audit/specs/B1_neverpanics_fault.lean` and `B1_refuted.lean` now take the entry address from
`Extracted.entry` instead of a literal, so they stay valid when the example binary changes.

## R1 (Critical, follow-up): compiled framework modules were not bound to the framework

Found after F1–F6 (2026-10-23, `agent/replay`); fixed by F7. Every later step trusts the compiled
framework modules (`.olean`): the proof and the consumer modules are elaborated against them, the
auditor *is* one (`Janus.Tools.Audit`), the statement is printed from them, and `leanchecker`
checks a module against its imports *as loaded from their oleans*. Nothing tied those oleans to
the framework sources.

* **The consumer workspace's framework build was writable by the untrusted build.** `janus verify
  --proof-root` copies the trusted framework build into `<workspace>/janus/.lake/build` and runs
  the consumer's `lake build` in the sandbox with the whole workspace writable. A `lakefile.lean`
  (or a dependency's lakefile) runs arbitrary IO while Lake elaborates it, so it could replace any
  framework module. Reproduced with the pre-fix verifier (`6fbaeba`) under bubblewrap, using
  `audit/attacks/R1_pkg` (`JANUS_R1_MODE` selects the variant):
  * `ensures`: the lakefile recompiles `Janus/GoABI.lean` with `Ensures … := True` over
    `Janus/GoABI.olean`; `R1.Ensures.claim : Ensures Extracted.program Extracted.entry [x, y]
    (fun _ => True) (fun _ s' => s'.regs 0 = 42)` (Add returns 42) is proved by `trivial` and was
    reported **Verified**, axioms `(none)`, kernel replay passed;
  * `auditor`: the lakefile recompiles `Janus.Tools.Audit` so that it prints an all-clear record;
    `theorem R1.False.claim : False := sorry` was reported **Verified**, axioms `(none)`,
    statement `R1.False.claim : Extracted.entry = Extracted.entry`.
* **The replay could not catch it.** The earlier note that leanchecker replayed only the root
  module `Janus` is not accurate: `leanchecker Janus` replays every module *whose name starts
  with* `Janus` that it finds on `LEAN_PATH` (its targets are name prefixes), so all framework
  modules were replayed. But a replay checks that a module is well-typed, not that it is the
  module its source describes: an olean compiled from a modified source replays fine (the
  `ensures` attack passed it). `JanusTrusted` was not replayed at all, and modules were not
  checked to come from where they should (a `Janus.*` olean without a framework source counted as
  framework for the auditor's trusted-module rule).
* In the single-file path the framework build was already read-only to the sandbox, so these
  attacks needed `--unsafe-no-sandbox` there.

**Fix (F7), in depth:**

1. **Read-only**: in a consumer workspace the `janus/` package is mounted read-only over the
   writable workspace for every sandboxed process (bubblewrap `--ro-bind` after the writable binds;
   the `unshare` fallback remounts it read-only and aborts if it cannot). A mount point cannot be
   renamed or removed from inside, so the tree cannot be swapped either. `Extracted` and
   `JanusTrusted` are now built by `janus` (Lake on our lakefile, unsandboxed) before any untrusted
   code runs. The workspace's framework build is replaced from the trusted base whenever it
   differs from the pins. In the single-file path the framework and trusted directories are
   re-mounted read-only too, and the audit and replay run with the proof build read-only.
2. **Pins**: the SHA-256 of every module-data file (`.olean`, `.olean.server`, `.olean.private`,
   `.ir`) of the framework build — only `Janus.*` modules with a framework source — and of the
   trusted `Extracted`/`JanusTrusted` is recorded after the trusted build and re-verified after
   every untrusted step (proof compile, Lake build, each `lake query`), after the audit and after
   the replay. Untrusted outputs (consumer and dependency libraries, the proof's work dir) are
   pinned once final. A modified, missing or unexpected module is `Invalid` (`framework
   integrity`) and named in the message.
3. **Closure check and full replay**: every module of the audited environment must resolve from
   its home (core from the toolchain, `Janus.*` from the pinned framework build and only framework
   modules, `Extracted`/`JanusTrusted` from the trusted directory); then every non-core module of
   the closure is kernel-replayed (`Janus.*`, `Extracted`, `JanusTrusted`, consumer, dependency
   modules), in chunks of 32 modules per `leanchecker` run. Passing replays are cached in
   `v1/replay` (never writable by the sandbox), keyed by the toolchain version, the module's bytes
   and, recursively, its imports' keys; off with `--fresh` and without a sandbox.
   `--replay-fresh` adds `leanchecker --fresh` on the theorem module (core included; ≈140 s for a
   closure importing `Lean`), the most rigorous mode leanchecker has; it is not the default because
   of that cost and because Init/Std/Lean ship read-only with the toolchain.

Regressions (`audit/run-all.sh`, rows `R1*`; Go tests `TestR1FrameworkTamper`,
`TestR1ForgedFrameworkLemma`, `TestPins`, `TestClosureCheck`, `TestReplayPlanKeys`,
`TestProtectedOverlay` in `cmd/janus/replay_test.go`):

```
                             pre-fix (6fbaeba, bubblewrap)   after F7
R1a_ensures                  Verified: R1.Ensures.claim      Invalid: Lean rejected the proof module R1/Ensures.lean   [proof checking: the write hit the read-only framework, so Ensures is the real one]
R1a_ensures_nosandbox        —                               Invalid: the Janus framework build … changed after the consumer's Lake build … modified Janus/GoABI.olean   [framework integrity]
R1a_auditor                  Verified: R1.False.claim        Invalid: The audit rejected the proof: the statement does not mention Extracted.program …   [statement identity: the genuine auditor ran]
R1a_auditor_nosandbox        —                               Invalid: … modified Janus/Tools/Audit.olean   [framework integrity]
R1b_corrupt                  Invalid (proof checking)        Invalid: Lean rejected the proof module R1/Ensures.lean   [proof checking]
R1b_corrupt_nosandbox        —                               Invalid: … modified Janus/GoABI.olean   [framework integrity]
R1b_forged_lemma             Invalid (kernel replay)         Invalid: Kernel replay rejected the environment: leanchecker found a problem in Janus.GoABI … 'Janus.GoABI.forged'   [kernel replay]
R1c_inject                   Invalid (proof checking)        Invalid: Lean rejected the proof module R1/Inject.lean   [proof checking]
R1c_inject_nosandbox         —                               Invalid: … unexpected Janus/Backdoor.olean   [framework integrity]
R1c_inject_dep               —                               Invalid: the dependency r1dep defines the module Janus.Backdoor, whose root Janus is reserved …   [module identity]
R1c_inject_dep_nosandbox     —                               Invalid: … unexpected Janus/Backdoor.olean   [framework integrity]
R1_proof_overwrite           —                               Verified: Proof.correctness   [mitigated: the proof's write to the framework build fails; the theorem is honest]
R1_proof_overwrite_nosandbox —                               Invalid: the Janus framework build … changed after the proof compile … modified Janus/GoABI.olean   [framework integrity]
```

**Cost** (single-file `janus verify artifacts/Max --proof examples/proofs/Max.lean`, warm framework
cache, three alternating runs each on a shared 48-core host): pre-fix 25.5–26.4 s; after F7 with an
empty replay cache (the first verification per framework version replays all 29 closure modules in
one `leanchecker` run) 25.3–27.5 s; after F7 with the cache warm 16.1–16.8 s. The pre-fix verifier
spent about 10 s of every run replaying the unchanged framework (`leanchecker Janus` replays all of
`Janus.*`); now only modules whose bytes, or whose imports' bytes, changed are replayed (a new
proof: just the proof module). `scripts/verify-examples.sh` (14 examples): 422–548 s summed before,
320 s after (warm), under load that varied between runs.

The layers also back each other up. Re-running the unsandboxed rows in the same workspaces
without changing the lakefiles (so Lake did not elaborate them again) showed it: the framework
build had been re-seeded from the trusted base, but Lake still considered the consumer's
`R1/Ensures.olean`, compiled against the forged `GoABI` in the previous run, up to date, since
Lake's traces record the hashes of the framework sources and outputs it last wrote, not the bytes
now on disk. The audit then passed (printing the genuine `Ensures`), and the kernel replay of
`R1.Ensures` against the genuine framework rejected it. Since then, when a workspace's
framework build has to be re-seeded, `janus` also discards that workspace's consumer and
dependency builds (and does not seed them from a sibling), and `run-all.sh` gives each run's
lakefiles a new hash so every row exercises its attack.

`R1b_forged_lemma` is the case only the replay can catch: the forged olean is in a `--janus-root`
copy, which is the build the pins are taken from (and the old prefix replay caught it as well).
All earlier rows of `audit/run-all.sh` still print their expected result.

## Round 2 (2026-10-23)

A second, independent adversarial review attacked the auditor's constant/instance rules, the
dependency/replay/sandbox machinery and the newest model semantics. The full report is
[docs/AUDIT-ROUND2.md](AUDIT-ROUND2.md); its attack files are in `audit/round2/`
(`attacks/`, `controls/`, `model/`, `amd64/`) and `audit/round2/run-round2.sh` reproduces the
verifier findings and exits 1 if a fixed one regresses. The CRITICAL-1 and U1 rows are also in
`audit/run-all.sh` (`R2.*`).

| # | Finding | Severity | Status |
|---|---|---|---|
| CRITICAL-1 | An instance written inline in the statement (`@HMul.hMul _ _ _ ⟨fun a b => a + b⟩ x y`) is hidden by the default pretty-printer: against `example.com/basic.Add` the statement printed `… = x * y` (S1c) or `x - y` (S1) and verified, every constant being Lean core. | critical | **fixed** (below). `run-round2.sh` and run-all `R2.S1*`: `Invalid`, `Stage: statement identity` |
| U1 | The `unshare` fallback remounted only `/` read-only: `/tmp`, `/dev/shm`, `/boot`, `/run/user/…` stayed writable on the host (the trusted cache was already safe). | low (confinement) | **fixed**: every mount is remounted read-only (keeping its locked flags), `/tmp` and `/dev/shm` are private tmpfs mounts, binds under the host `/tmp` are re-exposed from the hidden original; if a mount cannot be made read-only the fallback is refused (install bubblewrap). The self-test checks `/tmp` and `/dev/shm` are private. `JANUS_SANDBOX=unshare` forces the fallback; run-all `R2.U1*` and `TestUnshareFallback*` |
| M1, deps, replay cache, verify-batch, audit marker | Module-system proof, dependency pinning, cache poisoning, cross-request influence, record spoofing | n/a | blocked (no change) |
| LOW-3 | arm64 feature list missing FP/AdvSIMD; the `arm64HasATOMICS` precondition trusts the kernel's HWCAP report | low (docs) | **documented** in [SOUNDNESS.md](SOUNDNESS.md) ("Atomics, exclusives and system registers") |
| LOW-4 | `DCZID_EL0` assumed identical on all cores | low (docs) | **documented** in SOUNDNESS.md |
| Residual | the auditor and `leanchecker` load untrusted `.olean` bytes; the loader does not validate them | TCB | **documented** in SOUNDNESS.md (trusted computing base, item 4) |
| MEDIUM-1 | amd64: the direction flag is not in the state; a verified *mid-function* theorem says memmove's backward `REP MOVSQ` copies forward (call theorems unaffected) | medium | open (amd64 model) |
| LOW-1 | amd64: LOCK accesses that straddle a cache line (SIGBUS with `split_lock_detect=fatal`) | low–medium | open (amd64 model/preconditions) |
| LOW-2 | amd64: 64-bit BSF/BSR of zero follows AMD | low | open (amd64 model) |

**Fix for CRITICAL-1 (`Janus/Tools/Audit.lean`), in depth.** The guarantee is the printed
statement, so the auditor now checks that the text means what the kernel proved:

1. **Instance arguments** (`checkInstArgs`): the statement's type is walked; at every
   application, the head's binder info (`getFunInfoNArgs`) gives the instance-implicit
   positions, and each argument there must be, up to unfolding reducible definitions and
   `whnfCore`, an application of a registered instance of the clean trusted environment (core,
   `Janus`, `Extracted`; plus `scoped` instances declared in trusted modules) — the head is
   tested before unfolding, since instances themselves unfold to structure literals — or a
   local variable bound by an instance binder of the theorem. Structure-instance literals,
   anonymous constructors, lambdas, `let`-bound values, `dite` terms and proof-local or
   dependency definitions are rejected ("inline instance"). Dependencies contribute no
   instances (their instances are not allowed in statements at all).
2. **Round-trip** (`printFaithful`/`roundTrip`): the printed signature is parsed back
   (`ident declSig`) and elaborated in the same clean environment with the same options
   (`autoImplicit` off, `errToSorry` off, a heartbeat budget); any parse or elaboration error,
   remaining metavariable or `sorry` rejects. The result must be structurally equal to the
   checked type, or definitionally equal by the elaborator at **default** transparency *and*
   by the kernel's `isDefEq`. Default transparency is sound here: definitionally equal
   propositions are the same proposition to the kernel, so the printed text, read with the
   canonical instances, states exactly what was proved; a planted instance makes the canonical
   reading (real `*`) differ from the checked term (really `+`) and the check fails. To keep
   honest statements printable, coercions are printed with their target type
   (`pp.coercions.types`, `(↑n : Int)`), and if the plain print still reads back differently
   only because of a numeral's type, the statement is printed with `pp.numericTypes`
   (`(5 : BitVec 64)`); a statement that round-trips neither way is rejected ("does not
   round-trip").
3. **Inspection**: `verified.json` has `statementExplicit`, the statement printed with
   `pp.explicit` (every implicit and instance argument shown).

Either check alone rejects every S1 variant (`JanusTests/Audit.lean` tests each separately, and
each accepts honest statements with canonical instances, numerals, `if`, `<`, coercions and
instance binders). All 20 arm64 example theorems (including the SIMD `A64Equal64`/`A64IndexByte`) and the 23 amd64 ones, the consumer examples and the
deps tests still verify (no arm64 example statement needed the coercion or numeral annotations); A2 and A4 stay **verified-honest** (their
clean prints round-trip). Tests: `cmd/janus/round2_test.go` (`TestInlineInstanceRejected`,
`TestRoundTripRejectsAmbiguousPrint`, `TestUnshareFallbackConfinement`,
`TestUnshareFallbackVerifies`).

## ASL corollary forgeries (`janus verify --asl`)

`--asl` derives the verified theorem's corollary about Arm's ASL ([ASL.md](ASL.md#janus-verify---asl-the-corollary-of-a-verified-theorem)).
The corollary module imports the untrusted proof, so its compile runs sandboxed and its result is
re-checked by the trusted auditor (`JanusAudit.runASL`). `audit/asl/attacks/` holds proofs whose
main theorem verifies but which try to forge the corollary; `audit/run-all.sh` runs them with
`JANUS_AUDIT_ASL=1` (rows `ASL.*`), and `TestASLForgeryRejected` in `cmd/janus/asl_test.go`.

| attack | what it tries | result |
|---|---|---|
| X1_shadow_toASL | declares `JanusASL.Proofs.Ensures.toASL` itself | blocked (`ASL corollary`: the corollary module cannot import both) |
| X2_own_toASL | proves a fake "ASL" statement with a proof-local `aslRun`/`Ensures.toASL` and asks `--theorem Proof.correctness_asl` | main theorem verifies, honestly disclosed; ASL blocked (not an `Ensures` theorem) |
| X3_plant_words | plants `JanusASLWords.covered : True` | blocked (`ASL corollary`: import clash with the trusted coverage module) |
| X4_plant_corollary | declares `JanusASLCorollary.correctness_asl : True` | blocked (`ASL corollary`: name taken) |
| X5_elab_override | its own higher-priority `janus_asl_corollary` command adds `True` under the corollary's name | blocked (`ASL audit`: type is not the derivation from the verified theorem) |
| X6_other_program | theorem about a `p` only assumed equal to `Extracted.program` | blocked (not about `Extracted.program` itself) |
| X7_reserved_name | a non-clashing look-alike under a reserved root (`JanusASL.Proofs.LinuxEL0Config'`) | blocked (`ASL audit`: reserved namespace rule) |
| consumer `JanusASL.Fake` | a consumer module under the `JanusASL` root | blocked (`ASL module identity`; `TestASLConsumer`) |

## Files

* `audit/run-all.sh`: reproduces every row (`BROKEN` rows print `Verified`, blocked rows `Invalid`), extracting its own `audit/work/{Add,Add256,Get}`; it marks a row `<-- BROKEN` and exits 1 if a blocked row verifies or a control does not.
* `audit/attacks/`: A1–A10, C1 (`C1_fake_Extracted.lean`, `C1_proof.lean`), C2 (`C2_toctou_swap.sh`), R1 (`R1_pkg/` consumer package whose lakefile tampers with the framework build, `R1_dep/` a dependency that plants `Janus.Backdoor`, `R1_forged_lemma.lean` + `R1_forged_proof.lean`, `R1_proof_overwrite.lean`).
* `audit/specs/`: B1 (`B1_neverpanics_fault.lean`, verify against Add256), B2 (`B2_exit_sentinel.lean`, `lake env lean`).
* `audit/controls/`: Add, Add256 and Get witnesses (verify against the respective artifact).
* `audit/model/`: `Model.lean` (M1–M3 and the OK controls), `decoder_vs_objdump.sh`, `gen_words.py`, `objcmp.py`.
* `audit/probe/`: `P.lean` and `Q.lean` (shows that `initialize` and `#eval` run).
* `audit/bin/`: `janus` (rebuilt by `run-all.sh` from the current tree), `janus-head` (working tree with the `verify.go` rewrite).
* `audit/work/`: scratch artifact copies (regenerated by `run-all.sh`).
* `audit/round2/`: the round-2 attacks (`attacks/S1*` inline instances, `M1_module_system`, `U1*` unshare fallback), positive controls, arm64/amd64 model probes and `run-round2.sh`; see [AUDIT-ROUND2.md](AUDIT-ROUND2.md).
