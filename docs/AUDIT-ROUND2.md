# Janus soundness audit — round 2

> **Status (agent/audit-fix):** CRITICAL-1 and U1 are fixed, LOW-3/LOW-4 and the olean-loader
> residual are documented in [SOUNDNESS.md](SOUNDNESS.md); MEDIUM-1, LOW-1 and LOW-2 (amd64
> model) are open. See the per-finding table in [AUDIT.md](AUDIT.md#round-2-2026-10-23). The
> report below is kept as written.

Second independent adversarial review of the claim: *if `janus verify` (or `verify-batch`, or
consumer `--proof-root` verification) prints `Verified`, the printed theorem holds for the actual
bytes of this binary under the documented semantics.*

Round 1 (`docs/AUDIT.md`) and the later F7 review fixed forged audits, pretty-printer/unexpander
tricks, sandbox and replay holes, framework-olean rebuilding, and model issues up to the
atomics/DC-ZVA coverage. This round attacks the auditor's constant/instance rules, the new
dependency/replay/sandbox machinery, and the newest model semantics.

Attacks live in `audit/round2/` (`attacks/`, `controls/`, `model/`, `amd64/`) with
`run-round2.sh`. Severity: **critical** = a false/misleading theorem prints `Verified`;
**high** = a wrong value for a valid instruction in the trusted model; **medium** = an accepted
encoding hardware rejects (matters only if a fixed binary could rely on it); **low** = hygiene.

---

## CRITICAL-1 (BROKEN): a non-canonical instance written *inline in the statement* makes the printed theorem lie

**Status: BROKEN.** Reproduced against the shipped `example.com/basic.Add` (which computes
`x + y`). Files: `audit/round2/attacks/S1_inline_instance.lean`, `S1c_mul.lean`.

### What happens

The statement's post-condition is written with an explicit, anonymous instance argument:

```lean
(fun _ s' => s'.regs 0 =
  @HMul.hMul (BitVec 64) (BitVec 64) (BitVec 64) ⟨fun a b => a + b⟩ x y)   -- S1c
```

`⟨fun a b => a + b⟩` is `HMul.mk` whose operation is **addition**. So the term is kernel-defeq to
`x + y`, the real `Add` proof closes, every check passes, and `janus verify` prints:

```
Verified: Proof.correctness
  Statement:
    … fun x_1 s' => s'.regs 0 = x * y
```

The binary adds; the printed, audited guarantee says it **multiplies**. `S1_inline_instance.lean`
is the same with `HSub` (`⟨fun a b => a + b⟩`), printing `s'.regs 0 = x - y`. Both print
`Verified`. A reader of the statement — the entire basis of the guarantee — is deceived.

### Why every existing defence misses it

* The axiom audit, `Extracted` identity and kernel replay all pass: the term is honestly
  `x + y`, the proof is real, nothing is forged.
* The A1 / A2 / A4 fixes target **named** proof-local or dependency *instances* and
  proof-side *unexpanders/delaborators*. Here there is **no named instance and no proof-local
  definition at all** — the misleading instance is an anonymous `Structure.mk` literal sitting
  directly in the theorem *type*. `JanusAudit` only inspects `ci.type.getUsedConstants`
  (`HMul.hMul`, `HMul.mk`, `BitVec`, … all trusted core) and never looks at the *values* of
  instance-implicit arguments.
* `cleanEnvAndPrint` pretty-prints the **true** type in the trusted environment, but the lie is
  in the type itself: Lean's built-in delaborator for `HMul.hMul`/`HSub.hSub` renders `a * b` /
  `a - b` from the *head symbol* and **suppresses the instance argument** under default options.
  Confirmed directly: `pp.all` shows the real term is `@HMul.hMul … (@HMul.mk … fun a b => a + b) x y`,
  while default pp (what the auditor uses, `Options.empty.setBool pp.fullNames true`) prints
  `x * y`. `:= rfl` proves the whole thing defeq to `x + y`.

This is **not** a disabled-unexpander situation like A2/A4 (where the clean print shows the
honest statement). The clean, trusted printer faithfully prints a type whose *notation does not
determine its semantics*, because a caller-supplied instance overrides the canonical one.

### Impact

Breaks the central claim outright, on the default single-file path and (same auditor) on the
consumer and batch paths. Any Janus theorem can be made to print an arbitrary wrong operation
(`+`↔`-`↔`*`, `≤`↔`<`, `=`↔`≠` via `Decidable`/`BEq`, `OfNat`, coercions `↑`, …) while remaining
a true, fully-checked theorem about the real bytes. The published statement is worthless as a
guarantee until this is closed.

### Proposed fix

The guarantee is "the *printed* statement holds", so the auditor must enforce that the printed
text means what the kernel proved. Two options, in order of preference:

1. **Round-trip the printed statement (recommended).** After `cleanEnvAndPrint` produces the
   signature string, re-parse and re-elaborate it in the same clean environment (which has only
   canonical instances and the type-only dependency stubs) and require the result to be
   `isDefEq` to the real `ci.type`. When the real type carries a non-canonical instance, the
   re-elaboration binds the *canonical* instance (real `*`), which is not defeq to the planted
   `+`, so the audit fails. This also closes any future pp-hiding (coercions, `OfNat`, numeric
   literals) in one check. Report the re-elaborated, confirmed statement, not the raw pp.
   Cost: one extra elaboration of the signature; dependency stubs are already present as axioms,
   so parse/elaborate succeeds and defeq is essentially syntactic.

2. **Reject non-canonical instance arguments structurally.** Walk `ci.type`; for every
   application, use the function's type to locate `instImplicit` argument positions, and for each
   such argument require its head to be a constant that is a registered instance (an
   `instance`/`default_instance`, or the field projections thereof) — rejecting bare
   `Structure.mk`/`fun`/`fvar` instance terms with a message like the existing
   "state the operation by name". Lighter (no re-elaboration) but must enumerate instance
   positions correctly and still misses non-instance pp-hiding, so prefer (1).

A reviewer-facing mitigation until fixed: `janus explain`/`verify` should additionally print the
statement with `pp.all` (or at least `pp.explicit`) so instance arguments are visible; this is
ugly but makes the lie detectable.

---

## Blocked / correct (verifier & auditor)

* **M1 — Lean module-system proof (`module` / `public import`).** `audit/round2/attacks/M1_module_system.lean`.
  A `module`-mode proof whose theorem body lives in the `.olean.private` part could, in
  principle, hide the proof term from the auditor's `importModules (loadExts := false)`. Blocked
  earlier than that: `Extracted` is a plain (non-`module`) module, so Lean refuses
  `cannot import non-module Extracted from module`, and the proof does not compile. (The audit
  did key its replay on `.olean.private` bytes anyway — see `replay.go` `moduleDataExts` —, so
  even a hypothetical module-mode proof is replayed over its private part.)

* **Dependency pinning (`deps.go`).** `.git` must exist (`os.Lstat`); non-blob tree entries
  (submodules/gitlinks) are skipped, symlinked *source* files are rejected, every copied file is
  re-hashed to its git blob id (SHA-1 or SHA-256 by id length), `subDir` is cleaned and
  `..`-escapes rejected, a direct dep must be asked for by the full revision in the lakefile
  (not only resolved in the manifest), both-lakefiles and no-lakefile are rejected, and
  `checkGitState` is re-run at `recheck`. `git` runs with hooks/fsmonitor/global config disabled
  and sandboxed. No break found; case-collision and alternate-`.git`-file tricks are defeated by
  the per-file blob-id check (the working file must hash to the pinned tree's blob).

* **Replay cache & sandbox writability.** The replay cache lives under `cacheRoot()/v1/replay`,
  which every sandboxed process sees **read-only** (`--ro-bind $base`), and `replayCacheOK` turns
  the cache off entirely in `--unsafe-no-sandbox` mode, so a sandboxed proof cannot poison it.
  Cache keys bind the toolchain version, each module's `.olean`/`.server`/`.private` bytes and,
  recursively, the keys of its imports, so "a module whose import changed" gets a different key.
  Framework/trusted/proof/dependency oleans are additionally pinned by SHA-256 and re-checked
  after every untrusted step, the audit and the replay. No break found.

* **U1 — `unshare` fallback writability (blocked; residual low).**
  `audit/round2/attacks/U1_unshare_cache_write.lean` (run with `bwrap` hidden from `PATH`). The
  fallback remounts only `/` read-only; I confirmed that other mounts (`/tmp`, `/dev/shm`,
  `/boot`, `/run/user/0` on this host) stay writable inside it and the writes land on the host.
  Escalation to the trusted cache is blocked both ways: with the cache on `/`, the proof's write
  to `$JANUS_CACHE_DIR/v1/replay` fails with `read-only file system`; with the cache on a
  separate mount (`JANUS_CACHE_DIR` under `/tmp`), the sandbox self-test's "denied" probe lands
  on that writable mount, so `detectSandbox` refuses (`Stage: sandbox`). The framework build and
  the trusted dirs are additionally bound read-only with `set -e` (`protected`), so a
  `--janus-root` on another mount is safe too. Residual: under the fallback a proof can still
  write host `/tmp`, `/dev/shm` etc. (confinement, not the verdict), contrary to the documented
  "private /tmp". Fix: in the `unshare` script, `mount -t tmpfs tmpfs /tmp` (and `/dev/shm`) and
  remount every other mount read-only (`findmnt -rno TARGET` loop with `remount,ro,bind`).

* **verify-batch request sharing (blocked).** Requests with byte-identical extractions share one
  Lake build, but each gets its own audit (fresh nonce marker, own module), its own
  `closureCheck` and replay of its own closure, and pins are re-checked after the build, every
  `lake query`, every audit and the replay. `checkModuleLayout` forbids duplicate module names and
  shared roots, so one request's modules can enter another's verdict only if that theorem imports
  them, and then they are audited and replayed as part of it. Different `proofRoot`s get separate
  snapshots/workspaces. No cross-request influence found. (CRITICAL-1 applies here too: same
  auditor.)

* **Audit output spoofing (blocked).** The record is found by a per-run random marker passed in
  the generated `Audit.lean`; the audit process imports the proof with `loadExts := false` and
  without `enableInitializersExecution`, so no proof code runs there and nothing untrusted can
  print the marker. The marker never exists while the proof compiles.

* **Residual trust assumption, not attacked.** The auditor and `leanchecker` load untrusted
  `.olean` bytes (written by the sandboxed compile). Lean's olean loader does not validate
  compacted-region structure, so robustness of the loader against malformed oleans is part of
  the TCB. I did not attempt to build malformed oleans; I record it so the docs can state it.

---

## Spec vocabulary — positive controls (non-vacuity)

Constructed concrete witness states proving the preconditions of the newest examples are
satisfiable (so the theorems are not vacuous), each instantiating the shipped `correctness` to a
concrete `Returns`, elaborated with only `propext`/`Quot.sound`/`Classical.choice` (no
`native_decide`):

* `audit/round2/controls/AtomicAdd_witness.lean` — LSE flag byte set, 8-aligned writable `p`
  disjoint from `runtime.arm64HasATOMICS`; `Proof.correctness` fires. ✓
* `audit/round2/controls/CopyBlock_witness.lean` — readable `g.stackguard0` below `SP`, 56-byte
  writable stack window, 128-byte writable `dst`, 128-byte readable `src`, all disjoint;
  `Proof.correctness` fires. ✓

(These complement round-1 `audit/controls/` for Add/Add256/Get.)

---

## Model-level findings

arm64: `audit/round2/model/` (audited on `agent/arm64cov2` at accb078, which adds
`Janus/Arm64/Vector.lean`; see its `README.txt`). amd64: `audit/round2/amd64/` (committed tree
8bf7610). No case was found where either model computes a wrong value for a valid instruction.

### MEDIUM-1 (BROKEN under a literal reading): amd64 direction flag not in the state

`audit/round2/amd64/controls/DFMemmove.lean`, theorem
`DFRepro.memmove_backward_rep_copies_forward`, against the amd64 `CopyBlock` extraction
(`runtime.memmove`). I re-ran it: `janus verify … --theorem DFRepro.memmove_backward_rep_copies_forward`
prints **Verified** (axioms `Quot.sound`, `propext`). The theorem says that running from the
`REP MOVSQ` at `0x47d6e9`, the instruction right after `STD` (`fd`) on memmove's backward path,
copies **forward** (`RSI += 16`). On hardware every state at that PC has DF = 1 and copies
backward (host probe `host/probe.c` case 5).

Why: `Amd64.State` has no DF; `MOVS`/`STOS` always step forward. DF = 0 is a documented CPU
assumption (AMD64.md), argued from "STD is undecodable, so DF is 0 in every reachable state".
That holds for call theorems (`Ensures`/`CallSetup`), so no shipped `correctness` theorem is
affected. But `verify` accepts any statement mentioning `Extracted`, including statements about
arbitrary mid-function states (as exported loop lemmas such as `ClearWords.clear_loop`,
`CopyWords.loop` already are), and those can be false on hardware.

Fix: add `df : Bool` to `Amd64.State`, `df = false` to `CallSetup`, make `MOVS`/`STOS` fault (or
step backward) when `df`, and decode `CLD`/`STD` as `df := false`/`true`. The in-progress
`/srv/janus-amd64cov2` decodes `CLD` as a plain NOP, which is only sound under the implicit
assumption; it should set `df := false`. (RFLAGS.AC is implicit in the same way, documented;
Go never sets it.)

### LOW-1: amd64 LOCK accesses that straddle a cache line

`f0 48 0f c1 18` (LOCK XADDQ, AtomicAdd), LOCK CMPXCHGQ (AtomicMax). The model accepts a locked
access at any address. With `split_lock_detect=fatal` Linux sends SIGBUS. In the default `warn`
mode the result is correct but the trap fires; `host/splitlock.c` shows the dmesg trap on this
host. The amd64 AtomicAdd/AtomicMax preconditions don't require alignment;
`amd64/controls/AtomicAdd_witness.lean` (namespace `Split`) instantiates the theorem at
`p = 0x203C`. Fix: add `p.toNat % 8 = 0` to both preconditions (Go aligns `*uint64`), or fault
on misaligned LOCK/XCHG-mem, or document "split-lock detection not fatal".

### LOW-2: amd64 64-bit BSF/BSR of zero

`48 0f bc c1`: with a zero source the model leaves the destination unchanged (AMD-documented,
Intel "undefined"). That contradicts AMD64.md's stated vendor-neutrality policy, which already
faults for 16/32-bit. No shipped theorem depends on it. Fix: fault with `undefinedResult`, or
document the exception.

### LOW-3: arm64 feature list incomplete; HWCAP trust

LSE/LRCPC/AES (`0xf8e10002` LDADDAL, `0xc8fbfc01` CASAL, `0xf8bfc002` LDAPR, `0x4e284820` AESE)
decode unconditionally. I decoded all 678 words of every shipped arm64 example. LSE appears only
in AtomicAdd/AtomicMax, behind `runtime.arm64HasATOMICS` with the flag in the precondition. No
example uses LRCPC or AES. FP/AdvSIMD, used unguarded by `memequal`/`IndexByte` (A64Equal64,
A64IndexByte on arm64cov2), is formally optional but missing from SOUNDNESS's feature list. The
flag precondition trusts the kernel's HWCAP (Go issue 28431: a heterogeneous-core kernel
over-reported atomics). Fix: documentation (add FEAT_AdvSIMD/FP; state the HWCAP assumption).

### LOW-4: arm64 DCZID_EL0 assumed identical on all cores

`State.dczid` is constant per run. It is IMPLEMENTATION DEFINED per core, so a thread
migrating between Go's cached `block_size` and `DC ZVA` on a mixed system would zero a different
block. ClearWords holds only where all cores agree; I know of no shipping hardware where they
differ. Fix: documentation.

### Informational

* arm64 reserved DCZID.BS 10..15 are accepted (`4 * 2^(dczid % 16)` zeroes up to 128 KiB;
  the ARM ARM caps BS at 9). These states can't occur on hardware, so they only add vacuous
  cases. BS is 4 bits, so "BS = 31" doesn't exist: `dczid = 31` is DZP = 1, which traps.
  Optional: `min 9`.
* amd64 feature-dependent encodings (`F3 0F BD` is BSR without LZCNT, `F3 0F BC` is BSF without
  BMI1, POPCNT, CMPXCHG16B) are assumed, as documented. AMD64.md wrongly attributes LZCNT to BMI1
  (it is ABM/LZCNT). No example uses them.

### Checked and correct (model)

* arm64 decoder: 48 kernel-checked reserved-encoding facts (`model/M1_decode_reserved.lean`,
  each cross-checked with objdump). They cover LDAR/STLR Rs/Rt2, LDLAR, CASP odd/Rt2, LDAPR
  fields, store-exclusives rejected, MSR TPIDR_EL0, other DC ops, AES size/opcode, size:Q=110,
  EXT Q=0 imm4<3>, DUP/UMOV/SMOV/INS imm5/Q, MOVI op=1 cmode=1111 Q=0, FP16 FMOV, shift-imm
  immh/Q, LD1 single/replicate, LDR scale, LDP Rt==Rt2, LDR literal opc=11. Plus a 1.5M-word
  random sweep: 365,909 accepted, 0 that objdump calls invalid. PRFM reserved prfops are hints
  (correct).
* arm64 values (`model/M2_values.lean`, 27 checks):
  - SMAX/SMIN at element width with zero-extended old value; W results clear the upper half.
  - Rt=31 ST<op> discards the result; CAS width; CASP pair order; LDAPR zero-extension.
  - Q=0 SIMD writes zero bits 127:64, while INS/XTN2/SHRN2 keep the other half.
  - SMOV/UMOV extension, little-endian lanes, LD1 register wrap and SP/Rm=31 handling.
  - By reading against the ASL: MOVI expansion, EXT/TBL/TBX, AES ShiftRows/MixColumns, DC ZVA
    alignment, permission and DZP behaviour.
  - Unaligned LDAR faults (conservative vs FEAT_LSE2); CAS on read-only memory faults (matches
    the ASL).
* amd64 (`amd64/Probe.lean`, `ExecProbe.lean`, cross-checked on the host CPU):
  - Rejected: REPNE/67/FS/GS/segment prefixes on string ops, CMPS/LODS/SCAS/STD/CLD/POPF, F3
    on non-string ops, LOCK on every non-lockable form, VEX, MOVNT*, CPUID/RDTSC.
  - REP with RCX = 0: no memory access, flags untouched. REP with 66/REX.W uses the full RCX.
    Overlapping forward MOVSB is sequential. A fault partway through is a fault.
  - CMPXCHG32: RAX untouched on success, zero-extended on failure, write-back on failure.
    CMPXCHG8B/16B (16B alignment fault), XADD, XCHG-mem and LOCK ALU flags are correct.
  - MOVAPS/MOVDQA/XORPS-mem alignment faults; MOVQ/MOVD zeroing.
  - Every SDM-undefined flag is `none`, and reading one faults.

## Severity summary

| # | Finding | Severity | Status |
|---|---|---|---|
| CRITICAL-1 | Inline non-canonical instance in the statement: prints `x * y` for code computing `x + y`, **Verified** | critical | **BROKEN** |
| MEDIUM-1 | amd64 DF not in state: a verified mid-function theorem says memmove's backward `REP MOVSQ` copies forward | medium | **BROKEN** (call theorems unaffected) |
| LOW-1 | amd64 LOCK split across a cache line (SIGBUS with `split_lock_detect=fatal`); AtomicAdd/AtomicMax don't require alignment | low–medium | open |
| LOW-2 | amd64 64-bit BSF/BSR of zero follows AMD, against the vendor-neutral policy | low | open |
| LOW-3 | arm64 feature list missing AdvSIMD/FP; HWCAP trust | low (docs) | open |
| LOW-4 | arm64 DCZID_EL0 assumed identical on all cores | low (docs) | open |
| U1 | `unshare` fallback leaves non-root mounts writable | low (confinement) | trusted state blocked; `/tmp` residual |
| M1, deps, cache, batch, marker | see "Blocked / correct" | n/a | blocked |
