# Janus soundness audit — round 3

Third independent adversarial review of the claim: *if `janus verify` (or `verify-batch`, or
consumer `--proof-root` verification) prints `Verified`, the printed statement is exactly what was
proved, and it holds for the actual bytes of this binary under the documented semantics.*

Rounds 1 and 2 (`docs/AUDIT.md`, `docs/AUDIT-ROUND2.md`) fixed forged audits, pretty-printer and
unexpander tricks, sandbox/replay holes, dependency pinning, and the inline-instance hole in the
theorem *type* (round-2 CRITICAL-1: `checkInstArgs` + statement round-trip). This round attacks
the round-2 fixes themselves: the round-trip check, the instance-argument check, the new sandbox
confinement, and the newest model semantics (amd64 DF/REP, YMM, VEX, FS, split-lock; arm64
Advanced SIMD/AES, atomics, DC ZVA). It also builds non-vacuity witnesses for the four newest
example theorems and checks their doc comments against their statements.

Attacks live in `audit/round3/` (`attacks/`, `controls/`) with `run-round3.sh`. Severity:
**critical** = a false/misleading theorem prints `Verified`; **high** = a confinement break that
lets untrusted proof code forge a verdict, or a wrong value for a valid instruction; **low** =
hygiene / defence-in-depth.

Two findings, both now fixed in this branch; everything else attacked was blocked.

| # | Severity | Finding | Status |
|---|----------|---------|--------|
| R1 | **critical** | round-2 CRITICAL-1 reopened through a proof-local **definition body** | **BROKEN → fixed** |
| S2 | **high** | the sandbox `--ro-bind / /` exposes the host's live `/run` daemon sockets | **BROKEN → fixed** |
| R2 | low | theorem-level instance binder prints a misleading operator (self-disclosing) | blocked (residual) |
| model/AES, DF, round-trip truncation, instance reach, JANUS_SANDBOX | — | attacked | blocked |

---

## R1 (CRITICAL, BROKEN → fixed): the inline-instance lie, moved from the statement type into a disclosed definition body

**Files:** `audit/round3/attacks/R1_def_body_instance.lean`. Target: the shipped
`example.com/basic.Add`, which computes `x + y`.

### What happens

Round-2 CRITICAL-1 was closed for the theorem *type* by `checkInstArgs` (reject inline
instances) and the round-trip (re-elaborate the printed statement). But the auditor also
**discloses the body of every plain proof-local `def` the statement uses** (`verified.json`
`definitions`, printed by `janus explain`), and those bodies are pretty-printed with the *same*
default printer — with **no** `checkInstArgs` and **no** round-trip applied to them.

So move the hole one level down. The statement names only a proof-local constant:

```lean
def mul (a b : BitVec 64) : BitVec 64 :=
  @HMul.hMul (BitVec 64) (BitVec 64) (BitVec 64) ⟨fun a b => a + b⟩ a b   -- an inline HMul that ADDS
theorem correctness (x y : BitVec 64) :
    Ensures … (fun _ s' => s'.regs 0 = mul x y) := by … janus_run; rfl
```

The theorem type is `s'.regs 0 = Proof.mul x y` — a single constant application, no inline
instance, round-trips trivially. The proof closes (`mul x y` is kernel-defeq to `x + y`, which
the Add binary leaves in `X0`). Before the fix, `janus verify` printed **Verified** with:

```
Statement:  … fun x_1 s' => s'.regs 0 = Proof.mul x y
definitions: Proof.mul : BitVec 64 → BitVec 64 → BitVec 64 := fun a b => a * b
```

The only place a reader learns what `Proof.mul` *is* is that disclosed body — and it reads
`fun a b => a * b`. The function adds; its disclosure says it multiplies. The reader, and
`janus explain`, conclude "returns `x * y`" for a binary that returns `x + y`. This is exactly
CRITICAL-1 (a true, fully-checked theorem whose *printed guarantee* lies), reached through the
definition-disclosure surface that the round-2 fix never covered.

### Why the round-2 defences miss it

* `checkInstArgs` and `roundTrip` run **only on `thmType`** (`cleanEnvAndPrint`, the `printAll`
  block). The `localDefs` were printed with a bare `Meta.ppExpr ci.value?` — no instance check.
* The round-trip can't catch it: the statement `s'.regs 0 = Proof.mul x y` re-elaborates to the
  same constant `Proof.mul`; the lie is in how the *body* of that constant is displayed, not in
  the statement text.
* `statementExplicit` prints `Proof.mul x y` opaquely (`pp.explicit` does not unfold the def), so
  it does not expose the body either.

### Fix (applied)

`Janus/Tools/Audit.lean`, `cleanEnvAndPrint`'s `printAll`: before disclosing each proof-local
def, run the same `checkInstArgs` on the def's **type and value**. An inline non-canonical
instance in a body is now rejected with `Stage: statement identity`:

```
the proof-local definition Proof.mul used in the statement passes the inline instance
`{ hMul := fun a b => a + b }` as the instance argument 4 of HMul.hMul; …
```

`run-round3.sh` confirms R1 now prints `Invalid`, while `examples/proofs/Add.lean` and the
examples whose statements legitimately use proof-local defs with honest bodies
(`A64IndexByte`'s `indexOf`, amd64 `Equal64`'s `hasAVX2`, `CopyBlock512`'s `memmoveBits`,
all elaborated from ordinary notation to canonical instances) still print `Verified`.

A fuller version would also round-trip each disclosed body (to also catch coercion/`OfNat`
pp-hiding inside a body, by analogy with the statement round-trip); `checkInstArgs` on bodies
closes the demonstrated break and is what is shipped here.

---

## S2 (HIGH, BROKEN → fixed): the sandbox binds the host's live `/run` daemon sockets read-only, which does not confine them

**Observed on this host** (verifier running as root, Docker present). The sandbox (both the
bubblewrap default and the `unshare` fallback) exposes the whole host filesystem with
`--ro-bind / /` / an all-read-only remount. That bind includes the live unix sockets under
`/run`: `/run/docker.sock`, `/run/dbus/system_bus_socket`, `/run/containerd/containerd.sock`.

A **read-only** bind of a directory does **not** stop a process from `connect()`-ing to a unix
socket inside it and exchanging bytes — socket I/O is not a filesystem write — and unix sockets
are **not** scoped by the network namespace that `--unshare-all` creates. So untrusted proof
code (a `#eval`/`initialize`/macro that runs while Lean elaborates the proof or a consumer
`lakefile.lean`) can reach the Docker daemon API from inside the sandbox. I confirmed the Docker
API answered a request made from inside the default bwrap sandbox (the daemon `/version` reply
came back); I did **not** go further. From there a proof could start a privileged container that
mounts the host, escaping confinement entirely and then rewriting the `janus` binary, the trusted
framework `.olean`s or the replay cache to forge a `Verified` for any statement. That makes it a
verdict-integrity break, not merely an exfiltration concern.

Round 2's U1 analysis checked that `/tmp`, `/dev/shm`, `/boot`, `/run/user/0` writes do not reach
the host, but it reasoned only about *file writes*; a reachable privileged *socket* was not
considered. The documented guarantee ("no network, read-only filesystem, private build dir") is
silent on daemon sockets, so this is a real gap in the confinement that protects the verdict.

It is host-conditional: it bites when the verifier's uid can reach such a socket (root, or a user
in the `docker` group, with the daemon running). A plain developer laptop without Docker is not
affected. But Janus is meant to be run in CI and on servers where exactly those sockets exist.

### Fix (applied)

`cmd/janus/sandbox.go`: overmount `/run` (and thus `/var/run`, a symlink to it) with an empty
`tmpfs`, the same treatment `/tmp` already gets, so the host's runtime sockets are not present
inside the sandbox:

* **bwrap**: add `--tmpfs /run` to the base arguments (the cache re-bind still restores any janus
  directory that happens to live under `/run`).
* **unshare fallback**: `mount -t tmpfs … /run` after the `/tmp`/`/dev/shm` tmpfs mounts, skipped
  only when a path janus must bind back (cache, read-only, writable or protected dirs) lives under
  `/run` — those are normally under the home cache, not `/run`.

Verified: `janus verify` of the honest `Add` proof still prints `Verified` under both bwrap and
the forced `unshare` fallback, with `/run` now an empty tmpfs inside. `TestUnshareFallbackConfinement`
was updated to treat `/run` as a private tmpfs (like `/tmp`/`/dev/shm`): writable inside, isolated
from the host (the host-leak check still applies).

A stronger future hardening is to stop binding all of `/` and bind only the toolchain, framework
and work directories; the tmpfs overmount is the minimal change that closes the demonstrated hole
without risking the build's path assumptions.

---

## R2 (LOW, blocked — residual): a theorem-level instance binder prints a misleading operator, but self-disclosingly

**File:** `audit/round3/attacks/R2_inst_binder.lean`. This is the instance-binder case from the
round-3 brief (attack idea 2). The theorem takes an instance *binder* and a hypothesis tying it
to `+`:

```lean
theorem correctness [inst : HMul (BitVec 64) (BitVec 64) (BitVec 64)]
    (x y : BitVec 64) (h : @HMul.hMul _ _ _ inst x y = x + y) :
    Ensures … (fun _ s' => s'.regs 0 = @HMul.hMul _ _ _ inst x y) := …
```

It verifies and prints `s'.regs 0 = x * y`. `instArgOk` accepts the `inst` fvar (it is an
instance-implicit binder), and the round-trip succeeds because the clean environment resolves
`*` to the *same* bound instance.

**Why this is only LOW, not a break.** Unlike R1/CRITICAL-1, nothing is hidden: the printed
signature carries the binder `[inst : HMul (BitVec 64) (BitVec 64) (BitVec 64)]` and the
hypothesis `(h : x * y = x + y)` verbatim. The `*` is honestly the abstract bound instance's
operation (there is an `HMul` binder in scope), so the print is faithful. The statement is a
true, *weaker* claim: "for every `HMul` instance such that `x * y = x + y`, the result is
`x * y`" — which, instantiated at the real `+`-as-`HMul` with `h` discharged, says the result is
`x + y`. A reader who reads the whole signature (the binder and the glaring `x * y = x + y`
hypothesis, which no honest multiplication statement carries) has the complete picture. The
inability to render a bound-instance operator distinctly from the canonical one is a
pretty-printer limitation; the fully-disclosed binder and hypothesis are the mitigation. Recorded
as a residual, not fixed.

---

## Blocked (verifier & auditor)

* **Round-trip truncation (attack idea 1, last bullet).** A statement large enough to trip the
  pretty-printer's term/step limits would print with an `⋯` ellipsis; the round-trip then fails
  to *parse* it back and the audit prints `Invalid` ("does not round-trip"). Truncation can
  therefore only cause a (sound) false rejection, never an accepted-but-misleading statement.
  `printOptions` sets no low `pp.maxSteps`/`pp.deepTerms`, so ordinary statements are unaffected.

* **Instances reached through `outParam`/default instances / Janus's own instances.** The only
  `instance` Janus declares on its own types is `Inhabited State` (arm64 and amd64), which cannot
  appear in an `Ensures`/`Returns` statement in a meaning-changing position. `trustedInstance`
  only accepts `Meta.isInstance` globals of the clean environment (core/`Janus`/`Extracted`) and
  trusted-module scoped instances; dependency instance lists are empty by rule (`checkExternal`).
  A non-canonical operator must still be written inline, which R1's fix (plus the round-2 type
  check) now rejects in both the type and the bodies.

* **`JANUS_SANDBOX` consumer influence (attack idea 3).** `detectSandbox` reads the operator's
  process environment; a submitted proof/consumer package cannot set it. An unknown value is
  rejected; `unshare` and `bwrap` are the only accepted values and give equivalent confinement
  (and S2's fix applies to both). No consumer-reachable path changes the sandbox choice.

* **sorry / disallowed axioms.** A statement whose postcondition needs an unproved step still
  fails the axiom audit (`sorryAx`), as `audit/round3` confirmed incidentally. `native_decide`
  (`ofReduceBool`) and `bv_decide` (`trustCompiler`) remain rejected.

## Model (blocked)

* **arm64 AES matches FIPS-197.** Concrete evaluation of `Janus/Arm64/Vector.lean` against the
  FIPS-197 reference:
  - S-box: `aesSbox[0x53] = 0xed`, `[0x00] = 0x63`, `[0xff] = 0x16` ✓
  - MixColumns: column `db 13 53 45 → 8e 4d a1 bc` ✓; `InvMixColumns ∘ MixColumns = id` ✓
  - ShiftRows permutation ✓
  - a full `AESE` round on FIPS-197 Appendix B round-1 state (`SubBytes ∘ ShiftRows`) produces
    exactly the appendix's "After ShiftRows" state
    (`d4 bf 5d 30 27 98 e5 1e 11 f1 b8 41 ae e0 b4 52`) ✓.
  No wrong value found.

* **amd64 DF / REP / overlapping memmove** (round-2 MEDIUM-1, now closed). The direction flag is
  a `State` field `df`; `CLD`/`STD` (`0xFC`/`0xFD`) write it, `CallSetup.df` requires it clear at
  a call. `MOVS`/`STOS` iterate **per element, load-then-store** (`movsIter`/`movsIterB`,
  `stosIter`/`stosIterB`), so an overlapping `REP MOVS` copies byte ranges in the exact
  hardware order, and the backward (`df = true`) iterators decrement `RSI`/`RDI`. The round-2
  `DFMemmove` finding (DF not in the state) no longer applies.

## Non-vacuity controls (attack idea 5)

Concrete positive-control witnesses, each building a satisfying call state and instantiating the
shipped `Proof.correctness` to a concrete `Returns`, so none of the four newest examples is
vacuous. All four compile (`audit/round3/controls/`, see `README.txt`):

* `A64Equal64_witness.lean` (arm64) — readable `stackguard0`, 24-byte stack window, two readable
  64-byte arrays, pairwise disjoint. ✓
* `A64IndexByte_witness.lean` (arm64) — 72-byte stack window, a length-64, 32-byte-aligned
  readable slice disjoint from the stack. ✓
* `Equal64_witness.lean` (amd64) — return address on the stack, readable `stackguard0`, 48-byte
  stack window, two readable 64-byte arrays, a readable `HasAVX2` feature byte (`0x579264`),
  pairwise disjoint; holds for any value of the feature byte. ✓
* `CopyBlock512_witness.lean` (amd64) — as above with a 512-byte writable `dst`, 512-byte
  readable `src`, and `runtime.memmoveBits` (`0x578ab0`) readable with the AVX bit set. ✓

**Doc comments vs statements.** The plain-English guarantee comment of each of the four matches
its statement: `A64Equal64`/`Equal64` return `1`/`0` (resp. `AL = 1`/`0`) iff the 64 bytes are
equal, over readable arrays disjoint from the stated stack window; `A64IndexByte` returns the
first matching index or `-1` as a two's-complement 64-bit value, using only the low byte of the
argument (`c % 256`), on a 32-byte-aligned length-64 slice; `CopyBlock512` leaves the 512 bytes
at `dst` equal to those that were at `src`, on an AVX CPU (`memmoveBits` bit 0 set), with the
stated accessibility and disjointness preconditions. (Note, not a mismatch: `CopyBlock512.correctness`,
like its doc comment, asserts only the `dst = src` copy and ABI return — neither claims other
memory is preserved, unlike the arm64 `CopyBlock`, whose statement and doc both include
`OnlyWrites`.)

---

## Reproduce

```
audit/round3/run-round3.sh          # R1 (now Invalid), R2 (Verified, self-disclosing), regression
                                    # witnesses: see audit/round3/controls/README.txt
```
