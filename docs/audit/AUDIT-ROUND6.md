# Janus soundness audit — round 6

Sixth independent review. Rounds 2–5 each found a CRITICAL hole of one family: the printed
statement used a symbol that meant something other than it read (an inline instance in r2, an
instance hidden in a disclosed def body in r3, a numeral's type in r4, an instance binder inside
the statement in r5). This round does not try one more instance pattern. It writes down the
invariant the auditor now enforces, lists the assumptions needed to get from that invariant to
the guarantee, and attacks each assumption live. It also attacks one surface no earlier round
looked at: how the extracted program's stubs are classified.

Guarantee under review: *a reader who reads the printed statement and the printed definitions
with Lean's standard meaning of core, Janus and dependency notation understands exactly the
proposition that was proved, and that proposition is about the bytes of this binary.*

Rows are in `audit/round6/` (`attacks/`, `stubmod/`, `run-round6.sh`), `cmd/janus/round6_test.go`
and `TestStubKind`. Severity is as in earlier rounds: **critical** means a misleading account
prints `Verified`; **high** means a false claim about the binary prints `Verified`; **low** means
hygiene.

| # | Severity | Finding | Status |
|---|----------|---------|--------|
| F1 | **critical** | **Lookalike names.** Lean identifiers may contain Greek, Coptic, letterlike and mathematical-alphanumeric letters. A proof-local `Εxtracted.program` (Greek capital epsilon) or `Janus.GoABI.Εnsures` prints exactly like the trusted constant it imitates. The `Extracted`-component rule compared strings and missed both the lookalike and a one-component `«Extracted.program»`. | **BROKEN → fixed** |
| F2 | high (readability) | **Out-of-range numerals.** `y ≠ 18446744073709551616` at `BitVec 64` round-trips exactly, because Lean also reads it as `y ≠ 0`. It prints as a plain decimal and reads as a vacuous hypothesis. | **hazard → hardened** |
| F3 | high | **Stub classification by symbol prefix.** An ordinary function in a package whose import path starts with `runtime.panic` (for example, module `runtime.panicky`, symbol `runtime.panicky/lib.Zero`) was classified as a Go panic stub. "`Add` panics on every call" then verified, while the real `Add` returns `x + y` (qemu prints 3). No linker flag is needed. | **BROKEN → fixed** |
| A* | — | The other assumptions (see the table below) | hold or are documented residuals |

**This round found BROKEN items: F1 (critical) and F3 (high). Both are fixed, with regression
rows. F2 is a hazard under the stated guarantee (Lean reads the text the same way) and is hardened
anyway.**

---

## 1. The invariant (after this round)

Let `T` be the theorem's type. Let `L` be the proof-local (consumer) constants reachable from `T`
through types and values, and `X` the dependency constants reached on the way. Let `D(c)` be
the disclosure of `c ∈ L`. `janus-audit` prints `Verified` input only if all of the following
hold (`Janus/Tools/Audit.lean`):

1. **Kind/module.** `thm` is a `theorem` declared in the proof module. Its axioms are ⊆
   {propext, Quot.sound, Classical.choice} (checked in Go).
2. **Program identity (C1).** The imported `Extracted.program`/`entry` are kernel-defeq to
   `JanusTrusted.*`, which is compiled by `janus` from the `Extracted.lean` that `check`
   regenerated from the binary and compared byte for byte, before and after the run. `T`
   mentions `Extracted.program` or `Extracted.entry`. **No non-trusted module declares a name
   with a component that is, or that reads as, `Extracted`/`JanusTrusted`.** For "reads as",
   the component is split at non-identifier characters and lookalike letters are folded to Latin
   (round 6, `imitatesExtracted`).
3. **Origin.** Every constant of `T` comes from a trusted module root (`Init`, `Std`, `Lean`,
   `Janus`, `Extracted`, `JanusTrusted`), or is in `L`, or is in `X`. Members of `L` are safe
   plain `def`/`theorem`s that are not instances and not class-valued; consumer inductives are
   rejected. Members of `X` are plain defs, theorems, inductives, constructors or recursors, and
   never instances, classes, class-valued, opaque, axioms or unsafe. Bodies of `X` are not
   unfolded.
4. **Plain names (round 6).** Every name in `L ∪ X` has components made only of ASCII letters,
   digits, `_ ' ! ?` and Lean's subscript letters (`plainName`).
5. **Instance provenance.** In `T`, and in the type and value of every `c ∈ L`, every argument in
   an instance-implicit position has, up to reducible unfolding and `whnfCore`, a head that is a
   registered trusted instance or an instance binder of the *leading* telescope (the theorem's or
   the def's own parameters). No binder below the leading telescope is instance-implicit or of
   class type. No term is used unapplied while its type still takes an instance parameter.
6. **Numerals (round 6).** No `OfNat.ofNat τ n _` in `T` or in any `c ∈ L` has `n ≥ |τ|` for a
   wrapping `τ`: `BitVec w`, `Fin k`, `UIntN`, `IntN` (bound `2^(N-1)`), `USize`/`ISize` (the
   portable 32-bit bound).
7. **Round trip.** The statement is printed in a clean environment that imports only `Janus` and
   `Extracted`, with `L` re-added and `X` as type-only axioms. It is printed with `pp.fullNames`
   and `pp.coercions.types`, plus `pp.numericTypes` if the plain print fails. The printed text
   must parse and elaborate (no auto-implicits, no `sorry`, no mvars) to a term that is
   `Meta`-defeq at default transparency **and** kernel-defeq to `T`. Each `D(c)` must round-trip
   the same way, plain or annotated. Otherwise it is printed annotated and tagged
   `[not round-tripped: read with care]`; universe-polymorphic defs are always tagged.
8. **Report hygiene.** Control and bidi characters in report text are escaped (`termSafe`).
9. **Stubs (round 6, Go).** An address is a `panic`/`morestack` stub only if the symbol is in
   package `runtime` itself, that is, the name has no `/` and no `%`. The `runtime.panic*`,
   `runtime.goPanic*`, `runtime.gopanic` and `runtime.morestack*` prefixes still apply.

### From the invariant to the guarantee: the assumptions, and a verdict for each

| # | Assumption | Verdict |
|---|---|---|
| A1 | Defeq at default transparency preserves meaning | **Holds.** Kernel-defeq propositions are the same proposition, so a proof of `T` is a proof of the printed text as elaborated. |
| A2 | The clean environment's elaboration of the text is the reader's: no proof-local notation, macros, delaborators or instances apply | **Holds** (r5 E4). The clean environment never imports the proof or a dependency's code. |
| A3 | Trusted global instances are canonical | **Holds, with documented hazards.** Janus defines only `Inhabited State`/`Memory` and derived `Repr`/`DecidableEq`/`BEq`/`Inhabited`. Core instances are Lean's standard ones. Some standard meanings surprise readers: `Nat` subtraction truncates, `x / 0 = 0`, `BitVec`/`Fin`/`UIntN` arithmetic wraps (`(2 : BitVec 64) ^ 64 = 0`), `xs[i]!` returns `default`, `<` on `BitVec` is unsigned. These are "Lean's standard meaning", so they are not BROKEN. Only the *literal* form is rejected (F2). |
| A4 | Each printed numeral denotes the value its digits spell | **Was false** for out-of-range literals at wrapping types. **Hardened** (F2). |
| A5 | Names the reader sees can be told apart | **Was false** (F1). **Fixed** for every constant name in `L ∪ X` and for the `Extracted` namespace across all non-trusted modules. Residual (low): *bound variable* names are not checked. A local `Υ` and a theorem parameter `Y` look alike, but each binder is printed where it is introduced, with its type. |
| A6 | `Decidable` instances cannot change meaning | **Holds.** It is a subsingleton, and non-canonical instances are rejected anyway (r5 E1). |
| A7 | A disclosed body is read by the reader, so its name cannot mislead | **Holds**, given F1. `Proof.add := fun a b => a - b` is printed under "Proof-local definitions used by the statement (part of its meaning)", with its body. The report states plainly that these definitions are part of the meaning. A proof-local name in a trusted namespace (`Janus.Arm64.State.result`, r5 E3d) is still allowed and disclosed. With F1 it can no longer be *spelled* like an existing trusted name. |
| A8 | Tagged (not round-tripped) definitions hide nothing that changes meaning | **Residual, unchanged.** See §3. |
| A9 | Dependency bodies mean what their pinned source says | **Residual** (r5). They are listed by name, and F1's plain-name rule now applies to them too. |
| A10 | `Extracted.program` is the binary's code | **Holds**: byte-for-byte regeneration plus the kernel-defeq identity check. `withExit` and structure eta change nothing, because any rewrite of the program in `T` is printed (for example `{ Extracted.program with stubs := [] }` prints as a structure literal). The F1 lookalike route is now closed. |
| A11 | A stub's outcome is what the runtime function does | **Was false** for non-runtime packages with a `runtime.panic…`/`runtime.morestack…` import path (F3). **Fixed.** Residual (unchanged, out of threat model): a `-checklinkname=0` push into package `runtime`, or a hand-made ELF. The binary is the subject, not the adversary (docs/AUDIT.md §4). |
| A12 | Hypotheses are read | Not the auditor's job. A false hypothesis (`h : x * y = x + y`) makes a weaker but disclosed claim (r3 R2). |

---

## 2. Attacks and results

### F1 (CRITICAL, BROKEN → fixed): lookalike names

Target: the shipped `example.com/basic.Add` (`add x0, x0, x1; ret`).

* **F1a.** `def Εxtracted.program := { Extracted.program with segments := [ … mul x0, x0, x1 … ] }`.
  The statement is `Ensures Εxtracted.program Extracted.entry [x, y] … (s'.regs 0 = x * y)`.
  Before the fix:
  ```
  Verified: Proof.correctness
    Statement:
      Proof.correctness (x y : BitVec 64) : Janus.GoABI.Ensures Εxtracted.program Extracted.entry [x, y] (fun x => True) fun x_1 s' => s'.regs 0 = x * y
    Proof-local definitions used by the statement (part of its meaning):
      Εxtracted.program : Janus.Program := have __src := Extracted.program; { segments := [… words := [2600565760, 3596551104] }], … }
  ```
  That is "Add returns `x * y`" for code that adds. The rule meant to forbid this, "no proof name
  has an `Extracted` component", compared strings.
* **F1b.** The one-component name `«Extracted.program»`. It printed as `«Extracted.program»` and
  verified the same way.
* **F1c.** `def Janus.GoABI.Εnsures … : Prop := True`, proved by `trivial`. The statement printed
  exactly like a real `Ensures` claim that `Add` returns `x * y`. The only clue was a disclosed
  definition whose name looks like the trusted `Janus.GoABI.Ensures`.

**Fix.** Invariant items 2 and 4: `imitatesExtracted` covers the whole non-trusted environment,
and `plainName` covers every constant the statement reaches. Messages: "shadows the Extracted
namespace" and "… lookalike letters …", both at `Stage: statement identity`. The plain-name
rule also covers dependency constants, by code reading; there is no live dependency row. No
shipped example or consumer test uses a non-ASCII constant name.

### F2 (hazard → hardened): out-of-range numerals

* **F2a** (Div). Hypothesis `(hy : y ≠ 18446744073709551616)` with `Returns … x.toNat / y.toNat`.
  It reads as "Div returns `x / y` for every `y`". It is really `y ≠ 0`, and `Div(x, 0)` panics.
  Before the fix it verified, printed as a plain decimal.
* **F2b.** `def bias : BitVec 64 := 18446744073709551616` and `s'.regs 0 = x + y + bias`. This
  reads as "adds 2^64". It verified before the fix.
* **F2c** (control). `18446744073709551615 : BitVec 64` and `255 : UInt8` still verify.

**Fix.** Invariant item 6, `checkNumerals`, applied to the statement and to every disclosed type
and value. Message: "out-of-range numeral". Wrapping produced by *operations* (`2 ^ 64`,
`x + 1` at the maximum) is standard Lean meaning and stays a documented hazard (A3).

### F3 (HIGH, BROKEN → fixed): stub classification by symbol prefix

`audit/round6/stubmod` is the module `runtime.panicky`. Its `lib.Zero` returns 0, and its
`main.Add(x, y)` returns `x + y + lib.Zero()`. The Go linker names the callee
`runtime.panicky/lib.Zero` (only a dot in the *last* path element is escaped). Before the fix,
`janus extract` printed `stub 0xa6010 panic runtime.panicky/lib.Zero`, and **F3a**,
`Panics (Extracted.program.withExit ret) s` for every call, verified. On hardware (qemu-aarch64),
`Add(1, 2)` returns 3. `Returns` cannot be established through a stub (SOUNDNESS item 3).
`Panics`, `¬NeverPanics` and `GrowsStack` claims could all be made about code that returns.

**Fix.** `stubKind` (`cmd/janus/extract.go`, shared by arm64 and amd64) accepts only names
without `/` and `%`, which means package `runtime` itself. `Zero` is now extracted as code.
F3a no longer checks, and **F3b**, `Returns … s'.regs 0 = x + y`, verifies on the new
extraction. `TestStubKind` has rows for `runtime.panicky/lib.Zero`, `runtime.morestacks.io/x.F`,
`runtime.gopanic/x.F` and `runtime%2epanicky.F`. Inside package `runtime`, every
`panic*`/`goPanic*` function in go1.26.0's sources panics or throws, except the helpers
`panicCheck1`/`panicCheck2`, which return when their check passes. Only the runtime's own panic
functions call them, never generated code. They are therefore never a direct branch target of
extracted user code: they are reached only from inside a stub, which is not extracted.

Other binary-identity probes, by reading:

* duplicate stub addresses are deduplicated by address;
* two symbols at one address take the same `containing` choice on every path;
* `lookup` requires a unique name;
* `data` segments come only from non-writable sections, and the precondition states them (`DataLoaded`);
* `Program` structure eta and `withExit` cannot change what `Extracted.program` denotes (A10).

No further issue was found.

---

## 3. The D4 residual (tagged definitions)

What a tagged disclosure can still hide is limited to three kinds of term:

* **Proofs (`⋯`).** No data can be extracted from a proof except by eliminating into a
  subsingleton. `cast`, `▸`, `Eq.mpr`, `Acc.rec` and `WellFounded.fix` keep the value they
  transport, and `False.elim` occurs only in dead code. `Classical.choice ⋯` is unspecified, so
  no theorem can rely on its value.
* **Universe levels.** They do not affect values.
* **Implicit arguments.** For recursor motives (`Nat.rec`, `brecOn`, `casesOn`), the value is
  determined by the explicit minor premises. For type arguments, the value is fixed by the types
  of the explicit arguments, and those are shown with `pp.funBinderTypes`/`pp.numericTypes`.
  For instances, round 3's body check and round 5's binder check still apply to tagged defs.

The F1 and F2 checks also run on tagged defs, because they are structural. A forged
`….match_1` is disclosed with its own body. No deceptive tagged disclosure was found, so the
equation-lemma disclosure is still recommended hardening, not a fix. It was not implemented.

## Residual risks (honest list)

* Standard-but-surprising Lean semantics produced by operations, not literals: wrapping
  `BitVec` arithmetic and `^`, truncating `Nat` subtraction, `/ 0`, `[i]!` (A3).
* Bound-variable lookalikes (A5): printed with their binder, not checked.
* Tagged defs (§3) and dependency bodies (A9): unchanged.
* Stubs pushed into package `runtime` by `-checklinkname=0`, or a hand-made ELF (A11): out of
  threat model.

## Changes to earlier rows

* **Round 4 D1.** Its fixture `Proof.wide := (256 : BitVec 8) ≠ 0 ∨ True` is itself an
  out-of-range literal. Round 4 fixed its disclosure (it printed `256 ≠ 0`, true at `Nat`) by
  annotating the type. Round 6 F2 now rejects it outright, and `run-round4.sh` checks that
  rejection. The property round 4 tested, that a disclosure carries a numeral's type when the
  plain print would read back at `Nat`, is checked on a new in-range fixture,
  `audit/round4/attacks/D1b_def_numeral_type_inrange.lean`
  (`(255 : BitVec 8) + 1 = 0 ∨ True`, true at `BitVec 8` and false at `Nat`). The D2 checks,
  that `verify` and `explain` show the definitions, move to that fixture too.

## Regression status

With this branch, all of these pass: `audit/round6/run-round6.sh`, `scripts/verify-examples.sh`,
`scripts/verify-amd64-examples.sh`, `audit/run-all.sh`, `audit/round2/run-round2.sh` through
`audit/round5/run-round5.sh`, and `go test -timeout 50m ./cmd/...`.

## Reproduce

```
audit/round6/run-round6.sh
```
