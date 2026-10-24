# Janus soundness audit — round 5

Fifth independent review of the claim: *if `janus verify` (or `verify-batch`, or consumer
`--proof-root` verification) prints `Verified`, everything it reports (the printed statement, the
printed proof-local definitions, `janus explain`, `verified.json`) is an exact and honest account
of a theorem that holds for the actual bytes of this binary under the documented semantics.*

Round 4 left six areas checked only by reading the code, with no live attack or regression row.
This round attacks each of them live: `Decidable` instances, instance stand-ins, proof-local
types, proof-local notation, the D4 residual, and the instruction semantics. Rows are in
`audit/round5/` (`attacks/`, `dep/`, `model/`, `run-round5.sh`) and
`cmd/janus/round5_test.go`.

Severity, as in earlier rounds: **critical** = a misleading account prints `Verified`;
**high** = a reported item the user relies on is missing or unconfirmed; **low** = hygiene.

| # | Severity | Finding | Status |
|---|----------|---------|--------|
| E5 | **critical** | an instance **bound inside** the statement or a disclosed def (`∃ [_ : HMul …], r = x * y`, or a def passed to `Exists` without its instance argument) makes `x * y` mean "some multiplication", so the claim holds for every result while it prints, round-trips and is disclosed as `… = x * y` | **BROKEN → fixed** |
| E1 | — | `Decidable` instances in `decide`/`if`, statement and hypotheses, proof-local and from a pinned dependency | blocked (13 rows) |
| E2 | — | `@[reducible]`/`abbrev` instances, `let`/`fun`/beta, `letI`/`haveI`, `inferInstanceAs`, `attribute [instance]` after the fact, `attribute [local instance]`, `scoped`, priorities | blocked (11 rows) |
| E3 | low | proof-local structures/inductives are rejected; a dependency structure with a field named `regs` is accepted and listed | blocked / residual |
| E4 | — | `macro_rules`, `local notation`, global notation and unexpanders declared in the proof | blocked (the report prints the term, never the source) |
| E6 | residual | D4: `match_1`, well-founded and universe-polymorphic defs stay tagged `[not round-tripped]`; no deceptive print found | residual, row added |
| E7 | low | a proof-local auxiliary theorem was disclosed as `:= <opaque>` | fixed (cosmetic) |
| M | — | model level: 6 families, 94,000 targeted cases plus 23 hand-derived kernel checks | 0 MISMATCH |

**This round found one BROKEN item (E5, critical). It is fixed, with regression rows.**

---

## E5 (CRITICAL, BROKEN → fixed): an instance bound inside the statement

**Files:** `audit/round5/attacks/E5a`–`E5f`. Target: the shipped `example.com/basic.Add`, which
computes `x + y`.

### What happens

In Lean, any local of class type is a local instance. Inside
`Exists fun [_i : HMul (BitVec 64) (BitVec 64) (BitVec 64)] => r = x * y`, the `*` therefore
elaborates to `@HMul.hMul _ _ _ _i x y`, where `_i` is the bound instance, not the canonical
`BitVec` multiplication. The proposition says only that *some* `HMul` maps `(x, y)` to `r`.
That is true for every `r` (take `hMul := fun _ _ => r`), so the claim says nothing about
`X0`. Before the fix, all of these printed `Verified`:

```lean
-- E5b, in the statement:
(fun _ s' => Exists fun [_i : HMul (BitVec 64) (BitVec 64) (BitVec 64)] => s'.regs 0 = x * y)
-- proved by:  exact ⟨⟨fun _ _ => x + y⟩, rfl⟩
```
```
Statement:
  Proof.correctness (x y : BitVec 64) : Janus.GoABI.Ensures Extracted.program Extracted.entry [x, y]
    (fun x => True) fun x_1 s' => Exists fun [HMul (BitVec 64) (BitVec 64) (BitVec 64)] => s'.regs 0 = x * y
```

* **E5a** moves it into a disclosed def, `Proof.isProd x y (s'.regs 0)`. The disclosure round-trips
  and is *not* tagged: `Proof.isProd : … := fun x y r => Exists fun [HMul …] => r = x * y`.
* **E5e** needs no binder in the statement at all. The def takes its instance as its last
  parameter, `def isProd (x y r : BitVec 64) [_i : HMul …] : Prop := r = x * y`, which is a
  legitimate top-level parameter. The statement then passes it to `Exists` unapplied:
  `Exists (@Proof.isProd x y (s'.regs 0))`. `Exists` supplies the instance.
* **E5f** is E5e with the parameter type hidden behind `def Pred := HMul … → Prop`. The binder is
  then a *default* one, so the def's type shows no `[…]` at all.

Every check passes, and that is why it is critical:

* `checkInstArgs` accepts the bound variable, because `instArgOk` admits any fvar whose binder is
  instance-implicit. That rule was meant for the theorem's own `[inst : C]` parameters (round 3,
  R2), but it applied at any depth.
* The round trip succeeds. The printed `fun [HMul …] =>` re-elaborates with the same local
  instance, so the term is faithful *as Lean*.
* The theorem is true. It is simply vacuous about the result.

To a reader, `… s'.regs 0 = x * y` is a claim that `Add` returns `x * y`. The `Exists fun [HMul …]`
prefix is easy to misread, and in E5e/E5f there is no binder at all. This differs from round-3
R2, a theorem-level `[inst : HMul …]` binder. R2 is universal and carries a glaring
`(h : x * y = x + y)` hypothesis, so it makes a *weaker but true and disclosed* claim. E5 is an
existential, and it makes no claim at all.

### Fix (`Janus/Tools/Audit.lean`, `checkInstArgs`)

* A binder that is instance-implicit **or of class type** (any local instance) is accepted only
  in the *leading* binder telescope of the checked term. For the statement that means the
  theorem's parameters, so R2 is unchanged. For a disclosed def it means the def's parameters,
  in its type and its value. Any other such binder is rejected: a nested `∃`, `∀` or `fun`,
  including inside hypotheses (E5d: `∀ [_ : HMul …], x * y = x + y`, a false hypothesis that reads
  like a fact about `*`).
* A term used as a value whose type, up to `whnf`, still takes a parameter of class type or an
  instance-implicit parameter is rejected (`unappliedInstParam`). This covers E5e and E5f. Heads
  of applications are exempt, because their instance arguments are the ones checked.
* `cmd/janus/verify.go` maps the new message ("binds the instance") to `Stage: statement identity`.

Rows: `run-round5.sh` (E5a–E5f must be rejected, and R2 must still verify) and
`TestBoundInstanceRejected`. Every shipped example still verifies; none of them binds an
instance below the top level.

**Residual (unchanged):** the body of a dependency def is not unfolded (it is the pinned
dependency's source, which a reader of that source sees). A dependency def written as
`∃ [_ : HMul …], …` would mislead in the dependency's source just as it would here. The
dependency constants are listed by name in the report.

---

## E1 (blocked): `Decidable` in `decide` and `if`

`Decidable p` is a subsingleton, so no instance can change what `decide p = true` or `if p …`
means. Janus is stricter than that and rejects non-canonical instances anyway:

| Row | Attack | Verdict, and the mechanism |
|---|---|---|
| E1a | `@decide (x = x) (myDec x)`, a proof-local def of type `Decidable …` | Invalid: class-valued proof-local def |
| E1b | `noncomputable instance (priority := high)` picked up by `decide` in a **hypothesis** | Invalid: proof-local instance |
| E1c | `@ite Prop (x = 0) (cdec _) False True` in a hypothesis (`Classical.propDecidable` behind a name) | Invalid: class-valued def |
| E1d | `@decide (x = 0) (Classical.propDecidable _)` inline (a *trusted* scoped instance) | Invalid: round trip (`decide` re-elaborates with `instDecidableEqBitVec`, which is not defeq). Over-strict, never misleading |
| E1e | `decide` with a custom def inside a disclosed def body | Invalid: class-valued def (round-3 body check) |
| E1g | the instance projected out of a non-class def, `(pair x).1 : Decidable …` | Invalid: inline instance (`instArgOk`: a projection of a non-instance) |
| E1f | control: canonical `decide`/`if` in the statement and a hypothesis | Verified, printed as `Decidable.decide (x = x) = Bool.true` |
| E1h | **dependency** (pinned git, `audit/round5/dep/`): a high-priority `instance … : Decidable (x = 0)` that `decide` in a hypothesis picks up | Invalid: dependency instance (`checkExternal`) |
| E1i | dependency def of type `Decidable …` | Invalid: class-valued dependency def |
| E1j | dependency **def body** using that instance (`DecLib.isZero`) | Verified, listed as `DecLib.isZero (def, DecLib)`. Dependency bodies are not unfolded, and the subsingleton argument makes it harmless |

## E2 (blocked): stand-ins for instances

| Row | Attack | Rejected by |
|---|---|---|
| E2a | `@[reducible] def addMul : HMul … := ⟨+⟩` passed explicitly | class-valued proof-local def |
| E2b | `abbrev addMul : Mul …` fed to the trusted `instHMul` | class-valued def (also `instArgOk` on the argument) |
| E2c | `let i : HMul … := ⟨+⟩; … @HMul.hMul _ _ _ i x y` | `instArgOk`: `let` fvar |
| E2d | beta-redex `(fun [_i : HMul …] => x * y) (_i := ⟨+⟩)` | inline instance (the redex argument is inst-implicit). E5 also rejects the inner binder now |
| E2e | `letI _i := ⟨+⟩; … inferInstanceAs (HMul …)` (now a term elaborator) | inline literal (`letI` substitutes the value) |
| E2f | plain def, then `attribute [instance high] addMul` | proof-local instance (the extension entry is exported) |
| E2g | `attribute [local instance high] addMul`: **not exported** to the `.olean`, so the instance set never sees it | class-valued def, and `Proof.addMul` is not a registered instance |
| E2h | `instance (priority := high + 1000)` overriding core `*` | proof-local instance |
| E2i | `scoped instance` in another namespace, `open … in` | proof-local instance |
| E2j | `(fun (i : HMul …) => @HMul.hMul _ _ _ i x y) ⟨+⟩` | the class-typed inner binder (E5); before the fix, `instArgOk` (default-binder fvar) |
| E2k | `haveI : HMul … := ⟨+⟩; s'.regs 0 = x * y` | inline literal |

## E3 (blocked / low residual): types declared in the proof

* E3a: a proof-local `structure View where regs : Nat → BitVec 64`, so that the statement reads
  `(view x y s').regs 0 = x * y`. E3b: `structure MyState extends State`, whose inherited `regs`
  is rewired by `{ s with regs := … }`. E3c: a proof-local `inductive` that is used only inside a
  disclosed def body. All three are Invalid, because `collectLocalDefs` accepts only `def` and
  `theorem` and follows the constants of def bodies.
* E3d: a proof-local `def Janus.Arm64.State.result`, which field notation prints as `s'.result`.
  It verifies, and it is disclosed as
  `Janus.Arm64.State.result : Janus.Arm64.State → BitVec 64 := fun s => s.regs 0`. Origin is
  decided by module, not by namespace, so nothing proof-local can pass as trusted. (Reserved
  module roots, `Janus` included, are refused by `checkModuleLayout` for consumer packages.)
* E3e (low residual): a **dependency** structure `DecLib.View` with a field `regs` is allowed. The
  statement prints `(DecLib.View.ofFun s'.regs).regs 0`, and the report lists
  `DecLib.View.regs (def, DecLib)`. The field name can only mislead someone who reads neither
  the full name nor the dependency list, and the dependency is pinned. Recorded, not changed.

## E4 (blocked): proof-local notation and macros

The auditor prints and round-trips in a clean environment that never imports the proof, so the
report shows the *elaborated term* with its global meaning, whatever the source text said:

* E4b: `macro_rules | `($a * $b) => `(binop% HAdd.hAdd $a $b)`. The source reads `x * y`; the
  report prints `s'.regs 0 = x + y`, which is Verified and honest.
* E4c: `local notation a " ^ " b => HAdd.hAdd a b`. The source reads `x ^ y`; the report prints
  `x + y`. (A local `*` is ambiguous with the global one, and Lean refuses it.)
* E4d: a global `notation … ⊗ …` and an `app_unexpander HAdd.hAdd` that would print `+` as `*`.
  Neither is active in the clean environment, so the report prints
  `s'.regs 0 = x + y ∧ s'.regs 0 = x.add y`.
* E4a: `macro_rules` turning `+` into `*` makes the source's `x + y` mean `x * y`. That is false for
  `Add`, so the proof does not check.

"A statement that round-trips to a *different but defeq* term whose text misleads": defeq
propositions are the same proposition to the kernel, and the round trip reads the text with
global meanings in the same clean environment the reader is told about. The text therefore
means what was proved. The one way found for a faithful text to read as something it does not
say is the *bound-instance* reading of an operator, and that is E5.

## E6 (residual): definitions that are not round-tripped (D4)

`E6a_match_wf_disclosure.lean` discloses a `match` def, a well-founded def
(`termination_by`/`decreasing_by`) and a universe-polymorphic def:

```
Proof.sel : Nat → BitVec 64 → BitVec 64 → BitVec 64 := fun n a b => Proof.sel.match_1 (fun n => BitVec 64) n (fun _ => a + b) fun n => a * b
Proof.sel.match_1 : (motive : Nat → Sort u_1) → … := fun (motive …) (n : Nat) (h_1 …) (h_2 …) => Nat.casesOn n (h_1 ()) fun (n : Nat) => h_2 n  [not round-tripped: read with care]
Proof.countdown._unary : … := fun (acc …) => WellFounded.Nat.fix (fun (x : Nat) => x) fun (n : Nat) (a : …) => if h : n = (0 : Nat) then acc else a (n - (1 : Nat)) ⋯  [not round-tripped: read with care]
Proof.poly : {α : Sort u} → α → BitVec (64 : Nat) → BitVec (64 : Nat) := fun {α : Sort u} (_a : α) (x : BitVec (64 : Nat)) => x  [not round-tripped: read with care]
```

The clean environment has no matcher info for the proof's auxiliaries, so `sel` shows the
explicit `Proof.sel.match_1` application, not a `match`. The auxiliary's body is shown
alternative by alternative, and the WF body is shown with its functional. Whatever is not
round-tripped is printed with `pp.numericTypes`/`pp.funBinderTypes`/`pp.coercions.types`,
inline instances are still rejected (round 3), and bound instances are rejected too (E5). What
the annotated print can still hide is limited to:

* proofs, shown as `⋯` (irrelevant to meaning);
* universe levels;
* implicit arguments.

I looked for an implicit argument that changes a value and is not fixed by the types of the
explicit arguments or by the expected type (`default`, `[]`, `cast`, `Nat.rec` motives,
`Classical.choice`, …) and found none that could make a disclosed body read differently from
what it computes. A forged `….match_1` (a hand-written def with that name) is disclosed with its
own body like any other. No deceptive tagged disclosure was found, so D4 stays a residual.
Disclosing the equation lemmas (`f.eq_1`, …, round-tripped like a statement) would remove the
"read with care" cases entirely, and remains the recommended hardening.

**E7 (cosmetic, fixed):** in Lean 4.34, `ConstantInfo.value?` is `none` for theorems, so the
WF auxiliary theorem `countdown._unary._proof_1` was disclosed as `:= <opaque>`. It now reads
`:= <proof>`; only its type, which is round-tripped, matters.

---

## Model level (item 6): targeted oracle cases

`docs/ASL.md` does **not** exist in this tree. No arm64 class is recorded as proved equal to the
ASL, so all of them are only tested (qemu and, in earlier rounds, Sail). I picked the three
families per architecture with the fewest oracle cases relative to their encoding space. Edge
cases were hand-derived from the Arm ARM ASL and the Intel SDM pseudocode; the derivations are
comments in `audit/round5/model/gen.py`. The references are qemu-aarch64 10.2.1 `-cpu max` for
arm64, and this host's Xeon (Sapphire Rapids) for amd64. `audit/round5/model/HandDerived.lean`
has 23 `decide` checks of `Janus.Arm64.step`/`Janus.Amd64.step` against values computed by
hand. The same words and states also run on hardware (`r5/*.hand`), and one flipped expected
value was confirmed to be rejected.

| Family | Cases | Agree (of which both fault) | Model-gap | MISMATCH |
|---|---:|---:|---:|---:|
| arm64 ADD/SUB (extended register) | 6,776 | 6,776 (1,656) | 0 | **0** |
| arm64 Advanced SIMD shift by immediate (vector + scalar) | 62,400 | 51,545 (45,273) | 10,855 | **0** |
| arm64 Advanced SIMD across lanes | 20,480 | 20,000 (18,600) | 480 | **0** |
| amd64 BT/BTS/BTR/BTC | 4,104 | 3,228 (1,026) | 876 | **0** |
| amd64 SHLD/SHRD | 4,032 | 3,616 (53) | 416 | **0** |
| amd64 BSF/BSR/TZCNT/LZCNT/POPCNT | 855 | 600 (0) | 255 | **0** |
| hand-derived states, run on hardware | 22 | 20 (3) | 2 | **0** |

### arm64

* **ADD/SUB extended register.** Every `sf`/`op`/`S`, `option` 0–7 and `imm3` 0–7 was enumerated,
  with `Rn`/`Rd`/`Rm` either 31 or ordinary, and odd SP values.
  * `Rn = 31` reads SP. `Rd = 31` writes SP for ADD/SUB and the zero register for ADDS/SUBS.
  * 32-bit `UXTX`/`SXTX` read only `Rm<31:0>` (`len = Min(len, N - shift)`).
  * `imm3 = 5..7` and `opt ≠ 00` are UNDEFINED, and both sides fault.
* **Shift by immediate.** Every `Q`, `U`, `immh` 1..15, `immb` and opcode was enumerated, so every
  shift amount at every element size was covered, including `shift = esize`.
  * `SSHR #esize` gives the sign. `USHR`/`USRA #esize` give or add 0, and `SRI #esize` leaves
    `Vd` unchanged.
  * `Q = 0` with `immh<3> = 1` is reserved, and both sides fault.
  * `SHRN2`/`SSHLL2` use the upper half, and the `Q = 0` forms zero bits 127:64.
  * The gaps are opcodes the model does not decode (rounding and saturating shifts, fixed-point
    conversions, the scalar forms).
* **Across lanes.**
  * `SADDLV`/`UADDLV` widen without wrapping, and `SMAXV`/`UMAXV` pick different winners on
    `0x80` vs `0x7f`.
  * `size = 11` and the `2S` forms are reserved, and both sides fault.
  * The gaps are the FP across-lanes forms.

### amd64

* **BT family.**
  * With a register destination, the bit offset is taken modulo the width, for register and
    imm8 offsets (33, 2^31, 2^63, −65, imm8 up to 255).
  * `LOCK` is accepted only on memory `BTS`/`BTR`/`BTC`.
  * The memory form with a **register** offset (signed bit-string addressing,
    `EA + (w/8)·(off SAR log2 w)`) is rejected by the model. All 876 of its cases are
    conservative gaps; out of the buffer, both sides fault.
* **SHLD/SHRD.**
  * A masked count of 0 still writes, and zero-extends a 32-bit destination.
  * A count of 16 at 16 bits gives `dest = src`, with `CF = DEST[0]`.
  * `OF` is compared only at count 1, where it is defined.
  * The gaps are the 16-bit counts 17–31, which the SDM leaves undefined (`undefinedResult`).
* **Bit counts.**
  * A zero source to `TZCNT`/`LZCNT` gives the operand size with `CF = 1`, and `POPCNT` clears
    the other flags.
  * `BSF`/`BSR` of 0 are deliberate gaps.
  * The 16-bit `TZCNT`/`LZCNT`/`POPCNT` forms are not decoded, which is a coverage note, not a
    soundness one.

No model file was changed.

---

## Regression status

With this branch's changes, all of these pass: `scripts/verify-examples.sh`,
`scripts/verify-amd64-examples.sh`, `audit/run-all.sh`, `audit/round2/run-round2.sh`,
`audit/round3/run-round3.sh`, `audit/round4/run-round4.sh`, `audit/round5/run-round5.sh` and
`go test -timeout 50m ./cmd/...`.

Round 4's P1 (the round-2 MEDIUM-1 `DFRepro` row) is resolved on this base. The merged round-2
commits changed the row's expectation: the repro's `DF = 0` state makes the theorem honest, and
`JanusTests.Amd64.df_backward_not_forward` checks the `DF = 1` case. `run-round2.sh` now exits 0.

## Reproduce

```
audit/round5/run-round5.sh                 # all rows, including the oracle rows (SKIP_MODEL=1 skips them)
audit/round5/model/run-model.sh            # the model-level rows only (about a minute)
```
