# Changelog

## v0.4.0 (unreleased)

**BREAKING: `Ensures` and its sibling forms evaluate the precondition BEFORE the return address is installed.**
No precondition can restrict the caller's return address any more, by construction. This closes the known gap of
v0.3.3 (a precondition that pins `[RSP]` on amd64 in a spelling the auditor's syntactic rule did not recognise, or
`X30` on arm64, where there was no rule at all).

### What changed

Per ISA (`Janus.GoABI`, `Janus.Amd64.GoABI`):

- `State.setRet s ret` installs the return address: arm64 sets `X30 := ret`; amd64 writes the 8-byte little-endian
  word `ret` at `[RSP]` (what `CALL` pushes). Nothing else changes; the memory regions (accessibility) are kept.
- `CallSetup0 entry args s` is `CallSetup` without the return-address field (arm64: `pc`, `len`, `args`; amd64:
  `rip`, `zero`, `len`, `args`, `df`). `CallSetup0.setRet : CallSetup0 .. s → CallSetup (p.withExit ret) .. (s.setRet ret)`.
  (arm64 `CallSetup0` has the field `len : args.length ≤ numIntRegs` that amd64 `CallSetup` always had: arguments live
  in `R0 .. R15`, never in the link register that `setRet` overwrites.)
- `Ensures`, `EnsuresWithin`, `EnsuresGo`, `EnsuresGoX` and `RunsAtLeastOnCall` (and so `EnsuresResults`) are now

  ```
  ∀ s, CallSetup0 entry args s → pre s → ∀ ret, RetAddr p ret →
    Returns (p.withExit ret) (s.setRet ret) (fun s' => ABIReturn (s.setRet ret) s' ∧ post (s.setRet ret) s')
  ```

  `pre` sees `s` (the call state before the return address exists); `post`, `bound`, the classifier, `ret`/`pan`/`gox`
  see `s.setRet ret`, so every existing postcondition keeps its meaning. `Summary` (callee contracts) is unchanged.
- Bridges: `Ensures.of_old`, `EnsuresWithin.of_old`, `EnsuresGo.of_old`, `EnsuresGoX.of_old`,
  `RunsAtLeastOnCall.of_old` (a proof of the old statement plus `hinv : ∀ s ret, RetAddr p ret → pre s → pre (s.setRet ret)`
  give the new one), and the reverse `Ensures.toOld` (the old-shaped statement for a state that already holds `ret`;
  arm64 also needs `args.length ≤ numIntRegs`, an auto-parameter closed by `simp [numIntRegs]`). `Ensures.toSummary`,
  `Ensures.toSummaryIn` use it, so their statements are unchanged (arm64: they gain the auto-parameter `hlen`).
- Simp lemmas `setRet_*` (registers other than `X30`, `SP`/`RSP`, pc/rip, flags, xmm, mem regions, `accessible`
  unchanged); amd64 `readLE_setRet_of_disjoint` (a read of `[a, a + n)` outside `[RSP, RSP + 8)`), `readLE_setRet_sp`
  (the return slot holds `ret`), `bytes_setRet_of_outside`; `CallSetup.setRet_eq`; `Memory.writeLE_readLE_self`.
- Tactics: `janus_pre_setRet` / `janus64_pre_setRet` prove `hinv` for the common preconditions; `janus_ensures_old` /
  `janus64_ensures_old` do `refine Ensures.of_old (by janus_pre_setRet) ?_` (or the `Within`/`Go`/`GoX`/`RunsAtLeast`
  form), leaving the old-shaped goal. Optional `[defs]` lists proof-local definitions to unfold.
- **Auditor:** the amd64 `[RSP]`-word rule (`the precondition constrains the memory word at the entry RSP`, and its
  helpers `isSpRead`, `constReadsSp`, `mentionsSpWord`, `ensuresPres`) is removed: the precondition cannot see the
  return address, so no spelling of a restriction exists. `ErrorfAmd64.RetLow` as a precondition conjunct is therefore
  accepted (and harmless). The witness rules are unchanged in meaning: the statement of a witness exhibits
  `CallSetup0 … s`, the precondition at `s`, a `RetAddr` and the returning run at `s.setRet ret`; the matching is
  still definitional unification of the unfolded conclusion's premises and final run claim. The amd64 undefined-value
  rule accepts `State.setRet s ret` (it changes only the memory).
- The v0.3.4 items below are part of this release.

### The other main-theorem forms (same change)

Every other form that quantified `∀ ret, RetAddr p ret → ∀ s, <setup> s → pre s → …` is now
`∀ s, <setup without the return address> s → pre s → ∀ ret, RetAddr p ret → <run claim from s.setRet ret>`, with `s.setRet ret` in
the run claim, the post, the class and the relocation, and an `.of_old` bridge:

| Form (module) | Ret-free setup | Return address |
| --- | --- | --- |
| `GoABI0.Ensures0`, `EnsuresResults0` (both ISAs) | `GoABI0.CallSetupF` | arm64 `X30`, amd64 `[RSP]` |
| `CABI.CEnsures`, `CEnsuresResults`, `CEnsuresA`, `CEnsuresR` (both ISAs) | `CABI.CCallF`, `CABI.CCallAF` | arm64 `X30`, amd64 `[RSP]` (System V) |
| `FFI.EnsuresC`, `FFI.CEnsuresC` (both ISAs) | `GoABI.CallSetup0`, `CABI.CCallF` | as above |
| `Kernel.EnsuresK` (both ISAs; `pre s k`, `post s k s' k'`, `onExit s k`) | `GoABI.CallSetup0` | as above |
| `Contracts.Stack.EnsuresGrow`, `StackAmd64.EnsuresGrow64` (new argument `caller`) | `GoABI.CallSetup0` | as above |

Notes: `CCallAF` (classified C calls) states the by-reference argument copies of the amd64 call apart from `[RSP, RSP + 8)`
(`ArgAtF`; System V never passes a copy by reference, so nothing changes for a real prototype); on arm64 it needs no extra
condition (`assignAll_low`: no argument lives in `X30`). Each form also has the `.of_old` bridge, the `toOld` direction for
`EnsuresC`/`CEnsuresC` (used by `CgoCall.refines`/`CgoCallback.refines`), `CCall.toF`; `Ensures0.of_summary`,
`of_summary0`, `CEnsures.of_summary`, `CEnsuresA.of_summary` take their call-site hypotheses on the pre-setRet state
(`hpre : … → spre (s.setRet ret)`). `EnsuresC.of_ensures` no longer needs the arm64 `hlen`. `janus_ensures_old` and
`janus64_ensures_old` dispatch on all these heads; `janus_pre_setRet_k` / `janus64_pre_setRet_k` are the variants for `EnsuresK`
(`pre s k`) and `janus_pre_setRet_c` / `janus64_pre_setRet_c` for `EnsuresGrow` (`hinv` also gets `caller (s.setRet ret)`). `scripts/dev/migrate-v040.py` rewrites them all.

### Migration guide

A proof of the old statement migrates by adding ONE line, and its witness by a mechanical rewrite
(`scripts/dev/migrate-v040.py FILE.lean` does both for the usual shapes):

```
-- arm64 and amd64 before                         -- after (arm64; amd64: janus64_ensures_old)
theorem correctness : Ensures P E [x, y] pre post := by      theorem correctness : Ensures P E [x, y] pre post := by
  intro ret hret s hs hpre                                      janus_ensures_old
  janus_intro hs                                                intro ret hret s hs hpre
  janus_run                                                     janus_intro hs
                                                                janus_run
```

`janus_ensures_old` is `refine Ensures.of_old (by janus_pre_setRet) ?_`; the remaining goal is the old statement, so the
old proof is unchanged (`intro ret hret s hs hpre` still takes the state with the return address installed). The same
line works for `EnsuresResults`, `EnsuresWithin`, `EnsuresGo`, `EnsuresGoX`, `RunsAtLeastOnCall`, `Ensures0`/`EnsuresResults0`, `CEnsures`,
`CEnsuresA`, `EnsuresC`, `CEnsuresC`, `EnsuresK` (`intro ret hret s k hs …` follows) and `EnsuresGrow(64)`. A proof that is not
introduced by `intro ret hret …` (a hand-written `fun ret hret s hs hp => …`) uses the bridge lemma directly:
`Ensures.of_old (by janus_pre_setRet) (fun ret hret s hs hp => …)`.

Witnesses (`Witness.nonvacuous` and friends): `CallSetup (P.withExit ret) E args s` becomes `CallSetup0 E args s` (ABI0
`GoABI0.CallSetup0 (P.withExit ret) E args nres s` becomes `CallSetupF E args nres s`, `CCall` becomes `CCallF`, `CCallA` becomes `CCallAF`;
the ABI0/C setup proofs drop the return-address field as well)
(the setup lemma drops the return-address field `⟨rfl, rfl, …⟩` on arm64: `⟨rfl, by decide, …⟩` with the `len` field; amd64:
`⟨rfl, by decide, rfl, by decide, args, rfl⟩` becomes `⟨rfl, rfl, by decide, args, rfl⟩`), the run claim is stated at
`s.setRet ret` (`Returns (P.withExit ret) (s.setRet ret) fun s' => ABIReturn (s.setRet ret) s' ∧ …`, with `s` in the
post replaced by `s.setRet ret`), and the proof term applies the theorem as `thm args s0 setup hpre ret hret` (was
`thm args ret hret s0 setup hpre`). The precondition conjunct of the witness stays at `s`.

Direct style (no bridge; for a new proof or a precondition the bridge cannot discharge): `intro s hs hp ret hret`,
`have hs1 := hs.setRet ret` (arm64; amd64: `hs.setRet hret.lt64`) is the old-shaped `CallSetup (p.withExit ret) … (s.setRet ret)`,
`generalize hsr : s.setRet ret = s1 at hs1 ⊢`, state what the run needs about `s1` from the precondition on `s` with the
`setRet_*` simp lemmas, `clear hsr`, then `janus_intro hs1` and `janus_run` as before (see `test/lean/JanusTests/RetAddr.lean`,
`a4c` and `m11`: the old attack statements, proved for every return address).

`janus_pre_setRet` discharges `pre s → pre (s.setRet ret)` by rewriting `s.setRet ret` away:
- arm64: every register but `X30`, `SP`, the flags and the memory are unchanged, so everything but a statement about
  `X30` goes through. A precondition that pins or bounds `X30` is not invariant: the tactic fails, and the theorem no
  longer needs it (state it without the `X30` conjunct; it was a restriction of the return address).
- amd64: `setRet` changes only the 8 bytes `[RSP, RSP + 8)`. Reads of memory at `RSP + k` with `k ≥ 8` (stack
  arguments, `StackWords`), reads below `RSP`, and reads at a pointer the precondition keeps apart from the return slot
  (an `Apart`/`Disjoint`/`Outside` conjunct over a window containing `[RSP, RSP + 8)`) are discharged by `omega` from
  the precondition. A read at a pointer the precondition only places in a buffer (`Buffer`, `Ptr`, `accessible`), or
  outside the callee's writable windows (`calleeStack64` leaves the return slot out), needs an extra conjunct
  `Apart ptr n RSP 8` (or `Disjoint`) in the precondition. A precondition that reads `[RSP]` itself keeps its reads
  of `ret`: `[RSP] < 2^47` is derived from `RetAddr`; a pin (`[RSP] = 0`, a bound on `ret`) fails, correctly.
- Post conditions that read the initial memory at the return slot see `ret`, as the callee does.
- Predicates that live in other modules or are proof-local are not unfolded by default: pass them, e.g.
  `janus64_ensures_old [Janus.Amd64.CABI.CStack]`, `janus_ensures_old [GPre]`. (The default list is the `GoABI` predicates.)
- **amd64 `TlsG`** reads the slot `[fsBase - 8, fsBase)`: state `fsBase ≤ RSP ∨ RSP + 16 ≤ fsBase` as a precondition conjunct (`omega` and
  `tlsG_setRet_iff` use it). `StackGuardOK` needs nothing (see below).
- **`EnsuresGrow` / `EnsuresGrow64` gain an explicit `caller` argument.** Their old precondition walked the caller's frames
  from `X30` / `[RSP]` (`Chain … (s.regs 30).toNat …`: stack growth copies the stack and needs the caller to be a real Go
  frame). That is a statement about the return address, and it must not hide in `pre`. The form is now
  `EnsuresGrow p reloc entry args pre caller post` =
  `∀ s, CallSetup0 entry args s → pre s → ∀ ret, RetAddr p ret → caller (s.setRet ret) → GrownReturns (p.withExit ret) reloc (s.setRet ret) (fun s' => post (s.setRet ret) s')`:
  `pre` is ret-independent (evaluated before the return address is installed), `caller` is evaluated WITH the return address
  installed and is printed in the statement. The verify report discloses it:
  `Assumes of the caller (return address / frame chain): <caller>` (field `callerAssumption` of the JSON report). The witness
  rule is unchanged: the witness states the caller conjunct (`caller (s.setRet ret)`) at its instantiation, and the pairing
  unifies it like any premise.
  **Migration (manual; the script only warns):** move the `Chain`/`framesCls` conjuncts out of the precondition into a
  `GCaller FT hi fs s`, make `lo hi fs` parameters of the theorem (an `∃` in the old precondition is a `∀` outside the new
  statement), keep the old proof as `correctness_old` (the old-shaped statement), and derive the new theorem with
  `EnsuresGrow.of_old_with (Pold := <old precondition>) (hinv) correctness_old`; `hinv` rebuilds the old precondition at
  `s.setRet ret` from `pre s` and `caller (s.setRet ret)`. The alignment and range facts of `X30` / `[RSP]` come from `RetAddr`.
  `BigLocal`, `SumRec` and `HoldPtr` (both ISAs) are migrated this way and verify with their witnesses; on amd64 the
  slot-invariance lemmas `StackAmd64.gStack_setRet`, `noStackPtr_setRet`, `rtView_setRet`, `inRanges_slot` do the memory part.
- **amd64 `StackGuardOK` carries the apartness of the guard word from `[RSP, RSP + 8)`** (new field `apart`; BREAKING for the
  3-field pattern `⟨noWrap, readable, below⟩`: it is now `⟨noWrap, readable, below, apart⟩`). `StackGuardOK (s.setRet ret) adj ↔
  StackGuardOK s adj` is a simp lemma (`stackGuardOK_setRet`), so `janus64_pre_setRet` needs no extra conjunct. `TlsG` keeps its
  three fields: `tlsG_setRet_iff` needs `fsBase ≤ RSP ∨ RSP + 16 ≤ fsBase` (a precondition conjunct, as in `proofs-sys/amd64/Pid`).
  The `RTPre`/`CallerOK`/`PanicPre`/`EqPre` families discharge the new field from their `Disjoint (g + 16) …` conjunct.

### v0.3.4 items (merged)

Auditor and CLI fixes requested by fv-modexp.

- **`StackWords` is accepted as a stack-argument form.** (The amd64 `[RSP]`-word rule it was added to is removed in
  this release; `StackWords s skip words` reads only `RSP + 8 + skip + 8 * i`, so `janus64_pre_setRet` discharges it.)
- **The statement round-trip check tries a print with binder types** (`pp.funBinderTypes`) after the plain and the
  `pp.numericTypes` prints. Before, `∃ yp : W64, … = yp.toNat` printed as `∃ yp, … yp.toNat` and was refused with
  "the printed statement does not elaborate back". The annotated print must still elaborate back to a definitionally
  equal statement.
- **`janus --version`** prints the release (`janus 0.4.0 (extractor 0.2.0)`). Before, it printed only the
  extraction-format version, `0.2.0`.
- Round n9: b17 (`StackWords`) and b20 (the `∃`-bound `yp.toNat` statement) are controls that verify. b18 and b19
  were blocked by the removed `[RSP]` rule: now see below.

### Red-team round `roundretaddr` and round n9

- Phase-1 migration scope: the `janus_*`/`Within` tests of `test/lean/JanusTests`, round n9 and `rounderrorf`'s a9/a10, and
  six pilot examples (`Add`, `Max`, `LoadThird` on both ISAs). The other examples, the other red-team rounds
  (`test/redteam`), `models/asl` (`Ensures.toASL` is updated but not rebuilt:
  Sail is not part of this tree's build) and the docs' code snippets still hold the old shape.
- Phase 1b/1c: pilots `proofs-cgo/{arm64,amd64}/CAdd` and `arm64/GoAdd`, `proofs-sys/{arm64,amd64}/Pid` (`EnsuresK`),
  `proofs/{BigLocal,SumRec,HoldPtr}` and `proofs-amd64/{BigLocal,SumRec,HoldPtr}` (`EnsuresGrow` with `caller`),
  `asm/proofs/{arm64,amd64}/AddAsm` (`Ensures0`); `cmd/janus` tests (`asl_test.go`, `deps_test.go`, `hardening_test.go`, `round2_test.go`,
  `within_test.go`) updated to the new shape.
- New `test/redteam/rounds/roundretaddr/` (both ISAs) and `test/lean/JanusTests/RetAddr.lean`: preconditions that pin
  the return address (`(s.regs 30).toNat = 0`, `readLE RSP 8 = 0`, the probe forms `RspBypass64.lean` and `LrPin.lean` of
  v0.3.3) are accepted and harmless: the theorem still covers every admissible `ret`.
- Round n9 rows whose expectation changed (the rule that blocked them is gone, and none of them restricts the return
  address any more): b1-b7, b9-b11, b13-b16, b18, b19 were `blocked`, are now `Verified` (audit-only). b8, b12, b17, b20
  stay `Verified`.

## v0.3.3 (2026-11-13)

Auditor fix (PR #4): the amd64 `[RSP]`-word rule (a main theorem's precondition must not constrain the caller's
return address at `[RSP]`) refused every statement about a function with Go stack arguments: ABIInternal passes
the integer argument words beyond the registers at `RSP + 8, RSP + 16, …`, and any `readLE` whose address mentioned
`RSP` counted as a read of `[RSP]`. A read whose address is exactly `(RSP).toNat + k` with a numeral `k ≥ 8` now counts
as a stack-argument read (it starts above the return-address word). Every other address that mentions `RSP` (offset
`< 8`, subtraction, a non-numeral offset, nested arithmetic) is still treated as a read of `[RSP]`.

- Round n9: b12 (control: two stack-argument words, verifies) and b13–b16 (offset 4, `8 - 8`, `RSP - 4`, a definition
  mixing an argument read with a `[RSP]` read; all blocked, pinned).
- **Known gap, not fixed in this release (present in every release since the rule was added):** the rule recognises
  `[RSP]` reads syntactically, so a statement can constrain the word without such a read: through an alias
  (`∃ sp, (s.regs 4).toNat = sp ∧ s.mem.readLE sp 8 = …`, a `∀`/`let` alias, two inequalities), a byte read
  (`s.mem.bytes`), `RSP` pinned to a constant and the word read at that constant, or an equation on the whole memory.
  Such a precondition restricts the caller's return address the reader does not see (e.g. to `0`, so that a jump to a
  nil code pointer counts as a return). It needs a deliberately misleading statement; read the precondition of a
  theorem you rely on. The same holds on arm64, where the return address is in `X30` and there is no rule at all:
  `(s.regs 30).toNat = 0` in a precondition is accepted. A sound fix (evaluate the precondition before the return
  address is installed, BREAKING) is planned for v0.4.0.

## v0.3.2 (2026-11-13)

Bug fix (PR #3): janus's own compile of a consumer package's modules (olean provenance) could reuse a stale
stored olean. The trusted olean store key of a module covered its source and its direct imports' olean bytes
only. An olean does not cover its own imports, so a change deep in the import closure (the body of a reducible
definition) could leave an intermediate olean byte-identical while a module above it elaborated against the old
body. The stale olean was then reused, and the kernel replay rejected it: **fail closed, never a wrong
verdict**, but such rows failed in warm caches until the store was wiped.

- The key now also covers each import's own key, hence the whole closure (`cmd/janus/provenance.go`). Key
  format `janus-own-olean-v3`: existing store entries are rebuilt once.
- `TestOleanStoreKeyTransitive`: Deep → Mid → Add, where Mid's olean is byte-identical across a change of Deep's
  body; all three must recompile (fails before the fix: only Deep and Mid did).

## v0.3.1 (2026-11-12)

`lakefile.toml` still says version 0.3.0: it is embedded in `janus` (verifier identity), and the release ships
the exact gated tree.

### BREAKING: the allocation contracts keep the type descriptor out of the callee's stack window
**BREAKING (runtime-contract preconditions; consumers must re-discharge).** The allocation contracts'
preconditions (`NewobjectPre`, `MakeslicePre`, `MallocgcPre` for `typ ≠ 0`, `GrowsliceArgs`, and their amd64
twins `…Pre64`, `GrowsliceArgs64`) now also require the type descriptor to lie outside the callee's stack
window: `Outside (s.regs 0).toNat 16 (calleeStack s stack 1|3)` (arm64; `s.regs 1` for `mallocgc`, `s.regs 4`
for `growslice`; amd64 `RAX`/`RBX`/`RSI`, `calleeStack64`). `GrowsliceOld`/`GrowsliceOld64` now take the stack
bound and require the old elements outside the window.
Why: the pinned go1.26.10 `runtime.makeslice` pushes its frame before it reads `et.Size_` (arm64
`MOVD.W R30,-48(RSP)`, `MOVD R29,-8(RSP)`; amd64 `PUSHQ BP`), so for a state with the descriptor inside
`[SP-56, SP-40)` the real runtime does not do what the contract says. The old contracts held there, so every
theorem assuming them was vacuous for the real binary in those states (no real caller passes such a descriptor).
The change reaches the non-live contracts (`NewobjectContract`, `MakesliceContract`, `MallocgcContract`,
`GrowsliceContract`) and the live ones (`…LiveContract`, the SC variants) through their shared `…Pre`.
`TypedMemmove`/`TypedMemclr` (+Live, +RtPre64 reads) already had this conjunct.
Migration: at a call site, prove `Outside et 16 (calleeStack s stack n)` for the descriptor. A real descriptor
is `.rodata`, which is not writable: with `janus_data hd [hw]` (the call window `hw`) the context has
`a + n ≤ base ∨ base + len ≤ a` per data object, and `simp only [calleeStack, outside_cons, outside_nil,
and_true]; omega` closes it (arm64 and, with `calleeStack64`, amd64). For a concrete witness state: `by simp only
[calleeStack, outside_cons, outside_nil]; decide` (`Outside` has no `Decidable` instance; the fv-uint256 call-site
modules define a scoped one). `growslice`: also the old array (a live object, `hL2W`-style fact) outside the window.
Tests: red-team round `test/redteam/rounds/roundalloc` (the descriptor-in-window state satisfied the old
precondition, falsifies the new one; ten drop-the-conjunct mutants flip; rodata control passes);
`LiveSat*`/`AllocSat*`/`MallocSCSat*` witnesses carry the conjunct.

### Additive: zero-byte `memmove` and `makeslice` contracts (PR #2)
New runtime contracts for zero-byte runtime calls, `memmove` and `makeslice` (additive: no existing statement, proof
or auditor rule changes).

- `MakesliceZeroLive` (arm64, `Janus/Contracts/Live.lean`) and `MakesliceZeroLive64` (amd64, `LiveAmd64.lean`): a call
  of `runtime.makeslice(et, len, cap)` with `et.Size_ · cap = 0` returns with the live set and the budget unchanged
  (`ZeroAllocRet` / `ZeroAllocRet64`; the result pointer is unconstrained). `MakesliceLiveContract` appends an empty
  range at an unconstrained pointer to the live set in that case, after which a caller can state neither `LiveExt`
  nor a later call's `LiveSep`. The precondition is `MakesliceLiveContract`'s with cost `0`, the zero size, and the
  type descriptor outside the callee's window. `MakesliceZeroLive(64).of_codeIn`.
- Justification: the pinned `makeslice` calls `mallocgc(0, …)`, which returns `&runtime.zerobase` first thing
  (`malloc.go:1075`). `LiveSat.makesliceZeroLive_pinned` / `LiveSatAmd64.makesliceZeroLive64_pinned` run the pinned
  go1.26.10 `makeslice` and `mallocgc` themselves in the model, for every runtime hypothesis.
- `zeroAllocRet_of_frame` (`LiveCall.lean`), `zeroAllocRet64_of_frame`, `MakesliceZeroLive.of_live` /
  `MakesliceZeroLive64.of_live` (a live-contract stub is a zero-byte witness when the invariant ignores empty live
  ranges), `LiveSat.toyR_dropEmpty`, `inRs_append_empty`, `view_append_empty`; SAT witnesses
  `makesliceZeroLive(64)_satisfiable` (both makeslice contracts on one stub).
- Both contracts are on the auditor's pinned-contract list. JanusTests.MakesliceZero (incl. a red team: a stub that
  charges the budget for a zero-byte request is refuted, `¬ MakesliceZeroLive …`, both ISAs). docs/RUNTIME-CONTRACTS.md:
  "Zero-byte allocations".

New runtime contract for `memmove` of zero bytes:

- `MemmoveZeroLive` (arm64, `Janus/Contracts/Live.lean`) and `MemmoveZeroLive64` (amd64, `LiveAmd64.lean`): a call of
  `runtime.memmove(dst, src, 0)` returns as a `MemmoveLive` call does, with an empty written range, under only the ABI
  and live parts of the precondition (nothing about `dst` or `src`). Go's `copy` calls `memmove` with `n = 0` and a nil or
  `zerobase` pointer, which `MemmoveLive`'s precondition cannot accept.
- `MemmoveLive.withZero` / `MemmoveLive64.withZero`: the two contracts give the `memmove` summary whose precondition is
  `n = 0 ∨` the destination and source facts. `LiveMemRet.of_nil`, `LiveMemRet64.of_nil`, `liveMemRet_none`,
  `liveMemRet_none64`, `MemmoveZeroLive(64).of_codeIn`.
- Justification: the pinned runtime's `memmove` returns before any memory access for `n = 0` (arm64 `CBZ R2, copy0`;
  amd64 `TESTQ BX, BX; JEQ move_0`). `LiveSat.memmoveZeroLive_pinned` / `LiveSatAmd64.memmoveZeroLive64_pinned` run the
  pinned go1.26 code in the model and prove the contract for every runtime hypothesis; they are the SAT witnesses.
  `MemmoveUptoSat(Amd64).memmoveUptoWithZero(64)_satisfiable`: both premises of `withZero` hold of one stub.
- Tactics `janus_live_memmove_zero` / `janus64_live_memmove_zero` prove the contract for a stub that returns without a
  memory access when `n = 0` (e.g. `LiveStub.memmoveUptoSeg`).
- Both contracts are on the auditor's pinned-contract list (`Janus/Tools/Audit.lean`, round 9 SAT row).
- docs/RUNTIME-CONTRACTS.md: "Copies of zero bytes".

## v0.3.0 (2026-11-12)

Instruction-count bounds. **Auditor change** (new accepted statement shapes and one new rule; every existing
rule is unchanged), so the result and framework caches rebuild once.

- `GoABI.ReturnsWithin`, `RunsAtLeast`, `EnsuresWithin`, `RunsAtLeastOnCall` (arm64 `Janus/GoABI.lean`,
  amd64 `Janus/Amd64/GoABI.lean`): at most `n` / at least `m` instructions executed by the model
  (`Program.run` fuel; not CPU cycles; runtime-call stubs are not counted). Kernel-checked lemmas
  (no axiom, `sorry` or `native_decide`): `ReturnsWithin.returns`, `.mono`, `.post_mono`, `Returns.within`,
  `RunsAtLeast.mono`, `RunsAtLeast.le_of_returnsWithin`, `exact_count`, `EnsuresWithin.ensures`,
  `.mono_bound`, `.mono`, `RunsAtLeastOnCall.mono`.
- `janus_run` / `janus64_run` prove `ReturnsWithin n` and `RunsAtLeast m` goals by fuel-counted stepping
  (`ReachesW`, `Going`; a bound one too small or too large is not provable and the tactic says so).
- Auditor: `EnsuresWithin` is an Ensures-family main (same Extracted.program mention, contract, call-site,
  binder and `[RSP]`-word rules; through def-wrapped statements too); `ReturnsWithin`/`RunsAtLeast` are run
  claims; the tied witness of an `EnsuresWithin` main may use `Returns` or `ReturnsWithin`; a
  `RunsAtLeastOnCall` witness must also contain a returning run from the same state; the instruction bound
  may not mention the execution of the program (U-BOUND-PURE).
- Examples: `Max` (arm64, amd64) gets `within` (N = 4) and `atLeast` (M = 3) with witnesses; `JanusTests.Within`;
  red-team round `test/redteam/rounds/roundwithin`.
- `lakefile.toml` version 0.3.0 (it still said 0.1.0).
- Includes everything in v0.2.1 below (PR #1: module-system consumer dependencies, olean store v2,
  and the `import all` parser fix).
- Disclosed (pre-existing since v0.1.0, fixed in v0.3.1): the live allocation contracts (makeslice, newobject,
  mallocgc with a type, growslice; both ISAs) do not keep the type descriptor outside the callee's stack
  window, so the pinned runtime does not meet them for a descriptor in the slots `makeslice` pushes before
  reading it. See docs/RUNTIME-CONTRACTS.md ("Known gap").
- Known limitations: `janus verify --asl` transfers `Ensures` theorems only; an `EnsuresWithin` theorem is
  rejected there ("not `Janus.GoABI.Ensures`"); derive the plain `Ensures` with `EnsuresWithin.ensures` and
  transfer that. `janus_run` proves numeral bounds only (no state-dependent budget from a loop invariant), and
  has no `calls`/`join` in bound goals. A def-wrapped `EnsuresWithin` statement is rejected like a def-wrapped
  `Ensures` (the statement must mention `Extracted.program`).

## v0.2.1 (2026-11-12, maintenance release, tagged separately on branch release/v0.2.1)

Bug fix for consumer packages whose dependencies use Lean's module system (`module` header,
`public import`), such as ethereum/EthLib. Before, `janus verify --proof-root` failed at
"Stage: olean provenance" for them; it never produced a wrong verdict.

- janus's own compile of the consumer closure keeps every module-data part `lean -o` writes
  (`.olean`, `.olean.server`, `.olean.private`, `.ir`), not only the `.olean`.
- The trusted olean store records and authenticates each part (entry format v2; v0.2.0 entries are
  rebuilt once). A module's identity covers all its parts; olean-only modules keep their keys.
- The import-header parser accepts the module system's modifiers before `import`
  (`public import`, `public meta import`, `private import`) and `all` after it.
- `import all` is always read as the modifier, as Lean 4.34.1 reads it: the module name follows,
  across newlines and comments, and `import all` without a module is refused. Found by red-teaming
  this release: an intermediate version of the parser read `import all` followed by a newline as an
  import of a module named `all`, which would have left the real import out of a module's key. The
  incremental item keys' header parser (`incr.go`) is fixed the same way, and no longer treats
  `runtime` as a modifier.

## v0.2.0 (2026-11-10)

Repository restructure and an arm64 host-build fix. **No Lean API, auditor rule, gate, red-team
expectation or safety check changed.** Lean module names (`Janus.*`, `JanusTests.*`, `Oracle.*`) are
unchanged; consumers need no source edits. See `docs/MIGRATION.md` ("v0.1 to v0.2") and
`Structure/README.md`.

- New layout: `models/{asl,x86}` (was `JanusASL/`, `JanusX86/`), `validation/` (was `oracle*/` and
  `Oracle/`, organised as `hardware-comparison/`, `reference-models/`, `model-runner/`),
  `test/lean` (was `JanusTests*`), `test/redteam` (was `audit/`, rounds under `rounds/`),
  `scripts/{gate,build,verify,validation,dev,archive}`, `docs/{design,audit,validation,dev-notes,assets}`.
  History is preserved (`git mv`). One-shot generators (`jx1_*`, `jx2_*`, `break-demo.sh`,
  `incr-sample.py`) moved to `scripts/archive/`.
- `Janus.lean`, `Janus/`, `framework.go`, `identity_sentinel.*`, `go.mod`, `go.sum`, `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain` stay at the root (Lake modules and `go:embed`).
- `janus` now builds for linux/arm64 hosts: `blockers_amd64.go` / `sweep_amd64_test.go` lost their
  `_amd64` file-name suffix (now `blockers_x86.go`, `sweep_x86_test.go`).
- The verifier identity changes (embedded sources moved), so result and framework caches rebuild once.
- The validation Go modules are renamed to their directories
  (`github.com/Giulio2002/Janus/validation/hardware-comparison/{arm64,amd64}`).
- Added `Structure/README.md` (repository map) and this changelog. Removed the stray `.x1` / `.x2`.

## v0.1.0

First tagged release (tag `v0.1.0`, commit `77054be0`): Lean framework and `janus` CLI for formally
verifying compiled Go machine code (arm64, amd64).

- Mandatory non-vacuity witnesses: a returning run from a state satisfying the precondition, a
  call-site state for every runtime-contract hypothesis, strict by-name pairing, anchoring for
  Panics/Faults/Traps conclusions; narrow, labelled exemptions for refutations and run-free statements.
- Hermetic proof sandbox: allowlist root, environment allowlist, hidden cache keys, fds above 2 closed.
- `verify-batch` with witness companions and stale-report withdrawal; speed batch 14; provenance fix.
- ~840 pinned red-team expectations; trust model in `docs/SOUNDNESS.md`.
- Known limitations: a witness shows some run returns, not that every contract call site is reachable
  on it (KA1); main theorems with class-typed binders cannot be witnessed; red-team controls N45/N53
  are rejected conservatively; accepted sandbox nondeterminism: clock, random bytes, uid, host
  `/proc/{cpuinfo,meminfo,loadavg}`.
- Not shipped: linux/arm64 host binaries (fixed in v0.2.0).
