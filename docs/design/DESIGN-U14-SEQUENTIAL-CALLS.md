# U14: two or more runtime contract calls on one path (design note)

Status: design + scratch prototypes. **No trusted-base change is proposed or made.** Recommendation:
use the *live* contracts that are already pinned in `Janus/Contracts/Live.lean` (`LiveAmd64.lean`,
`LiveSat*.lean`); they are option (c) below, and they already cover the call sequences of
`(*Int).IntoBig` / `ToBig`, `Hex`, `Dec`/`String`/`PrettyDec`, `MarshalJSON`/`MarshalText` on both ISAs. One
gap remains (a live `convT64` / `convTstring`, needed by `Value` only); it is described at the end as a
design only.

Scratch prototypes (not committed, not trusted code): `/srv/janus-ops/u14-protos/`.

## 1. The request

FV-C (uint256 `IntoBig`, `ToBig`): `runtime.newobject` (`new(big.Int)`, or the `[4]Word` array) is followed on
the same path by `runtime.gcWriteBarrier2` (the pointer store `*b = p`, `abs.ptr = words`). With the single-call
contracts (`NewobjectContract`, `WbContract`, `RtContract`, each taking its own readiness `H : RtReady`),
`Ready H rt args s` is required at the call and "readiness is not handed back"
(`docs/RUNTIME-CONTRACTS.md` section 5), so the second call's readiness would have to be assumed for a memory
that does not exist at the theorem's entry.

## 2. Why readiness is not handed back (the soundness argument)

A `Summary` speaks about every state that satisfies its precondition. A contract whose postcondition
re-establishes everything its precondition needs can be applied again to its own output, without bound, from
one call state. Two things then go wrong, both found by the round 10 audit (`docs/audit/AUDIT-ROUND10.md`):

* **V2 (critical, kernel-checked)**: the map contracts handed `M.Env` back. `2^64` inserts of distinct keys (or
  `2^48 + 1` new maps) in the model's fixed finite memory contradict the model's own laws:
  `audit/round10/model/MapUnsat.lean` proves `M.Laws ∧ Assign … ∧ (one call state) → False`. Every theorem
  that assumed such a contract was vacuous (`V2a` proved a false statement about the real binary).
* **V3 (high)**: `convT64(v)`, `v >= 256`, allocates a fresh box per call; handing `R.Env` back demands
  unboundedly many disjoint boxes from any `R.Env` state, which the real runtime (finite heap, no `mmap` in the
  model, no collector) never meets. Not refutable in the kernel (a toy model meets it), but vacuous for the real
  binary.

For allocation specifically: the contract also lets the allocator change any byte of `rt`, including objects the
caller already holds (the single-call `NewobjectContract` has no live set), so even a safe handed-back readiness
would let a second allocation overwrite the first object.

So any sequential-call mechanism must (i) bound the number of allocations that readiness can pay for,
(ii) say what survives an allocation (the caller's objects), and (iii) keep every assumption on the runtime's
state a hypothesis about a *variable* of the statement, so that it cannot be instantiated into a vacuous one
(round 10 V1, the auditor rule "contracts are applied only to variables of the statement").

## 3. Options

### (a) A readiness that is a runtime-state property preserved by allocation

Statement (hypothetical): a contract kind for the barrier whose readiness is `HRoom`-like
(`WbRoom : Memory -> Prop`, "the P's write-barrier buffer has room") and an allocation contract with
`WbRoom (rtView rt s.mem) -> WbRoom (rtView rt m)` for the fields it does not touch.

* Trusted-base change: new contract statements for `newobject`/`mallocgc`/... (a second family next to
  `Alloc.lean`), a new readiness class.
* Problem 1: preserving `WbRoom` across an allocation is a claim about the real runtime that is true only when
  the allocation does not start a GC cycle or flush the buffer; the live invariant `R.inv` exists exactly to say
  "the runtime is in a state from which it serves the next call", for every runtime function at once, not for one
  field. Option (a) re-derives `R.inv` for one field and one pair of functions.
* Problem 2: it does not bound the number of allocations (V2/V3) and does not say the first object survives.
  Both would have to be added: a budget and a live set. That is `Live.lean`.

### (b) An explicit sequential-call lemma with a second consumer-supplied readiness predicate

Statement (hypothetical): `Ready H rt args s -> AllocRet … s s' -> Ready H' rt args' s'` for a user-chosen `H'`.

* The lemma is a *hypothesis about every allocator output* `m`: "after any allocation the barrier is ready".
  It cannot be discharged at the theorem's entry for a specific memory, so it is an assumption of the form
  `forall m, Post_alloc m -> H' (rtView rt m)`. Unbounded chaining (`H'` again after the barrier, then another
  allocation, ...) reproduces V2/V3 unless a budget is added; the audit then has to check, per call site, a
  second `RtReady` predicate, its budget and its live set by hand. This is more audited surface per consumer
  than (c), for the same guarantee.

### (c) The live contracts (already in the framework)

`Janus/Contracts/Live.lean` (arm64) and `LiveAmd64.lean` (`…64`): **one** `R : RtInv` is threaded through every
runtime call of a function.

```lean
structure RtInv where
  inv : Nat -> List (Nat × Nat) -> Nat -> Memory -> Prop   -- budget b, live set L, g, view
  ok  : Nat -> List Nat -> Prop                            -- requests served, by (address, args)
  rt  : List (Nat × Nat)                                   -- the runtime's private ranges
  ext : …                                                  -- inv depends only on bytes and accessibility
```

Every contract is `∀ L b, Summary p addr pre post`; for instance

```lean
def NewobjectLiveContract (p : Program) (addr stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => NewobjectPre stack s ∧ StackRoom s stack 1 ∧
      LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem (calleeStack s stack 1))
    (fun s s' => LiveAllocRet R stack 1 (fun ptr => [ptr]) L b (newobjectRound s) (newobjectRound s) s s'
      fun m ptr => 0 < typSize s.mem (s.regs 0).toNat → newobjectObj R.rt s m ptr ∧ ApartAll ptr (newobjectRound s) L)

def WbLiveContract (p : Program) (addr stack : Nat) (R : RtInv) (n : Nat) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => CallOK s stack 0 ∧ R.ok addr [n] ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ …)
    (fun s s' => … MemFrame … ∧ LiveFrame s.mem m L [] ∧ WbSlots … ∧ ApartAll buf.toNat (8 * n) L ∧ InvSlots R b L … )
```

How it meets (i)-(iii):

* **Hand back, with a bound**: the postcondition of each allocating call is
  `R.inv (b - cost) (L ++ [obj]) g (view R.rt (L ++ [obj]) m)`: the invariant again, for the *smaller budget* and
  the *larger live set*. It establishes the next call's precondition for as many calls as the budget pays for, and
  no more. Barriers and copies cost nothing (they allocate nothing). This is what V2/V3 required: no unbounded chain
  (`blockSize >= 1` per object), so a finite model/runtime can meet it (`LiveSat*.lean`: bump allocator over a
  64 KiB heap meets every contract for every live set and budget).
* **What survives**: `LiveFrame s.mem m L ws`: every read inside a live object is unchanged; the new object is
  `ApartAll` from `L`. The first object cannot be overwritten by the second allocation.
* **Variables only**: `R` is a variable of the statement; the auditor's round 10 V1 rule applies unchanged
  (contract applied to the variable `R`, `impl`). `R.ok`/`R.inv`/budget occur only in the theorem's own
  precondition.
* **Compatibility**: the single-call contracts follow from the live ones (`….ready`).

## 4. Soundness and trusted base of the recommendation (c)

No Lean definition, contract, pin or model changes. What is already trusted and documented
(`docs/SOUNDNESS.md`, "Live allocation"): that the Go 1.26 runtime meets these contracts for some `R` that holds at
the theorem's entry, in particular that the collector frees no object of `L` while the program holds it, and that
the runtime's behaviour does not depend on the bytes of live objects or of filled barrier slots beyond what a
type-correct Go program stores there.

* Pinning: the runtime symbols are the same (`runtime.newobject`, `mallocgc`, `makeslice`, `growslice`,
  `gcWriteBarrier1..8`, `memmove`, `memclrNoHeapPointers`, …); `janus extract --contract …` and the stub pins
  (`checkContractPin`, rows `P_*`) do not change. The extraction of IntoBig is the one FV-C already has
  (`ex-{arm64,amd64}-IntoBig`).
* Non-vacuity (contract level): `newobjectLive_satisfiable`, `wbLive_satisfiable`, `rtLive_satisfiable`,
  `memmoveLive_satisfiable`, … (`LiveSat*.lean`; round 9 SAT row, 243/243).
* Non-vacuity (theorem level): `Witness.nonvacuous` needs an `R`; the toy bump allocator `LiveToy.lean`
  (`toyR`, `toy_alloc`) is the instance used by `examples/rtmisc/proofs/*/{Three,Chain}/…/Witness.lean`.
  The consumer reuses it; `AllocWitness.lean` (`janus_alloc_witness`) is the single-call analogue.

## 5. Prototypes (scratch) and what they show

All in `/srv/janus-ops/u14-protos/`, kernel-checked with Janus `agent/speed-u16` (9ce83d7e + the U16 fix), no
`sorry` in the accepted ones.

* `IntoBigSegA_arm64.lean` and `IntoBigSegA_amd64.lean` (both ISAs): `(*Int).IntoBig` on the `*b == nil` path from
  the entry to the join after `*b = new(big.Int)`: **`runtime.newobject` then `runtime.gcWriteBarrier2` in a single
  `janus_run` / `janus64_run`** with `calls [hnew.pos, hwb]`, `hnew : NewobjectLiveContract…`,
  `hwb : WbLiveContract… 2`, one `R`, **both branches of the barrier flag**, continuation as a hypothesis
  (`hcont`). arm64 11 s, amd64 8 s.
  Statement shape (identical to `Three`): `Pre R b z bp s` = `GuardOK`/`StackOK` (or `StackGuardOK`/`StackWritable`)
  of 4096 + frame, `DataLoaded`, `Outside` the frame/type descriptors `R.rt`, `R.ok (contractAddr "runtime.newobject")
  [typ]`, `R.ok (… "runtime.gcWriteBarrier2") [2]`, `R.inv b [] g (view R.rt [] s.mem)`, `blockSize 32 false <= b`.
* `IntoBigSegB_arm64_panic.lean`: the second half (the `[4]Word` array, the normalisation loop, `SetBits`, the
  second barrier), starting from a state `S` that carries the first half's facts (`p1 ∈ R.rt`, live set `[p1]`,
  budget `b - 32`, `MemFrame`). The second `newobject` is accepted with `L = [p1]` and the carried invariant
  (`R.inv (b-32) [(p1,p1+32)] …`), i.e. the sequence works; the run then stops at an unrelated engine failure at
  `stp x1, x3, [x2,#16]` (pc `IntoBig+0x11c`): `PANIC at Lean.Meta.whnfEasyCases: loose bvar in expression`
  inside `janus_run`'s branch splitting (also on 9ce83d7e; not caused by U16). To be filed as a Janus bug (U17).
  The full-function single run (`IntoBigFull_arm64.lean`) shows why the proof must be segmented as in `Three`:
  after the first call janus cannot decide the `cap(words) >= 4` test (it needs the zero-ness of the fresh object,
  `Fresh … ZeroBytes`), which a segment boundary supplies as a hypothesis on `S`.

Conclusion for IntoBig/ToBig: the existing live contracts cover the sequence. The proof is the `Three` pattern: one
module per runtime-call segment, one `Reaches` lemma each, all about the same `R`, a short main theorem.

## 6. Which uint256 symbols have more than one runtime call (from `identity.json`, arm64 and amd64)

| Symbol | Contract calls on its paths | Live coverage today |
| --- | --- | --- |
| `IntoBig`, `ToBig` | `newobject`, `gcWriteBarrier2`, `gcWriteBarrier1` | `NewobjectLiveContract(64)`, `WbLiveContract(64) n` : covered (prototype) |
| `Hex` | `slicebytetostring` (one call per path; `mallocgc`/`memmove` are inside it) | single call: no sequence needed; `RtLiveContract … slicebytetostringSpec slicebytetostringLive` exists if a caller needs one |
| `Dec`, `String`, `PrettyDec` | `memmove`, `growslice`, `mallocgc` | `MemmoveLive`, `RtLiveContract growsliceSpec growsliceLive` (any element size), `MallocgcLiveContract` : covered |
| `MarshalText`, `MarshalJSON` | + `memclrNoHeapPointers` | `MemclrNoHeapPointersLive` : covered |
| `Value` | `convTstring`, `memmove`, `growslice`, `mallocgc` | **gap**: `ConvTstring` is a single-call `IfaceModel` contract (`Iface.lean`), no live variant |
| `UnmarshalSSZ`, `MarshalSSZInto` | `newobject`, `convT64`, `fmt.errorf` | `newobject` covered; `convT64` and `fmt.errorf` only on error paths (partial theorems, U5) |

(`GrowsliceLiveContract` itself is 8-byte pointer-free elements only; the `RtSpec` form `growsliceSpec` with
`growsliceLive` covers any element type, so the 1-byte `append` of `Dec`/`String` does not need U13's new variant.)

## 7. The remaining gap: a live `convT64` / `convTstring` (design only; trusted-base addition)

`convT64(v)` (v >= 256) and `convTstring(s)` allocate a box; the interface contracts take `IfaceModel` + a
single-call `H` (V3: they cannot hand `R.Env` back). A live variant has the shape of `NewobjectLiveContract`:
`∀ L b, Summary p addr (… ∧ LiveAt R addr [v] L b 8 g m win) (… box ∈ R.rt, ApartAll box 8 L, box holds v,
R.inv (b - 8) (L ++ [box]) …)` plus the `v < 256` static case (`&staticuint64s[v]`, nothing allocated, no live-set
change), with the interface model (itab/type facts) taken from `R`-independent definitions. It would be an
`RtSpec`/`LiveSpec` pair (`convTstringSpec`, `convTstringLive : fresh := box`) reusing `RtLiveContract`, so the
new trusted statements are two specs; their SAT witnesses follow `LiveSat*` (toy bump allocator), and the pins are
unchanged (`convT64`, `convTstring` are already in the `--contract` stub list). Needed only for `Value`; not
requested for implementation here.

## 8. What the auditor must check in a consumer theorem that uses live contracts

* `R : RtInv` is a variable; every live contract hypothesis is `…LiveContract (Extracted.program.link impl)
  (Extracted.program.contractAddr "<symbol>") <stack> R …` with the same `R` (the auditor rule for contracts).
* The only constraints on `R` are in the theorem's precondition: `R.ok` for each call with exactly the arguments
  the call site passes (type descriptors recomputed from the extracted code, not typed in), `R.inv b [] g (view
  R.rt [] s.mem)`, and a budget hypothesis `sum of block sizes <= b` with `b` a variable (not a literal chosen to
  be huge).
* The caller's frame, its arguments and every pointer it passes are `Outside … R.rt` (and `Apart` the callee
  window), as in `Three`/`Chain`; freshness (`ApartAll`) is then a theorem.
* `Witness.nonvacuous` builds a concrete `R` (`LiveToy`) and a call state satisfying the whole precondition.

## 9. Red-team checklist

1. A statement that fixes the budget to a constant larger than any real heap, or `R.inv` for a literal `L`/`b`
   (`R.inv 0 …`, `R.inv (2^64) …`): the theorem is then about states the real runtime never reaches. Check `b`.
2. `R.ok addr args` stated for arguments the code does not pass (vacuous for the real call), or omitted for a call
   that is made (then the proof would not go through; a missing premise is not a soundness issue).
3. A caller object inside `R.rt` (the object may then overlap runtime memory): `Outside` facts required.
4. A live set that omits an object the function keeps across a later call: a later allocation may then overlap it
   (the contract does not protect objects not in `L`); the proof of a "kept" property fails, so check the final
   postcondition mentions all kept objects.
5. Mixing a live contract and a single-call contract on the same path (e.g. `Value`: live `mallocgc` then
   single-call `convTstring` with its own `H`): the second `H` must be assumed for a memory that does not exist at the
   entry; do not "fix" that by choosing `H := True` (V1/C1).
6. The statement's `stack` parameter (4096) must be at least what the contract's callee window needs; it is a
   precondition like any other.
7. Unreached error paths (`fmt.errorf`, panics): they remain `noCode` faults, i.e. the precondition must exclude them.

## 10. Recommendation

Use (c). Close U14 for `IntoBig`/`ToBig`/`Hex`/`Dec`/`String`/`PrettyDec`/`MarshalText`/`MarshalJSON` with a
documentation note (this file) and a pointer for FV-C to `examples/rtmisc/proofs/{arm64,amd64}/Three` as the
template, the scratch prototypes as the IntoBig starting point, and U17 (the `stp` panic) as the engine issue to
fix before the second half of IntoBig can be proved. `Value` needs the live `convT*` design of section 7, a
trusted-base addition that needs main's approval, a SAT witness and a red team before any code.
