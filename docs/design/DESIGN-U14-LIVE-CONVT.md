# Design (no code): live `convT64` / `convTstring` (and `convT16/32/convTslice`)

Status: IMPLEMENTED (agent/u14-liveconvt): `Janus/Contracts/IfaceLive.lean` (specs), `LiveStubConvT[Amd64].lean` (stubs + tactics), `IfaceLiveSat[Amd64].lean` (satisfiability), `test/lean/JanusTests/LiveStubConvT.lean` (tests + red team). `convT16/32/convTslice` are not covered.
Motivation: `(*uint256.Int).Value` (both ISAs) reaches `runtime.convTstring` after live `growslice`/`mallocgc`/`memmove` calls
(`ex-{arm64,amd64}-Value`: convTstring, memmove, growslice, mallocgc). The single-call `ConvTstring` (Janus/Contracts/Iface.lean) needs its own
`H : RtReady` and an `IfaceModel R`, and `R.Env` is handed back without budget (round 10 V3), so it cannot sit on a path after live calls.
Also unlocks: any `any(v)` boxing of an integer/string after an allocation (`UnmarshalSSZ`/`MarshalSSZInto` error paths via `convT64`, U5).

## 1. Shape (reuse `RtLiveContract`, no new contract kind)
`RtSpec` (Janus/Contracts/Rt.lean) already describes a runtime function by nargs/pre/reads/writes/guard/post; `LiveSpec` (Live.lean) adds
cost/fresh/keep; `RtLiveContract p addr stack R sp ls` turns the pair into `∀ L b, Summary …` over ONE `R : RtInv`. So the new trusted
statements are two `RtSpec`s and two `LiveSpec`s per ISA-independent definition (the contract wrappers exist for both ISAs already):

```lean
-- Janus/Contracts/IfaceLive.lean (new)
def convTstringSpec : RtSpec where
  nargs := 2                                  -- X0 = ptr, X1 = len (amd64: RAX, RBX)
  pre a m := True                             -- any string header; the string bytes are NOT read by convTstring
  rtWrites := true
  ready := true                               -- R.ok/R.inv carry readiness (live), not an H
  post rt a m0 r0 _ _ m :=
    BoxWords' rt m r0 [if arg a 1 = 0 then 0 else arg a 0, arg a 1]     -- box holds the header; ""-> &zeroVal (words 0,0)
def convTstringLive : LiveSpec where
  cost a _ := if arg a 1 = 0 then 0 else blockSize 16 false               -- 16-byte pointerful? see §3: noscan=false
  fresh a _ r0 _ _ := if arg a 1 = 0 then [] else [(r0, r0 + 16)]         -- the box is a new live object; &zeroVal is static, not live
  keep := fun _ _ _ _ _ => []                                              -- the string BYTES stay as the caller's own live range
def convT64Spec : RtSpec where
  nargs := 1
  pre a m := True
  post rt a m0 r0 _ _ m := BoxHolds' rt m r0 8 (arg a 0)                   -- &staticuint64s[v] for v < 256
def convT64Live : LiveSpec where
  cost a _ := if arg a 0 < 256 then 0 else blockSize 8 true               -- noscan 8-byte box (tiny allocator: see §3)
  fresh a _ r0 _ _ := if arg a 0 < 256 then [] else [(r0, r0 + 8)]
```
`BoxWords'`/`BoxHolds'` are `BoxWords`/`BoxHolds` with `R.priv` replaced by `R.rt` (the `RtInv` runtime ranges); the facts are the same
(box readable, below 2^48, inside the runtime ranges, holds the value). The static boxes (`&zeroVal`, `&staticuint64s[v]`) are inside
`R.rt` (runtime data), so `InRanges` holds for both branches; only the allocated branch adds to the live set.
Contracts: `RtLiveContract p (contractAddr "runtime.convTstring") stack R convTstringSpec convTstringLive` and `…64` (amd64). No change to
extraction: `runtime.convT*` are already `--contract` patterns and pinned (`stubpins_gen.go`).

## 2. What the interface model is replaced by
The single-call contracts quantify an `IfaceModel` only for itab/eq facts. `convT*` need none of them: the result is a box holding the
operand. So the live form takes only `R : RtInv`; a theorem that also asserts/compares interfaces keeps its `IfaceModel` for those (non-allocating)
contracts and links the two environments through its own precondition on `R.rt` / `R.priv` (the auditor rule "contract applied to variables only"
holds: `R` and `M` are separate statement variables).

## 3. Soundness points to be argued in the review (what is new and trusted)
1. `cost`: `convTstring` calls `mallocgc(16, stringType, false)` (pointerful: the string header has a pointer) -> `blockSize 16 false`;
   `convT64` calls `mallocgc(8, uint64Type, false)` for pointer-free 8 bytes -> tiny allocator, `blockSize 8 true` (tiny blocks share a 16-byte block:
   the existing `blockSize` models `<16` noscan as "owns only its own bytes"; the cost is an upper bound, not exact, as for `newobject`). Cost
   MUST be >= the real consumption; use the `LiveCost` bounds (`blockSize_le : <= 2n+24`) if the exact class is not wanted in statements.
2. Freshness/ApartAll from `L`: same argument as `NewobjectLiveContract` (allocator returns an unused slot; the collector frees only unreachable objects).
3. The box is new, initialised by the runtime: `convTstring` stores the header into the box (`*(*string)(x) = val`, with write barrier when marking).
   The contract may not promise the box's OTHER bytes (there are none: 16 bytes = header).
4. `val.len == 0` returns `&zeroVal[0]`, a static all-zero object: `ZeroBytes` is true of the box words, nothing allocated, `R.inv` unchanged (same `b`, same `L`).
   `v < 256` for `convT64`: `&staticuint64s[v]`, box holds `v` by the runtime's table (a fact about the runtime's data; pinned code + `R.rt`).
5. `v ≥ 256` / `len > 0` chains are bounded by the budget `b` (V3 closed): each call costs >= 1.
6. Write-barrier interplay: the call may run `gcWriteBarrier` internally; `R.inv` for the next call covers it (same as `mallocgc`).
7. No claim about the string's pointee: it is the caller's object and stays in `L` if it was there (`LiveFrame` leaves it unchanged).

## 4. SAT-witness plan (round 9 SAT row; 243 -> 245 contracts, arm64 + amd64 = 4 new `…_satisfiable`)
Files: `Janus/Contracts/IfaceLiveSat.lean`, `…SatAmd64.lean`; register in `Janus.lean`; the SAT row requires the name `convTstringLive_satisfiable`
etc. in module `IfaceLiveSat`. Proof pattern = `LiveSat.lean` `rtLive_satisfiable`: the bump allocator `LiveToy` (code `constCode`, invariant `toyInv`,
`toy_alloc`) with `LiveSpec.cost = 16`/`8`; the zero/static branch served by a toy static region inside `rt`; a concrete call state (len = 0 and len = 5,
v = 7 and v = 300 as separate lemmas so both branches are non-vacuous). `LiveSat` already proves `rt_post_nochange`-style frame lemmas to reuse.
Theorem-level non-vacuity for `Value`: `Witness.nonvacuous` built on `LiveToy` as in `examples/rtmisc/proofs/*/Three/…/Witness.lean`.

## 5. Red-team checklist (specific to this addition)
1. `cost := 0` for the allocating branch (mis-stated cheap contract -> unbounded chains again, V3): check `cost >= 1` whenever `len > 0` / `v >= 256`; add a Lean lemma `convT*_cost_pos` and a mutant test.
2. The "static" branch claiming a fresh object (adds `&zeroVal` to `L`): a later allocation could then be forced apart from runtime static data (over-constrains, but also lets `LiveFrame` claims about static memory); `fresh := []` there; mutant: put it in `fresh`.
3. Box contents for `len = 0`: `(0,0)` not `(ptr,0)` (the existing `ConvTstring` states `if len = 0 then 0 else ptr`); mutant swapping this must fail a witness on the real runtime (`test/redteam/rounds/rtstr`-style probe: 20000 random inputs vs Go's `any(s)`; add `convT*` rows) .
4. Readiness: no `H` in the live contract; `R.ok addr [ptr,len]` is the only per-call premise (like `NewobjectLive`): check the auditor rejects `R.ok` instantiated with constants for these addresses (round 10 V1 rule covers `R` as variable).
5. Mixed use: a path that calls the single-call `ConvTstring` after a live call (the old situation) must still be unprovable, not silently assumed (docs rule, section 9.5 of DESIGN-U14-SEQUENTIAL-CALLS).
6. `R.rt` containing the caller's string bytes: `Outside` facts required for the string pointee (it is the caller's or earlier allocated; earlier allocated = in `L`, outside `R.inv`'s view).
7. The real-runtime probe (`test/redteam/rounds/round10/probe`, 100000 boxes distinct, both ISAs) must keep passing with live statements; add a probe row that interleaves `convTstring` and `growslice` and checks distinctness/non-overlap.
8. Pin: extraction stays `pinned: true`; `test/redteam/rounds/roundfw` P_* mutates one byte of `convT64`/`convTstring` (already listed) -> still rejected.

## 6. Unlocks
`Value` (arm64, amd64). `UnmarshalSSZ`/`MarshalSSZInto` convT64 error paths (still needs `fmt.errorf`, U5: partial theorems only). Any future `any(x)` in an allocating function.
Single-call `ConvT*` stay for functions that box once (and need itab/eq model).

## 7. Cost estimate
2 `RtSpec` + 2 `LiveSpec` (~60 lines), 4 SAT witnesses (~150 lines, template exists), docs paragraph in RUNTIME-CONTRACTS.md, 2-3 audit probe rows, one mutant row; about one day of coder work, plus red team. Not started.
