# Migrating to wave 2

Wave 2 changes the shape of several public definitions. Proofs written against the previous
release (main `4a75ac7`) need the edits below. Each entry gives the definition, the old and the
new form, and the typical proof edit. The state-field rule behind most of them: **an arm64 runtime
contract leaves the exclusive monitor (`excl`, `exclPass`) unspecified after the call; an amd64
runtime contract leaves the AVX-512 state (`zmmHi`, `kreg`) unspecified.** The callee may run
load/store-exclusives or AVX-512 code, so a contract promises nothing about those fields.

## 1. `Ret0` and `ret0_iff` (ABI0 returns)

arm64 (`Janus/GoABI0.lean`). `Ret0` keeps its binders, but `ret0_iff` now also states that the
exclusive-monitor fields are kept (an ABI0 assembly callee does not run exclusives):

```lean
-- before
Ret0 s s' Q ↔ s'.sp = s.sp ∧ s'.pc = s.regs regLR ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
  s'.regs 29 = s.regs 29 ∧ s'.fpcr = s.fpcr ∧ s'.tpidr = s.tpidr ∧ s'.dczid = s.dczid ∧ Q s'.mem
-- after: two more conjuncts before `Q s'.mem`
  ... ∧ s'.dczid = s.dczid ∧ s'.excl = s.excl ∧ s'.exclPass = s.exclPass ∧ Q s'.mem
```

amd64 (`Janus/Amd64/GoABI0.lean`). `Ret0` gained the AVX-512 junk `z : Avx512Junk`
(`zmmHi`, `kreg`) and `ret0_iff` gained `fpucw`/`x87` preservation:

```lean
-- before
∃ (junk) (f) (v vh : Nat → W128) (mx : BitVec 32) (m : Memory),
  s' = retState0 s junk f v vh mx m ∧ mx.toNat / 64 = s.mxcsr.toNat / 64 ∧ Q m
-- after
∃ (junk) (f) (v vh : Nat → W128) (mx : BitVec 32) (m : Memory) (z : Avx512Junk),
  s' = retState0 s junk f v vh mx m z ∧ mx.toNat / 64 = s.mxcsr.toNat / 64 ∧ Q m
-- ret0_iff: ... ∧ s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64 ∧ s'.fpucw = s.fpucw ∧ s'.x87 = s.x87 ∧ Q s'.mem
```

Edit: `obtain ⟨junk, f, v, vh, mx, m, rfl, hmx, hq⟩ := h` becomes
`obtain ⟨junk, f, v, vh, mx, m, z, rfl, hmx, hq⟩ := h`; patterns that destructure `ret0_iff`'s
right-hand side need the extra conjuncts.

## 2. `retStateX` (arm64) and `retState64` (amd64): runtime-contract return states

arm64: runtime contracts return in `retStateX`, which adds the unspecified monitor
(`Janus/Contracts/Alloc.lean`):

```lean
-- before
def retState (s) (junk) (res) (f) (v) (m) : State :=
  { s with regs := callRegs s.regs junk res, pc := s.regs 30, flags := f, vregs := v, mem := m }
-- after (retState is kept for C-ABI uses)
def retStateX (s) (junk) (res) (f) (v) (m) (ex : Option (Nat × Nat)) (ep : Nat → Bool) : State :=
  { s with ..., mem := m, excl := ex, exclPass := ep }
```

amd64: `retState64` takes `zh : Nat → BitVec 256` and `kr : Nat → W64`
(`Janus/Contracts/AllocAmd64.lean`):

```lean
-- before
def retState64 (s) (junk) (res) (f) (x yh : Nat → BitVec 128) (m) : State
-- after
def retState64 (s) (junk) (res) (f) (x yh : Nat → BitVec 128) (m) (zh : Nat → BitVec 256) (kr : Nat → W64) : State
```

Edits in a proof of a contract (or of a function-pointer implementation):

```lean
-- arm64: two more witnesses, and simp with retStateX
refine ⟨ptr, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_, ...⟩
simp only [retStateX]
-- amd64: two more existentials and two more ret_of arguments
refine ⟨ptr, _, _, _, _, _, _, _, ret_of s _ [ptr] ..., ...⟩
-- and in rintro patterns for a contract's post:  ⟨regs, flags, xmm, ymmHi, mx, zh, kr, rfl, ...⟩
```

`retStateX_intro` proves a state is one. A `Summary` whose postcondition said
`s'.excl = s.excl` (arm64) or `s'.zmmHi = s.zmmHi` (amd64) after a runtime call must drop it.

## 3. Live contracts replace per-call `Ready`

Before, an allocation contract took a readiness predicate for the one call and the runtime-owned
ranges `rt` (`Janus/Contracts/Alloc.lean`):

```lean
def NewobjectContract (p) (addr) (rt : List (Nat × Nat)) (stack : Nat) (H : RtReady) : Prop :=
  Summary p addr (fun s => NewobjectPre stack s ∧ Ready H rt [(s.regs 0).toNat] s) (...)
```

A theorem could make only one such call (the second object could overlap the first). The live
contracts (`Janus/Contracts/Live.lean`, `LiveAmd64.lean`) thread one `R : RtInv` through every call
and a ghost live set `L` and budget `b`:

```lean
def MallocgcLiveContract (p : Program) (addr : Nat) (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => MallocgcPre stack s ∧ StackRoom s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
        (s.regs 28).toNat s.mem (calleeStack s stack 3))
    (fun s s' => LiveAllocRet R stack 3 ...)
```

Edit: replace `(rt) (H : RtReady)` hypotheses by one `(R : RtInv)`; the precondition `Ready H rt args s`
becomes `LiveAt R addr args L b cost g s.mem win`; a postcondition now also gives
`R.inv (b - cost) (L ++ [obj]) g (view R.rt (L ++ [obj]) m)`, which is the next call's
precondition. Live versions exist for `mallocgc`, `newobject`, `makeslice`, `growslice`, the SC
entries, `gcWriteBarrierN`, the string/slice specs and the copies/clears (`MemmoveLive`, ...).
The per-call forms are kept and still hold.

## 4. `LiveSep`

New (`Janus/Contracts/Live.lean`): `LiveSep L win := ∀ r ∈ L, Outside r.1 (r.2 - r.1) win`, every
live object lies outside the callee's stack window. It is a conjunct of `LiveAt`/`LiveMemAt`
(`LiveSep L win ∧ LiveSep win R.rt`). Simp lemmas `liveSep_nil`, `liveSep_cons` discharge it for a
literal list `L`:

```lean
-- the caller supplies, per call:
have hsep : LiveSep [(a, a + 16)] (calleeStack s stack 3) := by simp [LiveSep]; omega
```

## 5. `MemModel` to `RtInv`

`Mem.MemModel` (a per-contract model of typed memory) is kept for the legacy contracts. The live
contracts take `RtInv` (`inv`, `ok`, `rt`, `ext`) instead of a `MemModel` plus `rt`:

```lean
-- before
theorem foo (M : MemModel) (h : TypedMemmove p addr M wb d) ...
-- after
theorem foo (R : RtInv) (h : TypedMemmoveLive p addr wb d R) ...
-- bridge: MemModel.ofRt R states a MemModel over a live runtime's model
```

## 6. Other source-visible changes in this wave

* `Program` gained globals (`--global`, `GlobalsInit`) and `Extracted.dyngot` (`GotBound`);
  `janus extract --frames` renders `Extracted.frames` for the stack-growth contracts
  (`EnsuresGrow`, `GrownReturns`; docs/RUNTIME-CONTRACTS.md, "Stack growth").
* `Stub` kinds `syscall` and `trap`: a `match` over the stub kind needs those alternatives
  (`| syscall => ... | trap => ...`).
* Regenerate extractions: `identity.json` records `globals`, `frames`, `buildModes` when used.
