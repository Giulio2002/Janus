import Janus.Spec.Type
import Janus.Contracts.Map

/-!
# Contracts of the Go interface runtime (arm64)

Go 1.26 lowers interface conversions, type assertions, type switches and interface comparisons
to calls of `runtime/iface.go` and `runtime/alg.go` functions (and inline probes of the
assertion and switch caches). A theorem about a function that uses them leaves the runtime
functions out (`janus extract --contract runtime.convT64`, …), states its result about
`Extracted.program.link impl` for **any** code `impl` at their addresses, and takes the behaviour
of each one as a hypothesis: a `Summary` at its address whose pre- and postcondition are the
definitions below, over an abstract model `R : IfaceModel` of the runtime (`Janus.Spec.Type`).
See docs/RUNTIME-CONTRACTS.md, "Interfaces".

| Go source | Runtime entry (Go 1.26) | Contract | Result |
| --- | --- | --- | --- |
| `any(v)`, `I(v)` for a non-pointer-shaped `T` | `convT(t, &v)` | `ConvT` | a box in `R.priv` holding a copy of the `t.Size_` bytes of `v` |
| same, pointer-free `T` | `convTnoptr(t, &v)` | `ConvTnoptr` | as `ConvT` |
| 2-, 4-, 8-byte `T` | `convT16(v)`, `convT32(v)`, `convT64(v)` | `ConvT16`, `ConvT32`, `ConvT64` | a box holding `v` (for `v < 256`, `&staticuint64s[v]`) |
| `string` | `convTstring(s)` | `ConvTstring` | a box holding the string header (`""`: `&zeroVal`, all zero) |
| `[]T` | `convTslice(s)` | `ConvTslice` | a box holding the slice header (nil: `&zeroVal`) |
| `x.(I)` (generic code) | `assertE2I(inter, t)` | `AssertE2I` | `getitab(inter, t, false)` |
| `v, ok := x.(I)` (generic code) | `assertE2I2(inter, t)` | `AssertE2I2` | `getitab(inter, t, true)`, `0` for a nil `t` |
| `x.(I)`, `v, ok := x.(I)` | cache probe, then `typeAssert(desc, t)` | `TypeAssert` | the itab (or `0`), and the descriptor's cache well formed again |
| `switch x.(type)` with interface cases | cache probe, then `interfaceSwitch(desc, t)` | `InterfaceSwitch` | `switchCase`: the first case `t` implements and its itab |
| `a == b` on `any` | `efaceeq(t, x, y)` | `Efaceeq` | `t = nil`, or `x == y` for a direct type, or `R.eq t` |
| `a == b` on a non-empty interface | `ifaceeq(tab, x, y)` | `Ifaceeq` | the same with `t = tab.Type` |

Every contract has the frame of the map contracts (`RTReturn`): the call returns to `X30` with
`SP`, `X18`, `X28` (`g`) and `X29` preserved, every other general register, the SIMD registers
and the flags arbitrary, the memory regions unchanged, bytes changed only in `R.priv`, in at most
`R.depth` bytes below `SP` (never the caller's frame-pointer slot `[SP-8, SP)`), in the argument
spill slots, and (`typeAssert`, `interfaceSwitch`) in the descriptor's `Cache` word; and `R.Env`
holds again.

**Panics are excluded, not specified.** Each precondition rules out the runtime's panic and throw
paths: a nil or non-implementing type in `assertE2I` (`TypeAssertionError`), a failing
`typeAssert` without `CanFail`, an uncomparable type in `efaceeq`/`ifaceeq` (`R.Comparable`), an
empty interface in `getitab` (`R.IsInter` is non-empty), and a nil type in `interfaceSwitch`
(the compiled code tests for nil before the call). A theorem says nothing about such calls.

**What a box is.** The pointer a `convT*` returns is in `R.priv` (heap, `staticuint64s` or
`zeroVal`) and holds the value right after the call. The contracts do not say that a box keeps
its value across later runtime calls (they may change `R.priv`); the GC never moves or frees a
reachable object, but this model has no notion of reachability.
-/

namespace Janus.Contracts.Iface

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts

/-! ## The common shape -/

/-- What every interface runtime call with `nargs` register arguments needs (arm64): the runtime
environment `R.Env` (with the goroutine in `X28`), the stack guard at least `R.depth` bytes below
`SP`, the ABI conditions of `CallOK` (admissible `X30`, aligned `SP`, the window
`[SP - R.depth, SP + 8 + 8·nargs)` writable) and that window outside the runtime's memory. -/
def RTPre (R : IfaceModel) (nargs : Nat) (s : State) : Prop :=
  R.Env s.mem (s.regs 28) ∧ StackGuardOK s R.depth ∧ CallOK s R.depth nargs ∧
    Outside (s.sp.toNat - R.depth) (R.depth + 8 + 8 * nargs) R.priv

/-- The byte ranges an interface runtime call with `nargs` register arguments may write, at
call state `s`. -/
def rtWrites (R : IfaceModel) (s : State) (nargs : Nat) : List (Nat × Nat) :=
  R.priv ++ calleeStack s R.depth nargs

attribute [janus_exec, janus_post] rtWrites

/-- The return of an interface runtime call from `s` to `s'` (arm64), with the call-specific
facts `P r m` about the result registers `r` and the new memory `m`. -/
def RTReturn (R : IfaceModel) (nargs : Nat) (extra : List (Nat × Nat)) (s s' : State)
    (P : (Nat → W64) → Memory → Prop) : Prop :=
  ∃ r v fl m, s' = { s with regs := Map.keepABI s.regs r, vregs := v, flags := fl, mem := m,
                            pc := s.regs 30 } ∧
    MemFrame s.mem m (rtWrites R s nargs ++ extra) ∧ R.Env m (s.regs 28) ∧ P r m

/-- What a caller needs to call the interface runtime from inside a frame of `frame` bytes
below its `SP`, with `above` bytes of its caller's frame (argument spill slots) it may write: as
`Map.CallerOK`, for the model `R`. -/
def CallerOK (R : IfaceModel) (s : State) (frame above : Nat) : Prop :=
  R.Env s.mem (s.regs 28) ∧ StackGuardOK s (R.depth + frame) ∧ s.sp.toNat % 16 = 0 ∧
    8 ≤ R.depth ∧ R.depth + frame ≤ s.sp.toNat ∧ s.sp.toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible (s.sp.toNat - (R.depth + frame)) (R.depth + frame + above) true = true ∧
    Outside (s.sp.toNat - (R.depth + frame)) (R.depth + frame + above) R.priv ∧
    Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - (R.depth + frame)) (R.depth + frame + above) ∧
    Outside ((s.regs 28).toNat + 16) 8 R.priv

/-- `RTPre` at a call site `S`, from the caller's `CallerOK` at its entry `s`. -/
theorem RTPre.of_parts {R : IfaceModel} {s S : State} {frame above nargs : Nat}
    (hc : CallerOK R s frame above) (henv : R.Env S.mem (s.regs 28))
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (hguard : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) (hfr : frame % 16 = 0)
    (hn : 8 + 8 * nargs ≤ frame + above) : RTPre R nargs S := by
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, -⟩ := hc
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  refine ⟨by rw [hg]; exact henv, ⟨?_, ?_, ?_⟩, ⟨hlr, hlr', ?_, ?_, hd8, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hacc]; exact hg2
  · simp only [stackguard0, regG, stackguard0Offset, hg, hguard, hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hacc]; exact Memory.accessible_mono _ hst (by omega) (by omega)
  · rw [hsp]; exact Outside.of_sub hout (by omega) (by omega)

/-- `RTPre.of_parts` for a first call: the call state's memory differs from the caller's entry
memory only inside the caller's window. -/
theorem RTPre.of_caller {R : IfaceModel} (hl : R.Laws) {s S : State}
    {frame above nargs : Nat} (hc : CallerOK R s frame above)
    (hf : MemFrame s.mem S.mem [(s.sp.toNat - (R.depth + frame), s.sp.toNat + above)])
    (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) (hfr : frame % 16 = 0)
    (hn : 8 + 8 * nargs ≤ frame + above) : RTPre R nargs S := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, -, -⟩, -, -, -, -, -, hout, hgd, -⟩ := hc'
  simp only [regG, stackguard0Offset, Spec.Disjoint] at hg1 hgd
  refine RTPre.of_parts hc (hl.env_frame _ _ _ henv
    (Agrees.of_window hf (Outside.of_sub hout (by omega) (by omega)))) hf.accessible
    (hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)) hsp hg hlr hlr' hfr hn

/-! ## Arithmetic of the cache probes (arm64 encodings) -/

theorem testBit_two_pow_sub_two_pow (n i : Nat) (hn : n ≤ 64) :
    (2 ^ 64 - 2 ^ n).testBit i = (decide (n ≤ i) && decide (i < 64)) := by
  have : 2 ^ 64 - 2 ^ n = 2 ^ n * (2 ^ (64 - n) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hn]
  rw [this, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
  by_cases h : n ≤ i <;> simp [h] <;> omega

/-- `LSL #n` is `UBFM` (rotate right by `64 - n`, keep the bits from `n` up): a left shift. -/
theorem rotateRight_and_eq_shiftLeft (x : BitVec 64) (n : Nat) (hn : n < 64) :
    x.rotateRight (64 - n) &&& BitVec.ofNat 64 (2 ^ 64 - 2 ^ n) = x <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, testBit_two_pow_sub_two_pow n i (by omega), hi, decide_true,
    Bool.true_and]
  by_cases hin : i < n
  · simp [hin, show ¬ n ≤ i by omega]
  · have h0 : n = 0 ∨ 0 < n := by omega
    rcases h0 with rfl | h0
    · simp; omega
    · rw [Nat.mod_eq_of_lt (show 64 - n < 64 by omega)]
      simp [hin, show n ≤ i by omega, show ¬ i < 64 - (64 - n) by omega,
        show i - (64 - (64 - n)) = i - n by omega]

theorem lsl_toNat (x : BitVec 64) (n : Nat) (hn : n < 64) :
    ((x.rotateRight (64 - n)).toNat &&& (2 ^ 64 - 2 ^ n)) = 2 ^ n * x.toNat % 2 ^ 64 := by
  have h := congrArg BitVec.toNat (rotateRight_and_eq_shiftLeft x n hn)
  have hp : 0 < 2 ^ n := Nat.two_pow_pos n
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.mul_comm] at h
  exact h

/-- `LSL #4` (`UBFM X, X, #60, #59`) as the executor leaves it: a product by 16. -/
@[janus_exec, janus_post] theorem lsl4_toNat (x : BitVec 64) :
    ((x.rotateRight 60).toNat &&& 18446744073709551600) = 16 * x.toNat % 18446744073709551616 :=
  lsl_toNat x 4 (by decide)

/-- `LSL #3` as the executor leaves it: a product by 8. -/
@[janus_exec, janus_post] theorem lsl3_toNat (x : BitVec 64) :
    ((x.rotateRight 61).toNat &&& 18446744073709551608) = 8 * x.toNat % 18446744073709551616 :=
  lsl_toNat x 3 (by decide)

/-- `CMN Wn, Wm` (a 32-bit add that only sets the flags; the compiler tests a 32-bit type hash
against a negated constant this way): the `Z` flag as arithmetic. -/
@[janus_exec, janus_post] theorem add_flags_z32 (x y : BitVec 32) :
    (addWithCarry x y false).2.z = decide ((x.toNat + y.toNat) % 4294967296 = 0) := by
  simp only [addWithCarry, Bool.toNat_false, Nat.add_zero]
  apply decide_eq_decide.mpr
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa using this
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

/-- The probe index `h & Mask` for `Mask = 2^k - 1`. -/
theorem and_mask_toNat (h : BitVec 64) (k : Nat) (hk : k ≤ 64) :
    (h &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = h.toNat % 2 ^ k := by
  have : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod]

/-! ## Results -/

/-- The box at `ptr` (in the runtime's memory, readable) holds a copy of the `n` bytes at `src`
of the call-time memory `m₀`. -/
def BoxCopy (R : IfaceModel) (m₀ m : Memory) (ptr src n : Nat) : Prop :=
  ptr + n ≤ 2 ^ 48 ∧ m.accessible ptr n false = true ∧ InRanges ptr n R.priv ∧
    ∀ i, i < n → m.bytes (ptr + i) = m₀.bytes (src + i)

/-- The box at `ptr` (in the runtime's memory, readable) holds the words `ws`
(at `ptr`, `ptr + 8`, …). -/
def BoxWords (R : IfaceModel) (m : Memory) (ptr : Nat) (ws : List Nat) : Prop :=
  ptr + 8 * ws.length ≤ 2 ^ 48 ∧ m.accessible ptr (8 * ws.length) false = true ∧
    InRanges ptr (8 * ws.length) R.priv ∧ ∀ i (h : i < ws.length), m.readLE (ptr + 8 * i) 8 = ws[i]

/-- The box at `ptr` (in the runtime's memory, readable) holds the `n`-byte value `v`. -/
def BoxHolds (R : IfaceModel) (m : Memory) (ptr n v : Nat) : Prop :=
  ptr + n ≤ 2 ^ 48 ∧ m.accessible ptr n false = true ∧ InRanges ptr n R.priv ∧ m.readLE ptr n = v

/-- The itab result `v` of an assertion of the type `t` to the interface `inter`: `0` for a nil
type, else `getitab`'s answer (`0` if `t` does not implement `inter`); a non-zero result is a
readable itab of the pair. -/
def ItabResult (R : IfaceModel) (m : Memory) (inter t v : Nat) : Prop :=
  v = (if t = 0 then 0 else (R.itab inter t).getD 0) ∧ (v ≠ 0 → ItabAt R.priv m v inter t)

/-- `efaceeq(t, x, y)`: true for a nil type; for a direct-interface type the data words compare;
otherwise `t.Equal(x, y)`. -/
def efaceEqual (R : IfaceModel) (m : Memory) (t x y : Nat) : Bool :=
  t == 0 || (if isDirectIface m t then x == y else R.eq t m x y)

/-- `ifaceeq(tab, x, y)`: true for a nil itab, else `efaceEqual` of `tab.Type`. -/
def ifaceEqual (R : IfaceModel) (m : Memory) (tab x y : Nat) : Bool :=
  tab == 0 || efaceEqual R m (m.readLE (tab + 8) 8) x y

/-- The values at `x` and `y` of the type `t` can be compared by `efaceeq` (`t` nil, or a type
whose comparison returns). -/
def EqOK (R : IfaceModel) (m : Memory) (t x y : Nat) : Prop :=
  t ≠ 0 → R.IsType t ∧ R.Comparable t m x y

/-- A frame that does not affect the comparison keeps `EqOK`. -/
theorem EqFrame.eqOK {R : IfaceModel} {t : Nat} {m m' : Memory} {x y : Nat} {ws : List (Nat × Nat)}
    (h : EqFrame R t m x y ws) (hok : EqOK R m t x y) (hf : MemFrame m m' ws) : EqOK R m' t x y :=
  fun ht => ⟨(hok ht).1, (h m' hf).1 (hok ht).2⟩

/-- A frame that does not affect the comparison keeps `efaceEqual`. -/
theorem EqFrame.efaceEqual {R : IfaceModel} {t : Nat} {m m' : Memory} {x y : Nat}
    {ws : List (Nat × Nat)} (h : EqFrame R t m x y ws) (hf : MemFrame m m' ws) :
    efaceEqual R m' t x y = efaceEqual R m t x y := by
  obtain ⟨-, he, hd⟩ := h m' hf
  simp only [Iface.efaceEqual, he, hd]

/-- `efaceEqual` of a `TFlagRegularMemory` type that is not direct: its `Size_` bytes compare. -/
theorem efaceEqual_regular {R : IfaceModel} (hl : R.Laws) {m : Memory} {g : W64} {t x y : Nat}
    (henv : R.Env m g) (ht0 : t ≠ 0) (ht : R.IsType t) (hreg : isRegularMemory m t = true)
    (hnd : isDirectIface m t = false)
    (hx : m.accessible x (tySize m t) false = true) (hy : m.accessible y (tySize m t) false = true) :
    efaceEqual R m t x y = (m.readLE x (tySize m t) == m.readLE y (tySize m t)) := by
  obtain ⟨-, he⟩ := hl.regular m g t x y henv ht hreg hnd hx hy
  simp [Iface.efaceEqual, ht0, hnd, he]

/-! ## Boxing -/

/-- **`runtime.convT(t, v)`** (`X0 = t`, `X1 = v`): `mallocgc(t.Size_, t, true)` and
`typedmemmove`: a box holding a copy of the `t.Size_` bytes at `v`. -/
def ConvT (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr
    (fun s => RTPre R 2 s ∧ R.IsType (s.regs 0).toNat ∧
      (s.regs 1).toNat + tySize s.mem (s.regs 0).toNat ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 1).toNat (tySize s.mem (s.regs 0).toNat) false = true)
    (fun s s' => RTReturn R 2 [] s s' fun r m =>
      BoxCopy R s.mem m (r 0).toNat (s.regs 1).toNat (tySize s.mem (s.regs 0).toNat))

/-- **`runtime.convTnoptr(t, v)`**: as `ConvT`, for a pointer-free `t` (`t.PtrBytes = 0`;
`mallocgc` without zeroing and `memmove`). -/
def ConvTnoptr (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr
    (fun s => RTPre R 2 s ∧ R.IsType (s.regs 0).toNat ∧ tyPtrBytes s.mem (s.regs 0).toNat = 0 ∧
      (s.regs 1).toNat + tySize s.mem (s.regs 0).toNat ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 1).toNat (tySize s.mem (s.regs 0).toNat) false = true)
    (fun s s' => RTReturn R 2 [] s s' fun r m =>
      BoxCopy R s.mem m (r 0).toNat (s.regs 1).toNat (tySize s.mem (s.regs 0).toNat))

/-- **`runtime.convT16(v)`** (`X0 = v`): a box holding the low 16 bits of `v`. -/
def ConvT16 (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr (fun s => RTPre R 1 s)
    (fun s s' => RTReturn R 1 [] s s' fun r m => BoxHolds R m (r 0).toNat 2 ((s.regs 0).toNat % 2 ^ 16))

/-- **`runtime.convT32(v)`**: a box holding the low 32 bits of `v`. -/
def ConvT32 (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr (fun s => RTPre R 1 s)
    (fun s s' => RTReturn R 1 [] s s' fun r m => BoxHolds R m (r 0).toNat 4 ((s.regs 0).toNat % 2 ^ 32))

/-- **`runtime.convT64(v)`**: a box holding `v`. -/
def ConvT64 (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr (fun s => RTPre R 1 s)
    (fun s s' => RTReturn R 1 [] s s' fun r m => BoxHolds R m (r 0).toNat 8 (s.regs 0).toNat)

/-- **`runtime.convTstring(s)`** (`X0 = ptr`, `X1 = len`): a box holding the string header;
the empty string's box is `&zeroVal[0]`, whose header words are both `0`. -/
def ConvTstring (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr (fun s => RTPre R 2 s)
    (fun s s' => RTReturn R 2 [] s s' fun r m =>
      BoxWords R m (r 0).toNat
        [if (s.regs 1).toNat = 0 then 0 else (s.regs 0).toNat, (s.regs 1).toNat])

/-- **`runtime.convTslice(s)`** (`X0 = ptr`, `X1 = len`, `X2 = cap`): a box holding the slice
header; a nil slice's box is `&zeroVal[0]` (all three words `0`). -/
def ConvTslice (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr (fun s => RTPre R 3 s)
    (fun s s' => RTReturn R 3 [] s s' fun r m =>
      BoxWords R m (r 0).toNat
        (if (s.regs 0).toNat = 0 then [0, 0, 0]
         else [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat]))

/-! ## Assertions and switches -/

/-- **`runtime.assertE2I(inter, t)`** (`X0 = inter`, `X1 = t`), for a non-nil `t` that
implements `inter` (otherwise it panics): the itab. -/
def AssertE2I (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr
    (fun s => RTPre R 2 s ∧ R.IsInter (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
      R.IsType (s.regs 1).toNat ∧ (R.itab (s.regs 0).toNat (s.regs 1).toNat).isSome)
    (fun s s' => RTReturn R 2 [] s s' fun r m =>
      ItabResult R m (s.regs 0).toNat (s.regs 1).toNat (r 0).toNat)

/-- **`runtime.assertE2I2(inter, t)`**: the itab, or `0` if `t` is nil or does not implement
`inter`. -/
def AssertE2I2 (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr
    (fun s => RTPre R 2 s ∧ R.IsInter (s.regs 0).toNat ∧
      ((s.regs 1).toNat ≠ 0 → R.IsType (s.regs 1).toNat))
    (fun s s' => RTReturn R 2 [] s s' fun r m =>
      ItabResult R m (s.regs 0).toNat (s.regs 1).toNat (r 0).toNat)

/-- **`runtime.typeAssert(desc, t)`** (`X0 = desc`, an `abi.TypeAssert`; `X1 = t`): the itab of
`t` for `desc.Inter` (`0` if `t` is nil or does not implement it; without `CanFail` those cases
panic and are excluded). The runtime may replace `desc.Cache` by a new cache (one call in about
1000): afterwards the descriptor is well formed again, with the same `Inter` and `CanFail`. -/
def TypeAssert (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr
    (fun s => RTPre R 2 s ∧ TADescOK R s.mem (s.regs 0).toNat ∧
      ((s.regs 1).toNat = 0 → taCanFail s.mem (s.regs 0).toNat = true) ∧
      ((s.regs 1).toNat ≠ 0 → R.IsType (s.regs 1).toNat ∧
        (taCanFail s.mem (s.regs 0).toNat = true ∨
          (R.itab (taInter s.mem (s.regs 0).toNat) (s.regs 1).toNat).isSome)))
    (fun s s' => RTReturn R 2 [((s.regs 0).toNat, (s.regs 0).toNat + 8)] s s' fun r m =>
      ItabResult R m (taInter s.mem (s.regs 0).toNat) (s.regs 1).toNat (r 0).toNat ∧
      TADescOK R m (s.regs 0).toNat ∧ taInter m (s.regs 0).toNat = taInter s.mem (s.regs 0).toNat ∧
      taCanFail m (s.regs 0).toNat = taCanFail s.mem (s.regs 0).toNat)

/-- **`runtime.interfaceSwitch(desc, t)`** (`X0 = desc`, an `abi.InterfaceSwitch` with the cases
`cs`; `X1 = t`, non-nil): `(case, itab)` in `X0`, `X1`, the index of the first case `t`
implements and its itab, or `(len cs, 0)` (`switchCase`). The runtime may replace `desc.Cache`;
afterwards the descriptor is well formed again for the same cases. -/
def InterfaceSwitch (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  ∀ cs : List Nat, Summary p addr
    (fun s => RTPre R 2 s ∧ ISDescOK R s.mem (s.regs 0).toNat cs ∧ (s.regs 1).toNat ≠ 0 ∧
      R.IsType (s.regs 1).toNat)
    (fun s s' => RTReturn R 2 [((s.regs 0).toNat, (s.regs 0).toNat + 8)] s s' fun r m =>
      (r 0).toNat = (switchCase R (s.regs 1).toNat cs).1 ∧
      (r 1).toNat = (switchCase R (s.regs 1).toNat cs).2 ∧
      ((r 1).toNat ≠ 0 → ItabAt R.priv m (r 1).toNat (cs.getD (r 0).toNat 0) (s.regs 1).toNat) ∧
      ISDescOK R m (s.regs 0).toNat cs)

/-! ## Comparison -/

/-- **`runtime.efaceeq(t, x, y)`** (`X0 = t`, `X1`, `X2` the data words): `efaceEqual`, in the
low byte of `X0`. The compiled `a == b` on `any` calls it when the type words are equal. -/
def Efaceeq (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr
    (fun s => RTPre R 3 s ∧ EqOK R s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat)
    (fun s s' => RTReturn R 3 [] s s' fun r _ =>
      (r 0).toNat % 256 =
        (efaceEqual R s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat).toNat)

/-- **`runtime.ifaceeq(tab, x, y)`** (`X0 = tab`, `X1`, `X2`): `ifaceEqual`, in the low byte of
`X0`; a non-nil itab must be readable (its `Type` word is compared with). -/
def Ifaceeq (p : Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr
    (fun s => RTPre R 3 s ∧ ((s.regs 0).toNat ≠ 0 →
      (s.regs 0).toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 16 false = true ∧
      (s.mem.readLE ((s.regs 0).toNat + 8) 8 ≠ 0) ∧
      EqOK R s.mem (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.regs 1).toNat (s.regs 2).toNat))
    (fun s s' => RTReturn R 3 [] s s' fun r _ =>
      (r 0).toNat % 256 =
        (ifaceEqual R s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat).toNat)

end Janus.Contracts.Iface
