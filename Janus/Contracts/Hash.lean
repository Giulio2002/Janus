import Janus.Contracts.Mem

/-!
# Contracts of the Go hashing runtime (arm64)

Go maps hash their keys with the key type's hash function (`Type.Hasher`; for a `map[K]V` with a
compiler-generated `type:.hash.K` it calls them field by field): `memhash` and its fixed-size
forms, `strhash`, `f32hash`, `f64hash`, `c64hash`, `c128hash`, `interhash`, `nilinterhash`
(`runtime/alg.go`, `runtime/asm_arm64.s`). `memhash`, `memhash32`, `memhash64` and `strhash` use
the AES instructions when the CPU has them (`useAeshash`) and a `wyhash` variant otherwise, both
keyed by a per-process random key (`aeskeysched`, `hashkey`); the float hashes call `rand()` for
a NaN.

**The hash is not fixed, it is a model.** A theorem quantifies over every `H : HashModel`: its
byte hashes `H.mem`, `H.mem32`, `H.mem64` are uninterpreted functions of the seed and the bytes
(the process's key is whatever the runtime chose), so a proof can only use what every hash
satisfies: it is a function (equal seeds and bytes give equal hashes). The float hashes are stated
on top of them with Go's special cases (`FHashIs`): `+0` and `-0` hash alike (`fhashIs_zero`),
equal floats hash alike (`fhashIs_of_feq`), and a NaN may hash to any value (`fhashIs_nan`), so
nothing can be concluded about it. `typehash` (the hash of a value of a dynamic type, behind
`interhash`) is a relation `H.TypeHash t m p h r` ("`r` is a possible hash"), equal to the byte
hash for `TFlagRegularMemory` types (`HashModel.Laws.regular`).

| Runtime function (Go 1.26) | Arguments (arm64) | Contract | Result in `X0` |
| --- | --- | --- | --- |
| `memhash(p, h, n)` | `X0, X1, X2` | `Memhash` | `H.mem h n v` (`v`: the `n` bytes at `p`) |
| `memhash0/8/16/128(p, h)` | `X0, X1` | `Memhash0`, `MemhashN 1/2/16` | `h`; `H.mem h n v` |
| `memhash32`, `memhash64(p, h)` | `X0, X1` | `Memhash32`, `Memhash64` | `H.mem32 h v`, `H.mem64 h v` |
| `memhash_varlen(p, h)` | `X0, X1`, size at `8(X26)` | `MemhashVarlen` | `H.mem h n v` |
| `strhash(p, h)` | `X0` (string header), `X1` | `Strhash` | `H.mem h len bytes` |
| `f32hash`, `f64hash(p, h)` | `X0, X1` | `Fhash binary32 4`, `Fhash binary64 8` | `FHashIs` |
| `c64hash`, `c128hash(p, h)` | `X0, X1` | `Chash binary32 4`, `Chash binary64 8` | real part, then imaginary part |
| `interhash`, `nilinterhash(p, h)` | `X0, X1` | `Interhash`, `Nilinterhash` | `h` for nil, else `c1 · r` with `TypeHash t … (h ^ c0) r` |
| `typehash(t, p, h)` | `X0, X1, X2` | `Typehash` | a `TypeHash` result |
| `rand()` | none | `Rand` | anything |

Every contract has the frame of `Janus.Contracts.Mem` with the model's private memory `H.priv`
(the random generator's state changes; the key does not, as `H.Env` holds again): the call
returns to `X30` with `SP`, `X18`, `X28`, `X29` and `FPCR` preserved, everything else arbitrary,
memory changed only in `H.priv`, `[SP - d, SP - 8)` and the argument spill slots.

**Not covered.** `interhash` and `nilinterhash` panic for an unhashable dynamic type
(`t.Equal = nil`); the contracts require the type hashable (`H.Hashable`).
-/

namespace Janus.Contracts.Hash

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Mem Janus.Float

/-! ## The model -/

/-- An abstract model of the hashing runtime (see the module documentation). -/
structure HashModel where
  /-- `memhash(p, h, n)` of the `n` bytes at `p` with little-endian value `v`, seed `h`. -/
  mem : Nat → Nat → Nat → Nat
  /-- `memhash32(p, h)` of the 4 bytes with value `v`. -/
  mem32 : Nat → Nat → Nat
  /-- `memhash64(p, h)` of the 8 bytes with value `v`. -/
  mem64 : Nat → Nat → Nat
  /-- `typehash(t, p, h)` may return `r`, for the value of type `t` at `p` in `m`. -/
  TypeHash : Nat → Memory → Nat → Nat → Nat → Prop
  /-- `t` is a hashable type (`t.Equal ≠ nil`) whose hash of the value at `p` returns. -/
  Hashable : Nat → Memory → Nat → Prop
  /-- The runtime (its hash key and random generator) is usable in `m` by the goroutine `g`. -/
  Env : Memory → W64 → Prop
  /-- The runtime's own memory. -/
  priv : List (Nat × Nat)

/-- `typehash` of a `TFlagRegularMemory` value of `n` bytes with value `v`: `memhash32` for 4
bytes, `memhash64` for 8, `memhash` otherwise. -/
def HashModel.regHash (H : HashModel) (h n v : Nat) : Nat :=
  if n = 4 then H.mem32 h v else if n = 8 then H.mem64 h v else H.mem h n v

/-- The laws of a `HashModel`: the hashes are 64-bit, the environment lives in the private
memory, a hashable type has a readable descriptor in that memory with an `Equal` function, and a
`TFlagRegularMemory` type hashes its bytes (`typehash`'s first case: `memhash32` for 4 bytes,
`memhash64` for 8, `memhash` otherwise). -/
structure HashModel.Laws (H : HashModel) : Prop where
  mem_lt : ∀ h n v, H.mem h n v < 2 ^ 64
  mem32_lt : ∀ h v, H.mem32 h v < 2 ^ 64
  mem64_lt : ∀ h v, H.mem64 h v < 2 ^ 64
  env_frame : ∀ m m' g, H.Env m g → Agrees m m' H.priv → H.Env m' g
  type_desc : ∀ m g t p, H.Env m g → H.Hashable t m p →
    t ≠ 0 ∧ t + typeDescSize ≤ 2 ^ 48 ∧ m.accessible t typeDescSize false = true ∧
      InRanges t typeDescSize H.priv ∧ tyEqual m t ≠ 0
  regular : ∀ m g t p h r, H.Env m g → H.Hashable t m p → isRegularMemory m t = true →
    (H.TypeHash t m p h r ↔ r = H.regHash h (tySize m t) (m.readLE p (tySize m t)))

/-- Go's hash constants (`runtime/alg.go`, 64-bit). -/
def c0 : Nat := 33054211828000289
def c1 : Nat := 23344194077549503

/-- `f32hash`/`f64hash` of the float `x` (format `f`, `k` bytes) with seed `h` may return `r`:
`c1 · (c0 ^ h)` for `±0`, `c1 · (c0 ^ h ^ rand())` for a NaN (any random word), the byte hash
`H.mem h k x` otherwise (all mod `2^64`). -/
def FHashIs (H : HashModel) (f : Fmt) (k x h r : Nat) : Prop :=
  if classify f x = .zero then r = c1 * (c0 ^^^ h) % 2 ^ 64
  else if isNaN f x then ∃ rnd, rnd < 2 ^ 64 ∧ r = c1 * (c0 ^^^ h ^^^ rnd) % 2 ^ 64
  else r = H.mem h k x

/-! ## The common shape -/

/-- What every hashing runtime call needs (arm64): `H.Env` with the goroutine in `X28`, the stack
guard at least `d` bytes below `SP`, `CallOK`, and the window outside `H.priv`. -/
def HPre (H : HashModel) (d nargs : Nat) (s : State) : Prop :=
  H.Env s.mem (s.regs 28) ∧ StackGuardOK s d ∧ CallOK s d nargs ∧
    Outside (s.sp.toNat - d) (d + 8 + 8 * nargs) H.priv ∧
    Outside ((s.regs 28).toNat + 16) 8 (calleeStack s d nargs) ∧ Outside ((s.regs 28).toNat + 16) 8 H.priv

/-- The return of a hashing runtime call (arm64), with the facts `P r` about the result
registers `r`. -/
def HRet (H : HashModel) (d nargs : Nat) (s s' : State) (P : (Nat → W64) → Prop) : Prop :=
  ∃ r v fl fs m, s' = { s with regs := Map.keepABI s.regs r, vregs := v, flags := fl, fpsr := fs,
                               mem := m, pc := s.regs 30 } ∧
    MemFrame s.mem m (H.priv ++ calleeStack s d nargs) ∧ H.Env m (s.regs 28) ∧ P r

/-! ## Byte hashes -/

/-- **`runtime.memhash(p, h, n)`** (`X0 = p`, `X1 = h`, `X2 = n`): `H.mem h n v`. -/
def Memhash (p : Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 3 s ∧ Input s d 3 (s.regs 0).toNat (s.regs 2).toNat)
    (fun s s' => HRet H d 3 s s' fun r => (r 0).toNat =
      H.mem (s.regs 1).toNat (s.regs 2).toNat (s.mem.readLE (s.regs 0).toNat (s.regs 2).toNat))

/-- **`runtime.memhash0(p, h)`**: the seed `h`. -/
def Memhash0 (p : Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr (fun s => HPre H d 2 s)
    (fun s s' => HRet H d 2 s s' fun r => r 0 = s.regs 1)

/-- **`runtime.memhash8/16/128(p, h)`** (`n = 1, 2, 16`): `memhash(p, h, n)`. -/
def MemhashN (p : Program) (addr : Nat) (H : HashModel) (d n : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ Input s d 2 (s.regs 0).toNat n)
    (fun s s' => HRet H d 2 s s' fun r => (r 0).toNat =
      H.mem (s.regs 1).toNat n (s.mem.readLE (s.regs 0).toNat n))

/-- **`runtime.memhash32(p, h)`**: `H.mem32 h v` of the 4 bytes at `p`. -/
def Memhash32 (p : Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ Input s d 2 (s.regs 0).toNat 4)
    (fun s s' => HRet H d 2 s s' fun r => (r 0).toNat =
      H.mem32 (s.regs 1).toNat (s.mem.readLE (s.regs 0).toNat 4))

/-- **`runtime.memhash64(p, h)`**: `H.mem64 h v` of the 8 bytes at `p`. -/
def Memhash64 (p : Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ Input s d 2 (s.regs 0).toNat 8)
    (fun s s' => HRet H d 2 s s' fun r => (r 0).toNat =
      H.mem64 (s.regs 1).toNat (s.mem.readLE (s.regs 0).toNat 8))

/-- **`runtime.memhash_varlen(p, h)`** (the closure context `X26` with the size at `8(X26)`):
`memhash(p, h, size)`. -/
def MemhashVarlen (p : Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ Input s d 2 ((s.regs 26).toNat + 8) 8 ∧
      Input s d 2 (s.regs 0).toNat (varlenSize s))
    (fun s s' => HRet H d 2 s s' fun r => (r 0).toNat =
      H.mem (s.regs 1).toNat (varlenSize s) (s.mem.readLE (s.regs 0).toNat (varlenSize s)))

/-- **`runtime.strhash(p, h)`** (`X0` points at a string header): `memhash(ptr, h, len)`. -/
def Strhash (p : Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ StrInput s d 2 (s.regs 0).toNat)
    (fun s s' => HRet H d 2 s s' fun r => (r 0).toNat =
      H.mem (s.regs 1).toNat (strLen s.mem (s.regs 0).toNat)
        (s.mem.readLE (strPtr s.mem (s.regs 0).toNat) (strLen s.mem (s.regs 0).toNat)))

/-! ## Floats and complex numbers -/

/-- **`runtime.f32hash(p, h)`** (`Fhash binary32 4`) and **`runtime.f64hash(p, h)`**
(`Fhash binary64 8`): `FHashIs` of the float at `p`. -/
def Fhash (p : Program) (addr : Nat) (H : HashModel) (d : Nat) (f : Fmt) (k : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ s.fpcr = 0 ∧ Input s d 2 (s.regs 0).toNat k)
    (fun s s' => HRet H d 2 s s' fun r =>
      FHashIs H f k (s.mem.readLE (s.regs 0).toNat k) (s.regs 1).toNat (r 0).toNat)

/-- **`runtime.c64hash(p, h)`** (`Chash binary32 4`) and **`runtime.c128hash(p, h)`**
(`Chash binary64 8`): the real part hashed with `h`, then the imaginary part with that hash. -/
def Chash (p : Program) (addr : Nat) (H : HashModel) (d : Nat) (f : Fmt) (k : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ s.fpcr = 0 ∧ Input s d 2 (s.regs 0).toNat (2 * k) ∧
      Outside (s.regs 0).toNat (2 * k) H.priv)
    (fun s s' => HRet H d 2 s s' fun r => ∃ h1,
      FHashIs H f k (s.mem.readLE (s.regs 0).toNat k) (s.regs 1).toNat h1 ∧
      FHashIs H f k (s.mem.readLE ((s.regs 0).toNat + k) k) h1 (r 0).toNat)

/-! ## Interfaces and dynamic types -/

/-- Changing memory only inside `ws` changes neither whether the value of type `t` at `p` is
hashable nor its possible hashes (nor whether `t` is direct): what a function that writes its
frame before it calls `typehash` needs (`HashFrame.of_regular` for regular-memory types). -/
def HashFrame (H : HashModel) (t : Nat) (m : Memory) (p : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ m', MemFrame m m' ws →
    (H.Hashable t m p → H.Hashable t m' p) ∧ (∀ h r, H.TypeHash t m' p h r ↔ H.TypeHash t m p h r) ∧
      isDirectIface m' t = isDirectIface m t

/-- **`runtime.typehash(t, p, h)`** (`X0 = t`, `X1 = p`, `X2 = h`) for a hashable `t`: some
`TypeHash` result. -/
def Typehash (p : Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 3 s ∧ H.Hashable (s.regs 0).toNat s.mem (s.regs 1).toNat)
    (fun s s' => HRet H d 3 s s' fun r =>
      H.TypeHash (s.regs 0).toNat s.mem (s.regs 1).toNat (s.regs 2).toNat (r 0).toNat)

/-- Where `interhash`/`nilinterhash` hash the value of an interface value at `a` with dynamic
type `t`: the data word itself (`a + 8`) for a direct type, else the word's target. -/
def dataAt (m : Memory) (t a : Nat) : Nat :=
  if isDirectIface m t then a + 8 else m.readLE (a + 8) 8

/-- The hash `interhash`/`nilinterhash` return for the dynamic type `t` (`0` = nil) of the
interface value at `a`, seed `h`: `h` for nil, else `c1 · r` for a `typehash` result `r` with
seed `h ^ c0`. -/
def IHashIs (H : HashModel) (m : Memory) (t a h res : Nat) : Prop :=
  if t = 0 then res = h
  else ∃ r, H.TypeHash t m (dataAt m t a) (h ^^^ c0) r ∧ res = c1 * r % 2 ^ 64

/-- **`runtime.nilinterhash(p, h)`** (`X0` points at an `any` value `(type, data)`, `X1 = h`):
`IHashIs` of its type word; a non-nil type must be hashable, and its hashes must not depend on
the callee's window (`HashFrame`). -/
def Nilinterhash (p : Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ IfaceInput s d (s.regs 0).toNat ∧
      (s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
        H.Hashable (s.mem.readLE (s.regs 0).toNat 8) s.mem
          (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat) ∧
        HashFrame H (s.mem.readLE (s.regs 0).toNat 8) s.mem
          (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat) (calleeStack s d 2)))
    (fun s s' => HRet H d 2 s s' fun r =>
      IHashIs H s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat (s.regs 1).toNat (r 0).toNat)

/-- The dynamic type of the non-empty interface value at `a` in `m`: `tab.Type` (`0` for a nil
itab). -/
def itabType (m : Memory) (a : Nat) : Nat :=
  if m.readLE a 8 = 0 then 0 else m.readLE (m.readLE a 8 + 8) 8

/-- **`runtime.interhash(p, h)`** (`X0` points at a non-empty interface value `(itab, data)`):
`IHashIs` of `itab.Type`; a non-nil itab must be readable (outside the window) with a non-nil,
hashable type. -/
def Interhash (p : Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ IfaceInput s d (s.regs 0).toNat ∧
      (s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
        Input s d 2 (s.mem.readLE (s.regs 0).toNat 8) 16 ∧
        itabType s.mem (s.regs 0).toNat ≠ 0 ∧
        H.Hashable (itabType s.mem (s.regs 0).toNat) s.mem
          (dataAt s.mem (itabType s.mem (s.regs 0).toNat) (s.regs 0).toNat) ∧
        HashFrame H (itabType s.mem (s.regs 0).toNat) s.mem
          (dataAt s.mem (itabType s.mem (s.regs 0).toNat) (s.regs 0).toNat) (calleeStack s d 2)))
    (fun s s' => HRet H d 2 s s' fun r =>
      IHashIs H s.mem (itabType s.mem (s.regs 0).toNat) (s.regs 0).toNat (s.regs 1).toNat (r 0).toNat)

/-! ## The random generator -/

/-- **`runtime.rand()`**: some 64-bit word (the generator's state, in `H.priv`, advances). -/
def Rand (p : Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr (fun s => HPre H d 0 s) (fun s s' => HRet H d 0 s s' fun _ => True)

end Janus.Contracts.Hash
