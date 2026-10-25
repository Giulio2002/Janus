import Janus.Contracts.Hash
import Janus.Contracts.MemAmd64

/-!
# Contracts of the Go hashing runtime (amd64)

The amd64 counterparts of `Janus.Contracts.Hash` (see that file and docs/RUNTIME-CONTRACTS.md,
"Equality, hashing and typed memory"): the same runtime entry points and results over the same
model `H : HashModel`, stated with the amd64 ABIInternal (`RAX`, `RBX`, `RCX` = `regs 0`,
`regs 3`, `regs 1`; the closure context `RDX` = `regs 2`; the result in `RAX`) and the frame of
`Janus.Contracts.MemAmd64`, with the model's private memory `H.priv`.
-/

namespace Janus.Contracts.HashAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Type Janus.Contracts Janus.Contracts.Mem Janus.Contracts.MemAmd64
  Janus.Contracts.Hash Janus.Float

/-- What every hashing runtime call needs (amd64): `H.Env` with the goroutine in `R14`, the
stack guard, `MemAmd64.CallOK`, and the window outside `H.priv`. -/
def HPre (H : HashModel) (d nargs : Nat) (s : State) : Prop :=
  H.Env s.mem (s.regs 14) ∧ StackGuardOK s d ∧ MemAmd64.CallOK s d nargs ∧
    Outside ((s.regs 4).toNat - d) (d + 8 + 8 * nargs) H.priv

/-- The return of a hashing runtime call (amd64), with the facts `P r` about the result
registers `r`. -/
def HRet (H : HashModel) (d nargs : Nat) (s s' : State) (P : (Nat → W64) → Prop) : Prop :=
  ∃ r x y fl mx m, s' = MemAmd64.retState s r x y fl mx m ∧ mx.toNat / 64 = s.mxcsr.toNat / 64 ∧
    MemFrame s.mem m (H.priv ++ MemAmd64.calleeStack s d nargs) ∧ H.Env m (s.regs 14) ∧ P r

/-- **`runtime.memhash(p, h, n)`** (`RAX = p`, `RBX = h`, `RCX = n`). -/
def Memhash (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 3 s ∧ MemAmd64.Input s d 3 (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => HRet H d 3 s s' fun r => (r 0).toNat =
      H.mem (s.regs 3).toNat (s.regs 1).toNat (s.mem.readLE (s.regs 0).toNat (s.regs 1).toNat))

/-- **`runtime.memhash0(p, h)`**: the seed `h`. -/
def Memhash0 (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr (fun s => HPre H d 2 s)
    (fun s s' => HRet H d 2 s s' fun r => r 0 = s.regs 3)

/-- **`runtime.memhash8/16/128(p, h)`** (`n = 1, 2, 16`). -/
def MemhashN (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d n : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat n)
    (fun s s' => HRet H d 2 s s' fun r => (r 0).toNat =
      H.mem (s.regs 3).toNat n (s.mem.readLE (s.regs 0).toNat n))

/-- **`runtime.memhash32(p, h)`**. -/
def Memhash32 (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 4)
    (fun s s' => HRet H d 2 s s' fun r => (r 0).toNat =
      H.mem32 (s.regs 3).toNat (s.mem.readLE (s.regs 0).toNat 4))

/-- **`runtime.memhash64(p, h)`**. -/
def Memhash64 (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 8)
    (fun s s' => HRet H d 2 s s' fun r => (r 0).toNat =
      H.mem64 (s.regs 3).toNat (s.mem.readLE (s.regs 0).toNat 8))

/-- **`runtime.memhash_varlen(p, h)`** (the closure context `RDX`, the size at `8(RDX)`). -/
def MemhashVarlen (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ MemAmd64.Input s d 2 ((s.regs 2).toNat + 8) 8 ∧
      MemAmd64.Input s d 2 (s.regs 0).toNat (MemAmd64.varlenSize s))
    (fun s s' => HRet H d 2 s s' fun r => (r 0).toNat =
      H.mem (s.regs 3).toNat (MemAmd64.varlenSize s)
        (s.mem.readLE (s.regs 0).toNat (MemAmd64.varlenSize s)))

/-- **`runtime.strhash(p, h)`** (`RAX` points at a string header, `RBX = h`). -/
def Strhash (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ MemAmd64.StrInput s d 2 (s.regs 0).toNat)
    (fun s s' => HRet H d 2 s s' fun r => (r 0).toNat =
      H.mem (s.regs 3).toNat (strLen s.mem (s.regs 0).toNat)
        (s.mem.readLE (strPtr s.mem (s.regs 0).toNat) (strLen s.mem (s.regs 0).toNat)))

/-- **`runtime.f32hash`/`f64hash(p, h)`** (`Fhash binary32 4`, `Fhash binary64 8`). -/
def Fhash (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) (f : Fmt) (k : Nat) :
    Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ GoMXCSR s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat k)
    (fun s s' => HRet H d 2 s s' fun r =>
      FHashIs H f k (s.mem.readLE (s.regs 0).toNat k) (s.regs 3).toNat (r 0).toNat)

/-- **`runtime.c64hash`/`c128hash(p, h)`** (`Chash binary32 4`, `Chash binary64 8`). -/
def Chash (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) (f : Fmt) (k : Nat) :
    Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ GoMXCSR s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat (2 * k))
    (fun s s' => HRet H d 2 s s' fun r => ∃ h1,
      FHashIs H f k (s.mem.readLE (s.regs 0).toNat k) (s.regs 3).toNat h1 ∧
      FHashIs H f k (s.mem.readLE ((s.regs 0).toNat + k) k) h1 (r 0).toNat)

/-- **`runtime.typehash(t, p, h)`** (`RAX = t`, `RBX = p`, `RCX = h`). -/
def Typehash (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 3 s ∧ H.Hashable (s.regs 0).toNat s.mem (s.regs 3).toNat)
    (fun s s' => HRet H d 3 s s' fun r =>
      H.TypeHash (s.regs 0).toNat s.mem (s.regs 3).toNat (s.regs 1).toNat (r 0).toNat)

/-- **`runtime.nilinterhash(p, h)`** (`RAX` points at an `any` value, `RBX = h`). -/
def Nilinterhash (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 16 ∧
      (s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
        H.Hashable (s.mem.readLE (s.regs 0).toNat 8) s.mem
          (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat) ∧
        HashFrame H (s.mem.readLE (s.regs 0).toNat 8) s.mem
          (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat)
          (H.priv ++ MemAmd64.calleeStack s d 2)))
    (fun s s' => HRet H d 2 s s' fun r =>
      IHashIs H s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat (s.regs 3).toNat (r 0).toNat)

/-- **`runtime.interhash(p, h)`** (`RAX` points at a non-empty interface value, `RBX = h`). -/
def Interhash (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 16 ∧
      (s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
        MemAmd64.Input s d 2 (s.mem.readLE (s.regs 0).toNat 8) 16 ∧
        itabType s.mem (s.regs 0).toNat ≠ 0 ∧
        H.Hashable (itabType s.mem (s.regs 0).toNat) s.mem
          (dataAt s.mem (itabType s.mem (s.regs 0).toNat) (s.regs 0).toNat) ∧
        HashFrame H (itabType s.mem (s.regs 0).toNat) s.mem
          (dataAt s.mem (itabType s.mem (s.regs 0).toNat) (s.regs 0).toNat)
          (H.priv ++ MemAmd64.calleeStack s d 2)))
    (fun s s' => HRet H d 2 s s' fun r =>
      IHashIs H s.mem (itabType s.mem (s.regs 0).toNat) (s.regs 0).toNat (s.regs 3).toNat (r 0).toNat)

/-- **`runtime.rand()`**: some 64-bit word. -/
def Rand (p : Janus.Amd64.Program) (addr : Nat) (H : HashModel) (d : Nat) : Prop :=
  Summary p addr (fun s => HPre H d 0 s) (fun s s' => HRet H d 0 s s' fun _ => True)

end Janus.Contracts.HashAmd64
