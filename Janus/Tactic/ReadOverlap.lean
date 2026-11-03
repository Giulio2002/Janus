import Lean
import Janus.Arm64.MemoryLemmas

/-!
# Reads that partially overlap an earlier store

`(m.writeLE a n v).readLE b k` where the two ranges overlap without one containing the other
(a 16-byte vector load over an 8-byte store, a load that runs past the end of the store, a load that
ends inside it). The result is byte-exact: the bytes of the store where the ranges meet, the old
bytes of `m` elsewhere (`Memory.readLE_writeLE_contained_at`, `_overrun_at`, `_underrun_at`).

The simproc `reduceReadOverWrite` fires when
* the widths `n`, `k` are numerals, and
* the two addresses are the same term up to numeric offsets (`x - 72`, `x - 64`, `x + 8`), which gives
  the literal offset `d = a - b` between them, and
* the simp discharger (the executor's omega) proves the offset equation `a = b + d` (or
  `b = a + d`) from the context. When it cannot (an unknown relation, a possibly wrapping
  subtraction), the read stays as it is, and
* the read is at most `janus.readOverlap.maxWidth` (16) bytes wide: wider reads, which specifications
  state over a chain of stores (a block copy, a multi-limb result), are left in their stuck form for
  the lemmas written for it.
The rewrite is justified by an ordinary lemma instance; nothing is trusted.
-/

namespace Janus.Tactic.ReadOverlap

open Lean Meta Simp

register_option janus.readOverlap.maxWidth : Nat := {
  defValue := 16
  descr := "janus_run/janus64_run: widest read (in bytes) whose partial overlap with an earlier store \
    is forwarded byte-exactly (`Janus.Tactic.ReadOverlap`). The default 16 covers the scalar, SSE and \
    NEON loads of an instruction; wider reads (a block read stated by a specification, an AVX load) keep \
    their `(m.writeLE a n v).readLE b k` form, which block-copy lemmas such as `copy_step` expect. \
    0 turns the forwarding off; raise it to forward AVX/AVX-512 loads."
}
open Janus.Arm64

/-- A numeral. -/
def lit? (e : Expr) : Option Nat := e.nat? <|> e.rawNatLit?

/-- `e` as `base + off` with a numeric offset (`none` base for a pure numeral). -/
partial def addrOffset (e : Expr) : Option Expr × Int :=
  match_expr e with
  | HAdd.hAdd _ _ _ _ x y =>
    match lit? y with
    | some c => let (b, o) := addrOffset x; (b, o + c)
    | none =>
      match lit? x with
      | some c => let (b, o) := addrOffset y; (b, o + c)
      | none => (some e, 0)
  | HSub.hSub _ _ _ _ x y =>
    match lit? y with
    | some c => let (b, o) := addrOffset x; (b, o - c)
    | none => (some e, 0)
  | _ =>
    match lit? e with
    | some c => (none, c)
    | none => (some e, 0)

/-- `base + off` as a term (`base - |off|` for a negative offset). -/
def mkAddr (base : Option Expr) (off : Int) : MetaM Expr := do
  match base with
  | none => return mkNatLit off.toNat
  | some x =>
    if off == 0 then return x
    else if 0 < off then mkAppM ``HAdd.hAdd #[x, mkNatLit off.toNat]
    else mkAppM ``HSub.hSub #[x, mkNatLit (-off).toNat]

private def discharge (p : Expr) : SimpM (Option Expr) := do
  (← getMethods).discharge? p

private def natEq (l r : Expr) : MetaM Expr := mkEqRefl l >>= fun pf =>
  mkExpectedTypeHint pf (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) l r)

/-- See the module documentation. -/
simproc_decl reduceReadOverWrite (Janus.Arm64.Memory.readLE (Janus.Arm64.Memory.writeLE _ _ _ _) _ _) :=
  fun e => do
  let_expr Janus.Arm64.Memory.readLE w b k := e | return .continue
  let_expr Janus.Arm64.Memory.writeLE m a n v := w | return .continue
  let some n' := lit? n | return .continue
  let some k' := lit? k | return .continue
  if n' == 0 || k' == 0 || k' > janus.readOverlap.maxWidth.get (← getOptions) then return .continue
  let (ba, oa) := addrOffset a
  let (bb, ob) := addrOffset b
  unless ba == bb do return .continue
  let d := oa - ob   -- a = b + d
  let nl := mkNatLit
  let n'' : Int := n'
  let k'' : Int := k'
  let eqAdd (l x : Expr) (j : Nat) : MetaM Expr := do
    mkEq l (← mkAppM ``HAdd.hAdd #[x, nl j])
  let finish (pf : Expr) : SimpM Simp.Step := do
    let some (_, _, rhs) := (← inferType pf).eq? | return .continue
    return .visit { expr := rhs, proof? := some pf }
  if 0 ≤ d && d + n'' ≤ k'' && n'' < k'' then
    -- the store lies inside the read
    let j := d.toNat
    let r := (k'' - d - n'').toNat
    let some hj ← discharge (← eqAdd a b j) | return .continue
    let hk ← natEq k (← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[nl j, n], nl r])
    let c ← mkAddr ba (ob + j + n'')
    let some hc ← discharge (← mkEq c (← mkAppM ``HAdd.hAdd #[b, nl (j + n')])) | return .continue
    finish (← mkAppOptM ``Memory.readLE_writeLE_contained_at
      (#[m, a, n, b, k, v, nl j, nl r, c, hj, hk, hc].map some))
  else if d < 0 && -d < n'' && n'' + d < k'' then
    -- the read starts inside the store and runs past its end
    let j := (-d).toNat
    let t := (n'' + d).toNat
    let r := (k'' - t).toNat
    let some hj ← discharge (← eqAdd b a j) | return .continue
    let hn ← natEq n (← mkAppM ``HAdd.hAdd #[nl j, nl t])
    let hk ← natEq k (← mkAppM ``HAdd.hAdd #[nl t, nl r])
    let ht ← mkDecideProof (← mkAppM ``LT.lt #[nl 0, nl t])
    let hr ← mkDecideProof (← mkAppM ``LT.lt #[nl 0, nl r])
    let c ← mkAddr ba (ob + t)
    let some hc ← discharge (← mkEq c (← mkAppM ``HAdd.hAdd #[b, nl t])) | return .continue
    finish (← mkAppOptM ``Memory.readLE_writeLE_overrun_at
      (#[m, a, n, b, k, v, nl j, nl t, nl r, c, hj, hn, hk, ht, hr, hc].map some))
  else if 0 < d && d < k'' && k'' < d + n'' then
    -- the read ends inside the store
    let j := d.toNat
    let t := (k'' - d).toNat
    let some hj ← discharge (← eqAdd a b j) | return .continue
    let hk ← natEq k (← mkAppM ``HAdd.hAdd #[nl j, nl t])
    let hj0 ← mkDecideProof (← mkAppM ``LT.lt #[nl 0, nl j])
    let ht ← mkDecideProof (← mkAppM ``LT.lt #[nl 0, nl t])
    let htn ← mkDecideProof (← mkAppM ``LT.lt #[nl t, n])
    finish (← mkAppOptM ``Memory.readLE_writeLE_underrun_at
      (#[m, a, n, b, k, v, nl j, nl t, hj, hk, hj0, ht, htn].map some))
  else return .continue

/-- `256 ^ (a - b)` for two addresses with the same base and numeric offsets (`x - 64 - (x - 72)`):
the exponent is the literal distance, when the discharger can prove it. The executor's lemma for a
read inside a store, `readLE_writeLE_inside`, states `v / 256 ^ (b - a)`; this keeps the shift a
numeral. Only this position is rewritten: the same subtraction elsewhere (a range length) is left
as the proofs about it state it. -/
simproc_decl reducePowSameBaseSub ((256 : Nat) ^ (_ : Nat)) := fun e => do
  let_expr HPow.hPow _ _ _ _ base ex := e | return .continue
  let_expr HSub.hSub _ _ _ _ a b := ex | return .continue
  if (lit? a).isSome || (lit? b).isSome then return .continue
  let (ba, oa) := addrOffset a
  let (bb, ob) := addrOffset b
  let some _ := ba | return .continue
  unless ba == bb do return .continue
  let d : Nat := (oa - ob).toNat   -- `a - b` is `d` when `ob ≤ oa`, else `0`
  let some pf ← discharge (← mkEq ex (mkNatLit d)) | return .continue
  let f := e.appFn!
  return .visit { expr := mkApp f (mkNatLit d), proof? := some (← mkCongrArg f pf) }

end Janus.Tactic.ReadOverlap
