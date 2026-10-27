import Janus.Spec.Pool
import Janus.Contracts.Map
import Janus.Contracts.Live

/-!
# Contracts of `sync.Pool` for one goroutine (arm64)

`math/big` (`nat.expNN`, `div`, `sqr`, `mul` and their deferred `stack.free`) and much of the
standard library keep scratch objects in a `sync.Pool`. Its methods are concurrency code: `Get`
and `Put` pin the goroutine to its P (`runtime_procPin`), use a lock-free per-P deque
(`poolDequeue`, `poolChain`), steal from other Ps (`getSlow`), and register a new pool under the
`allPools` mutex (`pinSlow`, `Mutex.lockSlow` → `semacquire1`). A theorem about a caller leaves
the two methods out (`janus extract --contract 'sync.(*Pool).Get' --contract
'sync.(*Pool).Put'`; the extractor pins both to package `sync`'s code), states its result about
`Extracted.program.link impl` for **any** code `impl` at their addresses, and takes the
behaviour of each as a hypothesis: a `Summary` at its address whose pre- and postcondition are
the definitions below. See docs/RUNTIME-CONTRACTS.md, "sync.Pool".

| Go source | Function (Go 1.26, ABIInternal) | Contract | Result |
| --- | --- | --- | --- |
| `x := p.Get()` | `sync.(*Pool).Get()` (`X0 = p`; result `X0` type word, `X1` data word) | `PoolGetLive` | nil, or `(T, d)` with the object `d` (ranges `rs`) **caller-owned** |
| `p.Put(x)` | `sync.(*Pool).Put()` (`X0 = p`, `X1`/`X2` the interface words of `x`) | `PoolPutLive` | the caller gives the ranges `rs` of `x` up |

**Ownership, not content.** The contracts do not say which value `Get` returns, or what the pool
holds. A `Get` returns nil or an element of the pool's element type `T`: an object `d` whose
shape the pool's user fixes (`Sh`, e.g. `SliceObj`: a 24-byte header holding a slice and the
slice's backing array) with **arbitrary contents**, and the ranges `rs` of that object are
**caller-owned**: fresh for the caller's live set `L` (outside every object it holds and the
callee's stack window), inside the runtime-owned ranges `R.rt` like an allocator's result (the
caller keeps its own frame outside `R.rt`), and added to `L`. `Put` gives them back: the caller must own them (`rs ⊆ L`)
and afterwards they are not in its live set (`dropAll L rs`): it no longer owns them, the pool
may hand them out again. Neither call touches the caller's memory (`LiveFrame`: every live object
reads as before, the object being put included) and neither allocates anything the caller sees
(the pool's own allocations, `pinSlow` and `poolChain.pushHead`, are runtime memory).

**The live set and the invariant.** The statement has the shape of the live allocation and
write-barrier contracts (`Janus.Contracts.Live`: `RtInv`, `view`, `LiveFrame`, `LiveAt`,
`FreshFrom`, `LiveSep` come from there). A ghost list `L` holds the caller's live ranges; `R : RtInv` is the runtime's
invariant over the memory as the runtime sees it (`view R.rt L m`: the runtime-owned ranges `R.rt`
with the caller's live set masked out). A theorem calls `Get`, then any number of allocations,
write barriers and pool calls, then `Put`, threading `L`, because every call returns the
invariant for the next live set. A real runtime meets the contracts for an `R` whose invariant
says that every pool the program uses holds only objects of the shape `Sh` outside the live
set, which is exactly what `Put`'s precondition hands over (the pool's user must not give it
anything else: see docs/RUNTIME-CONTRACTS.md); `R.ok` names the pools it serves.

**Single goroutine.** The contracts describe a pool used by one goroutine: no other goroutine
calls `Get` or `Put` on any pool, or changes a pool's memory, during the calls of the theorem
(docs/SOUNDNESS.md, "The single-threaded assumption"). The goroutine may move between Ps between
calls (the pool's content is the union over all Ps).

**`New` must be nil.** `Get` calls `p.New()` when it finds nothing and `New` is set: a callback
into arbitrary Go code. `PoolGetLive` requires the `New` word (offset 32) to be `0`, as for
`math/big`'s `stackPool`, and both calls keep it; a `Get` on a pool with `New` set is a call
this contract says nothing about.

**Frame.** Both contracts return to `X30` with `SP`, `X18`, `X28` (`g`) and `X29` preserved,
every other general register, the SIMD registers and the flags arbitrary (the exclusive monitor
and its outcome stream `excl`, `exclPass` are unspecified too, like every arm64 call: `retStateX`), and bytes changed only in `rt` and in the
callee's stack window (at most `stack` bytes below `SP`, never the caller's frame-pointer slot
`[SP-8, SP)`, and the argument spill slots `[SP+8, SP+8+8·nargs)`). The pool's own memory (the
pool's struct, the per-P arrays and chains, the P's write-barrier buffer: the barrier the calls
execute when they store an interface into a `poolLocal`) is part of `R.rt`.
-/

namespace Janus.Contracts.Pool

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Pool
  Janus.Contracts

/-! ## Shapes of pooled objects -/

/-- The shape of the objects a pool holds: `Sh m d rs` says that the pointer `d`, in memory `m`,
is an object of the pool's element type that owns the ranges `rs` (e.g. a header and its
backing array). The pool's user fixes it; the contracts take it as a parameter. -/
abbrev PoolShape := Memory → Nat → List (Nat × Nat) → Prop

/-- A pooled **slice header** (`math/big`'s `type stack struct{ w []Word }`): `d` points to a
24-byte header `{ptr, len, cap}` of a slice of 8-byte elements that is writable and 8-aligned,
with `len ≤ cap ≤ bound` (`bound < 2^40`); the object owns the header and, when `cap > 0`, the
backing array `[ptr, ptr + 8·cap)` (`rs`), which are disjoint. Their contents are arbitrary. -/
def SliceObj (bound : Nat) : PoolShape := fun m d rs =>
  0 < d ∧ d % 8 = 0 ∧ d + 24 ≤ 2 ^ 48 ∧ m.accessible d 24 true = true ∧
    m.readLE (d + 8) 8 ≤ m.readLE (d + 16) 8 ∧ m.readLE (d + 16) 8 ≤ bound ∧ bound < 2 ^ 40 ∧
    m.readLE d 8 % 8 = 0 ∧ m.readLE d 8 + 8 * m.readLE (d + 16) 8 ≤ 2 ^ 48 ∧
    (0 < m.readLE (d + 16) 8 → m.accessible (m.readLE d 8) (8 * m.readLE (d + 16) 8) true = true) ∧
    Disjoint d 24 (m.readLE d 8) (8 * m.readLE (d + 16) 8) ∧
    rs = (d, d + 24) :: (if m.readLE (d + 16) 8 = 0 then []
      else [(m.readLE d 8, m.readLE d 8 + 8 * m.readLE (d + 16) 8)])

/-- A pooled slice header is still one after a frame that does not touch the header (the shape
reads the header and the accessibility of the ranges only). -/
theorem SliceObj.of_frame {B : Nat} {m m' : Memory} {d : Nat} {rs : List (Nat × Nat)} {ws : List (Nat × Nat)}
    (h : SliceObj B m d rs) (hf : MemFrame m m' ws) (hd : Outside d 24 ws) : SliceObj B m' d rs := by
  unfold SliceObj at h ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have e0 : m'.readLE d 8 = m.readLE d 8 := hf.readLE _ _ (Outside.of_sub hd (Nat.le_refl _) (by omega))
  have e1 : m'.readLE (d + 8) 8 = m.readLE (d + 8) 8 := hf.readLE _ _ (Outside.of_sub hd (by omega) (by omega))
  have e2 : m'.readLE (d + 16) 8 = m.readLE (d + 16) 8 := hf.readLE _ _ (Outside.of_sub hd (by omega) (by omega))
  simp only [e0, e1, e2, hf.accessible]
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The live set `L` without the ranges `rs`. -/
def dropAll (L rs : List (Nat × Nat)) : List (Nat × Nat) := L.filter fun r => !rs.contains r

theorem mem_dropAll {L rs : List (Nat × Nat)} {r : Nat × Nat} (h : r ∈ dropAll L rs) : r ∈ L :=
  (List.mem_filter.1 h).1

theorem mem_dropAll_of {L rs : List (Nat × Nat)} {r : Nat × Nat} (h : r ∈ L) (h' : r ∉ rs) :
    r ∈ dropAll L rs := by
  simp only [dropAll, List.mem_filter, Bool.not_eq_true']
  exact ⟨h, by simpa using h'⟩

/-! ## The contracts -/

/-- The return of a live pool call from `s` to `s'` (arm64): to `X30` with `SP`, `X18`, `X28`,
`X29` kept and everything else as `Map.keepABI`, memory changed only in `rt` and the callee's
window, the exclusive monitor unspecified (`ex`, `ep`), none of the live objects of `L` changed, and `P r m` about the result registers and the
new memory. -/
def LiveRet (R : RtInv) (stack nargs : Nat) (L : List (Nat × Nat)) (s s' : State)
    (P : (Nat → W64) → Memory → Prop) : Prop :=
  ∃ (r : Nat → W64) (v : Nat → BitVec 128) (fl : Flags) (m : Memory) (ex : Option (Nat × Nat))
    (ep : Nat → Bool),
    s' = { s with regs := Map.keepABI s.regs r, vregs := v, flags := fl, mem := m, pc := s.regs 30,
                  excl := ex, exclPass := ep } ∧
    MemFrame s.mem m (R.rt ++ calleeStack s stack nargs) ∧ LiveFrame s.mem m L [] ∧ P r m

attribute [janus_exec, janus_post] LiveRet

/-- The pool's `New` word is unchanged. -/
def NewSame (p : Nat) (s m : Memory) : Prop := m.readLE (p + newOffset) 8 = s.readLE (p + newOffset) 8

/-- **`sync.(*Pool).Get()`** (arm64; `X0 = p`, a pool whose `New` is nil; result `X0` the type
word, `X1` the data word): returns nil with the invariant kept, or `(T, d)` with the object `d`
of shape `Sh` (ranges `rs`), caller-owned: fresh for `L` and the callee's stack window, and the
invariant holds for `L ++ rs`. The contents of the object are arbitrary (the caller assumes only
`Sh`). -/
def PoolGetLive (p : Program) (addr : Nat) (stack : Nat) (R : RtInv)
    (T : Nat) (Sh : PoolShape) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => CallOK s stack 1 ∧ StackRoom s stack 1 ∧
      s.mem.readLE ((s.regs 0).toNat + newOffset) 8 = 0 ∧
      LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 28).toNat s.mem (calleeStack s stack 1))
    (fun s s' => LiveRet R stack 1 L s s' fun r m =>
      NewSame (s.regs 0).toNat s.mem m ∧
      (((r 0).toNat = 0 ∧ (r 1).toNat = 0 ∧ R.inv b L (s.regs 28).toNat (view R.rt L m)) ∨
       ∃ rs, (r 0).toNat = T ∧ Sh m (r 1).toNat rs ∧ FreshFrom rs L ∧
         (∀ x ∈ rs, InRanges x.1 (x.2 - x.1) R.rt) ∧ LiveSep rs (calleeStack s stack 1) ∧
         R.inv b (L ++ rs) (s.regs 28).toNat (view R.rt (L ++ rs) m)))

/-- **`sync.(*Pool).Put(x)`** (arm64; `X0 = p`, `X1`/`X2` the type and data words of `x`): the
caller gives up the object `x = (T, d)` of shape `Sh` and the ranges `rs` it owns (`rs ⊆ L`);
afterwards the invariant holds for the live set without them. -/
def PoolPutLive (p : Program) (addr : Nat) (stack : Nat) (R : RtInv)
    (T : Nat) (Sh : PoolShape) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)), Summary p addr
    (fun s => CallOK s stack 3 ∧ StackRoom s stack 3 ∧ (s.regs 1).toNat = T ∧
      Sh s.mem (s.regs 2).toNat rs ∧ (∀ r ∈ rs, r ∈ L) ∧
      LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 28).toNat s.mem (calleeStack s stack 3))
    (fun s s' => LiveRet R stack 3 L s s' fun _ m =>
      NewSame (s.regs 0).toNat s.mem m ∧
      R.inv b (dropAll L rs) (s.regs 28).toNat (view R.rt (dropAll L rs) m))

end Janus.Contracts.Pool
