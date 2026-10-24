import Janus.Spec.Map
import Janus.Tactic.Core
import Janus.Contracts.Alloc

/-!
# Contracts of the Go map runtime (arm64)

Go 1.26 lowers map operations to calls of `internal/runtime/maps` functions (linknamed into
`runtime`). A theorem about a function that uses a map is stated about the extracted code linked
with **any** implementation of those runtime functions (`Program.link impl`), and takes the
behaviour of each one as a hypothesis: a `Summary` at its address (`Program.contractAddr`) whose
pre- and postcondition are the definitions below. The printed statement names every contract it
relies on. See docs/RUNTIME-CONTRACTS.md, "Maps", for what each assumes and why.

| Go | Runtime call (Go 1.26, `map[uint64]V` keys use the `_fast64` variants) | Contract |
| --- | --- | --- |
| `v := m[k]` | `runtime.mapaccess1_fast64(t, m, k) *V` | `Access1` |
| `v, ok := m[k]` | `runtime.mapaccess2_fast64(t, m, k) (*V, bool)` | `Access2` |
| `m[k] = v` | `runtime.mapassign_fast64(t, m, k) *V`, then a store through the result | `Assign` |
| `delete(m, k)` | `runtime.mapdelete_fast64(t, m, k)` | `Delete` |
| `make(map[K]V)` | `runtime.makemap_small() *Map` | `MakeSmall` |
| `clear(m)` | `runtime.mapclear(t, m)` | `Clear` |
| `for k, v := range m` | `runtime.mapIterStart(t, m, it)`, `runtime.mapIterNext(it)` | `IterStart`, `IterNext` |
| `len(m)` | inline: `0` if `m` is nil, else the header's first word | `MapModel.Laws.len` |
| `v, ok := m[*kp]` (`[16]byte` keys) | `runtime.mapaccess2(t, m, kp) (*V, bool)` | `Access2Ptr` |

Every contract has the same frame (`RTReturn`): the call returns to `X30` with `SP`, `X18`,
`X28` (`g`) and `X29` preserved, every other general register, the SIMD registers and the flags
arbitrary, the memory regions unchanged, and bytes changed only in the runtime's private memory
(`M.priv`), in the caller's memory the call is given (the iterator struct of `IterStart`
and `IterNext`), in the stack below `SP` (at most `M.depth` bytes, never the caller's frame-pointer
slot `[SP-8, SP)`) and in the argument spill slots `[SP+8, SP+8+8·nargs)` that Go's ABI lets a
callee write. Maps other than the one operated on keep their contents, and `M.Env` (the runtime
is usable) is preserved. Each precondition requires `RTPre` (the runtime environment, stack
room and an admissible `X30`) and, for an operation on a map, `M.Typ t` for the type descriptor
`t` in `X0`.

**Not covered.** A nil map passed to `mapassign` panics in the runtime
(`panic(plainError("assignment to entry in nil map"))`); the `Assign` contract requires a
non-nil map, so no theorem here says anything about that call. The runtime's detection of
concurrent map writes (`fatal("concurrent map writes")`) cannot trigger in the single-threaded
model and is not part of any contract. Modifying a map during a `range` over it is not covered
(`IterNext` requires the map unchanged since `IterStart`).
-/

namespace Janus.Contracts.Map

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts

/-- The register file after a Go call: `X18`, `X28`, `X29` from `f`, everything else from `r`. -/
def keepABI (f r : Nat → W64) : Nat → W64 :=
  fun i => if i = 18 ∨ i = 28 ∨ i = 29 then f i else r i

@[janus_exec, janus_post] theorem keepABI_apply (f r : Nat → W64) (i : Nat) :
    keepABI f r i = if i = 18 ∨ i = 28 ∨ i = 29 then f i else r i := rfl

/-- What every map runtime call with `nargs` register arguments needs: the runtime environment
(`M.Env`, with the goroutine in `X28`), the stack guard at least `M.depth` bytes below `SP` (so
no stack growth), the ABI conditions of `Contracts.CallOK` (admissible `X30`, aligned `SP`, the
window `[SP - M.depth, SP + 8 + 8·nargs)` writable), and that window outside the runtime's
private memory. -/
def RTPre {K V : Type} (M : MapModel K V) (nargs : Nat) (s : State) : Prop :=
  M.Env s.mem (s.regs 28) ∧ StackGuardOK s M.depth ∧ CallOK s M.depth nargs ∧
    Outside (s.sp.toNat - M.depth) (M.depth + 8 + 8 * nargs) M.priv

/-- The byte ranges a map runtime call with `nargs` register arguments may write, at call state
`s`: the private memory, the stack below `SP` (`M.depth` bytes, not the caller's frame-pointer
slot) and the argument spill slots above `SP`. -/
def rtWrites {K V : Type} (M : MapModel K V) (s : State) (nargs : Nat) : List (Nat × Nat) :=
  M.priv ++ calleeStack s M.depth nargs

attribute [janus_exec, janus_post] rtWrites

/-- What a caller needs to call the map runtime from inside a frame of `frame` bytes below its
`SP` (so the runtime runs with `SP - frame`), with `above` bytes of its caller's frame
(argument spill slots) it may write: the runtime environment, the stack guard at least
`M.depth + frame` bytes below `SP`, an aligned `SP`, `M.depth ≥ 8` (`CallOK`), the window
`[SP - M.depth - frame, SP + above)` writable and outside the private memory, and the guard word
`16(g)` outside that window and outside the private memory (no map operation changes it). -/
def CallerOK {K V : Type} (M : MapModel K V) (s : State) (frame above : Nat) : Prop :=
  M.Env s.mem (s.regs 28) ∧ StackGuardOK s (M.depth + frame) ∧ s.sp.toNat % 16 = 0 ∧
    8 ≤ M.depth ∧ M.depth + frame ≤ s.sp.toNat ∧ s.sp.toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible (s.sp.toNat - (M.depth + frame)) (M.depth + frame + above) true = true ∧
    Outside (s.sp.toNat - (M.depth + frame)) (M.depth + frame + above) M.priv ∧
    Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - (M.depth + frame)) (M.depth + frame + above) ∧
    Outside ((s.regs 28).toNat + 16) 8 M.priv

/-- The contract precondition `RTPre` at a call site `S`, from the caller's `CallerOK` at its
entry state `s`: `S` is `frame` bytes below the caller's `SP`, keeps `g`, has an admissible
return address in `X30`, the same accessible ranges and guard word as at entry, and a memory in
which the runtime environment holds (`henv`). -/
theorem RTPre.of_parts {K V : Type} {M : MapModel K V} {s S : State} {frame above nargs : Nat}
    (hc : CallerOK M s frame above) (henv : M.Env S.mem (s.regs 28))
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (hguard : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) (hfr : frame % 16 = 0)
    (hn : 8 + 8 * nargs ≤ frame + above) : RTPre M nargs S := by
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
memory only inside the caller's window (its frame record and spills). -/
theorem RTPre.of_caller {K V : Type} {M : MapModel K V} (hl : M.Laws) {s S : State}
    {frame above nargs : Nat} (hc : CallerOK M s frame above)
    (hf : MemFrame s.mem S.mem [(s.sp.toNat - (M.depth + frame), s.sp.toNat + above)])
    (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) (hfr : frame % 16 = 0)
    (hn : 8 + 8 * nargs ≤ frame + above) : RTPre M nargs S := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, -, -⟩, -, -, -, -, -, hout, hgd⟩ := hc'
  simp only [regG, stackguard0Offset, Spec.Disjoint] at hg1 hgd
  refine RTPre.of_parts hc (hl.env_frame _ _ _ henv
    (Agrees.of_window hf (Outside.of_sub hout (by omega) (by omega)))) hf.accessible
    (hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)) hsp hg hlr hlr' hfr hn

/-- Maps other than the one at `except` keep their contents from `m` to `m'`. -/
def OthersKept {K V : Type} (M : MapModel K V) (m m' : Memory) (except : Nat) : Prop :=
  ∀ mp f, mp ≠ except → M.Rep m mp f → M.Rep m' mp f

/-- The return of a map runtime call from call state `s` to `s'` (see the module comment), with
the call-specific facts `P r m` about the result registers `r` and the new memory `m`. -/
def RTReturn {K V : Type} (M : MapModel K V) (nargs : Nat) (extra : List (Nat × Nat))
    (except : Nat) (s s' : State) (P : (Nat → W64) → Memory → Prop) : Prop :=
  ∃ r v fl m, s' = { s with regs := keepABI s.regs r, vregs := v, flags := fl, mem := m,
                            pc := s.regs 30 } ∧
    MemFrame s.mem m (rtWrites M s nargs ++ extra) ∧ M.Env m (s.regs 28) ∧ OthersKept M s.mem m except ∧
    P r m

/-- The value slot `p` returned by an access: readable, in the runtime's memory, holding `v`. -/
def SlotHolds {K V : Type} (M : MapModel K V) (m : Memory) (p : Nat) (v : BitVec 64) : Prop :=
  m.accessible p 8 false = true ∧ InRanges p 8 M.priv ∧ m.readLE p 8 = v.toNat

/-- `runtime.mapaccess1_fast64(t, m, k)`: returns a pointer to `m[k]`, or to a zero value if
`k` is absent or `m` is nil. The map is unchanged. -/
def Access1 (p : Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      IsMap M m (s.regs 1).toNat f ∧ SlotHolds M m (r 0).toNat ((f (s.regs 2)).getD 0))

/-- `runtime.mapaccess2_fast64(t, m, k)`: as `Access1`, and the low byte of `X1` is `1` if `k`
is present, `0` if not. -/
def Access2 (p : Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      IsMap M m (s.regs 1).toNat f ∧ SlotHolds M m (r 0).toNat ((f (s.regs 2)).getD 0) ∧
      (r 1).toNat % 256 = (f (s.regs 2)).isSome.toNat)

/-- `runtime.mapassign_fast64(t, m, k)` on a non-nil map: returns a writable value slot `p` in
the runtime's memory such that storing any `v` there (8 bytes) makes the map `f` with `k ↦ v`.
The compiled `m[k] = v` performs exactly that store right after the call. -/
def Assign (p : Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 1).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      m.accessible (r 0).toNat 8 true = true ∧ InRanges (r 0).toNat 8 M.priv ∧
      ∀ v : BitVec 64, M.Rep (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 1).toNat (f.set (s.regs 2) v) ∧
        M.Env (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 28) ∧
        OthersKept M m (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 1).toNat)

/-- `runtime.mapdelete_fast64(t, m, k)`: removes `k` (nothing happens for a nil map or an absent
key). -/
def Delete (p : Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun _ m =>
      IsMap M m (s.regs 1).toNat (f.erase (s.regs 2)))

/-- `runtime.mapclear(t, m)`: removes every entry (nothing happens for a nil map). -/
def Clear {K V : Type} (p : Program) (addr : Nat) (M : MapModel K V) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 2 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f)
    (fun s s' => RTReturn M 2 [] (s.regs 1).toNat s s' fun _ m =>
      IsMap M m (s.regs 1).toNat AMap.empty)

/-- `runtime.makemap_small()`: returns a new, non-nil, empty map, distinct from every map that
existed before. -/
def MakeSmall {K V : Type} (p : Program) (addr : Nat) (M : MapModel K V) : Prop :=
  Summary p addr (fun s => RTPre M 0 s)
    (fun s s' => RTReturn M 0 [] 0 s s' fun r m =>
      (r 0).toNat ≠ 0 ∧ M.Rep m (r 0).toNat AMap.empty ∧
      ∀ mp f, M.Rep s.mem mp f → mp ≠ (r 0).toNat)

/-- What the compiled loop reads from an iterator over a `map[uint64]uint64`
(`IterView` with 8-byte keys). -/
abbrev View64 (M : MapModel (BitVec 64) (BitVec 64)) (m : Memory) (it : Nat)
    (f : AMap (BitVec 64) (BitVec 64)) (ks : List (BitVec 64)) : Prop :=
  IterView M.priv 8 (BitVec.ofNat 64) m it f ks

/-- `runtime.mapIterStart(t, m, it)`: starts an iteration over `m` (nil: no keys) with the
iterator struct at `it` (`iterSize` writable bytes in the caller's memory, outside the private
memory). The keys come in **some** order `ks`: the contract does not say which, so a theorem
proved with it holds for every iteration order. -/
def IterStart (p : Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f ∧
      s.mem.accessible (s.regs 2).toNat iterSize true = true ∧
      Outside (s.regs 2).toNat iterSize M.priv)
    (fun s s' => RTReturn M 3 [((s.regs 2).toNat, (s.regs 2).toNat + iterSize)] (s.regs 1).toNat
      s s' fun _ m =>
      IsMap M m (s.regs 1).toNat f ∧ ∃ ks, Keys f ks ∧
        M.Iter m (s.regs 2).toNat (s.regs 1).toNat f ks ∧ View64 M m (s.regs 2).toNat f ks)

/-- `runtime.mapIterNext(it)`: advances an iterator that has the key `k` and then `ks` left to
produce, over a map that has not changed since the iteration started. -/
def IterNext (p : Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ mp f k ks, Summary p addr
    (fun s => RTPre M 1 s ∧ IsMap M s.mem mp f ∧ M.Iter s.mem (s.regs 0).toNat mp f (k :: ks) ∧
      Outside (s.regs 0).toNat iterSize M.priv)
    (fun s s' => RTReturn M 1 [((s.regs 0).toNat, (s.regs 0).toNat + iterSize)] mp s s' fun _ m =>
      IsMap M m mp f ∧ M.Iter m (s.regs 0).toNat mp f ks ∧ View64 M m (s.regs 0).toNat f ks)

/-- `runtime.mapaccess2(t, m, kp)` for `[16]byte` keys passed by pointer (the generic path):
the key is the 16 bytes at `kp`, read little-endian. -/
def Access2Ptr (p : Program) (addr : Nat) (M : MapModel (BitVec 128) (BitVec 64)) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f ∧
      s.mem.accessible (s.regs 2).toNat 16 false = true)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      let k := BitVec.ofNat 128 (s.mem.readLE (s.regs 2).toNat 16)
      IsMap M m (s.regs 1).toNat f ∧ SlotHolds M m (r 0).toNat ((f k).getD 0) ∧
      (r 1).toNat % 256 = (f k).isSome.toNat)

end Janus.Contracts.Map
