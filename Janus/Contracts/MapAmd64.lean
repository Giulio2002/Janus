import Janus.Spec.Map
import Janus.Amd64.TacticExt

/-!
# Contracts of the Go map runtime (amd64)

The amd64 counterparts of `Janus.Contracts.Map` (see that file and docs/RUNTIME-CONTRACTS.md,
"Maps"): the same runtime entry points, the same abstract effects on the map, stated with the
amd64 ABIInternal. Arguments are in `RAX`, `RBX`, `RCX` (`argReg 0..2`), results in `RAX` and
`RBX`; `CALL` pushes the return address, so the callee starts with `[RSP]` holding it and
returns to it with `RSP + 8`; `RBP`, `R14` (`g`) and `X15` (zero) are preserved, every other
general register, `X0`–`X14`, the upper `YMM` halves and the flags are arbitrary afterwards.
A call may write the runtime's private memory, at most `M.depth` bytes below `RSP` (never the
return-address slot `[RSP, RSP + 8)`), and the argument spill slots `[RSP + 8, RSP + 8 + 8·nargs)`
in the caller's frame.
-/

namespace Janus.Contracts.MapAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map

/-- The register file after a Go call (amd64): `RSP` popped past the return address, `RBP` and
`R14` from `f`, everything else from `r`. -/
def keepABI (f r : Nat → W64) : Nat → W64 :=
  fun i => if i = 4 then f 4 + 8 else if i = 5 ∨ i = 14 then f i else r i

@[janus64_exec, janus64_post] theorem keepABI_apply (f r : Nat → W64) (i : Nat) :
    keepABI f r i = if i = 4 then f 4 + 8 else if i = 5 ∨ i = 14 then f i else r i := rfl

/-- The SSE registers after a Go call: `X15` (zero) from `f`, the others from `x`. -/
def keepX15 (f x : Nat → W128) : Nat → W128 := fun i => if i = 15 then f 15 else x i

@[janus64_exec, janus64_post] theorem keepX15_apply (f x : Nat → W128) (i : Nat) :
    keepX15 f x i = if i = 15 then f 15 else x i := rfl

/-- The stack a callee with `nargs` register arguments may write (amd64): `[RSP - stack, RSP)`
below the return-address slot, and the spill slots `[RSP + 8, RSP + 8 + 8·nargs)`. -/
def calleeStack (s : State) (stack nargs : Nat) : List (Nat × Nat) :=
  [((s.regs 4).toNat - stack, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 8 + 8 * nargs)]

/-- What every map runtime call with `nargs` register arguments needs (amd64): the runtime
environment (`M.Env`, with the goroutine in `R14`), the stack guard at least `M.depth` bytes
below `RSP`, an 8-aligned `RSP`, the window `[RSP - M.depth, RSP + 8 + 8·nargs)` writable, below
`2^48` and outside the private memory, `X15 = 0`, the direction flag clear, and a canonical
return address (below `2^47`) at `[RSP]`. -/
def RTPre {K V : Type} (M : MapModel K V) (nargs : Nat) (s : State) : Prop :=
  M.Env s.mem (s.regs 14) ∧ StackGuardOK s M.depth ∧ (s.regs 4).toNat % 8 = 0 ∧
    M.depth ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 8 + 8 * nargs ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - M.depth) (M.depth + 8 + 8 * nargs) true = true ∧
    s.xmm 15 = 0 ∧ s.df = false ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    Outside ((s.regs 4).toNat - M.depth) (M.depth + 8 + 8 * nargs) M.priv

/-- What a caller needs to call the map runtime (amd64) with `RSP` at `frame` bytes below its
entry `RSP` at the callee's entry (its own frame plus the pushed return address), with `above`
bytes of its own caller's frame (return address, spill slots) it uses: the runtime environment,
the stack guard at least `M.depth + frame` bytes below `RSP`, an 8-aligned `RSP`, the window
`[RSP - M.depth - frame, RSP + above)` writable and outside the private memory, and the guard
word `16(g)` outside that window and outside the private memory. -/
def CallerOK {K V : Type} (M : MapModel K V) (s : State) (frame above : Nat) : Prop :=
  M.Env s.mem (s.regs 14) ∧ StackGuardOK s (M.depth + frame) ∧ (s.regs 4).toNat % 8 = 0 ∧
    M.depth + frame ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - (M.depth + frame)) (M.depth + frame + above) true = true ∧
    Outside ((s.regs 4).toNat - (M.depth + frame)) (M.depth + frame + above) M.priv ∧
    Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - (M.depth + frame))
      (M.depth + frame + above) ∧
    Outside ((s.regs 14).toNat + 16) 8 M.priv

/-- `RTPre` at a call site `S` from the caller's `CallerOK` at its entry `s` (amd64). -/
theorem RTPre.of_parts {K V : Type} {M : MapModel K V} {s S : State} {frame above nargs : Nat}
    (hc : CallerOK M s frame above) (henv : M.Env S.mem (s.regs 14))
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (hguard : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame + above) : RTPre M nargs S := by
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, -, -⟩ := hc
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  refine ⟨by rw [hg]; exact henv, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hx, hdf, hra, ?_⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hacc]; exact hg2
  · simp only [stackguard0, regG, regSP, stackguard0Offset, hg, hguard, hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hacc]; exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
  · rw [hsp]; exact Outside.of_sub hout (by omega) (by omega)

/-- `RTPre.of_parts` for a first call: the call state's memory differs from the caller's entry
memory only inside the caller's window. -/
theorem RTPre.of_caller {K V : Type} {M : MapModel K V} (hl : M.Laws) {s S : State}
    {frame above nargs : Nat} (hc : CallerOK M s frame above)
    (hf : MemFrame s.mem S.mem [((s.regs 4).toNat - (M.depth + frame), (s.regs 4).toNat + above)])
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame + above) : RTPre M nargs S := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, -, -⟩, -, -, -, -, hout, hgd, -⟩ := hc'
  simp only [regG, stackguard0Offset, Spec.Disjoint] at hg1 hgd
  refine RTPre.of_parts hc (hl.env_frame _ _ _ henv
    (Agrees.of_window hf (Outside.of_sub hout (by omega) (by omega)))) hf.accessible
    (hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)) hsp hg hx hdf hra hfr hn

/-- The ranges a map runtime call may write at call state `s`. -/
def rtWrites {K V : Type} (M : MapModel K V) (s : State) (nargs : Nat) : List (Nat × Nat) :=
  M.priv ++ calleeStack s M.depth nargs

attribute [janus64_exec, janus64_post] rtWrites calleeStack

/-- Maps other than the one at `except` keep their contents from `m` to `m'`. -/
def OthersKept {K V : Type} (M : MapModel K V) (m m' : Memory) (except : Nat) : Prop :=
  ∀ mp f, mp ≠ except → M.Rep m mp f → M.Rep m' mp f

/-- The return of a map runtime call from call state `s` to `s'` (amd64), with the call-specific
facts `P r m` about the result registers `r` and the new memory `m`. -/
def RTReturn {K V : Type} (M : MapModel K V) (nargs : Nat) (extra : List (Nat × Nat))
    (except : Nat) (s s' : State) (P : (Nat → W64) → Memory → Prop) : Prop :=
  ∃ r x y fl m zh kr,
    s' = { s with regs := keepABI s.regs r, xmm := keepX15 s.xmm x, ymmHi := y,
                  flags := fl, mem := m, rip := retAddrOf s, zmmHi := zh, kreg := kr } ∧
    MemFrame s.mem m (rtWrites M s nargs ++ extra) ∧ M.Env m (s.regs 14) ∧
    OthersKept M s.mem m except ∧ P r m

/-- The value slot `p` returned by an access: readable, in the runtime's memory, holding `v`. -/
def SlotHolds {K V : Type} (M : MapModel K V) (m : Memory) (p : Nat) (v : BitVec 64) : Prop :=
  m.accessible p 8 false = true ∧ InRanges p 8 M.priv ∧ m.readLE p 8 = v.toNat

/-- `runtime.mapaccess1_fast64(t, m, k)`: returns a pointer to `m[k]`, or to a zero value if
`k` is absent or `m` is nil. The map is unchanged. -/
def Access1 (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      IsMap M m (s.regs 3).toNat f ∧ SlotHolds M m (r 0).toNat ((f (s.regs 1)).getD 0))

/-- `runtime.mapaccess2_fast64(t, m, k)`: as `Access1`, and the low byte of `RBX` is `1` if `k`
is present, `0` if not. -/
def Access2 (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      IsMap M m (s.regs 3).toNat f ∧ SlotHolds M m (r 0).toNat ((f (s.regs 1)).getD 0) ∧
      (r 3).toNat % 256 = (f (s.regs 1)).isSome.toNat)

/-- `runtime.mapassign_fast64(t, m, k)` on a non-nil map: returns a writable value slot `p` in
the runtime's memory such that storing any `v` there (8 bytes) makes the map `f` with `k ↦ v`.
The compiled `m[k] = v` performs exactly that store right after the call. -/
def Assign (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 3).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      m.accessible (r 0).toNat 8 true = true ∧ InRanges (r 0).toNat 8 M.priv ∧
      ∀ v : BitVec 64, M.Rep (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 3).toNat (f.set (s.regs 1) v) ∧
        M.Env (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 14) ∧
        OthersKept M m (m.writeLE (r 0).toNat 8 v.toNat) (s.regs 3).toNat)

/-- `runtime.mapdelete_fast64(t, m, k)`: removes `k` (nothing happens for a nil map or an absent
key). -/
def Delete (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun _ m =>
      IsMap M m (s.regs 3).toNat (f.erase (s.regs 1)))

/-- `runtime.mapclear(t, m)`: removes every entry (nothing happens for a nil map). -/
def Clear {K V : Type} (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel K V) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 2 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f)
    (fun s s' => RTReturn M 2 [] (s.regs 3).toNat s s' fun _ m =>
      IsMap M m (s.regs 3).toNat AMap.empty)

/-- `runtime.makemap_small()`: returns a new, non-nil, empty map, distinct from every map that
existed before. -/
def MakeSmall {K V : Type} (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel K V) : Prop :=
  Janus.Amd64.Tactic.Summary p addr (fun s => RTPre M 0 s)
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
def IterStart (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f ∧
      s.mem.accessible (s.regs 1).toNat iterSize true = true ∧
      Outside (s.regs 1).toNat iterSize M.priv)
    (fun s s' => RTReturn M 3 [((s.regs 1).toNat, (s.regs 1).toNat + iterSize)] (s.regs 3).toNat
      s s' fun _ m =>
      IsMap M m (s.regs 3).toNat f ∧ ∃ ks, Keys f ks ∧
        M.Iter m (s.regs 1).toNat (s.regs 3).toNat f ks ∧ View64 M m (s.regs 1).toNat f ks)

/-- `runtime.mapIterNext(it)`: advances an iterator that has the key `k` and then `ks` left to
produce, over a map that has not changed since the iteration started. -/
def IterNext (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel (BitVec 64) (BitVec 64)) : Prop :=
  ∀ mp f k ks, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 1 s ∧ IsMap M s.mem mp f ∧ M.Iter s.mem (s.regs 0).toNat mp f (k :: ks) ∧
      Outside (s.regs 0).toNat iterSize M.priv)
    (fun s s' => RTReturn M 1 [((s.regs 0).toNat, (s.regs 0).toNat + iterSize)] mp s s' fun _ m =>
      IsMap M m mp f ∧ M.Iter m (s.regs 0).toNat mp f ks ∧ View64 M m (s.regs 0).toNat f ks)

/-- `runtime.mapaccess2(t, m, kp)` for `[16]byte` keys passed by pointer (the generic path):
the key is the 16 bytes at `kp`, read little-endian. -/
def Access2Ptr (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel (BitVec 128) (BitVec 64)) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f ∧
      s.mem.accessible (s.regs 1).toNat 16 false = true)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      let k := BitVec.ofNat 128 (s.mem.readLE (s.regs 1).toNat 16)
      IsMap M m (s.regs 3).toNat f ∧ SlotHolds M m (r 0).toNat ((f k).getD 0) ∧
      (r 3).toNat % 256 = (f k).isSome.toNat)

end Janus.Contracts.MapAmd64
