import Extracted

/-!
# `struct k_big k_big(int64_t x, int64_t y)` (C, amd64): a MEMORY-class result through `RDI`

```c
struct k_big { int64_t a, b, c, d; };
struct k_big k_big(int64_t x, int64_t y) { struct k_big r = { x + y, x - y, x * y, x ^ y }; return r; }
```

**Guarantee.** For all 64-bit `x`, `y`, every System V call of the gcc-compiled `k_big` whose
arguments are where the classification puts them — the 32-byte result is MEMORY, so the caller
passes the address of a writable result buffer as a hidden first argument in `RDI`
(`CCallA.retBuf`) and `x`, `y` go in `RSI`, `RDX` — returns, restores what System V requires
(`CReturn`), leaves `{x + y, x - y, x * y, x ^ y}` (mod 2^64) in the buffer, returns the buffer's
address in `RAX` (`ResultAt`), and writes no other memory.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.C Janus.Spec

namespace Proof

def big : CType := .struct [.int 8 true, .int 8 true, .int 8 true, .int 8 true]
def sig : SysV.Sig := ⟨some big, [.int 8 true, .int 8 true], none⟩

theorem passing : sig.passing = [.direct [⟨0, 8, .gpr 6⟩], .direct [⟨0, 8, .gpr 2⟩]] := by decide
theorem result : SysV.result big = .indirect (.gpr 7) := by decide
theorem size_big : CType.size big = 32 := by decide

def quad (a b c d : BitVec 64) : Nat :=
  a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + 2 ^ 192 * d.toNat

/-- The memory after `k_big` wrote the struct at `a` (its four stores, in gcc's order). -/
def bigMem (m : Memory) (a : Nat) (x y : BitVec 64) : Memory :=
  (((m.writeLE a 8 (x.toNat + y.toNat)).writeLE (a + 8) 8 (18446744073709551616 - y.toNat + x.toNat)).writeLE
    (a + 24) 8 (x ^^^ y).toNat).writeLE (a + 16) 8 (x * y).toNat

theorem bigMem_read (m : Memory) (a : Nat) (x y : BitVec 64) :
    (bigMem m a x y).readLE a 32 = quad (x + y) (x - y) (x * y) (x ^^^ y) := by
  simp only [bigMem, readLE_32]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  simp only [quad, BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow]
  have := (x ^^^ y).isLt
  have := (x * y).isLt
  omega

def vals (x y : BitVec 64) : List Nat := [x.toNat, y.toNat]

def SPre (vs : List Nat) (s : State) : Prop :=
  ArgsAt s sig.args vs sig.passing ∧ RetBuf s sig ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.df = false

theorem spre_iff (x y : BitVec 64) (s : State) :
    SPre (vals x y) s ↔ s.regs 6 = x ∧ s.regs 2 = y ∧ (s.regs 7).toNat + 32 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 7).toNat 32 true = true ∧
      ((s.regs 7).toNat + 32 ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 8 ≤ (s.regs 7).toNat) ∧
      (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
      s.df = false := by
  unfold SPre
  have hrb : RetBuf s sig ↔ (s.regs 7).toNat + 32 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 7).toNat 32 true = true ∧
      ((s.regs 7).toNat + 32 ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 8 ≤ (s.regs 7).toNat) := by
    constructor
    · intro h; have := h big rfl result; rwa [size_big] at this
    · intro h t ht _; cases ht; rw [size_big]; exact h
  rw [passing, hrb]
  simp only [vals, sig, ArgsAt, ArgAt, PiecesAt, and_true, pieceAt_gpr_word, and_assoc]

abbrev SPost (x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 3 = s.regs 3 ∧ s'.regs 5 = s.regs 5 ∧
    s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    s'.regs 15 = s.regs 15 ∧ s'.df = false ∧ s'.mxcsr = s.mxcsr ∧ s'.fpucw = s.fpucw ∧
    s'.mem = bigMem s.mem (s.regs 7).toNat x y ∧ s'.regs 0 = s.regs 7

theorem summary (x y : BitVec 64) :
    Summary Extracted.program Extracted.entry (SPre (vals x y)) (SPost x y) := by
  intro s hpc hpre
  obtain ⟨h6, h2, hb, hacc, hdisj, hsb, hsa, hra, hdf⟩ := (spre_iff x y s).1 hpre
  janus64_run
  simp only [SPost, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, true_and]
  exact ⟨rfl, rfl, trivial⟩

/-- **`k_big` under the System V calling convention**: the struct is written through the hidden
`RDI` pointer, whose value comes back in `RAX`. -/
theorem correctness (x y : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig (vals x y) (fun s => CStack s 0 8)
      (fun s s' v => v = quad (x + y) (x - y) (x * y) (x ^^^ y) ∧
        MemFrame s.mem s'.mem [((s.regs 7).toNat, (s.regs 7).toNat + 32)]) :=
  CEnsuresA.of_summary (summary x y)
    (fun _ s hret hs ⟨_, _, hnw, hst⟩ => by
      simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add] at hnw hst
      exact ⟨hs.args, hs.retBuf, hnw, Janus.Arm64.Memory.accessible_weaken _ hst, hs.ret_lt hret,
        hs.df⟩)
    (fun s _ _ ⟨hsp, h3, h5, h12, h13, h14, h15, hdf, hmx, hfw, hm, h0⟩ =>
      ⟨CReturn.of_eqs hsp h3 h5 h12 h13 h14 h15 hdf hmx hfw, _,
        by simp only [Returned, sig, result, ResultAt, size_big, hm, bigMem_read, h0, and_true], rfl,
        by rw [hm]; unfold bigMem; janus_frame⟩)

namespace Witness

def ret : Nat := 0x1000
def wsp : Nat := 0x20008  -- addr-ok: a chosen stack window, not a binary address
def P : Nat := 0x100000  -- addr-ok: a chosen result buffer
def x0 : BitVec 64 := 5#64
def y0 : BitVec 64 := 3#64

def smem : Janus.Arm64.Memory :=
  ⟨fun a => if wsp ≤ a ∧ a < wsp + 8 then BitVec.ofNat 8 (ret / 256 ^ (a - wsp)) else 0,
   [⟨wsp - 64, 128, true⟩, ⟨P, 32, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 6 then x0 else if i = 2 then y0 else if i = 7 then BitVec.ofNat 64 P
      else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := smem }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem spre : SPre (vals x0 y0) s0 :=
  (spre_iff x0 y0 s0).2 ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem call : CCallA (Extracted.program.withExit ret) Extracted.entry sig (vals x0 y0) s0 :=
  ⟨rfl, by decide, by decide, rfl, spre.1, spre.2.1, by intro h; simp [sig] at h⟩

theorem stack : CStack s0 0 8 := ⟨by decide, by decide, by decide, by decide⟩

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (x y : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCallA (Extracted.program.withExit ret) Extracted.entry sig (vals x y) s ∧ (CStack s 0 8) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧
      (∃ v, Returned sig s s' v ∧ (v = quad (x + y) (x - y) (x * y) (x ^^^ y) ∧
        MemFrame s.mem s'.mem [((s.regs 7).toNat, (s.regs 7).toNat + 32)]))) :=
  ⟨x0, y0, ret, s0, hret, call, stack, correctness x0 y0 ret hret s0 call stack⟩

end Witness

end Proof
