import Extracted

/-!
# `CallXor(xs []uint64) uint64` (Go, arm64): a direct ABI0 call of Go assembly

```go
func CallXor(xs []uint64) uint64 { return XorSlice(xs) ^ 1 }   // examples/asm/asm.go
```

The compiler knows that `XorSlice` is assembly in the same package and calls it directly with
ABI0: it stores the three slice words into its outgoing argument area (`MOVD R0, 8(RSP)`,
`STP (R1, R2), 16(RSP)`), `BL example.com/asm.XorSlice.abi0`, and loads the result word
(`MOVD 32(RSP), R0`) — no wrapper.

**Guarantee.** For every slice `(ptr, len, cap)` passed in `X0`–`X2` (ABIInternal) and every Go
call state of `example.com/asm.CallXor` in which the stack-growth prologue falls through, the
stack window `[SP-56, SP+16)` is writable (`CallXor`'s 48-byte frame, the saved frame pointer,
the spill slot of `xs.ptr` in the caller's frame), and the `8·len` bytes at `ptr` are readable
and outside that window, the call returns (never faulting or panicking), obeys the ABIInternal
return rules, and `X0 = xs[0] ^ … ^ xs[len-1] ^ 1`.

**How (composition).** The assembly callee is proved once, from *any* state at its entry, as an
ABI0 callee summary `xor_summary : Summary0 … XorPre XorQ`: when the frame words describe a
readable slice it returns to `X30` with every register but `R18`, `g`, `FP` unspecified
(`Ret0`) and memory equal, outside its (empty) scratch range, to the call state's memory with
the XOR in result word 3 (`XorQ`). `janus_run calls [xor_summary]` executes `CallXor` and uses
the summary at the `BL`; the callee's code is not re-executed. `xorWords_writeLE` moves the
XOR across `CallXor`'s own stores (the slice is outside its stack window).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec

namespace Proof

def xorWords (m : Memory) (p : Nat) : Nat → W64
  | 0 => 0
  | n + 1 => xorWords m p n ^^^ BitVec.ofNat 64 (m.readLE (p + 8 * n) 8)

/-- A store outside the words does not change their XOR. -/
theorem xorWords_writeLE (m : Memory) (a v p n : Nat) (h : a + 8 ≤ p ∨ p + 8 * n ≤ a) :
    xorWords (m.writeLE a 8 v) p n = xorWords m p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorWords]
    rw [ih (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

abbrev callee : Nat := segAddr Extracted.program "example.com/asm.XorSlice.abi0"
abbrev head : Nat := callee + 0xc

/-- What the callee needs at its entry `s`. -/
def XorPre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧
  s.sp.toNat % 16 = 0 ∧ s.sp.toNat + 40 ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat + 8) 32 true = true ∧
  s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8 ≤ 2 ^ 48 ∧
  s.mem.accessible (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) false = true

/-- What the callee guarantees about the memory it returns with: the XOR of the slice in the
result word, and nothing else written. -/
abbrev XorQ (s : State) (m : Memory) : Prop :=
  MemFrame (s.mem.writeLE (s.sp.toNat + 32) 8
    (xorWords s.mem (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8)).toNat) m
    [(s.sp.toNat, s.sp.toNat)]

theorem loop (s : State) (ptr len : Nat) (hptr : s.mem.readLE (s.sp.toNat + 8) 8 = ptr)
    (hlen : s.mem.readLE (s.sp.toNat + 16) 8 = len) (hpre : XorPre s) :
    ∀ n (S : State) (i : Nat), i + n = len →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = BitVec.ofNat 64 (ptr + 8 * i) →
      S.regs 1 = BitVec.ofNat 64 n → S.regs 2 = xorWords s.mem ptr i →
      S.regs 30 = s.regs 30 → S.sp = s.sp → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 18 = s.regs 18 → S.mem = s.mem → S.fpcr = s.fpcr →
      S.tpidr = s.tpidr → S.dczid = s.dczid →
      ReachesRet Extracted.program (s.regs 30) S (fun s' => Ret0 s s' (XorQ s)) := by
  obtain ⟨hr1, hr2, hal, hfb, hfacc, hp', hp⟩ := hpre
  rw [hptr, hlen] at hp hp'
  have hlt : len < 2 ^ 64 := hlen ▸ Memory.readLE_lt _ _ 8
  intro n
  induction n with
  | zero =>
    intro S i hn hpc h0 h1 h2 h30 hsp h28 h29 h18 hm hfpcr htp hdc
    janus_run [XorQ]
    refine ⟨htp, hdc, ?_⟩
    rw [hptr, hlen, show i = len by omega]
    exact MemFrame.refl _ _
  | succ n ih =>
    intro S i hn hpc h0 h1 h2 h30 hsp h28 h29 h18 hm hfpcr htp hdc
    janus_run until [head]
    refine ih _ (i + 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htp hdc
    all_goals janus_simp [xorWords]
    · omega
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega

/-- `XorSlice.abi0` as a callee: from any state at its entry satisfying `XorPre`. -/
theorem xor_summary : Summary0 Extracted.program callee XorPre XorQ := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨hr1, hr2, hal, hfb, hfacc, hp', hp⟩ := hpre'
  janus_run until [head]
  exact loop s _ _ rfl rfl hpre (s.mem.readLE (s.sp.toNat + 16) 8) _ 0 (by simp) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp [xorWords]) (by janus_simp) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) rfl rfl rfl

theorem correctness (ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [ptr, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 56 16 ∧ Ptr s.mem ptr (8 * len.toNat) false ∧
        Disjoint ptr.toNat (8 * len.toNat) (s.sp.toNat - 56) 72)
      (fun s s' => s'.regs 0 = xorWords s.mem ptr.toNat len.toNat ^^^ 1#64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hst⟩, ⟨hp, hp'⟩, hd⟩
  janus_intro hs
  simp only [Disjoint] at hd
  janus_run calls [xor_summary]
  simp (disch := omega) only [xorWords_writeLE]

end Proof
