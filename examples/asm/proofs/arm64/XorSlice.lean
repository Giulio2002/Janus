import Extracted

/-!
# `XorSlice(xs []uint64) uint64` (Go assembly, ABI0, arm64): the XOR of the elements

```
TEXT ·XorSlice(SB), NOSPLIT, $0-32         // examples/asm/asm_arm64.s
	MOVD	xs_base+0(FP), R0
	MOVD	xs_len+8(FP), R1
	MOVD	$0, R2
loop:
	CBZ	R1, done
	MOVD.P	8(R0), R3
	EOR	R3, R2, R2
	SUB	$1, R1, R1
	B	loop
done:
	MOVD	R2, ret+24(FP)
	RET
```

**Guarantee.** For every slice header `(ptr, len, cap)` passed in the ABI0 frame (words 0–2 at
`8(RSP)`, the result word 3 at `32(RSP)`) and every ABI0 call state of
`example.com/asm.XorSlice.abi0` (`CallSetup0`: the frame writable, `RSP` aligned) in which the
`8·len` bytes at `ptr` are readable, the call returns to the caller (never faulting), restores
`RSP`, `g`, `FP` and `R18` (`ABIReturn0`), its result word is `xs[0] ^ … ^ xs[len-1]` (the
64-bit words at `ptr + 8k` before the call), and it writes nothing but the result word. This
holds for every length, so the loop terminates and has no out-of-bounds access. The slice may
overlap the frame: the elements are all read before the result is stored.

**How.** `loop` is the invariant at the loop head (`CBZ R1, done`): after `i` iterations
`R0 = ptr + 8i`, `R1 = len - i` and the accumulator `R2` is the XOR of the first `i` words. It is
proved by induction on the iterations left, one iteration per `janus_run until [head]`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec

namespace Proof

/-- XOR of the `n` little-endian 64-bit words at `p`. -/
def xorWords (m : Memory) (p : Nat) : Nat → W64
  | 0 => 0
  | n + 1 => xorWords m p n ^^^ BitVec.ofNat 64 (m.readLE (p + 8 * n) 8)

/-- The loop head `CBZ R1, done`. -/
abbrev head : Nat := Extracted.entry + 0xc

/-- What the call guarantees, about the call state `s` and the return state `s'`. -/
def Post (ptr len : BitVec 64) (s s' : State) : Prop :=
  results0 s s' 3 1 = [xorWords s.mem ptr.toNat len.toNat] ∧
    OnlyWrites s.mem s'.mem (s.sp.toNat + 32) 8

theorem loop (ptr len : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hp : s.mem.accessible ptr.toNat (8 * len.toNat) false = true)
    (hp' : ptr.toNat + 8 * len.toNat ≤ 2 ^ 48)
    (hfb : s.sp.toNat + 40 ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hfacc : s.mem.accessible (s.sp.toNat + 8) 32 true = true) :
    ∀ n (S : State) (i : Nat), i + n = len.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = BitVec.ofNat 64 (ptr.toNat + 8 * i) →
      S.regs 1 = BitVec.ofNat 64 n → S.regs 2 = xorWords s.mem ptr.toNat i →
      S.regs 30 = BitVec.ofNat 64 ret → S.sp = s.sp → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 18 = s.regs 18 → S.mem = s.mem →
      Reaches (Extracted.program.withExit ret) S
        (IsReturn fun s' => ABIReturn0 s s' ∧ Post ptr len s s') := by
  intro n
  induction n with
  | zero =>
    intro S i hn hpc h0 h1 h2 h30 hsp h28 h29 h18 hm
    janus_run [Post]
    rw [show i = len.toNat by omega]
  | succ n ih =>
    intro S i hn hpc h0 h1 h2 h30 hsp h28 h29 h18 hm
    janus_run until [head]
    apply ih _ (i + 1)
    all_goals janus_simp [xorWords]
    · omega
    · have := len.isLt
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · have := len.isLt
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega

theorem correctness (ptr len cap : BitVec 64) :
    Ensures0 Extracted.program Extracted.entry [ptr, len, cap] 1
      (fun s => Ptr s.mem ptr (8 * len.toNat) false)
      (fun s s' => results0 s s' 3 1 = [xorWords s.mem ptr.toNat len.toNat] ∧
        OnlyWrites s.mem s'.mem (s.sp.toNat + 32) 8) := by
  intro ret hret s hs ⟨hp, hp'⟩
  janus_intro0 hs
  janus_run until [head]
  exact loop ptr len ret hret s hp hp' h_fb h_al h_facc len.toNat _ 0 (by simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp [xorWords]) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)

end Proof
