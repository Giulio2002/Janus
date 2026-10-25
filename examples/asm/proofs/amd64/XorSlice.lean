import Janus
import Extracted

/-!
# `XorSlice(xs []uint64) uint64` (Go assembly, ABI0, amd64): the XOR of the elements

```
TEXT ·XorSlice(SB), NOSPLIT, $0-32         // examples/asm/asm_amd64.s
	MOVQ xs_base+0(FP), SI ; MOVQ xs_len+8(FP), CX ; XORQ AX, AX
loop:	TESTQ CX, CX ; JZ done ; XORQ (SI), AX ; ADDQ $8, SI ; DECQ CX ; JMP loop
done:	MOVQ AX, ret+24(FP) ; RET
```

**Guarantee.** For every slice header `(ptr, len, cap)` in the ABI0 frame (words 0–2 at
`8(RSP)`, the result word at `32(RSP)`) and every ABI0 call state of
`example.com/asm.XorSlice.abi0` in which the `8·len` bytes at `ptr` are readable, the call
returns (never faulting), obeys `ABIReturn0`, its result word is `xs[0] ^ … ^ xs[len-1]`, and it
writes nothing but the result word. For every length, so the loop terminates.

**How.** `loop` is the invariant at the loop head `TESTQ CX, CX`, by induction on the iterations
left (one per `janus64_run until [head]`).
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic

namespace Proof

/-- XOR of the `n` little-endian 64-bit words at `p`. -/
def xorWords (m : Memory) (p : Nat) : Nat → W64
  | 0 => 0
  | n + 1 => xorWords m p n ^^^ BitVec.ofNat 64 (m.readLE (p + 8 * n) 8)

/-- The loop head `TESTQ CX, CX`. -/
abbrev head : Nat := Extracted.entry + 0xd

def Post (ptr len : BitVec 64) (s s' : State) : Prop :=
  results0 s s' 3 1 = [xorWords s.mem ptr.toNat len.toNat] ∧
    Janus.Spec.OnlyWrites s.mem s'.mem ((s.regs 4).toNat + 32) 8

theorem loop (ptr len : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hp : s.mem.accessible ptr.toNat (8 * len.toNat) false = true)
    (hp' : ptr.toNat + 8 * len.toNat ≤ 2 ^ 48)
    (hfb : (s.regs 4).toNat + 40 ≤ 2 ^ 48)
    (hfacc : s.mem.accessible (s.regs 4).toNat 40 true = true)
    (hra : s.mem.readLE (s.regs 4).toNat 8 = ret) :
    ∀ n (S : State) (i : Nat), i + n = len.toNat →
      S.rip = BitVec.ofNat 64 head → S.regs 6 = BitVec.ofNat 64 (ptr.toNat + 8 * i) →
      S.regs 1 = BitVec.ofNat 64 n → S.regs 0 = xorWords s.mem ptr.toNat i →
      S.regs 4 = s.regs 4 → S.regs 5 = s.regs 5 → S.mem = s.mem → S.fsBase = s.fsBase →
      S.df = s.df →
      Reaches (Extracted.program.withExit ret) S
        (IsReturn fun s' => ABIReturn0 s s' ∧ Post ptr len s s') := by
  intro n
  induction n with
  | zero =>
    intro S i hn hpc h6 h1 h0 h4 h5 hm hfs hdf
    janus64_run [Post]
    refine ⟨hfs, by rw [show i = len.toNat by omega], ?_⟩
    exact Janus.Spec.onlyWrites_writeLE _ (Janus.Spec.onlyWrites_refl _ _ _) (by omega) (by omega)
  | succ n ih =>
    intro S i hn hpc h6 h1 h0 h4 h5 hm hfs hdf
    janus64_run until [head]
    have := len.isLt
    apply ih _ (i + 1) (by omega) rfl
    · simp only [setRegF_apply, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    all_goals simp [setRegF_apply, xorWords, h4, h5, hfs]

theorem correctness (ptr len cap : BitVec 64) :
    Ensures0 Extracted.program Extracted.entry [ptr, len, cap] 1
      (fun s => Buffer s ptr (8 * len.toNat) false)
      (fun s s' => results0 s s' 3 1 = [xorWords s.mem ptr.toNat len.toNat] ∧
        Janus.Spec.OnlyWrites s.mem s'.mem ((s.regs 4).toNat + 32) 8) := by
  intro ret hret s hs ⟨hp', hp⟩
  janus64_intro0 hs
  janus64_run until [head]
  exact loop ptr len ret hret s hp hp' h_fb h_facc h_ret len.toNat _ 0 (by simp) rfl
    (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply, xorWords])
    (by simp [setRegF_apply]) (by simp [setRegF_apply]) rfl rfl (by simp [h_df])

end Proof
