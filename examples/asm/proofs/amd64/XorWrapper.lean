import Janus
import Extracted

/-!
# The ABIInternal → ABI0 wrapper `example.com/asm.XorSlice` (amd64)

```
PUSHQ BP ; MOVQ SP, BP ; SUBQ $32, SP
MOVQ AX, 48(SP) ; MOVQ AX, 0(SP) ; MOVQ BX, 8(SP) ; MOVQ CX, 16(SP)   // registers -> frame
CALL example.com/asm.XorSlice.abi0
XORPS X15, X15 ; MOVQ FS:-8, R14                                    // re-entry
MOVQ 24(SP), AX                                                     // result word -> RAX
ADDQ $32, SP ; POPQ BP ; RET
```

**Guarantee.** For every slice in `RAX RBX RCX` and every Go call state in which
`[RSP-48, RSP+16)` is writable, the TLS slot holds `g` (`TlsG`), and the slice and the TLS slot
are readable and outside the stack window, the call returns, obeys `ABIReturn` (`R14 = g` and
`X15 = 0` restored by the re-entry sequence) and `RAX = xs[0] ^ … ^ xs[len-1]`.

**How.** `xor_summary : Summary0` composed at the `CALL` by `janus64_run calls [xor_summary]`;
the re-entry is executed from the `TlsG` facts.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic

namespace Proof

def xorWords (m : Memory) (p : Nat) : Nat → W64
  | 0 => 0
  | n + 1 => xorWords m p n ^^^ BitVec.ofNat 64 (m.readLE (p + 8 * n) 8)

theorem xorWords_writeLE (m : Memory) (a v p n : Nat) (h : a + 8 ≤ p ∨ p + 8 * n ≤ a) :
    xorWords (m.writeLE a 8 v) p n = xorWords m p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorWords]
    rw [ih (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

abbrev callee : Nat := segAddr Extracted.program "example.com/asm.XorSlice.abi0"
abbrev head : Nat := callee + 0xd

def XorPre (s : State) : Prop :=
  s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
  (s.regs 4).toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 4).toNat 40 true = true ∧
  s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8 ≤ 2 ^ 48 ∧
  s.mem.accessible (s.mem.readLE ((s.regs 4).toNat + 8) 8)
    (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) false = true

abbrev XorQ (s : State) (m : Memory) : Prop :=
  MemFrame (s.mem.writeLE ((s.regs 4).toNat + 32) 8
    (xorWords s.mem (s.mem.readLE ((s.regs 4).toNat + 8) 8)
      (s.mem.readLE ((s.regs 4).toNat + 16) 8)).toNat) m
    [((s.regs 4).toNat, (s.regs 4).toNat)]

theorem loop (s : State) (ptr len : Nat) (hptr : s.mem.readLE ((s.regs 4).toNat + 8) 8 = ptr)
    (hlen : s.mem.readLE ((s.regs 4).toNat + 16) 8 = len) (hpre : XorPre s) :
    ∀ n (S : State) (i : Nat), i + n = len →
      S.rip = BitVec.ofNat 64 head → S.regs 6 = BitVec.ofNat 64 (ptr + 8 * i) →
      S.regs 1 = BitVec.ofNat 64 n → S.regs 0 = xorWords s.mem ptr i →
      S.regs 4 = s.regs 4 → S.regs 5 = s.regs 5 → S.mem = s.mem → S.fsBase = s.fsBase →
      S.df = s.df → S.mxcsr = s.mxcsr → S.fpucw = s.fpucw → S.x87 = s.x87 →
      ReachesRet Extracted.program (retAddrOf s) S (fun s' => Ret0 s s' (XorQ s)) := by
  obtain ⟨hr, hfb, hfacc, hp', hp⟩ := hpre
  rw [hptr, hlen] at hp hp'
  have hlt : len < 2 ^ 64 := hlen ▸ Janus.Arm64.Memory.readLE_lt _ _ 8
  intro n
  induction n with
  | zero =>
    intro S i hn hpc h6 h1 h0 h4 h5 hm hfs hdf hmx hfw hx
    janus64_run [XorQ]
    exact ⟨hfs, hfw, hx, by rw [show i = len by omega]; exact MemFrame.refl _ _⟩
  | succ n ih =>
    intro S i hn hpc h6 h1 h0 h4 h5 hm hfs hdf hmx hfw hx
    janus64_run until [head]
    refine ih _ (i + 1) (by omega) rfl ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_
    · simp only [setRegF_apply, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    all_goals simp [setRegF_apply, xorWords, h4, h5, hfs, hfw, hx]

theorem xor_summary : Summary0 Extracted.program callee XorPre XorQ := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨hr, hfb, hfacc, hp', hp⟩ := hpre'
  janus64_run until [head]
  exact loop s _ _ rfl rfl hpre (s.mem.readLE ((s.regs 4).toNat + 16) 8) _ 0 (by simp) rfl
    (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply, xorWords])
    (by simp [setRegF_apply]) (by simp [setRegF_apply]) rfl rfl rfl rfl rfl rfl

theorem correctness (ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [ptr, len, cap]
      (fun s => StackWritable s 48 16 ∧ TlsG s ∧
        Buffer s ptr (8 * len.toNat) false ∧
        Janus.Spec.Disjoint ptr.toNat (8 * len.toNat) ((s.regs 4).toNat - 48) 64 ∧
        Janus.Spec.Disjoint (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - 48) 64)
      (fun s s' => results 1 s' = [xorWords s.mem ptr.toNat len.toNat]) := by
  intro ret hret s hs ⟨⟨hle, hnw, hacc⟩, htls, ⟨hp', hp⟩, hd, hdt⟩
  janus64_intro hs
  have htr := htls.readable
  have htg := htls.g
  have htb := htls.base
  simp only [regSP] at hacc hle hnw
  simp only [Janus.Spec.Disjoint] at hd hdt
  janus64_run calls [xor_summary]
  refine ⟨rfl, ?_⟩
  simp (disch := omega) only [xorWords_writeLE]

end Proof
