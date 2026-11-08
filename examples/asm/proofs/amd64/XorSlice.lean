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

namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def tls0 : Nat := 0x400000
def dat : Nat := 0x500000

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else if a = sp0 + 10 then 0x50 else if a = sp0 + 16 then 2
  else if a = sp0 + 24 then 2 else if a = dat then 5 else if a = dat + 8 then 6 else 0

def s0 : Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨g0, 0x100, false⟩, ⟨tls0, 0x100, false⟩, ⟨dat, 0x100, false⟩]⟩,
    fsBase := BitVec.ofNat 64 (tls0 + 8) }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup0 (Extracted.program.withExit ret) Extracted.entry
    [(0x500000 : BitVec 64), 2, 2] 1 s0 :=
  ⟨rfl, by decide, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide,
   ⟨by decide, by decide⟩, rfl⟩

theorem hpre : Buffer s0 (0x500000 : BitVec 64) (8 * (2 : BitVec 64).toNat) false := by
  unfold Buffer; decide

/-- The theorem fires: `XorSlice` of the two words `5, 6` at `dat`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0
    (fun s' => ABIReturn0 s0 s' ∧
      (results0 s0 s' 3 1 = [xorWords s0.mem (0x500000 : BitVec 64).toNat (2 : BitVec 64).toNat] ∧
        Janus.Spec.OnlyWrites s0.mem s'.mem ((s0.regs 4).toNat + 32) 8)) :=
  correctness 0x500000 2 2 ret hret s0 setup hpre

/-- All the hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : Amd64.State) (ptr len cap : BitVec 64),
    RetAddr Extracted.program ret ∧
    CallSetup0 (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap] 1 s ∧
    Buffer s ptr (8 * len.toNat) false ∧
    Returns (Extracted.program.withExit ret) s
      (fun s' => ABIReturn0 s s' ∧
        (results0 s s' 3 1 = [xorWords s.mem ptr.toNat len.toNat] ∧
          Janus.Spec.OnlyWrites s.mem s'.mem ((s.regs 4).toNat + 32) 8)) :=
  ⟨ret, s0, 0x500000, 2, 2, hret, setup, hpre, returns⟩

end Witness

end Proof
