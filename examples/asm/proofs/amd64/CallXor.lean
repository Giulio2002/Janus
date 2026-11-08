import Janus
import Extracted

/-!
# `CallXor(xs []uint64) uint64` (Go, amd64): a direct ABI0 call of Go assembly, with re-entry

```go
func CallXor(xs []uint64) uint64 { return XorSlice(xs) ^ 1 }   // examples/asm/asm.go
```

The compiler calls the same-package assembly directly with ABI0 and then **re-enters**
ABIInternal itself:

```
MOVQ AX, 0(SP) ; MOVQ BX, 8(SP) ; MOVQ CX, 16(SP)   // the frame words
CALL example.com/asm.XorSlice.abi0
XORPS X15, X15                                      // X15 := 0
MOVQ FS:-8, R14                                     // R14 := g (TLS)
MOVQ 24(SP), AX                                     // the result word
```

**Guarantee.** For every slice `(ptr, len, cap)` in `RAX RBX RCX` and every Go call state of
`example.com/asm.CallXor` in which the stack check falls through, `[RSP-48, RSP+16)` is
writable, the TLS slot holds `g` (`TlsG`: the slot at `FS:-8` is readable and holds `R14`), the
`8·len` bytes at `ptr` are readable, and neither the slice nor the TLS slot overlaps the stack
window, the call returns (never faulting or panicking), obeys the ABIInternal return rules —
`R14 = g` and `X15 = 0` again, although the ABI0 callee was free to clobber both — and
`RAX = xs[0] ^ … ^ xs[len-1] ^ 1`.

**How.** `xor_summary : Summary0 … XorPre XorQ` proves the assembly once from any state at its
entry (loop invariant `loop`, in `ReachesRet` form); its return state has the ABI0 shape `Ret0`
(`R14`, `X15` and all other registers but `RSP`/`RBP` unspecified). `janus64_run calls
[xor_summary]` executes `CallXor`, uses the summary at the `CALL`, and executes the re-entry
sequence: the `MOVQ FS:-8, R14` load reads `g` from the TLS slot, which the callee's memory
frame (`MemFrame`) leaves intact.
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
      (fun s => StackGuardOK s 0 ∧ StackWritable s 48 16 ∧ TlsG s ∧
        Buffer s ptr (8 * len.toNat) false ∧
        Janus.Spec.Disjoint ptr.toNat (8 * len.toNat) ((s.regs 4).toNat - 48) 64 ∧
        Janus.Spec.Disjoint (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - 48) 64)
      (fun s s' => results 1 s' = [xorWords s.mem ptr.toNat len.toNat ^^^ 1#64]) := by
  intro ret hret s hs ⟨hg, ⟨hle, hnw, hacc⟩, htls, ⟨hp', hp⟩, hd, hdt⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  have htr := htls.readable
  have htg := htls.g
  have htb := htls.base
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  simp only [Janus.Spec.Disjoint] at hd hdt
  janus64_run calls [xor_summary]
  simp (disch := omega) only [xorWords_writeLE]

namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def tls0 : Nat := 0x400000
def dat : Nat := 0x500000

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else if a = tls0 + 2 then 0x30 else if a = dat then 5 else if a = dat + 8 then 6 else 0

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 dat else if i = 1 then 2 else if i = 2 then 2 else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨g0, 0x100, false⟩, ⟨tls0, 0x100, false⟩, ⟨dat, 0x100, false⟩]⟩,
    fsBase := BitVec.ofNat 64 (tls0 + 8) }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry
    [(0x500000 : BitVec 64), 2, 2] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 48 16 ∧ TlsG s0 ∧
    Buffer s0 (0x500000 : BitVec 64) (8 * (2 : BitVec 64).toNat) false ∧
    Janus.Spec.Disjoint (0x500000 : BitVec 64).toNat (8 * (2 : BitVec 64).toNat) ((s0.regs 4).toNat - 48) 64 ∧
    Janus.Spec.Disjoint (s0.fsBase.toNat - 8) 8 ((s0.regs 4).toNat - 48) 64 := by
  unfold Buffer Janus.Spec.Disjoint
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    by decide, by decide⟩

/-- All the hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : Amd64.State) (ptr len cap : BitVec 64),
    RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 48 16 ∧ TlsG s ∧
      Buffer s ptr (8 * len.toNat) false ∧
      Janus.Spec.Disjoint ptr.toNat (8 * len.toNat) ((s.regs 4).toNat - 48) 64 ∧
      Janus.Spec.Disjoint (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - 48) 64) ∧
    Returns (Extracted.program.withExit ret) s
      (fun s' => ABIReturn s s' ∧ results 1 s' = [xorWords s.mem ptr.toNat len.toNat ^^^ 1#64]) :=
  ⟨ret, s0, 0x500000, 2, 2, hret, setup, hpre, correctness 0x500000 2 2 ret hret s0 setup hpre⟩

end Witness

end Proof
