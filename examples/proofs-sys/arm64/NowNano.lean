import Extracted

/-!
# `NowNano() int64`: `time.Now().UnixNano()` is the wall clock the kernel reported (arm64)

```go
func NowNano() int64 { return time.Now().UnixNano() }
```

`time.Now` → `time.runtimeNow` → `time.now` (Go 1.26's `runtime.time_now`) → `runtime.walltime`
and `runtime.nanotime1`, the two vDSO clock functions, which are `.syscall` stubs: their effect is
the clock contract of `Janus.Kernel` (`Site.walltime`: any `CLOCK_REALTIME` reading `(sec, nsec)`
with `nsec < 10^9`, recorded in the trace; `Site.nanotime`: a `CLOCK_MONOTONIC` reading no smaller
than the last one). Everything else, including the three encodings of `time.Time`
(`hasMonotonic` with the 33-bit seconds field, the overflow case after 2157, and no monotonic
reading) and the decoding in `UnixNano`, is executed by the model.

**Guarantee.** For every kernel state `k` and runtime-owned memory `rt` (the `m` and `g0` stack
the vDSO wrappers write), from every call state whose stack checks fall through, with
`[SP-1128, SP)` writable and outside `rt`, the calling goroutine not in a `synctest` bubble
(`g.bubble = nil`), and `time.startNano`/`time.Local` readable: the call returns, the trace gains
exactly a wall-clock reading `(sec, nsec)` and a monotonic reading `(msec, mnsec)` (no smaller
than any earlier one, and now the clock's lower bound), and the result is
`sec · 10^9 + nsec` (mod 2^64) — the Unix time in nanoseconds of the wall-clock reading.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel

namespace Proof

/-- `time.startNano` and `time.Local` (writable globals `time.Now` reads). -/
def startNano : Nat :=
  adrpLdTarget (segAddr Extracted.program "time.Now" + 4 * 8)
    (segWord Extracted.program "time.Now" 8) (segWord Extracted.program "time.Now" 9) 3
def timeLocal : Nat :=
  adrpLdTarget (segAddr Extracted.program "time.Now" + 4 * 21)
    (segWord Extracted.program "time.Now" 21) (segWord Extracted.program "time.Now" 22) 3

theorem rr0 (x : BitVec 64) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]
theorem m32 (x : BitVec 64) : x &&& 4294967295#64 = BitVec.ofNat 64 (x.toNat % 4294967296) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have : (4294967295#64).toNat = 2 ^ 32 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  simp; omega
theorem m30 (x : BitVec 64) : x &&& 1073741823#64 = BitVec.ofNat 64 (x.toNat % 1073741824) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have : (1073741823#64).toNat = 2 ^ 30 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  simp; omega
set_option maxRecDepth 100000 in
theorem rr30 (x : BitVec 64) :
    x.rotateRight 30 &&& 18446744065119617023#64 &&& 8589934591#64 =
      BitVec.ofNat 64 (x.toNat / 1073741824 % 8589934592) := by
  rw [BitVec.and_assoc]
  have hc : (18446744065119617023#64 &&& 8589934591#64) = 8589934591#64 := by decide
  rw [hc]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have : (8589934591#64).toNat = 2 ^ 33 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.rotateRight, BitVec.rotateRightAux, BitVec.toNat_or, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [Nat.reduceMod, Nat.reduceSub]
  have hm : x.toNat * 2 ^ 34 % 2 ^ 64 = (x.toNat % 2 ^ 30) * 2 ^ 34 := by omega
  rw [hm]
  have ha : x.toNat / 2 ^ 30 < 2 ^ 34 := by omega
  have key := Nat.shiftLeft_add_eq_or_of_lt ha (x.toNat % 2 ^ 30)
  rw [Nat.shiftLeft_eq] at key
  rw [Nat.or_comm, ← key]
  clear key hc this
  have h2 : x.toNat % 2 ^ 30 * 2 ^ 34 = (x.toNat % 2 ^ 30 * 2) * 2 ^ 33 := by
    rw [Nat.mul_assoc]
  rw [h2, Nat.add_comm, Nat.add_mul_mod_self_right]
  simp only [Nat.reducePow]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm
theorem g1' (sec nsec : Nat) :
    BitVec.ofNat 64 nsec + (BitVec.ofNat 64 sec + 62135596800#64) * 1000000000#64 -
      6795364578871345152#64 = BitVec.ofNat 64 (sec * 1000000000 + nsec) := by
  rw [BitVec.add_mul, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_assoc]
  have h2 : (62135596800#64 * 1000000000#64 + -6795364578871345152#64) = 0#64 := by decide
  rw [h2, BitVec.add_zero, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.add_comm]

theorem g1 (sec nsec : Nat) (hn : nsec < 10 ^ 9) :
    BitVec.ofNat 64 (nsec % 1073741824) + (BitVec.ofNat 64 sec + 62135596800#64) * 1000000000#64 -
      6795364578871345152#64 = BitVec.ofNat 64 (sec * 1000000000 + nsec) := by
  rw [Nat.mod_eq_of_lt (show nsec < 1073741824 by omega)]; exact g1' sec nsec

theorem hb63 (nsec : Nat) (hn : nsec < 10 ^ 9) : (BitVec.ofNat 64 nsec).getLsbD 63 = false := by
  simp only [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have : nsec % 2 ^ 64 / 2 ^ 63 = 0 := by omega
  simp [this]

theorem rr33 (x : BitVec 64) : (x.rotateRight 33).toNat % 2147483648 = x.toNat / 8589934592 := by
  simp only [BitVec.rotateRight, BitVec.rotateRightAux, BitVec.toNat_or, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reduceMod, Nat.reduceSub]
  have hx := x.isLt
  have hm : x.toNat * 2 ^ 31 % 2 ^ 64 = (x.toNat % 2 ^ 33) * 2 ^ 31 := by omega
  rw [hm]
  have ha : x.toNat / 2 ^ 33 < 2 ^ 31 := by omega
  have key := Nat.shiftLeft_add_eq_or_of_lt ha (x.toNat % 2 ^ 33)
  rw [Nat.shiftLeft_eq] at key
  rw [Nat.or_comm, ← key, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]

set_option maxRecDepth 100000 in
theorem orEncN (n w : Nat) (hn : n < 2 ^ 30) (hw : w < 2 ^ 33) :
    (n ||| 1073741824 * w ||| 9223372036854775808) = n + w * 2 ^ 30 + 2 ^ 63 := by
  have k1 := Nat.shiftLeft_add_eq_or_of_lt hn w
  rw [Nat.shiftLeft_eq] at k1
  have hlt : w * 2 ^ 30 + n < 2 ^ 63 := by
    have : w * 2 ^ 30 + 2 ^ 30 ≤ 2 ^ 33 * 2 ^ 30 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hw
    rw [← Nat.pow_add] at this
    omega
  have k2 := Nat.shiftLeft_add_eq_or_of_lt hlt 1
  rw [Nat.shiftLeft_eq] at k2
  have e : (1073741824 * w) = w * 2 ^ 30 := by rw [Nat.mul_comm]
  have e2 : (9223372036854775808 : Nat) = 1 * 2 ^ 63 := by decide
  rw [e, e2, Nat.or_comm n, ← k1, Nat.or_comm, ← k2, Nat.one_mul]
  generalize (2 : Nat) ^ 63 = P
  generalize w * 2 ^ 30 = Q
  omega

set_option maxRecDepth 100000 in
/-- The monotonic encoding of `time.Now` decoded by `UnixNano`: the wall seconds survive the
33-bit field when `sec + (unixToInternal - minWall) < 2^33`. -/
theorem g4 (sec nsec : Nat) (hn : nsec < 10 ^ 9) (hw : (2682288000 + sec) / 8589934592 = 0) :
    BitVec.ofNat 64 ((nsec ||| 1073741824 * (2682288000 + sec) ||| 9223372036854775808) % 1073741824) +
        (BitVec.ofNat 64 ((nsec ||| 1073741824 * (2682288000 + sec) ||| 9223372036854775808) / 1073741824 % 8589934592) +
            59453308800#64) * 1000000000#64 - 6795364578871345152#64 =
      BitVec.ofNat 64 (sec * 1000000000 + nsec) := by
  have hw' : 2682288000 + sec < 2 ^ 33 := by omega
  rw [orEncN nsec _ (by omega) hw']
  have e2 : (nsec + (2682288000 + sec) * 2 ^ 30 + 2 ^ 63) % 1073741824 = nsec := by omega
  have e3 : (nsec + (2682288000 + sec) * 2 ^ 30 + 2 ^ 63) / 1073741824 % 8589934592 = 2682288000 + sec := by
    omega
  rw [e2, e3, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 2682288000), BitVec.add_assoc]
  have e4 : (BitVec.ofNat 64 2682288000 + 59453308800#64) = 62135596800#64 := by decide
  rw [e4]; exact g1' sec nsec

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
theorem correctness (rt : List (Nat × Nat)) :
    EnsuresK Extracted.program ⟨rt, 1024⟩ Extracted.entry []
      (fun s _ => GuardOK s 48 ∧ StackOK s 1128 0 ∧ Outside (s.sp.toNat - 1128) 1128 rt ∧
        (s.regs 28).toNat + 400 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 28).toNat + 392) 8 false = true ∧
        s.mem.readLE ((s.regs 28).toNat + 392) 8 = 0 ∧
        ((s.regs 28).toNat + 400 ≤ s.sp.toNat - 1128 ∨ s.sp.toNat ≤ (s.regs 28).toNat + 16) ∧
        s.mem.accessible startNano 8 false = true ∧ s.mem.accessible timeLocal 8 false = true)
      (fun _ k s' k' => ∃ sec nsec msec mnsec, nsec < 10 ^ 9 ∧
        k'.trace = k.trace ++ [.clock 0 sec nsec, .clock 1 msec mnsec] ∧
        k.mono ≤ msec * 10 ^ 9 + mnsec ∧ k'.mono = msec * 10 ^ 9 + mnsec ∧
        s'.regs 0 = BitVec.ofNat 64 (sec * 10 ^ 9 + nsec)) := by
  intro ret hret s k hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hout, hb1, hb2, hb3, hgd, hsn, hloc⟩
  janus_eval_nat hS : startNano
  janus_eval_nat hL : timeLocal
  simp only [hS, hL] at hsn hloc
  apply ReturnsK.of_reaches
  janus_intro hs
  janus_run
  have h96 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := by
    rw [BitVec.toNat_sub]; simp; omega
  refine ⟨.walltime, by kernel_site, Or.inl ⟨?_, ?_⟩⟩
  · simp only [SiteSafe, CallOK]
    janus_simp
    repeat' apply And.intro
    all_goals first | omega | janus_disch
  rintro s₁ k₁ ⟨sec, nsec, hn, hsec, rfl, regs, fl, vr, fpsr, m, rfl, h28, h29, hf, hsl, hns⟩
  simp only [h96, setReg_apply] at hf hsl hns
  simp [setReg_apply] at h28 h29
  have e8 : s.sp.toNat - 96 + 8 = s.sp.toNat - 88 := by omega
  have e16 : s.sp.toNat - 96 + 16 = s.sp.toNat - 80 := by omega
  rw [e8] at hsl; rw [e16] at hns
  have hn31 : nsec < 2147483648 := by omega
  have hnm : nsec % 4294967296 = nsec := Nat.mod_eq_of_lt (by omega)
  have hb31 : (BitVec.ofNat 64 nsec).getLsbD 31 = false := by
    simp only [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
    have : nsec % 2 ^ 64 / 2 ^ 31 = 0 := by omega
    simp [this]
  apply ReturnsK.of_reaches
  janus_run [hsl, hns, hn31, hnm, hb31, rr0, m32, m30, rr30, rr33]
  refine ⟨.nanotime, by kernel_site, Or.inl ⟨?_, ?_⟩⟩
  · simp only [SiteSafe, CallOK]
    janus_simp
    repeat' apply And.intro
    all_goals first | omega | janus_disch
  rintro s₂ k₂ ⟨msec, mnsec, hmn, hmono, rfl, regs₂, fl₂, vr₂, fpsr₂, m₂, rfl, h28', h29', hf₂, hsl₂⟩
  simp only [h96, setReg_apply] at hf₂ hsl₂
  have hg₂ : regs₂ 28 = s.regs 28 := h28'.trans (by simp [setReg_apply, h28])
  rw [e8] at hsl₂
  apply ReturnsK.of_reaches
  janus_run [hg₂, hsl₂, hn31, hnm, hb31, rr0, m32, m30, rr30, rr33]
  all_goals refine ⟨sec, nsec, msec, mnsec, hn, by simp [Kern.emit], by simpa [Kern.emit] using hmono, by first | rfl | omega, ?_⟩
  all_goals try (rw [g1 sec nsec hn]; done)
  all_goals try (exfalso; rw [hb63 nsec hn] at hbr; exact hbr rfl)
  all_goals try (exfalso
                 have h63 : (9223372036854775808#64).getLsbD 63 = true := by decide
                 simp [BitVec.getLsbD_or, h63] at hbr; done)
  all_goals rw [g4 sec nsec hn (by assumption)]

end Proof
