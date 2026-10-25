import Janus
import Extracted

/-!
# `NowNano() int64`: `time.Now().UnixNano()` is the wall clock the kernel reported (amd64)

The amd64 build of `examples/sys.NowNano` (see the arm64 proof). `time.Now` → `time.runtimeNow`
(with the calling goroutine outside a `synctest` bubble: `g.bubble = nil`) → `time.now`, which
on linux/amd64 is assembly reading both clocks through the vDSO (`runtime/time_linux_amd64.s`):
a `.syscall` stub whose effect is `Amd64.Kernel.Site.timeNow` (a `CLOCK_REALTIME` reading
`(sec, nsec)` in `RAX`/`RBX`, a monotonic reading no smaller than the last one in `RCX`, both
recorded in the trace). The three encodings of `time.Time` and `UnixNano`'s decoding are executed.

**Guarantee.** As on arm64: the trace gains exactly the two clock readings, the monotonic one is
now the clock's lower bound, and the result is `sec · 10^9 + nsec` (mod 2^64).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel

namespace Proof

/-- `time.startNano` and `time.Local` (writable globals `time.Now` reads). -/
def startNano : Nat := 0x575260
def timeLocal : Nat := 0x54fb40

theorem sx (n : Nat) (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  have hm : (BitVec.setWidth 32 (BitVec.ofNat 64 n)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp; omega

theorem g1' (sec nsec : Nat) :
    BitVec.ofNat 64 nsec + (BitVec.ofNat 64 sec + 62135596800#64) * 1000000000#64 -
      6795364578871345152#64 = BitVec.ofNat 64 (sec * 1000000000 + nsec) := by
  rw [BitVec.add_mul, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_assoc]
  have h2 : (62135596800#64 * 1000000000#64 + -6795364578871345152#64) = 0#64 := by decide
  rw [h2, BitVec.add_zero, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.add_comm]

/-- `UnixNano`'s nanoseconds on amd64 (`ANDL $0x3fffffff; MOVSXD`). -/
theorem nf (x : BitVec 64) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x &&& 1073741823#32))) =
      BitVec.ofNat 64 (x.toNat % 1073741824) := by
  have hm : (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x &&& 1073741823#32))).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
    have : (1073741823#32).toNat = 2 ^ 30 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
    simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have : (1073741823 % 2 ^ 32 : Nat) = 2 ^ 30 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  have hx := x.isLt
  omega

/-- `(x + x) >>> 31`: bits 30..62 of `x` (`UnixNano`'s `SHLQ $1; SHRQ $31` on the wall word). -/
theorem dbl (x : BitVec 64) : (x + x) >>> 31 = BitVec.ofNat 64 (x.toNat % 2 ^ 63 / 2 ^ 30) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  omega

/-- `K + ((C + sec)·10^9 + nsec) = sec·10^9 + nsec` for the constants of `time.Now`/`UnixNano`
(`K + C·10^9 = 0` mod `2^64`). -/
theorem kfold (sec nsec : Nat) :
    11651379494838206464#64 + ((62135596800#64 + BitVec.ofNat 64 sec) * 1000000000#64 +
      BitVec.ofNat 64 nsec) = BitVec.ofNat 64 (sec * 1000000000 + nsec) := by
  rw [BitVec.add_mul, ← BitVec.add_assoc, ← BitVec.add_assoc]
  have h : 11651379494838206464#64 + 62135596800#64 * 1000000000#64 = 0#64 := by decide
  rw [h, BitVec.zero_add, BitVec.ofNat_add, BitVec.ofNat_mul]

theorem g1a (sec nsec : Nat) (hn : nsec < 10 ^ 9) :
    11651379494838206464#64 +
      ((62135596800#64 + BitVec.ofNat 64 sec) * 1000000000#64 +
        BitVec.signExtend 64
          (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 nsec) &&& 1073741823#32)))) =
    BitVec.ofNat 64 (sec * 1000000000 + nsec) := by
  rw [nf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nsec < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show nsec < 1073741824 by omega)]
  exact kfold sec nsec

set_option maxRecDepth 100000 in
theorem orEncN (n w : Nat) (hn : n < 2 ^ 30) (hw : w < 2 ^ 33) :
    (n ||| w * 2 ^ 30 ||| 2 ^ 63) = n + w * 2 ^ 30 + 2 ^ 63 := by
  have k1 := Nat.shiftLeft_add_eq_or_of_lt hn w
  rw [Nat.shiftLeft_eq] at k1
  have hlt : w * 2 ^ 30 + n < 2 ^ 63 := by
    have : w * 2 ^ 30 + 2 ^ 30 ≤ 2 ^ 33 * 2 ^ 30 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hw
    rw [← Nat.pow_add] at this
    omega
  have k2 := Nat.shiftLeft_add_eq_or_of_lt hlt 1
  rw [Nat.shiftLeft_eq, Nat.one_mul] at k2
  rw [Nat.or_comm n, ← k1, Nat.or_comm, ← k2]
  generalize (2 : Nat) ^ 63 = P
  generalize w * 2 ^ 30 = Q
  omega

set_option maxRecDepth 100000 in
theorem orEncC (n : Nat) (W : BitVec 64) (hn : n < 2 ^ 30) (hw : W.toNat < 2 ^ 33) :
    (BitVec.ofNat 64 n ||| W <<< 30 ||| (↑(9223372036854775808 : Nat) : BitVec 64)) =
      BitVec.ofNat 64 (n + W.toNat * 2 ^ 30 + 2 ^ 63) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    BitVec.natCast_eq_ofNat]
  have h1 : W.toNat * 2 ^ 30 % 2 ^ 64 = W.toNat * 2 ^ 30 := Nat.mod_eq_of_lt (by
    have : W.toNat * 2 ^ 30 < 2 ^ 33 * 2 ^ 30 := Nat.mul_lt_mul_of_pos_right hw (Nat.two_pow_pos 30)
    rw [← Nat.pow_add] at this; omega)
  have h2 : (9223372036854775808 : Nat) % 2 ^ 64 = 2 ^ 63 := by decide
  rw [h1, h2, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), orEncN n _ hn hw]
  have : n + W.toNat * 2 ^ 30 + 2 ^ 63 < 2 ^ 64 := by
    have : W.toNat * 2 ^ 30 + 2 ^ 30 ≤ 2 ^ 33 * 2 ^ 30 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hw
    rw [← Nat.pow_add] at this
    generalize W.toNat * 2 ^ 30 = Q at *
    omega
  rw [Nat.mod_eq_of_lt this]

set_option maxRecDepth 100000 in
theorem g4a (sec nsec : Nat) (hn : nsec < 10 ^ 9)
    (hw : ((2682288000#64 + BitVec.ofNat 64 sec) >>> 33).toNat = 0) :
    11651379494838206464#64 +
      ((((BitVec.ofNat 64 nsec ||| (2682288000#64 + BitVec.ofNat 64 sec) <<< 30 ||| (↑(9223372036854775808 : Nat) : BitVec 64)) +
                (BitVec.ofNat 64 nsec ||| (2682288000#64 + BitVec.ofNat 64 sec) <<< 30 ||| (↑(9223372036854775808 : Nat) : BitVec 64))) >>>
              31 +
            59453308800#64) *
          1000000000#64 +
        BitVec.signExtend 64
          (BitVec.setWidth 32
            (BitVec.setWidth 64
              (BitVec.setWidth 32
                  (BitVec.ofNat 64 nsec ||| (2682288000#64 + BitVec.ofNat 64 sec) <<< 30 ||| (↑(9223372036854775808 : Nat) : BitVec 64)) &&&
                1073741823#32)))) =
    BitVec.ofNat 64 (sec * 1000000000 + nsec) := by
  generalize hW : 2682288000#64 + BitVec.ofNat 64 sec = W at hw ⊢
  have hw' : W.toNat < 2 ^ 33 := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hw; omega
  rw [orEncC nsec W (by omega) hw', dbl, nf]
  simp only [BitVec.toNat_ofNat]
  have hv : nsec + W.toNat * 2 ^ 30 + 2 ^ 63 < 2 ^ 64 := by
    have : W.toNat * 2 ^ 30 + 2 ^ 30 ≤ 2 ^ 33 * 2 ^ 30 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hw'
    rw [← Nat.pow_add] at this
    generalize W.toNat * 2 ^ 30 = Q at *
    omega
  rw [Nat.mod_eq_of_lt hv]
  have e1 : (nsec + W.toNat * 2 ^ 30 + 2 ^ 63) % 2 ^ 63 / 2 ^ 30 = W.toNat := by
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [Nat.add_comm, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos 30), Nat.div_eq_of_lt (by omega)]
    rfl
  have e2 : (nsec + W.toNat * 2 ^ 30 + 2 ^ 63) % 1073741824 = nsec := by
    rw [show nsec + W.toNat * 2 ^ 30 + 2 ^ 63 = nsec + 1073741824 * (W.toNat + 2 ^ 33) by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hW, BitVec.add_comm (2682288000#64), BitVec.add_assoc]
  have e4 : (2682288000#64 + 59453308800#64) = 62135596800#64 := by decide
  rw [e4, BitVec.add_comm (BitVec.ofNat 64 sec)]
  exact kfold sec nsec

theorem hb63 (nsec : Nat) (hn : nsec < 10 ^ 9) : (BitVec.ofNat 64 nsec).getLsbD 63 = false := by
  simp only [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have : nsec % 2 ^ 64 / 2 ^ 63 = 0 := by omega
  simp [this]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
theorem correctness (rt : List (Nat × Nat)) :
    Amd64.Kernel.EnsuresK Extracted.program ⟨rt, 1024⟩ Extracted.entry []
      (fun s _ => StackGuardOK s 32 ∧ StackWritable s 1072 8 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Outside ((s.regs 4).toNat - 1072) 1080 rt ∧
        (s.regs 14).toNat + 400 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 392) 8 false = true ∧
        s.mem.readLE ((s.regs 14).toNat + 392) 8 = 0 ∧
        ((s.regs 14).toNat + 400 ≤ (s.regs 4).toNat - 1072 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        s.mem.accessible startNano 8 false = true ∧ s.mem.accessible timeLocal 8 false = true)
      (fun _ k s' k' => ∃ sec nsec msec mnsec, nsec < 10 ^ 9 ∧
        k'.trace = k.trace ++ [.clock 0 sec nsec, .clock 1 msec mnsec] ∧
        k.mono ≤ msec * 10 ^ 9 + mnsec ∧ k'.mono = msec * 10 ^ 9 + mnsec ∧
        s'.regs 0 = BitVec.ofNat 64 (sec * 10 ^ 9 + nsec)) := by
  intro ret hret s k hs ⟨hg, ⟨hb, ha, hw⟩, hal, hout, hb1, hb2, hb3, hgd, hsn, hloc⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, startNano, timeLocal] at hgl hgb hnw2 hgr hb ha hw hout hal hsn hloc ⊢
  apply Amd64.Kernel.ReturnsK.of_reaches
  janus64_intro hs
  janus64_run
  refine ⟨.timeNow, by kernel_site64, Or.inl ⟨?_, ?_⟩⟩
  · simp only [Amd64.Kernel.SiteSafe, CallOK64]
    janus64_simp
    repeat' apply And.intro
    all_goals first | omega | janus_disch
  rintro s₁ k₁ ⟨sec, nsec, msec, mnsec, hn, hsec, hmn, hmono, rfl, junk, f, x, yh, m, rfl, hf⟩
  have hn31 : nsec < 2147483648 := by omega
  have h48 : (s.regs 4 - 48#64).toNat = (s.regs 4).toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  simp (config := { decide := true }) only [setRegF, ite_false, ite_true] at hf
  simp only [h48] at hf
  -- the caller frames above `time.now`'s stack window keep their contents
  have hrd := fun (a : Nat) (h1 : (s.regs 4).toNat - 48 ≤ a) (h2 : a + 8 ≤ (s.regs 4).toNat + 8) =>
    hf.readLE a 8 (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega⟩)
  apply Amd64.Kernel.ReturnsK.of_reaches
  janus64_run [hn31, hrd, sx nsec hn31]
  all_goals refine ⟨sec, nsec, msec, mnsec, hn, by simp [Kern.emit], hmono, by first | rfl | omega, ?_⟩
  all_goals try (rw [g1a sec nsec hn]; done)
  all_goals try (exfalso; exact hbr (hb63 nsec hn))
  all_goals try (exfalso
                 have h63 : (↑(9223372036854775808 : Nat) : BitVec 64).getLsbD 63 = true := by decide
                 simp [BitVec.getLsbD_or, h63] at hbr; done)
  all_goals rw [g4a sec nsec hn (by assumption)]

end Proof
