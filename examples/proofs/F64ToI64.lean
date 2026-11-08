import Extracted

/-!
# `F64ToI64(x float64) int64`: one `FCVTZS X0, D0`

**Guarantee (`correctness`).** For every binary64 encoding `x` whose value truncated toward zero
is an integer `i` with `-2^63 ≤ i < 2^63` (`Janus.Float.truncInt`), and every Go call state of
`example.com/basic.F64ToI64` with `x` in `D0` and `FPCR = 0`, the call returns, obeys the ABI,
and returns `i` in `X0` (as a 64-bit two's-complement value: `X0.toInt = i`).

**Out of range (`saturation`).** The Go specification leaves the result of an out-of-range
float-to-integer conversion implementation-specific. On arm64 it is what `FCVTZS` delivers
(Arm's `FPToFixed(x, 0, signed, FPCR, RZ, 64)`), which saturates: a truncation below `-2^63`
and `-∞` give `-2^63` (`0x8000000000000000`), a truncation at or above `2^63` and `+∞` give
`2^63 - 1`, and a NaN gives `0`. (amd64 differs: see `examples/proofs-amd64/F64ToI64`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 64) (i : Int) (hi : truncInt binary64 x.toNat = some i)
    (h0 : -(2 ^ 63 : Int) ≤ i) (h1 : i < 2 ^ 63) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat ∧ s.fpcr = 0)
      (fun _ s' => (s'.regs 0).toInt = i) := by
  intro ret hret s hs ⟨hx, hf⟩
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx, hf]
  rw [FP.fpToFixed_rzs_ieee FP.IEEEMode.zero binary64 x.toNat i hi h0 h1]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  have : ((i % (2 ^ 64 : Int)).toNat) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  split <;> omega

/-- Saturation, for `FPCR = 0`. -/
theorem saturation (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat ∧ s.fpcr = 0)
      (fun _ s' =>
        (∀ i, truncInt binary64 x.toNat = some i → i < -(2 ^ 63 : Int) → (s'.regs 0).toNat = 2 ^ 63) ∧
        (∀ i, truncInt binary64 x.toNat = some i → 2 ^ 63 ≤ i → (s'.regs 0).toNat = 2 ^ 63 - 1) ∧
        (isNaN binary64 x.toNat = true → (s'.regs 0).toNat = 0) ∧
        (classify binary64 x.toNat = .inf →
          (s'.regs 0).toNat = if signOf binary64 x.toNat then 2 ^ 63 else 2 ^ 63 - 1)) := by
  intro ret hret s hs ⟨hx, hf⟩
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx, hf]
  have hsp := FP.fpToFixed_rzs_special FP.IEEEMode.zero binary64 x.toNat
  refine ⟨fun i hi hneg => ?_, fun i hi hbig => ?_, fun hn => ?_, fun hinf => ?_⟩
  · rw [(FP.fpToFixed_rzs_sat FP.IEEEMode.zero binary64 x.toNat i hi).1 hneg]
  · rw [(FP.fpToFixed_rzs_sat FP.IEEEMode.zero binary64 x.toNat i hi).2 hbig]
  · rw [hsp.1 hn]
  · rw [hsp.2 hinf]; split <;> rfl


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def c_x : BitVec 64 := 0x4004000000000000
def c_i : Int := 2

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem,
    vregs := fun i => if i = 0 then BitVec.ofNat 128 (c_x.toNat) else 0 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    omega⟩
theorem c_hi : truncInt binary64 c_x.toNat = some c_i := by decide

theorem c_h0 : -(2 ^ 63 : Int) ≤ c_i := by decide

theorem c_h1 : c_i < 2 ^ 63 := by decide

theorem hpre : (s0.getV 0 64 = c_x.toNat ∧ s0.fpcr = 0) := by
  simp only [Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp, c_x]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧
    (truncInt binary64 c_x.toNat = some c_i ∧ -(2 ^ 63 : Int) ≤ c_i ∧ c_i < 2 ^ 63) ∧
    (s.getV 0 64 = c_x.toNat ∧ s.fpcr = 0) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toInt = c_i)) :=
  ⟨ret, s0, hret, setup, ⟨c_hi, c_h0, c_h1⟩, hpre, correctness c_x c_i c_hi c_h0 c_h1 ret hret s0 setup hpre⟩

end Witness

end Proof
