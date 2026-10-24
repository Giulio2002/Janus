import Janus
import JanusASL.Proofs.Monad

/-! The ASL pseudocode library (as generated) against Janus' `Exec` helpers, as pure functions. -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem integer_subrange_eq (N : Nat) (hN : 0 < N) (i : Int) :
    (integer_subrange i ((N : Int) - 1) 0 : BitVec _).setWidth N = BitVec.ofInt N i := by
  apply BitVec.eq_of_toNat_eq
  simp [integer_subrange, Sail.get_slice_int]
  have e : N - 1 + 1 = N := by omega
  rw [e, Nat.mod_mod, Nat.mod_mod]
  have hp : (0 : Int) < 2 ^ (N + 1) := Int.pow_pos (by decide)
  have hq : (0 : Int) < 2 ^ N := Int.pow_pos (by decide)
  have h1 : ((i % 2 ^ (N + 1)).toNat : Int) = i % 2 ^ (N + 1) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have h2 : ((i % 2 ^ N).toNat : Int) = i % 2 ^ N := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hd : (2 : Int) ^ N ∣ 2 ^ (N + 1) := ⟨2, by rw [Int.pow_succ]⟩
  apply Int.ofNat.inj
  show ((((i % 2 ^ (N + 1)).toNat % 2 ^ N : Nat)) : Int) = (((i % 2 ^ N).toNat : Nat) : Int)
  rw [Int.natCast_emod, h1, h2, Int.natCast_pow]
  exact Int.emod_emod_of_dvd i hd

/-- Flags as the 4-bit NZCV value ASL builds (`n : z : c : v`). -/
def nzcvBits (f : Janus.Arm64.Flags) : BitVec 4 :=
  BitVec.ofBool f.n ++ BitVec.ofBool f.z ++ BitVec.ofBool f.c ++ BitVec.ofBool f.v

theorem AddWithCarry_eq {N : Nat} (hN : 0 < N) (x y : BitVec N) (c : Bool) :
    AddWithCarry x y (BitVec.ofBool c) =
      ((Janus.Arm64.addWithCarry x y c).1, nzcvBits (Janus.Arm64.addWithCarry x y c).2) := by
  unfold AddWithCarry Janus.Arm64.addWithCarry nzcvBits
  simp only
  have hr := integer_subrange_eq N hN ((x.toNat : Int) + y.toNat + (BitVec.ofBool c).toNat)
  have hl : (Sail.BitVec.length y) = N := rfl
  have hc : (BitVec.ofBool c).toNat = c.toNat := by cases c <;> rfl
  have ho : BitVec.ofInt N ((x.toNat : Int) + y.toNat + (BitVec.ofBool c).toNat) =
      BitVec.ofNat N (x.toNat + y.toNat + c.toNat) := by
    rw [hc, show ((x.toNat : Int) + y.toNat + (c.toNat : Int)) = ((x.toNat + y.toNat + c.toNat : Nat) : Int)
      by push_cast; rfl, BitVec.ofInt_natCast]
  rw [hl, hr, ho]
  have hs : ((x.toNat : Int) + y.toNat + (BitVec.ofBool c).toNat).toNat = x.toNat + y.toNat + c.toNat := by
    rw [hc]; omega
  have hi : x.toInt + y.toInt + ((BitVec.ofBool c).toNat : Int) = x.toInt + y.toInt + (c.toNat : Int) := by
    rw [hc]
  simp only [hc]
  have hs' : (((x.toNat : Int) + y.toNat + (c.toNat : Int))).toNat = x.toNat + y.toNat + c.toNat := by omega
  simp only [hs']
  generalize BitVec.ofNat N (x.toNat + y.toNat + c.toNat) = R
  have hm : (Sail.BitVec.access R ((N : Int) - 1).toNat) = BitVec.ofBool R.msb := by
    simp only [Sail.BitVec.access, BitVec.msb_eq_getLsbD_last]
    have : ((N : Int) - 1).toNat = N - 1 := by omega
    rw [this]
    rw [BitVec.getLsbD_eq_getElem (by omega)]
    simp [getElem!_pos, show N - 1 < N by omega]
  rw [hm]
  simp only [IsZero, Prod.mk.injEq, true_and]
  have e1 : ∀ (p : Prop) [Decidable p], (if p then 1#1 else 0#1) = BitVec.ofBool (decide p) := by
    intro p _; by_cases h : p <;> simp [h]
  have e2 : ∀ (p : Prop) [Decidable p], (if p then 0#1 else 1#1) = BitVec.ofBool (!decide p) := by
    intro p _; by_cases h : p <;> simp [h]
  simp only [Sail.BitVec.length, beq_iff_eq, e1, e2, decide_not, ne_eq, BitVec.zero_eq]
  rfl

end JanusASL.Proofs
