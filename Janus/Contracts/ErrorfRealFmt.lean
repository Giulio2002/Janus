import Janus.Contracts.Errorf
import Janus.Contracts.IfaceModel

/-!
# The real format of the `uint256` library: `"%w: have %d, want %d bytes"`

The facts about `msgOf` for the one format the `fmt.errorf` witness stubs are built for
(`ErrorfRealSat`, `ErrorfRealSatAmd64`): its length and bytes, its segments, and the message as the
three literals around the text and the two decimal numbers.
-/

namespace Janus.Contracts.ErrorfRealFmt

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.Errorf

/-- The format, as bytes. -/
def fmtList : List Nat :=
  [37, 119, 58, 32, 104, 97, 118, 101, 32, 37, 100, 44, 32, 119, 97, 110, 116, 32, 37, 100, 32, 98, 121, 116, 101, 115]

/-- The format as a little-endian number (the `Fm` parameter of the contract). -/
def fmtNum : Nat := 185434718302992804189262808438449144100701425152729625373865765

theorem strBytes_of_readLE (m : Memory) (p n X : Nat) (h : m.readLE p n = X) :
    strBytes m p n = (List.range n).map (fun i => X / 256 ^ i % 256) := by
  simp only [strBytes]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have := IfaceModel.byte_of_readLE m n p i hi
  rw [h] at this
  rw [← this]
  simp [BitVec.toNat_ofNat]

theorem fmt_strBytes (m : Memory) (p : Nat) (h : m.readLE p 26 = fmtNum) : strBytes m p 26 = fmtList :=
  by rw [strBytes_of_readLE m p 26 fmtNum h]; decide

theorem fmt_segs : parseFmt fmtList =
    some [Seg.ch 58, Seg.ch 32, Seg.ch 104, Seg.ch 97, Seg.ch 118, Seg.ch 101, Seg.ch 32, Seg.dec, Seg.ch 44,
      Seg.ch 32, Seg.ch 119, Seg.ch 97, Seg.ch 110, Seg.ch 116, Seg.ch 32, Seg.dec, Seg.ch 32, Seg.ch 98,
      Seg.ch 121, Seg.ch 116, Seg.ch 101, Seg.ch 115] := by decide

theorem toInt_ofNat64 (v : Nat) (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v).toInt = toSigned v := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  unfold toSigned
  split <;> split <;> omega

theorem abs_bv (v : Nat) (hv : v < 2 ^ 64) :
    (if 0 ≤ (BitVec.ofNat 64 v).toInt then BitVec.ofNat 64 v else ~~~BitVec.ofNat 64 v + 1#64) =
      BitVec.ofNat 64 (toSigned v).natAbs := by
  rw [toInt_ofNat64 v hv]
  unfold toSigned
  split
  · rw [if_pos (by omega)]; congr 1
  · rw [if_neg (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat]
    omega

theorem neg_bv (v : Nat) (hv : v < 2 ^ 64) :
    (if 0 ≤ (BitVec.ofNat 64 v).toInt then 0#64 else 1#64) = BitVec.ofNat 64 (if toSigned v < 0 then 1 else 0) := by
  rw [toInt_ofNat64 v hv]
  split <;> split <;> first | rfl | omega

theorem bv_sub_lit (x : BitVec 64) (k : Nat) (h : k ≤ x.toNat) (hk : k < 2 ^ 64) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt hk]
  omega

theorem natAbs_lt (v : Nat) (hv : v < 2 ^ 64) : (toSigned v).natAbs ≤ 2 ^ 63 := by
  unfold toSigned; split <;> omega

/-- The sign of the `int` with the two's complement word `v` (1 for a negative number) and its magnitude. -/
def sgn (v : Nat) : Nat := if toSigned v < 0 then 1 else 0
def absn (v : Nat) : Nat := (toSigned v).natAbs

theorem decBytes_eq (v : Nat) : decBytes (toSigned v) = (if sgn v = 1 then [45] else []) ++ natBytes (absn v) := by
  unfold decBytes sgn absn
  by_cases h : toSigned v < 0
  · simp [h]
  · simp [h]; congr 1; omega

end Janus.Contracts.ErrorfRealFmt
