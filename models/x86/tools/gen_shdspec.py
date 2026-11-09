#!/usr/bin/env python3
"""Generate JanusX86/Proofs/ShdWidth.lean: the model's per-width SHLD/SHRD specifications
(`shld_spec_W`, `shrd_spec_W`, W in 16/32/64) against Janus' `execShd` (`shdVal`/`shdFl` in ShdSpec.lean).

Usage: gen_shdspec.py > JanusX86/Proofs/ShdWidth.lean
"""

WIDTHS = [16, 32, 64]

RFGET = """rf_get_cf_upd_cf, rf_get_cf_upd_pf, rf_get_cf_upd_af, rf_get_cf_upd_zf, rf_get_cf_upd_sf, rf_get_cf_upd_of,
      rf_get_pf_upd_cf, rf_get_pf_upd_pf, rf_get_pf_upd_af, rf_get_pf_upd_zf, rf_get_pf_upd_sf, rf_get_pf_upd_of,
      rf_get_af_upd_cf, rf_get_af_upd_pf, rf_get_af_upd_af, rf_get_af_upd_zf, rf_get_af_upd_sf, rf_get_af_upd_of,
      rf_get_zf_upd_cf, rf_get_zf_upd_pf, rf_get_zf_upd_af, rf_get_zf_upd_zf, rf_get_zf_upd_sf, rf_get_zf_upd_of,
      rf_get_sf_upd_cf, rf_get_sf_upd_pf, rf_get_sf_upd_af, rf_get_sf_upd_zf, rf_get_sf_upd_sf, rf_get_sf_upd_of,
      rf_get_of_upd_cf, rf_get_of_upd_pf, rf_get_of_upd_af, rf_get_of_upd_zf, rf_get_of_upd_sf, rf_get_of_upd_of"""


def close(ind):
    i = " " * ind
    return (f"""{i}refine flagsRel_wurf hr _ _ _ u ?_ ?_ ?_ ?_ ?_ ?_ <;> simp (config := {{decide := true}}) only [Bool.false_eq_true,
{i}  ↓reduceIte, hz, """ + RFGET + f"""]
{i}all_goals first
{i}  | exact flagEq_none _
{i}  | exact flagEq_some _
{i}  | exact hr.cf | exact hr.pf | exact hr.af | exact hr.zf | exact hr.sf | exact hr.ovf
{i}  | exact flagEq_bne _ _
{i}  | (simp only [Option.map_some, zf_bv, hsf, Nat.reduceSub, hmsb]; first | exact flagEq_some _ | exact flagEq_bne _ _)""")


def lemma(left, W):
    nm = "shld" if left else "shrd"
    lb = "true" if left else "false"
    W2 = 2 * W
    fs = (f"run_pf_spec{W}, Sail.BitVec.extractLsb, extractLsb_one_eq_ofBool, Nat.reduceSub, Nat.reduceAdd, "
          f"BitVec.setWidth_eq, ofb_if, zf_spec_eq, sf_spec{W}_eq, logbit_eqI (w := {W}) _ {W-1} (by decide) (by decide), "
          f"Int.reduceToNat")
    if left:
        hv = f"""  have hv : bits_of_int (ash_int (Sail.BitVec.toNatInt (bits_of_int (ash_left_int (Sail.BitVec.toNatInt x) {W}) {W2} |||
      Sail.BitVec.zeroExtend y {W2})) (Sail.BitVec.toNatInt (Sail.BitVec.zeroExtend (BitVec.ofNat 6 c) {W}) - {W})) {W} =
      shdVal true x y c := by
    rw [concat_val {W} {W2} rfl, toNatInt_ze6 c {W} hc (by decide)]
    exact shld_val {W} c hcw _ rfl
"""
        pre = ""
        bs = (f"run_bitslice1 x (({W} : Int) - (c : Int)) (by omega) (by omega), "
              f"show (({W} : Int) - (c : Int)).toNat = {W} - c by omega")
    else:
        hv = f"""  have hn : (bits_of_int (Neg.neg (Sail.BitVec.toNatInt (BitVec.ofNat 6 c))) {W+1}).toInt = -(c : Int) :=
    neg6 {W} c hc (by decide)
  have hv : bits_of_int (ash_int (Sail.BitVec.toNatInt (bits_of_int (ash_left_int (Sail.BitVec.toNatInt y) {W}) {W2} |||
      Sail.BitVec.zeroExtend x {W2})) (bits_of_int (Neg.neg (Sail.BitVec.toNatInt (BitVec.ofNat 6 c))) {W+1}).toInt) {W} =
      shdVal false x y c := by
    rw [concat_val {W} {W2} rfl, hn]
    exact shrd_val {W} c _ rfl
"""
        pre = ""
        bs = ("run_bitslice1 x ((c : Int) - 1) (by omega) (by omega), "
              "show ((c : Int) - 1).toNat = c - 1 by omega")
    return f"""theorem run_{nm}{W} (x y : BitVec {W}) (c : Nat) (hc : c < 64) (hcw : c ≤ {W}) (rin : BitVec 32) (s : SState)
    (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, ({nm}_spec_{W} x y (BitVec.ofNat 6 c) rin).run s = .ok (shdVal {lb} x y c, false, out, und) s ∧
      FlagsRel (shdFl {lb} x y c f) df (wurf rin out und u) := by
  have hz : ∀ g : BitVec 32 → BitVec 1, (g (Mk_rflagsbits 0#32) == 1#1) = (g 0#32 == 1#1) := fun _ => rfl
  have hsf : ∀ r : BitVec {W}, BitVec.ofBool (decide (2 ^ {W-1} ≤ r.toNat)) = BitVec.ofBool r.msb := fun r => by
    rw [BitVec.msb_eq_decide]
  have hmsb : ∀ r : BitVec {W}, r.getLsbD {W-1} = r.msb := fun r => by rw [BitVec.msb_eq_getLsbD_last]
{hv}  have hgt : ((Sail.BitVec.toNatInt (BitVec.ofNat 6 c)) >b {W}) = false := by
    rw [toNatInt_ofNat6 c hc]; simp; omega
  have hle : ((Sail.BitVec.toNatInt (BitVec.ofNat 6 c)) ≤b {W}) = true := by
    rw [toNatInt_ofNat6 c hc]; simp; omega
  simp only [{nm}_spec_{W}, eqb6 c _ hc, run_bind, run_pure, hv, hgt, hle]
  by_cases h0 : c = 0
  · have hd : decide (c = 0) = true := by simp [h0]
    simp only [hd, ↓reduceIte, run_pure]
    refine ⟨_, _, rfl, ?_⟩
    simp only [shdFl, h0, ↓reduceIte]
{close(4)}
  have hd0 : decide (c = 0) = false := by simp [h0]
  by_cases h1 : c = 1
  · have hd1 : decide (c = 1) = true := by simp [h1]
    simp only [hd0, hd1, Bool.false_eq_true, ↓reduceIte, run_bind, run_pure, {fs}]
    refine ⟨_, _, rfl, ?_⟩
    simp only [shdFl, h0, h1, ↓reduceIte, Nat.reduceSub, hmsb]
{close(4)}
  have hd1 : decide (c = 1) = false := by simp [h1]
  simp only [hd0, hd1, Bool.false_eq_true, ↓reduceIte, run_bind, run_pure, toNatInt_ofNat6 c hc,
    {bs}, {fs}]
  refine ⟨_, _, rfl, ?_⟩
  try simp only [shdFl, h0, h1, ↓reduceIte]
{close(2)}

"""


def main():
    print("""import JanusX86.Proofs.ShdSpec

/-! # Per-width SHLD/SHRD specifications (generated by JanusX86/tools/gen_shdspec.py; do not edit)

For each operand size `w ∈ {16, 32, 64}` and masked count `c ≤ w`: the model's `shld_spec_w` and
`shrd_spec_w` return Janus' `execShd` value (`shdVal`), a defined result, and, through
`write_user_rflags`, flags related to Janus' (`shdFl`). A 16-bit count above 16 is excluded: Janus
reports an undefined result, the model an undefined value. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

theorem ofb_if (a b : Bool) :
    bits_of_int (if (BitVec.ofBool a == BitVec.ofBool b) = true then (0 : Int) else 1) 1 = BitVec.ofBool (a != b) := by
  cases a <;> cases b <;> rfl
""")
    for W in WIDTHS:
        print(f"/-! ## {W}-bit -/\n")
        print(lemma(True, W))
        print(lemma(False, W))
    print("end JanusX86.Proofs")


main()
