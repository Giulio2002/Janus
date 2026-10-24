#!/usr/bin/env python3
"""Generate JanusX86/Proofs/ShiftWidth.lean: the model's per-width shift/rotate specifications
(`sal_shl_spec_W`, `shr_spec_W`, `sar_spec_W`, `rol_spec_W`, `ror_spec_W`, W in 8/16/32/64)
against Janus' `execShift` (`shVal`/`shRes`/`shFl` in ShiftSpec.lean).

Usage: gen_shiftspec.py > JanusX86/Proofs/ShiftWidth.lean
"""

WIDTHS = [8, 16, 32, 64]

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
{i}  | (simp only [Option.map_some, zf_bv, hsf, Nat.reduceSub, hmsb]; first | exact flagEq_some _ | exact flagEq_bne _ _)""")


CLOSE = close(4)


def head(W):
    return f"""  have hz : ∀ g : BitVec 32 → BitVec 1, (g (Mk_rflagsbits 0#32) == 1#1) = (g 0#32 == 1#1) := fun _ => rfl
  have hsf : ∀ r : BitVec {W}, BitVec.ofBool (decide (2 ^ {W-1} ≤ r.toNat)) = BitVec.ofBool r.msb := fun r => by
    rw [BitVec.msb_eq_decide]
  have hmsb : ∀ r : BitVec {W}, r.getLsbD {W-1} = r.msb := fun r => by rw [BitVec.msb_eq_getLsbD_last]
"""


def flags_simp(W):
    return (f"run_pf_spec{W}, Sail.BitVec.extractLsb, extractLsb_one_eq_ofBool, Nat.reduceSub, Nat.reduceAdd, "
            f"BitVec.setWidth_eq, run_b_xor, bits1_xor, zf_spec_eq, sf_spec{W}_eq, "
            f"logbit_eqI (w := {W}) _ {W-1} (by decide) (by decide), Int.reduceToNat")


def shift_lemma(op, W, sar_msb=None):
    """SHL/SHR/SAR at width W.  sar_msb: None (not SAR), True/False (the msb case of SAR)."""
    spec = {"shl": f"sal_shl_spec_{W}", "shr": f"shr_spec_{W}", "sar": f"sar_spec_{W}"}[op]
    cm = 64 if W == 64 else 32
    neg = f"(bits_of_int (Neg.neg (Sail.BitVec.toNatInt (BitVec.ofNat 6 c))) {W+1})"
    out = []
    out.append(head(W))
    # value: hv (pre-rewrite form) used in stage-1 simps
    if op == "shl":
        out.append(f"""  have hv : bits_of_int (ash_left_int (Sail.BitVec.toNatInt x) (Sail.BitVec.toNatInt (BitVec.ofNat 6 c)).toNat) {W} =
      shVal .shl x c := by
    rw [toNatInt_ofNat6 c hc, Int.toNat_natCast, shl_val]; unfold shVal; split <;> simp_all
""")
        vsimp = "hv"
    else:
        out.append(f"""  have hn : {neg}.toInt = -(c : Int) := neg6 {W} c hc (by decide)
""")
        if op == "shr":
            out.append(f"""  have hv : bits_of_int (ash_int (Sail.BitVec.toNatInt x) {neg}.toInt) {W} = shVal .shr x c := by
    rw [hn, shr_val]; unfold shVal; split <;> simp_all
""")
            vsimp = "hv"
        else:
            if sar_msb:
                out.append(f"""  have hlb : logbit_bits {W-1} x = BitVec.ofBool true := by
    simp only [logbit_eqI (w := {W}) _ {W-1} (by decide) (by decide), Int.reduceToNat, hmsb, hm]
  have hv : bits_of_int (loghead_int {W} (ash_int x.toInt {neg}.toInt)) {W} = shVal .sar x c := by
    rw [hn, ash_neg, sar_neg x {W} rfl (by decide)]; unfold shVal; split <;> simp_all
""")
                vsimp = f"hlb, show (BitVec.ofBool true == 1#1) = true from rfl, run_logext{W}, hv"
            else:
                out.append(f"""  have hlb : logbit_bits {W-1} x = BitVec.ofBool false := by
    simp only [logbit_eqI (w := {W}) _ {W-1} (by decide) (by decide), Int.reduceToNat, hmsb, hm]
  have hv : bits_of_int (Sail.BitVec.toNatInt (bits_of_int (ash_int (Sail.BitVec.toNatInt x) {neg}.toInt) {W})) {W} =
      shVal .sar x c := by
    rw [hn, sar_pos x hm]; unfold shVal; split <;> simp_all
""")
                vsimp = f"hlb, show (BitVec.ofBool false == 1#1) = false from rfl, hv"
    jval = {"shl": "x <<< c", "shr": "x >>> c", "sar": "x.sshiftRight c"}[op]
    s1 = f"simp only [{spec}, eqb6 c _ hc, Bool.false_eq_true, ↓reduceIte, run_bind, run_pure, {vsimp}"
    # c = 0
    out.append(f"""  by_cases h0 : c = 0
  · have hd : decide (c = 0) = true := by simp [h0]
    {s1}, hd]
    refine ⟨_, _, rfl, ?_⟩
    simp only [shRes, h0, ↓reduceIte]
{CLOSE}
  have hsv : shVal .{op} x c = {jval} := by simp [shVal, h0]
  have hd0 : decide (c = 0) = false := by simp [h0]
  by_cases h1 : c = 1
  · have hd1 : decide (c = 1) = true := by simp [h1]
    {s1}, hd0, hd1]
    simp only [run_bind, run_pure, {flags_simp(W)}]
    refine ⟨_, _, rfl, ?_⟩
    simp only [shRes_fst, hsv]
    simp only [shRes, h0, h1, ↓reduceIte]
{CLOSE}
  have hd1 : decide (c = 1) = false := by simp [h1]
""")
    if op == "shl":
        bs = f"run_bitslice1 x ((({W} : Int)) - (c : Int)) (by omega) (by omega)"
        sub = f"show (({W} : Int) - (c : Int)).toNat = {W} - c by omega"
    else:
        bs = f"run_bitslice1 x ((c : Int) - 1) (by omega) (by omega)"
        sub = f"show ((c : Int) - 1).toNat = c - 1 by omega"
    if W <= 16:
        out.append(f"""  by_cases hge : {W} ≤ c
  · have hgeb : (({W} : Int) ≤b (c : Int)) = true := by simp; omega
    {s1}, hd0, hd1]
    simp only [toNatInt_ofNat6 c hc, hgeb, ↓reduceIte, run_bind, run_pure, {flags_simp(W)}]
    refine ⟨_, _, rfl, ?_⟩
    simp only [shRes_fst, hsv]
    simp only [shRes, h0, h1, ↓reduceIte, show ¬ c < {W} by omega]
{CLOSE}
""")
    out.append(f"""  have hgeb : (({W} : Int) ≤b (c : Int)) = false := by simp; omega
  {s1}, hd0, hd1]
  simp only [toNatInt_ofNat6 c hc, hgeb, Bool.false_eq_true, ↓reduceIte, run_bind, run_pure, {bs}, {sub}, {flags_simp(W)}]
  refine ⟨_, _, rfl, ?_⟩
  simp only [shRes_fst, hsv]
  simp only [shRes, h0, h1, ↓reduceIte, show c < {W} by omega]
""" + close(2) + "\n")
    return "".join(out)


def rot_lemma(op, W):
    spec = {"rol": f"rol_spec_{W}", "ror": f"ror_spec_{W}"}[op]
    fn = {"rol": "rotate_left_bits", "ror": "rotate_right_bits"}[op]
    vl = {"rol": "rotl_val", "ror": "rotr_val"}[op]
    jval = {"rol": f"x.rotateLeft (c % {W})", "ror": f"x.rotateRight (c % {W})"}[op]
    fl = "shFl" if op == "ror" else "shRes"
    out = [head(W)]
    out.append(f"""  have hv : {fn} x {W} (Sail.BitVec.toNatInt (BitVec.ofNat 6 c)) = shVal .{op} x c := by
    rw [toNatInt_ofNat6 c hc, {vl} x {W} rfl c hcw]; unfold shVal; split <;> simp_all [rotl0, rotr0]
""")
    s1 = f"simp only [{spec}, eqb6 c _ hc, Bool.false_eq_true, ↓reduceIte, run_bind, run_pure, hv"
    unf = "shFl, shRes" if op == "ror" else "shRes"
    out.append(f"""  by_cases h0 : c = 0
  · have hd : decide (c = 0) = true := by simp [h0]
    {s1}, hd]
    refine ⟨_, _, rfl, ?_⟩
    simp only [{unf}, h0, ↓reduceIte, show ¬ (ShOp.{op} = .ror ∧ 2 ≤ 0) by decide, false_and, and_false]
{CLOSE}
  have hsv : shVal .{op} x c = {jval} := by simp [shVal, h0]
  have hd0 : decide (c = 0) = false := by simp [h0]
  by_cases h1 : c = 1
  · have hd1 : decide (c = 1) = true := by simp [h1]
    {s1}, hd0, hd1]
    simp only [run_bind, run_pure, {flags_simp(W)}, hsv]
    refine ⟨_, _, rfl, ?_⟩
    simp only [{unf}, h0, h1, ↓reduceIte, show ¬ (2 ≤ 1) by decide, and_false]
{CLOSE}
  have hd1 : decide (c = 1) = false := by simp [h1]
  {s1}, hd0, hd1]
  simp only [run_bind, run_pure, {flags_simp(W)}, hsv]
  refine ⟨_, _, rfl, ?_⟩
  simp only [{unf}, h0, h1, ↓reduceIte, show 2 ≤ c by omega, and_true]
""" + close(2) + "\n")
    return "".join(out)


def logext(W):
    return f"""theorem run_logext{W} (x : BitVec {W}) (s : SState) :
    (binary_logext {W} (Sail.BitVec.toNatInt x)).run s = .ok x.toInt s := by
  have hx := x.isLt
  simp (config := {{decide := true}}) only [binary_logext, logbitp_int, binary_logapp, loghead_int, run_bind,
    run_sail_assert_true, run_pure, bits_to_bool_eq, toNat_slice1, Sail.BitVec.toNatInt, toNat_slice0]
  simp only [ite_pure, run_pure]
  rw [BitVec.toInt_eq_toNat_cond]
  simp
  split <;> split <;> omega

"""


def main():
    print("""import JanusX86.Proofs.ShiftSpec

/-! # Per-width shift/rotate specifications (generated by JanusX86/tools/gen_shiftspec.py; do not edit)

For each operand size `w ∈ {8, 16, 32, 64}` and masked count `c` (`< 32`, or `< 64` at 64 bits): the
model's `sal_shl_spec_w`, `shr_spec_w`, `sar_spec_w`, `rol_spec_w` and `ror_spec_w` return Janus'
`execShift` value (`shVal`) and, through `write_user_rflags`, flags related to Janus' (`shRes`; for
`ROR`, `shFl`: `CF` unconstrained at a count ≥ 2, Sail-x86 defect D6). The 8/16-bit rotates are stated
for `c < w` only (Sail-x86 defect D3: a count ≥ the width is not reduced modulo the width). -/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64
""")
    for W in WIDTHS:
        print(f"/-! ## {W}-bit -/\n")
        print(logext(W))
        cm = 64 if W == 64 else 32
        for op in ["shl", "shr"]:
            spec = {"shl": f"sal_shl_spec_{W}", "shr": f"shr_spec_{W}"}[op]
            print(f"""theorem run_{op}{W} (x : BitVec {W}) (c : Nat) (hc : c < 64) (hcw : c < {cm}) (rin : BitVec 32) (s : SState)
    (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, ({spec} x (BitVec.ofNat 6 c) rin).run s = .ok (shVal .{op} x c, out, und) s ∧
      FlagsRel (shRes .{op} x c f).2 df (wurf rin out und u) := by
{shift_lemma(op, W)}""")
        for m in [True, False]:
            nm = "n" if m else "p"
            print(f"""theorem run_sar{W}{nm} (x : BitVec {W}) (hm : x.msb = {'true' if m else 'false'}) (c : Nat) (hc : c < 64) (hcw : c < {cm})
    (rin : BitVec 32) (s : SState) (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, (sar_spec_{W} x (BitVec.ofNat 6 c) rin).run s = .ok (shVal .sar x c, out, und) s ∧
      FlagsRel (shRes .sar x c f).2 df (wurf rin out und u) := by
{shift_lemma("sar", W, sar_msb=m)}""")
        print(f"""theorem run_sar{W} (x : BitVec {W}) (c : Nat) (hc : c < 64) (hcw : c < {cm})
    (rin : BitVec 32) (s : SState) (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, (sar_spec_{W} x (BitVec.ofNat 6 c) rin).run s = .ok (shVal .sar x c, out, und) s ∧
      FlagsRel (shRes .sar x c f).2 df (wurf rin out und u) := by
  cases hm : x.msb
  · exact run_sar{W}p x hm c hc hcw rin s f df u hr
  · exact run_sar{W}n x hm c hc hcw rin s f df u hr
""")
        rw = W  # rotates: c < W
        for op in ["rol", "ror"]:
            spec = {"rol": f"rol_spec_{W}", "ror": f"ror_spec_{W}"}[op]
            fl = "shFl" if op == "ror" else "shRes"
            fl2 = f"shFl .ror x c f" if op == "ror" else f"(shRes .rol x c f).2"
            print(f"""theorem run_{op}{W} (x : BitVec {W}) (c : Nat) (hc : c < 64) (hcw : c < {W}) (rin : BitVec 32) (s : SState)
    (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, ({spec} x (BitVec.ofNat 6 c) rin).run s = .ok (shVal .{op} x c, out, und) s ∧
      FlagsRel ({fl2}) df (wurf rin out und u) := by
{rot_lemma(op, W)}""")
    print("end JanusX86.Proofs")


if __name__ == "__main__":
    main()
