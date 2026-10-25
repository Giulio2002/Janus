#!/usr/bin/env python3
"""Generate JanusX86/Proofs/RcxWidth.lean: the model's per-width RCL/RCR specifications
(`rcl_spec_W`, `rcr_spec_W`, W in 32/64) against Janus' `execRcx` (`rcxVal`/`rcxFl` in RcxSpec.lean).
The 64-bit RCL proof is the template; the others are derived from it.

Usage: gen_rcxspec.py > JanusX86/Proofs/RcxWidth.lean
"""
import re, sys

HDR = 'import JanusX86.Proofs.RcxSpec\n\nset_option linter.unusedSimpArgs false\nset_option maxHeartbeats 4000000\n\nnamespace JanusX86.Proofs\nopen X86Sail X86Sail.Functions\nopen Janus.Amd64\n\ntheorem run_bxor_bind {β : Type} (a b : Bool) (k : Int → SailM β) (s : SState) :\n    (b_xor (Sail.BitVec.toNatInt (BitVec.ofBool a)) (Sail.BitVec.toNatInt (BitVec.ofBool b)) >>= k).run s =\n      (k (if a != b then 1 else 0)).run s := by\n  rw [run_bind, run_b_xor]\n\n'
TMPL = "theorem run_rcl64 (x : BitVec 64) (c : Nat) (hc : c < 64) (rin : BitVec 32) (s : SState)\n    (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) (b : Bool) (hb : c ≠ 0 → f.cf = some b) :\n    ∃ out und, (rcl_spec_64 x (BitVec.ofNat 6 c) rin).run s = .ok (rcxVal true b x c, out, und) s ∧\n      FlagsRel (rcxFl true b x c f) df (wurf rin out und u) := by\n  have hz : ∀ g : BitVec 32 → BitVec 1, (g (Mk_rflagsbits 0#32) == 1#1) = (g 0#32 == 1#1) := fun _ => rfl\n  have hmsb : ∀ r : BitVec 64, r.getLsbD 63 = r.msb := fun r => by rw [BitVec.msb_eq_getLsbD_last]\n  simp only [rcl_spec_64]\n  rw [ofBool_get0 (_get_rflagsbits_cf rin)]\n  generalize hb' : (_get_rflagsbits_cf rin).getLsbD 0 = b'\n  simp only [eqb6 c _ hc, run_bind, run_pure, chs_val 64 65 rfl, toNatInt_ofNat6 c hc,\n    rotl_val (BitVec.ofNat 65 (b'.toNat * 2 ^ 64 + x.toNat)) 65 rfl c (by omega), Nat.mod_eq_of_lt (show c < 65 by omega)]\n  by_cases h0 : c = 0\n  · subst h0\n    simp only [decide_true, ↓reduceIte, run_pure, rotl0, tr_ofNat_cat 64 65 rfl]\n    refine ⟨_, _, rfl, ?_⟩\n    simp only [rcxFl, ↓reduceIte]\n    refine flagsRel_wurf hr _ _ _ u ?_ ?_ ?_ ?_ ?_ ?_ <;> simp (config := {decide := true}) only [Bool.false_eq_true,\n      ↓reduceIte, hz, rf_get_cf_upd_cf, rf_get_cf_upd_pf, rf_get_cf_upd_af, rf_get_cf_upd_zf, rf_get_cf_upd_sf, rf_get_cf_upd_of,\n      rf_get_pf_upd_cf, rf_get_pf_upd_pf, rf_get_pf_upd_af, rf_get_pf_upd_zf, rf_get_pf_upd_sf, rf_get_pf_upd_of,\n      rf_get_af_upd_cf, rf_get_af_upd_pf, rf_get_af_upd_af, rf_get_af_upd_zf, rf_get_af_upd_sf, rf_get_af_upd_of,\n      rf_get_zf_upd_cf, rf_get_zf_upd_pf, rf_get_zf_upd_af, rf_get_zf_upd_zf, rf_get_zf_upd_sf, rf_get_zf_upd_of,\n      rf_get_sf_upd_cf, rf_get_sf_upd_pf, rf_get_sf_upd_af, rf_get_sf_upd_zf, rf_get_sf_upd_sf, rf_get_sf_upd_of,\n      rf_get_of_upd_cf, rf_get_of_upd_pf, rf_get_of_upd_af, rf_get_of_upd_zf, rf_get_of_upd_sf, rf_get_of_upd_of]\n    all_goals first\n      | exact flagEq_some _\n      | exact flagEq_none _\n      | exact hr.cf | exact hr.pf | exact hr.af | exact hr.zf | exact hr.sf | exact hr.ovf\n      | exact flagEq_bne _ _\n  have hbb : b' = b := by\n    have := hr.cf b (hb h0); rw [← hb', this]; cases b <;> rfl\n  subst hbb\n  have hd0 : decide (c = 0) = false := by simp [h0]\n  have hR : ∀ R : BitVec 65, Sail.BitVec.truncate R 64 = R.setWidth 64 := fun _ => rfl\n  simp only [rcxFl, rcxVal, rcxR, h0, ↓reduceIte]\n  generalize hT : BitVec.ofNat 65 (b'.toNat * 2 ^ 64 + x.toNat) = T\n  simp only [hd0, Bool.false_eq_true, ↓reduceIte, hR, logbit_eqI (w := 65) _ 64 (by decide) (by decide),\n    logbit_eqI (w := 64) _ 63 (by decide) (by decide), Int.reduceToNat, hmsb]\n  by_cases h1 : c = 1\n  · have hd1 : decide (c = 1) = true := decide_eq_true h1\n    simp only [hd1, hd0, decide_false, Bool.false_eq_true, ↓reduceIte]\n    rw [run_bxor_bind]\n    simp only [run_pure, bits1_xor]\n    refine ⟨_, _, rfl, ?_⟩\n    simp only [h1, ↓reduceIte]\n    refine flagsRel_wurf hr _ _ _ u ?_ ?_ ?_ ?_ ?_ ?_ <;> simp (config := {decide := true}) only [Bool.false_eq_true,\n      ↓reduceIte, hz, rf_get_cf_upd_cf, rf_get_cf_upd_pf, rf_get_cf_upd_af, rf_get_cf_upd_zf, rf_get_cf_upd_sf, rf_get_cf_upd_of,\n        rf_get_pf_upd_cf, rf_get_pf_upd_pf, rf_get_pf_upd_af, rf_get_pf_upd_zf, rf_get_pf_upd_sf, rf_get_pf_upd_of,\n        rf_get_af_upd_cf, rf_get_af_upd_pf, rf_get_af_upd_af, rf_get_af_upd_zf, rf_get_af_upd_sf, rf_get_af_upd_of,\n        rf_get_zf_upd_cf, rf_get_zf_upd_pf, rf_get_zf_upd_af, rf_get_zf_upd_zf, rf_get_zf_upd_sf, rf_get_zf_upd_of,\n        rf_get_sf_upd_cf, rf_get_sf_upd_pf, rf_get_sf_upd_af, rf_get_sf_upd_zf, rf_get_sf_upd_sf, rf_get_sf_upd_of,\n        rf_get_of_upd_cf, rf_get_of_upd_pf, rf_get_of_upd_af, rf_get_of_upd_zf, rf_get_of_upd_sf, rf_get_of_upd_of]\n    · exact flagEq_some _\n    · exact hr.pf\n    · exact hr.af\n    · exact hr.zf\n    · exact hr.sf\n    · exact flagEq_bne _ _\n  have hd1 : decide (c = 1) = false := by simp [h1]\n  simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte, run_pure]\n  refine ⟨_, _, rfl, ?_⟩\n  refine flagsRel_wurf hr _ _ _ u ?_ ?_ ?_ ?_ ?_ ?_ <;> simp (config := {decide := true}) only [Bool.false_eq_true,\n    ↓reduceIte, hz, rf_get_cf_upd_cf, rf_get_cf_upd_pf, rf_get_cf_upd_af, rf_get_cf_upd_zf, rf_get_cf_upd_sf, rf_get_cf_upd_of,\n      rf_get_pf_upd_cf, rf_get_pf_upd_pf, rf_get_pf_upd_af, rf_get_pf_upd_zf, rf_get_pf_upd_sf, rf_get_pf_upd_of,\n      rf_get_af_upd_cf, rf_get_af_upd_pf, rf_get_af_upd_af, rf_get_af_upd_zf, rf_get_af_upd_sf, rf_get_af_upd_of,\n      rf_get_zf_upd_cf, rf_get_zf_upd_pf, rf_get_zf_upd_af, rf_get_zf_upd_zf, rf_get_zf_upd_sf, rf_get_zf_upd_of,\n      rf_get_sf_upd_cf, rf_get_sf_upd_pf, rf_get_sf_upd_af, rf_get_sf_upd_zf, rf_get_sf_upd_sf, rf_get_sf_upd_of,\n      rf_get_of_upd_cf, rf_get_of_upd_pf, rf_get_of_upd_af, rf_get_of_upd_zf, rf_get_of_upd_sf, rf_get_of_upd_of]\n  · exact flagEq_some _\n  · exact hr.pf\n  · exact hr.af\n  · exact hr.zf\n  · exact hr.sf\n  · exact flagEq_none _\n\n\n"


def mk(left, W):
    t = TMPL
    W1 = W + 1
    t = t.replace("rcl_spec_64", f"{'rcl' if left else 'rcr'}_spec_{W}")
    t = t.replace("run_rcl64", f"run_{'rcl' if left else 'rcr'}{W}")
    t = t.replace("rcxVal true", "rcxVal LEFT").replace("rcxFl true", "rcxFl LEFT")
    t = t.replace("BitVec 65", f"BitVec {W1}").replace("BitVec 64", f"BitVec {W}")
    t = t.replace("2 ^ 64", f"2 ^ {W}").replace("chs_val 64 65 rfl", f"chs_val {W} {W1} rfl")
    t = t.replace("tr_ofNat_cat 64 65 rfl", f"tr_ofNat_cat {W} {W1} rfl")
    t = t.replace(") 65 rfl c (by omega), Nat.mod_eq_of_lt (show c < 65 by omega)",
                  f") {W1} rfl c (by omega), Nat.mod_eq_of_lt (show c < {W1} by omega)")
    t = t.replace("Sail.BitVec.truncate R 64 = R.setWidth 64", f"Sail.BitVec.truncate R {W} = R.setWidth {W}")
    t = t.replace("logbit_eqI (w := 65) _ 64", f"logbit_eqI (w := {W1}) _ {W}")
    t = t.replace("logbit_eqI (w := 64) _ 63", f"logbit_eqI (w := {W}) _ {W-1}")
    t = t.replace("r.getLsbD 63 = r.msb", f"r.getLsbD {W-1} = r.msb")
    t = t.replace("(BitVec.ofNat 65 ", f"(BitVec.ofNat {W1} ")
    t = t.replace("LEFT", "true" if left else "false")
    t = re.sub(r"\(x : BitVec (\d+)\) \(c : Nat\) \(hc : c < 64\)",
               lambda m: f"(x : BitVec {m.group(1)}) (c : Nat) (hc : c < 64) (hcw : c < {int(m.group(1)) + 1})", t)
    if not left:
        t = t.replace("rotl_val", "rotr_val").replace("rotateLeft", "rotateRight").replace("rotl0", "rotr0")
        t = t.replace("  simp only [rcxFl, rcxVal, rcxR, h0, ↓reduceIte]\n  generalize hT : ",
f"""  have hr2 : c = 1 → (BitVec.setWidth {W} ((BitVec.ofNat {W1} (b'.toNat * 2 ^ {W} + x.toNat)).rotateRight c)).msb = b' ∧
      (BitVec.setWidth {W} ((BitVec.ofNat {W1} (b'.toNat * 2 ^ {W} + x.toNat)).rotateRight c)).getLsbD {W-2} = x.msb := by
    intro h; subst h
    simp only [ofNat_cat, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateRight,
      BitVec.getLsbD_cast, BitVec.getLsbD_append]
    simp
  simp only [rcxFl, rcxVal, rcxR, h0, ↓reduceIte]
  generalize hT : """)
        t = t.replace(f"(b'.toNat * 2 ^ {W} + x.toNat) = T\n", f"(b'.toNat * 2 ^ {W} + x.toNat) = T at hr2 ⊢\n", 1)
        t = t.replace("Int.reduceToNat, hmsb]\n  by_cases h1",
                      "Int.reduceToNat, hmsb, Sail.BitVec.extractLsb, extractLsb_one_eq_ofBool, Nat.reduceSub, "
                      "Nat.reduceAdd, BitVec.setWidth_eq]\n  by_cases h1")
        t = t.replace("    simp only [h1, ↓reduceIte]\n",
                      "    obtain ⟨e1, e2⟩ := hr2 h1\n    simp only [e1, e2]\n    simp only [h1, ↓reduceIte]\n")
    return t


DOC = """import JanusX86.Proofs.RcxSpec

/-! # Per-width RCL/RCR specifications (generated by JanusX86/tools/gen_rcxspec.py; do not edit)

For operand sizes 32 and 64 and masked count `c`: the model's `rcl_spec_w`/`rcr_spec_w` return
Janus' `execRcx` value (`rcxVal`) and flags related to Janus' (`rcxFl`), given Janus' `CF` (`b`)
when the count is not 0. -/"""

sys.stdout.write(HDR.replace("import JanusX86.Proofs.RcxSpec", DOC) +
                 "".join(mk(l, W) for W in (32, 64) for l in (True, False)) + "end JanusX86.Proofs\n")
