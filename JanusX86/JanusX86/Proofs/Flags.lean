import JanusX86.Proofs.Dispatch

/-! # RFLAGS

The status flags of the model's `rflags` register against Janus' `Flags` (`FlagsRel`: every flag
Janus defines has its value; undefined ones are unrelated), and `write_user_rflags`, which writes
each status flag either from the computed flag vector or, where the instruction's undefined mask
has it, from the model's undefined-value source (`janus_undef`, JanusX86/sail/slice.py). -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

@[simp] theorem rf_get_cf_upd_cf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_cf (_update_rflagsbits_cf x v) = v := by
  simp only [_get_rflagsbits_cf, _update_rflagsbits_cf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 0 _ v (by decide) (by decide)]; rfl

@[simp] theorem rf_get_cf_upd_pf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_cf (_update_rflagsbits_pf x v) = _get_rflagsbits_cf x := by
  simp only [_get_rflagsbits_cf, _update_rflagsbits_pf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 0 0 2 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_cf_upd_af (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_cf (_update_rflagsbits_af x v) = _get_rflagsbits_cf x := by
  simp only [_get_rflagsbits_cf, _update_rflagsbits_af, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 0 0 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_cf_upd_zf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_cf (_update_rflagsbits_zf x v) = _get_rflagsbits_cf x := by
  simp only [_get_rflagsbits_cf, _update_rflagsbits_zf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 0 0 6 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_cf_upd_sf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_cf (_update_rflagsbits_sf x v) = _get_rflagsbits_cf x := by
  simp only [_get_rflagsbits_cf, _update_rflagsbits_sf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 0 0 7 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_cf_upd_df (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_cf (_update_rflagsbits_df x v) = _get_rflagsbits_cf x := by
  simp only [_get_rflagsbits_cf, _update_rflagsbits_df, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 0 0 10 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_cf_upd_of (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_cf (_update_rflagsbits_of x v) = _get_rflagsbits_cf x := by
  simp only [_get_rflagsbits_cf, _update_rflagsbits_of, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 0 0 11 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_pf_upd_cf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_pf (_update_rflagsbits_cf x v) = _get_rflagsbits_pf x := by
  simp only [_get_rflagsbits_pf, _update_rflagsbits_cf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 2 2 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_pf_upd_pf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_pf (_update_rflagsbits_pf x v) = v := by
  simp only [_get_rflagsbits_pf, _update_rflagsbits_pf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 2 _ v (by decide) (by decide)]; rfl

@[simp] theorem rf_get_pf_upd_af (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_pf (_update_rflagsbits_af x v) = _get_rflagsbits_pf x := by
  simp only [_get_rflagsbits_pf, _update_rflagsbits_af, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 2 2 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_pf_upd_zf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_pf (_update_rflagsbits_zf x v) = _get_rflagsbits_pf x := by
  simp only [_get_rflagsbits_pf, _update_rflagsbits_zf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 2 2 6 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_pf_upd_sf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_pf (_update_rflagsbits_sf x v) = _get_rflagsbits_pf x := by
  simp only [_get_rflagsbits_pf, _update_rflagsbits_sf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 2 2 7 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_pf_upd_df (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_pf (_update_rflagsbits_df x v) = _get_rflagsbits_pf x := by
  simp only [_get_rflagsbits_pf, _update_rflagsbits_df, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 2 2 10 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_pf_upd_of (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_pf (_update_rflagsbits_of x v) = _get_rflagsbits_pf x := by
  simp only [_get_rflagsbits_pf, _update_rflagsbits_of, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 2 2 11 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_af_upd_cf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_af (_update_rflagsbits_cf x v) = _get_rflagsbits_af x := by
  simp only [_get_rflagsbits_af, _update_rflagsbits_cf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 4 4 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_af_upd_pf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_af (_update_rflagsbits_pf x v) = _get_rflagsbits_af x := by
  simp only [_get_rflagsbits_af, _update_rflagsbits_pf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 4 4 2 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_af_upd_af (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_af (_update_rflagsbits_af x v) = v := by
  simp only [_get_rflagsbits_af, _update_rflagsbits_af, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 4 _ v (by decide) (by decide)]; rfl

@[simp] theorem rf_get_af_upd_zf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_af (_update_rflagsbits_zf x v) = _get_rflagsbits_af x := by
  simp only [_get_rflagsbits_af, _update_rflagsbits_zf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 4 4 6 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_af_upd_sf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_af (_update_rflagsbits_sf x v) = _get_rflagsbits_af x := by
  simp only [_get_rflagsbits_af, _update_rflagsbits_sf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 4 4 7 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_af_upd_df (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_af (_update_rflagsbits_df x v) = _get_rflagsbits_af x := by
  simp only [_get_rflagsbits_af, _update_rflagsbits_df, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 4 4 10 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_af_upd_of (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_af (_update_rflagsbits_of x v) = _get_rflagsbits_af x := by
  simp only [_get_rflagsbits_af, _update_rflagsbits_of, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 4 4 11 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_zf_upd_cf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_zf (_update_rflagsbits_cf x v) = _get_rflagsbits_zf x := by
  simp only [_get_rflagsbits_zf, _update_rflagsbits_cf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 6 6 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_zf_upd_pf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_zf (_update_rflagsbits_pf x v) = _get_rflagsbits_zf x := by
  simp only [_get_rflagsbits_zf, _update_rflagsbits_pf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 6 6 2 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_zf_upd_af (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_zf (_update_rflagsbits_af x v) = _get_rflagsbits_zf x := by
  simp only [_get_rflagsbits_zf, _update_rflagsbits_af, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 6 6 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_zf_upd_zf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_zf (_update_rflagsbits_zf x v) = v := by
  simp only [_get_rflagsbits_zf, _update_rflagsbits_zf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 6 _ v (by decide) (by decide)]; rfl

@[simp] theorem rf_get_zf_upd_sf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_zf (_update_rflagsbits_sf x v) = _get_rflagsbits_zf x := by
  simp only [_get_rflagsbits_zf, _update_rflagsbits_sf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 6 6 7 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_zf_upd_df (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_zf (_update_rflagsbits_df x v) = _get_rflagsbits_zf x := by
  simp only [_get_rflagsbits_zf, _update_rflagsbits_df, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 6 6 10 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_zf_upd_of (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_zf (_update_rflagsbits_of x v) = _get_rflagsbits_zf x := by
  simp only [_get_rflagsbits_zf, _update_rflagsbits_of, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 6 6 11 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_sf_upd_cf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_sf (_update_rflagsbits_cf x v) = _get_rflagsbits_sf x := by
  simp only [_get_rflagsbits_sf, _update_rflagsbits_cf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 7 7 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_sf_upd_pf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_sf (_update_rflagsbits_pf x v) = _get_rflagsbits_sf x := by
  simp only [_get_rflagsbits_sf, _update_rflagsbits_pf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 7 7 2 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_sf_upd_af (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_sf (_update_rflagsbits_af x v) = _get_rflagsbits_sf x := by
  simp only [_get_rflagsbits_sf, _update_rflagsbits_af, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 7 7 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_sf_upd_zf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_sf (_update_rflagsbits_zf x v) = _get_rflagsbits_sf x := by
  simp only [_get_rflagsbits_sf, _update_rflagsbits_zf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 7 7 6 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_sf_upd_sf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_sf (_update_rflagsbits_sf x v) = v := by
  simp only [_get_rflagsbits_sf, _update_rflagsbits_sf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 7 _ v (by decide) (by decide)]; rfl

@[simp] theorem rf_get_sf_upd_df (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_sf (_update_rflagsbits_df x v) = _get_rflagsbits_sf x := by
  simp only [_get_rflagsbits_sf, _update_rflagsbits_df, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 7 7 10 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_sf_upd_of (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_sf (_update_rflagsbits_of x v) = _get_rflagsbits_sf x := by
  simp only [_get_rflagsbits_sf, _update_rflagsbits_of, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 7 7 11 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_df_upd_cf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_df (_update_rflagsbits_cf x v) = _get_rflagsbits_df x := by
  simp only [_get_rflagsbits_df, _update_rflagsbits_cf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 10 10 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_df_upd_pf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_df (_update_rflagsbits_pf x v) = _get_rflagsbits_df x := by
  simp only [_get_rflagsbits_df, _update_rflagsbits_pf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 10 10 2 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_df_upd_af (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_df (_update_rflagsbits_af x v) = _get_rflagsbits_df x := by
  simp only [_get_rflagsbits_df, _update_rflagsbits_af, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 10 10 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_df_upd_zf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_df (_update_rflagsbits_zf x v) = _get_rflagsbits_df x := by
  simp only [_get_rflagsbits_df, _update_rflagsbits_zf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 10 10 6 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_df_upd_sf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_df (_update_rflagsbits_sf x v) = _get_rflagsbits_df x := by
  simp only [_get_rflagsbits_df, _update_rflagsbits_sf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 10 10 7 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_df_upd_df (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_df (_update_rflagsbits_df x v) = v := by
  simp only [_get_rflagsbits_df, _update_rflagsbits_df, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 10 _ v (by decide) (by decide)]; rfl

@[simp] theorem rf_get_df_upd_of (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_df (_update_rflagsbits_of x v) = _get_rflagsbits_df x := by
  simp only [_get_rflagsbits_df, _update_rflagsbits_of, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 10 10 11 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_of_upd_cf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_of (_update_rflagsbits_cf x v) = _get_rflagsbits_of x := by
  simp only [_get_rflagsbits_of, _update_rflagsbits_cf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 11 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_of_upd_pf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_of (_update_rflagsbits_pf x v) = _get_rflagsbits_of x := by
  simp only [_get_rflagsbits_of, _update_rflagsbits_pf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 11 2 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_of_upd_af (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_of (_update_rflagsbits_af x v) = _get_rflagsbits_of x := by
  simp only [_get_rflagsbits_of, _update_rflagsbits_af, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 11 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_of_upd_zf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_of (_update_rflagsbits_zf x v) = _get_rflagsbits_of x := by
  simp only [_get_rflagsbits_of, _update_rflagsbits_zf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 11 6 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_of_upd_sf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_of (_update_rflagsbits_sf x v) = _get_rflagsbits_of x := by
  simp only [_get_rflagsbits_of, _update_rflagsbits_sf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 11 7 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_of_upd_df (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_of (_update_rflagsbits_df x v) = _get_rflagsbits_of x := by
  simp only [_get_rflagsbits_of, _update_rflagsbits_df, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 11 10 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_of_upd_of (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_of (_update_rflagsbits_of x v) = v := by
  simp only [_get_rflagsbits_of, _update_rflagsbits_of, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 11 _ v (by decide) (by decide)]; rfl

@[simp] theorem rf_get_ac_upd_cf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_ac (_update_rflagsbits_cf x v) = _get_rflagsbits_ac x := by
  simp only [_get_rflagsbits_ac, _update_rflagsbits_cf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 18 18 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_ac_upd_pf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_ac (_update_rflagsbits_pf x v) = _get_rflagsbits_ac x := by
  simp only [_get_rflagsbits_ac, _update_rflagsbits_pf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 18 18 2 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_ac_upd_af (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_ac (_update_rflagsbits_af x v) = _get_rflagsbits_ac x := by
  simp only [_get_rflagsbits_ac, _update_rflagsbits_af, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 18 18 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_ac_upd_zf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_ac (_update_rflagsbits_zf x v) = _get_rflagsbits_ac x := by
  simp only [_get_rflagsbits_ac, _update_rflagsbits_zf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 18 18 6 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_ac_upd_sf (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_ac (_update_rflagsbits_sf x v) = _get_rflagsbits_ac x := by
  simp only [_get_rflagsbits_ac, _update_rflagsbits_sf, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 18 18 7 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_ac_upd_df (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_ac (_update_rflagsbits_df x v) = _get_rflagsbits_ac x := by
  simp only [_get_rflagsbits_ac, _update_rflagsbits_df, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 18 18 10 _ v (by decide) (by decide) (by decide)

@[simp] theorem rf_get_ac_upd_of (x : BitVec 32) (v : BitVec 1) : _get_rflagsbits_ac (_update_rflagsbits_of x v) = _get_rflagsbits_ac x := by
  simp only [_get_rflagsbits_ac, _update_rflagsbits_of, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 18 18 11 _ v (by decide) (by decide) (by decide)

/-- A flag value against a model flag bit: equal where Janus defines it. -/
def FlagEq (o : Option Bool) (b : BitVec 1) : Prop := ∀ v, o = some v → b = BitVec.ofBool v

/-- The model's `rflags` holds Janus' status flags (where defined), DF, and `AC = 0`. -/
structure FlagsRel (f : Janus.Amd64.Flags) (df : Bool) (r : BitVec 32) : Prop where
  cf : FlagEq f.cf (_get_rflagsbits_cf r)
  pf : FlagEq f.pf (_get_rflagsbits_pf r)
  af : FlagEq f.af (_get_rflagsbits_af r)
  zf : FlagEq f.zf (_get_rflagsbits_zf r)
  sf : FlagEq f.sf (_get_rflagsbits_sf r)
  ovf : FlagEq f.ovf (_get_rflagsbits_of r)
  df : _get_rflagsbits_df r = BitVec.ofBool df
  ac : _get_rflagsbits_ac r = 0#1

/-- `write_user_rflags out undef` on `rflags = r` with the undefined source `u`. -/
def wurf (r out undef : BitVec 32) (u : Nat) : BitVec 32 :=
  let pick (g : BitVec 32 → BitVec 1) : BitVec 1 := if g undef == 1#1 then bits_of_int (u : Int) 1 else g out
  _update_rflagsbits_of (_update_rflagsbits_sf (_update_rflagsbits_zf (_update_rflagsbits_af
    (_update_rflagsbits_pf (_update_rflagsbits_cf r (pick _get_rflagsbits_cf)) (pick _get_rflagsbits_pf))
    (pick _get_rflagsbits_af)) (pick _get_rflagsbits_zf)) (pick _get_rflagsbits_sf)) (pick _get_rflagsbits_of)

theorem run_undef_flg {s : SState} {u : Nat} (hu : s.regs.get? .janus_undef = some u) :
    (undef_flg ()).run s = .ok (bits_of_int (u : Int) 1) s := by
  simp only [undef_flg, undef_flg_logic, undef_read, undef_read_logic, run_bind, run_readReg hu, run_pure]

theorem run_flagstep (s : SState) (u : Nat) (hu : s.regs.get? .janus_undef = some u) (r : BitVec 32)
    (c : Bool) (upd : BitVec 32 → BitVec 1 → BitVec 32) (x : BitVec 1) :
    (if c = true then do
        let rv ← readReg Register.rflags
        let sv ← undef_flg ()
        writeReg Register.rflags (upd rv sv)
      else do
        let rv ← readReg Register.rflags
        writeReg Register.rflags (upd rv x)).run (s.set .rflags r) =
      .ok () (s.set .rflags (upd r (if c then bits_of_int (u : Int) 1 else x))) := by
  have hu' : (s.set .rflags r).regs.get? .janus_undef = some u := by rw [get?_set_ne _ _ (by decide)]; exact hu
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, run_bind, run_readReg (get?_set_same s .rflags r), run_writeReg,
      set_set]
  · simp only [↓reduceIte, run_bind, run_readReg (get?_set_same s .rflags r), run_undef_flg hu', run_writeReg,
      set_set]

theorem run_write_user_rflags {s : SState} {r : BitVec 32} (hr : s.regs.get? .rflags = some r)
    {u : Nat} (hu : s.regs.get? .janus_undef = some u)
    (hl : s.regs.get? .log_register_writes = some false) (out undef : BitVec 32) :
    (write_user_rflags out undef).run s = .ok () (s.set .rflags (wurf r out undef u)) := by
  have hu' : ∀ v : BitVec 32, (s.set .rflags v).regs.get? .janus_undef = some u := fun v => by
    rw [get?_set_ne _ _ (by decide)]; exact hu
  have hl' : ∀ v : BitVec 32, (s.set .rflags v).regs.get? .log_register_writes = some false := fun v => by
    rw [get?_set_ne _ _ (by decide)]; exact hl
  rw [← set_self hr]
  simp only [write_user_rflags, run_bind, run_readReg (get?_set_same s .rflags r), run_flagstep s u hu,
    run_readReg (hl' _), Bool.false_eq_true, ↓reduceIte, run_pure, set_set]
  rfl

end JanusX86.Proofs
