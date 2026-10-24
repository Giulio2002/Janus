import JanusX86.Proofs.Fetch
import Janus

/-! # Legacy prefixes and REX: `get_prefixes` against Janus' `parsePrefixes`

`get_prefixes` reads one byte at a time and records the last prefix of each group in the
`prefixes` bitfield (`lck`/`rep`, `seg`, `opr`, `adr`), the REX byte separately (reset by a later
legacy prefix), and finally the opcode byte (`nxt`) and the number of prefix bytes (`num`). On
every prefix sequence Janus accepts, the result is the image of Janus' `Decode.Prefixes`
(`PfxRel`). -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem getLsbD_updateSubrange' {N : Nat} (x : BitVec N) (lo len : Nat) (y : BitVec len) (k : Nat)
    (hlen : lo + len ≤ N) :
    (Sail.BitVec.updateSubrange' x lo len y).getLsbD k =
      if lo ≤ k ∧ k < lo + len then y.getLsbD (k - lo) else x.getLsbD k := by
  simp only [Sail.BitVec.updateSubrange']
  by_cases hkN : k < N
  · by_cases h1 : lo ≤ k ∧ k < lo + len
    · rw [if_pos h1]
      simp [BitVec.getLsbD_shiftLeft, hkN, h1.1, show ¬ k < lo by omega, show k - lo < len by omega]
    · rw [if_neg h1]
      by_cases h2 : k < lo
      · simp [BitVec.getLsbD_shiftLeft, hkN, h2]
      · have : y.getLsbD (k - lo) = false := BitVec.getLsbD_of_ge y _ (by omega)
        simp [BitVec.getLsbD_shiftLeft, hkN, h2, this]; omega
  · have e1 : x.getLsbD k = false := BitVec.getLsbD_of_ge x k (by omega)
    simp [hkN, BitVec.getLsbD_shiftLeft, e1]
    intro _ _; omega

theorem extractLsb_upd_disj {N : Nat} (x : BitVec N) (hi lo lo' len : Nat) (y : BitVec len)
    (hd : hi < lo' ∨ lo' + len ≤ lo) (hlo : lo ≤ hi) (hw : lo' + len ≤ N) :
    (Sail.BitVec.updateSubrange' x lo' len y).extractLsb hi lo = x.extractLsb hi lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb, getLsbD_updateSubrange' x lo' len y _ hw]
  have : ¬ (lo' ≤ lo + k ∧ lo + k < lo' + len) := by omega
  simp [this]

theorem extractLsb_upd_same {N : Nat} (x : BitVec N) (lo len : Nat) (y : BitVec len)
    (hl : 0 < len) (hw : lo + len ≤ N) :
    (Sail.BitVec.updateSubrange' x lo len y).extractLsb (lo + len - 1) lo = y.setWidth _ := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb, getLsbD_updateSubrange' x lo len y _ hw, BitVec.getLsbD_setWidth]
  have : lo ≤ lo + k ∧ lo + k < lo + len := by omega
  simp [this, show k < lo + len - 1 - lo + 1 by omega]

theorem bits_of_int_natCast_toNat (x n : Nat) : (bits_of_int (x : Int) n).toNat = x % 2 ^ n := by
  simp only [bits_of_int, Sail.get_slice_int, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.zero_add,
    BitVec.toNat_ofInt]
  have : ((x : Int) % ((2 ^ (n + 1) : Nat) : Int)).toNat = x % 2 ^ (n + 1) := by omega
  rw [this, Nat.pow_succ, Nat.mod_mul_right_mod]

theorem run_add_to_iptr (a d : BitVec 48) (h : a.toNat + d.toNat < 2 ^ 47) (s : SState) :
    (add_to_iptr .Mode_64bit a d).run s = .ok (BitVec.ofNat 48 (a.toNat + d.toNat)) s := by
  have ha : a.toInt = a.toNat := toInt_of_lt a (by omega)
  have hd : d.toInt = d.toNat := toInt_of_lt d (by omega)
  have e : (bits_of_int ((a.toNat : Int) + (d.toNat : Int)) 49).toNat = a.toNat + d.toNat := by
    rw [show ((a.toNat : Int) + (d.toNat : Int)) = ((a.toNat + d.toNat : Nat) : Int) by omega,
      bits_of_int_natCast_toNat, Nat.mod_eq_of_lt (by omega)]
  have hi : (bits_of_int ((a.toNat : Int) + (d.toNat : Int)) 49).toInt = ((a.toNat + d.toNat : Nat) : Int) := by
    rw [toInt_of_lt _ (by rw [e]; omega), e]
  simp only [add_to_iptr, ha, hd, in_64bit_mode, ↓reduceIte, run_bind, run_canonical_address_p, hi,
    canon_ok (Int.natCast_nonneg _) (by omega : ((a.toNat + d.toNat : Nat) : Int) < 2 ^ 47)]
  show EStateM.Result.ok _ s = _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.truncate, e]

/-- The prefix group of a byte (the model's 256-entry table), on all 256 bytes. -/
def prefixGroup (b : Nat) : Int :=
  if b = 0xF0 ∨ b = 0xF2 ∨ b = 0xF3 then 1
  else if b = 0x26 ∨ b = 0x2E ∨ b = 0x36 ∨ b = 0x3E ∨ b = 0x64 ∨ b = 0x65 then 2
  else if b = 0x66 then 3 else if b = 0x67 then 4 else 0

theorem prefix_code_all : ∀ b < 256, get_one_byte_prefix_array_code (BitVec.ofNat 8 b) = prefixGroup b := by
  decide +kernel

/-! Field reads after field writes of the `prefixes` bitfield. -/

@[simp] theorem pfx_get_nxt_upd_nxt (x : BitVec 52) (v : BitVec 8) : _get_prefixes_nxt (_update_prefixes_nxt x v) = v := by
  simp only [_get_prefixes_nxt, _update_prefixes_nxt, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 44 _ v (by decide) (by decide)]; rfl

@[simp] theorem pfx_get_nxt_upd_adr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_nxt (_update_prefixes_adr x v) = _get_prefixes_nxt x := by
  simp only [_get_prefixes_nxt, _update_prefixes_adr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 51 44 36 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_nxt_upd_opr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_nxt (_update_prefixes_opr x v) = _get_prefixes_nxt x := by
  simp only [_get_prefixes_nxt, _update_prefixes_opr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 51 44 28 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_nxt_upd_seg (x : BitVec 52) (v : BitVec 8) : _get_prefixes_nxt (_update_prefixes_seg x v) = _get_prefixes_nxt x := by
  simp only [_get_prefixes_nxt, _update_prefixes_seg, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 51 44 20 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_nxt_upd_rep (x : BitVec 52) (v : BitVec 8) : _get_prefixes_nxt (_update_prefixes_rep x v) = _get_prefixes_nxt x := by
  simp only [_get_prefixes_nxt, _update_prefixes_rep, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 51 44 12 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_nxt_upd_lck (x : BitVec 52) (v : BitVec 8) : _get_prefixes_nxt (_update_prefixes_lck x v) = _get_prefixes_nxt x := by
  simp only [_get_prefixes_nxt, _update_prefixes_lck, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 51 44 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_nxt_upd_num (x : BitVec 52) (v : BitVec 4) : _get_prefixes_nxt (_update_prefixes_num x v) = _get_prefixes_nxt x := by
  simp only [_get_prefixes_nxt, _update_prefixes_num, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 51 44 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_adr_upd_nxt (x : BitVec 52) (v : BitVec 8) : _get_prefixes_adr (_update_prefixes_nxt x v) = _get_prefixes_adr x := by
  simp only [_get_prefixes_adr, _update_prefixes_nxt, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 43 36 44 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_adr_upd_adr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_adr (_update_prefixes_adr x v) = v := by
  simp only [_get_prefixes_adr, _update_prefixes_adr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 36 _ v (by decide) (by decide)]; rfl

@[simp] theorem pfx_get_adr_upd_opr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_adr (_update_prefixes_opr x v) = _get_prefixes_adr x := by
  simp only [_get_prefixes_adr, _update_prefixes_opr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 43 36 28 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_adr_upd_seg (x : BitVec 52) (v : BitVec 8) : _get_prefixes_adr (_update_prefixes_seg x v) = _get_prefixes_adr x := by
  simp only [_get_prefixes_adr, _update_prefixes_seg, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 43 36 20 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_adr_upd_rep (x : BitVec 52) (v : BitVec 8) : _get_prefixes_adr (_update_prefixes_rep x v) = _get_prefixes_adr x := by
  simp only [_get_prefixes_adr, _update_prefixes_rep, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 43 36 12 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_adr_upd_lck (x : BitVec 52) (v : BitVec 8) : _get_prefixes_adr (_update_prefixes_lck x v) = _get_prefixes_adr x := by
  simp only [_get_prefixes_adr, _update_prefixes_lck, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 43 36 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_adr_upd_num (x : BitVec 52) (v : BitVec 4) : _get_prefixes_adr (_update_prefixes_num x v) = _get_prefixes_adr x := by
  simp only [_get_prefixes_adr, _update_prefixes_num, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 43 36 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_opr_upd_nxt (x : BitVec 52) (v : BitVec 8) : _get_prefixes_opr (_update_prefixes_nxt x v) = _get_prefixes_opr x := by
  simp only [_get_prefixes_opr, _update_prefixes_nxt, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 35 28 44 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_opr_upd_adr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_opr (_update_prefixes_adr x v) = _get_prefixes_opr x := by
  simp only [_get_prefixes_opr, _update_prefixes_adr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 35 28 36 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_opr_upd_opr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_opr (_update_prefixes_opr x v) = v := by
  simp only [_get_prefixes_opr, _update_prefixes_opr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 28 _ v (by decide) (by decide)]; rfl

@[simp] theorem pfx_get_opr_upd_seg (x : BitVec 52) (v : BitVec 8) : _get_prefixes_opr (_update_prefixes_seg x v) = _get_prefixes_opr x := by
  simp only [_get_prefixes_opr, _update_prefixes_seg, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 35 28 20 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_opr_upd_rep (x : BitVec 52) (v : BitVec 8) : _get_prefixes_opr (_update_prefixes_rep x v) = _get_prefixes_opr x := by
  simp only [_get_prefixes_opr, _update_prefixes_rep, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 35 28 12 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_opr_upd_lck (x : BitVec 52) (v : BitVec 8) : _get_prefixes_opr (_update_prefixes_lck x v) = _get_prefixes_opr x := by
  simp only [_get_prefixes_opr, _update_prefixes_lck, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 35 28 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_opr_upd_num (x : BitVec 52) (v : BitVec 4) : _get_prefixes_opr (_update_prefixes_num x v) = _get_prefixes_opr x := by
  simp only [_get_prefixes_opr, _update_prefixes_num, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 35 28 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_seg_upd_nxt (x : BitVec 52) (v : BitVec 8) : _get_prefixes_seg (_update_prefixes_nxt x v) = _get_prefixes_seg x := by
  simp only [_get_prefixes_seg, _update_prefixes_nxt, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 27 20 44 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_seg_upd_adr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_seg (_update_prefixes_adr x v) = _get_prefixes_seg x := by
  simp only [_get_prefixes_seg, _update_prefixes_adr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 27 20 36 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_seg_upd_opr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_seg (_update_prefixes_opr x v) = _get_prefixes_seg x := by
  simp only [_get_prefixes_seg, _update_prefixes_opr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 27 20 28 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_seg_upd_seg (x : BitVec 52) (v : BitVec 8) : _get_prefixes_seg (_update_prefixes_seg x v) = v := by
  simp only [_get_prefixes_seg, _update_prefixes_seg, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 20 _ v (by decide) (by decide)]; rfl

@[simp] theorem pfx_get_seg_upd_rep (x : BitVec 52) (v : BitVec 8) : _get_prefixes_seg (_update_prefixes_rep x v) = _get_prefixes_seg x := by
  simp only [_get_prefixes_seg, _update_prefixes_rep, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 27 20 12 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_seg_upd_lck (x : BitVec 52) (v : BitVec 8) : _get_prefixes_seg (_update_prefixes_lck x v) = _get_prefixes_seg x := by
  simp only [_get_prefixes_seg, _update_prefixes_lck, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 27 20 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_seg_upd_num (x : BitVec 52) (v : BitVec 4) : _get_prefixes_seg (_update_prefixes_num x v) = _get_prefixes_seg x := by
  simp only [_get_prefixes_seg, _update_prefixes_num, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 27 20 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_rep_upd_nxt (x : BitVec 52) (v : BitVec 8) : _get_prefixes_rep (_update_prefixes_nxt x v) = _get_prefixes_rep x := by
  simp only [_get_prefixes_rep, _update_prefixes_nxt, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 19 12 44 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_rep_upd_adr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_rep (_update_prefixes_adr x v) = _get_prefixes_rep x := by
  simp only [_get_prefixes_rep, _update_prefixes_adr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 19 12 36 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_rep_upd_opr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_rep (_update_prefixes_opr x v) = _get_prefixes_rep x := by
  simp only [_get_prefixes_rep, _update_prefixes_opr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 19 12 28 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_rep_upd_seg (x : BitVec 52) (v : BitVec 8) : _get_prefixes_rep (_update_prefixes_seg x v) = _get_prefixes_rep x := by
  simp only [_get_prefixes_rep, _update_prefixes_seg, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 19 12 20 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_rep_upd_rep (x : BitVec 52) (v : BitVec 8) : _get_prefixes_rep (_update_prefixes_rep x v) = v := by
  simp only [_get_prefixes_rep, _update_prefixes_rep, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 12 _ v (by decide) (by decide)]; rfl

@[simp] theorem pfx_get_rep_upd_lck (x : BitVec 52) (v : BitVec 8) : _get_prefixes_rep (_update_prefixes_lck x v) = _get_prefixes_rep x := by
  simp only [_get_prefixes_rep, _update_prefixes_lck, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 19 12 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_rep_upd_num (x : BitVec 52) (v : BitVec 4) : _get_prefixes_rep (_update_prefixes_num x v) = _get_prefixes_rep x := by
  simp only [_get_prefixes_rep, _update_prefixes_num, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 19 12 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_lck_upd_nxt (x : BitVec 52) (v : BitVec 8) : _get_prefixes_lck (_update_prefixes_nxt x v) = _get_prefixes_lck x := by
  simp only [_get_prefixes_lck, _update_prefixes_nxt, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 4 44 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_lck_upd_adr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_lck (_update_prefixes_adr x v) = _get_prefixes_lck x := by
  simp only [_get_prefixes_lck, _update_prefixes_adr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 4 36 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_lck_upd_opr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_lck (_update_prefixes_opr x v) = _get_prefixes_lck x := by
  simp only [_get_prefixes_lck, _update_prefixes_opr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 4 28 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_lck_upd_seg (x : BitVec 52) (v : BitVec 8) : _get_prefixes_lck (_update_prefixes_seg x v) = _get_prefixes_lck x := by
  simp only [_get_prefixes_lck, _update_prefixes_seg, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 4 20 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_lck_upd_rep (x : BitVec 52) (v : BitVec 8) : _get_prefixes_lck (_update_prefixes_rep x v) = _get_prefixes_lck x := by
  simp only [_get_prefixes_lck, _update_prefixes_rep, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 4 12 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_lck_upd_lck (x : BitVec 52) (v : BitVec 8) : _get_prefixes_lck (_update_prefixes_lck x v) = v := by
  simp only [_get_prefixes_lck, _update_prefixes_lck, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 4 _ v (by decide) (by decide)]; rfl

@[simp] theorem pfx_get_lck_upd_num (x : BitVec 52) (v : BitVec 4) : _get_prefixes_lck (_update_prefixes_num x v) = _get_prefixes_lck x := by
  simp only [_get_prefixes_lck, _update_prefixes_num, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 11 4 0 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_num_upd_nxt (x : BitVec 52) (v : BitVec 8) : _get_prefixes_num (_update_prefixes_nxt x v) = _get_prefixes_num x := by
  simp only [_get_prefixes_num, _update_prefixes_nxt, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 3 0 44 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_num_upd_adr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_num (_update_prefixes_adr x v) = _get_prefixes_num x := by
  simp only [_get_prefixes_num, _update_prefixes_adr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 3 0 36 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_num_upd_opr (x : BitVec 52) (v : BitVec 8) : _get_prefixes_num (_update_prefixes_opr x v) = _get_prefixes_num x := by
  simp only [_get_prefixes_num, _update_prefixes_opr, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 3 0 28 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_num_upd_seg (x : BitVec 52) (v : BitVec 8) : _get_prefixes_num (_update_prefixes_seg x v) = _get_prefixes_num x := by
  simp only [_get_prefixes_num, _update_prefixes_seg, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 3 0 20 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_num_upd_rep (x : BitVec 52) (v : BitVec 8) : _get_prefixes_num (_update_prefixes_rep x v) = _get_prefixes_num x := by
  simp only [_get_prefixes_num, _update_prefixes_rep, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 3 0 12 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_num_upd_lck (x : BitVec 52) (v : BitVec 8) : _get_prefixes_num (_update_prefixes_lck x v) = _get_prefixes_num x := by
  simp only [_get_prefixes_num, _update_prefixes_lck, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  exact extractLsb_upd_disj x 3 0 4 _ v (by decide) (by decide) (by decide)

@[simp] theorem pfx_get_num_upd_num (x : BitVec 52) (v : BitVec 4) : _get_prefixes_num (_update_prefixes_num x v) = v := by
  simp only [_get_prefixes_num, _update_prefixes_num, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange]
  rw [extractLsb_upd_same x 0 _ v (by decide) (by decide)]; rfl

theorem rex_test_all : ∀ b < 256,
    (bits_of_int (ash_int (Sail.BitVec.toNatInt (BitVec.ofNat 8 b)) (Neg.neg 4)) 4 == 0x4#4) = decide (b / 16 = 4) := by
  decide +kernel

theorem signExtend48_toNat (a : Nat) (h : a < 2 ^ 47) :
    (Sail.BitVec.signExtend (BitVec.ofNat 48 a) 64).toNat = a := by
  have hm : (BitVec.ofNat 48 a).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp; omega
  simp only [Sail.BitVec.signExtend]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  simp; omega

open Janus.Amd64.Decode in
/-- The Sail prefix record `x` and REX byte `rex` hold Janus' parsed prefixes `p`. -/
structure PfxRel (p : Prefixes) (x : BitVec 52) (rex : BitVec 8) : Prop where
  opr : _get_prefixes_opr x = if p.opsize then 0x66#8 else 0#8
  rep : _get_prefixes_rep x = BitVec.ofNat 8 p.rep
  lck : _get_prefixes_lck x = if p.lock then 0xF0#8 else 0#8
  seg : _get_prefixes_seg x = if p.fs then 0x64#8 else 0#8
  adr : _get_prefixes_adr x = 0#8
  rexb : rex = BitVec.ofNat 8 (match p.rex with | some r => 0x40 + r | none => 0)
  repv : p.rep = 0 ∨ p.rep = 0xF2 ∨ p.rep = 0xF3

theorem pfxRel_init : PfxRel {} (Mk_prefixes 0x0000000000000#52) 0x00#8 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩

/-- One step of `get_prefixes`: read the byte at `a`, then dispatch on its prefix group. -/
theorem run_get_prefixes_step {s : SState} (h : X86Config s) {r : BitVec 64}
    (hr : s.regs.get? .rip = some r) {a : Nat} (ha : a + 1 < 2 ^ 47) {x : BitVec 52} {rex : BitVec 8}
    (hadr : _get_prefixes_adr x = 0#8) {b : Nat} (hb : b < 256)
    (hm : s.mem[a]? = some (BitVec.ofNat 8 b)) {c : Nat} (hc : c ≠ 0) :
    (get_prefixes .Mode_64bit (BitVec.ofNat 48 a) x rex c).run s =
      (if prefixGroup b = 0 then
        (if b / 16 = 4 then (get_prefixes .Mode_64bit (BitVec.ofNat 48 (a + 1)) x (BitVec.ofNat 8 b) (c - 1)).run s
         else .ok (_update_prefixes_num (_update_prefixes_nxt x (BitVec.ofNat 8 b)) (bits_of_int (15 - (c : Int)) 4), rex) s)
      else if prefixGroup b = 1 then
        (get_prefixes .Mode_64bit (BitVec.ofNat 48 (a + 1))
          (if b = 0xF0 then _update_prefixes_lck x (BitVec.ofNat 8 b) else _update_prefixes_rep x (BitVec.ofNat 8 b))
          0#8 (c - 1)).run s
      else if prefixGroup b = 2 then
        (get_prefixes .Mode_64bit (BitVec.ofNat 48 (a + 1))
          (if b = 0x64 ∨ b = 0x65 then _update_prefixes_seg x (BitVec.ofNat 8 b) else x) 0#8 (c - 1)).run s
      else if prefixGroup b = 3 then
        (get_prefixes .Mode_64bit (BitVec.ofNat 48 (a + 1)) (_update_prefixes_opr x (BitVec.ofNat 8 b)) 0#8 (c - 1)).run s
      else
        (get_prefixes .Mode_64bit (BitVec.ofNat 48 (a + 1)) (_update_prefixes_adr x (BitVec.ofNat 8 b)) 0#8 (c - 1)).run s) := by
  have ha' : (BitVec.ofNat 48 a).toNat = a := by simp; omega
  have hsx : (Sail.BitVec.signExtend (BitVec.ofNat 48 a) 64).toNat = a := signExtend48_toNat a (by omega)
  have hm' : s.mem[(Sail.BitVec.signExtend (BitVec.ofNat 48 a) 64).toNat]? = some (BitVec.ofNat 8 b) := by
    rw [hsx]; exact hm
  have hadd : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 a) 1#48).run s = .ok (BitVec.ofNat 48 (a + 1)) s := by
    rw [run_add_to_iptr _ _ (by rw [ha']; simp; omega)]; rw [ha']; rfl
  have hc1 : ((c : Int) - 1).toNat = c - 1 := by omega
  rw [get_prefixes]
  simp only [show (c == 0) = false by simpa using hc, Bool.false_eq_true, ↓reduceIte, is_ext_prefix_byte,
    run_bind, run_select_address_size x (by rw [hadr]; decide), run_rme08 h hr _ _ (by omega) hm',
    prefix_code_all b hb, rex_test_all b hb, in_64bit_mode, Bool.true_and, hc1]
  unfold prefixGroup
  by_cases h1 : b = 0xF0 ∨ b = 0xF2 ∨ b = 0xF3
  · simp only [h1, ↓reduceIte, run_bind, hadd]
    rcases h1 with rfl | rfl | rfl <;> rfl
  by_cases h2 : b = 0x26 ∨ b = 0x2E ∨ b = 0x36 ∨ b = 0x3E ∨ b = 0x64 ∨ b = 0x65
  · simp only [h1, h2, ↓reduceIte, run_bind, hadd]
    rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  by_cases h3 : b = 0x66
  · subst h3; simp (config := {decide := true}) only [↓reduceIte, run_bind, hadd]
  by_cases h4 : b = 0x67
  · subst h4; simp (config := {decide := true}) only [↓reduceIte, run_bind, hadd]
  simp only [h1, h2, h3, h4, ↓reduceIte]
  by_cases h5 : b / 16 = 4
  · simp only [h5, decide_true, ↓reduceIte, run_bind, hadd]
  · simp only [h5, decide_false, Bool.false_eq_true, ↓reduceIte, run_pure]

open Janus.Amd64.Decode in
theorem parsePrefixes_le : ∀ (bs : List Nat) (p : Prefixes) (n : Nat) {p' ops n'},
    parsePrefixes bs p n = some (p', ops, n') → n ≤ n'
  | [], _, _, _, _, _, h => by simp [parsePrefixes] at h
  | b :: bs, p, n, p', ops, n', h => by
    revert h
    unfold parsePrefixes
    repeat' split
    all_goals intro h
    all_goals first
      | (simp at h; done)
      | (have := parsePrefixes_le _ _ _ h; omega)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; omega)

namespace PfxRel
open Janus.Amd64.Decode
variable {p : Prefixes} {x : BitVec 52} {rex : BitVec 8}

theorem opsize (h : PfxRel p x rex) (hr : p.rex = none) :
    PfxRel { p with opsize := true } (_update_prefixes_opr x (BitVec.ofNat 8 0x66)) 0#8 :=
  ⟨by simp, by simp [h.rep], by simp [h.lck], by simp [h.seg], by simp [h.adr], by simp [hr], h.repv⟩

theorem repP (h : PfxRel p x rex) (hr : p.rex = none) {b : Nat} (hb : b = 0xF2 ∨ b = 0xF3) :
    PfxRel { p with rep := b } (_update_prefixes_rep x (BitVec.ofNat 8 b)) 0#8 :=
  ⟨by simp [h.opr], by simp, by simp [h.lck], by simp [h.seg], by simp [h.adr], by simp [hr],
    by rcases hb with rfl | rfl <;> simp⟩

theorem lockP (h : PfxRel p x rex) (hr : p.rex = none) :
    PfxRel { p with lock := true } (_update_prefixes_lck x (BitVec.ofNat 8 0xF0)) 0#8 :=
  ⟨by simp [h.opr], by simp [h.rep], by simp, by simp [h.seg], by simp [h.adr], by simp [hr], h.repv⟩

theorem nullSeg (h : PfxRel p x rex) (hr : p.rex = none) : PfxRel { p with seg := true } x 0#8 :=
  ⟨h.opr, h.rep, h.lck, h.seg, h.adr, by simp [hr], h.repv⟩

theorem fsP (h : PfxRel p x rex) (hr : p.rex = none) :
    PfxRel { p with fs := true } (_update_prefixes_seg x (BitVec.ofNat 8 0x64)) 0#8 :=
  ⟨by simp [h.opr], by simp [h.rep], by simp [h.lck], by simp, by simp [h.adr], by simp [hr], h.repv⟩

theorem rexp (h : PfxRel p x rex) {b : Nat} (hb : 64 ≤ b ∧ b < 80) :
    PfxRel { p with rex := some (b - 64) } x (BitVec.ofNat 8 b) :=
  ⟨h.opr, h.rep, h.lck, h.seg, h.adr, by simp; congr 1; omega, h.repv⟩

theorem fin (h : PfxRel p x rex) (v : BitVec 8) (w : BitVec 4) :
    PfxRel p (_update_prefixes_num (_update_prefixes_nxt x v) w) rex :=
  ⟨by simp [h.opr], by simp [h.rep], by simp [h.lck], by simp [h.seg], by simp [h.adr], h.rexb, h.repv⟩

end PfxRel

open Janus.Amd64.Decode in
/-- `get_prefixes` simulates Janus' `parsePrefixes` on every prefix sequence Janus accepts, up to an
opcode byte that is not a prefix for the model either. -/
theorem run_get_prefixes {s : SState} (h : X86Config s) {r : BitVec 64}
    (hr : s.regs.get? .rip = some r) (base : Nat) :
    ∀ (bs : List Nat) (p : Prefixes) (n : Nat) (x : BitVec 52) (rex : BitVec 8) {p' : Prefixes} {op : Nat}
      {rest : List Nat} {n' : Nat},
      PfxRel p x rex → (∀ b ∈ bs, b < 256) →
      (∀ i (hi : i < bs.length), s.mem[base + n + i]? = some (BitVec.ofNat 8 bs[i])) →
      parsePrefixes bs p n = some (p', op :: rest, n') → n' ≤ 14 → base + n' + 1 < 2 ^ 47 →
      prefixGroup op = 0 → op / 16 ≠ 4 →
      ∃ x' rex', (get_prefixes .Mode_64bit (BitVec.ofNat 48 (base + n)) x rex (15 - n)).run s =
          .ok (x', rex') s ∧ PfxRel p' x' rex' ∧ _get_prefixes_nxt x' = BitVec.ofNat 8 op ∧
          (_get_prefixes_num x').toNat = n'
  | [], _, _, _, _, _, _, _, _, _, _, _, hp, _, _, _, _ => by simp [parsePrefixes] at hp
  | b :: bs, p, n, x, rex, p', op, rest, n', hrel, hbs, hm, hp, hn', hlim, hop, hop4 => by
    have hb : b < 256 := hbs b (by simp)
    have hbs' : ∀ c ∈ bs, c < 256 := fun c hc => hbs c (by simp [hc])
    have hm0 : s.mem[base + n]? = some (BitVec.ofNat 8 b) := by
      have := hm 0 (by simp); rwa [List.getElem_cons_zero, Nat.add_zero] at this
    have hm' : ∀ i (hi : i < bs.length), s.mem[base + (n + 1) + i]? = some (BitVec.ofNat 8 bs[i]) := by
      intro i hi
      have := hm (i + 1) (by simp; omega)
      rw [List.getElem_cons_succ] at this
      rwa [show base + n + (i + 1) = base + (n + 1) + i by omega] at this
    have hle : n ≤ n' := parsePrefixes_le _ _ _ hp
    have hc : 15 - n ≠ 0 := by omega
    have hc1 : 15 - n - 1 = 15 - (n + 1) := by omega
    have ha : base + n + 1 < 2 ^ 47 := by omega
    rw [run_get_prefixes_step h hr ha hrel.adr hb hm0 hc, hc1, show base + n + 1 = base + (n + 1) by omega]
    unfold parsePrefixes at hp
    have hnone : ∀ {o : Option Nat}, (o.isSome = true) = False → o = none := by
      intro o ho; cases o <;> simp_all
    by_cases h1 : b = 0x66
    · subst h1
      simp only [↓reduceIte] at hp
      split at hp
      · simp at hp
      · next hrx =>
        simp (config := {decide := true}) only [prefixGroup, ↓reduceIte]
        exact run_get_prefixes h hr base bs _ (n + 1) _ _ (hrel.opsize (by simpa using hrx)) hbs' hm' hp
          hn' hlim hop hop4
    simp only [h1, ↓reduceIte] at hp
    by_cases h2 : b = 0xF2 ∨ b = 0xF3
    · simp only [h2, ↓reduceIte] at hp
      split at hp
      · simp at hp
      · next hc2 =>
        have hrx : p.rex = none := by
          cases e : p.rex <;> simp_all
        rcases h2 with rfl | rfl <;>
        · simp (config := {decide := true}) only [prefixGroup, ↓reduceIte]
          exact run_get_prefixes h hr base bs _ (n + 1) _ _ (hrel.repP hrx (by decide)) hbs' hm' hp
            hn' hlim hop hop4
    simp only [h2, ↓reduceIte] at hp
    by_cases h3 : b = 0xF0
    · subst h3
      simp only [↓reduceIte] at hp
      split at hp
      · simp at hp
      · next hc2 =>
        have hrx : p.rex = none := by
          cases e : p.rex <;> simp_all
        simp (config := {decide := true}) only [prefixGroup, ↓reduceIte]
        exact run_get_prefixes h hr base bs _ (n + 1) _ _ (hrel.lockP hrx) hbs' hm' hp hn' hlim hop hop4
    simp only [h3, ↓reduceIte] at hp
    by_cases h4 : b = 0x26 ∨ b = 0x2E ∨ b = 0x36 ∨ b = 0x3E
    · simp only [h4, ↓reduceIte] at hp
      split at hp
      · simp at hp
      · next hc2 =>
        have hrx : p.rex = none := by
          cases e : p.rex <;> simp_all
        rcases h4 with rfl | rfl | rfl | rfl <;>
        · simp (config := {decide := true}) only [prefixGroup, ↓reduceIte]
          exact run_get_prefixes h hr base bs _ (n + 1) _ _ (hrel.nullSeg hrx) hbs' hm' hp hn' hlim hop hop4
    simp only [h4, ↓reduceIte] at hp
    by_cases h5 : b = 0x64
    · subst h5
      simp only [↓reduceIte] at hp
      split at hp
      · simp at hp
      · next hc2 =>
        have hrx : p.rex = none := by
          cases e : p.rex <;> simp_all
        simp (config := {decide := true}) only [prefixGroup, ↓reduceIte]
        exact run_get_prefixes h hr base bs _ (n + 1) _ _ (hrel.fsP hrx) hbs' hm' hp hn' hlim hop hop4
    simp only [h5, ↓reduceIte] at hp
    by_cases h6 : 64 ≤ b ∧ b < 80
    · simp only [h6, and_self, ↓reduceIte] at hp
      split at hp
      · simp at hp
      · have hg : prefixGroup b = 0 := by unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
        have h16 : b / 16 = 4 := by omega
        simp only [hg, h16, ↓reduceIte]
        exact run_get_prefixes h hr base bs _ (n + 1) _ _ (hrel.rexp h6) hbs' hm' hp hn' hlim hop hop4
    simp only [h6, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at hp
    obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := hp
    simp only [hop, hop4, ↓reduceIte]
    refine ⟨_, _, rfl, hrel.fin _ _, by simp, ?_⟩
    simp only [pfx_get_num_upd_num]
    have : (15 : Int) - ((15 - n : Nat) : Int) = (n : Nat) := by omega
    rw [this, bits_of_int_natCast_toNat, Nat.mod_eq_of_lt (by omega)]

end JanusX86.Proofs
