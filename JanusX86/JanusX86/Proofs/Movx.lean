import JanusX86.Proofs.TwoByte

/-! # MOVZX/MOVSX (`0F B6/B7/BE/BF`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem sw_dw {sw dw : Nat} (h : sw ≤ dw) (hd : dw ≤ 64) (V : BitVec sw) :
    V.setWidth 64 = (V.setWidth dw).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have := V.isLt
  have : 2 ^ sw ≤ 2 ^ dw := Nat.pow_le_pow_right (by decide) h
  have : 2 ^ dw ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hd
  simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 2000000 in
theorem run_movzx {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0xB6 ∨ opc = 0xB7) {sw : Nat} (hsw : sw = if opc = 0xB6 then 8 else 16)
    (hdw : sw < osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (V : BitVec sw) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (sw / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_movzx .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((regWrite js (osz p) (regLocOf p.rex.isSome (osz p) (regNum p m)) (V.setWidth (osz p))).setRip
        (BitVec.ofNat 64 (tr + inc))) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW3 := osz_cases p
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := Or.inr hW3
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hl := hc.log
  have hb : (if (BitVec.ofNat 8 opc == 0xB6#8) = true then (1 : Int) else 2) = ((sw / 8 : Nat) : Int) := by
    rcases hopc with rfl | rfl <;> subst hsw <;> decide
  have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) = ((osz p / 8 : Nat) : Int) := by
    unfold osz; cases rexW p <;> cases p.opsize <;> simp
  have hswv : sw ≤ osz p := by omega
  simp only [x86_movzx, h1, h2, h3, run_bind, hsg, hb, Int.toNat_natCast, ← bits3_zero, hX sg hsg4 hsg5,
    run_add_inc tr inc hinc htr, hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_pure, trunc128,
    run_select_operand_size hp hrv, hsz, nbytes_eq _ hW, show reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 =
      BitVec.ofNat 4 (regNum p m) by rw [hrexb]; exact hidx_reg hrv m,
    sw_dw hswv (by rcases hW3 with e | e | e <;> omega) V,
    run_write_rgfi_size h hl hW _ rex hrex (regNum_lt p m) (regNum_8 p m) (V.setWidth (osz p))]
  have hn' := locReg_lt p.rex.isSome (osz p) (regNum p m) (regNum_lt p m)
  refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn' rfl]; exact hl) _ htr, ?_,
    (hc.setGpr hn' _).set (by decide) _⟩
  exact (h.writeReg _ (regNum_lt p m) _).setRipR _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem sbs (sw W : Nat) (h : sw < W) (h1 : 1 < sw) (V : BitVec sw) (s : SState) :
    (signed_bitslice V 0 (W : Int)).run s = .ok (V.signExtend W) s := by
  simp only [signed_bitslice, run_bind, Sail.BitVec.length]
  have h2 : ((0 : Int) + W ≤b (sw : Int)) = false := by simp; omega
  have h3 : ((0 : Int) <b (sw : Int) - 1) = true := by simp; omega
  simp only [h2, h3, ↓reduceIte, Bool.false_eq_true, run_pure]
  rw [run_sail_assert_of ?ha]
  case ha => simp; omega
  show EStateM.Result.ok (BitVec.setWidth W (Sail.BitVec.replicateBits _ _ +++ _)) s = _
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sail.BitVec.replicateBits, Sail.BitVec.access, Sail.BitVec.extractLsb, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append, BitVec.getLsbD_replicate, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb]
  have e1 : (↑sw - 1 : Int).toNat = sw - 1 := by omega
  have e2 : ((0 : Int) + ↑W - ↑sw).toNat = W - sw := by omega
  have e3 : ((W : Int)).toNat = W := by simp
  simp only [e1, e2, e3, Int.toNat_zero, Nat.sub_zero, Nat.zero_add, Nat.mod_one, Nat.one_mul] at hi ⊢
  have hsw1 : sw - 1 + 1 = sw := by omega
  simp only [hsw1, BitVec.getLsbD_signExtend, hi, decide_true, Bool.true_and]
  by_cases hs : i < sw
  · simp [hs]
  · simp only [hs, ↓reduceIte, decide_false]
    simp [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ofBool]
    have : (i - sw < W - sw) = True := by simp; omega
    simp only [this, decide_true, Bool.true_and]
    rw [getElem!_pos V (sw - 1) (by omega)]
    rfl

theorem sbsI (sw : Nat) (W : Int) (h : (sw : Int) < W) (h1 : 1 < sw) (V : BitVec sw) (s : SState) :
    (signed_bitslice V 0 W).run s = .ok (V.signExtend W.toNat) s := by
  simp only [signed_bitslice, run_bind, Sail.BitVec.length]
  have h2 : ((0 : Int) + W ≤b (sw : Int)) = false := by simp; omega
  have h3 : ((0 : Int) <b (sw : Int) - 1) = true := by simp; omega
  simp only [h2, h3, ↓reduceIte, Bool.false_eq_true, run_pure]
  rw [run_sail_assert_of ?ha]
  case ha => simp; omega
  show EStateM.Result.ok (BitVec.setWidth W.toNat (Sail.BitVec.replicateBits _ _ +++ _)) s = _
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sail.BitVec.replicateBits, Sail.BitVec.access, Sail.BitVec.extractLsb, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append, BitVec.getLsbD_replicate, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb]
  have e1 : (↑sw - 1 : Int).toNat = sw - 1 := by omega
  have e2 : ((0 : Int) + W - ↑sw).toNat = W.toNat - sw := by omega
  simp only [e1, e2, Int.toNat_zero, Nat.sub_zero, Nat.zero_add, Nat.mod_one, Nat.one_mul] at hi ⊢
  have hsw1 : sw - 1 + 1 = sw := by omega
  simp only [hsw1, BitVec.getLsbD_signExtend, hi, decide_true, Bool.true_and]
  by_cases hs : i < sw
  · simp [hs]
  · simp only [hs, ↓reduceIte, decide_false]
    simp [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ofBool]
    have : (i - sw < W.toNat - sw) = True := by simp; omega
    simp only [this, decide_true, Bool.true_and]
    rw [getElem!_pos V (sw - 1) (by omega)]
    rfl

theorem movsx_fin {sw : Nat} (hsw : sw = 8 ∨ sw = 16) (V : BitVec sw) (W dw : Nat) (hW : W = dw) (h1 : sw < dw)
    (h2 : dw ≤ 64) :
    Sail.BitVec.truncate (Sail.BitVec.zeroExtend (sail_mask 64 (BitVec.signExtend W
      (Sail.BitVec.truncate (BitVec.setWidth 128 (BitVec.setWidth 64 V)) sw))) 128) 64 = (V.signExtend dw).setWidth 64 := by
  subst hW
  have e : Sail.BitVec.truncate (BitVec.setWidth 128 (BitVec.setWidth 64 V)) sw = V := by
    apply BitVec.eq_of_toNat_eq
    have := V.isLt
    have : 2 ^ sw ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    simp [Sail.BitVec.truncate]; try rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [sail_mask, Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Sail.BitVec.length, BitVec.getLsbD_setWidth]
  try (split <;> simp_all <;> try omega)

set_option maxHeartbeats 4000000 in
theorem run_movsx {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0xBE ∨ opc = 0xBF) {sw : Nat} (hsw : sw = if opc = 0xBE then 8 else 16)
    (hdw : sw < osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (V : BitVec sw) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (sw / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_movsxd .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((regWrite js (osz p) (regLocOf p.rex.isSome (osz p) (regNum p m)) (V.signExtend (osz p))).setRip
        (BitVec.ofNat 64 (tr + inc))) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW3 := osz_cases p
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := Or.inr hW3
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hl := hc.log
  have hb : (if (BitVec.ofNat 8 opc == 0xBE#8) = true then (1 : Int) else 2) = ((sw / 8 : Nat) : Int) := by
    rcases hopc with rfl | rfl <;> subst hsw <;> decide
  have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) = ((osz p / 8 : Nat) : Int) := by
    unfold osz; cases rexW p <;> cases p.opsize <;> simp
  have hn' := locReg_lt p.rex.isSome (osz p) (regNum p m) (regNum_lt p m)
  have hfin := run_write_rgfi_size h hl hW _ rex hrex (regNum_lt p m) (regNum_8 p m) (V.signExtend (osz p))
  simp only [x86_movsxd, h1, h2, h3, run_bind, hsg, hb, Int.toNat_natCast, ← bits3_zero, hX sg hsg4 hsg5,
    run_add_inc tr inc hinc htr, hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_pure,
    run_select_operand_size hp hrv, hsz, show reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 =
      BitVec.ofNat 4 (regNum p m) by rw [hrexb]; exact hidx_reg hrv m]
  generalize hD : osz p = dw at hfin hn' hdw hW3 ⊢
  obtain ⟨a1, a2, a4, a8⟩ := ash_k
  have hcs : (sw = 8 ∧ (dw = 16 ∨ dw = 32 ∨ dw = 64)) ∨ (sw = 16 ∧ (dw = 32 ∨ dw = 64)) := by
    rcases hopc with rfl | rfl <;> subst hsw <;> simp (config := {decide := true}) at hdw ⊢ <;> omega
  rcases hcs with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
  simp only [Nat.reduceDiv, a1, a2, a4, a8, run_bind, run_pure] at hfin ⊢ <;>
  (try simp only [show ((1 : Nat) : Int) = 1 from rfl, show ((2 : Nat) : Int) = 2 from rfl,
    show ((4 : Nat) : Int) = 4 from rfl, show ((8 : Nat) : Int) = 8 from rfl]) <;>
  (try simp only [run_bind]) <;>
  simp (disch := decide) only [sbsI, run_pure] <;>
  (first
    | simp (disch := decide) only [movsx_fin (dw := 16) (by decide) V]
    | simp (disch := decide) only [movsx_fin (dw := 32) (by decide) V]
    | simp (disch := decide) only [movsx_fin (dw := 64) (by decide) V]) <;>
  simp only [show bits_of_int 2 4 = BitVec.ofNat 4 2 by decide, show bits_of_int 4 4 = BitVec.ofNat 4 4 by decide,
    show bits_of_int 8 4 = BitVec.ofNat 4 8 by decide, hfin] <;>
  exact ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn' rfl]; exact hl) _ htr,
    (h.writeReg _ (regNum_lt p m) _).setRipR _, (hc.setGpr hn' _).set (by decide) _⟩

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_two_byte_movx (opc : Nat) (hopc : opc = 0xB6 ∨ opc = 0xB7 ∨ opc = 0xBE ∨ opc = 0xBF)
    (sr tr : BitVec 48) (x : BitVec 52) (mp : BitVec 8) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (s : SState) :
    (two_byte_opcode_execute .Mode_64bit sr tr x mp rex (BitVec.ofNat 8 opc) m sib).run s =
      (if opc < 0xBE then x86_movzx .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib
       else x86_movsxd .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases hopc with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [two_byte_opcode_execute, ext_two_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

open Janus.Amd64 Janus.Amd64.Decode in
theorem withFS_movx_r (sg : Bool) (dw sw d : Nat) (b : Bool) (k : Nat) :
    withFS (.movx sg dw sw d (regLocOf b sw k)) = none := by
  rcases regLocOf_cases b sw k with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] <;> rfl

open Janus.Amd64 in
/-- The SSE decoder has nothing at the two-byte opcodes the frame proofs cover: `CMOVcc`
(`0F 40-4F`), `SETcc` (`0F 90-9F`), `MOVZX`/`MOVSX` (`0F B6/B7/BE/BF`). -/
theorem sse_ext_none {o : Nat}
    (ho : (0x40 ≤ o ∧ o < 0x50) ∨ (0x90 ≤ o ∧ o < 0xA0) ∨ o = 0xB6 ∨ o = 0xB7 ∨ o = 0xBE ∨ o = 0xBF)
    (a : Bool) (b : Nat) (c : Option Nat) (mrm : DecodeSSE.MRM) (bs : List Nat) (n : Nat) :
    DecodeSSE.decode a b c mrm o bs n = none := by
  have : o = 0x40 ∨ o = 0x41 ∨ o = 0x42 ∨ o = 0x43 ∨ o = 0x44 ∨ o = 0x45 ∨ o = 0x46 ∨ o = 0x47 ∨
      o = 0x48 ∨ o = 0x49 ∨ o = 0x4A ∨ o = 0x4B ∨ o = 0x4C ∨ o = 0x4D ∨ o = 0x4E ∨ o = 0x4F ∨
      o = 0x90 ∨ o = 0x91 ∨ o = 0x92 ∨ o = 0x93 ∨ o = 0x94 ∨ o = 0x95 ∨ o = 0x96 ∨ o = 0x97 ∨
      o = 0x98 ∨ o = 0x99 ∨ o = 0x9A ∨ o = 0x9B ∨ o = 0x9C ∨ o = 0x9D ∨ o = 0x9E ∨ o = 0x9F ∨
      o = 0xB6 ∨ o = 0xB7 ∨ o = 0xBE ∨ o = 0xBF := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp [DecodeSSE.decode, DecodeSSE.pfop, DecodeSSE.pint66]

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_movx {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n))
    (ho : o = 0xB6 ∨ o = 0xB7 ∨ o = 0xBE ∨ o = 0xBF)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {sw : Nat} (hsw : sw = if o % 2 = 0 then 8 else 16)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.rep = 0 ∧ sw < osz p ∧ len = n + 2 + c ∧ len ≤ 15 ∧
      i = .movx (o ≥ 0xBE) (osz p) sw (regNum p m) (rmDst p sw mm.rm) ∧
      (∀ k', mm.rm = .r k' → p.fs = false) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hreg : mm.reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hreg; subst hreg
  have hW3 := osz_cases p
  rcases ho with rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, hou, true_and, and_true,
      false_and, and_false, or_false, false_or, finish] at hd hsw ⊢
    subst hsw
    by_cases hle : osz p ≤ 8 <;> by_cases hle16 : osz p ≤ 16 <;>
      by_cases hl : 15 < n + 1 + 1 + c <;> by_cases hrp : p.rep = 0 <;>
      cases hf : p.fs <;> cases hk : p.lock <;> cases rm <;>
      simp (config := {decide := true}) only [hle, hle16, hf, hk, hl, hrp, rmDst_r, rmDst_m, rmLoc_r, rmLoc_m,
        ↓reduceIte, Bool.false_eq_true, withFS_movx_r, sse_ext_none, Janus.Amd64.DecodeCrypto.decode_eq_none_of,
        Option.or_none, Option.or_some] at hd ⊢ <;>
      (try simp [withFS, lockable, withFS_movx_r, sse_ext_none] at hd ⊢)
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := hd; refine ⟨by omega, by omega, rfl, ?_⟩ <;> simp)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, by omega, rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, by omega, by omega, rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, by omega, rfl, fun _ h => by cases h⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, by omega, by omega, rfl, fun _ h => by cases h⟩)
      | omega
      | (rcases regLocOf_cases p.rex.isSome 8 ‹_› with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] at hd <;> simp at hd)
      | (rcases regLocOf_cases p.rex.isSome 16 ‹_› with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] at hd <;> simp at hd)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem modrmP2_movx {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hr : p.rep = 0) (o : Nat) (ho : o = 0xB6 ∨ o = 0xB7 ∨ o = 0xBE ∨ o = 0xBF) : modrmP2 x o = true := by
  unfold modrmP2; rw [mpref_norep hp hr]
  cases p.opsize <;> rcases ho with rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **MOVZX/MOVSX r, r/m8 / r/m16** (`0F B6/B7/BE/BF`): every ModRM form (incl. FS-relative),
destination width and prefix sequence Janus accepts. -/
theorem movx_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n))
    (ho : o = 0xB6 ∨ o = 0xB7 ∨ o = 0xBE ∨ o = 0xBF)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  cases hmd : modrm (p.rex.getD 0) (m :: rest) with
  | none =>
    exfalso
    obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
    simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
    rcases ho with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [twoByte, hmd, sse_ext_none] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  generalize hsw : (if o % 2 = 0 then 8 else 16) = sw
  obtain ⟨hlk, hrep, hdw, rfl, hlen, rfl, hfs⟩ := decode_movx hpp ho hmd hsw.symm hd
  rw [step_of_decode hd] at hstep
  have hW : sw = 8 ∨ sw = 16 ∨ sw = 32 ∨ sw = 64 := by rw [← hsw]; split <;> simp
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = 0x0F :: o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 2 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 2 + c) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  simp only [exec] at hstep
  rw [hnext] at hstep
  cases hrd : readLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c)) sw (rmDst p sw mm.rm) with
  | error e => simp [hrd] at hstep
  | ok X =>
  obtain ⟨hok, rfl⟩ := readLoc_loc hrd
  simp only [hrd, Except.ok.injEq] at hstep
  subst hstep
  refine rm_frame2 hrel hcfg hcode hlim hpp
    (fun x rex hpr => modrmP2_movx hpr hrep o ho) hlk hmd hfs hW (k := 0) (by decide)
    (by omega)
    (fun sr tr x rex sib => if o < 0xBE then x86_movzx .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib
       else x86_movsxd .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_two_byte_movx o ho sr tr x _ hl rex _ sib s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr _ _ _
  have hreg : (regLocOf p.rex.isSome (osz p) (regNum p m)) = .reg (regNum p m) := by
    unfold regLocOf; rw [if_neg (by rcases osz_cases p with e | e | e <;> omega)]
  by_cases hz : o < 0xBE
  · simp only [hz, ↓reduceIte, show decide (o ≥ 0xBE) = false by simp; omega, Bool.false_eq_true]
    obtain ⟨s', hs', hrel', hc'⟩ := run_movzx hrel hcfg hpr hrv o (by omega) (by rw [← hsw]; rcases ho with rfl | rfl | rfl | rfl <;> simp_all)
      hdw m hm256 sib tr _ inc eaddr (hX true false false hok) hinc8 js.rip.toNat (by omega) (by omega) (by omega)
    refine ⟨s', hs', ?_, hc'⟩
    rw [hreg] at hrel'
    rw [hinc'] at hrel'
    exact hrel'
  · simp only [hz, ↓reduceIte, show decide (o ≥ 0xBE) = true by simp; omega]
    obtain ⟨s', hs', hrel', hc'⟩ := run_movsx hrel hcfg hpr hrv o (by omega) (by rw [← hsw]; rcases ho with rfl | rfl | rfl | rfl <;> simp_all)
      hdw m hm256 sib tr _ inc eaddr (hX true false false hok) hinc8 js.rip.toNat (by omega) (by omega) (by omega)
    refine ⟨s', hs', ?_, hc'⟩
    rw [hreg] at hrel'
    rw [hinc'] at hrel'
    exact hrel'

end JanusX86.Proofs
