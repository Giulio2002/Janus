import JanusX86.Proofs.Top

/-! # Displacements and effective addresses

`x86_effective_addr` (32/64-bit addressing: ModRM, SIB, `disp8`/`disp32`, RIP-relative) against
Janus' `Decode.modrm` and `eaOff`. Displacements are read by the model from the instruction bytes
in memory (`rime_size`, sign-extending), by Janus from the byte list (`Decode.readLE`, `sext`). -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem sumLE_cons (f : Nat → Nat) : ∀ k, sumLE f (k + 1) = f 0 + 256 * sumLE (fun j => f (j + 1)) k
  | 0 => by simp [sumLE]
  | k + 1 => by
    rw [sumLE, sumLE_cons f k, sumLE]
    simp only [Nat.pow_succ]
    rw [Nat.mul_add, show f (k + 1) * (256 ^ k * 256) = 256 * (f (k + 1) * 256 ^ k) by
      rw [Nat.mul_comm (256 ^ k) 256, ← Nat.mul_assoc, Nat.mul_comm (f (k + 1)) 256, Nat.mul_assoc]]
    omega

open Janus.Amd64.Decode in
theorem readLE_sumLE : ∀ (k : Nat) (bs : List Nat) {v r}, readLE k bs = some (v, r) →
    k ≤ bs.length ∧ v = sumLE (fun j => bs.getD j 0) k ∧ r = bs.drop k
  | 0, bs, v, r, h => by simp [readLE] at h; obtain ⟨rfl, rfl⟩ := h; simp [sumLE]
  | k + 1, [], v, r, h => by simp [readLE] at h
  | k + 1, b :: bs, v, r, h => by
    simp only [readLE] at h
    cases e : readLE k bs with
    | none => simp [e] at h
    | some vr =>
      obtain ⟨v', r'⟩ := vr
      simp only [e, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3⟩ := readLE_sumLE k bs e
      refine ⟨by simp; omega, ?_, by simp [h3]⟩
      rw [sumLE_cons, h2]; simp

/-- Janus' sign extension as a model sign extension (8-, 16- and 32-bit displacements and immediates). -/
theorem sext_eq_8 (v : Nat) (hv : v < 2 ^ 8) :
    (BitVec.ofNat 8 v).signExtend 64 = BitVec.ofNat 64 (Janus.Amd64.Decode.sext 8 64 v) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  simp only [BitVec.toInt, BitVec.toNat_ofNat, Janus.Amd64.Decode.sext]
  split <;> split <;> split <;> (try rw [Nat.mod_eq_of_lt (by omega)] at *) <;> omega

theorem sext_eq_16 (v : Nat) (hv : v < 2 ^ 16) :
    (BitVec.ofNat 16 v).signExtend 64 = BitVec.ofNat 64 (Janus.Amd64.Decode.sext 16 64 v) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  simp only [BitVec.toInt, BitVec.toNat_ofNat, Janus.Amd64.Decode.sext]
  split <;> split <;> split <;> (try rw [Nat.mod_eq_of_lt (by omega)] at *) <;> omega

theorem sext_eq_32 (v : Nat) (hv : v < 2 ^ 32) :
    (BitVec.ofNat 32 v).signExtend 64 = BitVec.ofNat 64 (Janus.Amd64.Decode.sext 32 64 v) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  simp only [BitVec.toInt, BitVec.toNat_ofNat, Janus.Amd64.Decode.sext]
  split <;> split <;> split <;> (try rw [Nat.mod_eq_of_lt (by omega)] at *) <;> omega

theorem sumLE_congr (f g : Nat → Nat) (k : Nat) (h : ∀ j < k, f j = g j) : sumLE f k = sumLE g k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [sumLE]; rw [ih (fun j hj => h j (by omega)), h k (by omega)]

/-- A load of `k` instruction bytes at `t` (from `CodeAt`) as Janus reads them (`readLE`). -/
theorem run_load_code {s : SState} (hc : X86Config s) {rr : BitVec 64} (hr : s.regs.get? .rip = some rr)
    (asz : Nat) {t : Nat} {ds : List Nat} (hds : CodeAt s t ds) {k : Nat} (hk : 0 < k) {v : Nat} {r : List Nat}
    (hle : Janus.Amd64.Decode.readLE k ds = some (v, r)) (ht : t + k ≤ 2 ^ 47) (rx : String) :
    (load_bytes_from_ea .Mode_64bit asz k (Sail.BitVec.signExtend (BitVec.ofNat 48 t) 64) none 1 rx false false).run s =
      .ok (BitVec.ofNat (8 * k) v) s := by
  obtain ⟨hkl, hv, -⟩ := readLE_sumLE k ds hle
  have hst := signExtend48_toNat t (by omega)
  rw [run_load_bytes_from_ea hc hr asz hk _ none (by decide) rx false (by omega) (fun j => BitVec.ofNat 8 (ds.getD j 0))
    (fun j hj => by
      rw [hst]
      have := hds.2 j (by omega)
      rw [this]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < ds.length by omega)])]
  congr 2
  rw [hv]
  apply sumLE_congr; intro j hj
  have : ds[j]?.getD 0 < 256 := by
    rw [List.getElem?_eq_getElem (show j < ds.length by omega)]
    exact hds.1 _ (List.getElem_mem _)
  simp [Nat.mod_eq_of_lt this]

theorem run_rime_size_disp {s : SState} (hc : X86Config s) {rr : BitVec 64} (hr : s.regs.get? .rip = some rr)
    (asz : Nat) {t : Nat} {ds : List Nat} (hds : CodeAt s t ds) {k : Nat} (hk : k = 1 ∨ k = 4) {v : Nat}
    {r : List Nat} (hle : Janus.Amd64.Decode.readLE k ds = some (v, r)) (ht : t + k ≤ 2 ^ 47) :
    (rime_size .Mode_64bit asz k (Sail.BitVec.signExtend (BitVec.ofNat 48 t) 64) none 1 ":X" false false).run s =
      .ok (BitVec.ofNat 64 (Janus.Amd64.Decode.sext (8 * k) 64 v)) s := by
  obtain ⟨hkl, hv, -⟩ := readLE_sumLE k ds hle
  have hvl : v < 2 ^ (8 * k) := by
    rw [hv, Nat.pow_mul]
    exact sumLE_lt _ (fun j => by
      by_cases hj : j < ds.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hds.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
  simp only [rime_size, run_bind]
  rw [run_load_code hc hr asz hds (by omega) hle ht]
  simp only [run_pure, Sail.BitVec.signExtend]
  rcases hk with rfl | rfl
  · rw [sext_eq_8 v hvl]
  · rw [sext_eq_32 v hvl]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem ofInt_two_pow (sc : Nat) : BitVec.ofInt 64 ((2 : Int) ^ sc) = BitVec.twoPow 64 sc := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_twoPow, BitVec.toNat_ofInt]
  rw [show ((2 : Int) ^ sc) = ((2 ^ sc : Nat) : Int) by push_cast; rfl]
  rw [← Int.natCast_emod, Int.toNat_natCast]

theorem ea_combine (b i d : BitVec 64) (sc : Nat) :
    bits_of_int (b.toInt + ash_left_int i.toInt sc + d.toInt) 64 = b + (i <<< sc) + d := by
  rw [bits_of_int_eq_ofInt, BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt,
    ash_left_int, show (2 : Int) ^i (sc : Int) = (2 : Int) ^ sc by rfl, BitVec.ofInt_mul, BitVec.ofInt_toInt,
    ofInt_two_pow, ← BitVec.shiftLeft_eq_mul_twoPow]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem ea_combine2 (b d : BitVec 64) : bits_of_int (b.toInt + d.toInt) 64 = b + d := by
  rw [bits_of_int_eq_ofInt, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

theorem select_address_size_none (s : SState) :
    (select_address_size .Mode_64bit none).run s = .ok 8 s := rfl

/-- The displacement of `Decode.disp md`, as the model reads it at `t`. -/
theorem run_disp {s : SState} (hc : X86Config s) {rr : BitVec 64} (hr : s.regs.get? .rip = some rr)
    {t : Nat} {ds : List Nat} (hds : CodeAt s t ds) {md : Nat} (hmd : md = 1 ∨ md = 2) {d : Nat} {r : List Nat}
    {k : Nat} (h : Janus.Amd64.Decode.disp md ds = some (d, r, k)) (ht : t + k ≤ 2 ^ 47) :
    (rime_size .Mode_64bit 8 (if md = 1 then 1 else 4) (Sail.BitVec.signExtend (BitVec.ofNat 48 t) 64) none 1 ":X" false
      false).run s = .ok (BitVec.ofNat 64 d) s ∧ k = (if md = 1 then 1 else 4) := by
  unfold Janus.Amd64.Decode.disp at h
  rcases hmd with rfl | rfl
  · simp only [↓reduceIte] at h
    cases e : Janus.Amd64.Decode.readLE 1 ds with
    | none => simp [e] at h
    | some vr =>
      obtain ⟨v, r'⟩ := vr
      simp only [e, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact ⟨run_rime_size_disp hc hr 8 hds (Or.inl rfl) e ht, rfl⟩
  · simp only [show (2 : Nat) ≠ 1 by decide, ↓reduceIte] at h ⊢
    cases e : Janus.Amd64.Decode.readLE 4 ds with
    | none => simp [e] at h
    | some vr =>
      obtain ⟨v, r'⟩ := vr
      simp only [e, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact ⟨run_rime_size_disp hc hr 8 hds (Or.inr rfl) e ht, rfl⟩

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem beq3_5 : ∀ a < 8, (BitVec.ofNat 3 a == 0b101#3) = decide (a = 5) := by decide +kernel

theorem eqb3 : ∀ a < 8, ∀ j < 8, eq_bits_nat (BitVec.ofNat 3 a) j = decide (a = j) := by decide +kernel
theorem eqb2 : ∀ a < 4, ∀ j < 4, eq_bits_nat (BitVec.ofNat 2 a) j = decide (a = j) := by decide +kernel
theorem eqb4 : ∀ a < 16, eq_bits_nat (BitVec.ofNat 4 a) 4 = decide (a = 4) := by decide +kernel

theorem run_ea_base {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s) {rr : BitVec 64}
    (hr : s.regs.get? .rip = some rr) (rex : BitVec 8) {q m : Nat} {rest : List Nat} (hcs : CodeAt s (q + 1) rest)
    (hrm4 : m % 8 ≠ 4) (hrm5 : ¬(m % 8 = 5 ∧ m / 64 = 0)) (hmd3 : m / 64 < 3) {n : Nat} (hn16 : n < 16)
    (hn : reg_index (BitVec.ofNat 3 (m % 8)) rex 0#2 = BitVec.ofNat 4 n) {d : Nat} {r : List Nat} {k : Nat}
    (hdisp : Janus.Amd64.Decode.disp (m / 64) rest = some (d, r, k)) (nimm : BitVec 3) (sib : BitVec 8)
    (hq : q + 1 + k ≤ 2 ^ 47) :
    (x86_effective_addr_32_64 .Mode_64bit false (BitVec.ofNat 48 (q + 1)) rex (BitVec.ofNat 3 (m % 8))
      (BitVec.ofNat 2 (m / 64)) sib nimm).run s = .ok (js.regs n + BitVec.ofNat 64 d, (k : Int)) s := by
  have hrg : (rgfi (Sail.BitVec.toNatInt (BitVec.ofNat 4 n))).run s = .ok (js.regs n) s := by
    rw [toNatInt_ofNat4 n hn16]; exact run_rgfi hn16 (h.gpr n hn16)
  have hb4 : eq_bits_nat (BitVec.ofNat 3 (m % 8)) 4 = false := by
    rw [eqb3 _ (by omega) 4 (by decide)]; simp; omega
  have hb5 : eq_bits_nat (BitVec.ofNat 3 (m % 8)) 5 = decide (m % 8 = 5) := eqb3 _ (by omega) 5 (by decide)
  have hmdv : ∀ j < 4, eq_bits_nat (BitVec.ofNat 2 (m / 64)) j = decide (m / 64 = j) :=
    fun j hj => eqb2 _ (by omega) j hj
  rcases (by omega : m / 64 = 0 ∨ m / 64 = 1 ∨ m / 64 = 2) with h0 | h1 | h2
  · -- mod 00: no displacement
    have h5 : ¬ m % 8 = 5 := fun e => hrm5 ⟨e, h0⟩
    simp only [Janus.Amd64.Decode.disp, h0, show (0 : Nat) ≠ 1 by decide, show (0 : Nat) ≠ 2 by decide,
      ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdisp
    obtain ⟨rfl, -, rfl⟩ := hdisp
    simp only [x86_effective_addr_32_64, h0, hb4, hb5, h5, decide_false]
    simp (config := {decide := true}) only [↓reduceIte, Bool.false_eq_true, in_64bit_mode, run_bind, hn, hrg, run_pure]
    rw [show (BitVec.toInt (0#64)) = 0 from rfl, Int.add_zero, bits_of_int_eq_ofInt, BitVec.ofInt_toInt]
    simp
  · obtain ⟨hd, hk⟩ := run_disp hc hr hcs (Or.inl rfl) (by rw [h1] at hdisp; exact hdisp) (by omega)
    simp (config := {decide := true}) only [↓reduceIte] at hd hk
    subst hk
    simp only [x86_effective_addr_32_64, h1, hb4]
    simp (config := {decide := true}) only [↓reduceIte, Bool.false_eq_true, in_64bit_mode, run_bind, hn, hrg, run_pure,
      select_address_size_none, show Int.toNat 8 = 8 from rfl, hd]
    rw [ea_combine2]; rfl
  · obtain ⟨hd, hk⟩ := run_disp hc hr hcs (Or.inr rfl) (by rw [h2] at hdisp; exact hdisp) (by omega)
    simp (config := {decide := true}) only [↓reduceIte] at hd hk
    subst hk
    simp only [x86_effective_addr_32_64, h2, hb4]
    simp (config := {decide := true}) only [↓reduceIte, Bool.false_eq_true, in_64bit_mode, run_bind, hn, hrg, run_pure,
      select_address_size_none, show Int.toNat 8 = 8 from rfl, hd]
    rw [ea_combine2]; rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_ea_rip {s : SState} (hc : X86Config s) {rr : BitVec 64} (hr : s.regs.get? .rip = some rr)
    (rex : BitVec 8) {q : Nat} {rest : List Nat} (hcs : CodeAt s (q + 1) rest) {d : Nat} {r : List Nat}
    (hle : Janus.Amd64.Decode.readLE 4 rest = some (d, r)) {nimm : Nat} (hni : nimm < 8) (sib : BitVec 8)
    (hq : q + 5 + nimm < 2 ^ 47) :
    (x86_effective_addr_32_64 .Mode_64bit false (BitVec.ofNat 48 (q + 1)) rex (BitVec.ofNat 3 5)
      (BitVec.ofNat 2 0) sib (BitVec.ofNat 3 nimm)).run s =
      .ok (BitVec.ofNat 64 ((q + 5 + nimm + Janus.Amd64.Decode.sext 32 64 d) % 2 ^ 64), (4 : Int)) s := by
  have hd := run_rime_size_disp hc hr 8 hcs (Or.inr rfl) hle (by omega)
  have hn3 : Sail.BitVec.toNatInt (BitVec.ofNat 3 nimm) = (nimm : Int) := by
    simp [Sail.BitVec.toNatInt, Nat.mod_eq_of_lt hni]
  have hadd : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 (q + 1)) (bits_of_int (4 + (nimm : Int)) 48)).run s =
      .ok (BitVec.ofNat 48 (q + 5 + nimm)) s := by
    have e : (bits_of_int (4 + (nimm : Int)) 48).toNat = 4 + nimm := by
      rw [show (4 + (nimm : Int)) = ((4 + nimm : Nat) : Int) by omega, bits_of_int_natCast_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [run_add_to_iptr _ _ (by rw [e]; simp; omega), e]
    congr 2; simp; omega
  simp (config := {decide := true}) only [x86_effective_addr_32_64, ↓reduceIte, in_64bit_mode, run_bind,
    select_address_size_none, show Int.toNat 8 = 8 from rfl, hd, hn3, hadd, run_pure]
  rw [toInt_ofNat48 _ (by omega)]
  congr 2
  rw [bits_of_int_eq_ofInt, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reduceMul]
  omega

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- The index register value of a SIB index `idx` (`4` = no index). -/
def sibIdxVal (js : Janus.Amd64.State) (idx : Nat) : BitVec 64 := if idx = 4 then 0 else js.regs idx

theorem run_sib_index {js : Janus.Amd64.State} {s : SState} (h : Rel js s) {idx : Nat} (hidx : idx < 16)
    (s0 : SState) (hs0 : s0 = s) :
    (if eq_bits_nat (BitVec.ofNat 4 idx) 4 = true then (pure 0#64 : SailM (BitVec 64))
     else rgfi (Sail.BitVec.toNatInt (BitVec.ofNat 4 idx))).run s0 =
      .ok (sibIdxVal js idx) s := by
  subst hs0
  rw [eqb4 idx hidx]
  by_cases h4 : idx = 4
  · simp [h4, sibIdxVal]
  · simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte, sibIdxVal,
      toNatInt_ofNat4 idx hidx, run_rgfi hidx (h.gpr idx hidx)]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_from_sib_nobase {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {rr : BitVec 64} (hr : s.regs.get? .rip = some rr) (rex : BitVec 8) {q sb : Nat} (hsb : sb < 256)
    (hb5 : sb % 8 = 5) {rest2 : List Nat} (hcs : CodeAt s (q + 2) rest2) {idx : Nat} (hidx16 : idx < 16)
    (hix : reg_index (BitVec.ofNat 3 (sb / 8 % 8)) rex 1#2 = BitVec.ofNat 4 idx) {d : Nat} {r : List Nat}
    (hle : Janus.Amd64.Decode.readLE 4 rest2 = some (d, r)) (hq : q + 6 ≤ 2 ^ 47) :
    (x86_effective_addr_from_sib .Mode_64bit (BitVec.ofNat 48 (q + 2)) rex (BitVec.ofNat 2 0) (BitVec.ofNat 8 sb)).run s =
      .ok ((0#64).toInt + ash_left_int (sibIdxVal js idx).toInt (sb / 64),
        BitVec.ofNat 64 (Janus.Amd64.Decode.sext 32 64 d), (4 : Int)) s := by
  obtain ⟨f1, f2, f3⟩ := sib_fields sb hsb
  have hd := run_rime_size_disp hc hr 8 hcs (Or.inr rfl) hle (by omega)
  have hsc : Sail.BitVec.toNatInt (BitVec.ofNat 2 (sb / 64)) = ((sb / 64 : Nat) : Int) := by
    simp [Sail.BitVec.toNatInt]; omega
  have hbb : (BitVec.ofNat 3 (sb % 8) == 0b101#3) = true := by rw [hb5]; rfl
  simp (config := {decide := true}) only [x86_effective_addr_from_sib, f1, f2, f3, hbb, ↓reduceIte, run_bind,
    select_address_size_none, show Int.toNat 8 = 8 from rfl, hd, run_pure, hix, hsc]
  rw [run_sib_index h hidx16 _ rfl]
  simp only [Int.toNat_natCast, Nat.reduceMul]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_from_sib_base {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {rr : BitVec 64} (hr : s.regs.get? .rip = some rr) (rex : BitVec 8) {q sb md : Nat} (hsb : sb < 256)
    (hmd : md < 3) (hb5 : ¬(sb % 8 = 5 ∧ md = 0)) {rest2 : List Nat} (hcs : CodeAt s (q + 2) rest2)
    {bn : Nat} (hbn16 : bn < 16) (hb : reg_index (BitVec.ofNat 3 (sb % 8)) rex 0#2 = BitVec.ofNat 4 bn)
    {idx : Nat} (hidx16 : idx < 16)
    (hix : reg_index (BitVec.ofNat 3 (sb / 8 % 8)) rex 1#2 = BitVec.ofNat 4 idx) {d : Nat} {r : List Nat} {k : Nat}
    (hdisp : Janus.Amd64.Decode.disp md rest2 = some (d, r, k)) (hq : q + 2 + k ≤ 2 ^ 47) :
    (x86_effective_addr_from_sib .Mode_64bit (BitVec.ofNat 48 (q + 2)) rex (BitVec.ofNat 2 md) (BitVec.ofNat 8 sb)).run s =
      .ok ((js.regs bn).toInt + ash_left_int (sibIdxVal js idx).toInt (sb / 64), BitVec.ofNat 64 d, (k : Int)) s := by
  obtain ⟨f1, f2, f3⟩ := sib_fields sb hsb
  have hsc : Sail.BitVec.toNatInt (BitVec.ofNat 2 (sb / 64)) = ((sb / 64 : Nat) : Int) := by
    simp [Sail.BitVec.toNatInt]; omega
  have hrg : (rgfi (Sail.BitVec.toNatInt (BitVec.ofNat 4 bn))).run s = .ok (js.regs bn) s := by
    rw [toNatInt_ofNat4 bn hbn16]; exact run_rgfi hbn16 (h.gpr bn hbn16)
  have hmdv : ∀ j < 4, eq_bits_nat (BitVec.ofNat 2 md) j = decide (md = j) := fun j hj => eqb2 _ (by omega) j hj
  rcases (by omega : md = 0 ∨ md = 1 ∨ md = 2) with h0 | h1 | h2
  · subst h0
    have hbb : (BitVec.ofNat 3 (sb % 8) == 0b101#3) = false := by
      have : sb % 8 ≠ 5 := fun e => hb5 ⟨e, rfl⟩
      rw [beq3_5 _ (by omega)]; simpa using this
    simp only [Janus.Amd64.Decode.disp, show (0 : Nat) ≠ 1 by decide, show (0 : Nat) ≠ 2 by decide,
      ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdisp
    obtain ⟨rfl, -, rfl⟩ := hdisp
    simp (config := {decide := true}) only [x86_effective_addr_from_sib, f1, f2, f3, hbb, ↓reduceIte, run_bind,
      in_64bit_mode, hb, hrg, run_pure, hix, hsc]
    rw [run_sib_index h hidx16 _ rfl]
    simp only [Int.toNat_natCast]
    rfl
  · subst h1
    obtain ⟨hd, hk⟩ := run_disp hc hr hcs (Or.inl rfl) hdisp (by omega)
    simp (config := {decide := true}) only [↓reduceIte] at hd hk
    subst hk
    simp (config := {decide := true}) only [x86_effective_addr_from_sib, f1, f2, f3, ↓reduceIte, run_bind,
      in_64bit_mode, hb, hrg, run_pure, hix, hsc, select_address_size_none, show Int.toNat 8 = 8 from rfl, hd]
    rw [run_sib_index h hidx16 _ rfl]
    simp only [Int.toNat_natCast]
    rfl
  · subst h2
    obtain ⟨hd, hk⟩ := run_disp hc hr hcs (Or.inr rfl) hdisp (by omega)
    simp (config := {decide := true}) only [↓reduceIte] at hd hk
    subst hk
    simp (config := {decide := true}) only [x86_effective_addr_from_sib, f1, f2, f3, ↓reduceIte, run_bind,
      in_64bit_mode, hb, hrg, run_pure, hix, hsc, select_address_size_none, show Int.toNat 8 = 8 from rfl, hd]
    rw [run_sib_index h hidx16 _ rfl]
    simp only [Int.toNat_natCast]
    rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem CodeAt.tail {s : SState} {q b : Nat} {bs : List Nat} (h : CodeAt s q (b :: bs)) : CodeAt s (q + 1) bs :=
  ⟨fun x hx => h.1 x (by simp [hx]), fun i hi => by
    have := h.2 (i + 1) (by simp; omega)
    rw [List.getElem_cons_succ, show q + (i + 1) = q + 1 + i by omega] at this
    exact this⟩

theorem CodeAt.head {s : SState} {q b : Nat} {bs : List Nat} (h : CodeAt s q (b :: bs)) :
    s.mem[q]? = some (BitVec.ofNat 8 b) ∧ b < 256 :=
  ⟨by have := h.2 0 (by simp); rwa [List.getElem_cons_zero, Nat.add_zero] at this, h.1 b (by simp)⟩

/-- `REX.X`. -/
def rexX (p : Janus.Amd64.Decode.Prefixes) : Nat := (p.rex.getD 0) / 2 % 2

theorem hidx_x {p : Janus.Amd64.Decode.Prefixes} (hrv : ∀ r, p.rex = some r → r < 16) (a : Nat) (ha : a < 8) :
    reg_index (BitVec.ofNat 3 a) (BitVec.ofNat 8 (rexByte p)) 1#2 = BitVec.ofNat 4 (a + 8 * rexX p) := by
  unfold rexByte rexX
  cases e : p.rex with
  | none => simpa using reg_index_norex a ha 1 (by decide)
  | some r => simpa using reg_index_rex a ha r (hrv r e) 1 (by decide)

theorem hidx_b {p : Janus.Amd64.Decode.Prefixes} (hrv : ∀ r, p.rex = some r → r < 16) (a : Nat) (ha : a < 8) :
    reg_index (BitVec.ofNat 3 a) (BitVec.ofNat 8 (rexByte p)) 0#2 = BitVec.ofNat 4 (a + 8 * ((p.rex.getD 0) % 2)) := by
  unfold rexByte
  cases e : p.rex with
  | none => simpa using reg_index_norex a ha 0 (by decide)
  | some r => simpa using reg_index_rex a ha r (hrv r e) 0 (by decide)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_ea32_sib {s : SState} (t : BitVec 48) (rex : BitVec 8) (md : Nat) (hmd : md < 3) (sb : BitVec 8)
    (ni : BitVec 3) {A : Int} {D : BitVec 64} {K : Int}
    (hs : (x86_effective_addr_from_sib .Mode_64bit t rex (BitVec.ofNat 2 md) sb).run s = .ok (A, D, K) s) :
    (x86_effective_addr_32_64 .Mode_64bit false t rex (BitVec.ofNat 3 4) (BitVec.ofNat 2 md) sb ni).run s =
      .ok (bits_of_int (A + D.toInt) 64, K) s := by
  rcases (by omega : md = 0 ∨ md = 1 ∨ md = 2) with rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [x86_effective_addr_32_64, ↓reduceIte, run_bind, hs, run_pure, in_64bit_mode] <;>
  rfl

open Janus.Amd64 Janus.Amd64.Decode in
/-- **Effective addresses.** For every memory ModRM (+ SIB + displacement) Janus decodes, the model's
`x86_effective_addr` (from the bytes in memory) is Janus' `eaOff`, and its displacement length
is Janus'. `nimm` immediate bytes follow (they enter only RIP-relative addresses). -/
theorem run_x86_effective_addr {js : State} {s : SState} (h : Rel js s) (hc : X86Config s) {rr : BitVec 64}
    (hr : s.regs.get? .rip = some rr) {p : Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) {q m : Nat} {rest : List Nat} (hcs : CodeAt s (q + 1) rest) (hm : m < 256)
    {md reg ext : Nat} {a : Addr} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (⟨md, reg, ext, .m a⟩, r3, c)) {nimm : Nat} (hni : nimm < 8)
    (hq : q + c + nimm < 2 ^ 47) :
    (x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 (q + 1 + (if sibP m then 1 else 0))) rex (BitVec.ofNat 3 (m % 8))
      (BitVec.ofNat 2 (m / 64)) (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8) (BitVec.ofNat 3 nimm)).run s =
      .ok (eaOff js (BitVec.ofNat 64 (q + c + nimm)) a, ((c - 1 - (if sibP m then 1 else 0) : Nat) : Int)) s ∧
      a.fs = false ∧ md = m / 64 := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hadr : (0x67#8 == _get_prefixes_adr x) = false := by rw [hp.adr]; decide
  have hx : ∀ t rm mo sb ni, (x86_effective_addr .Mode_64bit x t rex rm mo sb ni).run s =
      (x86_effective_addr_32_64 .Mode_64bit false t rex rm mo sb ni).run s := by
    intro t rm mo sb ni
    simp only [x86_effective_addr, run_bind, run_select_address_size x hadr, hadr]
    rfl
  rw [hx]
  unfold modrm at hmd
  simp only at hmd
  have hmd3 : ¬ (m / 64 = 3) := by intro e; simp [e] at hmd
  simp only [hmd3, ↓reduceIte] at hmd
  by_cases h4 : m % 8 = 4
  · simp only [h4, ↓reduceIte] at hmd
    have hsib : sibP m = true := by unfold sibP; simp [h4]; omega
    cases rest with
    | nil => simp at hmd
    | cons sb rest2 =>
    have hsb := (CodeAt.head hcs).2
    have hcs2 : CodeAt s (q + 2) rest2 := CodeAt.tail hcs
    simp only at hmd
    have hidx := hidx_x hrv (sb / 8 % 8) (by omega)
    rw [← hrexb] at hidx
    have hidx16 : sb / 8 % 8 + 8 * rexX p < 16 := by unfold rexX; omega
    simp only [hsib, ↓reduceIte, List.getD_cons_zero, h4]
    by_cases h5 : sb % 8 = 5 ∧ m / 64 = 0
    · simp only [h5, and_self, ↓reduceIte] at hmd
      cases e : readLE 4 rest2 with
      | none => simp [e] at hmd
      | some dr =>
        obtain ⟨d, r'⟩ := dr
        simp only [e, Option.some.injEq, Prod.mk.injEq, ModRM.mk.injEq, RM.m.injEq] at hmd
        obtain ⟨⟨hmdq, -, -, rfl⟩, -, rfl⟩ := hmd
        have hS := run_from_sib_nobase h hc hr rex hsb h5.1 hcs2 hidx16 hidx e (by omega)
        rw [show m / 64 = 0 from h5.2]
        rw [run_ea32_sib _ rex 0 (by omega) _ _ hS]
        refine ⟨?_, rfl, by omega⟩
        clear hmdq
        rw [ea_combine]
        simp only [eaOff, Bool.false_eq_true, ↓reduceIte, sibIdxVal, rexX]
        congr 2
        by_cases hi : sb / 8 % 8 + 8 * (p.rex.getD 0 / 2 % 2) = 4 <;> simp [hi]
    · simp only [h5, ↓reduceIte] at hmd
      cases e : disp (m / 64) rest2 with
      | none => simp [e] at hmd
      | some drk =>
        obtain ⟨d, r', k⟩ := drk
        simp only [e, Option.some.injEq, Prod.mk.injEq, ModRM.mk.injEq, RM.m.injEq] at hmd
        obtain ⟨⟨hmdq, -, -, rfl⟩, -, rfl⟩ := hmd
        have hbn := hidx_b hrv (sb % 8) (by omega)
        rw [← hrexb] at hbn
        have hS := run_from_sib_base h hc hr rex hsb (by omega : m / 64 < 3) h5 hcs2 (by omega) hbn hidx16 hidx e
          (by omega)
        rw [run_ea32_sib _ rex (m / 64) (by omega) _ _ hS]
        refine ⟨?_, rfl, by omega⟩
        clear hmdq
        rw [ea_combine]
        simp only [eaOff, Bool.false_eq_true, ↓reduceIte, sibIdxVal, rexX]
        by_cases hi : sb / 8 % 8 + 8 * (p.rex.getD 0 / 2 % 2) = 4 <;> simp [hi]
  · simp only [h4, ↓reduceIte] at hmd
    have hsib : sibP m = false := by unfold sibP; simp [h4]
    simp only [hsib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.sub_zero]
    by_cases h5 : m % 8 = 5 ∧ m / 64 = 0
    · simp only [h5, and_self, ↓reduceIte] at hmd
      cases e : readLE 4 rest with
      | none => simp [e] at hmd
      | some dr =>
        obtain ⟨d, r'⟩ := dr
        simp only [e, Option.some.injEq, Prod.mk.injEq, ModRM.mk.injEq, RM.m.injEq] at hmd
        obtain ⟨⟨hmdq, -, -, rfl⟩, -, rfl⟩ := hmd
        rw [show m % 8 = 5 from h5.1, show m / 64 = 0 from h5.2, run_ea_rip hc hr rex hcs e hni _ (by omega)]
        refine ⟨?_, rfl, by omega⟩
        simp only [eaOff, ↓reduceIte, BitVec.toNat_ofNat]
        congr 3
        rw [Nat.mod_eq_of_lt (show q + 5 + nimm < 2 ^ 64 by omega)]
    · simp only [h5, ↓reduceIte] at hmd
      cases e : disp (m / 64) rest with
      | none => simp [e] at hmd
      | some drk =>
        obtain ⟨d, r', k⟩ := drk
        simp only [e, Option.some.injEq, Prod.mk.injEq, ModRM.mk.injEq, RM.m.injEq] at hmd
        obtain ⟨⟨hmdq, -, -, rfl⟩, -, rfl⟩ := hmd
        have hbn := hidx_b hrv (m % 8) (by omega)
        rw [← hrexb] at hbn
        rw [run_ea_base h hc hr rex hcs h4 h5 (by omega) (by omega) hbn e _ _ (by omega)]
        refine ⟨?_, rfl, by omega⟩
        simp only [eaOff, Bool.false_eq_true, ↓reduceIte]
        congr 3
        · simp
        · omega

end JanusX86.Proofs

namespace JanusX86.Proofs
open Janus.Amd64 Janus.Amd64.Decode in
theorem disp_k {md : Nat} {bs : List Nat} {d : Nat} {r : List Nat} {k : Nat} (h : disp md bs = some (d, r, k)) :
    k ≤ 4 := by
  unfold disp at h
  split at h
  · split at h <;> simp at h; omega
  · split at h
    · split at h <;> simp at h; omega
    · simp at h; omega

open Janus.Amd64 Janus.Amd64.Decode in
theorem modrm_c_ge {rx m : Nat} {rest : List Nat} {md reg ext : Nat} {a : Addr} {r3 : List Nat} {c : Nat}
    (hmd : modrm rx (m :: rest) = some (⟨md, reg, ext, .m a⟩, r3, c)) :
    1 + (if sibP m then 1 else 0) ≤ c ∧ c ≤ 6 ∧ m / 64 ≠ 3 := by
  unfold modrm at hmd
  simp only at hmd
  have hmd3 : ¬ (m / 64 = 3) := by intro e; simp [e] at hmd
  simp only [hmd3, ↓reduceIte] at hmd
  suffices H : 1 + (if sibP m then 1 else 0) ≤ c ∧ c ≤ 6 from ⟨H.1, H.2, hmd3⟩
  by_cases h4 : m % 8 = 4
  · have hs : sibP m = true := by unfold sibP; simp [h4]; omega
    simp only [h4, ↓reduceIte] at hmd
    rw [hs]; simp only [↓reduceIte]
    cases rest with
    | nil => simp at hmd
    | cons sb rest2 =>
      simp only at hmd
      split at hmd
      · cases e : readLE 4 rest2 <;> simp [e] at hmd; omega
      · cases e : disp (m / 64) rest2 <;> simp [e] at hmd
        rename_i drk; obtain ⟨d, r, k⟩ := drk; have := disp_k e; simp at hmd; omega
  · have hs : sibP m = false := by unfold sibP; simp [h4]
    simp only [h4, ↓reduceIte] at hmd
    rw [hs]; simp only [Bool.false_eq_true, ↓reduceIte]
    split at hmd
    · cases e : readLE 4 rest <;> simp [e] at hmd; omega
    · cases e : disp (m / 64) rest <;> simp [e] at hmd
      rename_i drk; obtain ⟨d, r, k⟩ := drk; have := disp_k e; simp at hmd; omega

end JanusX86.Proofs
