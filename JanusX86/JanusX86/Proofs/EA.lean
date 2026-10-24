import JanusX86.Proofs.AluClass

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
