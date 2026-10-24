import JanusX86.Proofs.Call

/-! # The two-byte map (`0F xx`): fetch and dispatch -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- The model's mandatory prefix of a two-byte opcode. -/
def mpref (x : BitVec 52) (op2 : Nat) : BitVec 8 :=
  compute_mandatory_prefix_for_two_byte_opcode .Mode_64bit (BitVec.ofNat 8 op2) x

/-- Does the two-byte opcode have a ModRM byte (the model's table for that mandatory prefix)? -/
def modrmP2 (x : BitVec 52) (op2 : Nat) : Bool :=
  two_byte_opcode_modr_m_p .Mode_64bit (mpref x op2) (BitVec.ofNat 8 op2)

set_option maxRecDepth 100000 in
theorem run_one_byte_0f (sr tr : BitVec 48) (x : BitVec 52) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x0F) m sib).run s =
      (two_byte_opcode_decode_and_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x0F)).run s := by
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true] <;> rfl

open Janus.Amd64.Decode in
/-- Fetch and decode up to `two_byte_opcode_execute`. -/
theorem run_fetch_two {s : SState} (h : X86Config s) {base : Nat}
    (hr : s.regs.get? .rip = some (BitVec.ofNat 64 base)) {bs : List Nat} (hc : CodeAt s base bs)
    {p : Prefixes} {op2 : Nat} {rest : List Nat} {n : Nat}
    (hp : parsePrefixes bs {} 0 = some (p, 0x0F :: op2 :: rest, n)) (hn : n ≤ 13) (hlim : base + 17 < 2 ^ 47) :
    ∃ x rex, PfxRel p x rex ∧
      ((modrmSib (modrmP2 x op2) rest).2.2 ≤ rest.length →
      (x86_fetch_decode_execute ()).run s =
        (two_byte_opcode_execute .Mode_64bit (BitVec.ofNat 48 base)
          (BitVec.ofNat 48 (base + n + 2 + (modrmSib (modrmP2 x op2) rest).2.2)) x (mpref x op2) rex
          (BitVec.ofNat 8 op2) (modrmSib (modrmP2 x op2) rest).1 (modrmSib (modrmP2 x op2) rest).2.1).run s) := by
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one h hr hc hp (by omega) hlim (by decide) (by decide)
    ⟨by decide, by decide, by decide⟩ (by simp [modrmSib, show modrmP1 0x0F = false by decide])
  refine ⟨x, rex, hpr, fun hlen => ?_⟩
  rw [hf]
  simp only [show modrmP1 0x0F = false by decide, modrmSib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  rw [run_one_byte_0f]
  have hdrop : bs.drop n = 0x0F :: op2 :: rest := by simpa using parsePrefixes_drop _ _ _ hp
  have hcs : CodeAt s (base + n + 1) (op2 :: rest) := by
    have h2 : (bs.drop n).drop 1 = op2 :: rest := by rw [hdrop]; rfl
    have := hc.drop (n + 1)
    rw [show bs.drop (n + 1) = op2 :: rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show base + (n + 1) = base + n + 1 by omega] at this
  have hlenb : n + 2 ≤ bs.length := by have := congrArg List.length hdrop; simp at this; omega
  have hsel : (select_address_size .Mode_64bit (some x)).run s = .ok 8 s :=
    run_select_address_size x (by rw [hpr.adr]; decide) s
  have hm1 : ∀ k, k < rest.length + 1 → k ≤ 2 →
      s.mem[(Sail.BitVec.signExtend (BitVec.ofNat 48 (base + n + 1 + k)) 64).toNat]? =
      some (BitVec.ofNat 8 ((op2 :: rest).getD k 0)) := by
    intro k hk hk2
    rw [signExtend48_toNat _ (by omega)]
    rw [hcs.2 k (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < (op2 :: rest).length by simp; omega)]
  have hadd2 : ∀ k, k ≤ 2 → (add_to_iptr .Mode_64bit (BitVec.ofNat 48 (base + n + 1 + k)) 1#48).run s =
      .ok (BitVec.ofNat 48 (base + n + 1 + (k + 1))) s := by
    intro k hk
    rw [run_add_to_iptr _ _ (by simp; omega)]
    simp; congr 1; omega
  have hb256 : ∀ b ∈ op2 :: rest, b < 256 := hcs.1
  have hm0 := hm1 0 (by omega) (by decide)
  have ha0 := hadd2 0 (by decide)
  simp only [Nat.add_zero, List.getD_cons_zero] at hm0 ha0
  simp only [two_byte_opcode_decode_and_execute, run_bind, hsel,
    run_rme08 h hr _ _ (by rw [signExtend48_toNat _ (by omega)]; omega) hm0, ha0, run_pure, Mk_modr_m, Mk_sib]
  simp only [show compute_mandatory_prefix_for_two_byte_opcode .Mode_64bit (BitVec.ofNat 8 op2) x = mpref x op2 from rfl,
    show two_byte_opcode_modr_m_p .Mode_64bit (mpref x op2) (BitVec.ofNat 8 op2) = modrmP2 x op2 from rfl]
  cases hmpv : modrmP2 x op2
  · simp only [Bool.false_eq_true, ↓reduceIte, run_pure, Bool.false_and, modrmSib, Nat.add_zero,
      run_andM_pure_false]
    (try congr 2)
  · have hr0 : 0 < rest.length := by simp [modrmSib, hmpv] at hlen; split at hlen <;> simp at hlen <;> omega
    have hm0' := hm1 1 (by omega) (by decide)
    have ha1 := hadd2 1 (by decide)
    simp only [List.getD_cons_succ] at hm0'
    have hmb := hb256 (rest.getD 0 0) (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr0])
    simp only [↓reduceIte, run_rme08 h hr _ _ (by rw [signExtend48_toNat _ (by omega)]; omega) hm0',
      ha1, Bool.true_and, run_pure, run_bind, run_andM_pure_true, modrmSib, hsel,
      show (2 == (8 : Int)) = false from rfl, sib_p_all _ hmb]
    cases hsb : sibP (rest.getD 0 0)
    · simp only [Bool.false_eq_true, ↓reduceIte, run_pure]
      (try congr 2)
    · have hr1 : 1 < rest.length := by
        have : (modrmSib (modrmP2 x op2) rest).2.2 = 2 := by simp only [modrmSib, hmpv, ↓reduceIte, hsb]
        omega
      have hm1' := hm1 2 (by omega) (by decide)
      have ha2 := hadd2 2 (by decide)
      simp only [List.getD_cons_succ] at hm1'
      simp only [↓reduceIte, run_bind, run_pure, hsel,
        run_rme08 h hr _ _ (by rw [signExtend48_toNat _ (by omega)]; omega) hm1', ha2]
      (try congr 2)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

set_option maxHeartbeats 1000000 in
/-- The frame of a two-byte (`0F xx`) instruction with a ModRM operand (and `k` immediate bytes after it). -/
theorem rm_frame2 {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n))
    (hmp : ∀ x rex, PfxRel p x rex → modrmP2 x o = true)
    (hlk : p.lock = false)
    {mm : ModRM} {r3 : List Nat} {c : Nat} (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    (hfs : ∀ k', mm.rm = .r k' → p.fs = false)
    {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {k : Nat} (hk : k < 8) (hlen : n + 2 + c + k ≤ 15)
    (arm : BitVec 48 → BitVec 48 → BitVec 52 → BitVec 8 → BitVec 8 → SailM Unit)
    (hdisp : ∀ x rex, PfxRel p x rex → _get_prefixes_lck x = 0#8 → ∀ sr tr sib,
      (two_byte_opcode_execute .Mode_64bit sr tr x (mpref x o) rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib).run s =
        (arm sr tr x rex sib).run s)
    (hsem : ∀ x rex, PfxRel p x rex → (∀ r, p.rex = some r → r < 16) → ∀ (sib : BitVec 8) (tr inc : Nat) (eaddr : BitVec 64),
      tr + inc = js.rip.toNat + n + 2 + c → inc < 8 → CodeAt s (js.rip.toNat + n + 2 + c) r3 →
      (∀ iac mp wr, locOK js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + k)) w (rmDst p w mm.rm) wr →
        ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
        (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) iac mp sg x (BitVec.ofNat 48 tr) rex
          (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 k)).run s =
          .ok (((locVal js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + k)) w (rmDst p w mm.rm)).setWidth 64).setWidth 128,
            (inc : Int), eaddr) s) →
      (∀ iac mp sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
        locOK js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + k)) w (rmDst p w mm.rm) true →
        ∀ js0 s0, Rel js0 s0 → X86Config s0 → js0.regs = js.regs → js0.mem = js.mem → js0.fsBase = js.fsBase →
        ∀ y : BitVec w, ∃ s1,
          (x86_operand_to_reg_mem .Mode_64bit (w / 8) iac mp ((y.setWidth 64).setWidth 128) sg eaddr x rex
            (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run s0 = .ok () s1 ∧
          Rel (locWrite js0 (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + k)) w (rmDst p w mm.rm) y) s1 ∧ X86Config s1 ∧
          s1.regs.get? .rflags = s0.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s0.regs.get? .janus_undef) →
      (m / 64 ≠ 3 → (x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 tr) rex (BitVec.ofNat 3 (m % 8))
        (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 k)).run s = .ok (eaddr, (inc : Int)) s) →
      (m / 64 = 3 → inc = 0 ∧ eaddr = 0#64) →
      (∀ a, mm.rm = .m a → eaddr = eaOff js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + k)) a) →
      ∃ s', (arm (BitVec.ofNat 48 js.rip.toNat) (BitVec.ofNat 48 tr) x rex sib).run s = .ok () s' ∧
        Rel js' s' ∧ X86Config s') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  have hdrop : bytes.drop n = 0x0F :: o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hm256 : m < 256 := hcode.1 m (by
    have : m ∈ bytes.drop n := by rw [hdrop]; simp
    exact List.mem_of_mem_drop this)
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hcs : CodeAt s (js.rip.toNat + n + 2 + 1) rest := by
    have h2 : (bytes.drop n).drop 3 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 3); rw [show bytes.drop (n + 3) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 3) = js.rip.toNat + n + 2 + 1 by omega] at this
  have hmdc := modrm_drop hmd
  have hc1 : 1 ≤ c := by
    obtain ⟨md, rg, ext, rm⟩ := mm
    cases rm with
    | r _ => obtain ⟨-, -, rfl, -⟩ := modrm_r hmd; omega
    | m _ => exact Nat.le_trans (by omega) (modrm_c_ge hmd).1
  have hcs3 : CodeAt s (js.rip.toNat + n + 2 + c) r3 := by
    rw [hmdc]; have := hcs.drop (c - 1)
    rwa [show js.rip.toNat + n + 2 + 1 + (c - 1) = js.rip.toNat + n + 2 + c by omega] at this
  obtain ⟨x, rex, hpr, hf⟩ := run_fetch_two hcfg hrip hcode hpp (by omega) hlim
  have hm4 : modrmSib (modrmP2 x o) (m :: rest) = (BitVec.ofNat 8 m, (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8),
      1 + (if sibP m then 1 else 0)) := by rw [hmp x rex hpr, modrmSib_eq]
  have hsl : (1 + (if sibP m then 1 else 0)) ≤ (m :: rest).length := by
    cases rest with
    | cons _ _ => simp; split <;> omega
    | nil =>
      cases hs : sibP m
      · simp
      · exfalso
        unfold sibP at hs; simp at hs
        unfold modrm at hmd; simp [hs.1, hs.2] at hmd
  have hf := hf (by rw [hm4]; simp at hsl ⊢; omega)
  rw [hm4] at hf
  simp only at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  rw [hdisp x rex hpr hl0] at hf
  obtain ⟨inc, eaddr, hinc, hinc8, hEA, hR3, hEo, hX, hWr⟩ := rm_operand hrel hcfg hpr hrv (q := js.rip.toNat + n + 2) hcs hm256 hmd hfs hW
    hk (by omega)
  rw [show js.rip.toNat + n + 2 + (1 + (if sibP m then 1 else 0)) = js.rip.toNat + n + 2 + 1 + (if sibP m then 1 else 0)
    by omega] at hf
  obtain ⟨s', hs', hr', hc'⟩ := hsem x rex hpr hrv (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8)
    (js.rip.toNat + n + 2 + 1 + (if sibP m then 1 else 0)) inc eaddr (by omega) hinc8 hcs3 hX hWr hEA hR3 hEo
  exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hr', hc'⟩


set_option maxHeartbeats 1000000 in
/-- `rm_frame2` with the dispatch stated for any `LOCK` prefix. -/
theorem rm_frame2_any {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n))
    (hmp : ∀ x rex, PfxRel p x rex → modrmP2 x o = true)
    {mm : ModRM} {r3 : List Nat} {c : Nat} (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    (hfs : ∀ k', mm.rm = .r k' → p.fs = false)
    {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {k : Nat} (hk : k < 8) (hlen : n + 2 + c + k ≤ 15)
    (arm : BitVec 48 → BitVec 48 → BitVec 52 → BitVec 8 → BitVec 8 → SailM Unit)
    (hdisp : ∀ x rex, PfxRel p x rex → ∀ sr tr sib,
      (two_byte_opcode_execute .Mode_64bit sr tr x (mpref x o) rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib).run s =
        (arm sr tr x rex sib).run s)
    (hsem : ∀ x rex, PfxRel p x rex → (∀ r, p.rex = some r → r < 16) → ∀ (sib : BitVec 8) (tr inc : Nat) (eaddr : BitVec 64),
      tr + inc = js.rip.toNat + n + 2 + c → inc < 8 → CodeAt s (js.rip.toNat + n + 2 + c) r3 →
      (∀ iac mp wr, locOK js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + k)) w (rmDst p w mm.rm) wr →
        ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
        (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) iac mp sg x (BitVec.ofNat 48 tr) rex
          (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 k)).run s =
          .ok (((locVal js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + k)) w (rmDst p w mm.rm)).setWidth 64).setWidth 128,
            (inc : Int), eaddr) s) →
      (∀ iac mp sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
        locOK js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + k)) w (rmDst p w mm.rm) true →
        ∀ js0 s0, Rel js0 s0 → X86Config s0 → js0.regs = js.regs → js0.mem = js.mem → js0.fsBase = js.fsBase →
        ∀ y : BitVec w, ∃ s1,
          (x86_operand_to_reg_mem .Mode_64bit (w / 8) iac mp ((y.setWidth 64).setWidth 128) sg eaddr x rex
            (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run s0 = .ok () s1 ∧
          Rel (locWrite js0 (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + k)) w (rmDst p w mm.rm) y) s1 ∧ X86Config s1 ∧
          s1.regs.get? .rflags = s0.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s0.regs.get? .janus_undef) →
      (m / 64 ≠ 3 → (x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 tr) rex (BitVec.ofNat 3 (m % 8))
        (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 k)).run s = .ok (eaddr, (inc : Int)) s) →
      (m / 64 = 3 → inc = 0 ∧ eaddr = 0#64) →
      (∀ a, mm.rm = .m a → eaddr = eaOff js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + k)) a) →
      ∃ s', (arm (BitVec.ofNat 48 js.rip.toNat) (BitVec.ofNat 48 tr) x rex sib).run s = .ok () s' ∧
        Rel js' s' ∧ X86Config s') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  have hdrop : bytes.drop n = 0x0F :: o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hm256 : m < 256 := hcode.1 m (by
    have : m ∈ bytes.drop n := by rw [hdrop]; simp
    exact List.mem_of_mem_drop this)
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hcs : CodeAt s (js.rip.toNat + n + 2 + 1) rest := by
    have h2 : (bytes.drop n).drop 3 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 3); rw [show bytes.drop (n + 3) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 3) = js.rip.toNat + n + 2 + 1 by omega] at this
  have hmdc := modrm_drop hmd
  have hc1 : 1 ≤ c := by
    obtain ⟨md, rg, ext, rm⟩ := mm
    cases rm with
    | r _ => obtain ⟨-, -, rfl, -⟩ := modrm_r hmd; omega
    | m _ => exact Nat.le_trans (by omega) (modrm_c_ge hmd).1
  have hcs3 : CodeAt s (js.rip.toNat + n + 2 + c) r3 := by
    rw [hmdc]; have := hcs.drop (c - 1)
    rwa [show js.rip.toNat + n + 2 + 1 + (c - 1) = js.rip.toNat + n + 2 + c by omega] at this
  obtain ⟨x, rex, hpr, hf⟩ := run_fetch_two hcfg hrip hcode hpp (by omega) hlim
  have hm4 : modrmSib (modrmP2 x o) (m :: rest) = (BitVec.ofNat 8 m, (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8),
      1 + (if sibP m then 1 else 0)) := by rw [hmp x rex hpr, modrmSib_eq]
  have hsl : (1 + (if sibP m then 1 else 0)) ≤ (m :: rest).length := by
    cases rest with
    | cons _ _ => simp; split <;> omega
    | nil =>
      cases hs : sibP m
      · simp
      · exfalso
        unfold sibP at hs; simp at hs
        unfold modrm at hmd; simp [hs.1, hs.2] at hmd
  have hf := hf (by rw [hm4]; simp at hsl ⊢; omega)
  rw [hm4] at hf
  simp only at hf
  rw [hdisp x rex hpr] at hf
  obtain ⟨inc, eaddr, hinc, hinc8, hEA, hR3, hEo, hX, hWr⟩ := rm_operand hrel hcfg hpr hrv (q := js.rip.toNat + n + 2) hcs hm256 hmd hfs hW
    hk (by omega)
  rw [show js.rip.toNat + n + 2 + (1 + (if sibP m then 1 else 0)) = js.rip.toNat + n + 2 + 1 + (if sibP m then 1 else 0)
    by omega] at hf
  obtain ⟨s', hs', hr', hc'⟩ := hsem x rex hpr hrv (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8)
    (js.rip.toNat + n + 2 + 1 + (if sibP m then 1 else 0)) inc eaddr (by omega) hinc8 hcs3 hX hWr hEA hR3 hEo
  exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hr', hc'⟩

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem n64_mp_cases (op : BitVec 8) (x : BitVec 52) :
    n64_bit_compute_mandatory_prefix_for_two_byte_opcode op x = _get_prefixes_rep x ∨
    n64_bit_compute_mandatory_prefix_for_two_byte_opcode op x = _get_prefixes_opr x ∨
    n64_bit_compute_mandatory_prefix_for_two_byte_opcode op x = 0#8 := by
  unfold n64_bit_compute_mandatory_prefix_for_two_byte_opcode
  generalize _get_prefixes_rep x = rp
  generalize _get_prefixes_opr x = oq
  cases h1 : (!rp == 0#8) <;> simp only [h1, Bool.false_eq_true, ↓reduceIte]
  · cases h2 : (!oq == 0#8) <;> simp only [h2, Bool.false_eq_true, ↓reduceIte]
    · simp
    · split <;> simp
  · split <;> simp

theorem mpref_cases {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (op2 : Nat) : mpref x op2 = 0#8 ∨ mpref x op2 = 0x66#8 ∨ mpref x op2 = 0xF2#8 ∨ mpref x op2 = 0xF3#8 := by
  have hr := hp.rep
  have ho := hp.opr
  have hm : mpref x op2 = n64_bit_compute_mandatory_prefix_for_two_byte_opcode (BitVec.ofNat 8 op2) x := rfl
  rcases n64_mp_cases (BitVec.ofNat 8 op2) x with e | e | e <;> rw [hm, e]
  · rw [hr]; rcases hp.repv with e | e | e <;> rw [e] <;> decide
  · rw [ho]; cases p.opsize <;> decide
  · decide

set_option maxRecDepth 100000 in
/-- The ModRM table of the two-byte map agrees for every mandatory prefix on `op2`. -/
theorem modrmP2_of {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (op2 : Nat) (h : ∀ mp ∈ [0#8, 0x66#8, 0xF2#8, 0xF3#8], two_byte_opcode_modr_m_p .Mode_64bit mp (BitVec.ofNat 8 op2) = true) :
    modrmP2 x op2 = true := by
  unfold modrmP2
  rcases mpref_cases hp op2 with e | e | e | e <;> rw [e] <;> exact h _ (by simp)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
/-- With no `F2`/`F3`, the mandatory prefix of `op2` is the model's `66` table entry. -/
theorem mpref_norep {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hr : p.rep = 0) (op2 : Nat) :
    mpref x op2 = n64_bit_compute_mandatory_prefix_for_two_byte_opcode (BitVec.ofNat 8 op2)
      (_update_prefixes_opr (_update_prefixes_rep 0#52 0#8) (if p.opsize then 0x66#8 else 0#8)) := by
  have h1 := hp.rep
  have h2 := hp.opr
  rw [hr] at h1
  unfold mpref compute_mandatory_prefix_for_two_byte_opcode
  simp only [in_64bit_mode, ↓reduceIte]
  unfold n64_bit_compute_mandatory_prefix_for_two_byte_opcode
  rw [h1, h2]
  cases p.opsize <;> rfl

end JanusX86.Proofs
