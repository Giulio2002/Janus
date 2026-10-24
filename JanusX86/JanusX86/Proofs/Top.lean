import JanusX86.Proofs.AluDisp1

/-! # The harness entry point and Janus' decoder -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_janus_x86_step {s s' : SState} (h : (x86_fetch_decode_execute ()).run s = .ok () s') :
    (janus_x86_step ()).run s = .ok .Janus_OK s' := by
  simp only [janus_x86_step, run_sailTryCatch, run_bind, h, run_pure]

open Janus.Amd64.Decode in
theorem parsePrefixes_rexv : ∀ (bs : List Nat) (p : Prefixes) (n : Nat) {p' ops n'},
    (∀ r, p.rex = some r → r < 16) → parsePrefixes bs p n = some (p', ops, n') → ∀ r, p'.rex = some r → r < 16
  | [], _, _, _, _, _, _, h => by simp [parsePrefixes] at h
  | b :: bs, p, n, p', ops, n', hv, h => by
    revert h
    unfold parsePrefixes
    repeat' split
    all_goals intro h
    all_goals first
      | (simp at h; done)
      | (exact parsePrefixes_rexv _ _ _ (by intro r hr; simp at hr; first | exact hv r hr | omega) h)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, -, -⟩ := h
         exact hv)

theorem modrmP1_eg : ∀ o < 64, o % 8 < 4 → modrmP1 o = true := by decide +kernel

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64.Decode in
theorem parsePrefixes_head : ∀ (bs : List Nat) (p : Prefixes) (n : Nat) {p' o rest n'},
    parsePrefixes bs p n = some (p', o :: rest, n') → o ≠ 0xC4 → o ≠ 0xC5 →
    ∃ b0 t, bs = b0 :: t ∧ b0 ≠ 0xC4 ∧ b0 ≠ 0xC5
  | [], _, _, _, _, _, _, h, _, _ => by simp [parsePrefixes] at h
  | b :: bs, p, n, p', o, rest, n', h, h4, h5 => by
    refine ⟨b, bs, rfl, ?_⟩
    revert h
    unfold parsePrefixes
    repeat' split
    all_goals intro h
    all_goals first
      | (simp at h; done)
      | omega
      | (simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at h
         obtain ⟨-, ⟨rfl, -⟩, -⟩ := h
         exact ⟨h4, h5⟩)

/-- The general-register number of a ModRM `r/m` field (with `REX.B`) and of its `reg` field
(with `REX.R`). -/
def rmNum (p : Janus.Amd64.Decode.Prefixes) (m : Nat) : Nat := m % 8 + 8 * ((p.rex.getD 0) % 2)
def regNum (p : Janus.Amd64.Decode.Prefixes) (m : Nat) : Nat := m / 8 % 8 + 8 * ((p.rex.getD 0) / 4 % 2)

open Janus.Amd64 Janus.Amd64.Decode in
theorem regLocOf_cases (rexP : Bool) (w n : Nat) :
    (∃ r, regLocOf rexP w n = .reg r) ∨ (∃ r, regLocOf rexP w n = .high r) := by
  unfold regLocOf reg8; split
  · split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

open Janus.Amd64 Janus.Amd64.Decode in
theorem lockable_alu_reg (op : AluOp) (w : Nat) (rexP : Bool) (w' n : Nat) (src : Src) :
    lockable (.alu op w (regLocOf rexP w' n) src) = false := by
  rcases regLocOf_cases rexP w' n with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] <;> rfl

open Janus.Amd64 Janus.Amd64.Decode in
theorem withFS_alu_reg (op : AluOp) (w : Nat) (rexP : Bool) (w' n n' : Nat) :
    withFS (.alu op w (regLocOf rexP w' n) (.loc (regLocOf rexP w' n'))) = none := by
  rcases regLocOf_cases rexP w' n with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] <;>
  rcases regLocOf_cases rexP w' n' with ⟨r', e'⟩ | ⟨r', e'⟩ <;> rw [e'] <;> rfl

theorem osz_eq (p : Janus.Amd64.Decode.Prefixes) (o : Nat) :
    (if o % 8 % 2 = 0 then 8 else if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) =
      (if o % 2 = 0 then 8 else osz p) := by
  have : o % 8 % 2 = o % 2 := by omega
  simp only [this, osz, rexW, decide_eq_true_eq]

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_eg_reg {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o < 0x40) (ho2 : o % 8 < 2)
    (hm : m / 64 = 3) {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ len = n + 2 ∧ len ≤ 15 ∧
      i = .alu (aluOp (o / 8)) (if o % 2 = 0 then 8 else osz p)
        (regLocOf p.rex.isSome (if o % 2 = 0 then 8 else osz p) (rmNum p m))
        (.loc (regLocOf p.rex.isSome (if o % 2 = 0 then 8 else osz p) (regNum p m))) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hno : ¬ (o = 0x0F) := by omega
  have hc1 : o < 0x40 ∧ o % 8 < 6 := ⟨ho, by omega⟩
  have hf4 : ¬ (o % 8 = 4) := by omega
  have hf5 : ¬ (o % 8 = 5) := by omega
  have hf2 : o % 8 < 2 := ho2
  have hmm : modrm (p.rex.getD 0) (m :: rest) =
      some (⟨3, regNum p m, m / 8 % 8, .r (rmNum p m)⟩, rest, 1) := by
    simp [modrm, hm, rmNum, regNum]
  simp only [hno, ↓reduceIte, oneByte, hc1, and_self, hf4, hf5, hmm, hf2, osz_eq] at hd
  have hrm : ∀ w, rmLoc p.rex.isSome w (RM.r (rmNum p m)) = regLocOf p.rex.isSome w (rmNum p m) := fun _ => rfl
  have hrg : ∀ w, regLoc p.rex.isSome w (regNum p m) = regLocOf p.rex.isSome w (regNum p m) := fun _ => rfl
  simp only [hrm, hrg, finish] at hd
  by_cases hlen : n + 1 + 1 > 15
  · simp [hlen] at hd
  by_cases hr : p.rep = 0
  · simp only [hlen, hr, ↓reduceIte] at hd
    cases hf : p.fs <;> cases hl : p.lock <;>
      simp [hf, hl, lockable_alu_reg, withFS_alu_reg] at hd
    obtain ⟨rfl, rfl⟩ := hd
    exact ⟨rfl, rfl, hr, rfl, by omega, rfl⟩
  · simp [hlen, hr] at hd

end JanusX86.Proofs
