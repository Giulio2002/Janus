import JanusX86.Proofs.Branch

/-! # `LOCK`ed forms as single steps (the model is single-threaded; Janus checks the alignment) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem decode_eg_mem_lock {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o < 0x40) (ho2 : o % 8 < 2)
    {md reg ext : Nat} {a : Addr} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (⟨md, reg, ext, .m a⟩, r3, c)) (hlk : p.lock = true)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.rep = 0 ∧ p.fs = false ∧ o / 8 ≠ 7 ∧ len = n + 1 + c ∧ len ≤ 15 ∧
      i = .locked (.alu (aluOp (o / 8)) (if o % 2 = 0 then 8 else osz p) (.mem a)
        (.loc (regLocOf p.rex.isSome (if o % 2 = 0 then 8 else osz p) (regNum p m)))) a
        ((if o % 2 = 0 then 8 else osz p) / 8) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hno : ¬ (o = 0x0F) := by omega
  have hc1 : o < 0x40 ∧ o % 8 < 6 := ⟨ho, by omega⟩
  have hf4 : ¬ (o % 8 = 4) := by omega
  have hf5 : ¬ (o % 8 = 5) := by omega
  have hreg : reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  subst hreg
  simp only [hno, ↓reduceIte, oneByte, hc1, and_self, hf4, hf5, hmd, ho2, osz_eq, hlk] at hd
  have hrg : ∀ w, regLoc p.rex.isSome w (regNum p m) = regLocOf p.rex.isSome w (regNum p m) := fun _ => rfl
  simp only [hrg, finish, rmLoc] at hd
  by_cases hlen : n + 1 + c > 15
  · simp [hlen] at hd
  by_cases hr : p.rep = 0
  · simp only [hlen, hr, ↓reduceIte] at hd
    by_cases h7 : o / 8 = 7
    · exfalso; simp [h7, aluOp, lockable] at hd
    · have hlo : lockable (.alu (aluOp (o / 8)) (if o % 2 = 0 then 8 else osz p) (.mem a)
          (.loc (regLocOf p.rex.isSome (if o % 2 = 0 then 8 else osz p) (regNum p m)))) = true := by
        have hne : aluOp (o / 8) ≠ AluOp.cmp := by
          unfold aluOp; (repeat' split) <;> first | omega | (intro h; cases h)
        simp [lockable, hne]
      simp only [hlo, ↓reduceIte, wrapLocked, lockMem] at hd
      cases hf : p.fs
      · simp [hf] at hd
        obtain ⟨rfl, rfl⟩ := hd
        exact ⟨hr, rfl, h7, rfl, by omega, rfl⟩
      · simp [hf, withFS] at hd
  · simp [hlen, hr] at hd

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

/-- A `LOCK`ed instruction that Janus executes executed its body (the alignment check passed). -/
theorem exec_locked {i : Instr} {a : Addr} {sz len : Nat} {js js' : State}
    (h : exec (.locked i a sz) len js = .ok js') : exec i len js = .ok js' := by
  simp only [exec] at h
  split at h
  · cases h
  · exact h

set_option maxHeartbeats 1000000 in
/-- **LOCK ADD/OR/ADC/SBB/AND/SUB/XOR m, r** (`F0 00/01 … 30/31`): the `LOCK`ed memory forms as one
step (the model is single-threaded: the same arm as without `LOCK`). -/
theorem alu_eg_mem_lock_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o < 0x40) (ho2 : o % 8 < 2)
    {md reg ext : Nat} {a : Addr} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (⟨md, reg, ext, .m a⟩, r3, c)) (hlk : p.lock = true)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hrep, hfs, h7, rfl, hlen, rfl⟩ := decode_eg_mem_lock hpp ho ho2 hmd hlk hd
  rw [step_of_decode hd] at hstep
  have hx := exec_locked hstep
  have hm3 := (modrm_c_ge hmd).2.2
  refine alu_eg_mem_core hrel hcfg hcode hlim hpp ho ho2 hmd (fun x rex hpr => ?_) hlen (by simpa [hfs] using hx)
  unfold lockChkEG
  rw [if_neg h7]
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hmod : (_get_modr_m_mod (BitVec.ofNat 8 m) == 3#2) = false := by
    rw [(modrm_fields m hm256).1]
    have : m / 64 < 4 := by omega
    revert hm3 this; generalize m / 64 = q; intro h1 h2
    rcases (show q = 0 ∨ q = 1 ∨ q = 2 by omega) with rfl | rfl | rfl <;> decide
  simp [hmod]

end JanusX86.Proofs
