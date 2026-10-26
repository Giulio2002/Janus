import JanusX86.Proofs.Top

/-! # Class theorems: integer ALU -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem hidx_rm {p : Janus.Amd64.Decode.Prefixes} (hrv : ∀ r, p.rex = some r → r < 16) (m : Nat) :
    reg_index (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 8 (rexByte p)) 0#2 = BitVec.ofNat 4 (rmNum p m) := by
  unfold rexByte rmNum
  cases e : p.rex with
  | none => simpa using reg_index_norex (m % 8) (by omega) 0 (by decide)
  | some r =>
    have := reg_index_rex (m % 8) (by omega) r (hrv r e) 0 (by decide)
    simpa using this

theorem hidx_reg {p : Janus.Amd64.Decode.Prefixes} (hrv : ∀ r, p.rex = some r → r < 16) (m : Nat) :
    reg_index (BitVec.ofNat 3 (m / 8 % 8)) (BitVec.ofNat 8 (rexByte p)) 2#2 = BitVec.ofNat 4 (regNum p m) := by
  unfold rexByte regNum
  cases e : p.rex with
  | none => simpa using reg_index_norex (m / 8 % 8) (by omega) 2 (by decide)
  | some r =>
    have := reg_index_rex (m / 8 % 8) (by omega) r (hrv r e) 2 (by decide)
    simpa using this

theorem rmNum_lt (p : Janus.Amd64.Decode.Prefixes) (m : Nat) : rmNum p m < 16 := by unfold rmNum; omega
theorem regNum_lt (p : Janus.Amd64.Decode.Prefixes) (m : Nat) : regNum p m < 16 := by unfold regNum; omega
theorem rmNum_8 (p : Janus.Amd64.Decode.Prefixes) (m : Nat) : rmNum p m < 8 ∨ p.rex.isSome = true := by
  unfold rmNum; cases p.rex <;> simp; omega
theorem regNum_8 (p : Janus.Amd64.Decode.Prefixes) (m : Nat) : regNum p m < 8 ∨ p.rex.isSome = true := by
  unfold regNum; cases p.rex <;> simp; omega

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem sibP_reg (m : Nat) (hm : m / 64 = 3) : sibP m = false := by
  unfold sibP; simp [hm]

open Janus.Amd64 Janus.Amd64.Decode in
/-- **ADD/OR/ADC/SBB/AND/SUB/XOR/CMP r/m, r** (opcodes `00/01 08/09 … 38/39`), register
destination (`mod = 11`), every prefix sequence Janus accepts, every width (8 with and
without REX, 16, 32, 64). -/
theorem alu_eg_reg_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o < 0x40) (ho2 : o % 8 < 2)
    (hm : m / 64 = 3) (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  -- Janus' side
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hlk, hfs, hrep, rfl, hlen, rfl⟩ := decode_eg_reg hpp ho ho2 hm hd
  rw [step_of_decode hd] at hstep
  simp only [exec] at hstep
  generalize hw : (if o % 2 = 0 then 8 else osz p) = w at hstep
  obtain ⟨c, hcf, rfl⟩ := execAlu_reg (readLoc_regLocOf _ _ _ _ _) (readLocRW_regLocOf _ _ _ _ _)
    (readLoc_regLocOf _ _ _ _ _) (writeLoc_regLocOf _ _ _ _ _) hstep
  -- the model's side
  have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hm256 : m < 256 := hcode.1 m (by
    have : m ∈ bytes.drop n := by rw [hdrop]; simp
    exact List.mem_of_mem_drop this)
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hpg : prefixGroup o = 0 := by
    unfold prefixGroup; split <;> (try split) <;> (try split) <;> (try split) <;> omega
  have hmp : modrmP1 o = true := modrmP1_eg o ho (by omega)
  have hms : modrmSib (modrmP1 o) (m :: rest) = (BitVec.ofNat 8 m, 0#8, 1) := by
    simp [modrmSib, hmp, sibP_reg m hm]
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [hms]; simp)
  rw [hms] at hf
  simp only at hf
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hpr.rexb]; rfl
  have ho' : o = 8 * (o / 8) + o % 8 := by omega
  rw [ho', run_one_byte_e_g (o / 8) (o % 8) (by omega) ho2] at hf
  have hlk' : lockChkEG (o / 8) (BitVec.ofNat 8 m) x = false := by
    have := hpr.lck; rw [hlk] at this; simp only [Bool.false_eq_true, ↓reduceIte] at this
    unfold lockChkEG; split <;> simp [this]
  rw [hlk'] at hf
  simp only [Bool.false_eq_true, ↓reduceIte, run_bind, run_pure] at hf
  rw [← ho'] at hf
  obtain ⟨s', hs', hrel', hcfg'⟩ := run_alu_e_g_reg hrel hcfg hpr hrv (aluOp (o / 8)) o (by omega) hw.symm m hm256 hm
    (rmNum_lt p m) (regNum_lt p m) (rmNum_8 p m) (regNum_8 p m) (by rw [hrexb]; exact hidx_rm hrv m)
    (by rw [hrexb]; exact hidx_reg hrv m) js.rip.toNat (js.rip.toNat + n + 1 + 1) (by omega) (by omega)
    (by omega) 0#8 c hcf
  refine ⟨s', run_janus_x86_step (by rw [hf, hs']), ?_, hcfg'⟩
  have e : (BitVec.toNat js.rip + (n + 2)) % 2 ^ 64 = js.rip.toNat + n + 1 + 1 := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [e]; exact hrel' 

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem modrm_reg {rx m : Nat} {rest : List Nat} {mm : ModRM} {r3 : List Nat} {c : Nat}
    (h : modrm rx (m :: rest) = some (mm, r3, c)) : mm.reg = m / 8 % 8 + 8 * (rx / 4 % 2) := by
  revert h
  unfold modrm
  simp only
  repeat' split
  all_goals intro h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, -⟩ := h; rfl)

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_eg_mem {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o < 0x40) (ho2 : o % 8 < 2)
    {md reg ext : Nat} {a : Addr} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (⟨md, reg, ext, .m a⟩, r3, c)) (hlk : p.lock = false)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.rep = 0 ∧ len = n + 1 + c ∧ len ≤ 15 ∧
      i = .alu (aluOp (o / 8)) (if o % 2 = 0 then 8 else osz p)
        (.mem (if p.fs then { a with fs := true } else a))
        (.loc (regLocOf p.rex.isSome (if o % 2 = 0 then 8 else osz p) (regNum p m))) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hno : ¬ (o = 0x0F) := by omega
  have hc1 : o < 0x40 ∧ o % 8 < 6 := ⟨ho, by omega⟩
  have hf4 : ¬ (o % 8 = 4) := by omega
  have hf5 : ¬ (o % 8 = 5) := by omega
  have hreg : reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  subst hreg
  simp only [hno, ↓reduceIte, oneByte, hc1, and_self, hf4, hf5, hmd, ho2, osz_eq, hlk, Bool.false_eq_true] at hd
  have hrg : ∀ w, regLoc p.rex.isSome w (regNum p m) = regLocOf p.rex.isSome w (regNum p m) := fun _ => rfl
  simp only [hrg, finish, rmLoc] at hd
  by_cases hlen : n + 1 + c > 15
  · simp [hlen] at hd
  by_cases hr : p.rep = 0
  · simp only [hlen, hr, ↓reduceIte] at hd
    cases hf : p.fs
    · simp [hf] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact ⟨hr, rfl, by omega, by simp⟩
    · simp [hf, withFS] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact ⟨hr, rfl, by omega, by simp⟩
  · simp [hlen, hr] at hd

end JanusX86.Proofs

