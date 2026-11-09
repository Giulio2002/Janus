import JanusX86.Proofs.AluClass
import JanusX86.Proofs.AluMem

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem CodeAt.drop {s : SState} {base : Nat} {bs : List Nat} (h : CodeAt s base bs) (k : Nat) :
    CodeAt s (base + k) (bs.drop k) :=
  ⟨fun x hx => h.1 x (List.mem_of_mem_drop hx), fun i hi => by
    have hi' : k + i < bs.length := by simp at hi; omega
    have := h.2 (k + i) hi'
    rw [show base + (k + i) = base + k + i by omega] at this
    rw [this, List.getElem_drop]⟩

theorem modrmSib_eq (m : Nat) (rest : List Nat) :
    modrmSib true (m :: rest) = (BitVec.ofNat 8 m, (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8),
      1 + (if sibP m then 1 else 0)) := by
  unfold modrmSib; cases h : sibP m <;> simp [h]

open Janus.Amd64 Janus.Amd64.Decode in
/-- The memory-destination `E, G` ALU forms from Janus' `exec` (shared by the plain and `LOCK`ed forms). -/
theorem alu_eg_mem_core {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o < 0x40) (ho2 : o % 8 < 2)
    {md reg ext : Nat} {a : Addr} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (⟨md, reg, ext, .m a⟩, r3, c))
    (hlc : ∀ x rex, PfxRel p x rex → lockChkEG (o / 8) (BitVec.ofNat 8 m) x = false)
    (hlen : n + 1 + c ≤ 15)
    (hstep : exec (.alu (aluOp (o / 8)) (if o % 2 = 0 then 8 else osz p)
        (.mem (if p.fs then { a with fs := true } else a))
        (.loc (regLocOf p.rex.isSome (if o % 2 = 0 then 8 else osz p) (regNum p m)))) (n + 1 + c) js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  simp only [exec] at hstep
  generalize hw : (if o % 2 = 0 then 8 else osz p) = w at hstep
  obtain ⟨cc, hcf, hacc, rfl⟩ := execAlu_mem (readLoc_regLocOf _ _ _ _ _) hstep
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
  obtain ⟨hc1, hc6, -⟩ := modrm_c_ge hmd
  have hsl : (1 + (if sibP m then 1 else 0)) ≤ (m :: rest).length := by
    cases rest with
    | cons _ _ => simp; split <;> omega
    | nil =>
      cases hs : sibP m
      · simp
      · exfalso
        unfold sibP at hs; simp at hs
        unfold modrm at hmd; simp [hs.1] at hmd
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [hmp, modrmSib_eq]; simp at hsl ⊢; omega)
  rw [hmp, modrmSib_eq] at hf
  simp only at hf
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hpr.rexb]; rfl
  have ho' : o = 8 * (o / 8) + o % 8 := by omega
  rw [ho', run_one_byte_e_g (o / 8) (o % 8) (by omega) ho2] at hf
  rw [hlc x rex hpr] at hf
  simp only [Bool.false_eq_true, ↓reduceIte, run_bind, run_pure] at hf
  rw [← ho'] at hf
  have hcs : CodeAt s (js.rip.toNat + n + 1 + 1) rest := by
    have h2 : (bytes.drop n).drop 2 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 2); rw [show bytes.drop (n + 2) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 2) = js.rip.toNat + n + 1 + 1 by omega] at this
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c)) % 2 ^ 64) = BitVec.ofNat 64 (js.rip.toNat + n + 1 + c) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  rw [hnext] at hacc ⊢
  obtain ⟨s', hs', hrel', hcfg'⟩ := run_alu_e_g_mem hrel hcfg hpr hrv (aluOp (o / 8)) o (by omega) hw.symm hcs hm256 hmd
    (by omega) (regNum_lt p m) (regNum_8 p m) (by rw [hrexb]; exact hidx_reg hrv m) js.rip.toNat (by omega) (by omega)
    cc hcf hacc
  rw [show js.rip.toNat + n + 1 + (1 + (if sibP m then 1 else 0)) = js.rip.toNat + n + 1 + 1 + (if sibP m then 1 else 0)
    by omega] at hf
  refine ⟨s', run_janus_x86_step (by rw [hf, hs']), ?_, hcfg'⟩
  rw [show js.rip.toNat + n + 1 + c = js.rip.toNat + n + 1 + c from rfl]
  exact hrel'

open Janus.Amd64 Janus.Amd64.Decode in
/-- **ADD/OR/ADC/SBB/AND/SUB/XOR/CMP m, r** (opcodes `00/01 … 38/39`), memory destination (every
ModRM/SIB/displacement form, RIP-relative, `FS`-relative), without `LOCK`, every width. -/
theorem alu_eg_mem_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o < 0x40) (ho2 : o % 8 < 2)
    {md reg ext : Nat} {a : Addr} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (⟨md, reg, ext, .m a⟩, r3, c)) (hlk : p.lock = false)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  obtain ⟨hrep, rfl, hlen, rfl⟩ := decode_eg_mem hpp ho ho2 hmd hlk hd
  rw [step_of_decode hd] at hstep
  refine alu_eg_mem_core hrel hcfg hcode hlim hpp ho ho2 hmd (fun x rex hpr => ?_) hlen hstep
  have := hpr.lck; rw [hlk] at this; simp only [Bool.false_eq_true, ↓reduceIte] at this
  unfold lockChkEG; split <;> simp [this]

end JanusX86.Proofs
