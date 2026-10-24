import JanusX86.Proofs.AluEI

/-! # The r/m operand frame

Every one-byte instruction with a ModRM byte follows the same path through the model: the
prefixes, the opcode, ModRM (and SIB), the dispatch to the instruction's arm, which reads the
r/m operand (a register, or memory at the effective address) and may write it back. `rm_frame`
does this once: it hands the arm's semantics (`hsem`) the facts about the r/m operand as
Janus sees it (`locOK`, `locVal`, `locWrite`) and turns the arm's agreement into agreement
of the whole step. -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

/-- Janus can access the r/m location (`wr`: for writing); always for a register. -/
def locOK (js : State) (next : BitVec 64) (w : Nat) : Loc → Bool → Prop
  | .mem a, wr => js.mem.accessible (ea js next a).toNat (w / 8) wr = true
  | _, _ => True

/-- The value Janus reads from the r/m location. -/
def locVal (js : State) (next : BitVec 64) (w : Nat) : Loc → BitVec w
  | .mem a => BitVec.ofNat w (js.mem.readLE (ea js next a).toNat (w / 8))
  | l => regVal js w l

/-- Janus' state after writing `y` to the r/m location. -/
def locWrite (js : State) (next : BitVec 64) (w : Nat) : Loc → BitVec w → State
  | .mem a, y => memWrite js (ea js next a).toNat (w / 8) y.toNat
  | l, y => regWrite js w l y

theorem readLoc_loc {js : State} {next : BitVec 64} {w : Nat} {D : Loc} {X : BitVec w}
    (h : readLoc js next w D = .ok X) : locOK js next w D false ∧ X = locVal js next w D := by
  cases D with
  | reg r => simp [readLoc] at h; exact ⟨trivial, h.symm⟩
  | high r => simp [readLoc] at h; exact ⟨trivial, h.symm⟩
  | mem a => exact readLoc_mem h

theorem readLocRW_loc {js : State} {next : BitVec 64} {w : Nat} {D : Loc} {X : BitVec w}
    (h : readLocRW js next w D = .ok X) : locOK js next w D true ∧ X = locVal js next w D := by
  cases D with
  | reg r => simp [readLocRW] at h; exact ⟨trivial, h.symm⟩
  | high r => simp [readLocRW] at h; exact ⟨trivial, h.symm⟩
  | mem a => exact readLocRW_mem h

theorem readLoc_of_ok {js : State} {next : BitVec 64} {w : Nat} {D : Loc} (h : locOK js next w D false) :
    readLoc js next w D = .ok (locVal js next w D) := by
  cases D with
  | reg r => rfl
  | high r => rfl
  | mem a =>
    simp only [locOK] at h
    simp [readLoc, load, h, locVal]

theorem writeLoc_loc {js : State} {next : BitVec 64} {w : Nat} {D : Loc} (h : locOK js next w D true) (y : BitVec w) :
    writeLoc js next w D y = .ok (locWrite js next w D y) := by
  cases D with
  | reg r => rfl
  | high r => rfl
  | mem a => exact writeLoc_mem y h

theorem locOK_mono {js : State} {next : BitVec 64} {w : Nat} {D : Loc} (h : locOK js next w D true) :
    locOK js next w D false := by
  cases D with
  | reg r => trivial
  | high r => trivial
  | mem a => exact Janus.Arm64.Memory.accessible_read_of_write js.mem h

theorem locVal_regLocOf (js : State) (next : BitVec 64) (w : Nat) (b : Bool) (n : Nat) :
    locVal js next w (regLocOf b w n) = regVal js w (regLocOf b w n) := by
  unfold regLocOf Janus.Amd64.Decode.reg8; split
  · split <;> rfl
  · rfl

theorem locWrite_regLocOf (js : State) (next : BitVec 64) (w : Nat) (b : Bool) (n : Nat) (y : BitVec w) :
    locWrite js next w (regLocOf b w n) y = regWrite js w (regLocOf b w n) y := by
  unfold regLocOf Janus.Amd64.Decode.reg8; split
  · split <;> rfl
  · rfl

theorem eaOff_congr {js js0 : State} (h : js0.regs = js.regs) (next : BitVec 64) (a : Addr) :
    eaOff js0 next a = eaOff js next a := by
  unfold eaOff; simp [h]

theorem ea_congr {js js0 : State} (h : js0.regs = js.regs) (hf : js0.fsBase = js.fsBase) (next : BitVec 64) (a : Addr) :
    ea js0 next a = ea js next a := by
  unfold ea; simp [eaOff_congr h, hf]

theorem locWrite_flags (js : State) (next : BitVec 64) (w : Nat) (D : Loc) (y : BitVec w) :
    (locWrite js next w D y).flags = js.flags ∧ (locWrite js next w D y).df = js.df := by
  cases D <;> simp [locWrite, memWrite, regWrite, State.putReg, State.putHigh, State.setReg] <;>
    (try split) <;> simp

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

/-- The r/m operand: what the model reads and writes is what Janus reads and writes. `q` is the
address of the ModRM byte, `k` the number of immediate bytes after the ModRM operand. -/
theorem rm_operand {js : State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) {q m : Nat} {rest : List Nat} (hcs : CodeAt s (q + 1) rest) (hm : m < 256)
    {mm : ModRM} {r3 : List Nat} {c : Nat} (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    (hfs : ∀ k', mm.rm = .r k' → p.fs = false)
    {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {k : Nat} (hk : k < 8) (hq : q + c + k < 2 ^ 47) :
    ∃ inc eaddr, q + 1 + (if sibP m then 1 else 0) + inc = q + c ∧ inc < 8 ∧
      (m / 64 ≠ 3 → (x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 (q + 1 + (if sibP m then 1 else 0))) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8)
        (BitVec.ofNat 3 k)).run s = .ok (eaddr, (inc : Int)) s) ∧
      (m / 64 = 3 → inc = 0 ∧ eaddr = 0#64) ∧
      (∀ iac mp wr, locOK js (BitVec.ofNat 64 (q + c + k)) w (rmDst p w mm.rm) wr → ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
        (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) iac mp sg x
          (BitVec.ofNat 48 (q + 1 + (if sibP m then 1 else 0))) rex (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64))
          (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8) (BitVec.ofNat 3 k)).run s =
          .ok (((locVal js (BitVec.ofNat 64 (q + c + k)) w (rmDst p w mm.rm)).setWidth 64).setWidth 128, (inc : Int), eaddr) s) ∧
      (∀ iac mp sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 → locOK js (BitVec.ofNat 64 (q + c + k)) w (rmDst p w mm.rm) true →
        ∀ js0 s0, Rel js0 s0 → X86Config s0 → js0.regs = js.regs → js0.mem = js.mem → js0.fsBase = js.fsBase →
        ∀ y : BitVec w, ∃ s1,
          (x86_operand_to_reg_mem .Mode_64bit (w / 8) iac mp ((y.setWidth 64).setWidth 128) sg eaddr x rex
            (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8)).run s0 =
            .ok () s1 ∧
          Rel (locWrite js0 (BitVec.ofNat 64 (q + c + k)) w (rmDst p w mm.rm) y) s1 ∧ X86Config s1 ∧
          s1.regs.get? .rflags = s0.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s0.regs.get? .janus_undef) := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  obtain ⟨md, rg, ext, rm⟩ := mm
  cases rm with
  | r k' =>
    obtain ⟨h3, rfl, rfl, -⟩ := modrm_r hmd
    have hsib : sibP m = false := sibP_reg m h3
    simp only [hsib, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    refine ⟨0, 0#64, rfl, by decide, fun h => absurd h3 h, fun _ => ⟨rfl, rfl⟩,
      fun iac mp wr _ sg _ _ => ?_, fun iac mp sg _ _ _ js0 s0 h0 hc0 hr0 _ _ y => ?_⟩
    · rw [h3]
      have := run_operand_from_reg h hW _ rex hrex (rmNum_lt p m) (rmNum_8 p m) _
        (by rw [hrexb]; exact hidx_rm hrv m) iac mp sg x (BitVec.ofNat 48 (q + 1)) 0#8 (BitVec.ofNat 3 k)
      rw [show rmDst p w (.r (m % 8 + 8 * (p.rex.getD 0 % 2))) = regLocOf p.rex.isSome w (rmNum p m) from rfl,
        locVal_regLocOf]
      simpa using this
    · rw [h3]
      have hn' := locReg_lt p.rex.isSome w (rmNum p m) (rmNum_lt p m)
      rw [show rmDst p w (.r (m % 8 + 8 * (p.rex.getD 0 % 2))) = regLocOf p.rex.isSome w (rmNum p m) from rfl,
        locWrite_regLocOf]
      exact ⟨_, run_operand_to_reg h0 hc0.log hW _ rex hrex (rmNum_lt p m) (rmNum_8 p m) _
        (by rw [hrexb]; exact hidx_rm hrv m) iac mp sg 0#64 x 0#8 y,
        h0.writeReg _ (rmNum_lt p m) y, hc0.setGpr hn' _, get?_setGpr_of_not s0 _ hn' rfl,
        get?_setGpr_of_not s0 _ hn' rfl⟩
  | m a =>
    obtain ⟨hc1, hc6, hmd3⟩ := modrm_c_ge hmd
    have hEA := run_x86_effective_addr h hc h.rip hp hrv hcs hm hmd (nimm := k) hk hq
    have hafs := hEA.2.1
    refine ⟨c - 1 - (if sibP m then 1 else 0), eaOff js (BitVec.ofNat 64 (q + c + k)) a, by omega,
      by omega, fun _ => hEA.1, fun h => absurd h hmd3, fun iac mp wr hacc sg hsg4 hsg5 => ?_, fun iac mp sg hsg4 hsg5 hacc js0 s0 h0 hc0 hr0 hm0 hf0 y => ?_⟩
    · have := run_operand_from_mem h hc hp hrv hcs hm hmd (nimm := k) hk hq hW hsg4 hsg5 iac mp (wr := wr) hacc
      simpa [rmDst, locVal] using this
    · simp only [rmDst, locOK] at hacc
      have hacc0 : js0.mem.accessible (ea js0 (BitVec.ofNat 64 (q + c + k)) (if p.fs then { a with fs := true } else a)).toNat
          (w / 8) true = true := by rw [ea_congr hr0 hf0, hm0]; exact hacc
      obtain ⟨s1, h1, h2, h3, h4⟩ := run_operand_to_mem h0 hc0 hp hW hsg4 hsg5 iac mp a hafs (BitVec.ofNat 64 (q + c + k)) (BitVec.ofNat 3 (m % 8))
        (md := BitVec.ofNat 2 (m / 64)) (by rw [beq2_3 _ (by omega)]; simpa using hmd3) _ y hacc0
      rw [eaOff_congr hr0] at h1
      exact ⟨s1, h1, h2, h3, by rw [h4], by rw [h4]⟩

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

set_option maxHeartbeats 1000000 in
/-- The frame of a one-byte instruction with a ModRM operand (and `k` immediate bytes after it). -/
theorem rm_frame {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (hpg : prefixGroup o = 0) (ho4 : o / 16 ≠ 4) (hvex : o ≠ 0xC4 ∧ o ≠ 0xC5 ∧ o ≠ 0x62) (hmp : modrmP1 o = true)
    (hlk : p.lock = false)
    {mm : ModRM} {r3 : List Nat} {c : Nat} (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    (hfs : ∀ k', mm.rm = .r k' → p.fs = false)
    {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {k : Nat} (hk : k < 8) (hlen : n + 1 + c + k ≤ 15)
    (arm : BitVec 48 → BitVec 48 → BitVec 52 → BitVec 8 → BitVec 8 → SailM Unit)
    (hdisp : ∀ x rex, PfxRel p x rex → _get_prefixes_lck x = 0#8 → ∀ sr tr sib,
      (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib).run s =
        (arm sr tr x rex sib).run s)
    (hsem : ∀ x rex, PfxRel p x rex → (∀ r, p.rex = some r → r < 16) → ∀ (sib : BitVec 8) (tr inc : Nat) (eaddr : BitVec 64),
      tr + inc = js.rip.toNat + n + 1 + c → inc < 8 → CodeAt s (js.rip.toNat + n + 1 + c) r3 →
      (∀ iac mp wr, locOK js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + k)) w (rmDst p w mm.rm) wr →
        ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
        (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) iac mp sg x (BitVec.ofNat 48 tr) rex
          (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 k)).run s =
          .ok (((locVal js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + k)) w (rmDst p w mm.rm)).setWidth 64).setWidth 128,
            (inc : Int), eaddr) s) →
      (∀ iac mp sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
        locOK js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + k)) w (rmDst p w mm.rm) true →
        ∀ js0 s0, Rel js0 s0 → X86Config s0 → js0.regs = js.regs → js0.mem = js.mem → js0.fsBase = js.fsBase →
        ∀ y : BitVec w, ∃ s1,
          (x86_operand_to_reg_mem .Mode_64bit (w / 8) iac mp ((y.setWidth 64).setWidth 128) sg eaddr x rex
            (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run s0 = .ok () s1 ∧
          Rel (locWrite js0 (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + k)) w (rmDst p w mm.rm) y) s1 ∧ X86Config s1 ∧
          s1.regs.get? .rflags = s0.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s0.regs.get? .janus_undef) →
      (m / 64 ≠ 3 → (x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 tr) rex (BitVec.ofNat 3 (m % 8))
        (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 k)).run s = .ok (eaddr, (inc : Int)) s) →
      (m / 64 = 3 → inc = 0 ∧ eaddr = 0#64) →
      ∃ s', (arm (BitVec.ofNat 48 js.rip.toNat) (BitVec.ofNat 48 tr) x rex sib).run s = .ok () s' ∧
        Rel js' s' ∧ X86Config s') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
  have hm256 : m < 256 := hcode.1 m (by
    have : m ∈ bytes.drop n := by rw [hdrop]; simp
    exact List.mem_of_mem_drop this)
  have hrv : ∀ r, p.rex = some r → r < 16 := parsePrefixes_rexv _ _ _ (by simp) hpp
  have hrip : s.regs.get? .rip = some (BitVec.ofNat 64 js.rip.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hrel.rip
  have hcs : CodeAt s (js.rip.toNat + n + 1 + 1) rest := by
    have h2 : (bytes.drop n).drop 2 = rest := by rw [hdrop]; rfl
    have := hcode.drop (n + 2); rw [show bytes.drop (n + 2) = rest by simpa [List.drop_drop, Nat.add_comm] using h2] at this
    rwa [show js.rip.toNat + (n + 2) = js.rip.toNat + n + 1 + 1 by omega] at this
  have hmdc := modrm_drop hmd
  have hc1 : 1 ≤ c := by
    obtain ⟨md, rg, ext, rm⟩ := mm
    cases rm with
    | r _ => obtain ⟨-, -, rfl, -⟩ := modrm_r hmd; omega
    | m _ => exact Nat.le_trans (by omega) (modrm_c_ge hmd).1
  have hcs3 : CodeAt s (js.rip.toNat + n + 1 + c) r3 := by
    rw [hmdc]; have := hcs.drop (c - 1)
    rwa [show js.rip.toNat + n + 1 + 1 + (c - 1) = js.rip.toNat + n + 1 + c by omega] at this
  have hm4 : modrmSib (modrmP1 o) (m :: rest) = (BitVec.ofNat 8 m, (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8),
      1 + (if sibP m then 1 else 0)) := by rw [hmp, modrmSib_eq]
  have hsl : (1 + (if sibP m then 1 else 0)) ≤ (m :: rest).length := by
    cases rest with
    | cons _ _ => simp; split <;> omega
    | nil =>
      cases hs : sibP m
      · simp
      · exfalso
        unfold sibP at hs; simp at hs
        unfold modrm at hmd; simp [hs.1, hs.2] at hmd
  obtain ⟨x, rex, hpr, hnx, hf⟩ := run_fetch_one hcfg hrip hcode hpp (by omega) hlim hpg ho4 hvex
    (by rw [hm4]; simp at hsl ⊢; omega)
  rw [hm4] at hf
  simp only at hf
  have hl0 : _get_prefixes_lck x = 0#8 := by have := hpr.lck; rw [hlk] at this; simpa using this
  rw [hdisp x rex hpr hl0] at hf
  obtain ⟨inc, eaddr, hinc, hinc8, hEA, hR3, hX, hWr⟩ := rm_operand hrel hcfg hpr hrv (q := js.rip.toNat + n + 1) hcs hm256 hmd hfs hW
    hk (by omega)
  rw [show js.rip.toNat + n + 1 + (1 + (if sibP m then 1 else 0)) = js.rip.toNat + n + 1 + 1 + (if sibP m then 1 else 0)
    by omega] at hf
  obtain ⟨s', hs', hr', hc'⟩ := hsem x rex hpr hrv (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8)
    (js.rip.toNat + n + 1 + 1 + (if sibP m then 1 else 0)) inc eaddr (by omega) hinc8 hcs3 hX hWr hEA hR3
  exact ⟨s', run_janus_x86_step (by rw [hf, hs']), hr', hc'⟩

end JanusX86.Proofs
