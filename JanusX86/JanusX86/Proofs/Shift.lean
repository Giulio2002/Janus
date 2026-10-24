import JanusX86.Proofs.ShiftWidth

/-! # Shifts and rotates (`C0/C1/D0–D3 /0,1,4,5,7`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

theorem tr_sw {w : Nat} (x : BitVec w) (k : Nat) (hk : w ≤ 64) (hkw : k = w) :
    Sail.BitVec.truncate (x.setWidth 64) k = BitVec.cast hkw.symm x := by
  subst hkw; apply BitVec.eq_of_toNat_eq
  have h1 := x.isLt
  have h2 : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
  simp only [Sail.BitVec.truncate, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_cast]
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt h1]

theorem run_shl_spec {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (x : BitVec w) (c : Nat) (hc : c < 64)
    (hcw : c < (if w = 64 then 64 else 32)) (rin : BitVec 32) (s : SState)
    (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, (sal_shl_spec (w / 8) (x.setWidth 64) (BitVec.ofNat 6 c) rin).run s =
      .ok ((shVal .shl x c).setWidth 64, out, und) s ∧ FlagsRel (shFl .shl x c f) df (wurf rin out und u) := by
  have hfl : shFl .shl x c f = (shRes .shl x c f).2 := by simp [shFl]
  rw [hfl]
  rcases hW with rfl | rfl | rfl | rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shl8 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [sal_shl_spec, Nat.reduceDiv, run_bind, tr_sw x 8 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shl16 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [sal_shl_spec, Nat.reduceDiv, run_bind, tr_sw x 16 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shl32 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [sal_shl_spec, Nat.reduceDiv, run_bind, tr_sw x 32 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shl64 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [sal_shl_spec, Nat.reduceDiv, BitVec.setWidth_eq, h1]

theorem run_shr_spec {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (x : BitVec w) (c : Nat) (hc : c < 64)
    (hcw : c < (if w = 64 then 64 else 32)) (rin : BitVec 32) (s : SState)
    (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, (shr_spec (w / 8) (x.setWidth 64) (BitVec.ofNat 6 c) rin).run s =
      .ok ((shVal .shr x c).setWidth 64, out, und) s ∧ FlagsRel (shFl .shr x c f) df (wurf rin out und u) := by
  have hfl : shFl .shr x c f = (shRes .shr x c f).2 := by simp [shFl]
  rw [hfl]
  rcases hW with rfl | rfl | rfl | rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shr8 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [shr_spec, Nat.reduceDiv, run_bind, tr_sw x 8 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shr16 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [shr_spec, Nat.reduceDiv, run_bind, tr_sw x 16 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shr32 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [shr_spec, Nat.reduceDiv, run_bind, tr_sw x 32 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shr64 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [shr_spec, Nat.reduceDiv, BitVec.setWidth_eq, h1]

theorem run_sar_spec {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (x : BitVec w) (c : Nat) (hc : c < 64)
    (hcw : c < (if w = 64 then 64 else 32)) (rin : BitVec 32) (s : SState)
    (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, (sar_spec (w / 8) (x.setWidth 64) (BitVec.ofNat 6 c) rin).run s =
      .ok ((shVal .sar x c).setWidth 64, out, und) s ∧ FlagsRel (shFl .sar x c f) df (wurf rin out und u) := by
  have hfl : shFl .sar x c f = (shRes .sar x c f).2 := by simp [shFl]
  rw [hfl]
  rcases hW with rfl | rfl | rfl | rfl
  · obtain ⟨out, und, h1, h2⟩ := run_sar8 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [sar_spec, Nat.reduceDiv, run_bind, tr_sw x 8 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_sar16 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [sar_spec, Nat.reduceDiv, run_bind, tr_sw x 16 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_sar32 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [sar_spec, Nat.reduceDiv, run_bind, tr_sw x 32 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_sar64 x c hc (by simpa using hcw) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [sar_spec, Nat.reduceDiv, BitVec.setWidth_eq, h1]

theorem run_rol_spec {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (x : BitVec w) (c : Nat) (hc : c < 64)
    (hcw : c < (if w = 64 then 64 else 32)) (hd3 : c < w) (rin : BitVec 32) (s : SState)
    (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, (rol_spec (w / 8) (x.setWidth 64) (BitVec.ofNat 6 c) rin).run s =
      .ok ((shVal .rol x c).setWidth 64, out, und) s ∧ FlagsRel (shFl .rol x c f) df (wurf rin out und u) := by
  have hfl : shFl .rol x c f = (shRes .rol x c f).2 := by simp [shFl]
  rw [hfl]
  rcases hW with rfl | rfl | rfl | rfl
  · obtain ⟨out, und, h1, h2⟩ := run_rol8 x c hc (by simpa using hd3) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [rol_spec, Nat.reduceDiv, run_bind, tr_sw x 8 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_rol16 x c hc (by simpa using hd3) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [rol_spec, Nat.reduceDiv, run_bind, tr_sw x 16 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_rol32 x c hc (by simpa using hd3) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [rol_spec, Nat.reduceDiv, run_bind, tr_sw x 32 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_rol64 x c hc (by simpa using hd3) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [rol_spec, Nat.reduceDiv, BitVec.setWidth_eq, h1]

theorem run_ror_spec {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (x : BitVec w) (c : Nat) (hc : c < 64)
    (hcw : c < (if w = 64 then 64 else 32)) (hd3 : c < w) (rin : BitVec 32) (s : SState)
    (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, (ror_spec (w / 8) (x.setWidth 64) (BitVec.ofNat 6 c) rin).run s =
      .ok ((shVal .ror x c).setWidth 64, out, und) s ∧ FlagsRel (shFl .ror x c f) df (wurf rin out und u) := by
  rcases hW with rfl | rfl | rfl | rfl
  · obtain ⟨out, und, h1, h2⟩ := run_ror8 x c hc (by simpa using hd3) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [ror_spec, Nat.reduceDiv, run_bind, tr_sw x 8 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_ror16 x c hc (by simpa using hd3) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [ror_spec, Nat.reduceDiv, run_bind, tr_sw x 16 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_ror32 x c hc (by simpa using hd3) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [ror_spec, Nat.reduceDiv, run_bind, tr_sw x 32 (by decide) rfl, BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_ror64 x c hc (by simpa using hd3) rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [ror_spec, Nat.reduceDiv, BitVec.setWidth_eq, h1]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

theorem execShift_any {js js' : State} {next : BitVec 64} {op : ShOp} {w : Nat} {D : Loc} {cnt : Src}
    (h : execShift js next op w D cnt = .ok js') :
    ∃ cv : BitVec 8, readSrc js next 8 cnt = .ok cv ∧ locOK js next w D true ∧
      js' = ((locWrite js next w D (shVal op (locVal js next w D) (cv.toNat % (if w = 64 then 64 else 32)))).setFlags
        (shRes op (locVal js next w D) (cv.toNat % (if w = 64 then 64 else 32)) js.flags).2).setRip next := by
  unfold execShift at h
  cases hc : readSrc js next 8 cnt with
  | error e => simp [hc] at h
  | ok cv =>
  cases hr : readLocRW js next w D with
  | error e => simp [hc, hr] at h
  | ok X =>
  obtain ⟨hok, rfl⟩ := readLocRW_loc hr
  refine ⟨cv, rfl, hok, ?_⟩
  simp only [hc, hr, writeLoc_loc hok] at h
  generalize cv.toNat % (if w = 64 then 64 else 32) = c at h ⊢
  by_cases h0 : c = 0
  · subst h0
    simp only [↓reduceIte, Except.ok.injEq] at h
    cases op <;> simp only at h <;> rw [← h] <;> simp [shRes, shVal]
  · simp only [h0, ↓reduceIte] at h
    cases op <;> simp only [Except.ok.injEq] at h <;> rw [← h] <;> simp [shRes, shVal, h0]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

/-- The count operand of `C0/C1` (`imm8`), `D0/D1` (`1`) and `D2/D3` (`CL`). -/
def shCnt (o v : Nat) : Src :=
  if o = 0xC0 ∨ o = 0xC1 then .imm v else if o = 0xD0 ∨ o = 0xD1 then .imm 1 else .loc (.reg 1)

/-- The immediate bytes of a shift encoding. -/
def shK (o : Nat) : Nat := if o = 0xC0 ∨ o = 0xC1 then 1 else 0

theorem decode_shift {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (ho : o = 0xC0 ∨ o = 0xC1 ∨ o = 0xD0 ∨ o = 0xD1 ∨ o = 0xD2 ∨ o = 0xD3)
    {op : ShOp} (hop : shOp (m / 8 % 8) = some op)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c)) (hlk : p.lock = false)
    {w : Nat} (hw : w = if o % 2 = 0 then 8 else osz p)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.rep = 0 ∧ p.fs = false ∧ ∃ v r4, ((o = 0xC0 ∨ o = 0xC1) → readLE 1 r3 = some (v, r4)) ∧
      len = n + 1 + c + shK o ∧ len ≤ 15 ∧ i = .shift op w (rmDst p w mm.rm) (shCnt o v) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp, hlk, Bool.false_eq_true] at hd
  have hex := modrm_ext hmd
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hex; subst hex
  have hrc : ¬ ((m / 8 % 8 = 2 ∨ m / 8 % 8 = 3)) := by
    intro h; rcases h with h | h <;> simp [h, shOp] at hop
  have ho8 : (osz p = 8) = False := by rcases osz_cases p with e | e | e <;> simp [e]
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, true_and, and_true,
      false_and, and_false, or_false, false_or, hrc, hop, ho8, shCnt, shK] at hd hw ⊢
    subst hw
  · cases hr : readLE 1 r3 with
    | none => simp [immU8, hr] at hd
    | some vr =>
      obtain ⟨v, r4⟩ := vr
      simp only [immU8, hr] at hd
      by_cases hl : 15 < n + 1 + c + 1 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases rm <;>
        simp (config := {decide := true}) [hf, hl, hrp, finish, withFS, rmDst, rmLoc, regLocOf, ho8] at hd ⊢
      all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl⟩)
  · cases hr : readLE 1 r3 with
    | none => simp [immU8, hr] at hd
    | some vr =>
      obtain ⟨v, r4⟩ := vr
      simp only [immU8, hr] at hd
      by_cases hl : 15 < n + 1 + c + 1 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases rm <;>
        simp (config := {decide := true}) [hf, hl, hrp, finish, withFS, rmDst, rmLoc, regLocOf, ho8] at hd ⊢
      all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl⟩)
  all_goals
    by_cases hl : 15 < n + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases rm <;>
      simp (config := {decide := true}) [hf, hl, hrp, finish, withFS, rmDst, rmLoc, regLocOf, ho8] at hd ⊢
  all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl⟩)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_shift (opc : Nat) (hopc : opc = 0xC0 ∨ opc = 0xC1 ∨ opc = 0xD0 ∨ opc = 0xD1 ∨ opc = 0xD2 ∨ opc = 0xD3)
    (e : Nat) (he : e = 0 ∨ e = 1 ∨ e = 4 ∨ e = 5 ∨ e = 7)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hm : _get_modr_m_reg m = BitVec.ofNat 3 e) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_sal_sar_shl_shr_rcl_rcr_rol_ror .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
  rcases hopc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
      ↓reduceIte, Bool.false_eq_true, hl, hm, Bool.and_false, run_bind, run_pure,
      show (240#8 == 0#8) = false from rfl] <;> rfl

theorem modrmP1_sh : ∀ o, (o = 0xC0 ∨ o = 0xC1 ∨ o = 0xD0 ∨ o = 0xD1 ∨ o = 0xD2 ∨ o = 0xD3) → modrmP1 o = true := by
  intro o h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem cmask_all : ∀ (y : BitVec 8) (b : Bool),
    Sail.BitVec.truncate (bits_of_int (if b then (63 : Int) else 31) 128 &&& Sail.BitVec.zeroExtend y 128) 6 =
      BitVec.ofNat 6 (y.toNat % (if b then 64 else 32)) := by
  decide +kernel

theorem cmask31 : ∀ (y : BitVec 8),
    Sail.BitVec.truncate (bits_of_int (31 : Int) 128 &&& Sail.BitVec.zeroExtend y 128) 6 = BitVec.ofNat 6 (y.toNat % 32) := by
  decide +kernel

theorem cmask_one : ∀ (b : Bool),
    Sail.BitVec.truncate (bits_of_int (if b then (63 : Int) else 31) 128 &&& 0x00000000000000000000000000000001#128) 6 =
      BitVec.ofNat 6 ((1#8 : BitVec 8).toNat % (if b then 64 else 32)) := by
  decide +kernel

theorem shres_trunc {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (Y : BitVec w) :
    sail_mask 64 (trunc (w / 8) (Y.setWidth 64)) = Y.setWidth 64 := by
  rcases hW with rfl | rfl | rfl | rfl <;>
  apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
  simp [sail_mask, trunc, Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Sail.BitVec.length, BitVec.getLsbD_setWidth] <;>
  omega

/-- The count byte of a shift encoding, as the model reads it. -/
def shCntOK (s : SState) (js : Janus.Amd64.State) (opc te : Nat) (cv : BitVec 8) : Prop :=
  (opc = 0xC0 ∨ opc = 0xC1 → ∃ ds r, CodeAt s te ds ∧ Janus.Amd64.Decode.readLE 1 ds = some (cv.toNat, r)) ∧
  (opc = 0xD0 ∨ opc = 0xD1 → cv = 1#8) ∧
  (opc = 0xD2 ∨ opc = 0xD3 → cv = (js.regs 1).setWidth 8)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The model's shift/rotate arm, any r/m operand (abstract read `hX` and write `hWr`). -/
theorem run_shift {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0xC0 ∨ opc = 0xC1 ∨ opc = 0xD0 ∨ opc = 0xD1 ∨ opc = 0xD2 ∨ opc = 0xD3)
    {w : Nat} (hw : w = if opc % 2 = 0 then 8 else osz p)
    (m : Nat) (hm : m < 256) {op : Janus.Amd64.ShOp} (hop : Janus.Amd64.Decode.shOp (m / 8 % 8) = some op)
    (sib : BitVec 8) (tr te : Nat)
    (V : BitVec w) (inc : Nat) (eaddr : BitVec 64) (NX : BitVec 64) (D : Janus.Amd64.Loc)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 (shK opc))).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hWr : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      ∀ js0 s0, Rel js0 s0 → X86Config s0 → js0.regs = js.regs → js0.mem = js.mem → js0.fsBase = js.fsBase →
      ∀ y : BitVec w, ∃ s1,
        (x86_operand_to_reg_mem .Mode_64bit (w / 8) true false ((y.setWidth 64).setWidth 128) sg eaddr x rex
          (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run s0 = .ok () s1 ∧
        Rel (locWrite js0 NX w D y) s1 ∧ X86Config s1 ∧
        s1.regs.get? .rflags = s0.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s0.regs.get? .janus_undef)
    (hte : te = tr + inc) (hinc : inc < 8) (cv : BitVec 8) (hcv : shCntOK s js opc te cv)
    (hd3 : (op = .rol ∨ op = .ror) → cv.toNat % (if w = 64 then 64 else 32) < w)
    (sr : Nat) (hl1 : sr ≤ te + shK opc) (hl2 : te + shK opc ≤ sr + 15) (htr : te + shK opc < 2 ^ 47) :
    ∃ s', (x86_sal_sar_shl_shr_rcl_rcr_rol_ror .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex
      (BitVec.ofNat 8 opc) (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (((locWrite js NX w D (shVal op V (cv.toNat % (if w = 64 then 64 else 32)))).setFlags
        (shFl op V (cv.toNat % (if w = 64 then 64 else 32)) js.flags)).setRip (BitVec.ofNat 64 (te + shK opc))) s' ∧
      X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hlb : logbitp_bits 3 rex = rexW p := by rw [hrexb]; exact logbitp3_rexByte hrv
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (te + shK opc) hl1 hl2 htr
  have hl := hc.log
  have hrip := h.rip
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  have hinc' : (bits_of_int (inc : Int) 3) = BitVec.ofNat 3 inc := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have hadd : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48)).run s =
      .ok (BitVec.ofNat 48 te) s := by
    have ez : (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48).toNat = inc := by
      simp [Sail.BitVec.zeroExtend]; omega
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hadd1 : opc = 0xC0 ∨ opc = 0xC1 → (add_to_iptr .Mode_64bit (BitVec.ofNat 48 te) 0x000000000001#48).run s =
      .ok (BitVec.ofNat 48 (te + 1)) s := by
    intro hc1
    have : te + 1 < 2 ^ 47 := by rcases hc1 with h | h <;> subst h <;> simp [shK] at htr <;> omega
    rw [run_add_to_iptr _ _ (by simp; omega)]
    congr 2; simp; omega
  have hb : (BitVec.ofNat 8 opc == 0xC0#8 || (BitVec.ofNat 8 opc == 0xD0#8 || BitVec.ofNat 8 opc == 0xD2#8)) =
      decide (opc % 2 = 0) := by rcases hopc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hsz := size_int p (decide (opc % 2 = 0))
  have hw' : (if decide (opc % 2 = 0) = true then 8 else osz p) = w := by rw [hw]; simp
  have hk3 : (if (BitVec.ofNat 8 opc == 0xC0#8 || BitVec.ofNat 8 opc == 0xC1#8) = true then 0b001#3 else 0b000#3) =
      BitVec.ofNat 3 (shK opc) := by rcases hopc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hmask : (if (rexW p && !decide (opc % 2 = 0)) = true then 64 else 32) = (if w = 64 then 64 else 32) := by
    rw [hw]; unfold osz
    rcases hopc with rfl | rfl | rfl | rfl | rfl | rfl <;> cases rexW p <;> cases p.opsize <;> simp
  generalize hM : (if w = 64 then 64 else 32) = M at hd3 hmask ⊢
  have hMp : M = 32 ∨ M = 64 := by rw [← hM]; split <;> simp
  have hc64 : cv.toNat % M < 64 := by rcases hMp with e | e <;> rw [e] <;> omega
  have hcw : cv.toNat % M < (if w = 64 then 64 else 32) := by rw [hM]; rcases hMp with e | e <;> rw [e] <;> omega
  have hext : (m / 8 % 8 = 0 ∧ op = .rol) ∨ (m / 8 % 8 = 1 ∧ op = .ror) ∨ (m / 8 % 8 = 4 ∧ op = .shl) ∨
      (m / 8 % 8 = 5 ∧ op = .shr) ∨ (m / 8 % 8 = 7 ∧ op = .sar) := by
    revert hop; unfold Janus.Amd64.Decode.shOp
    split
    · intro h; cases h; simp_all
    split
    · intro h; cases h; simp_all
    split
    · intro h; cases h; simp_all
    split
    · intro h; cases h; simp_all
    split
    · intro h; cases h; simp_all
    · intro h; cases h
  have hwr := run_write_user_rflags hr hu hl
  have htrunc := shres_trunc hW
  have hset : ∀ (F : Janus.Amd64.Flags) (out und : BitVec 32), FlagsRel F js.df (wurf rf out und u) →
      ∃ s1, (x86_operand_to_reg_mem .Mode_64bit (w / 8) true false
        ((((shVal op V (cv.toNat % M)).setWidth 64).setWidth 128)) sg eaddr x rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run (s.set .rflags (wurf rf out und u)) = .ok () s1 ∧
        Rel ((locWrite js NX w D (shVal op V (cv.toNat % M))).setFlags F) s1 ∧ X86Config s1 := by
    intro F out und hF
    obtain ⟨s1, hs1, hrel1, hcfg1, -, -⟩ := hWr sg hsg4 hsg5 _ _ (h.setFlagsR F _ hF) (hc.set (by decide) _) rfl rfl rfl
      (shVal op V (cv.toNat % M))
    refine ⟨s1, hs1, ?_, hcfg1⟩
    rwa [locWrite_setFlags] at hrel1
  have eqb3 : ∀ a < 8, ∀ k < 8, (Sail.BitVec.toNatInt (BitVec.ofNat 3 a) == ((k : Nat) : Int)) = decide (a = k) := by
    decide +kernel
  simp only [x86_sal_sar_shl_shr_rcl_rcr_rol_ror, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hb, hsz, hw',
    hsg, Int.toNat_natCast, hk3, hX sg hsg4 hsg5, hinc', hadd, run_pure, hlb]
  have h1c : opc = 0xD0 ∨ opc = 0xD1 → (0x00000000000000000000000000000001#128 : BitVec 128) = Sail.BitVec.zeroExtend cv 128 := by
    intro ho; rw [hcv.2.1 ho]; decide
  have hrr : opc = 0xD2 ∨ opc = 0xD3 → (rr08 1#4 rex).run s = .ok cv s := by
    intro ho; rw [hcv.2.2 ho]
    exact run_rr08_low (n := 1) (by decide) (h.gpr 1 (by decide)) rex (by simp [low8])
  have hld : opc = 0xC0 ∨ opc = 0xC1 → (rme_size .Mode_64bit 8 1 (Sail.BitVec.signExtend (BitVec.ofNat 48 te) 64) none 1 ":X"
      false false).run s = .ok (Sail.BitVec.zeroExtend cv 128) s := by
    intro ho
    obtain ⟨ds, r, hds, hle⟩ := hcv.1 ho
    have : te + 1 ≤ 2 ^ 47 := by rcases ho with h | h <;> subst h <;> simp [shK] at htr <;> omega
    simp only [rme_size, run_bind, run_load_code hc hrip 8 hds (by decide) hle this, run_pure]
    congr 2; simp
  rcases hopc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [eq_bits_nat, ↓reduceIte, Bool.false_eq_true, run_bind, run_pure,
      hsel, show (8 : Int).toNat = 8 from rfl, shK]
  all_goals (try simp only [hld (Or.inl rfl), hadd1 (Or.inl rfl), run_bind, run_pure])
  all_goals (try simp only [hld (Or.inr rfl), hadd1 (Or.inr rfl), run_bind, run_pure])
  all_goals (try simp only [hrr (Or.inl rfl), run_bind, run_pure])
  all_goals (try simp only [hrr (Or.inr rfl), run_bind, run_pure])
  all_goals (try simp only [h1c (Or.inl rfl)])
  all_goals (try simp only [h1c (Or.inr rfl)])
  all_goals simp (config := {decide := true}) only [shK, ↓reduceIte, Nat.add_zero, Bool.not_true, Bool.not_false,
    Bool.and_false, Bool.and_true, decide_true, decide_false] at hlen htr hl1 hl2 hmask
  all_goals simp only [decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true]
  all_goals simp only [tsx48, hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_pure, run_readReg hr, trunc128,
    cmask_all, cmask31, run_bind]
  all_goals first
    | (rw [show cv.toNat % 32 = cv.toNat % M by rw [hmask]])
    | (rw [show cv.toNat % 32 = cv.toNat % M by rw [← hmask]])
    | simp only [hmask]
    | skip
  all_goals rcases hext with ⟨he, rfl⟩ | ⟨he, rfl⟩ | ⟨he, rfl⟩ | ⟨he, rfl⟩ | ⟨he, rfl⟩
  all_goals simp only [he]
  all_goals simp (config := {decide := true}) only [Sail.BitVec.toNatInt, ↓reduceIte, Bool.false_eq_true]
  all_goals first
    | (obtain ⟨out, und, hs, hF⟩ := run_rol_spec hW V _ hc64 hcw (hd3 (Or.inl rfl)) rf s js.flags js.df u hfr; simp only [hs, hwr, htrunc, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]; obtain ⟨s1, hs1, hrel1, hcfg1⟩ := hset _ out und hF; simp only [hs1]; exact ⟨_, run_write_iptr hcfg1.log _ (by omega), hrel1.setRipR _, hcfg1.set (by decide) _⟩)
    | (obtain ⟨out, und, hs, hF⟩ := run_ror_spec hW V _ hc64 hcw (hd3 (Or.inr rfl)) rf s js.flags js.df u hfr; simp only [hs, hwr, htrunc, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]; obtain ⟨s1, hs1, hrel1, hcfg1⟩ := hset _ out und hF; simp only [hs1]; exact ⟨_, run_write_iptr hcfg1.log _ (by omega), hrel1.setRipR _, hcfg1.set (by decide) _⟩)
    | (obtain ⟨out, und, hs, hF⟩ := run_shl_spec hW V _ hc64 hcw rf s js.flags js.df u hfr; simp only [hs, hwr, htrunc, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]; obtain ⟨s1, hs1, hrel1, hcfg1⟩ := hset _ out und hF; simp only [hs1]; exact ⟨_, run_write_iptr hcfg1.log _ (by omega), hrel1.setRipR _, hcfg1.set (by decide) _⟩)
    | (obtain ⟨out, und, hs, hF⟩ := run_shr_spec hW V _ hc64 hcw rf s js.flags js.df u hfr; simp only [hs, hwr, htrunc, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]; obtain ⟨s1, hs1, hrel1, hcfg1⟩ := hset _ out und hF; simp only [hs1]; exact ⟨_, run_write_iptr hcfg1.log _ (by omega), hrel1.setRipR _, hcfg1.set (by decide) _⟩)
    | (obtain ⟨out, und, hs, hF⟩ := run_sar_spec hW V _ hc64 hcw rf s js.flags js.df u hfr; simp only [hs, hwr, htrunc, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]; obtain ⟨s1, hs1, hrel1, hcfg1⟩ := hset _ out und hF; simp only [hs1]; exact ⟨_, run_write_iptr hcfg1.log _ (by omega), hrel1.setRipR _, hcfg1.set (by decide) _⟩) 
end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

/-- Sail-x86 defect D3 excluded: a decoded 8/16-bit rotate has a masked count below the width. -/
def shiftNoD3 (bytes : List Nat) (js : State) : Prop :=
  ∀ op w D cnt len next cv, decode bytes = some (.shift op w D cnt, len) → readSrc js next 8 cnt = .ok cv →
    (op = .rol ∨ op = .ror) → cv.toNat % (if w = 64 then 64 else 32) < w

/-- Sail-x86 defect D6 excluded: a decoded `ROR` has a masked count of 0 or 1. -/
def shiftNoD6 (bytes : List Nat) (js : State) : Prop :=
  ∀ w D cnt len next cv, decode bytes = some (.shift .ror w D cnt, len) → readSrc js next 8 cnt = .ok cv →
    cv.toNat % (if w = 64 then 64 else 32) < 2

set_option maxHeartbeats 4000000 in
theorem shift_core {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (ho : o = 0xC0 ∨ o = 0xC1 ∨ o = 0xD0 ∨ o = 0xD1 ∨ o = 0xD2 ∨ o = 0xD3)
    {op : ShOp} (hop : shOp (m / 8 % 8) = some op) (hlk : p.lock = false) (hd3 : shiftNoD3 bytes js)
    (hstep : step bytes js = .ok js') :
    ∃ w D cnt len NX cv V, decode bytes = some (.shift op w D cnt, len) ∧ readSrc js NX 8 cnt = .ok cv ∧
      js' = ((locWrite js NX w D (shVal op V (cv.toNat % (if w = 64 then 64 else 32)))).setFlags
        (shRes op V (cv.toNat % (if w = 64 then 64 else 32)) js.flags).2).setRip NX ∧
      ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ X86Config s' ∧
        Rel (((locWrite js NX w D (shVal op V (cv.toNat % (if w = 64 then 64 else 32)))).setFlags
          (shFl op V (cv.toNat % (if w = 64 then 64 else 32)) js.flags)).setRip NX) s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  cases hmd : modrm (p.rex.getD 0) (m :: rest) with
  | none =>
    exfalso
    obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
    simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  generalize hw : (if o % 2 = 0 then 8 else osz p) = w
  obtain ⟨hrep, hfs, v, r4, hr4, rfl, hlen, rfl⟩ := decode_shift hpp ho hop hmd hlk hw.symm hd
  rw [step_of_decode hd] at hstep
  simp only [exec] at hstep
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [← hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hk8 : shK o < 8 := by unfold shK; split <;> omega
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c + shK o)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + shK o) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  rw [hnext] at hstep
  obtain ⟨cv, hcv, hok, rfl⟩ := execShift_any hstep
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hfld := (modrm_fields m hm256).2.1
  have he : m / 8 % 8 = 0 ∨ m / 8 % 8 = 1 ∨ m / 8 % 8 = 4 ∨ m / 8 % 8 = 5 ∨ m / 8 % 8 = 7 := by
    revert hop; unfold shOp; split
    · intro _; omega
    split
    · intro _; omega
    split
    · intro _; omega
    split
    · intro _; omega
    split
    · intro _; omega
    · intro h; cases h
  refine ⟨w, _, _, _, _, cv, _, rfl, hcv, rfl, ?_⟩
  have hd3' := hd3 op w _ _ _ _ cv hd hcv
  refine (fun h => let ⟨s', h1, h2, h3⟩ := h; ⟨s', h1, h3, h2⟩) (rm_frame hrel hcfg hcode hlim hpp
    (by unfold prefixGroup; rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by omega) (by omega)
    (modrmP1_sh o ho) hlk hmd (fun _ _ => hfs) hW (k := shK o) hk8 (by omega)
    (fun sr tr x rex sib => x86_sal_sar_shl_shr_rcl_rcr_rol_ror .Mode_64bit sr tr x rex (BitVec.ofNat 8 o)
      (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_one_byte_shift o ho (m / 8 % 8) he sr tr x hl rex _ sib hfld s) ?_)
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 hc3 hX hWr _ _ _
  have hcvok : shCntOK s js o (tr + inc) cv := by
    refine ⟨fun hoc => ?_, fun hoc => ?_, fun hoc => ?_⟩
    · have hcn : shCnt o v = .imm v := by simp [shCnt, hoc]
      rw [hcn] at hcv
      simp only [readSrc, Except.ok.injEq] at hcv
      have hv : v < 256 := by
        obtain ⟨-, hvv, -⟩ := readLE_sumLE _ _ (hr4 hoc)
        rw [hvv, show 256 = 256 ^ 1 from rfl]
        exact sumLE_lt _ (fun j => by
          by_cases hj : j < r3.length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hc3.1 _ (List.getElem_mem _)
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
      refine ⟨r3, r4, by rw [hinc']; exact hc3, ?_⟩
      rw [← hcv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; exact hr4 hoc
    · have hcn : shCnt o v = .imm 1 := by
        unfold shCnt; rw [if_neg (by omega), if_pos hoc]
      rw [hcn] at hcv
      simp only [readSrc, Except.ok.injEq] at hcv
      rw [← hcv]
    · have hcn : shCnt o v = .loc (.reg 1) := by
        unfold shCnt; rw [if_neg (by omega), if_neg (by omega)]
      rw [hcn] at hcv
      simp only [readSrc, readLoc, State.getReg, Except.ok.injEq] at hcv
      exact hcv.symm
  obtain ⟨s', hs', hrel', hc'⟩ := run_shift hrel hcfg hpr hrv o ho hw.symm m hm256 hop sib tr (tr + inc)
    (locVal js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + shK o)) w (rmDst p w mm.rm)) inc eaddr _ _
    (hX true false true hok) (fun sg h4 h5 => hWr true false sg h4 h5 hok) rfl hinc8 cv hcvok hd3'
    js.rip.toNat (by omega) (by omega) (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  rwa [hinc'] at hrel'

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

/-- Forgetting Janus' `CF` weakens the relation. -/
theorem Rel.forgetCF {js : State} {s : SState} (h : Rel js s) : Rel (js.setFlags { js.flags with cf := none }) s := by
  obtain ⟨r, hr, hf⟩ := h.flags
  refine ⟨h.gpr, h.rip, ⟨r, hr, ?_⟩, h.fs, h.mem, h.canon⟩
  exact ⟨(fun v hv => by cases hv), hf.pf, hf.af, hf.zf, hf.sf, hf.ovf, hf.df, hf.ac⟩

theorem setRip_setFlags (J : State) (F G : Flags) (v : BitVec 64) :
    ((J.setFlags F).setRip v).setFlags G = (J.setFlags G).setRip v := by
  cases J; rfl

theorem shOp_some {e : Nat} (h : e = 0 ∨ e = 1 ∨ e = 4 ∨ e = 5 ∨ e = 7) : ∃ op, shOp e = some op := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **SHL/SHR/SAR/ROL/ROR r/m, imm8 / 1 / CL** (`C0/C1/D0–D3 /0,1,4,5,7`): every width, destination,
count and prefix sequence, for the counts where the model is right: no 8/16-bit rotate by a masked
count ≥ the width (Sail-x86 defect D3) and no `ROR` by a masked count ≥ 2 (defect D6, see
`shift_agree_cf` for that case). -/
theorem shift_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (ho : o = 0xC0 ∨ o = 0xC1 ∨ o = 0xD0 ∨ o = 0xD1 ∨ o = 0xD2 ∨ o = 0xD3)
    (hext : m / 8 % 8 = 0 ∨ m / 8 % 8 = 1 ∨ m / 8 % 8 = 4 ∨ m / 8 % 8 = 5 ∨ m / 8 % 8 = 7) (hlk : p.lock = false)
    (hd3 : shiftNoD3 bytes js) (hd6 : shiftNoD6 bytes js)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  obtain ⟨op, hop⟩ := shOp_some hext
  obtain ⟨w, D, cnt, len, NX, cv, V, hd, hcv, rfl, s', hs', hc', hrel'⟩ :=
    shift_core hrel hcfg hcode hlim hpp ho hop hlk hd3 hstep
  refine ⟨s', hs', ?_, hc'⟩
  have hfl : shFl op V (cv.toNat % (if w = 64 then 64 else 32)) js.flags =
      (shRes op V (cv.toNat % (if w = 64 then 64 else 32)) js.flags).2 := by
    unfold shFl; rw [if_neg]; rintro ⟨rfl, h2⟩; have := hd6 w D cnt len NX cv hd hcv; omega
  rwa [hfl] at hrel'

set_option maxHeartbeats 1000000 in
/-- **SHL/SHR/SAR/ROL/ROR** including `ROR` by a masked count ≥ 2 (Sail-x86 defect D6, where the
model takes `CF` from bit 0 of the result): the model agrees with Janus on everything but `CF`. -/
theorem shift_agree_cf {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (ho : o = 0xC0 ∨ o = 0xC1 ∨ o = 0xD0 ∨ o = 0xD1 ∨ o = 0xD2 ∨ o = 0xD3)
    (hext : m / 8 % 8 = 0 ∨ m / 8 % 8 = 1 ∨ m / 8 % 8 = 4 ∨ m / 8 % 8 = 5 ∨ m / 8 % 8 = 7) (hlk : p.lock = false)
    (hd3 : shiftNoD3 bytes js)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel (js'.setFlags { js'.flags with cf := none }) s' ∧
      X86Config s' := by
  obtain ⟨op, hop⟩ := shOp_some hext
  obtain ⟨w, D, cnt, len, NX, cv, V, hd, hcv, rfl, s', hs', hc', hrel'⟩ :=
    shift_core hrel hcfg hcode hlim hpp ho hop hlk hd3 hstep
  refine ⟨s', hs', ?_, hc'⟩
  generalize cv.toNat % (if w = 64 then 64 else 32) = c at hrel' ⊢
  by_cases hrc : op = .ror ∧ 2 ≤ c
  · rw [shFl, if_pos hrc] at hrel'
    have e : (((locWrite js NX w D (shVal op V c)).setFlags (shRes op V c js.flags).2).setRip NX).flags =
        (shRes op V c js.flags).2 := by cases (locWrite js NX w D (shVal op V c)); rfl
    rw [e, setRip_setFlags]; exact hrel'
  · rw [shFl, if_neg hrc] at hrel'
    exact hrel'.forgetCF

end JanusX86.Proofs
