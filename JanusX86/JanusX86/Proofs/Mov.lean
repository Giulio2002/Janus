import JanusX86.Proofs.Unary

/-! # MOV (`88–8B`, `C6/C7 /0`, `B0–BF`) and LEA (`8D`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

theorem writeLoc_inv {js js' : State} {next : BitVec 64} {w : Nat} {D : Loc} {y : BitVec w}
    (h : writeLoc js next w D y = .ok js') : locOK js next w D true ∧ js' = locWrite js next w D y := by
  cases D with
  | reg r => simp [writeLoc] at h; exact ⟨trivial, h.symm⟩
  | high r => simp [writeLoc] at h; exact ⟨trivial, h.symm⟩
  | mem a =>
    simp only [writeLoc] at h
    cases hs : store js.mem (ea js next a).toNat (w / 8) y.toNat with
    | error e => simp [hs] at h
    | ok m' =>
      simp only [hs, Except.ok.injEq] at h
      unfold store at hs
      split at hs
      · split at hs
        · rename_i hacc
          simp only [Except.ok.injEq] at hs; subst hs; subst h
          exact ⟨hacc, rfl⟩
        · simp at hs
      · simp at hs

/-- Janus' `MOV`: the value read, and the written state. -/
theorem exec_mov {js js' : State} {len w : Nat} {dst : Loc} {src : Src}
    (h : exec (.mov w dst src) len js = .ok js') :
    ∃ V, readSrc js (BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64)) w src = .ok V ∧
      locOK js (BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64)) w dst true ∧
      js' = (locWrite js (BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64)) w dst V).setRip
        (BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64)) := by
  simp only [exec] at h
  cases hs : readSrc js (BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64)) w src with
  | error e => simp [hs] at h
  | ok V =>
    simp only [hs] at h
    cases hw : writeLoc js (BitVec.ofNat 64 ((js.rip.toNat + len) % 2 ^ 64)) w dst V with
    | error e => simp [hw] at h
    | ok j2 =>
      simp only [hw, Except.ok.injEq] at h
      obtain ⟨hok, rfl⟩ := writeLoc_inv hw
      exact ⟨V, rfl, hok, h.symm⟩

theorem write_rgfi_trunc {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (idx : BitVec 4) (m : BitVec 64)
    (rex : BitVec 8) :
    write_rgfi_size (BitVec.ofNat 4 (w / 8)) idx m rex =
      write_rgfi_size (BitVec.ofNat 4 (w / 8)) idx ((m.setWidth w).setWidth 64) rex := by
  rcases hw with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [write_rgfi_size, eq_bits_nat, Nat.reduceDiv, ↓reduceIte, Sail.BitVec.truncate,
    sw_sw8, sw_sw16, sw_sw32, BitVec.setWidth_eq] <;> rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem withFS_mov_reg8 (w : Nat) (b : Bool) (n : Nat) (s : Src) (hs : ∀ a, s ≠ .loc (.mem a)) :
    withFS (.mov w (reg8 b n) s) = none := by
  unfold reg8; split <;> (cases s with
    | imm _ => rfl
    | loc l => cases l with
      | mem a => exact absurd rfl (hs a)
      | _ => rfl)

open Janus.Amd64 Janus.Amd64.Decode in
theorem rmLoc_r (b : Bool) (w k : Nat) : rmLoc b w (.r k) = regLocOf b w k := rfl
open Janus.Amd64 Janus.Amd64.Decode in
theorem rmLoc_m (b : Bool) (w : Nat) (a : Addr) : rmLoc b w (.m a) = .mem a := rfl
open Janus.Amd64 Janus.Amd64.Decode in
theorem regLoc_eq (b : Bool) (w n : Nat) : regLoc b w n = regLocOf b w n := rfl
open Janus.Amd64 Janus.Amd64.Decode in
theorem rmDst_r (p : Prefixes) (w k : Nat) : rmDst p w (.r k) = regLocOf p.rex.isSome w k := rfl
open Janus.Amd64 Janus.Amd64.Decode in
theorem rmDst_m (p : Prefixes) (w : Nat) (a : Addr) :
    rmDst p w (.m a) = .mem (if p.fs then { a with fs := true } else a) := rfl
open Janus.Amd64 Janus.Amd64.Decode in
theorem withFS_mov_rr (w : Nat) (b : Bool) (n n' : Nat) :
    withFS (.mov w (regLocOf b w n) (.loc (regLocOf b w n'))) = none := by
  rcases regLocOf_cases b w n with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] <;>
  rcases regLocOf_cases b w n' with ⟨r', e'⟩ | ⟨r', e'⟩ <;> rw [e'] <;> rfl
open Janus.Amd64 Janus.Amd64.Decode in
theorem withFS_mov_ri (w : Nat) (b : Bool) (n v : Nat) :
    withFS (.mov w (regLocOf b w n) (.imm v)) = none := by
  rcases regLocOf_cases b w n with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] <;> rfl
open Janus.Amd64 Janus.Amd64.Decode in
theorem withFS_mov_rm (w : Nat) (b : Bool) (n : Nat) (a : Addr) :
    withFS (.mov w (regLocOf b w n) (.loc (.mem a))) = some (.mov w (regLocOf b w n) (.loc (.mem { a with fs := true }))) := by
  rcases regLocOf_cases b w n with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] <;> rfl
open Janus.Amd64 Janus.Amd64.Decode in
theorem lockable_mov (w : Nat) (d : Loc) (s : Src) : lockable (.mov w d s) = false := rfl

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_mov {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (ho : 0x88 ≤ o ∧ o ≤ 0x8B)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {w : Nat} (hw : w = if o % 2 = 0 then 8 else osz p)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.rep = 0 ∧ len = n + 1 + c ∧ len ≤ 15 ∧
      i = (if o < 0x8A then .mov w (rmDst p w mm.rm) (.loc (regLocOf p.rex.isSome w (regNum p m)))
        else .mov w (regLocOf p.rex.isSome w (regNum p m)) (.loc (rmDst p w mm.rm))) ∧
      (∀ k', mm.rm = .r k' → p.fs = false) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hreg : mm.reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hreg; subst hreg
  have hcases : o = 0x88 ∨ o = 0x89 ∨ o = 0x8A ∨ o = 0x8B := by omega
  have ho8 : (osz p = 8) = False := by rcases osz_cases p with e | e | e <;> simp [e]
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, true_and, and_true,
      false_and, and_false, or_false, false_or, finish] at hd hw ⊢
    subst hw
    by_cases hl : 15 < n + 1 + c <;> by_cases hrp : p.rep = 0 <;>
      cases hf : p.fs <;> cases hk : p.lock <;> cases rm <;>
      simp (config := {decide := true}) only [hf, hk, hl, hrp, rmDst_r, rmDst_m, rmLoc_r, rmLoc_m, regLoc_eq,
        lockable_mov, withFS_mov_rr, withFS_mov_rm, ↓reduceIte, Bool.false_eq_true, ho8] at hd ⊢ <;>
      (try simp [withFS] at hd ⊢)
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, rfl, fun _ h => by cases h⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; simp; omega)
      | omega

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem beq8_all : ∀ a < 256, ∀ b < 256, (BitVec.ofNat 8 a == BitVec.ofNat 8 b) = decide (a = b) := by
  intro a ha b hb
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this; exact h this

theorem run_add_inc (tr inc : Nat) (hinc : inc < 8) (h : tr + inc < 2 ^ 47) (s : SState) :
    (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (Sail.BitVec.zeroExtend (bits_of_int (inc : Int) 3) 48)).run s =
      .ok (BitVec.ofNat 48 (tr + inc)) s := by
  have hinc' : (bits_of_int (inc : Int) 3) = BitVec.ofNat 3 inc := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have ez : (Sail.BitVec.zeroExtend (BitVec.ofNat 3 inc) 48).toNat = inc := by
    simp [Sail.BitVec.zeroExtend]; omega
  rw [hinc', run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
  congr 2; simp; omega

theorem size_w {p : Janus.Amd64.Decode.Prefixes} {opc : Nat} {b : Bool} (hb : b = decide (opc % 2 = 0)) {w : Nat}
    (hw : w = if opc % 2 = 0 then 8 else osz p) :
    (if b = true then (1 : Int) else if rexW p = true then 8 else if p.opsize = true then 2 else 4) =
      ((w / 8 : Nat) : Int) := by
  subst hb hw; unfold osz; by_cases h : opc % 2 = 0 <;> cases rexW p <;> cases p.opsize <;> simp [h]

set_option maxHeartbeats 2000000 in
/-- The model's `MOV r, r/m` arm (`8A/8B`), any r/m operand. -/
theorem run_mov_rm {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0x8A ∨ opc = 0x8B) {w : Nat} (hw : w = if opc % 2 = 0 then 8 else osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (V : BitVec w) (inc : Nat) (eaddr : BitVec 64)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_mov_op_en_rm .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((regWrite js w (regLocOf p.rex.isSome w (regNum p m)) V).setRip (BitVec.ofNat 64 (tr + inc))) s' ∧
      X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hb : (BitVec.ofNat 8 opc == 0x8A#8) = decide (opc % 2 = 0) := by
    rcases hopc with rfl | rfl <;> decide
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hl := hc.log
  simp only [x86_mov_op_en_rm, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hb, size_w rfl hw,
    hsg, ← bits3_zero, hX sg hsg4 hsg5, run_add_inc tr inc hinc htr, hlen, is_some, Bool.false_eq_true, ↓reduceIte,
    run_pure, trunc128, Int.toNat_natCast, nbytes_eq w hW, show reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 =
      BitVec.ofNat 4 (regNum p m) by rw [hrexb]; exact hidx_reg hrv m,
    run_write_rgfi_size h hl hW _ rex hrex (regNum_lt p m) (regNum_8 p m) V]
  have hn' := locReg_lt p.rex.isSome w (regNum p m) (regNum_lt p m)
  refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn' rfl]; exact hl) _ htr, ?_,
    (hc.setGpr hn' _).set (by decide) _⟩
  exact (h.writeReg _ (regNum_lt p m) V).setRipR _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxHeartbeats 2000000 in
/-- The model's `MOV r/m, r` arm (`88/89`), any r/m operand. -/
theorem run_mov_mr {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0x88 ∨ opc = 0x89) {w : Nat} (hw : w = if opc % 2 = 0 then 8 else osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat) (inc : Nat) (eaddr : BitVec 64)
    (NX : BitVec 64) (D : Janus.Amd64.Loc)
    (hWr : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      ∀ js0 s0, Rel js0 s0 → X86Config s0 → js0.regs = js.regs → js0.mem = js.mem → js0.fsBase = js.fsBase →
      ∀ y : BitVec w, ∃ s1,
        (x86_operand_to_reg_mem .Mode_64bit (w / 8) true false ((y.setWidth 64).setWidth 128) sg eaddr x rex
          (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run s0 = .ok () s1 ∧
        Rel (locWrite js0 NX w D y) s1 ∧ X86Config s1 ∧
        s1.regs.get? .rflags = s0.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s0.regs.get? .janus_undef)
    (hEA : m / 64 ≠ 3 → (x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 tr) rex (BitVec.ofNat 3 (m % 8))
        (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s = .ok (eaddr, (inc : Int)) s)
    (hR3 : m / 64 = 3 → inc = 0 ∧ eaddr = 0#64)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_mov_op_en_mr .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((locWrite js NX w D (regVal js w (regLocOf p.rex.isSome w (regNum p m)))).setRip
        (BitVec.ofNat 64 (tr + inc))) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hb : (BitVec.ofNat 8 opc == 0x88#8) = decide (opc % 2 = 0) := by
    rcases hopc with rfl | rfl <;> decide
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hea : (if (BitVec.ofNat 2 (m / 64) == 3#2) = true then (pure ((0x0000000000000000#64 : BitVec 64), (0 : Int)) : SailM _)
      else x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 tr) rex (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64))
        sib 0b000#3).run s = .ok (eaddr, (inc : Int)) s := by
    by_cases h3' : m / 64 = 3
    · obtain ⟨rfl, rfl⟩ := hR3 h3'
      rw [beq2_3 _ (by omega)]; simp [h3']
    · rw [beq2_3 _ (by omega)]; simp only [h3', decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [← bits3_zero]; exact hEA h3'
  simp only [x86_mov_op_en_mr, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hb, size_w rfl hw,
    nbytes_eq w hW, show reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 =
      BitVec.ofNat 4 (regNum p m) by rw [hrexb]; exact hidx_reg hrv m,
    run_rgfi_size h hW _ rex hrex (regNum_lt p m) (regNum_8 p m), hea, hsg, run_add_inc tr inc hinc htr, hlen,
    is_some, Bool.false_eq_true, ↓reduceIte, run_pure, Int.toNat_natCast]
  simp only [Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
  obtain ⟨s1, hs1, hrel1, hcfg1, -, -⟩ := hWr sg hsg4 hsg5 _ _ h hc rfl rfl rfl
    (regVal js w (regLocOf p.rex.isSome w (regNum p m)))
  rw [hs1]
  exact ⟨_, run_write_iptr hcfg1.log _ htr, hrel1.setRipR _, hcfg1.set (by decide) _⟩

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_mov (opc : Nat) (hopc : 0x88 ≤ opc ∧ opc ≤ 0x8B)
    (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (if opc < 0x8A then x86_mov_op_en_mr .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib
       else x86_mov_op_en_rm .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  have : opc = 0x88 ∨ opc = 0x89 ∨ opc = 0x8A ∨ opc = 0x8B := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

theorem modrmP1_mov : ∀ o, (0x88 ≤ o ∧ o ≤ 0x8B) → modrmP1 o = true := by
  intro o h; have : o = 0x88 ∨ o = 0x89 ∨ o = 0x8A ∨ o = 0x8B := by omega
  rcases this with rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **MOV r/m, r** and **MOV r, r/m** (`88–8B`): every ModRM form (incl. FS-relative), width and
prefix sequence Janus accepts. -/
theorem mov_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : 0x88 ≤ o ∧ o ≤ 0x8B)
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
    have : o = 0x88 ∨ o = 0x89 ∨ o = 0x8A ∨ o = 0x8B := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  generalize hw : (if o % 2 = 0 then 8 else osz p) = w
  obtain ⟨hlk, hrep, rfl, hlen, rfl, hfs⟩ := decode_mov hpp ho hmd hw.symm hd
  rw [step_of_decode hd] at hstep
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [← hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + 0) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  refine rm_frame hrel hcfg hcode hlim hpp (by unfold prefixGroup; omega) (by omega) (by omega)
    (modrmP1_mov o ho) hlk hmd hfs hW (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => if o < 0x8A then x86_mov_op_en_mr .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib
       else x86_mov_op_en_rm .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_one_byte_mov o ho sr tr x hl rex _ sib s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr hEA hR3
  by_cases hmr : o < 0x8A
  · simp only [hmr, ↓reduceIte] at hstep ⊢
    obtain ⟨V, hV, hok, rfl⟩ := exec_mov hstep
    simp only [readSrc, readLoc_regLocOf, Except.ok.injEq] at hV; subst hV
    rw [hnext] at hok ⊢
    obtain ⟨s', hs', hrel', hc'⟩ := run_mov_mr hrel hcfg hpr hrv o (by omega) hw.symm m hm256 sib tr inc eaddr _ _
      (fun sg h4 h5 => hWr true false sg h4 h5 hok) hEA hR3 hinc8 js.rip.toNat (by omega) (by omega) (by omega)
    refine ⟨s', hs', ?_, hc'⟩
    rwa [hinc'] at hrel'
  · simp only [hmr, ↓reduceIte] at hstep ⊢
    obtain ⟨V, hV, hok, rfl⟩ := exec_mov hstep
    simp only [readSrc] at hV
    rw [hnext] at hok hV ⊢
    obtain ⟨hok', rfl⟩ := readLoc_loc hV
    obtain ⟨s', hs', hrel', hc'⟩ := run_mov_rm hrel hcfg hpr hrv o (by omega) hw.symm m hm256 sib tr _ inc eaddr
      (hX true false false hok') hinc8 js.rip.toNat (by omega) (by omega) (by omega)
    refine ⟨s', hs', ?_, hc'⟩
    rw [locWrite_regLocOf]
    rwa [hinc'] at hrel'

end JanusX86.Proofs
