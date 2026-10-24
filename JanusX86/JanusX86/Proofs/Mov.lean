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
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr hEA hR3 _
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

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem lea_mask {w : Nat} (hw : w = 16 ∨ w = 32 ∨ w = 64) (e : BitVec 64) :
    sail_mask 64 (trunc_signed (w / 8) e) = (e.setWidth w).setWidth 64 := by
  rcases hw with rfl | rfl | rfl <;>
  apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
  simp [sail_mask, trunc_signed, sail_mask_signed, Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Sail.BitVec.length,
    BitVec.getLsbD_setWidth] <;> omega

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_lea {bytes : List Nat} {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x8D :: m :: rest, n))
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.fs = false ∧ p.rep = 0 ∧ len = n + 1 + c ∧ len ≤ 15 ∧
      ∃ a, mm.rm = .m a ∧ i = .lea (osz p) (regNum p m) a := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hreg : mm.reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hreg; subst hreg
  simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, true_and, and_true,
    false_and, and_false, or_false, false_or, finish] at hd ⊢
  cases rm with
  | r k => simp at hd
  | m a =>
    by_cases hl : 15 < n + 1 + c <;> by_cases hrp : p.rep = 0 <;>
      cases hf : p.fs <;> cases hk : p.lock <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, lockable, withFS] at hd ⊢
    obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl⟩

set_option maxHeartbeats 2000000 in
theorem run_lea {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (m : Nat) (hm : m < 256) (hm3 : m / 64 ≠ 3) (sib : BitVec 8) (tr : Nat) (inc : Nat) (eaddr : BitVec 64)
    (hEA : (x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 tr) rex (BitVec.ofNat 3 (m % 8))
        (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s = .ok (eaddr, (inc : Int)) s)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_lea .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 0x8D)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((js.putReg (osz p) (regNum p m) (eaddr.setWidth (osz p))).setRip (BitVec.ofNat 64 (tr + inc))) s' ∧
      X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW3 := osz_cases p
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := Or.inr hW3
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hl := hc.log
  have hsz : (if rexW p = true then (8 : Int) else if p.opsize = true then 2 else 4) =
      ((osz p / 8 : Nat) : Int) := by unfold osz; cases rexW p <;> cases p.opsize <;> simp
  have hcr : (check_range 2 8 ((osz p / 8 : Nat) : Int)).run s = .ok ((osz p / 8 : Nat) : Int) s := by
    have hb : ((2 ≤b ((osz p / 8 : Nat) : Int)) && (((osz p / 8 : Nat) : Int) ≤b 8)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; rcases hW3 with e | e | e <;> rw [e] <;> decide
    simp only [check_range, run_bind, run_sail_assert_of hb, run_pure]
  have hreg8 : regLocOf p.rex.isSome (osz p) (regNum p m) = .reg (regNum p m) := by
    unfold regLocOf; rw [if_neg (by rcases hW3 with e | e | e <;> omega)]
  simp only [x86_lea, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hsz, hcr, ← bits3_zero, hEA,
    run_add_inc tr inc hinc htr, hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_pure, Int.toNat_natCast,
    nbytes_eq _ hW, lea_mask hW3, show reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 =
      BitVec.ofNat 4 (regNum p m) by rw [hrexb]; exact hidx_reg hrv m,
    run_write_rgfi_size h hl hW _ rex hrex (regNum_lt p m) (regNum_8 p m) (eaddr.setWidth (osz p))]
  have hn' := locReg_lt p.rex.isSome (osz p) (regNum p m) (regNum_lt p m)
  refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not s _ hn' rfl]; exact hl) _ htr, ?_,
    (hc.setGpr hn' _).set (by decide) _⟩
  have := (h.writeReg p.rex.isSome (regNum_lt p m) (eaddr.setWidth (osz p))).setRipR (BitVec.ofNat 64 (tr + inc))
  rw [hreg8] at this ⊢
  exact this

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem modrm_afs {rx m : Nat} {rest : List Nat} {md reg ext : Nat} {a : Addr} {r3 : List Nat} {c : Nat}
    (h : modrm rx (m :: rest) = some (⟨md, reg, ext, .m a⟩, r3, c)) : a.fs = false := by
  revert h
  unfold modrm
  simp only
  repeat' split
  all_goals intro h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq, ModRM.mk.injEq, RM.m.injEq] at h
       obtain ⟨⟨-, -, -, rfl⟩, -, -⟩ := h; rfl)

set_option maxRecDepth 100000 in
theorem run_one_byte_lea (sr tr : BitVec 48) (x : BitVec 52) (hl : _get_prefixes_lck x = 0#8) (rex m sib : BitVec 8)
    (hm : (_get_modr_m_mod m == 3#2) = false) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x8D) m sib).run s =
      (x86_lea .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x8D) m sib).run s := by
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, hm, Bool.false_or, Bool.or_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxHeartbeats 1000000 in
open Janus.Amd64 Janus.Amd64.Decode in
/-- **LEA r, m** (`8D`): every addressing form, operand size and prefix sequence Janus accepts. -/
theorem lea_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x8D :: m :: rest, n))
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
    simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hlk, hfs, hrep, rfl, hlen, a, hrm, rfl⟩ := decode_lea hpp hmd hd
  rw [step_of_decode hd] at hstep
  simp only [exec, Except.ok.injEq] at hstep
  subst hstep
  have hm3 : m / 64 ≠ 3 := by
    obtain ⟨md, rg, ext, rm⟩ := mm; simp only at hrm; subst hrm; exact (modrm_c_ge hmd).2.2
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + 0) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = 0x8D :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hmod : (_get_modr_m_mod (BitVec.ofNat 8 m) == 3#2) = false := by
    rw [(modrm_fields m hm256).1, beq2_3 _ (by omega)]; simpa using hm3
  refine rm_frame hrel hcfg hcode hlim hpp (by unfold prefixGroup; omega) (by omega) (by omega)
    (by decide) hlk hmd (fun k h => by rw [hrm] at h; cases h) (w := 64) (by decide) (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => x86_lea .Mode_64bit sr tr x rex (BitVec.ofNat 8 0x8D) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_one_byte_lea sr tr x hl rex _ sib hmod s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr hEA hR3 hEo
  obtain ⟨s', hs', hrel', hc'⟩ := run_lea hrel hcfg hpr hrv m hm256 hm3 sib tr inc eaddr (hEA hm3) hinc8
    js.rip.toNat (by omega) (by omega) (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  rw [hinc', hEo a hrm] at hrel'
  have hafs : a.fs = false := by
    obtain ⟨md, rg, ext, rm⟩ := mm; simp only at hrm; subst hrm; exact modrm_afs hmd
  simpa [ea, hafs, hnext] using hrel'

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- The immediate of `MOV r/m, imm` (`C6/C7`) as Janus reads it (`immU8`/`immZ`). -/
def immMov (w v : Nat) : Nat := if w = 64 then Janus.Amd64.Decode.sext 32 64 v else v

theorem mov_imm_val {k w : Nat} (hkw : (w = 8 ∧ k = 1) ∨ (w = 16 ∧ k = 2) ∨ (w = 32 ∧ k = 4) ∨ (w = 64 ∧ k = 4))
    (v : Nat) (hv : v < 2 ^ (8 * k)) :
    (if (((w / 8 : Nat) : Int) == 8) = true then
        Sail.BitVec.zeroExtend (Sail.BitVec.signExtend (Sail.BitVec.truncate
          (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * k) v) 128) 32) 64) 128
      else Sail.BitVec.zeroExtend (BitVec.ofNat (8 * k) v) 128) =
      ((BitVec.ofNat w (immMov w v)).setWidth 64).setWidth 128 := by
  rcases hkw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.zeroExtend, immMov] <;> omega
  · apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.zeroExtend, immMov] <;> omega
  · apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.zeroExtend, immMov] <;> omega
  · have e : Sail.BitVec.truncate (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * 4) v) 128) 32 = BitVec.ofNat 32 v := by
      apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.zeroExtend, Sail.BitVec.truncate] <;> omega
    rw [e]
    simp only [Sail.BitVec.signExtend, sext_eq_32 v (by simpa using hv), Sail.BitVec.zeroExtend,
      BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq, immMov, ↓reduceIte]
    rfl

set_option maxHeartbeats 2000000 in
/-- The model's `MOV r/m, imm` arm (`C6/C7 /0`), any r/m operand. -/
theorem run_mov_mi {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0xC6 ∨ opc = 0xC7) {w : Nat} (hw : w = if opc = 0xC6 then 8 else osz p)
    {k : Nat} (hk : k = if opc = 0xC6 then 1 else immBytes w)
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
        (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 k)).run s = .ok (eaddr, (inc : Int)) s)
    (hR3 : m / 64 = 3 → inc = 0 ∧ eaddr = 0#64)
    {ds : List Nat} (hds : CodeAt s (tr + inc) ds) {v : Nat} {r : List Nat}
    (hle : Janus.Amd64.Decode.readLE k ds = some (v, r))
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc + k) (hl2 : tr + inc + k ≤ sr + 15) (htr : tr + inc + k < 2 ^ 47) :
    ∃ s', (x86_mov_op_en_mi .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((locWrite js NX w D (BitVec.ofNat w (immMov w v))).setRip (BitVec.ofNat 64 (tr + inc + k))) s' ∧
      X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hlb : logbitp_bits 3 rex = rexW p := by rw [hrexb]; exact logbitp3_rexByte hrv
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hkw : (w = 8 ∧ k = 1) ∨ (w = 16 ∧ k = 2) ∨ (w = 32 ∧ k = 4) ∨ (w = 64 ∧ k = 4) := by
    subst hk hw; unfold osz immBytes
    rcases hopc with rfl | rfl <;> cases hx : rexW p <;> cases hy : p.opsize <;> simp
  have hb : (BitVec.ofNat 8 opc == 0xC6#8) = decide (opc = 0xC6) := by rcases hopc with rfl | rfl <;> decide
  have hb7 : (BitVec.ofNat 8 opc == 0xC7#8) = decide (opc = 0xC7) := by rcases hopc with rfl | rfl <;> decide
  have his : (if decide (opc = 0xC6) = true then (1 : Int) else if rexW p = true then 4 else if p.opsize = true then 2
      else 4) = ((k : Nat) : Int) := by
    subst hk hw; unfold osz immBytes
    rcases hopc with rfl | rfl <;> cases hx : rexW p <;> cases hy : p.opsize <;> simp
  have hrs : (if (decide (opc = 0xC7) && rexW p) = true then (8 : Int) else ((k : Nat) : Int)) = ((w / 8 : Nat) : Int) := by
    subst hk hw; unfold osz immBytes
    rcases hopc with rfl | rfl <;> cases hx : rexW p <;> cases hy : p.opsize <;> simp
  have hk3 : bits_of_int ((k : Nat) : Int) 3 = BitVec.ofNat 3 k := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have hk8 : k < 8 := by omega
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc + k) hl1 hl2 htr
  have hea : (if (BitVec.ofNat 2 (m / 64) == 3#2) = true then (pure ((0x0000000000000000#64 : BitVec 64), (0 : Int)) : SailM _)
      else x86_effective_addr .Mode_64bit x (BitVec.ofNat 48 tr) rex (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64))
        sib (BitVec.ofNat 3 k)).run s = .ok (eaddr, (inc : Int)) s := by
    by_cases h3' : m / 64 = 3
    · obtain ⟨rfl, rfl⟩ := hR3 h3'
      rw [beq2_3 _ (by omega)]; simp [h3']
    · rw [beq2_3 _ (by omega)]; simp only [h3', decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hEA h3'
  obtain ⟨-, hvv, -⟩ := readLE_sumLE _ ds hle
  have hvl : v < 2 ^ (8 * k) := by
    rw [hvv, Nat.pow_mul]
    exact sumLE_lt _ (fun j => by
      by_cases hj : j < ds.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hds.1 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
  have hrip := h.rip
  have hrme : (rme_size .Mode_64bit 8 k (Sail.BitVec.signExtend (BitVec.ofNat 48 (tr + inc)) 64) none 1 ":X"
      false false).run s = .ok (Sail.BitVec.zeroExtend (BitVec.ofNat (8 * k) v) 128) s := by
    simp only [rme_size, run_bind, run_load_code hc hrip 8 hds (by omega) hle (by omega), run_pure]
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  have hadd2 : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 (tr + inc)) (bits_of_int ((k : Nat) : Int) 48)).run s =
      .ok (BitVec.ofNat 48 (tr + inc + k)) s := by
    have ez : (bits_of_int ((k : Nat) : Int) 48).toNat = k := by
      rw [bits_of_int_natCast_toNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  simp only [x86_mov_op_en_mi, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hb, hb7, hlb, his, hrs, hk3, hea,
    hsg, run_add_inc tr inc hinc (by omega), hsel, show (8 : Int).toNat = 8 from rfl, Int.toNat_natCast, hrme, hadd2,
    hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_pure, mov_imm_val hkw v hvl]
  obtain ⟨s1, hs1, hrel1, hcfg1, -, -⟩ := hWr sg hsg4 hsg5 _ _ h hc rfl rfl rfl (BitVec.ofNat w (immMov w v))
  rw [hs1]
  exact ⟨_, run_write_iptr hcfg1.log _ htr, hrel1.setRipR _, hcfg1.set (by decide) _⟩

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem decode_movi {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n))
    (ho : o = 0xC6 ∨ o = 0xC7) (hext : m / 8 % 8 = 0)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {w : Nat} (hw : w = if o = 0xC6 then 8 else osz p)
    {k : Nat} (hk : k = if o = 0xC6 then 1 else immBytes w)
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.rep = 0 ∧ ∃ v r4, readLE k r3 = some (v, r4) ∧ len = n + 1 + c + k ∧ len ≤ 15 ∧
      i = .mov w (rmDst p w mm.rm) (.imm (immMov w v)) ∧ (∀ k', mm.rm = .r k' → p.fs = false) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hex := modrm_ext hmd
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have ho8 : (osz p = 8) = False := by rcases osz_cases p with e | e | e <;> simp [e]
  have hib2 : (if osz p = 16 then 2 else 4) = immBytes (osz p) := by simp [immBytes, ho8]
  have hib : ∀ q, (if q = 8 then 1 else if q = 16 then 2 else 4) = immBytes q := fun _ => rfl
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hex; subst hex
  cases hr : readLE k r3 with
  | none =>
    exfalso
    rcases ho with rfl | rfl
    all_goals
      simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, immZ, immU8, true_and, and_true,
        false_and, and_false, or_false, false_or, hib, hext, ho8, hib2, ne_eq, not_true_eq_false] at hd hw hk
      subst hw hk
      simp [hr, hib, hib2] at hd
  | some vr =>
  obtain ⟨v, r4⟩ := vr
  rcases ho with rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, immZ, immU8, true_and, and_true,
      false_and, and_false, or_false, false_or, hib, hext, ho8, hib2, ne_eq, not_true_eq_false] at hd hw hk ⊢
    subst hw hk
    simp only [hr, finish] at hd
    refine ⟨?_, ?_, v, r4, rfl, ?_⟩
    all_goals
      by_cases hl : 15 < n + 1 + c + 1 <;> by_cases hl2 : 15 < n + 1 + c + immBytes (osz p) <;>
      by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;> cases rm <;>
      simp (config := {decide := true}) only [hf, hk, hl, hl2, hrp, rmDst_r, rmDst_m, rmLoc_r, rmLoc_m,
        lockable_mov, withFS_mov_ri, ↓reduceIte, Bool.false_eq_true, ho8, immMov] at hd ⊢ <;>
      (try simp [withFS] at hd ⊢)
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl, fun _ h => by cases h⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl, fun _ _ => rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := hd; simp; omega)
      | omega
      | rfl
      | (trace_state; sorry)

end JanusX86.Proofs
