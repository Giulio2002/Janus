import JanusX86.Proofs.Lock
import JanusX86.Proofs.Mov

/-! # XCHG r/m, r (`86/87`, the memory form implicitly locked) and XCHG rAX, r (`91–97`, `REX.B 90`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_one_byte_xchg (opc : Nat) (hopc : opc = 0x86 ∨ opc = 0x87)
    (sr tr : BitVec 48) (x : BitVec 52) (rex m sib : BitVec 8)
    (hlm : ((_get_modr_m_mod m == 0b11#2) && (0xF0#8 == _get_prefixes_lck x)) = false) (s : SState) :
    (one_byte_opcode_execute .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_xchg .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases hopc with rfl | rfl <;>
  simp (config := {decide := true}) only [one_byte_opcode_execute, ext_one_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hlm, run_bind, run_pure] <;> rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxHeartbeats 4000000 in
/-- The model's `XCHG r/m, r` arm (abstract read `hX` and write `hWr`). -/
theorem run_xchg_rm {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0x86 ∨ opc = 0x87) {w : Nat} (hw : w = if opc = 0x86 then 8 else osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr : Nat)
    (V : BitVec w) (inc : Nat) (eaddr : BitVec 64) (NX : BitVec 64) (D : Janus.Amd64.Loc)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 0)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hWr : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      ∀ js0 s0, Rel js0 s0 → X86Config s0 → js0.regs = js.regs → js0.mem = js.mem → js0.fsBase = js.fsBase →
      ∀ y : BitVec w, ∃ s1,
        (x86_operand_to_reg_mem .Mode_64bit (w / 8) true false ((y.setWidth 64).setWidth 128) sg eaddr x rex
          (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run s0 = .ok () s1 ∧
        Rel (locWrite js0 NX w D y) s1 ∧ X86Config s1 ∧
        s1.regs.get? .rflags = s0.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s0.regs.get? .janus_undef)
    (hinc : inc < 8) (sr : Nat) (hl1 : sr ≤ tr + inc) (hl2 : tr + inc ≤ sr + 15) (htr : tr + inc < 2 ^ 47) :
    ∃ s', (x86_xchg .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel ((regWrite (locWrite js NX w D (regVal js w (regLocOf p.rex.isSome w (regNum p m)))) w
        (regLocOf p.rex.isSome w (regNum p m)) V).setRip (BitVec.ofNat 64 (tr + inc))) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hb : (BitVec.ofNat 8 opc == 0x86#8) = decide (opc = 0x86) := by rcases hopc with rfl | rfl <;> decide
  have hsz : (if decide (opc = 0x86) = true then (1 : Int) else if rexW p = true then 8
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    have := size_int p (decide (opc = 0x86)); simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [this, hw]; rcases hopc with rfl | rfl <;> simp
  have h9 : (ash_int (Sail.BitVec.toNatInt (BitVec.ofNat 8 opc)) (Neg.neg 4) == 9) = false := by
    rcases hopc with rfl | rfl <;> decide
  have h9' : (bits_of_int (ash_int (Sail.BitVec.toNatInt (BitVec.ofNat 8 opc)) (Neg.neg 4)) 4 == 0x9#4) = false := by
    rcases hopc with rfl | rfl <;> decide
  have hidx : reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 = BitVec.ofNat 4 (regNum p m) := by
    rw [hrexb]; exact hidx_reg hrv m
  have hrg := run_rgfi_size h hW _ rex hrex (regNum_lt p m) (regNum_8 p m) (s := s)
  obtain ⟨s1, hs1, hrel1, hcfg1, -, -⟩ := hWr sg hsg4 hsg5 _ _ h hc rfl rfl rfl
    (regVal js w (regLocOf p.rex.isSome w (regNum p m)))
  have hwr := run_write_rgfi_size hrel1 hcfg1.log hW _ rex hrex (regNum_lt p m) (regNum_8 p m) V
  simp only [x86_xchg, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hb, Bool.false_eq_true, ↓reduceIte, hsz,
    Int.toNat_natCast, hsg, h9, ← bits3_zero, hX sg hsg4 hsg5, run_add_inc tr inc hinc htr, hlen, is_some, run_pure,
    nbytes_eq _ hW, hidx, hrg]
  simp only [Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, hs1, h9', Bool.false_eq_true, ↓reduceIte,
    run_bind, trunc128, hidx, hwr]
  have hn' := locReg_lt p.rex.isSome w (regNum p m) (regNum_lt p m)
  refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not _ _ hn' rfl]; exact hcfg1.log) _ htr, ?_,
    (hcfg1.setGpr hn' _).set (by decide) _⟩
  exact (hrel1.writeReg _ (regNum_lt p m) _).setRipR _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

/-- Janus' `XCHG r/m, r` instruction: the memory form is always `LOCK`ed (alignment checked). -/
def xchgI (p : Prefixes) (w : Nat) (rm : RM) (r : Nat) : Instr :=
  match rm with
  | .r k => .xchg w (regLocOf p.rex.isSome w k) (regLocOf p.rex.isSome w r)
  | .m a => .locked (.xchg w (.mem a) (regLocOf p.rex.isSome w r)) a (w / 8)

theorem decode_xchg_r {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o = 0x86 ∨ o = 0x87)
    {md rg ext k : Nat} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (⟨md, rg, ext, .r k⟩, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.fs = false ∧ p.rep = 0 ∧ p.lock = false ∧ len = n + 1 + c ∧ len ≤ 15 ∧
      i = .xchg (if o = 0x86 then 8 else osz p) (regLocOf p.rex.isSome (if o = 0x86 then 8 else osz p) k)
        (regLocOf p.rex.isSome (if o = 0x86 then 8 else osz p) (regNum p m)) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hreg : rg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  subst hreg
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have hrg : ∀ w, regLoc p.rex.isSome w (regNum p m) = regLocOf p.rex.isSome w (regNum p m) := fun _ => rfl
  have hrm : ∀ w, rmLoc p.rex.isSome w (.r k) = regLocOf p.rex.isSome w k := fun _ => rfl
  rcases ho with rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, true_and, and_true, hrg, hrm,
      false_and, and_false, or_false, false_or] at hd ⊢
  · rcases regLocOf_cases p.rex.isSome 8 k with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] at hd ⊢ <;>
    by_cases hl : 15 < n + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, finish, withFS, lockable] at hd ⊢ <;>
    obtain ⟨rfl, rfl⟩ := hd <;> exact ⟨rfl, by omega, rfl⟩
  · rcases regLocOf_cases p.rex.isSome (osz p) k with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] at hd ⊢ <;>
    by_cases hl : 15 < n + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, finish, withFS, lockable] at hd ⊢ <;>
    obtain ⟨rfl, rfl⟩ := hd <;> exact ⟨rfl, by omega, rfl⟩

theorem decode_xchg_m {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o = 0x86 ∨ o = 0x87)
    {md rg ext : Nat} {a : Addr} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (⟨md, rg, ext, .m a⟩, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.fs = false ∧ p.rep = 0 ∧ len = n + 1 + c ∧ len ≤ 15 ∧
      i = .locked (.xchg (if o = 0x86 then 8 else osz p) (.mem a)
        (regLocOf p.rex.isSome (if o = 0x86 then 8 else osz p) (regNum p m))) a ((if o = 0x86 then 8 else osz p) / 8) := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hreg : rg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  subst hreg
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have hrg : ∀ w, regLoc p.rex.isSome w (regNum p m) = regLocOf p.rex.isSome w (regNum p m) := fun _ => rfl
  rcases ho with rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, oneByte, hmd, hou, true_and, and_true, hrg, rmLoc,
      false_and, and_false, or_false, false_or] at hd ⊢
    by_cases hl : 15 < n + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, finish, withFS, lockable, wrapLocked, lockMem] at hd ⊢
  all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl⟩)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem regLocOf_locOK (js : State) (next : BitVec 64) (w : Nat) (b : Bool) (k : Nat) (wr : Bool) :
    locOK js next w (regLocOf b w k) wr := by
  rcases regLocOf_cases b w k with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] <;> trivial

theorem locWrite_regLocOf' (js : State) (next : BitVec 64) (w : Nat) (b : Bool) (k : Nat) (v : BitVec w) :
    locWrite js next w (regLocOf b w k) v = regWrite js w (regLocOf b w k) v := by
  rcases regLocOf_cases b w k with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] <;> rfl

set_option maxHeartbeats 2000000 in
/-- **XCHG r/m, r** (`86/87`): register and memory forms (the memory form is implicitly locked; Janus
checks the alignment), every width. -/
theorem xchg_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, o :: m :: rest, n)) (ho : o = 0x86 ∨ o = 0x87)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  cases hmd : modrm (p.rex.getD 0) (m :: rest) with
  | none =>
    exfalso
    obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
    simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
    rcases ho with rfl | rfl <;> simp (config := {decide := true}) [oneByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨md, rg, ext, rm⟩ := mm
  generalize hw : (if o = 0x86 then 8 else osz p) = w
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [← hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  -- the executed body and its two pieces
  obtain ⟨hfs, hrep, hlen, hlen', hx, hlck⟩ : p.fs = false ∧ p.rep = 0 ∧ len = n + 1 + c ∧ len ≤ 15 ∧
      exec (.xchg w (rmDst p w rm) (regLocOf p.rex.isSome w (regNum p m))) len js = .ok js' ∧
      (∀ x rex, PfxRel p x rex → ((_get_modr_m_mod (BitVec.ofNat 8 m) == 0b11#2) &&
        (0xF0#8 == _get_prefixes_lck x)) = false) := by
    cases rm with
    | r k =>
      obtain ⟨hfs, hrep, hlk, rfl, hl, rfl⟩ := decode_xchg_r hpp ho hmd hd
      rw [step_of_decode hd, hw] at hstep
      refine ⟨hfs, hrep, rfl, hl, by simpa [rmDst] using hstep, fun x rex hpr => ?_⟩
      have := hpr.lck; rw [hlk] at this; simp [this]
    | m a =>
      obtain ⟨hfs, hrep, rfl, hl, rfl⟩ := decode_xchg_m hpp ho hmd hd
      rw [step_of_decode hd, hw] at hstep
      refine ⟨hfs, hrep, rfl, hl, by simpa [rmDst, hfs] using exec_locked hstep, fun x rex hpr => ?_⟩
      have hm3 := (modrm_c_ge hmd).2.2
      have hmod : (_get_modr_m_mod (BitVec.ofNat 8 m) == 0b11#2) = false := by
        rw [(modrm_fields m hm256).1]
        have : m / 64 < 4 := by omega
        revert hm3 this; generalize m / 64 = q; intro h1 h2
        rcases (show q = 0 ∨ q = 1 ∨ q = 2 by omega) with rfl | rfl | rfl <;> decide
      simp [hmod]
  subst hlen
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 1 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + 0) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  simp only [exec] at hx
  rw [hnext] at hx
  cases hra : readLocRW js (BitVec.ofNat 64 (js.rip.toNat + n + 1 + c + 0)) w (rmDst p w rm) with
  | error e => simp only [hra] at hx; cases hx
  | ok VA =>
  obtain ⟨hok, rfl⟩ := readLocRW_loc hra
  simp only [hra, readLoc_regLocOf, writeLoc_loc hok, writeLoc_loc (regLocOf_locOK _ _ _ _ _ true),
    locWrite_regLocOf', Except.ok.injEq] at hx
  subst hx
  have hfld := (modrm_fields m hm256).2.1
  refine rm_frame_any hrel hcfg hcode hlim hpp (by unfold prefixGroup; rcases ho with rfl | rfl <;> decide)
    (by omega) (by omega) (by rcases ho with rfl | rfl <;> decide) hmd (fun _ _ => hfs) hW (k := 0) (by decide)
    (by omega)
    (fun sr tr x rex sib => x86_xchg .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
    (fun x rex hpr sr tr sib => run_one_byte_xchg o ho sr tr x rex _ sib (hlck x rex hpr) s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr _ _ _
  obtain ⟨s', hs', hrel', hc'⟩ := run_xchg_rm hrel hcfg hpr hrv o ho hw.symm m hm256 sib tr _ inc eaddr _ _
    (hX true false true hok) (fun sg h4 h5 => hWr true false sg h4 h5 hok) hinc8 js.rip.toNat (by omega) (by omega)
    (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  rw [hinc'] at hrel'
  exact hrel'

end JanusX86.Proofs
