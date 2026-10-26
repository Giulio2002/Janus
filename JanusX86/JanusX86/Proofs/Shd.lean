import JanusX86.Proofs.ShdWidth
import JanusX86.Proofs.Shift

/-! # SHLD/SHRD (`0F A4/A5/AC/AD`) -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

theorem run_shld_spec {w : Nat} (hW : w = 16 ∨ w = 32 ∨ w = 64) (x y : BitVec w) (c : Nat) (hc : c < 64)
    (hcw : c ≤ w) (rin : BitVec 32) (s : SState) (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, (shld_spec (w / 8) (x.setWidth 64) (y.setWidth 64) (BitVec.ofNat 6 c) rin).run s =
      .ok ((shdVal true x y c).setWidth 64, false, out, und) s ∧ FlagsRel (shdFl true x y c f) df (wurf rin out und u) := by
  rcases hW with rfl | rfl | rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shld16 x y c hc hcw rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [shld_spec, Nat.reduceDiv, run_bind, tr_sw x 16 (by decide) rfl, tr_sw y 16 (by decide) rfl,
      BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shld32 x y c hc hcw rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [shld_spec, Nat.reduceDiv, run_bind, tr_sw x 32 (by decide) rfl, tr_sw y 32 (by decide) rfl,
      BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shld64 x y c hc hcw rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [shld_spec, Nat.reduceDiv, BitVec.setWidth_eq, h1]

theorem run_shrd_spec {w : Nat} (hW : w = 16 ∨ w = 32 ∨ w = 64) (x y : BitVec w) (c : Nat) (hc : c < 64)
    (hcw : c ≤ w) (rin : BitVec 32) (s : SState) (f : Flags) (df : Bool) (u : Nat) (hr : FlagsRel f df rin) :
    ∃ out und, (shrd_spec (w / 8) (x.setWidth 64) (y.setWidth 64) (BitVec.ofNat 6 c) rin).run s =
      .ok ((shdVal false x y c).setWidth 64, false, out, und) s ∧ FlagsRel (shdFl false x y c f) df (wurf rin out und u) := by
  rcases hW with rfl | rfl | rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shrd16 x y c hc hcw rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [shrd_spec, Nat.reduceDiv, run_bind, tr_sw x 16 (by decide) rfl, tr_sw y 16 (by decide) rfl,
      BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shrd32 x y c hc hcw rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [shrd_spec, Nat.reduceDiv, run_bind, tr_sw x 32 (by decide) rfl, tr_sw y 32 (by decide) rfl,
      BitVec.cast_eq, h1, run_pure]
    rfl
  · obtain ⟨out, und, h1, h2⟩ := run_shrd64 x y c hc hcw rin s f df u hr
    refine ⟨out, und, ?_, h2⟩
    simp only [shrd_spec, Nat.reduceDiv, BitVec.setWidth_eq, h1]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

def shdK (o : Nat) : Nat := if o % 2 = 0 then 1 else 0

/-- The count byte of a SHLD/SHRD encoding, as the model reads it. -/
def shdCntOK (s : SState) (js : Janus.Amd64.State) (opc te : Nat) (cv : BitVec 8) : Prop :=
  (opc % 2 = 0 → ∃ ds r, CodeAt s te ds ∧ Janus.Amd64.Decode.readLE 1 ds = some (cv.toNat, r)) ∧
  (opc % 2 = 1 → cv = (js.regs 1).setWidth 8)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The model's SHLD/SHRD arm, any r/m operand (abstract read `hX` and write `hWr`). -/
theorem run_shd {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0xA4 ∨ opc = 0xA5 ∨ opc = 0xAC ∨ opc = 0xAD) {w : Nat} (hw : w = osz p)
    (m : Nat) (hm : m < 256) (sib : BitVec 8) (tr te : Nat)
    (V : BitVec w) (inc : Nat) (eaddr : BitVec 64) (NX : BitVec 64) (D : Janus.Amd64.Loc)
    (hX : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) true false sg x (BitVec.ofNat 48 tr) rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib (BitVec.ofNat 3 1)).run s =
        .ok ((V.setWidth 64).setWidth 128, (inc : Int), eaddr) s)
    (hWr : ∀ sg, (sg = 4 ↔ p.fs = true) → sg ≠ 5 →
      ∀ js0 s0, Rel js0 s0 → X86Config s0 → js0.regs = js.regs → js0.mem = js.mem → js0.fsBase = js.fsBase →
      ∀ y : BitVec w, ∃ s1,
        (x86_operand_to_reg_mem .Mode_64bit (w / 8) true false ((y.setWidth 64).setWidth 128) sg eaddr x rex
          (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run s0 = .ok () s1 ∧
        Rel (locWrite js0 NX w D y) s1 ∧ X86Config s1 ∧
        s1.regs.get? .rflags = s0.regs.get? .rflags ∧ s1.regs.get? .janus_undef = s0.regs.get? .janus_undef)
    (hte : te = tr + inc) (hinc : inc < 8) (cv : BitVec 8) (hcv : shdCntOK s js opc te cv)
    (hcw : cv.toNat % (if w = 64 then 64 else 32) ≤ w)
    (sr : Nat) (hl1 : sr ≤ te + shdK opc) (hl2 : te + shdK opc ≤ sr + 15) (htr : te + shdK opc < 2 ^ 47) :
    ∃ s', (x86_shld_shrd .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex
      (BitVec.ofNat 8 opc) (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧
      Rel (((locWrite js NX w D (shdVal (decide (opc = 0xA4 ∨ opc = 0xA5)) V (js.getReg w (regNum p m))
          (cv.toNat % (if w = 64 then 64 else 32)))).setFlags
        (shdFl (decide (opc = 0xA4 ∨ opc = 0xA5)) V (js.getReg w (regNum p m)) (cv.toNat % (if w = 64 then 64 else 32))
          js.flags)).setRip (BitVec.ofNat 64 (te + shdK opc))) s' ∧
      X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hlb : logbitp_bits 3 rex = rexW p := by rw [hrexb]; exact logbitp3_rexByte hrv
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  have hW3 : w = 16 ∨ w = 32 ∨ w = 64 := by rw [hw]; exact osz_cases p
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := Or.inr hW3
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (te + shdK opc) hl1 hl2 htr
  have hl := hc.log
  have hrip := h.rip
  have hsel := run_select_address_size x (by rw [hp.adr]; decide) s
  have hadd : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 tr) (bits_of_int (inc : Int) 48)).run s =
      .ok (BitVec.ofNat 48 te) s := by
    have ez : (bits_of_int (inc : Int) 48).toNat = inc := by
      rw [bits_of_int_natCast_toNat]; omega
    rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
    congr 2; simp; omega
  have hsz : (if false = true then (1 : Int) else if rexW p = true then (if false = true then 4 else 8)
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    rw [size_int p false]; simp [hw]
  have hcr : (check_range 2 8 ((w / 8 : Nat) : Int)).run s = .ok ((w / 8 : Nat) : Int) s := by
    have hb : ((2 ≤b ((w / 8 : Nat) : Int)) && (((w / 8 : Nat) : Int) ≤b 8)) = true := by
      rcases hW3 with e | e | e <;> rw [e] <;> decide
    simp only [check_range, run_bind, run_sail_assert_of hb, run_pure]
  have hreg : regLocOf p.rex.isSome w (regNum p m) = .reg (regNum p m) := by
    unfold regLocOf; rw [if_neg (by rcases hW3 with e | e | e <;> omega)]
  have hidx : reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 = BitVec.ofNat 4 (regNum p m) := by
    rw [hrexb]; exact hidx_reg hrv m
  have hY := run_rgfi_size h hW _ rex hrex (regNum_lt p m) (regNum_8 p m) (s := s)
  rw [hreg] at hY; simp only [regVal] at hY
  simp only [x86_shld_shrd, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hsz, hcr, hsg, Int.toNat_natCast,
    show (0b001#3 : BitVec 3) = BitVec.ofNat 3 1 from rfl, hX sg hsg4 hsg5, hadd, run_pure, hlb, nbytes_eq _ hW,
    hidx, hY]
  have hmask : (if rexW p = true then 64 else 32) = (if w = 64 then 64 else 32) := by
    rw [hw]; unfold osz; cases rexW p <;> cases p.opsize <;> simp
  generalize hM : (if w = 64 then 64 else 32) = M at hcw hmask ⊢
  have hMp : M = 32 ∨ M = 64 := by rw [← hM]; split <;> simp
  have hc64 : cv.toNat % M < 64 := by rcases hMp with e | e <;> rw [e] <;> omega
  have hwr := run_write_user_rflags hr hu hl
  have htrunc := shres_trunc hW
  have hbt : ∀ R : BitVec 64, bits_of_int (Sail.BitVec.toNatInt R) 64 = R := fun R => by
    rw [show Sail.BitVec.toNatInt R = ((R.toNat : Nat) : Int) from rfl, bits_natCast, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have hset : ∀ (L : Bool) (F : Janus.Amd64.Flags) (out und : BitVec 32), FlagsRel F js.df (wurf rf out und u) →
      ∃ s1, (x86_operand_to_reg_mem .Mode_64bit (w / 8) true false
        ((((shdVal L V (js.getReg w (regNum p m)) (cv.toNat % M)).setWidth 64).setWidth 128)) sg eaddr x rex
        (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64)) sib).run (s.set .rflags (wurf rf out und u)) = .ok () s1 ∧
        Rel ((locWrite js NX w D (shdVal L V (js.getReg w (regNum p m)) (cv.toNat % M))).setFlags F) s1 ∧
        X86Config s1 := by
    intro L F out und hF
    obtain ⟨s1, hs1, hrel1, hcfg1, -, -⟩ := hWr sg hsg4 hsg5 _ _ (h.setFlagsR F _ hF) (hc.set (by decide) _) rfl rfl rfl
      (shdVal L V (js.getReg w (regNum p m)) (cv.toNat % M))
    refine ⟨s1, hs1, ?_, hcfg1⟩
    rwa [locWrite_setFlags] at hrel1
  have hrr : opc % 2 = 1 → (rr08 1#4 rex).run s = .ok cv s := by
    intro ho; rw [hcv.2 ho]
    exact run_rr08_low (n := 1) (by decide) (h.gpr 1 (by decide)) rex (by simp [low8])
  have hld : opc % 2 = 0 → (rme_size .Mode_64bit 8 1 (Sail.BitVec.signExtend (BitVec.ofNat 48 te) 64) none 1 ":X"
      false false).run s = .ok (Sail.BitVec.zeroExtend cv 128) s := by
    intro ho
    obtain ⟨ds, r, hds, hle⟩ := hcv.1 ho
    have : te + 1 ≤ 2 ^ 47 := by simp [shdK, ho] at htr; omega
    simp only [rme_size, run_bind, run_load_code hc hrip 8 hds (by decide) hle this, run_pure]
    congr 2; simp
  have hadd1 : opc % 2 = 0 → (add_to_iptr .Mode_64bit (BitVec.ofNat 48 te) 0x000000000001#48).run s =
      .ok (BitVec.ofNat 48 (te + 1)) s := by
    intro ho
    have : te + 1 < 2 ^ 47 := by simp [shdK, ho] at htr; omega
    rw [run_add_to_iptr _ _ (by simp; omega)]
    congr 2; simp; omega
  rcases hopc with rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [eq_bits_nat, ↓reduceIte, Bool.false_eq_true, run_bind, run_pure,
      hsel, show (8 : Int).toNat = 8 from rfl, shdK] at hlen htr hl1 hl2 ⊢
  all_goals (try simp only [hld rfl, hadd1 rfl, run_bind, run_pure])
  all_goals (try simp only [hrr rfl, run_bind, run_pure])
  all_goals (try simp only [Nat.add_zero] at hlen htr ⊢)
  all_goals simp only [hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_pure, run_readReg hr, trunc128,
    cmask_all, run_bind, hmask]
  all_goals simp only [decide_true, decide_false]
  all_goals first
    | (obtain ⟨out, und, hs, hF⟩ := run_shld_spec hW3 V (js.getReg w (regNum p m)) _ hc64 hcw rf s js.flags js.df u hfr; simp only [hs, ↓reduceIte, Bool.false_eq_true, run_pure, run_bind, hbt, hwr, htrunc, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]; obtain ⟨s1, hs1, hrel1, hcfg1⟩ := hset true _ out und hF; simp only [hs1]; exact ⟨_, run_write_iptr hcfg1.log _ (by omega), hrel1.setRipR _, hcfg1.set (by decide) _⟩)
    | (obtain ⟨out, und, hs, hF⟩ := run_shrd_spec hW3 V (js.getReg w (regNum p m)) _ hc64 hcw rf s js.flags js.df u hfr; simp only [hs, ↓reduceIte, Bool.false_eq_true, run_pure, run_bind, hbt, hwr, htrunc, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]; obtain ⟨s1, hs1, hrel1, hcfg1⟩ := hset false _ out und hF; simp only [hs1]; exact ⟨_, run_write_iptr hcfg1.log _ (by omega), hrel1.setRipR _, hcfg1.set (by decide) _⟩)

end JanusX86.Proofs


namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem decode_shd {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n))
    (ho : o = 0xA4 ∨ o = 0xA5 ∨ o = 0xAC ∨ o = 0xAD)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.lock = false ∧ p.rep = 0 ∧ (∀ k', mm.rm = .r k' → p.fs = false) ∧ ∃ cnt,
      (o % 2 = 0 → ∃ v r4, readLE 1 r3 = some (v, r4) ∧ cnt = .imm v ∧ len = n + 2 + c + 1) ∧
      (o % 2 = 1 → cnt = .loc (.reg 1) ∧ len = n + 2 + c) ∧ len ≤ 15 ∧
      i = .shd (decide (o = 0xA4 ∨ o = 0xA5)) (osz p) (rmDst p (osz p) mm.rm) mm.reg cnt := by
  obtain ⟨b0, t, rfl, h4, h5, hsys, h62⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega) (by sys_none) (by omega)
  simp only [decode, hsys, h62, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  obtain ⟨md, rg, ext, rm⟩ := mm
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  have ho8 : (osz p = 8) = False := by rcases osz_cases p with e | e | e <;> simp [e]
  rcases ho with rfl | rfl | rfl | rfl
  · cases hr : readLE 1 r3 with
    | none => simp (config := {decide := true}) [twoByte, hmd, immU8, hr] at hd
    | some vr =>
    obtain ⟨v, r4⟩ := vr
    simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, hou, true_and, and_true, immU8, hr,
      false_and, and_false, or_false, false_or] at hd ⊢
    by_cases hl : 15 < n + 1 + 1 + c + 1 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
      cases rm <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, finish, withFS, rmDst, rmLoc, regLocOf, ho8, lockable] at hd ⊢
    all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨_, ⟨rfl, by omega⟩, by omega, rfl⟩)
  · simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, hou, true_and, and_true,
      false_and, and_false, or_false, false_or] at hd ⊢
    by_cases hl : 15 < n + 1 + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
      cases rm <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, finish, withFS, rmDst, rmLoc, regLocOf, ho8, lockable] at hd ⊢
    all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨_, ⟨rfl, by omega⟩, by omega, rfl⟩)
  · cases hr : readLE 1 r3 with
    | none => simp (config := {decide := true}) [twoByte, hmd, immU8, hr] at hd
    | some vr =>
    obtain ⟨v, r4⟩ := vr
    simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, hou, true_and, and_true, immU8, hr,
      false_and, and_false, or_false, false_or] at hd ⊢
    by_cases hl : 15 < n + 1 + 1 + c + 1 <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
      cases rm <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, finish, withFS, rmDst, rmLoc, regLocOf, ho8, lockable] at hd ⊢
    all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨_, ⟨rfl, by omega⟩, by omega, rfl⟩)
  · simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, hou, true_and, and_true,
      false_and, and_false, or_false, false_or] at hd ⊢
    by_cases hl : 15 < n + 1 + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
      cases rm <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, finish, withFS, rmDst, rmLoc, regLocOf, ho8, lockable] at hd ⊢
    all_goals (obtain ⟨rfl, rfl⟩ := hd; exact ⟨_, ⟨rfl, by omega⟩, by omega, rfl⟩)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64

theorem execShd_any {js js' : State} {next : BitVec 64} {left : Bool} {w : Nat} {D : Loc} {src : Nat} {cnt : Src}
    (h : execShd js next left w D src cnt = .ok js') :
    ∃ cv : BitVec 8, readSrc js next 8 cnt = .ok cv ∧ locOK js next w D true ∧
      cv.toNat % (if w = 64 then 64 else 32) ≤ w ∧
      js' = ((locWrite js next w D (shdVal left (locVal js next w D) (js.getReg w src)
          (cv.toNat % (if w = 64 then 64 else 32)))).setFlags
        (shdFl left (locVal js next w D) (js.getReg w src) (cv.toNat % (if w = 64 then 64 else 32)) js.flags)).setRip
        next := by
  unfold execShd at h
  cases hc : readSrc js next 8 cnt with
  | error e => simp [hc] at h
  | ok cv =>
  cases hr : readLocRW js next w D with
  | error e => simp [hc, hr] at h
  | ok X =>
  obtain ⟨hok, rfl⟩ := readLocRW_loc hr
  simp only [hc, hr, writeLoc_loc hok] at h
  refine ⟨cv, rfl, hok, ?_⟩
  generalize cv.toNat % (if w = 64 then 64 else 32) = c at h ⊢
  by_cases h0 : c = 0
  · subst h0
    simp only [↓reduceIte, Except.ok.injEq] at h
    refine ⟨by omega, ?_⟩
    rw [← h, shdVal_zero]; simp only [shdFl, ↓reduceIte]
    have e := (locWrite_flags js next w D (locVal js next w D)).1
    generalize locWrite js next w D (locVal js next w D) = J at e ⊢
    rw [← e]; cases J; rfl
  · simp only [h0, ↓reduceIte] at h
    by_cases hg : c > w
    · simp [hg] at h
    · simp only [hg, ↓reduceIte, Except.ok.injEq] at h
      refine ⟨by omega, ?_⟩
      rw [← h]
      cases left <;> simp [shdFl, shdVal, h0]

/-- An r/m location whose address does not depend on the next instruction's address. -/
def noRip : Loc → Prop
  | .mem a => a.rip = false
  | _ => True

theorem ea_noRip {js : State} {N1 N2 : BitVec 64} {a : Janus.Amd64.Addr} (h : a.rip = false) :
    ea js N1 a = ea js N2 a := by
  simp [ea, eaOff, h]

theorem locOK_noRip {js : State} {N1 N2 : BitVec 64} {w : Nat} {D : Loc} (h : noRip D) (wr : Bool) :
    locOK js N1 w D wr ↔ locOK js N2 w D wr := by
  cases D <;> simp only [locOK] <;> simp only [noRip] at h <;> rw [ea_noRip h]

theorem locVal_noRip {js : State} {N1 N2 : BitVec 64} {w : Nat} {D : Loc} (h : noRip D) :
    locVal js N1 w D = locVal js N2 w D := by
  cases D <;> simp only [locVal] <;> simp only [noRip] at h <;> rw [ea_noRip h]

theorem locWrite_noRip {js : State} {N1 N2 : BitVec 64} {w : Nat} {D : Loc} (h : noRip D) (y : BitVec w) :
    locWrite js N1 w D y = locWrite js N2 w D y := by
  cases D <;> simp only [locWrite] <;> simp only [noRip] at h <;> rw [ea_noRip h]

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

set_option maxRecDepth 100000 in
theorem run_two_byte_shd (o : Nat) (ho : o = 0xA4 ∨ o = 0xA5 ∨ o = 0xAC ∨ o = 0xAD)
    (sr tr : BitVec 48) (x : BitVec 52) (mp : BitVec 8) (hl : _get_prefixes_lck x = 0#8)
    (rex m sib : BitVec 8) (s : SState) :
    (two_byte_opcode_execute .Mode_64bit sr tr x mp rex (BitVec.ofNat 8 o) m sib).run s =
      (x86_shld_shrd .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) m sib).run s := by
  rcases ho with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [two_byte_opcode_execute, ext_two_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hl, Bool.and_false, run_bind, run_pure,
    show (240#8 == 0#8) = false from rfl] <;> rfl

set_option maxRecDepth 100000 in
theorem modrmP2_shd {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hr : p.rep = 0) (o : Nat) (ho : o = 0xA4 ∨ o = 0xA5 ∨ o = 0xAC ∨ o = 0xAD) : modrmP2 x o = true := by
  unfold modrmP2; rw [mpref_norep hp hr]
  cases p.opsize <;> rcases ho with rfl | rfl | rfl | rfl <;> decide

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

set_option maxHeartbeats 4000000 in
/-- **SHLD/SHRD r/m16/32/64, r, imm8/CL** (`0F A4/A5/AC/AD`): register and memory forms, every width.
Side condition (Sail-x86 defect D8): the `CL` forms (`A5/AD`) with a RIP-relative memory operand are
excluded — the model computes their address as if an immediate byte followed. -/
theorem shd_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n))
    (ho : o = 0xA4 ∨ o = 0xA5 ∨ o = 0xAC ∨ o = 0xAD)
    (hd8 : o % 2 = 1 → ∀ mm r3 c, modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c) →
      ∀ a, mm.rm = .m a → a.rip = false)
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
    rcases ho with rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [twoByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hlk, hrep, hfs, cnt, himm, hcl, hlen, rfl⟩ := decode_shd hpp ho hmd hd
  rw [step_of_decode hd] at hstep
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = 0x0F :: o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hW3 := osz_cases p
  have hW : osz p = 8 ∨ osz p = 16 ∨ osz p = 32 ∨ osz p = 64 := Or.inr hW3
  have hreg : mm.reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  -- the length and the next address
  have hlk' : len = n + 2 + c + shdK o := by
    unfold shdK; split
    · obtain ⟨_, _, _, _, e⟩ := himm (by omega); exact e
    · exact (hcl (by omega)).2
  subst hlk'
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 2 + c + shdK o)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + shdK o) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  simp only [exec] at hstep
  rw [hnext] at hstep
  obtain ⟨cv, hcv, hok, hcw, rfl⟩ := execShd_any hstep
  generalize hNX : BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + shdK o) = NX at hcv hok hcw ⊢
  -- the model's r/m operand is located as if an immediate byte followed (`NF`)
  have hnr : o % 2 = 1 → noRip (rmDst p (osz p) mm.rm) := by
    intro h1
    obtain ⟨md, rg, ext, rm⟩ := mm
    cases rm with
    | r k => simp only [rmDst]; rcases regLocOf_cases p.rex.isSome (osz p) k with ⟨r, e⟩ | ⟨r, e⟩ <;> rw [e] <;> trivial
    | m a =>
      have := hd8 h1 _ _ _ hmd a rfl
      simp only [rmDst, noRip]; split <;> simpa using this
  have hNF : ∀ (NF : BitVec 64), NF = BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + 1) →
      (locOK js NF (osz p) (rmDst p (osz p) mm.rm) true) ∧
      locVal js NF (osz p) (rmDst p (osz p) mm.rm) = locVal js NX (osz p) (rmDst p (osz p) mm.rm) ∧
      ∀ y, locWrite js NF (osz p) (rmDst p (osz p) mm.rm) y = locWrite js NX (osz p) (rmDst p (osz p) mm.rm) y := by
    intro NF hNF
    by_cases h1 : o % 2 = 1
    · exact ⟨(locOK_noRip (hnr h1) true).2 hok, locVal_noRip (hnr h1), fun y => locWrite_noRip (hnr h1) y⟩
    · have : NF = NX := by rw [hNF, ← hNX]; simp [shdK, show o % 2 = 0 by omega]
      subst this; exact ⟨hok, rfl, fun _ => rfl⟩
  obtain ⟨hokF, hvF, hwF⟩ := hNF _ rfl
  refine rm_frame2 hrel hcfg hcode hlim hpp (fun x rex hpr => modrmP2_shd hpr hrep o ho) hlk hmd
    hfs hW (k := 1) (by decide) (by unfold shdK at hlen; split at hlen <;> omega)
    (fun sr tr x rex sib => x86_shld_shrd .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
    (fun x rex _ hl sr tr sib => run_two_byte_shd o ho sr tr x _ hl rex _ sib s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 hc3 hX hWr _ _ _
  have hcvok : shdCntOK s js o (tr + inc) cv := by
    refine ⟨fun hoc => ?_, fun hoc => ?_⟩
    · obtain ⟨v, r4, hr4, rfl, -⟩ := himm hoc
      simp only [readSrc, Except.ok.injEq] at hcv
      have hv : v < 256 := by
        obtain ⟨-, hvv, -⟩ := readLE_sumLE _ _ hr4
        rw [hvv, show 256 = 256 ^ 1 from rfl]
        exact sumLE_lt _ (fun j => by
          by_cases hj : j < r3.length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hc3.1 _ (List.getElem_mem _)
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide) _
      refine ⟨r3, r4, by rw [hinc']; exact hc3, ?_⟩
      rw [← hcv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; exact hr4
    · obtain ⟨rfl, -⟩ := hcl hoc
      simp only [readSrc, readLoc, State.getReg, Except.ok.injEq] at hcv
      exact hcv.symm
  obtain ⟨s', hs', hrel', hc'⟩ := run_shd hrel hcfg hpr hrv o ho rfl m hm256 sib tr (tr + inc)
    (locVal js NX (osz p) (rmDst p (osz p) mm.rm)) inc eaddr _ _
    (fun sg h4 h5 => by rw [← hvF]; exact hX true false true hokF sg h4 h5)
    (fun sg h4 h5 => hWr true false sg h4 h5 hokF) rfl hinc8 cv hcvok hcw
    js.rip.toNat (by unfold shdK; split <;> omega) (by unfold shdK at hlen ⊢; split at hlen <;> split <;> omega)
    (by unfold shdK; split <;> omega)
  refine ⟨s', hs', ?_, hc'⟩
  rw [hwF, hinc', hNX] at hrel'
  rw [hreg]
  exact hrel'

end JanusX86.Proofs
