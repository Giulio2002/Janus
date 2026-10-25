import JanusX86.Proofs.Movsxd

/-! # CMPXCHG m, r (`0F B0/B1`, with or without `LOCK`), up to the flags of Sail-x86 defect D1

The model computes the flags of `CMP m, rAX` (operands swapped, D1); Janus (and the hardware) those of
`CMP rAX, m`. The two agree on `ZF` (equality), the flag `CMPXCHG` users test, and on every register and
memory byte; the theorems leave the other status flags unconstrained. -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Arm64

theorem bytes_readLE_div (m : Memory) : ∀ (n a x : Nat), a ≤ x → x < a + n →
    BitVec.ofNat 8 (m.readLE a n / 256 ^ (x - a)) = m.bytes x
  | 0, a, x, h1, h2 => by omega
  | n + 1, a, x, h1, h2 => by
    have hb := (m.bytes a).isLt
    rw [Memory.readLE_succ]
    by_cases hx : x = a
    · subst hx
      simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      omega
    · have hk : x - a = (x - (a + 1)) + 1 := by omega
      have : ((m.bytes a).toNat + 256 * m.readLE (a + 1) n) / 256 = m.readLE (a + 1) n := by omega
      rw [hk, Nat.pow_succ, show 256 ^ (x - (a + 1)) * 256 = 256 * 256 ^ (x - (a + 1)) from Nat.mul_comm _ _, ← Nat.div_div_eq_div_mul, this]
      exact bytes_readLE_div m n (a + 1) x (by omega) (by omega)

theorem writeLE_readLE_self (m : Memory) (a n : Nat) : m.writeLE a n (m.readLE a n) = m := by
  cases m with
  | mk bytes regions =>
  simp only [Memory.writeLE, Memory.mk.injEq, and_true]
  funext x
  split
  · rename_i h; exact bytes_readLE_div ⟨bytes, regions⟩ n a x h.1 h.2
  · rfl


end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

set_option maxRecDepth 100000 in
theorem run_two_byte_cmpxchg (opc : Nat) (hopc : opc = 0xB0 ∨ opc = 0xB1)
    (sr tr : BitVec 48) (x : BitVec 52) (mp : BitVec 8) (rex m sib : BitVec 8) (hm : (_get_modr_m_mod m == 0b11#2) = false)
    (s : SState) :
    (two_byte_opcode_execute .Mode_64bit sr tr x mp rex (BitVec.ofNat 8 opc) m sib).run s =
      (x86_cmpxchg .Mode_64bit sr tr x rex (BitVec.ofNat 8 opc) m sib).run s := by
  rcases hopc with rfl | rfl <;>
  simp (config := {decide := true}) only [two_byte_opcode_execute, ext_two_byte_opcode_execute, eq_bits_nat,
    ↓reduceIte, Bool.false_eq_true, hm, Bool.false_and, run_bind, run_pure] <;> rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem regWrite_setFlags (js : Janus.Amd64.State) (w : Nat) (l : Janus.Amd64.Loc) (v : BitVec w) (F : Janus.Amd64.Flags) :
    regWrite (js.setFlags F) w l v = (regWrite js w l v).setFlags F := by
  cases l <;> simp [regWrite, Janus.Amd64.State.putReg, Janus.Amd64.State.putHigh, Janus.Amd64.State.setReg,
    Janus.Amd64.State.setFlags] <;> (try split) <;> rfl

set_option maxHeartbeats 8000000 in
/-- The model's `CMPXCHG` arm, memory destination (abstract read `hX` and write `hWr`). The flags are
the model's own (`CMP m, rAX`). -/
theorem run_cmpxchg {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16)
    (opc : Nat) (hopc : opc = 0xB0 ∨ opc = 0xB1) {w : Nat} (hw : w = if opc = 0xB0 then 8 else osz p)
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
    ∃ s', (x86_cmpxchg .Mode_64bit (BitVec.ofNat 48 sr) (BitVec.ofNat 48 tr) x rex (BitVec.ofNat 8 opc)
      (BitVec.ofNat 8 m) sib).run s = .ok () s' ∧ X86Config s' ∧
      Rel (((if V = js.getReg w 0 then locWrite js NX w D (regVal js w (regLocOf p.rex.isSome w (regNum p m)))
          else regWrite js w (.reg 0) V).setFlags (Janus.Amd64.subFlags V (js.getReg w 0) false).2).setRip
        (BitVec.ofNat 64 (tr + inc))) s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  obtain ⟨rf, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8)) sib s
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  have hlen := check_len_ok sr (tr + inc) hl1 hl2 htr
  have hl := hc.log
  have hb : (BitVec.ofNat 8 opc == 0xB0#8) = decide (opc = 0xB0) := by rcases hopc with rfl | rfl <;> decide
  have hsz : (if decide (opc = 0xB0) = true then (1 : Int) else if rexW p = true then 8
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    have := size_int p (decide (opc = 0xB0)); simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [this, hw]; rcases hopc with rfl | rfl <;> simp
  have hacc := run_rgfi_size h hW _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) (s := s)
  rw [regLocOf_zero] at hacc; simp only [regVal] at hacc
  let c' := (_get_rflagsbits_cf rf == 1#1)
  have hc' : _get_rflagsbits_cf rf = BitVec.ofBool c' := bv1_ofBool _
  have hspec : (gpr_arith_logic_spec (w / 8) 8 (V.setWidth 64) ((js.getReg w 0).setWidth 64) rf).run s = _ :=
    run_gpr_arith_logic_spec .cmp hW V (js.getReg w 0) rf c' hc' s
  simp only [x86_cmpxchg, h1, h2, h3, run_bind, run_select_operand_size hp hrv, hb, Bool.false_eq_true, ↓reduceIte, hsz, Int.toNat_natCast,
    nbytes_eq _ hW, show (0x0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl, hacc, hsg, ← bits3_zero,
    hX sg hsg4 hsg5, run_add_inc tr inc hinc htr, hlen, is_some, Bool.false_eq_true, ↓reduceIte, run_pure,
    run_readReg hr, trunc128, hspec, run_write_user_rflags hr hu hl]
  have hal : aluRes .cmp V (js.getReg w 0) c' = Janus.Amd64.subFlags V (js.getReg w 0) false := rfl
  have hF := flagsRel_aluOut hfr .cmp V (js.getReg w 0) c' u
  rw [hal] at hF ⊢
  generalize hR : wurf rf (aluOut .cmp rf (Janus.Amd64.subFlags V (js.getReg w 0) false).2).1
    (aluOut .cmp rf (Janus.Amd64.subFlags V (js.getReg w 0) false).2).2 u = R at hF ⊢
  generalize hFF : (Janus.Amd64.subFlags V (js.getReg w 0) false).2 = F at hF ⊢
  have hrel0 := h.setFlagsR F R hF
  have hc0 := hc.set (r := .rflags) (by decide) R
  have hl0 : (s.set .rflags R).regs.get? .log_register_writes = some false := by
    rw [get?_set_ne _ _ (by decide)]; exact hl
  have hcb : ∀ hi : BitVec w, (hi.setWidth 64 == 0#64) = decide (hi = 0) := by
    intro hi
    have h64 : w ≤ 64 := by omega
    have hlt := hi.isLt
    have : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h64
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro e; apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_setWidth, BitVec.toNat_zero, Nat.mod_eq_of_lt (show hi.toNat < 2 ^ 64 by omega)] at this
      simpa using this
    · intro e; subst e; simp
  have hz : ((V - js.getReg w 0).setWidth 64 == 0#64) = decide (V = js.getReg w 0) := by
    rw [hcb]; congr 1; apply propext; constructor
    · intro e
      have h2 : V - js.getReg w 0 + js.getReg w 0 = 0 + js.getReg w 0 := by rw [e]
      rw [BitVec.sub_add_cancel] at h2; simpa using h2
    · intro e; rw [e]; simp
  simp only [Janus.Amd64.subFlags_false_fst, hz]
  by_cases heq : V = js.getReg w 0
  · simp only [heq, decide_true, ↓reduceIte, run_bind]
    have hrg := run_rgfi_size hrel0 hW _ rex hrex (regNum_lt p m) (regNum_8 p m) (s := s.set .rflags R)
    rw [show reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 = BitVec.ofNat 4 (regNum p m) by
      rw [hrexb]; exact hidx_reg hrv m, hrg]
    simp only []
    obtain ⟨s1, hs1, hrel1, hcfg1, -, -⟩ := hWr sg hsg4 hsg5 _ _ hrel0 hc0 rfl rfl rfl
      (regVal (js.setFlags F) w (regLocOf p.rex.isSome w (regNum p m)))
    simp only [Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, hs1]
    refine ⟨_, run_write_iptr hcfg1.log _ htr, hcfg1.set (by decide) _, ?_⟩
    have := hrel1.setRipR (BitVec.ofNat 64 (tr + inc))
    rw [locWrite_setFlags] at this
    exact this
  · simp only [heq, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hwr := run_write_rgfi_size hrel0 hl0 hW _ rex hrex (n := 0) (by decide) (Or.inl (by decide)) V
    rw [regLocOf_zero] at hwr
    rw [show (0#4 : BitVec 4) = BitVec.ofNat 4 0 from rfl, hwr]
    simp only []
    have hn' : locReg (Janus.Amd64.Loc.reg 0) < 16 := by decide
    refine ⟨_, run_write_iptr (by rw [get?_setGpr_of_not _ _ hn' rfl]; exact hl0) _ htr,
      (hc0.setGpr hn' _).set (by decide) _, ?_⟩
    have := (hrel0.writeReg p.rex.isSome (n := 0) (by decide) V)
    rw [regLocOf_zero] at this
    rw [regWrite_setFlags] at this ⊢
    exact this.setRipR _

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

/-- Janus' flags restricted to `ZF` (the others unconstrained). -/
def zfOnly (f : Flags) : Flags := { cf := none, pf := none, af := none, zf := f.zf, sf := none, ovf := none }

theorem Rel.zfOnly {js : State} {s : SState} (h : Rel js s) : Rel (js.setFlags (zfOnly js.flags)) s := by
  obtain ⟨r, hr, hf⟩ := h.flags
  refine ⟨h.gpr, h.rip, ⟨r, hr, ?_⟩, h.fs, h.mem, h.canon⟩
  exact ⟨(fun v hv => by cases hv), (fun v hv => by cases hv), (fun v hv => by cases hv), hf.zf,
    (fun v hv => by cases hv), (fun v hv => by cases hv), hf.df, hf.ac⟩

theorem subFlags_zf {w : Nat} (x y : BitVec w) : (subFlags x y false).2.zf = some (decide (x = y)) := by
  have := subFlags_false_fst x y
  simp only [subFlags] at this ⊢
  rw [this]; congr 1; apply decide_eq_decide.mpr; constructor
  · intro e
    have h2 : x - y + y = 0 + y := by rw [e]
    rw [BitVec.sub_add_cancel] at h2; simpa using h2
  · intro e; rw [e]; simp

theorem locWrite_self_mem (js : State) (next : BitVec 64) {w : Nat} (hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (a : Addr) : locWrite js next w (.mem a) (locVal js next w (.mem a)) = js := by
  simp only [locWrite, locVal, memWrite, BitVec.toNat_ofNat]
  have hlt := Janus.Arm64.Memory.readLE_lt js.mem (ea js next a).toNat (w / 8)
  have e : (256 : Nat) ^ (w / 8) = 2 ^ w := by rcases hW with rfl | rfl | rfl | rfl <;> rfl
  rw [e] at hlt
  rw [Nat.mod_eq_of_lt hlt, writeLE_readLE_self]

theorem flags_sfr (K : State) (F : Flags) (r : BitVec 64) : ((K.setFlags F).setRip r).flags = F := by cases K; rfl

theorem setFlags_setRip_flags (K : State) (F G : Flags) (r : BitVec 64) :
    ((K.setFlags F).setRip r).setFlags G = (K.setFlags G).setRip r := by cases K; rfl

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

theorem decode_cmpxchg {bytes : List Nat} {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n)) (ho : o = 0xB0 ∨ o = 0xB1)
    {mm : ModRM} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (mm, r3, c))
    {i : Instr} {len : Nat} (hd : decode bytes = some (i, len)) :
    p.fs = false ∧ p.rep = 0 ∧ ∃ a, mm.rm = .m a ∧ len = n + 2 + c ∧ len ≤ 15 ∧
      i = (if p.lock then .locked (.cmpxchg (if o = 0xB0 then 8 else osz p) (.mem a)
            (regLocOf p.rex.isSome (if o = 0xB0 then 8 else osz p) (regNum p m))) a ((if o = 0xB0 then 8 else osz p) / 8)
          else .cmpxchg (if o = 0xB0 then 8 else osz p) (.mem a)
            (regLocOf p.rex.isSome (if o = 0xB0 then 8 else osz p) (regNum p m))) := by
  obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
  simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
  have hreg : mm.reg = regNum p m := by have := modrm_reg hmd; simpa [regNum] using this
  have hou : (if p.rex.getD 0 / 8 = 1 then 64 else if p.opsize = true then 16 else 32) = osz p := by
    simp [osz, rexW]
  obtain ⟨md, rg, ext, rm⟩ := mm
  simp only at hreg; subst hreg
  have hrg : ∀ w, regLoc p.rex.isSome w (regNum p m) = regLocOf p.rex.isSome w (regNum p m) := fun _ => rfl
  rcases ho with rfl | rfl
  all_goals
    simp (config := {decide := true}) only [↓reduceIte, twoByte, hmd, hou, true_and, and_true, hrg,
      false_and, and_false, or_false, false_or] at hd ⊢
    by_cases hl : 15 < n + 1 + 1 + c <;> by_cases hrp : p.rep = 0 <;> cases hf : p.fs <;> cases hk : p.lock <;>
      cases rm <;>
      simp (config := {decide := true}) [hf, hk, hl, hrp, finish, withFS, lockable, wrapLocked, lockMem] at hd ⊢
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨by omega, rfl⟩)
    | (obtain ⟨rfl, rfl⟩ := hd; exact ⟨rfl, by omega, rfl⟩)
    | omega

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions
open Janus.Amd64 Janus.Amd64.Decode

set_option maxRecDepth 100000 in
theorem modrmP2_cmpxchg {p : Janus.Amd64.Decode.Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hr : p.rep = 0) (o : Nat) (ho : o = 0xB0 ∨ o = 0xB1) : modrmP2 x o = true := by
  unfold modrmP2; rw [mpref_norep hp hr]
  cases p.opsize <;> rcases ho with rfl | rfl <;> decide

set_option maxHeartbeats 2000000 in
/-- **CMPXCHG m, r** (`0F B0/B1`, `LOCK`ed or not, every width and addressing form): every register
and memory byte agrees, and `ZF` (the comparison's outcome); the model's other status flags are those
of `CMP m, rAX` (Sail-x86 defect D1), so they are left unconstrained. -/
theorem cmpxchg_agree {js js' : State} {s : SState} (hrel : Rel js s) (hcfg : X86Config s)
    {bytes : List Nat} (hcode : CodeAt s js.rip.toNat bytes) (hlim : js.rip.toNat + 17 < 2 ^ 47)
    {p : Prefixes} {o m : Nat} {rest : List Nat} {n : Nat}
    (hpp : parsePrefixes bytes {} 0 = some (p, 0x0F :: o :: m :: rest, n)) (ho : o = 0xB0 ∨ o = 0xB1)
    (hstep : step bytes js = .ok js') :
    ∃ s', (janus_x86_step ()).run s = .ok .Janus_OK s' ∧ Rel (js'.setFlags (zfOnly js'.flags)) s' ∧
      X86Config s' := by
  cases hd : decode bytes with
  | none => simp [step, hd] at hstep
  | some il =>
  obtain ⟨i, len⟩ := il
  cases hmd : modrm (p.rex.getD 0) (m :: rest) with
  | none =>
    exfalso
    obtain ⟨b0, t, rfl, h4, h5⟩ := parsePrefixes_head _ _ _ hpp (by omega) (by omega)
    simp only [decode, h4, h5, false_or, ↓reduceIte, decodeLegacy, hpp] at hd
    rcases ho with rfl | rfl <;> simp (config := {decide := true}) [twoByte, hmd] at hd
  | some mrc =>
  obtain ⟨mm, r3, c⟩ := mrc
  obtain ⟨hfs, hrep, a, hrm, rfl, hlen, rfl⟩ := decode_cmpxchg hpp ho hmd hd
  rw [step_of_decode hd] at hstep
  generalize hw : (if o = 0xB0 then 8 else osz p) = w at hstep
  have hx : exec (.cmpxchg w (.mem a) (regLocOf p.rex.isSome w (regNum p m))) (n + 2 + c) js = .ok js' := by
    cases hk : p.lock
    · simpa [hk] using hstep
    · simp only [hk, ↓reduceIte] at hstep; exact exec_locked hstep
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [← hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  have hm256 : m < 256 := by
    have hdrop : bytes.drop n = 0x0F :: o :: m :: rest := by simpa using parsePrefixes_drop _ _ _ hpp
    exact hcode.1 m (by
      have : m ∈ bytes.drop n := by rw [hdrop]; simp
      exact List.mem_of_mem_drop this)
  have hm3 : m / 64 ≠ 3 := by
    obtain ⟨md, rg, ext, rm⟩ := mm; simp only at hrm; subst hrm; exact (modrm_c_ge hmd).2.2
  have hmod : (_get_modr_m_mod (BitVec.ofNat 8 m) == 0b11#2) = false := by
    rw [(modrm_fields m hm256).1]
    have : m / 64 < 4 := by omega
    revert hm3 this; generalize m / 64 = q; intro h1 h2
    rcases (show q = 0 ∨ q = 1 ∨ q = 2 by omega) with rfl | rfl | rfl <;> decide
  have hnext : BitVec.ofNat 64 ((BitVec.toNat js.rip + (n + 2 + c)) % 2 ^ 64) =
      BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + 0) := by
    rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega
  simp only [exec] at hx
  rw [hnext] at hx
  have hD : rmDst p w mm.rm = .mem a := by rw [hrm]; simp [rmDst, hfs]
  cases hrd : readLocRW js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + 0)) w (.mem a) with
  | error e => simp only [hrd] at hx; cases hx
  | ok X =>
  obtain ⟨hok, rfl⟩ := readLocRW_loc hrd
  have hsrc : readLoc js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + 0)) w (regLocOf p.rex.isSome w (regNum p m)) =
      .ok (regVal js w (regLocOf p.rex.isSome w (regNum p m))) := readLoc_regLocOf _ _ _ _ _
  simp only [hrd, hsrc, writeLoc_loc hok] at hx
  rw [← hD] at hok hx
  refine rm_frame2_any hrel hcfg hcode hlim hpp (fun x rex hpr => modrmP2_cmpxchg hpr hrep o ho) hmd
    (fun k' h => by rw [hrm] at h; cases h) hW (k := 0) (by decide) (by omega)
    (fun sr tr x rex sib => x86_cmpxchg .Mode_64bit sr tr x rex (BitVec.ofNat 8 o) (BitVec.ofNat 8 m) sib)
    (fun x rex _ sr tr sib => run_two_byte_cmpxchg o ho sr tr x _ rex _ sib hmod s) ?_
  intro x rex hpr hrv sib tr inc eaddr hinc' hinc8 _ hX hWr _ _ _
  obtain ⟨s', hs', hc', hrel'⟩ := run_cmpxchg hrel hcfg hpr hrv o ho hw.symm m hm256 sib tr _ inc eaddr _ _
    (hX true false true hok) (fun sg h4 h5 => hWr true false sg h4 h5 hok) hinc8 js.rip.toNat (by omega) (by omega)
    (by omega)
  refine ⟨s', hs', ?_, hc'⟩
  have hz := hrel'.zfOnly
  rw [setFlags_setRip_flags, hinc'] at hz
  rw [hD] at hz hx
  generalize hV : locVal js (BitVec.ofNat 64 (js.rip.toNat + n + 2 + c + 0)) w (.mem a) = V at hz hx
  have hzz : zfOnly (subFlags V (js.getReg w 0) false).2 = zfOnly (subFlags (js.getReg w 0) V false).2 := by
    simp only [zfOnly, subFlags_zf, eq_comm (a := V)]
  by_cases he : js.getReg w 0 = V
  · rw [if_pos he] at hx; rw [if_pos he.symm] at hz
    simp only [Except.ok.injEq] at hx; subst hx
    rw [flags_sfr, setFlags_setRip_flags, ← hzz]; exact hz
  · rw [if_neg he] at hx; rw [if_neg (fun e => he e.symm)] at hz
    simp only [Except.ok.injEq] at hx; subst hx
    rw [flags_sfr, setFlags_setRip_flags, ← hzz, ← hV, locWrite_self_mem js _ hW a, hV]
    exact hz
end JanusX86.Proofs
