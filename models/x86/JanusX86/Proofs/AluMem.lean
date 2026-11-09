import JanusX86.Proofs.MemOp

/-! # ALU instructions, memory forms -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- Janus' state after a store of `n` bytes of `v` at `E`. -/
def memWrite (js : Janus.Amd64.State) (E n v : Nat) : Janus.Amd64.State := { js with mem := js.mem.writeLE E n v }

open Janus.Amd64 in
theorem readLocRW_mem {js : State} {next : BitVec 64} {w : Nat} {a : Addr} {y : BitVec w}
    (h : readLocRW js next w (.mem a) = .ok y) :
    js.mem.accessible (ea js next a).toNat (w / 8) true = true ∧
      y = BitVec.ofNat w (js.mem.readLE (ea js next a).toNat (w / 8)) := by
  simp only [readLocRW] at h
  cases hl : loadRW js.mem (ea js next a).toNat (w / 8) with
  | error e => simp [hl] at h
  | ok v =>
    simp only [hl, Except.ok.injEq] at h; subst h
    unfold loadRW at hl
    split at hl <;> (try split at hl) <;> simp_all

open Janus.Amd64 in
theorem readLoc_mem {js : State} {next : BitVec 64} {w : Nat} {a : Addr} {y : BitVec w}
    (h : readLoc js next w (.mem a) = .ok y) :
    js.mem.accessible (ea js next a).toNat (w / 8) false = true ∧
      y = BitVec.ofNat w (js.mem.readLE (ea js next a).toNat (w / 8)) := by
  simp only [readLoc] at h
  cases hl : load js.mem (ea js next a).toNat (w / 8) with
  | error e => simp [hl] at h
  | ok v =>
    simp only [hl, Except.ok.injEq] at h; subst h
    unfold load at hl
    split at hl <;> simp_all

open Janus.Amd64 in
theorem writeLoc_mem {js : State} {next : BitVec 64} {w : Nat} {a : Addr} (v : BitVec w)
    (h : js.mem.accessible (ea js next a).toNat (w / 8) true = true) :
    writeLoc js next w (.mem a) v = .ok (memWrite js (ea js next a).toNat (w / 8) v.toNat) := by
  simp [writeLoc, store, h, Janus.Arm64.Memory.accessible_read_of_write js.mem h, memWrite]

open Janus.Amd64 in
/-- Janus' `execAlu` with a memory destination and a register source. -/
theorem execAlu_mem {js js' : State} {next : BitVec 64} {op : AluOp} {w : Nat} {a : Addr} {sl : Loc}
    (hs : readLoc js next w sl = .ok (regVal js w sl))
    (hJ : execAlu js next op w (.mem a) (.loc sl) = .ok js') :
    ∃ c, ((op = .adc ∨ op = .sbb) → js.flags.cf = some c) ∧
      js.mem.accessible (ea js next a).toNat (w / 8) (decide (op ≠ .cmp)) = true ∧
      js' = ((if op = .cmp then js else memWrite js (ea js next a).toNat (w / 8)
          (aluRes op (BitVec.ofNat w (js.mem.readLE (ea js next a).toNat (w / 8))) (regVal js w sl) c).1.toNat).setFlags
        (aluRes op (BitVec.ofNat w (js.mem.readLE (ea js next a).toNat (w / 8))) (regVal js w sl) c).2).setRip next := by
  unfold execAlu at hJ
  simp only [readSrc, hs] at hJ
  cases op
  all_goals first
    | (cases hrd : readLoc js next w (.mem a) with
       | error e => simp [hrd] at hJ
       | ok y =>
         obtain ⟨hacc, rfl⟩ := readLoc_mem hrd
         simp only [hrd, Except.ok.injEq] at hJ
         exact ⟨false, by simp, by simpa (config := {decide := true}) using hacc, by simp [← hJ, aluRes]⟩)
    | (cases hrd : readLocRW js next w (.mem a) with
       | error e => simp [hrd] at hJ
       | ok y =>
         obtain ⟨hacc, rfl⟩ := readLocRW_mem hrd
         first
         | (simp only [hrd, writeLoc_mem _ hacc] at hJ
            refine ⟨false, by simp, by simpa (config := {decide := true}) using hacc, ?_⟩
            simp only [Except.ok.injEq] at hJ; simp [← hJ, aluRes])
         | (cases hc : js.flags.cf with
            | none => simp [hrd, hc] at hJ
            | some c =>
              refine ⟨c, fun _ => rfl, by simpa (config := {decide := true}) using hacc, ?_⟩
              simp [hrd, hc, writeLoc_mem _ hacc] at hJ; simp [← hJ, aluRes]))

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem run_alu_e_g_mem {js : State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) (op : AluOp) (opc : Nat) (hopc : opc < 256)
    {w : Nat} (hw : w = if opc % 2 = 0 then 8 else osz p)
    {q m : Nat} {rest : List Nat} (hcs : CodeAt s (q + 1) rest) (hm : m < 256)
    {md reg ext : Nat} {a : Addr} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (⟨md, reg, ext, .m a⟩, r3, c)) (hq : q + c < 2 ^ 47)
    {n2 : Nat} (hn2 : n2 < 16) (h82 : n2 < 8 ∨ p.rex.isSome = true)
    (hidx2 : reg_index (BitVec.ofNat 3 (m / 8 % 8)) rex 2#2 = BitVec.ofNat 4 n2)
    (sr : Nat) (hl1 : sr ≤ q) (hl2 : q + c ≤ sr + 15) (cc : Bool) (hcf : (op = .adc ∨ op = .sbb) → js.flags.cf = some cc)
    (hacc : js.mem.accessible (ea js (BitVec.ofNat 64 (q + c)) (if p.fs then { a with fs := true } else a)).toNat (w / 8)
      (decide (op ≠ .cmp)) = true) :
    ∃ s', (x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g (sailOp op) .Mode_64bit (BitVec.ofNat 48 sr)
      (BitVec.ofNat 48 (q + 1 + (if sibP m then 1 else 0))) x rex (BitVec.ofNat 8 opc) (BitVec.ofNat 8 m)
      (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8)).run s = .ok () s' ∧
      Rel (((if op = .cmp then js else memWrite js
          (ea js (BitVec.ofNat 64 (q + c)) (if p.fs then { a with fs := true } else a)).toNat (w / 8)
          (aluRes op (BitVec.ofNat w (js.mem.readLE (ea js (BitVec.ofNat 64 (q + c))
            (if p.fs then { a with fs := true } else a)).toNat (w / 8))) (regVal js w (regLocOf p.rex.isSome w n2)) cc).1.toNat).setFlags
        (aluRes op (BitVec.ofNat w (js.mem.readLE (ea js (BitVec.ofNat 64 (q + c))
            (if p.fs then { a with fs := true } else a)).toNat (w / 8))) (regVal js w (regLocOf p.rex.isSome w n2)) cc).2).setRip
        (BitVec.ofNat 64 (q + c))) s' ∧ X86Config s' := by
  have hrexb : rex = BitVec.ofNat 8 (rexByte p) := by rw [hp.rexb]; rfl
  have hrex : (rex == 0#8) = !p.rex.isSome := by rw [hrexb]; exact rex_hrex hrv
  have hW : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
    rw [hw]; split
    · simp
    · rcases osz_cases p with e | e | e <;> simp [e]
  obtain ⟨-, hfs, hmdq⟩ := run_x86_effective_addr h hc h.rip hp hrv hcs hm hmd (nimm := 0) (by decide) (by omega)
  obtain ⟨h1, h2, h3⟩ := modrm_fields m hm
  obtain ⟨r, hr, hfr⟩ := h.flags
  obtain ⟨u, hu⟩ := hc.undef
  obtain ⟨sg, hsg, hsg4, hsg5⟩ := run_select_segment_register hp (BitVec.ofNat 2 (m / 64)) (BitVec.ofNat 3 (m % 8))
    (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8) s
  have hsz : (if decide (opc % 2 = 0) = true then (1 : Int) else if rexW p = true then 8
      else if p.opsize = true then 2 else 4) = ((w / 8 : Nat) : Int) := by
    have := size_int p (decide (opc % 2 = 0)); simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [this, hw]; simp
  let c' := (_get_rflagsbits_cf r == 1#1)
  have hc' : _get_rflagsbits_cf r = BitVec.ofBool c' := bv1_ofBool _
  generalize hE : (ea js (BitVec.ofNat 64 (q + c)) (if p.fs then { a with fs := true } else a)).toNat = E at hacc ⊢
  have hX := run_operand_from_mem h hc hp hrv hcs hm hmd (nimm := 0) (by decide) (by omega) hW hsg4 hsg5 true false
    (by rw [Nat.add_zero, hE]; exact hacc)
  simp only [Nat.add_zero, hE] at hX
  have hcc : aluRes op (BitVec.ofNat w (js.mem.readLE E (w / 8))) (regVal js w (regLocOf p.rex.isSome w n2)) c' =
      aluRes op (BitVec.ofNat w (js.mem.readLE E (w / 8))) (regVal js w (regLocOf p.rex.isSome w n2)) cc := by
    apply aluRes_c; intro hop
    have := hfr.cf cc (hcf hop)
    show (_get_rflagsbits_cf r == 1#1) = cc
    rw [this]; cases cc <;> rfl
  have hinc : (bits_of_int (((c - 1 - (if sibP m then 1 else 0) : Nat) : Int)) 3) =
      BitVec.ofNat 3 (c - 1 - (if sibP m then 1 else 0)) := by
    apply BitVec.eq_of_toNat_eq; rw [bits_of_int_natCast_toNat]; simp
  have htr : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 (q + 1 + (if sibP m then 1 else 0)))
      (Sail.BitVec.zeroExtend (BitVec.ofNat 3 (c - 1 - (if sibP m then 1 else 0))) 48)).run s =
      .ok (BitVec.ofNat 48 (q + c)) s := by
    obtain ⟨hc1, hc6, -⟩ := modrm_c_ge hmd
    cases hs : sibP m <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
    · have ez : (Sail.BitVec.zeroExtend (BitVec.ofNat 3 (c - 1 - 0)) 48).toNat = c - 1 - 0 := by
        simp [Sail.BitVec.zeroExtend]; omega
      rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
      congr 2; simp; omega
    · have ez : (Sail.BitVec.zeroExtend (BitVec.ofNat 3 (c - 1 - 1)) 48).toNat = c - 1 - 1 := by
        simp [Sail.BitVec.zeroExtend]; omega
      rw [run_add_to_iptr _ _ (by rw [ez]; simp; omega), ez]
      congr 2; simp; omega
  have hlen := check_len_ok sr (q + c) (by omega) hl2 hq
  simp only [x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g, h1, h2, h3, run_bind,
    run_select_operand_size hp hrv, byteop_all opc hopc, hsz, nbytes_eq w hW, hidx2,
    run_rgfi_size h hW _ rex hrex hn2 h82, hsg, Int.toNat_natCast, hX, hinc, htr, hlen, is_some,
    Bool.false_eq_true, ↓reduceIte, run_pure, run_readReg hr, trunc128,
    run_gpr_arith_logic_spec op hW _ _ r c' hc', hcc]
  generalize hR : aluRes op (BitVec.ofNat w (js.mem.readLE E (w / 8))) (regVal js w (regLocOf p.rex.isSome w n2)) cc = R
  have hfR : FlagsRel R.2 js.df (wurf r (aluOut op r R.2).1 (aluOut op r R.2).2 u) := by
    rw [← hR]; exact flagsRel_aluOut hfr op _ _ cc u
  by_cases hcmp : op = .cmp
  · subst hcmp
    simp only [sailOp, show ((8 : Nat) == 8 || (8 : Nat) == 7) = true from rfl, ↓reduceIte, run_pure,
      run_write_user_rflags hr hu hc.log]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact hc.log) _ hq, ?_, ?_⟩
    · exact h.flagsRip R.2 _ hfR _
    · exact (hc.set (by decide) _).set (by decide) _
  · have hop : (sailOp op == 8 || sailOp op == 7) = false := by cases op <;> simp_all [sailOp]
    have hmd3 : (BitVec.ofNat 2 (m / 64) == 3#2) = false := by
      rw [beq2_3 _ (by omega)]; simpa using (modrm_c_ge hmd).2.2
    simp only [hcmp, decide_not, decide_false, Bool.not_false] at hacc
    rw [← hE] at hacc
    obtain ⟨s1, hs1, hrel1, hcfg1, hreg1⟩ := run_operand_to_mem h hc hp hW hsg4 hsg5 true false a hfs _ _ hmd3 _ R.1 hacc
    rw [hE] at hrel1
    simp only [hop, Bool.false_eq_true, ↓reduceIte, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
    rw [hs1]
    have e1 : s1.regs.get? .rflags = some r := by rw [hreg1]; exact hr
    have e2 : s1.regs.get? .janus_undef = some u := by rw [hreg1]; exact hu
    have e3 : s1.regs.get? .log_register_writes = some false := by rw [hreg1]; exact hc.log
    simp only [run_write_user_rflags e1 e2 e3]
    refine ⟨_, run_write_iptr (by rw [get?_set_ne _ _ (by decide)]; exact e3) _ hq, ?_, ?_⟩
    · simp only [hcmp, ↓reduceIte]
      exact hrel1.flagsRip R.2 _ hfR _
    · exact (hcfg1.set (by decide) _).set (by decide) _

end JanusX86.Proofs
