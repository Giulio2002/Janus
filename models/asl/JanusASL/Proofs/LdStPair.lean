import JanusASL.Proofs.LdStLit
import JanusASL.Proofs.MemPair
import JanusASL.Proofs.LdStDecodeP

/-! # Proved: LDP/STP/LDPSW (general registers), all three addressing modes -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem writeLE_regions (m : Janus.Arm64.Memory) (a n v : Nat) : (m.writeLE a n v).regions = m.regions := rfl

theorem accessible_writeLE (m : Janus.Arm64.Memory) (a n v b k : Nat) (w : Bool) :
    (m.writeLE a n v).accessible b k w = m.accessible b k w := rfl

/-- The value of a pair load: zero-extended, or sign-extended for LDPSW (`opc = 1`). -/
def pairVal (opc v : Nat) : BitVec 64 :=
  if opc = 1 then Janus.Arm64.signExtendLoad 2 64 v else BitVec.ofNat 64 v

theorem memPair_load {js js2 : Janus.Arm64.State} {opc rt rt2 : Nat} {addr : BitVec 64}
    (h : Janus.Arm64.memPair js opc true rt rt2 addr = .ok js2) :
    js.mem.accessible addr.toNat (2 ^ (2 + opc / 2)) false = true ∧
      js.mem.accessible (addr + BitVec.ofNat 64 (2 ^ (2 + opc / 2))).toNat (2 ^ (2 + opc / 2)) false = true ∧
      js2 = (js.writeZR rt (pairVal opc (js.mem.readLE addr.toNat (2 ^ (2 + opc / 2))))).writeZR rt2
        (pairVal opc (js.mem.readLE (addr + BitVec.ofNat 64 (2 ^ (2 + opc / 2))).toNat (2 ^ (2 + opc / 2)))) := by
  unfold Janus.Arm64.memPair at h
  simp only [ite_true] at h
  split at h
  · cases h
  · next v1 h1 =>
    split at h
    · cases h
    · next v2 h2 =>
      obtain ⟨a1, rfl⟩ := load_ok h1
      obtain ⟨a2, rfl⟩ := load_ok h2
      cases h
      exact ⟨a1, a2, rfl⟩

/-- Janus' memory after STP. -/
def pairMem (js : Janus.Arm64.State) (opc rt rt2 : Nat) (addr : BitVec 64) : Janus.Arm64.Memory :=
  (js.mem.writeLE addr.toNat (2 ^ (2 + opc / 2)) (js.readZR rt).toNat).writeLE
    (addr + BitVec.ofNat 64 (2 ^ (2 + opc / 2))).toNat (2 ^ (2 + opc / 2)) (js.readZR rt2).toNat

theorem memPair_store {js js2 : Janus.Arm64.State} {opc rt rt2 : Nat} {addr : BitVec 64}
    (h : Janus.Arm64.memPair js opc false rt rt2 addr = .ok js2) :
    js.mem.accessible addr.toNat (2 ^ (2 + opc / 2)) true = true ∧
      js.mem.accessible (addr + BitVec.ofNat 64 (2 ^ (2 + opc / 2))).toNat (2 ^ (2 + opc / 2)) true = true ∧
      js2 = { js with mem := pairMem js opc rt rt2 addr } := by
  unfold Janus.Arm64.memPair at h
  simp only [Bool.false_eq_true, ite_false] at h
  split at h
  · cases h
  · next m1 h1 =>
    split at h
    · cases h
    · next m2 h2 =>
      obtain ⟨a1, rfl⟩ := store_ok h1
      obtain ⟨a2, rfl⟩ := store_ok h2
      cases h
      exact ⟨a1, by rw [← accessible_writeLE]; exact a2, rfl⟩

/-- Two adjacent accessible halves: every byte of the whole is in a region, below `2^48`. -/
theorem pair_bytes {m : Janus.Arm64.Memory} {a : BitVec 64} {d : Nat} {w : Bool}
    (h1 : m.accessible a.toNat d w = true) (h2 : m.accessible (a + BitVec.ofNat 64 d).toNat d w = true) :
    (a + BitVec.ofNat 64 d).toNat = a.toNat + d ∧ (∀ i < 2 * d, InRegion m (a.toNat + i) w) ∧
      a.toNat + 2 * d ≤ 2 ^ 48 := by
  have l1 := accessible_lt h1
  have e : (a + BitVec.ofNat 64 d).toNat = a.toNat + d := by
    simp [BitVec.toNat_add]; omega
  have l2 := accessible_lt h2
  rw [e] at l2 h2
  refine ⟨e, fun i hi => ?_, by omega⟩
  by_cases hi' : i < d
  · exact accessible_bytes h1 i hi'
  · have := accessible_bytes h2 (i - d) (by omega); rwa [Nat.add_assoc, show d + (i - d) = i by omega] at this

theorem run_BigEndian_gprAcc {s : SState} (h : LinuxEL0Config s) (w : Bool) :
    (BigEndian (gprAcc w).acctype).run s = .ok false s := run_BigEndian_gpr h

set_option maxHeartbeats 16000000 in
theorem run_exec_pair_load {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {opc ds : Nat}
    (hcase : (opc = 0 ∧ ds = 32) ∨ (opc = 2 ∧ ds = 64)) {rn rt rt2 : Nat} (hn : rn < 32) (ht : rt < 32)
    (ht2 : rt2 < 32) (offset : BitVec 64) (postindex wback tc : Bool)
    (hj : Janus.Arm64.memIndexed js rn offset postindex wback (fun s a => Janus.Arm64.memPair s opc true rt rt2 a) =
      .ok js1) :
    ∃ s', (execute_aarch64_instrs_memory_pair_general_post_idx ds .MemOp_LOAD rn false offset postindex false false
      rt rt2 tc false wback).run s = .ok () s' ∧ Rel js1 s' ∧ MemRel js1.mem s' ∧ RStep s s' := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  unfold Janus.Arm64.memIndexed at hj
  split at hj
  · cases hj
  · next base hb =>
  simp only at hj
  split at hj
  · cases hj
  · next js2 hs2 =>
  cases hj
  have hB := run_base h hc hn hb
  generalize hA : (if postindex = true then base else base + offset) = addr at hs2
  obtain ⟨hacc1, hacc2, rfl⟩ := memPair_load hs2
  obtain ⟨e2, hreg, hlt⟩ := pair_bytes hacc1 hacc2
  have hcr := run_CreateAccDescGPR hc false tc
  simp only [Bool.false_eq_true, ite_false] at hcr
  have hA' : (if postindex = false then base + offset else base) = addr := by rw [← hA]; cases postindex <;> rfl
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨v, hv, hvn⟩ := run_Mem_read_pair hU hf hc hm addr (2 * Int.ediv 32 8).toNat (Or.inl rfl)
      (fun i hi => hreg i (by have e1 : (2 * Int.ediv 32 8).toNat = 8 := rfl
                              have e2 : 2 * 2 ^ (2 + 0 / 2) = 8 := rfl
                              omega))
      (by have e1 : (2 * Int.ediv 32 8).toNat = 8 := rfl
          have e2 : 2 * 2 ^ (2 + 0 / 2) = 8 := rfl
          omega) tc
    unfold execute_aarch64_instrs_memory_pair_general_post_idx
    cfg_simp [run_readReg hp, he, EL0, hcr, hB, hA', HaveLSE2Ext, run_IsFeatureImplemented hc,
      run_BigEndian_gprAcc hc, hv]
    have hsplit : v.toNat = js.mem.readLE addr.toNat 4 + 2 ^ 32 * js.mem.readLE (addr.toNat + 4) 4 := by
      rw [hvn, show (2 * Int.ediv 32 8).toNat = 4 + 4 from rfl, readLE_add]
    have b1 := readLE_lt js.mem addr.toNat 4
    have b2 := readLE_lt js.mem (addr.toNat + 4) 4
    have hm4 : (addr.toNat + 4) % 18446744073709551616 = addr.toNat + 4 := Nat.mod_eq_of_lt (by omega)
    simp only [hm4]
    have hv1 : (Sail.BitVec.extractLsb (BitVec.setWidth 64 v) 31 0).setWidth 64 =
        pairVal 0 (js.mem.readLE addr.toNat 4) := by
      apply BitVec.eq_of_toNat_eq
      simp [Sail.BitVec.extractLsb, pairVal, Nat.shiftRight_eq_div_pow, hsplit]
      try omega
    have hv2 : (Sail.BitVec.extractLsb (BitVec.setWidth 64 v) 63 32).setWidth 64 =
        pairVal 0 (js.mem.readLE (addr.toNat + 4) 4) := by
      apply BitVec.eq_of_toNat_eq
      simp [Sail.BitVec.extractLsb, pairVal, Nat.shiftRight_eq_div_pow, hsplit]
      try omega
    obtain ⟨s1, hx1, hr1, hst1⟩ := run_X_set_r h ht (N := 32) (by decide) (Sail.BitVec.extractLsb (BitVec.setWidth 64 v) 31 0)
    simp only [Janus.Arm64.State.setX, hv1] at hr1
    obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r hr1 ht2 (N := 32) (by decide) (Sail.BitVec.extractLsb (BitVec.setWidth 64 v) 63 32)
    simp only [Janus.Arm64.State.setX, hv2] at hr2
    have hst12 := hst1.trans hst2
    have hc2 := hc.rstep hst12
    cases wback
    · refine ⟨s2, ?_, hr2, ?_, hst12⟩
      · cfg_simp [hx1, hx2, run_readReg hc2.speInFlight]
      · simp only [Bool.false_eq_true, ite_false, writeZR_mem]; exact hm.rstep hst12
    · obtain ⟨s3, hx3, hr3, hst3⟩ := run_writeback hr2 hc2 hn (base + offset)
      have hc3 := hc2.rstep hst3
      refine ⟨s3, ?_, hr3, ?_, hst12.trans hst3⟩
      · cases postindex <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hA <;> subst hA <;>
        cfg_simp [hx1, hx2, hx3, run_readReg hc3.speInFlight]
      · simp only [ite_true, writeSP_mem, writeZR_mem]; exact hm.rstep (hst12.trans hst3)
  · obtain ⟨v, hv, hvn⟩ := run_Mem_read_pair hU hf hc hm addr (2 * Int.ediv 64 8).toNat (Or.inr rfl)
      (fun i hi => hreg i (by have e1 : (2 * Int.ediv 64 8).toNat = 16 := rfl
                              have e2 : 2 * 2 ^ (2 + 2 / 2) = 16 := rfl
                              omega))
      (by have e1 : (2 * Int.ediv 64 8).toNat = 16 := rfl
          have e2 : 2 * 2 ^ (2 + 2 / 2) = 16 := rfl
          omega) tc
    unfold execute_aarch64_instrs_memory_pair_general_post_idx
    cfg_simp [run_readReg hp, he, EL0, hcr, hB, hA', HaveLSE2Ext, run_IsFeatureImplemented hc,
      run_BigEndian_gprAcc hc, hv]
    have hsplit : v.toNat = js.mem.readLE addr.toNat 8 + 2 ^ 64 * js.mem.readLE (addr.toNat + 8) 8 := by
      rw [hvn, show (2 * Int.ediv 64 8).toNat = 8 + 8 from rfl, readLE_add]
    have b1 := readLE_lt js.mem addr.toNat 8
    have b2 := readLE_lt js.mem (addr.toNat + 8) 8
    have hm4 : (addr.toNat + 8) % 18446744073709551616 = addr.toNat + 8 := Nat.mod_eq_of_lt (by omega)
    simp only [hm4]
    have hv1 : (Sail.BitVec.extractLsb (BitVec.setWidth 128 v) 63 0).setWidth 64 =
        pairVal 2 (js.mem.readLE addr.toNat 8) := by
      apply BitVec.eq_of_toNat_eq
      simp [Sail.BitVec.extractLsb, pairVal, Nat.shiftRight_eq_div_pow, hsplit]
      try omega
    have hv2 : (Sail.BitVec.extractLsb (BitVec.setWidth 128 v) 127 64).setWidth 64 =
        pairVal 2 (js.mem.readLE (addr.toNat + 8) 8) := by
      apply BitVec.eq_of_toNat_eq
      simp [Sail.BitVec.extractLsb, pairVal, Nat.shiftRight_eq_div_pow, hsplit]
      try omega
    obtain ⟨s1, hx1, hr1, hst1⟩ := run_X_set_r h ht (N := 64) (by decide) (Sail.BitVec.extractLsb (BitVec.setWidth 128 v) 63 0)
    simp only [Janus.Arm64.State.setX, hv1] at hr1
    obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r hr1 ht2 (N := 64) (by decide) (Sail.BitVec.extractLsb (BitVec.setWidth 128 v) 127 64)
    simp only [Janus.Arm64.State.setX, hv2] at hr2
    have hst12 := hst1.trans hst2
    have hc2 := hc.rstep hst12
    cases wback
    · refine ⟨s2, ?_, hr2, ?_, hst12⟩
      · cfg_simp [hx1, hx2, run_readReg hc2.speInFlight]
      · simp only [Bool.false_eq_true, ite_false, writeZR_mem]; exact hm.rstep hst12
    · obtain ⟨s3, hx3, hr3, hst3⟩ := run_writeback hr2 hc2 hn (base + offset)
      have hc3 := hc2.rstep hst3
      refine ⟨s3, ?_, hr3, ?_, hst12.trans hst3⟩
      · cases postindex <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hA <;> subst hA <;>
        cfg_simp [hx1, hx2, hx3, run_readReg hc3.speInFlight]
      · simp only [ite_true, writeSP_mem, writeZR_mem]; exact hm.rstep (hst12.trans hst3)


theorem app_toNat {k : Nat} (x y : BitVec k) : (x +++ y).toNat = x.toNat * 2 ^ k + y.toNat := by
  show (x ++ y).toNat = _
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem MemRel.store2 {m : Janus.Arm64.Memory} {s s1 : SState} {a d x v1 v2 : Nat} (hm : MemRel m s)
    (hs : Stored s s1 a (2 * d) x) (hx1 : x % 2 ^ (8 * d) = v1 % 2 ^ (8 * d))
    (hx2 : x / 2 ^ (8 * d) % 2 ^ (8 * d) = v2 % 2 ^ (8 * d)) :
    MemRel ((m.writeLE a d v1).writeLE (a + d) d v2) s1 := by
  intro b hb
  rw [hs.mem b]
  simp only [Janus.Arm64.Memory.writeLE]
  by_cases h2 : a + d ≤ b ∧ b < a + d + d
  · rw [if_pos (by omega), if_pos h2]
    congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl]
    rw [show b - a = d + (b - (a + d)) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show (256 : Nat) ^ d = 2 ^ (8 * d) by rw [Nat.pow_mul]]
    exact byteMod_eq (by omega) hx2
  · rw [if_neg h2]
    by_cases h1 : a ≤ b ∧ b < a + d
    · rw [if_pos (by omega), if_pos h1]
      congr 1; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl]
      exact byteMod_eq (by omega) hx1
    · rw [if_neg (by omega), if_neg h1]; exact hm b hb

set_option maxHeartbeats 16000000 in
theorem run_exec_pair_store {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {opc ds : Nat}
    (hcase : (opc = 0 ∧ ds = 32) ∨ (opc = 2 ∧ ds = 64)) {rn rt rt2 : Nat} (hn : rn < 32) (ht : rt < 32)
    (ht2 : rt2 < 32) (offset : BitVec 64) (postindex wback tc : Bool)
    (hj : Janus.Arm64.memIndexed js rn offset postindex wback (fun s a => Janus.Arm64.memPair s opc false rt rt2 a) =
      .ok js1) :
    ∃ s', (execute_aarch64_instrs_memory_pair_general_post_idx ds .MemOp_STORE rn false offset postindex false false
      rt rt2 tc false wback).run s = .ok () s' ∧ Rel js1 s' ∧ MemRel js1.mem s' ∧ GFrame s s' ∧
      (∀ b, ¬ InRegion js.mem b false → s'.mem.get? b = s.mem.get? b) ∧
      s'.cycleCount = s.cycleCount ∧ s'.sailOutput = s.sailOutput := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  unfold Janus.Arm64.memIndexed at hj
  split at hj
  · cases hj
  · next base hb =>
  simp only at hj
  split at hj
  · cases hj
  · next js2 hs2 =>
  cases hj
  have hB := run_base h hc hn hb
  generalize hA : (if postindex = true then base else base + offset) = addr at hs2
  obtain ⟨hacc1, hacc2, rfl⟩ := memPair_store hs2
  obtain ⟨e2, hreg, hlt⟩ := pair_bytes hacc1 hacc2
  have hcr := run_CreateAccDescGPR hc true tc
  simp only [ite_true] at hcr
  have hA' : (if postindex = false then base + offset else base) = addr := by rw [← hA]; cases postindex <;> rfl
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hX1 := run_X_read_w h ht (w := 32) (by decide)
    have hX2 := run_X_read_w h ht2 (w := 32) (by decide)
    obtain ⟨s1, hv, hst⟩ := run_Mem_set_pair hU hf hc addr (2 * Int.ediv 32 8).toNat (by decide)
      (fun i hi => hreg i (by have e1 : (2 * Int.ediv 32 8).toNat = 8 := rfl
                              have e2 : 2 * 2 ^ (2 + 0 / 2) = 8 := rfl
                              omega))
      (by have e1 : (2 * Int.ediv 32 8).toNat = 8 := rfl
          have e2 : 2 * 2 ^ (2 + 0 / 2) = 8 := rfl
          omega) tc
      (BitVec.setWidth ((2 * Int.ediv 32 8).toNat * 8)
        (BitVec.setWidth 32 (js.readZR rt2) +++ BitVec.setWidth 32 (js.readZR rt)))
    unfold execute_aarch64_instrs_memory_pair_general_post_idx
    cfg_simp [run_readReg hp, he, EL0, hcr, hB, hA', HaveLSE2Ext, run_IsFeatureImplemented hc,
      run_BigEndian_gprAcc hc, hX1, hX2, hv]
    have hst' : Stored s s1 addr.toNat (2 * 4) _ := hst
    have hm1 : MemRel (pairMem js 0 rt rt2 addr) s1 := by
      unfold pairMem
      rw [e2]
      refine hm.store2 (d := 4) hst' ?_ ?_
      · simp only [BitVec.toNat_setWidth]
        rw [app_toNat, show ((2 * Int.ediv 32 8).toNat * 8) = 2 * 32 from rfl]
        simp only [BitVec.toNat_setWidth]
        have := (js.readZR rt).isLt
        have := (js.readZR rt2).isLt
        omega
      · simp only [BitVec.toNat_setWidth]
        rw [app_toNat, show ((2 * Int.ediv 32 8).toNat * 8) = 2 * 32 from rfl]
        simp only [BitVec.toNat_setWidth]
        have := (js.readZR rt).isLt
        have := (js.readZR rt2).isLt
        omega
    have hr1 := h.mem_update hst.regs (pairMem js 0 rt rt2 addr)
    have hmo := MStep_of_stored hst (fun i hi => (hreg i (by
      have e1 : (2 * Int.ediv 32 8).toNat = 8 := rfl
      have e2 : 2 * 2 ^ (2 + 0 / 2) = 8 := rfl
      omega)).read)
    have hc1 : LinuxEL0Config s1 := hc.stored hst
    have hg1 : GFrame s s1 := fun r _ _ => by show s1.regs.get? r = s.regs.get? r; rw [hst.regs]
    have hwl : ∀ (dd : Nat) (vv : BitVec 64), ({ js with mem := pairMem js 0 rt rt2 addr }.writeSP dd vv).mem =
        pairMem js 0 rt rt2 addr := fun dd vv => writeSP_mem _ dd vv
    cases wback
    · refine ⟨s1, ?_, hr1, hm1, hg1, hmo, hst.cycle, hst.out⟩
      cfg_simp [run_readReg hc1.speInFlight]
    · obtain ⟨s2, hx2, hr2, hst2⟩ := run_writeback hr1 hc1 hn (base + offset)
      have hc2 := hc1.rstep hst2
      refine ⟨s2, ?_, hr2, ?_, fun r h1 h2 => (hst2.regs r h1 h2).trans (hg1 r h1 h2), fun b hb => ?_,
        hst2.cycle.trans hst.cycle, hst2.out.trans hst.out⟩
      · cases postindex <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hA <;> subst hA <;>
        cfg_simp [hx2, run_readReg hc2.speInFlight]
      · simp only [ite_true, hwl]; exact hm1.rstep hst2
      · rw [hst2.mem]; exact hmo b hb
  · have hX1 := run_X_read_w h ht (w := 64) (by decide)
    have hX2 := run_X_read_w h ht2 (w := 64) (by decide)
    obtain ⟨s1, hv, hst⟩ := run_Mem_set_pair hU hf hc addr (2 * Int.ediv 64 8).toNat (by decide)
      (fun i hi => hreg i (by have e1 : (2 * Int.ediv 64 8).toNat = 16 := rfl
                              have e2 : 2 * 2 ^ (2 + 2 / 2) = 16 := rfl
                              omega))
      (by have e1 : (2 * Int.ediv 64 8).toNat = 16 := rfl
          have e2 : 2 * 2 ^ (2 + 2 / 2) = 16 := rfl
          omega) tc
      (BitVec.setWidth ((2 * Int.ediv 64 8).toNat * 8)
        (js.readZR rt2 +++ js.readZR rt))
    unfold execute_aarch64_instrs_memory_pair_general_post_idx
    cfg_simp [run_readReg hp, he, EL0, hcr, hB, hA', HaveLSE2Ext, run_IsFeatureImplemented hc,
      run_BigEndian_gprAcc hc, hX1, hX2, hv]
    have hst' : Stored s s1 addr.toNat (2 * 8) _ := hst
    have hm1 : MemRel (pairMem js 2 rt rt2 addr) s1 := by
      unfold pairMem
      rw [e2]
      refine hm.store2 (d := 8) hst' ?_ ?_
      · simp only [BitVec.toNat_setWidth]
        rw [app_toNat, show ((2 * Int.ediv 64 8).toNat * 8) = 2 * 64 from rfl]
        have := (js.readZR rt).isLt
        have := (js.readZR rt2).isLt
        omega
      · simp only [BitVec.toNat_setWidth]
        rw [app_toNat, show ((2 * Int.ediv 64 8).toNat * 8) = 2 * 64 from rfl]
        have := (js.readZR rt).isLt
        have := (js.readZR rt2).isLt
        omega
    have hr1 := h.mem_update hst.regs (pairMem js 2 rt rt2 addr)
    have hmo := MStep_of_stored hst (fun i hi => (hreg i (by
      have e1 : (2 * Int.ediv 64 8).toNat = 16 := rfl
      have e2 : 2 * 2 ^ (2 + 2 / 2) = 16 := rfl
      omega)).read)
    have hc1 : LinuxEL0Config s1 := hc.stored hst
    have hg1 : GFrame s s1 := fun r _ _ => by show s1.regs.get? r = s.regs.get? r; rw [hst.regs]
    have hwl : ∀ (dd : Nat) (vv : BitVec 64), ({ js with mem := pairMem js 2 rt rt2 addr }.writeSP dd vv).mem =
        pairMem js 2 rt rt2 addr := fun dd vv => writeSP_mem _ dd vv
    cases wback
    · refine ⟨s1, ?_, hr1, hm1, hg1, hmo, hst.cycle, hst.out⟩
      cfg_simp [run_readReg hc1.speInFlight]
    · obtain ⟨s2, hx2, hr2, hst2⟩ := run_writeback hr1 hc1 hn (base + offset)
      have hc2 := hc1.rstep hst2
      refine ⟨s2, ?_, hr2, ?_, fun r h1 h2 => (hst2.regs r h1 h2).trans (hg1 r h1 h2), fun b hb => ?_,
        hst2.cycle.trans hst.cycle, hst2.out.trans hst.out⟩
      · cases postindex <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hA <;> subst hA <;>
        cfg_simp [hx2, run_readReg hc2.speInFlight]
      · simp only [ite_true, hwl]; exact hm1.rstep hst2
      · rw [hst2.mem]; exact hmo b hb

set_option maxHeartbeats 16000000 in
theorem run_exec_ldpsw {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {rn rt rt2 : Nat} (hn : rn < 32)
    (ht : rt < 32) (ht2 : rt2 < 32) (offset : BitVec 64) (postindex wback tc : Bool)
    (hj : Janus.Arm64.memIndexed js rn offset postindex wback (fun s a => Janus.Arm64.memPair s 1 true rt rt2 a) =
      .ok js1) :
    ∃ s', (execute_aarch64_instrs_memory_pair_general_post_idx 32 .MemOp_LOAD rn false offset postindex false true
      rt rt2 tc false wback).run s = .ok () s' ∧ Rel js1 s' ∧ MemRel js1.mem s' ∧ RStep s s' := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  unfold Janus.Arm64.memIndexed at hj
  split at hj
  · cases hj
  · next base hb =>
  simp only at hj
  split at hj
  · cases hj
  · next js2 hs2 =>
  cases hj
  have hB := run_base h hc hn hb
  generalize hA : (if postindex = true then base else base + offset) = addr at hs2
  obtain ⟨hacc1, hacc2, rfl⟩ := memPair_load hs2
  have hcr := run_CreateAccDescGPR hc false tc
  simp only [Bool.false_eq_true, ite_false] at hcr
  have hA' : (if postindex = false then base + offset else base) = addr := by rw [← hA]; cases postindex <;> rfl
  have ea0 : Sail.BitVec.addInt addr 0 = addr := by
    apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.addInt]
  have ea4 : Sail.BitVec.addInt addr (Int.ediv 32 8) = addr + BitVec.ofNat 64 (2 ^ (2 + 1 / 2)) := rfl
  obtain ⟨v1, hv1, hvn1⟩ := run_Mem_read hU hf hc hm addr (Int.ediv 32 8).toNat (by decide) hacc1 tc
  obtain ⟨v2, hv2, hvn2⟩ := run_Mem_read hU hf hc hm (addr + BitVec.ofNat 64 (2 ^ (2 + 1 / 2))) (Int.ediv 32 8).toNat
    (by decide) hacc2 tc
  unfold execute_aarch64_instrs_memory_pair_general_post_idx
  cfg_simp [run_readReg hp, he, EL0, hcr, hB, hA', HaveLSE2Ext, run_IsFeatureImplemented hc, ea0, ea4, hv1, hv2]
  have hval : ∀ (x : BitVec ((Int.ediv 32 8).toNat * 8)) (a : Nat), x.toNat = js.mem.readLE a (Int.ediv 32 8).toNat →
      (sign_extend (BitVec.setWidth 32 x) 64).setWidth 64 = pairVal 1 (js.mem.readLE a (2 ^ (2 + 1 / 2))) := by
    intro x a hx
    have e : BitVec.setWidth 32 x = BitVec.ofNat 32 (js.mem.readLE a (2 ^ (2 + 1 / 2))) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, hx]
      have := readLE_lt js.mem a 4
      simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ (2 + 1 / 2) = 4 from rfl, show (Int.ediv 32 8).toNat = 4 from rfl]
      try omega
    rw [e]; rfl
  have hv1' := hval v1 _ hvn1
  have hv2' := hval v2 _ hvn2
  obtain ⟨s1, hx1, hr1, hst1⟩ := run_X_set_r h ht (N := 64) (by decide) (sign_extend (BitVec.setWidth 32 v1) 64)
  simp only [Janus.Arm64.State.setX, hv1'] at hr1
  obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r hr1 ht2 (N := 64) (by decide) (sign_extend (BitVec.setWidth 32 v2) 64)
  simp only [Janus.Arm64.State.setX, hv2'] at hr2
  have hst12 := hst1.trans hst2
  have hc2 := hc.rstep hst12
  cases wback
  · refine ⟨s2, ?_, hr2, ?_, hst12⟩
    · cfg_simp [hx1, hx2, run_readReg hc2.speInFlight]
    · simp only [Bool.false_eq_true, ite_false, writeZR_mem]; exact hm.rstep hst12
  · obtain ⟨s3, hx3, hr3, hst3⟩ := run_writeback hr2 hc2 hn (base + offset)
    have hc3 := hc2.rstep hst3
    refine ⟨s3, ?_, hr3, ?_, hst12.trans hst3⟩
    · cases postindex <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hA <;> subst hA <;>
      cfg_simp [hx1, hx2, hx3, run_readReg hc3.speInFlight]
    · simp only [ite_true, writeSP_mem, writeZR_mem]; exact hm.rstep (hst12.trans hst3)

theorem run_dec_pair_1_0_0 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hnt : ¬((Rt.toNat = Rn.toNat ∨ Rt2.toNat = Rn.toNat) ∧ Rn.toNat ≠ 31)) :
    (decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 0#1 0#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 32 .MemOp_STORE Rn.toNat false (sign_extend imm7 64 <<< 2) true
        false false Rt.toNat Rt2.toNat true false true).run st := by
  unfold decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx
  cfg_simp [undefined_Constraint, run_internal_pick, hnt]
  all_goals first | rfl | skip

theorem run_dec_pair_1_0_1 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hnt : ¬((Rt.toNat = Rn.toNat ∨ Rt2.toNat = Rn.toNat) ∧ Rn.toNat ≠ 31)) (hne : Rt.toNat ≠ Rt2.toNat) :
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 1#1 0#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 32 .MemOp_LOAD Rn.toNat false (sign_extend imm7 64 <<< 2) true
        false false Rt.toNat Rt2.toNat true false true).run st := by
  unfold decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx
  cfg_simp [undefined_Constraint, run_internal_pick, hnt, hne]
  all_goals first | rfl | skip

theorem run_dec_pair_1_1_1 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hnt : ¬((Rt.toNat = Rn.toNat ∨ Rt2.toNat = Rn.toNat) ∧ Rn.toNat ≠ 31)) (hne : Rt.toNat ≠ Rt2.toNat) :
    (decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 1#1 1#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 32 .MemOp_LOAD Rn.toNat false (sign_extend imm7 64 <<< 2) true
        false true Rt.toNat Rt2.toNat true false true).run st := by
  unfold decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx
  cfg_simp [undefined_Constraint, run_internal_pick, hnt, hne]
  all_goals first | rfl | skip

theorem run_dec_pair_1_2_0 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hnt : ¬((Rt.toNat = Rn.toNat ∨ Rt2.toNat = Rn.toNat) ∧ Rn.toNat ≠ 31)) :
    (decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 0#1 2#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 64 .MemOp_STORE Rn.toNat false (sign_extend imm7 64 <<< 3) true
        false false Rt.toNat Rt2.toNat true false true).run st := by
  unfold decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx
  cfg_simp [undefined_Constraint, run_internal_pick, hnt]
  all_goals first | rfl | skip

theorem run_dec_pair_1_2_1 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hnt : ¬((Rt.toNat = Rn.toNat ∨ Rt2.toNat = Rn.toNat) ∧ Rn.toNat ≠ 31)) (hne : Rt.toNat ≠ Rt2.toNat) :
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 1#1 2#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 64 .MemOp_LOAD Rn.toNat false (sign_extend imm7 64 <<< 3) true
        false false Rt.toNat Rt2.toNat true false true).run st := by
  unfold decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx
  cfg_simp [undefined_Constraint, run_internal_pick, hnt, hne]
  all_goals first | rfl | skip

theorem run_dec_pair_2_0_0 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState)  :
    (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 0#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 32 .MemOp_STORE Rn.toNat false (sign_extend imm7 64 <<< 2) false
        false false Rt.toNat Rt2.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_stp_gen_aarch64_instrs_memory_pair_general_offset
  cfg_simp [undefined_Constraint, run_internal_pick]
  all_goals first | rfl | skip

theorem run_dec_pair_2_0_1 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hne : Rt.toNat ≠ Rt2.toNat) :
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 0#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 32 .MemOp_LOAD Rn.toNat false (sign_extend imm7 64 <<< 2) false
        false false Rt.toNat Rt2.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldp_gen_aarch64_instrs_memory_pair_general_offset
  cfg_simp [undefined_Constraint, run_internal_pick, hne]
  all_goals first | rfl | skip

theorem run_dec_pair_2_1_1 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hne : Rt.toNat ≠ Rt2.toNat) :
    (decode_ldpsw_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 1#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 32 .MemOp_LOAD Rn.toNat false (sign_extend imm7 64 <<< 2) false
        false true Rt.toNat Rt2.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldpsw_aarch64_instrs_memory_pair_general_offset
  cfg_simp [undefined_Constraint, run_internal_pick, hne]
  all_goals first | rfl | skip

theorem run_dec_pair_2_2_0 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState)  :
    (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 0#1 2#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 64 .MemOp_STORE Rn.toNat false (sign_extend imm7 64 <<< 3) false
        false false Rt.toNat Rt2.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_stp_gen_aarch64_instrs_memory_pair_general_offset
  cfg_simp [undefined_Constraint, run_internal_pick]
  all_goals first | rfl | skip

theorem run_dec_pair_2_2_1 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hne : Rt.toNat ≠ Rt2.toNat) :
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 1#1 2#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 64 .MemOp_LOAD Rn.toNat false (sign_extend imm7 64 <<< 3) false
        false false Rt.toNat Rt2.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldp_gen_aarch64_instrs_memory_pair_general_offset
  cfg_simp [undefined_Constraint, run_internal_pick, hne]
  all_goals first | rfl | skip

theorem run_dec_pair_3_0_0 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hnt : ¬((Rt.toNat = Rn.toNat ∨ Rt2.toNat = Rn.toNat) ∧ Rn.toNat ≠ 31)) :
    (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 0#1 0#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 32 .MemOp_STORE Rn.toNat false (sign_extend imm7 64 <<< 2) false
        false false Rt.toNat Rt2.toNat true false true).run st := by
  unfold decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx
  cfg_simp [undefined_Constraint, run_internal_pick, hnt]
  all_goals first | rfl | skip

theorem run_dec_pair_3_0_1 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hnt : ¬((Rt.toNat = Rn.toNat ∨ Rt2.toNat = Rn.toNat) ∧ Rn.toNat ≠ 31)) (hne : Rt.toNat ≠ Rt2.toNat) :
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 1#1 0#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 32 .MemOp_LOAD Rn.toNat false (sign_extend imm7 64 <<< 2) false
        false false Rt.toNat Rt2.toNat true false true).run st := by
  unfold decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx
  cfg_simp [undefined_Constraint, run_internal_pick, hnt, hne]
  all_goals first | rfl | skip

theorem run_dec_pair_3_1_1 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hnt : ¬((Rt.toNat = Rn.toNat ∨ Rt2.toNat = Rn.toNat) ∧ Rn.toNat ≠ 31)) (hne : Rt.toNat ≠ Rt2.toNat) :
    (decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 1#1 1#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 32 .MemOp_LOAD Rn.toNat false (sign_extend imm7 64 <<< 2) false
        false true Rt.toNat Rt2.toNat true false true).run st := by
  unfold decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx
  cfg_simp [undefined_Constraint, run_internal_pick, hnt, hne]
  all_goals first | rfl | skip

theorem run_dec_pair_3_2_0 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hnt : ¬((Rt.toNat = Rn.toNat ∨ Rt2.toNat = Rn.toNat) ∧ Rn.toNat ≠ 31)) :
    (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 0#1 2#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 64 .MemOp_STORE Rn.toNat false (sign_extend imm7 64 <<< 3) false
        false false Rt.toNat Rt2.toNat true false true).run st := by
  unfold decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx
  cfg_simp [undefined_Constraint, run_internal_pick, hnt]
  all_goals first | rfl | skip

theorem run_dec_pair_3_2_1 (Rt Rn Rt2 : BitVec 5) (imm7 : BitVec 7) (st : SState) (hnt : ¬((Rt.toNat = Rn.toNat ∨ Rt2.toNat = Rn.toNat) ∧ Rn.toNat ≠ 31)) (hne : Rt.toNat ≠ Rt2.toNat) :
    (decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 1#1 2#2).run st =
      (execute_aarch64_instrs_memory_pair_general_post_idx 64 .MemOp_LOAD Rn.toNat false (sign_extend imm7 64 <<< 3) false
        false false Rt.toNat Rt2.toNat true false true).run st := by
  unfold decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx
  cfg_simp [undefined_Constraint, run_internal_pick, hnt, hne]
  all_goals first | rfl | skip

open Janus.Arm64 in
theorem decode_ldstPair {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 5) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h25 : (w / 2 ^ 25) % 2 = 0) (hidx : (w / 2 ^ 23) % 4 ≠ 0) (hopc : (w / 2 ^ 30) % 4 ≠ 3)
    (hsl : ¬((w / 2 ^ 30) % 4 = 1 ∧ (w / 2 ^ 22) % 2 = 0))
    (hLt : (w / 2 ^ 22) % 2 = 1 → w % 32 ≠ (w / 2 ^ 10) % 32)
    (hwb : (w / 2 ^ 23) % 4 ≠ 2 → ¬((w % 32 = (w / 2 ^ 5) % 32 ∨ (w / 2 ^ 10) % 32 = (w / 2 ^ 5) % 32) ∧
      (w / 2 ^ 5) % 32 ≠ 31)) :
    decode w = some (.ldstPair (bits w 31 30)
      (if bits w 24 23 = 1 then PairMode.post else if bits w 24 23 = 2 then .offset else .pre) (bit w 22)
      (bits w 21 15) (bits w 14 10) (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ w ≥ 2 ^ 32 := by omega
  have e2 : bits w 28 25 = 4 ∨ bits w 28 25 = 6 := by simp only [bits_def]; omega
  have e3 : bit w 26 = false := by simp only [bit_def]; simp; omega
  have e4 : bits w 29 27 = 5 := by simp only [bits_def]; omega
  have e5 : ¬ bits w 24 23 = 0 := by simp only [bits_def]; omega
  have e6 : ¬ bits w 31 30 = 3 := by simp only [bits_def]; omega
  have e7 : (decide (bits w 31 30 = 1) && !bit w 22) = false := by
    simp only [bits_def, bit_def]; simp; omega
  have e8 : (bit w 22 && bits w 4 0 == bits w 14 10) = false := by
    simp only [bits_def, bit_def]; simp; omega
  have e9 : (decide (bits w 24 23 ≠ 2) && (bits w 4 0 == bits w 9 5 || bits w 14 10 == bits w 9 5) &&
      decide (bits w 9 5 ≠ 31)) = false := by
    simp only [bits_def, bit_def]; simp; omega
  rcases e2 with e2 | e2 <;>
  simp only [decode, e1, e2, if_false, decodeLdSt, e3, e4, e5, e6, e7, e8, e9, Bool.false_eq_true, ite_false,
    ite_true] <;> simp

theorem pair_offset {w : Nat} (hw : w < 2 ^ 32) (sc : Nat) :
    sign_extend (fld w 15 7) 64 <<< sc = (BitVec.ofNat 7 (Janus.Arm64.bits w 21 15)).signExtend 64 <<< sc := by
  have : fld w 15 7 = BitVec.ofNat 7 (Janus.Arm64.bits w 21 15) := by
    apply BitVec.eq_of_toNat_eq; rw [fld_toNat w 15 7 hw, bits_eq_fld w 21 15 hw, fld_toNat w 15 7 hw]; simp
  rw [this]; rfl

theorem writeZR_pc (js : Janus.Arm64.State) (d : Nat) (v : BitVec 64) : (js.writeZR d v).pc = js.pc := by
  unfold Janus.Arm64.State.writeZR; split <;> rfl

theorem memIndexed_pc_pair {js js1 : Janus.Arm64.State} {rn : Nat} {offset : BitVec 64} {post wb : Bool}
    {opc rt rt2 : Nat} {L : Bool}
    (hj : Janus.Arm64.memIndexed js rn offset post wb (fun s a => Janus.Arm64.memPair s opc L rt rt2 a) = .ok js1) :
    js1.pc = js.pc := by
  unfold Janus.Arm64.memIndexed at hj
  split at hj
  · cases hj
  · simp only at hj
    split at hj
    · cases hj
    · next js2 hs2 =>
      have : js2.pc = js.pc := by
        cases L
        · obtain ⟨_, _, rfl⟩ := memPair_store hs2; rfl
        · obtain ⟨_, _, rfl⟩ := memPair_load hs2
          rw [writeZR_pc, writeZR_pc]
      cases hj; split
      · rw [← this]; unfold Janus.Arm64.State.writeSP; split <;> rfl
      · exact this

theorem run_DecodeA64_LS' {w : Nat} (hw : w < 2 ^ 32) (h27 : (w / 2 ^ 27) % 2 = 1) (h25 : (w / 2 ^ 25) % 2 = 0) (pc : Int) (s : SState) :
    (__DecodeA64 pc (BitVec.ofNat 32 w)).run s = (__DecodeA64_LoadStore pc (BitVec.ofNat 32 w)).run s := by
  have e : ∀ c : Nat, c < 4 → (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 25 == BitVec.ofNat 4 c) = false := by
    intro c hc
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 26 == (0b100#3 : BitVec 3)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 26 == (0b101#3 : BitVec 3)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have e7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 27 27 == (1#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have e8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 25 25 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64]
  simp only [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e5, e6, e7, e8,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.false_eq_true, ite_false, ite_true]

set_option maxHeartbeats 16000000 in
theorem pair_case {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 5) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h25 : (w / 2 ^ 25) % 2 = 0)
    {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) {opc ds : Nat} {L : Bool} {k : Int} {sgn post wb tc : Bool} {mem : MemOp}
    (hkind : (L = true ∧ mem = .MemOp_LOAD ∧ sgn = false ∧ ((opc = 0 ∧ ds = 32) ∨ (opc = 2 ∧ ds = 64))) ∨
      (L = true ∧ mem = .MemOp_LOAD ∧ sgn = true ∧ opc = 1 ∧ ds = 32) ∨
      (L = false ∧ mem = .MemOp_STORE ∧ sgn = false ∧ ((opc = 0 ∧ ds = 32) ∨ (opc = 2 ∧ ds = 64))))
    (hchain : ∀ st : SState, st.regs.get? .SEE = some (-1) →
      (__DecodeA64_LoadStore (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run st =
        (execute_aarch64_instrs_memory_pair_general_post_idx ds mem (fld w 5 5).toNat false
          (sign_extend (fld w 15 7) 64 <<< (2 + opc / 2)) post false sgn (fld w 0 5).toNat (fld w 10 5).toNat tc
          false wb).run (st.set .SEE k))
    (hx : Janus.Arm64.memIndexed js (Janus.Arm64.bits w 9 5)
      ((BitVec.ofNat 7 (Janus.Arm64.bits w 21 15)).signExtend 64 <<< (2 + opc / 2)) post wb
      (fun s a => Janus.Arm64.memPair s opc L (Janus.Arm64.bits w 4 0) (Janus.Arm64.bits w 14 10) a) = .ok js1) :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js1.next s' ∧ MemRel js1.next.mem s' ∧
      LinuxEL0Config s' := by
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hrt2 : (fld w 10 5).toNat = Janus.Arm64.bits w 14 10 := (bits_eq_fld w 14 10 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have ht232 : Janus.Arm64.bits w 14 10 < 32 := by simp only [bits_def]; omega
  obtain ⟨hR, hM, hC, hT⟩ := entry_facts h hm hc w k
  have hpc := memIndexed_pc_pair hx
  have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      (execute_aarch64_instrs_memory_pair_general_post_idx ds mem (Janus.Arm64.bits w 9 5) false
          ((BitVec.ofNat 7 (Janus.Arm64.bits w 21 15)).signExtend 64 <<< (2 + opc / 2)) post false sgn
          (Janus.Arm64.bits w 4 0) (Janus.Arm64.bits w 14 10) tc false wb).run (entrySt s w k) := by
    rw [run_DecodeA64_LS' hw (by omega) (by omega), hchain _ (see_entry s _), hrn, hrt, hrt2,
      pair_offset hw]
  rcases hkind with ⟨rfl, rfl, rfl, hc'⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, hc'⟩
  · obtain ⟨s2, hr2, hrel, hmem, hst⟩ := run_exec_pair_load hR hM hC hU hT hc' hn32 ht32 ht232 _ _ _ tc hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · obtain ⟨s2, hr2, hrel, hmem, hst⟩ := run_exec_ldpsw hR hM hC hU hT hn32 ht32 ht232 _ _ _ tc hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · obtain ⟨s2, hr2, hrel, hmem, hg, _⟩ := run_exec_pair_store hR hM hC hU hT hc' hn32 ht32 ht232 _ _ _ tc hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hg hpc
    exact ⟨_, e1, e2, hmem, e3⟩

/-- **LDP/STP/LDPSW (general registers)**: for every word `opc 101 0 idx L imm7 Rt2 Rn Rt` with
`idx ≠ 00` (not LDNP/STNP), `opc ≠ 11`, not `opc = 01` with `L = 0` (STGP), `Rt ≠ Rt2` for loads,
and, with write-back, `Rn ∉ {Rt, Rt2}` unless `Rn = 31` (what Janus decodes), and every related
pair of states under `LinuxEL0Config` and `UserMapped`, whenever Janus steps the word the
generated ASL step completes in a related state, with Janus' memory related to the ASL's. -/
theorem ldstPair_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 5) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h25 : (w / 2 ^ 25) % 2 = 0) (hidx : (w / 2 ^ 23) % 4 ≠ 0) (hopc : (w / 2 ^ 30) % 4 ≠ 3)
    (hsl : ¬((w / 2 ^ 30) % 4 = 1 ∧ (w / 2 ^ 22) % 2 = 0))
    (hLt : (w / 2 ^ 22) % 2 = 1 → w % 32 ≠ (w / 2 ^ 10) % 32)
    (hwb : (w / 2 ^ 23) % 4 ≠ 2 → ¬((w % 32 = (w / 2 ^ 5) % 32 ∨ (w / 2 ^ 10) % 32 = (w / 2 ^ 5) % 32) ∧
      (w / 2 ^ 5) % 32 ≠ 31))
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_ldstPair hw h0 h1 h25 hidx hopc hsl hLt hwb)] at hj
  simp only [Janus.Arm64.exec] at hj
  have hrn' : (fld w 5 5).toNat = (w / 2 ^ 5) % 32 := by rw [fld_toNat w 5 5 hw]
  have hrt' : (fld w 0 5).toNat = w % 32 := by rw [fld_toNat w 0 5 hw]; simp
  have hrt2' : (fld w 10 5).toNat = (w / 2 ^ 10) % 32 := by rw [fld_toNat w 10 5 hw]
  have hb2423 : Janus.Arm64.bits w 24 23 = (w / 2 ^ 23) % 4 := by simp only [bits_def]
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  have hb22 : Janus.Arm64.bit w 22 = ((w / 2 ^ 22) % 2 == 1) := by simp only [bit_def]
  rw [hb2423, hb3130, hb22] at hj
  rcases (show (w / 2 ^ 23) % 4 = 1 ∨ (w / 2 ^ 23) % 4 = 2 ∨ (w / 2 ^ 23) % 4 = 3 by omega) with e1 | e1 | e1 <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 by omega) with e2 | e2 | e2 <;>
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with hL | hL <;>
  rw [e1, e2] at hj <;> rw [hL] at hsl hLt hj
  · -- idx 1, opc 0, L 0
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 615) (ds := 32) (sgn := false) (post := true) (wb := true) (tc := true)
        (mem := .MemOp_STORE) hw h0 h1 h25 h hm hc hU (Or.inr (Or.inr ⟨rfl, rfl, rfl, by decide⟩)) (fun st hst => by
          rw [run_LS_pair_1_0_0 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_1_0_0 _ _ _ _ _ (by rw [hrt', hrn', hrt2']; exact hwb (by omega))) hx
  · -- idx 1, opc 0, L 1
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 609) (ds := 32) (sgn := false) (post := true) (wb := true) (tc := true)
        (mem := .MemOp_LOAD) hw h0 h1 h25 h hm hc hU (Or.inl ⟨rfl, rfl, rfl, by decide⟩) (fun st hst => by
          rw [run_LS_pair_1_0_1 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_1_0_1 _ _ _ _ _ (by rw [hrt', hrn', hrt2']; exact hwb (by omega)) (by rw [hrt', hrt2']; exact hLt rfl)) hx
  · exact absurd ⟨e2, rfl⟩ hsl
  · -- idx 1, opc 1, L 1
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 612) (ds := 32) (sgn := true) (post := true) (wb := true) (tc := true)
        (mem := .MemOp_LOAD) hw h0 h1 h25 h hm hc hU (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)) (fun st hst => by
          rw [run_LS_pair_1_1_1 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_1_1_1 _ _ _ _ _ (by rw [hrt', hrn', hrt2']; exact hwb (by omega)) (by rw [hrt', hrt2']; exact hLt rfl)) hx
  · -- idx 1, opc 2, L 0
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 615) (ds := 64) (sgn := false) (post := true) (wb := true) (tc := true)
        (mem := .MemOp_STORE) hw h0 h1 h25 h hm hc hU (Or.inr (Or.inr ⟨rfl, rfl, rfl, by decide⟩)) (fun st hst => by
          rw [run_LS_pair_1_2_0 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_1_2_0 _ _ _ _ _ (by rw [hrt', hrn', hrt2']; exact hwb (by omega))) hx
  · -- idx 1, opc 2, L 1
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 609) (ds := 64) (sgn := false) (post := true) (wb := true) (tc := true)
        (mem := .MemOp_LOAD) hw h0 h1 h25 h hm hc hU (Or.inl ⟨rfl, rfl, rfl, by decide⟩) (fun st hst => by
          rw [run_LS_pair_1_2_1 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_1_2_1 _ _ _ _ _ (by rw [hrt', hrn', hrt2']; exact hwb (by omega)) (by rw [hrt', hrt2']; exact hLt rfl)) hx
  · -- idx 2, opc 0, L 0
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 617) (ds := 32) (sgn := false) (post := false) (wb := false) (tc := ((fld w 5 5).toNat != 31))
        (mem := .MemOp_STORE) hw h0 h1 h25 h hm hc hU (Or.inr (Or.inr ⟨rfl, rfl, rfl, by decide⟩)) (fun st hst => by
          rw [run_LS_pair_2_0_0 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_2_0_0 _ _ _ _ _ ) hx
  · -- idx 2, opc 0, L 1
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 611) (ds := 32) (sgn := false) (post := false) (wb := false) (tc := ((fld w 5 5).toNat != 31))
        (mem := .MemOp_LOAD) hw h0 h1 h25 h hm hc hU (Or.inl ⟨rfl, rfl, rfl, by decide⟩) (fun st hst => by
          rw [run_LS_pair_2_0_1 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_2_0_1 _ _ _ _ _ (by rw [hrt', hrt2']; exact hLt rfl)) hx
  · exact absurd ⟨e2, rfl⟩ hsl
  · -- idx 2, opc 1, L 1
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 614) (ds := 32) (sgn := true) (post := false) (wb := false) (tc := ((fld w 5 5).toNat != 31))
        (mem := .MemOp_LOAD) hw h0 h1 h25 h hm hc hU (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)) (fun st hst => by
          rw [run_LS_pair_2_1_1 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_2_1_1 _ _ _ _ _ (by rw [hrt', hrt2']; exact hLt rfl)) hx
  · -- idx 2, opc 2, L 0
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 617) (ds := 64) (sgn := false) (post := false) (wb := false) (tc := ((fld w 5 5).toNat != 31))
        (mem := .MemOp_STORE) hw h0 h1 h25 h hm hc hU (Or.inr (Or.inr ⟨rfl, rfl, rfl, by decide⟩)) (fun st hst => by
          rw [run_LS_pair_2_2_0 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_2_2_0 _ _ _ _ _ ) hx
  · -- idx 2, opc 2, L 1
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 611) (ds := 64) (sgn := false) (post := false) (wb := false) (tc := ((fld w 5 5).toNat != 31))
        (mem := .MemOp_LOAD) hw h0 h1 h25 h hm hc hU (Or.inl ⟨rfl, rfl, rfl, by decide⟩) (fun st hst => by
          rw [run_LS_pair_2_2_1 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_2_2_1 _ _ _ _ _ (by rw [hrt', hrt2']; exact hLt rfl)) hx
  · -- idx 3, opc 0, L 0
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 616) (ds := 32) (sgn := false) (post := false) (wb := true) (tc := true)
        (mem := .MemOp_STORE) hw h0 h1 h25 h hm hc hU (Or.inr (Or.inr ⟨rfl, rfl, rfl, by decide⟩)) (fun st hst => by
          rw [run_LS_pair_3_0_0 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_3_0_0 _ _ _ _ _ (by rw [hrt', hrn', hrt2']; exact hwb (by omega))) hx
  · -- idx 3, opc 0, L 1
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 610) (ds := 32) (sgn := false) (post := false) (wb := true) (tc := true)
        (mem := .MemOp_LOAD) hw h0 h1 h25 h hm hc hU (Or.inl ⟨rfl, rfl, rfl, by decide⟩) (fun st hst => by
          rw [run_LS_pair_3_0_1 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_3_0_1 _ _ _ _ _ (by rw [hrt', hrn', hrt2']; exact hwb (by omega)) (by rw [hrt', hrt2']; exact hLt rfl)) hx
  · exact absurd ⟨e2, rfl⟩ hsl
  · -- idx 3, opc 1, L 1
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 613) (ds := 32) (sgn := true) (post := false) (wb := true) (tc := true)
        (mem := .MemOp_LOAD) hw h0 h1 h25 h hm hc hU (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)) (fun st hst => by
          rw [run_LS_pair_3_1_1 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_3_1_1 _ _ _ _ _ (by rw [hrt', hrn', hrt2']; exact hwb (by omega)) (by rw [hrt', hrt2']; exact hLt rfl)) hx
  · -- idx 3, opc 2, L 0
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 616) (ds := 64) (sgn := false) (post := false) (wb := true) (tc := true)
        (mem := .MemOp_STORE) hw h0 h1 h25 h hm hc hU (Or.inr (Or.inr ⟨rfl, rfl, rfl, by decide⟩)) (fun st hst => by
          rw [run_LS_pair_3_2_0 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_3_2_0 _ _ _ _ _ (by rw [hrt', hrn', hrt2']; exact hwb (by omega))) hx
  · -- idx 3, opc 2, L 1
    simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl, ite_true, ite_false,
      Bool.false_eq_true] at hj
    split at hj
    · cases hj
    · next js1 hx =>
      cases hj
      exact pair_case (k := 610) (ds := 64) (sgn := false) (post := false) (wb := true) (tc := true)
        (mem := .MemOp_LOAD) hw h0 h1 h25 h hm hc hU (Or.inl ⟨rfl, rfl, rfl, by decide⟩) (fun st hst => by
          rw [run_LS_pair_3_2_1 hw h0 h1 h25 e1 (by omega) e2 hst,
            show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
            show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
          exact run_dec_pair_3_2_1 _ _ _ _ _ (by rw [hrt', hrn', hrt2']; exact hwb (by omega)) (by rw [hrt', hrt2']; exact hLt rfl)) hx

end JanusASL.Proofs
