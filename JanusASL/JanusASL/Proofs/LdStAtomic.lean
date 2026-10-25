import JanusASL.Proofs.LdStExcl
import JanusASL.Proofs.MemAtomic

/-! # Proved: LSE atomics LD<op> (LDADD, LDCLR, LDEOR, LDSET, LDSMAX, LDSMIN, LDUMAX, LDUMIN) and SWP -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- Janus' atomic operation as the ASL's `MemAtomicOp`. -/
def aslOpOf : Janus.Arm64.AtomicOp → MemAtomicOp
  | .add => .MemAtomicOp_ADD
  | .clr => .MemAtomicOp_BIC
  | .eor => .MemAtomicOp_EOR
  | .set => .MemAtomicOp_ORR
  | .smax => .MemAtomicOp_SMAX
  | .smin => .MemAtomicOp_SMIN
  | .umax => .MemAtomicOp_UMAX
  | .umin => .MemAtomicOp_UMIN
  | .swp => .MemAtomicOp_SWP

theorem isub_int {k : Nat} (hk : 0 < k) (z : Int) :
    (BitVec.setWidth k (integer_subrange z ((k : Int) - 1) 0)) = BitVec.ofInt k z := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  apply BitVec.eq_of_toNat_eq
  have e : (((n + 1 : Nat) : Int) - 1 - 0 + 1).toNat = n + 1 := by omega
  simp only [integer_subrange, Sail.get_slice_int, BitVec.extractLsb', BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofInt, e]
  have e2 : ((((n + 1 : Nat) : Int) - 1).toNat - Int.toNat 0 + 1) = n + 1 := by omega
  rw [e2, show Int.toNat 0 = 0 from rfl, Nat.shiftRight_zero, Nat.zero_add, Nat.mod_mod]
  have hd : ((2 : Int) ^ (n + 1)) ∣ (2 : Int) ^ (n + 1 + 1) := ⟨2, by rw [Int.pow_succ]⟩
  have h1 : z % ↑(2 ^ (n + 1) : Nat) = (z % ↑(2 ^ (n + 1 + 1) : Nat)) % ↑(2 ^ (n + 1) : Nat) := by
    push_cast; exact (Int.emod_emod_of_dvd z hd).symm
  rw [h1]
  have h0 : 0 ≤ z % ↑(2 ^ (n + 1 + 1) : Nat) := Int.emod_nonneg _ (by have := Nat.two_pow_pos (n + 1 + 1); omega)
  rw [Int.toNat_emod h0 (Int.natCast_nonneg _)]
  simp only [Int.toNat_natCast, Nat.mod_mod]


theorem aslAtomicNew_janus {k : Nat} (hk : 0 < k) (op : Janus.Arm64.AtomicOp) (cmp old v : BitVec k) :
    aslAtomicNew (aslOpOf op) cmp old v = (false, Janus.Arm64.atomicOp op old v) := by
  cases op <;> simp only [aslOpOf, aslAtomicNew, Janus.Arm64.atomicOp, isub_int hk]
  all_goals congr 1
  all_goals split
  all_goals first
    | (rw [Int.max_eq_right (by omega)]; simp)
    | (rw [Int.max_eq_left (by omega)]; simp)
    | (rw [Int.min_eq_left (by omega)]; simp)
    | (rw [Int.min_eq_right (by omega)]; simp)

theorem run_CreateAccDescAtomicOp {s : SState} (h : LinuxEL0Config s) (op : MemAtomicOp) (a r tc : Bool) :
    (CreateAccDescAtomicOp op a r tc).run s = .ok { atomAcc op a r with tagchecked := tc } s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  obtain ⟨tm, htm, htd⟩ := h.tstate
  cfg_simp [CreateAccDescAtomicOp, NewAccDesc, undefined_AccessDescriptor, run_readReg hp, he, run_SecurityStateAtEL0 h,
    run_GenMPAMcurEL h, HaveTME, run_IsFeatureImplemented h, run_readReg htm, htd, atomAcc, gprAcc, run_internal_pick,
    undefined_AccessType, undefined_SecurityState, undefined_MemAtomicOp, undefined_CacheOp, undefined_CacheOpScope,
    undefined_CacheType, undefined_VARange, undefined_MPAMinfo, undefined_PARTIDspaceType, EL0]

/-- Janus' memory after an LD<op>/SWP at `base`. -/
def atomMem (js : Janus.Arm64.State) (size : Nat) (op : Janus.Arm64.AtomicOp) (rs : Nat) (base : BitVec 64) :
    Janus.Arm64.Memory :=
  js.mem.writeLE base.toNat (2 ^ size)
    (Janus.Arm64.atomicOp op (BitVec.ofNat (8 * 2 ^ size) (js.mem.readLE base.toNat (2 ^ size)))
      (js.getX (8 * 2 ^ size) rs)).toNat

theorem execAtomic_ok {js js1 : Janus.Arm64.State} {size rs rn rt : Nat} {op : Janus.Arm64.AtomicOp}
    (h : Janus.Arm64.execAtomic js size op rs rn rt = .ok js1) :
    ∃ base, Janus.Arm64.baseAddr js rn = .ok base ∧ base.toNat % 2 ^ size = 0 ∧
      js.mem.accessible base.toNat (2 ^ size) true = true ∧
      js1 = ({ js with mem := atomMem js size op rs base }.writeZR rt
        (BitVec.ofNat 64 (js.mem.readLE base.toNat (2 ^ size)))).next := by
  unfold Janus.Arm64.execAtomic at h
  split at h
  · cases h
  · next base hb =>
    simp only at h
    split at h
    · cases h
    · next hal =>
      split at h
      · cases h
      · next v hl =>
        obtain ⟨_, rfl⟩ := load_ok hl
        split at h
        · cases h
        · next m hs =>
          obtain ⟨ha, rfl⟩ := store_ok hs
          cases h
          exact ⟨base, hb, by omega, ha, rfl⟩

set_option maxHeartbeats 16000000 in
theorem run_exec_atomic32 {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {op : Janus.Arm64.AtomicOp}
    {rn rt rs : Nat} (hn : rn < 32) (ht : rt < 32) (hrs : rs < 32) (acq rel isl tc : Bool)
    (hj : Janus.Arm64.execAtomic js 2 op rs rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_atomicops_ld acq 32 isl rn (aslOpOf op) 32 rel rs rt tc).run s = .ok () s' ∧
      Rel js2 s' ∧ MemRel js2.mem s' ∧ GFrame s s' := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execAtomic_ok hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat true := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hX := run_X_read_w h hrs (w := 32) (by decide)
  have hMA := run_MemAtomic32 hc hm (aslOpOf op) acq rel tc base
    (fun al sz => hU.trans_ord s hf base true al sz _ (Or.inr (Or.inr (Or.inr ⟨rfl, _, _, _, rfl⟩))) hr0)
    hal hacc (hU.nodev _ hr0.read) 0#32 (BitVec.setWidth 32 (js.readZR rs))
  rw [aslAtomicNew_janus (by decide)] at hMA
  simp only [Bool.false_eq_true, ite_false] at hMA
  have hcr := run_CreateAccDescAtomicOp hc (aslOpOf op) acq rel tc
  -- the state after the read-modify-write
  let new := Janus.Arm64.atomicOp op (BitVec.ofNat 32 (js.mem.readLE base.toNat 4)) (BitVec.setWidth 32 (js.readZR rs))
  let s1 := storeSt s base.toNat (Int.ediv 32 8).toNat (BitVec.setWidth (8 * (Int.ediv 32 8).toNat) new)
  have hst : Stored s s1 base.toNat 4 new.toNat := by
    have := stored_storeSt s base.toNat (Int.ediv 32 8).toNat (BitVec.setWidth (8 * (Int.ediv 32 8).toNat) new)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by exact new.isLt)] at this
    exact this
  have hjm : atomMem js 2 op rs base = js.mem.writeLE base.toNat 4 new.toNat := by
    simp [atomMem, new, Janus.Arm64.State.getX]
  have hm1 : MemRel (atomMem js 2 op rs base) s1 := by
    rw [hjm]; exact hm.store hst rfl
  have hr1 := h.mem_update hst.regs (atomMem js 2 op rs base)
  have hc1 : LinuxEL0Config s1 := hc.stored hst
  obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r hr1 ht (N := 32) (by decide)
    (Sail.BitVec.zeroExtend (BitVec.ofNat 32 (js.mem.readLE base.toNat 4)) 32)
  have hval : (Sail.BitVec.zeroExtend (BitVec.ofNat 32 (js.mem.readLE base.toNat 4)) 32).setWidth 64 =
      BitVec.ofNat 64 (js.mem.readLE base.toNat 4) := by
    apply BitVec.eq_of_toNat_eq; have := readLE_lt js.mem base.toNat 4; simp [Sail.BitVec.zeroExtend] <;> omega
  simp only [Janus.Arm64.State.setX, hval] at hr2
  have hc2 := hc1.rstep hst2
  try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hMA
  refine ⟨_, if rt = 31 then s1 else s2, rfl, writeZR_pc _ _ _, ?_, ?_, ?_, ?_⟩
  · unfold execute_aarch64_instrs_memory_atomicops_ld
    by_cases h31 : rt = 31
    · subst h31
      cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, spe_storeSt hc]
      all_goals simp only [s1, new, Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have hne : ((rt : Int) != 31) = true := by simp; omega
      simp only [s1, new] at hx2 hc2
      try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hx2 hc2
      cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, h31, hne, hx2,
        run_readReg hc2.speInFlight]
  · split
    · next h31 => subst h31; simpa [Janus.Arm64.State.writeZR] using hr1
    · exact hr2
  · rw [writeZR_mem]; split
    · exact hm1
    · exact hm1.rstep hst2
  · intro r g1 g2
    split
    · show s1.regs.get? r = s.regs.get? r; rw [hst.regs]
    · rw [hst2.regs r g1 g2]; show s1.regs.get? r = s.regs.get? r; rw [hst.regs]

set_option maxHeartbeats 16000000 in
theorem run_exec_atomic8 {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {op : Janus.Arm64.AtomicOp}
    {rn rt rs : Nat} (hn : rn < 32) (ht : rt < 32) (hrs : rs < 32) (acq rel isl tc : Bool)
    (hj : Janus.Arm64.execAtomic js 0 op rs rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_atomicops_ld acq 8 isl rn (aslOpOf op) 32 rel rs rt tc).run s = .ok () s' ∧
      Rel js2 s' ∧ MemRel js2.mem s' ∧ GFrame s s' := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execAtomic_ok hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat true := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hX := run_X_read_w h hrs (w := 8) (by decide)
  have hMA := run_MemAtomic8 hc hm (aslOpOf op) acq rel tc base
    (fun al sz => hU.trans_ord s hf base true al sz _ (Or.inr (Or.inr (Or.inr ⟨rfl, _, _, _, rfl⟩))) hr0)
    hal hacc (hU.nodev _ hr0.read) 0#8 (BitVec.setWidth 8 (js.readZR rs))
  rw [aslAtomicNew_janus (by decide)] at hMA
  simp only [Bool.false_eq_true, ite_false] at hMA
  have hcr := run_CreateAccDescAtomicOp hc (aslOpOf op) acq rel tc
  -- the state after the read-modify-write
  let new := Janus.Arm64.atomicOp op (BitVec.ofNat 8 (js.mem.readLE base.toNat 1)) (BitVec.setWidth 8 (js.readZR rs))
  let s1 := storeSt s base.toNat (Int.ediv 8 8).toNat (BitVec.setWidth (8 * (Int.ediv 8 8).toNat) new)
  have hst : Stored s s1 base.toNat 1 new.toNat := by
    have := stored_storeSt s base.toNat (Int.ediv 8 8).toNat (BitVec.setWidth (8 * (Int.ediv 8 8).toNat) new)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by exact new.isLt)] at this
    exact this
  have hjm : atomMem js 0 op rs base = js.mem.writeLE base.toNat 1 new.toNat := by
    simp [atomMem, new, Janus.Arm64.State.getX]
  have hm1 : MemRel (atomMem js 0 op rs base) s1 := by
    rw [hjm]; exact hm.store hst rfl
  have hr1 := h.mem_update hst.regs (atomMem js 0 op rs base)
  have hc1 : LinuxEL0Config s1 := hc.stored hst
  obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r hr1 ht (N := 32) (by decide)
    (Sail.BitVec.zeroExtend (BitVec.ofNat 8 (js.mem.readLE base.toNat 1)) 32)
  have hval : (Sail.BitVec.zeroExtend (BitVec.ofNat 8 (js.mem.readLE base.toNat 1)) 32).setWidth 64 =
      BitVec.ofNat 64 (js.mem.readLE base.toNat 1) := by
    apply BitVec.eq_of_toNat_eq; have := readLE_lt js.mem base.toNat 1; simp [Sail.BitVec.zeroExtend] <;> omega
  simp only [Janus.Arm64.State.setX, hval] at hr2
  have hc2 := hc1.rstep hst2
  try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hMA
  refine ⟨_, if rt = 31 then s1 else s2, rfl, writeZR_pc _ _ _, ?_, ?_, ?_, ?_⟩
  · unfold execute_aarch64_instrs_memory_atomicops_ld
    by_cases h31 : rt = 31
    · subst h31
      cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, spe_storeSt hc]
      all_goals simp only [s1, new, Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have hne : ((rt : Int) != 31) = true := by simp; omega
      simp only [s1, new] at hx2 hc2
      try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hx2 hc2
      cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, h31, hne, hx2,
        run_readReg hc2.speInFlight]
  · split
    · next h31 => subst h31; simpa [Janus.Arm64.State.writeZR] using hr1
    · exact hr2
  · rw [writeZR_mem]; split
    · exact hm1
    · exact hm1.rstep hst2
  · intro r g1 g2
    split
    · show s1.regs.get? r = s.regs.get? r; rw [hst.regs]
    · rw [hst2.regs r g1 g2]; show s1.regs.get? r = s.regs.get? r; rw [hst.regs]

set_option maxHeartbeats 16000000 in
theorem run_exec_atomic16 {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {op : Janus.Arm64.AtomicOp}
    {rn rt rs : Nat} (hn : rn < 32) (ht : rt < 32) (hrs : rs < 32) (acq rel isl tc : Bool)
    (hj : Janus.Arm64.execAtomic js 1 op rs rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_atomicops_ld acq 16 isl rn (aslOpOf op) 32 rel rs rt tc).run s = .ok () s' ∧
      Rel js2 s' ∧ MemRel js2.mem s' ∧ GFrame s s' := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execAtomic_ok hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat true := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hX := run_X_read_w h hrs (w := 16) (by decide)
  have hMA := run_MemAtomic16 hc hm (aslOpOf op) acq rel tc base
    (fun al sz => hU.trans_ord s hf base true al sz _ (Or.inr (Or.inr (Or.inr ⟨rfl, _, _, _, rfl⟩))) hr0)
    hal hacc (hU.nodev _ hr0.read) 0#16 (BitVec.setWidth 16 (js.readZR rs))
  rw [aslAtomicNew_janus (by decide)] at hMA
  simp only [Bool.false_eq_true, ite_false] at hMA
  have hcr := run_CreateAccDescAtomicOp hc (aslOpOf op) acq rel tc
  -- the state after the read-modify-write
  let new := Janus.Arm64.atomicOp op (BitVec.ofNat 16 (js.mem.readLE base.toNat 2)) (BitVec.setWidth 16 (js.readZR rs))
  let s1 := storeSt s base.toNat (Int.ediv 16 8).toNat (BitVec.setWidth (8 * (Int.ediv 16 8).toNat) new)
  have hst : Stored s s1 base.toNat 2 new.toNat := by
    have := stored_storeSt s base.toNat (Int.ediv 16 8).toNat (BitVec.setWidth (8 * (Int.ediv 16 8).toNat) new)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by exact new.isLt)] at this
    exact this
  have hjm : atomMem js 1 op rs base = js.mem.writeLE base.toNat 2 new.toNat := by
    simp [atomMem, new, Janus.Arm64.State.getX]
  have hm1 : MemRel (atomMem js 1 op rs base) s1 := by
    rw [hjm]; exact hm.store hst rfl
  have hr1 := h.mem_update hst.regs (atomMem js 1 op rs base)
  have hc1 : LinuxEL0Config s1 := hc.stored hst
  obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r hr1 ht (N := 32) (by decide)
    (Sail.BitVec.zeroExtend (BitVec.ofNat 16 (js.mem.readLE base.toNat 2)) 32)
  have hval : (Sail.BitVec.zeroExtend (BitVec.ofNat 16 (js.mem.readLE base.toNat 2)) 32).setWidth 64 =
      BitVec.ofNat 64 (js.mem.readLE base.toNat 2) := by
    apply BitVec.eq_of_toNat_eq; have := readLE_lt js.mem base.toNat 2; simp [Sail.BitVec.zeroExtend] <;> omega
  simp only [Janus.Arm64.State.setX, hval] at hr2
  have hc2 := hc1.rstep hst2
  try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hMA
  refine ⟨_, if rt = 31 then s1 else s2, rfl, writeZR_pc _ _ _, ?_, ?_, ?_, ?_⟩
  · unfold execute_aarch64_instrs_memory_atomicops_ld
    by_cases h31 : rt = 31
    · subst h31
      cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, spe_storeSt hc]
      all_goals simp only [s1, new, Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have hne : ((rt : Int) != 31) = true := by simp; omega
      simp only [s1, new] at hx2 hc2
      try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hx2 hc2
      cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, h31, hne, hx2,
        run_readReg hc2.speInFlight]
  · split
    · next h31 => subst h31; simpa [Janus.Arm64.State.writeZR] using hr1
    · exact hr2
  · rw [writeZR_mem]; split
    · exact hm1
    · exact hm1.rstep hst2
  · intro r g1 g2
    split
    · show s1.regs.get? r = s.regs.get? r; rw [hst.regs]
    · rw [hst2.regs r g1 g2]; show s1.regs.get? r = s.regs.get? r; rw [hst.regs]

set_option maxHeartbeats 16000000 in
theorem run_exec_atomic64 {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {op : Janus.Arm64.AtomicOp}
    {rn rt rs : Nat} (hn : rn < 32) (ht : rt < 32) (hrs : rs < 32) (acq rel isl tc : Bool)
    (hj : Janus.Arm64.execAtomic js 3 op rs rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_atomicops_ld acq 64 isl rn (aslOpOf op) 64 rel rs rt tc).run s = .ok () s' ∧
      Rel js2 s' ∧ MemRel js2.mem s' ∧ GFrame s s' := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execAtomic_ok hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat true := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hX := run_X_read_w h hrs (w := 64) (by decide)
  have hMA := run_MemAtomic64 hc hm (aslOpOf op) acq rel tc base
    (fun al sz => hU.trans_ord s hf base true al sz _ (Or.inr (Or.inr (Or.inr ⟨rfl, _, _, _, rfl⟩))) hr0)
    hal hacc (hU.nodev _ hr0.read) 0#64 (BitVec.setWidth 64 (js.readZR rs))
  rw [aslAtomicNew_janus (by decide)] at hMA
  simp only [Bool.false_eq_true, ite_false] at hMA
  have hcr := run_CreateAccDescAtomicOp hc (aslOpOf op) acq rel tc
  -- the state after the read-modify-write
  let new := Janus.Arm64.atomicOp op (BitVec.ofNat 64 (js.mem.readLE base.toNat 8)) (BitVec.setWidth 64 (js.readZR rs))
  let s1 := storeSt s base.toNat (Int.ediv 64 8).toNat (BitVec.setWidth (8 * (Int.ediv 64 8).toNat) new)
  have hst : Stored s s1 base.toNat 8 new.toNat := by
    have := stored_storeSt s base.toNat (Int.ediv 64 8).toNat (BitVec.setWidth (8 * (Int.ediv 64 8).toNat) new)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by exact new.isLt)] at this
    exact this
  have hjm : atomMem js 3 op rs base = js.mem.writeLE base.toNat 8 new.toNat := by
    simp [atomMem, new, Janus.Arm64.State.getX]
  have hm1 : MemRel (atomMem js 3 op rs base) s1 := by
    rw [hjm]; exact hm.store hst rfl
  have hr1 := h.mem_update hst.regs (atomMem js 3 op rs base)
  have hc1 : LinuxEL0Config s1 := hc.stored hst
  obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r hr1 ht (N := 64) (by decide)
    (Sail.BitVec.zeroExtend (BitVec.ofNat 64 (js.mem.readLE base.toNat 8)) 64)
  have hval : (Sail.BitVec.zeroExtend (BitVec.ofNat 64 (js.mem.readLE base.toNat 8)) 64).setWidth 64 =
      BitVec.ofNat 64 (js.mem.readLE base.toNat 8) := by
    apply BitVec.eq_of_toNat_eq; have := readLE_lt js.mem base.toNat 8; simp [Sail.BitVec.zeroExtend] <;> omega
  simp only [Janus.Arm64.State.setX, hval] at hr2
  have hc2 := hc1.rstep hst2
  try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hMA
  refine ⟨_, if rt = 31 then s1 else s2, rfl, writeZR_pc _ _ _, ?_, ?_, ?_, ?_⟩
  · unfold execute_aarch64_instrs_memory_atomicops_ld
    by_cases h31 : rt = 31
    · subst h31
      cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, spe_storeSt hc]
      all_goals simp only [s1, new, Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have hne : ((rt : Int) != 31) = true := by simp; omega
      simp only [s1, new] at hx2 hc2
      try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hx2 hc2
      cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, h31, hne, hx2,
        run_readReg hc2.speInFlight]
  · split
    · next h31 => subst h31; simpa [Janus.Arm64.State.writeZR] using hr1
    · exact hr2
  · rw [writeZR_mem]; split
    · exact hm1
    · exact hm1.rstep hst2
  · intro r g1 g2
    split
    · show s1.regs.get? r = s.regs.get? r; rw [hst.regs]
    · rw [hst2.regs r g1 g2]; show s1.regs.get? r = s.regs.get? r; rw [hst.regs]

set_option maxHeartbeats 16000000 in
theorem run_exec_swp8 {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s)
    {rn rt rs : Nat} (hn : rn < 32) (ht : rt < 32) (hrs : rs < 32) (acq rel tc : Bool)
    (hj : Janus.Arm64.execAtomic js 0 .swp rs rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_atomicops_swp acq 8 rn 32 rel rs rt tc).run s = .ok () s' ∧
      Rel js2 s' ∧ MemRel js2.mem s' ∧ GFrame s s' := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execAtomic_ok hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat true := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hX := run_X_read_w h hrs (w := 8) (by decide)
  have hMA := run_MemAtomic8 hc hm (aslOpOf .swp) acq rel tc base
    (fun al sz => hU.trans_ord s hf base true al sz _ (Or.inr (Or.inr (Or.inr ⟨rfl, _, _, _, rfl⟩))) hr0)
    hal hacc (hU.nodev _ hr0.read) 0#8 (BitVec.setWidth 8 (js.readZR rs))
  rw [aslAtomicNew_janus (by decide)] at hMA
  simp only [Bool.false_eq_true, ite_false] at hMA
  have hcr := run_CreateAccDescAtomicOp hc (aslOpOf .swp) acq rel tc
  -- the state after the read-modify-write
  let new := Janus.Arm64.atomicOp .swp (BitVec.ofNat 8 (js.mem.readLE base.toNat 1)) (BitVec.setWidth 8 (js.readZR rs))
  let s1 := storeSt s base.toNat (Int.ediv 8 8).toNat (BitVec.setWidth (8 * (Int.ediv 8 8).toNat) new)
  have hst : Stored s s1 base.toNat 1 new.toNat := by
    have := stored_storeSt s base.toNat (Int.ediv 8 8).toNat (BitVec.setWidth (8 * (Int.ediv 8 8).toNat) new)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by exact new.isLt)] at this
    exact this
  have hjm : atomMem js 0 .swp rs base = js.mem.writeLE base.toNat 1 new.toNat := by
    simp [atomMem, new, Janus.Arm64.State.getX]
  have hm1 : MemRel (atomMem js 0 .swp rs base) s1 := by
    rw [hjm]; exact hm.store hst rfl
  have hr1 := h.mem_update hst.regs (atomMem js 0 .swp rs base)
  have hc1 : LinuxEL0Config s1 := hc.stored hst
  obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r hr1 ht (N := 32) (by decide)
    (Sail.BitVec.zeroExtend (BitVec.ofNat 8 (js.mem.readLE base.toNat 1)) 32)
  have hval : (Sail.BitVec.zeroExtend (BitVec.ofNat 8 (js.mem.readLE base.toNat 1)) 32).setWidth 64 =
      BitVec.ofNat 64 (js.mem.readLE base.toNat 1) := by
    apply BitVec.eq_of_toNat_eq; have := readLE_lt js.mem base.toNat 1; simp [Sail.BitVec.zeroExtend] <;> omega
  simp only [Janus.Arm64.State.setX, hval] at hr2
  have hc2 := hc1.rstep hst2
  try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hMA
  simp only [aslOpOf] at hMA hcr
  refine ⟨_, s2, rfl, writeZR_pc _ _ _, ?_, hr2, by rw [writeZR_mem]; exact hm1.rstep hst2, fun r g1 g2 => ?_⟩
  · unfold execute_aarch64_instrs_memory_atomicops_swp
    simp only [s1, new] at hx2 hc2
    try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hx2 hc2
    cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, hx2, run_readReg hc2.speInFlight]
  · rw [hst2.regs r g1 g2]; show s1.regs.get? r = s.regs.get? r; rw [hst.regs]

set_option maxHeartbeats 16000000 in
theorem run_exec_swp16 {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s)
    {rn rt rs : Nat} (hn : rn < 32) (ht : rt < 32) (hrs : rs < 32) (acq rel tc : Bool)
    (hj : Janus.Arm64.execAtomic js 1 .swp rs rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_atomicops_swp acq 16 rn 32 rel rs rt tc).run s = .ok () s' ∧
      Rel js2 s' ∧ MemRel js2.mem s' ∧ GFrame s s' := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execAtomic_ok hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat true := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hX := run_X_read_w h hrs (w := 16) (by decide)
  have hMA := run_MemAtomic16 hc hm (aslOpOf .swp) acq rel tc base
    (fun al sz => hU.trans_ord s hf base true al sz _ (Or.inr (Or.inr (Or.inr ⟨rfl, _, _, _, rfl⟩))) hr0)
    hal hacc (hU.nodev _ hr0.read) 0#16 (BitVec.setWidth 16 (js.readZR rs))
  rw [aslAtomicNew_janus (by decide)] at hMA
  simp only [Bool.false_eq_true, ite_false] at hMA
  have hcr := run_CreateAccDescAtomicOp hc (aslOpOf .swp) acq rel tc
  -- the state after the read-modify-write
  let new := Janus.Arm64.atomicOp .swp (BitVec.ofNat 16 (js.mem.readLE base.toNat 2)) (BitVec.setWidth 16 (js.readZR rs))
  let s1 := storeSt s base.toNat (Int.ediv 16 8).toNat (BitVec.setWidth (8 * (Int.ediv 16 8).toNat) new)
  have hst : Stored s s1 base.toNat 2 new.toNat := by
    have := stored_storeSt s base.toNat (Int.ediv 16 8).toNat (BitVec.setWidth (8 * (Int.ediv 16 8).toNat) new)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by exact new.isLt)] at this
    exact this
  have hjm : atomMem js 1 .swp rs base = js.mem.writeLE base.toNat 2 new.toNat := by
    simp [atomMem, new, Janus.Arm64.State.getX]
  have hm1 : MemRel (atomMem js 1 .swp rs base) s1 := by
    rw [hjm]; exact hm.store hst rfl
  have hr1 := h.mem_update hst.regs (atomMem js 1 .swp rs base)
  have hc1 : LinuxEL0Config s1 := hc.stored hst
  obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r hr1 ht (N := 32) (by decide)
    (Sail.BitVec.zeroExtend (BitVec.ofNat 16 (js.mem.readLE base.toNat 2)) 32)
  have hval : (Sail.BitVec.zeroExtend (BitVec.ofNat 16 (js.mem.readLE base.toNat 2)) 32).setWidth 64 =
      BitVec.ofNat 64 (js.mem.readLE base.toNat 2) := by
    apply BitVec.eq_of_toNat_eq; have := readLE_lt js.mem base.toNat 2; simp [Sail.BitVec.zeroExtend] <;> omega
  simp only [Janus.Arm64.State.setX, hval] at hr2
  have hc2 := hc1.rstep hst2
  try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hMA
  simp only [aslOpOf] at hMA hcr
  refine ⟨_, s2, rfl, writeZR_pc _ _ _, ?_, hr2, by rw [writeZR_mem]; exact hm1.rstep hst2, fun r g1 g2 => ?_⟩
  · unfold execute_aarch64_instrs_memory_atomicops_swp
    simp only [s1, new] at hx2 hc2
    try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hx2 hc2
    cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, hx2, run_readReg hc2.speInFlight]
  · rw [hst2.regs r g1 g2]; show s1.regs.get? r = s.regs.get? r; rw [hst.regs]

set_option maxHeartbeats 16000000 in
theorem run_exec_swp32 {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s)
    {rn rt rs : Nat} (hn : rn < 32) (ht : rt < 32) (hrs : rs < 32) (acq rel tc : Bool)
    (hj : Janus.Arm64.execAtomic js 2 .swp rs rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_atomicops_swp acq 32 rn 32 rel rs rt tc).run s = .ok () s' ∧
      Rel js2 s' ∧ MemRel js2.mem s' ∧ GFrame s s' := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execAtomic_ok hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat true := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hX := run_X_read_w h hrs (w := 32) (by decide)
  have hMA := run_MemAtomic32 hc hm (aslOpOf .swp) acq rel tc base
    (fun al sz => hU.trans_ord s hf base true al sz _ (Or.inr (Or.inr (Or.inr ⟨rfl, _, _, _, rfl⟩))) hr0)
    hal hacc (hU.nodev _ hr0.read) 0#32 (BitVec.setWidth 32 (js.readZR rs))
  rw [aslAtomicNew_janus (by decide)] at hMA
  simp only [Bool.false_eq_true, ite_false] at hMA
  have hcr := run_CreateAccDescAtomicOp hc (aslOpOf .swp) acq rel tc
  -- the state after the read-modify-write
  let new := Janus.Arm64.atomicOp .swp (BitVec.ofNat 32 (js.mem.readLE base.toNat 4)) (BitVec.setWidth 32 (js.readZR rs))
  let s1 := storeSt s base.toNat (Int.ediv 32 8).toNat (BitVec.setWidth (8 * (Int.ediv 32 8).toNat) new)
  have hst : Stored s s1 base.toNat 4 new.toNat := by
    have := stored_storeSt s base.toNat (Int.ediv 32 8).toNat (BitVec.setWidth (8 * (Int.ediv 32 8).toNat) new)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by exact new.isLt)] at this
    exact this
  have hjm : atomMem js 2 .swp rs base = js.mem.writeLE base.toNat 4 new.toNat := by
    simp [atomMem, new, Janus.Arm64.State.getX]
  have hm1 : MemRel (atomMem js 2 .swp rs base) s1 := by
    rw [hjm]; exact hm.store hst rfl
  have hr1 := h.mem_update hst.regs (atomMem js 2 .swp rs base)
  have hc1 : LinuxEL0Config s1 := hc.stored hst
  obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r hr1 ht (N := 32) (by decide)
    (Sail.BitVec.zeroExtend (BitVec.ofNat 32 (js.mem.readLE base.toNat 4)) 32)
  have hval : (Sail.BitVec.zeroExtend (BitVec.ofNat 32 (js.mem.readLE base.toNat 4)) 32).setWidth 64 =
      BitVec.ofNat 64 (js.mem.readLE base.toNat 4) := by
    apply BitVec.eq_of_toNat_eq; have := readLE_lt js.mem base.toNat 4; simp [Sail.BitVec.zeroExtend] <;> omega
  simp only [Janus.Arm64.State.setX, hval] at hr2
  have hc2 := hc1.rstep hst2
  try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hMA
  simp only [aslOpOf] at hMA hcr
  refine ⟨_, s2, rfl, writeZR_pc _ _ _, ?_, hr2, by rw [writeZR_mem]; exact hm1.rstep hst2, fun r g1 g2 => ?_⟩
  · unfold execute_aarch64_instrs_memory_atomicops_swp
    simp only [s1, new] at hx2 hc2
    try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hx2 hc2
    cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, hx2, run_readReg hc2.speInFlight]
  · rw [hst2.regs r g1 g2]; show s1.regs.get? r = s.regs.get? r; rw [hst.regs]

set_option maxHeartbeats 16000000 in
theorem run_exec_swp64 {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s)
    {rn rt rs : Nat} (hn : rn < 32) (ht : rt < 32) (hrs : rs < 32) (acq rel tc : Bool)
    (hj : Janus.Arm64.execAtomic js 3 .swp rs rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_atomicops_swp acq 64 rn 64 rel rs rt tc).run s = .ok () s' ∧
      Rel js2 s' ∧ MemRel js2.mem s' ∧ GFrame s s' := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execAtomic_ok hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat true := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hX := run_X_read_w h hrs (w := 64) (by decide)
  have hMA := run_MemAtomic64 hc hm (aslOpOf .swp) acq rel tc base
    (fun al sz => hU.trans_ord s hf base true al sz _ (Or.inr (Or.inr (Or.inr ⟨rfl, _, _, _, rfl⟩))) hr0)
    hal hacc (hU.nodev _ hr0.read) 0#64 (BitVec.setWidth 64 (js.readZR rs))
  rw [aslAtomicNew_janus (by decide)] at hMA
  simp only [Bool.false_eq_true, ite_false] at hMA
  have hcr := run_CreateAccDescAtomicOp hc (aslOpOf .swp) acq rel tc
  -- the state after the read-modify-write
  let new := Janus.Arm64.atomicOp .swp (BitVec.ofNat 64 (js.mem.readLE base.toNat 8)) (BitVec.setWidth 64 (js.readZR rs))
  let s1 := storeSt s base.toNat (Int.ediv 64 8).toNat (BitVec.setWidth (8 * (Int.ediv 64 8).toNat) new)
  have hst : Stored s s1 base.toNat 8 new.toNat := by
    have := stored_storeSt s base.toNat (Int.ediv 64 8).toNat (BitVec.setWidth (8 * (Int.ediv 64 8).toNat) new)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by exact new.isLt)] at this
    exact this
  have hjm : atomMem js 3 .swp rs base = js.mem.writeLE base.toNat 8 new.toNat := by
    simp [atomMem, new, Janus.Arm64.State.getX]
  have hm1 : MemRel (atomMem js 3 .swp rs base) s1 := by
    rw [hjm]; exact hm.store hst rfl
  have hr1 := h.mem_update hst.regs (atomMem js 3 .swp rs base)
  have hc1 : LinuxEL0Config s1 := hc.stored hst
  obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r hr1 ht (N := 64) (by decide)
    (Sail.BitVec.zeroExtend (BitVec.ofNat 64 (js.mem.readLE base.toNat 8)) 64)
  have hval : (Sail.BitVec.zeroExtend (BitVec.ofNat 64 (js.mem.readLE base.toNat 8)) 64).setWidth 64 =
      BitVec.ofNat 64 (js.mem.readLE base.toNat 8) := by
    apply BitVec.eq_of_toNat_eq; have := readLE_lt js.mem base.toNat 8; simp [Sail.BitVec.zeroExtend] <;> omega
  simp only [Janus.Arm64.State.setX, hval] at hr2
  have hc2 := hc1.rstep hst2
  try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hMA
  simp only [aslOpOf] at hMA hcr
  refine ⟨_, s2, rfl, writeZR_pc _ _ _, ?_, hr2, by rw [writeZR_mem]; exact hm1.rstep hst2, fun r g1 g2 => ?_⟩
  · unfold execute_aarch64_instrs_memory_atomicops_swp
    simp only [s1, new] at hx2 hc2
    try simp only [Janus.Arm64.Memory.readLE_one, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hx2 hc2
    cfg_simp [run_readReg hp, he, EL0, hcr, hB, hX, hMA, __UNKNOWN_bits, hx2, run_readReg hc2.speInFlight]
  · rw [hst2.regs r g1 g2]; show s1.regs.get? r = s.regs.get? r; rw [hst.regs]

end JanusASL.Proofs
