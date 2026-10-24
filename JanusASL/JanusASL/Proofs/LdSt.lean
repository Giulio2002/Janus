import JanusASL.Proofs.MemWrite

/-! # Loads and stores (general registers): the single-register immediate forms -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- `s'` differs from `s` at most in the general-purpose registers and SP (and memory). -/
def GFrame (s s' : SState) : Prop :=
  ∀ r, isGprReg r = false → r ≠ .SP_EL0 → s'.regs.get? r = s.regs.get? r

theorem run_CheckSPAlignment {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hc : LinuxEL0Config s)
    (ha : js.sp.toNat % 16 = 0) : (CheckSPAlignment ()).run s = .ok () s := by
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  have hal := isAligned_iff js.sp 16 (by decide)
  simp only [IsAligned__1, ha, decide_true] at hal
  cfg_simp [CheckSPAlignment, run_SP_read hp hsp h.sp, run_readReg hp, he, EL0, SCTLR_read__1,
    S1TranslationRegime__1, run_S1TranslationRegime hc, SCTLR_read, EL1, run_readReg hc.sctlr1, Mk_SCTLRType,
    _get_SCTLRType_SA0]
  rw [if_pos (beq_iff_eq.mp (by simpa using hal))]; rfl

theorem baseAddr_ok {js : Janus.Arm64.State} {rn : Nat} {base : BitVec 64} (hj : Janus.Arm64.baseAddr js rn = .ok base) :
    (rn = 31 ∧ js.sp.toNat % 16 = 0 ∧ base = js.sp) ∨ (rn ≠ 31 ∧ base = js.regs rn) := by
  unfold Janus.Arm64.baseAddr at hj
  split at hj
  · split at hj
    · cases hj; left; exact ⟨by assumption, by assumption, rfl⟩
    · cases hj
  · cases hj; right; exact ⟨by assumption, rfl⟩

/-- A register-only step: only GPRs and SP change; memory and the rest of the state are kept. -/
structure RStep (s s' : SState) : Prop where
  regs : GFrame s s'
  mem : s'.mem = s.mem
  cycle : s'.cycleCount = s.cycleCount
  out : s'.sailOutput = s.sailOutput

theorem RStep.refl (s : SState) : RStep s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem RStep.trans {s1 s2 s3 : SState} (a : RStep s1 s2) (b : RStep s2 s3) : RStep s1 s3 :=
  ⟨fun r h1 h2 => (b.regs r h1 h2).trans (a.regs r h1 h2), b.mem.trans a.mem, b.cycle.trans a.cycle,
    b.out.trans a.out⟩

theorem setGpr_fields (s : SState) (v : BitVec 64) (d : Nat) :
    (setGpr s v d).mem = s.mem ∧ (setGpr s v d).cycleCount = s.cycleCount ∧
      (setGpr s v d).sailOutput = s.sailOutput := by
  unfold setGpr; split <;> exact ⟨rfl, rfl, rfl⟩

theorem RStep.setGpr (s : SState) (v : BitVec 64) {d : Nat} (hd : d < 31) : RStep s (setGpr s v d) :=
  ⟨fun r hr _ => get?_setGpr s v hd r hr, (setGpr_fields s v d).1, (setGpr_fields s v d).2.1,
    (setGpr_fields s v d).2.2⟩

theorem RStep.setSP (s : SState) (v : BitVec 64) : RStep s (s.set .SP_EL0 v) :=
  ⟨fun r _ h2 => get?_set_ne s v (Ne.symm h2), rfl, rfl, rfl⟩

theorem run_X_set_r {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {d : Nat} (hd : d < 32)
    {N : Nat} (hN : N = 32 ∨ N = 64) (v : BitVec N) :
    ∃ s', (X_set (d : Int) N v).run s = .ok () s' ∧ Rel (js.setX d v) s' ∧ RStep s s' := by
  by_cases hd31 : d = 31
  · subst hd31
    refine ⟨s, run_X_set_zr s hN v, ?_, RStep.refl s⟩
    simpa [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR] using h
  · have hd' : d < 31 := by omega
    refine ⟨_, run_X_set hd' hN v, ?_, RStep.setGpr _ _ hd'⟩
    simpa [Janus.Arm64.State.setX, Sail.BitVec.zeroExtend] using h.writeZR hd' (v.setWidth 64)

/-- The base-register write-back `if n == 31 then SP[] = a else X[n] = a`. -/
theorem run_writeback {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hc : LinuxEL0Config s) {rn : Nat}
    (hn : rn < 32) (a : BitVec 64) :
    ∃ s', (if rn = 31 then SP_set a else X_set (rn : Int) 64 a).run s = .ok () s' ∧ Rel (js.writeSP rn a) s' ∧
      RStep s s' := by
  obtain ⟨p, hp, _, _, hsp⟩ := hc.pstate
  by_cases h31 : rn = 31
  · subst h31
    exact ⟨_, by rw [if_pos rfl, run_SP_set hp hsp], h.writeSP31 a, RStep.setSP s a⟩
  · obtain ⟨s', hr, hrel, hst⟩ := run_X_set_r h hn (Or.inr rfl) a
    refine ⟨s', by rw [if_neg h31]; exact hr, ?_, hst⟩
    simpa [Janus.Arm64.State.setX, Janus.Arm64.State.writeZR, Janus.Arm64.State.writeSP, h31] using hrel

/-- The base address `if n == 31 then CheckSPAlignment(); SP[] else X[n]`. -/
theorem run_base {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hc : LinuxEL0Config s) {rn : Nat}
    (hn : rn < 32) {base : BitVec 64} (hj : Janus.Arm64.baseAddr js rn = .ok base) :
    (if rn = 31 then (do CheckSPAlignment (); SP_read ()) else X_read (rn : Int) 64).run s = .ok base s := by
  obtain ⟨p, hp, _, _, hsp⟩ := hc.pstate
  rcases baseAddr_ok hj with ⟨h31, ha, rfl⟩ | ⟨h31, rfl⟩
  · subst h31
    simp only [if_pos, run_bind, run_CheckSPAlignment h hc ha, run_SP_read hp hsp h.sp]
  · rw [if_neg h31, run_X_read_rel h hn (Or.inr rfl)]
    simp [Janus.Arm64.State.getX, Janus.Arm64.State.readZR, h31]

theorem load_ok {m : Janus.Arm64.Memory} {a n v : Nat} (h : Janus.Arm64.load m a n = .ok v) :
    m.accessible a n false = true ∧ v = m.readLE a n := by
  unfold Janus.Arm64.load at h
  split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

theorem store_ok {m m' : Janus.Arm64.Memory} {a n v : Nat} (h : Janus.Arm64.store m a n v = .ok m') :
    m.accessible a n true = true ∧ m' = m.writeLE a n v := by
  unfold Janus.Arm64.store at h
  split at h
  · split at h
    · cases h; exact ⟨by assumption, rfl⟩
    · cases h
  · cases h

/-- The value a load writes: zero-extended (`opc = 1`), sign-extended to 64 (`2`) or to 32 bits (`3`). -/
def loadVal (size opc v : Nat) : BitVec 64 :=
  if opc = 1 then BitVec.ofNat 64 v
  else if opc = 2 then Janus.Arm64.signExtendLoad size 64 v
  else (Janus.Arm64.signExtendLoad size 32 v).setWidth 64

theorem memSingle_load {js js2 : Janus.Arm64.State} {size opc rt : Nat} {addr : BitVec 64} (hopc : opc ≠ 0)
    (h : Janus.Arm64.memSingle js size opc rt addr = .ok js2) :
    js.mem.accessible addr.toNat (2 ^ size) false = true ∧
      js2 = js.writeZR rt (loadVal size opc (js.mem.readLE addr.toNat (2 ^ size))) := by
  unfold Janus.Arm64.memSingle at h
  rw [if_neg hopc] at h
  split at h
  · cases h
  · next v hl =>
    obtain ⟨ha, rfl⟩ := load_ok hl
    cases h; exact ⟨ha, rfl⟩

theorem memSingle_store {js js2 : Janus.Arm64.State} {size rt : Nat} {addr : BitVec 64}
    (h : Janus.Arm64.memSingle js size 0 rt addr = .ok js2) :
    js.mem.accessible addr.toNat (2 ^ size) true = true ∧
      js2 = { js with mem := js.mem.writeLE addr.toNat (2 ^ size) (js.readZR rt).toNat } := by
  unfold Janus.Arm64.memSingle at h
  rw [if_pos rfl] at h
  split at h
  · next m hs =>
    obtain ⟨ha, rfl⟩ := store_ok hs
    cases h; exact ⟨ha, rfl⟩
  · cases h

theorem LinuxEL0Config.rstep {s s' : SState} (hc : LinuxEL0Config s) (h : RStep s s') : LinuxEL0Config s' :=
  hc.of_eq fun r hr => h.regs r (cfgRegs_not_gpr r hr) (fun e => by subst e; revert hr; decide)

theorem MemRel.rstep {m : Janus.Arm64.Memory} {s s' : SState} (hm : MemRel m s) (h : RStep s s') : MemRel m s' :=
  fun a ha => by rw [show s'.mem.get? a = s.mem.get? a by rw [h.mem]]; exact hm a ha

theorem writeZR_mem (js : Janus.Arm64.State) (d : Nat) (v : BitVec 64) : (js.writeZR d v).mem = js.mem := by
  unfold Janus.Arm64.State.writeZR; split <;> rfl

theorem writeSP_mem (js : Janus.Arm64.State) (d : Nat) (v : BitVec 64) : (js.writeSP d v).mem = js.mem := by
  unfold Janus.Arm64.State.writeSP; split <;> rfl

/-- The ASL's `(datasize, regsize, signed)` of a load of `2^size` bytes selected by `opc` (1, 2, 3). -/
def LoadCase (size opc ds rs : Nat) (sgn : Bool) : Prop :=
  (opc = 1 ∧ size = 0 ∧ ds = 8 ∧ rs = 32 ∧ sgn = false) ∨ (opc = 1 ∧ size = 1 ∧ ds = 16 ∧ rs = 32 ∧ sgn = false) ∨
  (opc = 1 ∧ size = 2 ∧ ds = 32 ∧ rs = 32 ∧ sgn = false) ∨ (opc = 1 ∧ size = 3 ∧ ds = 64 ∧ rs = 64 ∧ sgn = false) ∨
  (opc = 2 ∧ size = 0 ∧ ds = 8 ∧ rs = 64 ∧ sgn = true) ∨ (opc = 2 ∧ size = 1 ∧ ds = 16 ∧ rs = 64 ∧ sgn = true) ∨
  (opc = 2 ∧ size = 2 ∧ ds = 32 ∧ rs = 64 ∧ sgn = true) ∨
  (opc = 3 ∧ size = 0 ∧ ds = 8 ∧ rs = 32 ∧ sgn = true) ∨ (opc = 3 ∧ size = 1 ∧ ds = 16 ∧ rs = 32 ∧ sgn = true)

theorem LoadCase.facts {size opc ds rs : Nat} {sgn : Bool} (h : LoadCase size opc ds rs sgn) :
    opc ≠ 0 ∧ (rs = 32 ∨ rs = 64) ∧ (Int.ediv (ds : Int) 8).toNat = 2 ^ size ∧
      (2 ^ size = 1 ∨ 2 ^ size = 2 ∨ 2 ^ size = 4 ∨ 2 ^ size = 8) ∧ 0 < ds ∧ ds ≤ rs := by
  unfold LoadCase at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;> decide

/-- The register value of a load: the ASL's `X[t, regsize] = Extend(data, regsize, !signed)` is
Janus' `loadVal`. -/
theorem load_value {size opc ds rs : Nat} {sgn : Bool} (h : LoadCase size opc ds rs sgn) {n : Nat}
    (hn : n = 2 ^ size) (data : BitVec (n * 8)) (x : Nat) (hx : data.toNat = x) :
    (if sgn then (Sail.BitVec.signExtend (BitVec.setWidth ds data) rs).setWidth 64
      else (Sail.BitVec.zeroExtend (BitVec.setWidth ds data) rs).setWidth 64) = loadVal size opc x := by
  subst hn
  have hlt := data.isLt
  unfold LoadCase at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
  · subst hx
    simp only [loadVal, Janus.Arm64.signExtendLoad, Bool.false_eq_true, ite_true, ite_false]
    first
    | (apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.zeroExtend]; done)
    | (apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.zeroExtend]; omega)
    | (rw [show BitVec.ofNat _ data.toNat = BitVec.setWidth _ data from BitVec.eq_of_toNat_eq (by simp; try omega)]
       simp [Sail.BitVec.signExtend])

set_option maxHeartbeats 16000000 in
/-- **The single-register immediate-offset load** (`LDR`/`LDRB`/`LDRH`/`LDRS*`, unsigned offset,
unscaled, pre- and post-index): Janus' `memIndexed`/`memSingle` against the ASL's
`execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx`. -/
theorem run_exec_load {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {size opc ds rs : Nat}
    {sgn : Bool} (hcase : LoadCase size opc ds rs sgn) {rn rt : Nat} (hn : rn < 32) (ht : rt < 32)
    (offset : BitVec 64) (postindex wback tc : Bool)
    (hj : Janus.Arm64.memIndexed js rn offset postindex wback (fun s a => Janus.Arm64.memSingle s size opc rt a) =
      .ok js1) :
    ∃ s', (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx ds .MemOp_LOAD rn false offset
      postindex rs false sgn rt tc false wback).run s = .ok () s' ∧ Rel js1 s' ∧ MemRel js1.mem s' ∧ RStep s s' := by
  obtain ⟨hopc, hrs, hdsn, hsz, hds0, hdsrs⟩ := hcase.facts
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
  obtain ⟨hacc, rfl⟩ := memSingle_load hopc hs2
  obtain ⟨v, hv, hvn⟩ := run_Mem_read hU hf hc hm addr (Int.ediv (ds : Int) 8).toNat (by rw [hdsn]; exact hsz)
    (by rw [hdsn]; exact hacc) tc
  unfold execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have hcr := run_CreateAccDescGPR hc false tc
  simp only [Bool.false_eq_true, ite_false] at hcr
  have hA' : (if postindex = false then base + offset else base) = addr := by rw [← hA]; cases postindex <;> rfl
  have hval := load_value hcase hdsn v _ (by rw [hvn, hdsn])
  have has : (decide (0 < ds) && decide (ds ≤ rs)) = true := by simp; omega
  have has2 : (decide (0 ≤ ds) && decide (ds ≤ rs)) = true := by simp; omega
  have has3 : decide (ds ≤ rs) = true := by simp; omega
  cfg_simp [run_readReg hp, he, EL0, hcr, hB, hA', hv, has, has2]
  obtain ⟨s1, hx1, hr1, hst1⟩ := run_X_set_r h ht hrs
    (if sgn then Sail.BitVec.signExtend (BitVec.setWidth ds v) rs else Sail.BitVec.zeroExtend (BitVec.setWidth ds v) rs)
  have hval' : (if sgn then Sail.BitVec.signExtend (BitVec.setWidth ds v) rs
      else Sail.BitVec.zeroExtend (BitVec.setWidth ds v) rs).setWidth 64 = loadVal size opc (js.mem.readLE addr.toNat (2 ^ size)) := by
    rw [← hval]; cases sgn <;> rfl
  simp only [Janus.Arm64.State.setX, hval'] at hr1
  have hc1 := hc.rstep hst1
  cases sgn <;> (try simp only [Bool.false_eq_true, ite_false, ite_true] at hx1) <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, hx1]
  all_goals
    cases wback
    · refine ⟨s1, ?_, hr1, ?_, hst1⟩
      · cfg_simp [run_readReg hc1.speInFlight, has3, hx1]
      · simp only [Bool.false_eq_true, ite_false, writeZR_mem]; exact hm.rstep hst1
    · obtain ⟨s2, hx2, hr2, hst2⟩ := run_writeback hr1 hc1 hn (base + offset)
      have hc2 := hc1.rstep hst2
      refine ⟨s2, ?_, hr2, ?_, hst1.trans hst2⟩
      · cases postindex <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hA <;> subst hA <;>
        cfg_simp [hx2, run_readReg hc2.speInFlight, has3, hx1]
      · simp only [ite_true, writeSP_mem, writeZR_mem]; exact hm.rstep (hst1.trans hst2)

theorem run_X_read_w {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {n : Nat} (hn : n < 32) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    (X_read (n : Int) w).run s = .ok (BitVec.ofNat w (js.readZR n).toNat) s := by
  have h3 : (w == 8 || (w == 16 || (w == 32 || w == 64))) = true := by
    rcases hw with rfl | rfl | rfl | rfl <;> rfl
  have h2 : (decide ((n : Int) ≥ 0) && decide ((n : Int) ≤ 31)) = true := by simp; omega
  by_cases h31 : n = 31
  · subst h31
    simp only [X_read, run_bind, h2, h3, run_sail_assert_true, Janus.Arm64.State.readZR, if_pos]
    rcases hw with rfl | rfl | rfl | rfl <;> rfl
  · have hn' : n < 31 := by omega
    have h1 : ((n : Int) != 31) = true := by simp; omega
    have h4 : ((n : Int).toNat) = n := by omega
    simp only [X_read, run_bind, h1, h2, h3, h4, get_R, run_sail_assert_true, ite_true,
      run_read_gpr hn' (h.gpr n hn')]
    simp only [Janus.Arm64.State.readZR, h31, ite_false]
    rcases hw with rfl | rfl | rfl | rfl <;>
    · simp only [pure, EStateM.pure]
      congr 1

theorem byte_mod_eq {x v k j : Nat} (hj : j < k) (h : x % 2 ^ (8 * k) = v % 2 ^ (8 * k)) :
    x / 256 ^ j % 256 = v / 256 ^ j % 256 := by
  have hd : 256 ^ j * 256 ∣ 2 ^ (8 * k) := by
    rw [show 256 ^ j * 256 = 2 ^ (8 * (j + 1)) by rw [Nat.pow_mul, Nat.pow_succ]]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self (m := v), ← Nat.mod_mod_of_dvd x hd,
    ← Nat.mod_mod_of_dvd v hd, h]

theorem MemRel.store {m : Janus.Arm64.Memory} {s s1 : SState} {a k x v : Nat} (hm : MemRel m s)
    (hs : Stored s s1 a k x) (hx : x % 2 ^ (8 * k) = v % 2 ^ (8 * k)) : MemRel (m.writeLE a k v) s1 := by
  intro b hb
  rw [hs.mem b]
  simp only [Janus.Arm64.Memory.writeLE]
  split
  · next hin =>
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl]
    exact byte_mod_eq (by omega) hx
  · exact hm b hb

theorem Rel.mem_update {js : Janus.Arm64.State} {s s' : SState} (h : Rel js s) (e : s'.regs = s.regs)
    (m : Janus.Arm64.Memory) : Rel { js with mem := m } s' where
  gpr i hi := by
    have := h.gpr i hi
    rw [← this]; unfold gprVal; split <;> simp [e]
  sp := by rw [e]; exact h.sp
  pc := by rw [e]; exact h.pc
  pstate := by rw [e]; exact h.pstate

def StoreCase (size ds : Nat) : Prop :=
  (size = 0 ∧ ds = 8) ∨ (size = 1 ∧ ds = 16) ∨ (size = 2 ∧ ds = 32) ∨ (size = 3 ∧ ds = 64)

theorem StoreCase.facts {size ds : Nat} (h : StoreCase size ds) :
    (ds = 8 ∨ ds = 16 ∨ ds = 32 ∨ ds = 64) ∧ (Int.ediv (ds : Int) 8).toNat = 2 ^ size ∧
      (2 ^ size = 1 ∨ 2 ^ size = 2 ∨ 2 ^ size = 4 ∨ 2 ^ size = 8) ∧ ds = 8 * 2 ^ size := by
  unfold StoreCase at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem MStep_of_stored {m : Janus.Arm64.Memory} {s s1 : SState} {a k x : Nat} (hs : Stored s s1 a k x)
    (hr : ∀ i < k, InRegion m (a + i) false) :
    ∀ b, ¬ InRegion m b false → s1.mem.get? b = s.mem.get? b := by
  intro b hb
  rw [hs.mem b, if_neg]
  intro hin; apply hb
  have := hr (b - a) (by omega); rwa [show a + (b - a) = b by omega] at this

set_option maxHeartbeats 16000000 in
/-- **The single-register immediate-offset store** (`STR`/`STRB`/`STRH`, all immediate forms). -/
theorem run_exec_store {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {size ds rs : Nat}
    (hcase : StoreCase size ds) {rn rt : Nat} (hn : rn < 32) (ht : rt < 32)
    (offset : BitVec 64) (postindex wback tc : Bool)
    (hj : Janus.Arm64.memIndexed js rn offset postindex wback (fun s a => Janus.Arm64.memSingle s size 0 rt a) =
      .ok js1) :
    ∃ s', (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx ds .MemOp_STORE rn false offset
      postindex rs false false rt tc false wback).run s = .ok () s' ∧ Rel js1 s' ∧ MemRel js1.mem s' ∧
      GFrame s s' ∧ (∀ b, ¬ InRegion js.mem b false → s'.mem.get? b = s.mem.get? b) ∧
      s'.cycleCount = s.cycleCount ∧ s'.sailOutput = s.sailOutput := by
  obtain ⟨hds, hdsn, hsz, hds8⟩ := hcase.facts
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
  obtain ⟨hacc, rfl⟩ := memSingle_store hs2
  have hX := run_X_read_w h ht hds
  obtain ⟨s1, hv, hst⟩ := run_Mem_set hU hf hc addr (Int.ediv (ds : Int) 8).toNat (by rw [hdsn]; exact hsz)
    (by rw [hdsn]; exact hacc) tc (BitVec.setWidth _ (BitVec.setWidth ds (js.readZR rt)))
  unfold execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have hcr := run_CreateAccDescGPR hc true tc
  simp only [ite_true] at hcr
  have hA' : (if postindex = false then base + offset else base) = addr := by rw [← hA]; cases postindex <;> rfl
  cfg_simp [run_readReg hp, he, EL0, hcr, hB, hA', hX, hv]
  have hr1 := h.mem_update hst.regs (js.mem.writeLE addr.toNat (2 ^ size) (js.readZR rt).toNat)
  have hreg := accessible_bytes hacc
  have hm1 : MemRel (js.mem.writeLE addr.toNat (2 ^ size) (js.readZR rt).toNat) s1 := by
    refine hm.store (hdsn ▸ hst) ?_
    simp only [BitVec.toNat_setWidth, hdsn]
    rw [show 2 ^ size * 8 = 8 * 2 ^ size by omega, ← hds8, Nat.mod_mod, Nat.mod_mod]
  have hmo := MStep_of_stored hst (fun i hi => (hreg i (by rw [hdsn] at hi; exact hi)).read)
  have hc1 : LinuxEL0Config s1 := hc.stored hst
  have hg1 : GFrame s s1 := fun r _ _ => by show s1.regs.get? r = s.regs.get? r; rw [hst.regs]
  have hwl : ∀ (d : Nat) (v : BitVec 64), ({ js with mem := js.mem.writeLE addr.toNat (2 ^ size) (js.readZR rt).toNat }.writeSP d v).mem =
      js.mem.writeLE addr.toNat (2 ^ size) (js.readZR rt).toNat := fun d v => writeSP_mem _ d v
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

/-! ## From the decoder to the whole step -/

theorem run_DecodeA64_LS {w : Nat} (hw : w < 2 ^ 32) (h27 : (w / 2 ^ 27) % 2 = 1) (h25 : (w / 2 ^ 25) % 2 = 0)
    (h28 : (w / 2 ^ 28) % 2 = 1) (pc : Int) (s : SState) :
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

/-- The state the decoder runs in, after the clause has set `SEE`. -/
abbrev entrySt (s : SState) (w : Nat) (k : Int) : SState := (stepEntry s (BitVec.ofNat 32 w)).set .SEE k

theorem entry_get (s : SState) (w : Nat) (k : Int) (r : Register) (hr : r ∉ stepEntryRegs) :
    (entrySt s w k).regs.get? r = s.regs.get? r := by
  simp only [entrySt, stepEntry]
  have hn : ∀ x ∈ stepEntryRegs, x ≠ r := fun x hx e => hr (e ▸ hx)
  rw [get?_set_ne _ _ (hn _ (by decide)), get?_set_ne _ _ (hn _ (by decide)), get?_set_ne _ _ (hn _ (by decide)),
    get?_set_ne _ _ (hn _ (by decide)), get?_set_ne _ _ (hn _ (by decide)), get?_set_ne _ _ (hn _ (by decide)),
    get?_set_ne _ _ (hn _ (by decide)), get?_set_ne _ _ (hn _ (by decide))]

theorem cfg_not_entry : ∀ r ∈ cfgRegs, r ∉ stepEntryRegs := by decide

theorem entry_facts {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (w : Nat) (k : Int) :
    Rel js (entrySt s w k) ∧ MemRel js.mem (entrySt s w k) ∧ LinuxEL0Config (entrySt s w k) ∧
      TFrame js.mem s (entrySt s w k) := by
  have hreg := entry_get s w k
  refine ⟨h.entry _ k, hm, hc.of_eq fun r hr => hreg r (cfg_not_entry r hr),
    ⟨fun r _ _ hr => hreg r hr, fun _ _ => rfl, rfl, rfl⟩⟩

theorem memIndexed_pc {js js1 : Janus.Arm64.State} {rn : Nat} {offset : BitVec 64} {post wb : Bool} {size opc rt : Nat}
    (hj : Janus.Arm64.memIndexed js rn offset post wb (fun s a => Janus.Arm64.memSingle s size opc rt a) = .ok js1) :
    js1.pc = js.pc := by
  unfold Janus.Arm64.memIndexed at hj
  split at hj
  · cases hj
  · simp only at hj
    split at hj
    · cases hj
    · next js2 hs2 =>
      have : js2.pc = js.pc := by
        unfold Janus.Arm64.memSingle at hs2
        split at hs2
        · split at hs2
          · cases hs2; rfl
          · cases hs2
        · split at hs2
          · cases hs2
          · cases hs2; unfold Janus.Arm64.State.writeZR; split <;> rfl
      cases hj; split
      · rw [← this]; unfold Janus.Arm64.State.writeSP; split <;> rfl
      · exact this

/-- Assembly for loads and stores: if the decoder, from the step-entry state with `SEE = k`,
completes in a state related to `js1` that changed no register but GPRs and SP, then the whole
ASL step completes in a state related to `js1.next`, with the configuration kept. -/
theorem step_agree_mem {w : Nat} {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hc : LinuxEL0Config s)
    {k : Int} {s2 : SState}
    (hrun : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2)
    (hr : Rel js1 s2) (hg : GFrame (entrySt s w k) s2) (hpc : js1.pc = js.pc) :
    (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK (s2.set ._PC (js.pc + 4)) ∧
      Rel js1.next (s2.set ._PC (js.pc + 4)) ∧ LinuxEL0Config (s2.set ._PC (js.pc + 4)) := by
  have hbt : s2.regs.get? .__BranchTaken = some false := by
    rw [hg _ rfl (by decide)]
    simp only [entrySt, stepEntry]; repeat rw [get?_set_ne _ _ (by decide)]
    exact get?_set_BranchTaken _ _
  have hpc2 : s2.regs.get? ._PC = some js.pc := by rw [hr.pc, hpc]
  refine ⟨run_janus_step (BitVec.ofNat 32 w) h.pc hrun hbt hpc2, by
    rw [show js1.next = { js1 with pc := js.pc + 4 } by simp [Janus.Arm64.State.next, hpc]]; exact hr.setPC _, ?_⟩
  refine hc.of_eq fun r hr => ?_
  rw [get?_set_ne _ _ (fun e => by subst e; revert hr; decide), hg r (cfgRegs_not_gpr r hr)
    (fun e => by subst e; revert hr; decide), entry_get s w k r (cfg_not_entry r hr)]

end JanusASL.Proofs
