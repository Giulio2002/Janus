import Janus.Contracts.Iface
import Janus.Contracts.IfaceModel

/-!
# The interface contracts are satisfiable (arm64)

For every contract of `Janus.Contracts.Iface`: machine code (written in A64 assembly, its words
below) placed at the address `A0` of a program with no other code, a proof by symbolic execution
that it satisfies the contract for the model `R0` of `Janus.Contracts.IfaceModel` (whose laws
hold, `R0_laws`), and a call state (`wstate`) that satisfies the contract's precondition. So no
contract is contradictory: `<contract>_satisfiable` states that a model, an implementation and a
state satisfying the precondition exist, and the implementation then reaches the contract's
postcondition from that state (`Summary`).

The code is the model's behaviour, not the Go runtime's: every conversion returns the box `BOX`,
every assertion compares with the one type `TD`, `interfaceSwitch` reads only `NCases`.
-/

namespace Janus.Contracts.IfaceSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Iface Janus.Contracts.IfaceModel

/-- A program with no code, stubs or data of its own. -/
def toy : Program := { segments := [], stubs := [], exitAddr := 0 }

/-- Where the model implementations are placed. -/
def A0 : Nat := 0x100000

/-- An implementation: the words `ws` at `A0`. -/
def at0 (ws : List Nat) : List Segment := [{ name := "model", base := A0, words := ws }]

/-- `toy` with the implementation `ws`, as a program of its own (the executor runs the code of a
closed program's own segments). -/
def withCode (ws : List Nat) : Program := { segments := at0 ws, stubs := [], exitAddr := 0 }

theorem link_at0 (ws : List Nat) : toy.link (at0 ws) = withCode ws := rfl

/-- The witness call state: the arguments `r`, goroutine `wg`, return address `wret`, stack
pointer `wsp`, memory `wmem`. -/
def wstate (r : Nat → W64) : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else r i,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := wmem }

theorem wstate_rtpre (r : Nat → W64) (n : Nat) (hn : n ≤ 3) : RTPre R0 n (wstate r) := by
  have hw : wmem.accessible (wsp - 64) (64 + 8 + 8 * 3) true = true := by decide
  have h28 : (wstate r).regs 28 = BitVec.ofNat 64 wg := rfl
  have h30 : (wstate r).regs 30 = BitVec.ofNat 64 wret := rfl
  have hsp : (wstate r).sp = BitVec.ofNat 64 wsp := rfl
  have hm : (wstate r).mem = wmem := rfl
  refine ⟨wmem_env ((wstate r).regs 28), ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, by decide, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, h28]; decide
  · simp only [regG, stackguard0Offset, h28, hm]; decide
  · simp only [stackguard0, regG, stackguard0Offset, h28, hm, hsp, R0_depth]; decide
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [hsp]; decide
  · simp only [hsp, R0_depth]; decide
  · simp only [hsp]; simp [wsp]; omega
  · simp only [hsp, hm, R0_depth, BitVec.toNat_ofNat]
    exact Memory.accessible_mono _ hw (by simp [wsp]) (by simp [wsp]; omega)
  · simp only [hsp, R0_depth, R0_priv, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [wsp]

/-- The return of a model implementation as `RTReturn`: the preserved registers and fields. -/
theorem rtReturn_of (R : IfaceModel) (nargs : Nat) (extra : List (Nat × Nat)) (s s' : State)
    (P : (Nat → W64) → Memory → Prop) (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30)
    (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29)
    (hdz : s'.dczid = s.dczid) (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr)
    (hfs : s'.fpsr = s.fpsr) (hfr : MemFrame s.mem s'.mem (rtWrites R s nargs ++ extra))
    (henv : R.Env s'.mem (s.regs 28)) (hp : P s'.regs s'.mem) : RTReturn R nargs extra s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.mem, ?_, hfr, henv, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s'
  simp only at hsp hpc hdz htp hfc hfs h18 h28 h29 ⊢
  subst hsp hpc hdz htp hfc hfs
  congr
  funext i
  simp only [Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

/-! ## Boxing -/

/-- `movz x1, #0x300; movk x1, #1, lsl 16; str x0, [x1]; mov x0, x1; ret`. -/
def convT64Code : List Nat := [0xd2806001, 0xf2a00021, 0xf9000020, 0xaa0103e0, 0xd65f03c0]

theorem convT64_impl : ConvT64 (toy.link (at0 convT64Code)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  refine rtReturn_of R0 1 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl ?_ ((show Env0 s.mem (s.regs 28) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
  · simp only [rtWrites, calleeStack, R0_priv, R0_depth, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    refine ⟨by decide, ?_, inPriv (by decide) (by decide), ?_⟩
    · rw [Memory.accessible_writeLE]
      exact acc_read_of_write (Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
    · show (s.mem.writeLE 66304 8 _).readLE 66304 8 = _
      rw [Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (s.regs 0).isLt

/-- `ConvT64` is satisfiable. -/
theorem convT64_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    ConvT64 (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ RTPre R 1 s :=
  ⟨R0, _, R0_laws, convT64_impl, wstate fun _ => 0, rfl, wstate_rtpre _ 1 (by decide)⟩

/-- `movz x1, #0x300; movk x1, #1, lsl 16; str w0, [x1]; mov x0, x1; ret`. -/
def convT32Code : List Nat := [0xd2806001, 0xf2a00021, 0xb9000020, 0xaa0103e0, 0xd65f03c0]

theorem convT32_impl : ConvT32 (toy.link (at0 convT32Code)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  refine rtReturn_of R0 1 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl ?_ ((show Env0 s.mem (s.regs 28) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
  · simp only [rtWrites, calleeStack, R0_priv, R0_depth, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    refine ⟨by decide, ?_, inPriv (by decide) (by decide), ?_⟩
    · rw [Memory.accessible_writeLE]
      exact acc_read_of_write (Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
    · show (s.mem.writeLE 66304 4 _).readLE 66304 4 = _
      rw [Memory.readLE_writeLE_self]

/-- `ConvT32` is satisfiable. -/
theorem convT32_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    ConvT32 (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ RTPre R 1 s :=
  ⟨R0, _, R0_laws, convT32_impl, wstate fun _ => 0, rfl, wstate_rtpre _ 1 (by decide)⟩

/-- `movz x1, #0x300; movk x1, #1, lsl 16; strh w0, [x1]; mov x0, x1; ret`. -/
def convT16Code : List Nat := [0xd2806001, 0xf2a00021, 0x79000020, 0xaa0103e0, 0xd65f03c0]

theorem convT16_impl : ConvT16 (toy.link (at0 convT16Code)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  refine rtReturn_of R0 1 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl ?_ ((show Env0 s.mem (s.regs 28) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
  · simp only [rtWrites, calleeStack, R0_priv, R0_depth, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    refine ⟨by decide, ?_, inPriv (by decide) (by decide), ?_⟩
    · rw [Memory.accessible_writeLE]
      exact acc_read_of_write (Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
    · show (s.mem.writeLE 66304 2 _).readLE 66304 2 = _
      rw [Memory.readLE_writeLE_self]

/-- `ConvT16` is satisfiable. -/
theorem convT16_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    ConvT16 (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ RTPre R 1 s :=
  ⟨R0, _, R0_laws, convT16_impl, wstate fun _ => 0, rfl, wstate_rtpre _ 1 (by decide)⟩

/-- `movz x2, #0x300; movk x2, #1, lsl 16; ldr x3, [x1]; str x3, [x2]; mov x0, x2; ret`: copy
the 8 bytes of a value of the model's types (both have `Size_ = 8`). -/
def convTCode : List Nat := [0xd2806002, 0xf2a00022, 0xf9400023, 0xf9000043, 0xaa0203e0, 0xd65f03c0]

/-- The model's types have 8-byte values. -/
theorem tySize_R0 {m : Memory} {g : W64} (h : Env0 m g) {t : Nat} (ht : R0.IsType t) : tySize m t = 8 := by
  obtain ⟨-, -, d1, -, -, d4, -⟩ := h
  rcases ht with rfl | rfl
  · exact d1
  · exact d4

theorem convT_impl : ConvT (toy.link (at0 convTCode)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hty, hb, hacc⟩ := hpre
  have hsz := tySize_R0 (g := s.regs 28) ⟨he1, he2, hd⟩ hty
  rw [hsz] at hb hacc
  janus_run
  refine rtReturn_of R0 2 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl ?_ ((show Env0 s.mem (s.regs 28) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
  · simp only [rtWrites, calleeStack, R0_priv, R0_depth, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    rw [hsz]
    refine ⟨by decide, ?_, inPriv (by decide) (by decide), fun i hi => ?_⟩
    · rw [Memory.accessible_writeLE]
      exact acc_read_of_write (Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
    · show (s.mem.writeLE 66304 8 _).bytes (66304 + i) = _
      exact bytes_writeLE_readLE _ _ _ _ _ hi

/-- `ConvT` is satisfiable. -/
theorem convT_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    ConvT (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ R.IsType (s.regs 0).toNat ∧
        (s.regs 1).toNat + tySize s.mem (s.regs 0).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 1).toNat (tySize s.mem (s.regs 0).toNat) false = true) :=
  ⟨R0, _, R0_laws, convT_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 TD else if i = 1 then BitVec.ofNat 64 VAL else 0,
    rfl, wstate_rtpre _ 2 (by decide), Or.inl rfl, by decide, by decide⟩

theorem convTnoptr_impl : ConvTnoptr (toy.link (at0 convTCode)) A0 R0 :=
  Summary.mono convT_impl (fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩) fun _ _ _ h => h

/-- `ConvTnoptr` is satisfiable. -/
theorem convTnoptr_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    ConvTnoptr (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ R.IsType (s.regs 0).toNat ∧ tyPtrBytes s.mem (s.regs 0).toNat = 0 ∧
        (s.regs 1).toNat + tySize s.mem (s.regs 0).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 1).toNat (tySize s.mem (s.regs 0).toNat) false = true) :=
  ⟨R0, _, R0_laws, convTnoptr_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 TD else if i = 1 then BitVec.ofNat 64 VAL else 0,
    rfl, wstate_rtpre _ 2 (by decide), Or.inl rfl, by decide, by decide, by decide⟩

/-- `movz x2, #0x300; movk x2, #1, lsl 16; cmp x1, #0; csel x0, xzr, x0, eq; stp x0, x1, [x2];
mov x0, x2; ret`: the header, with a zero pointer for the empty string. -/
def convTstringCode : List Nat :=
  [0xd2806002, 0xf2a00022, 0xf100003f, 0x9a8003e0, 0xa9000440, 0xaa0203e0, 0xd65f03c0]

theorem convTstring_impl : ConvTstring (toy.link (at0 convTstringCode)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  have hb2 : wmem.accessible 0 0 false = wmem.accessible 0 0 false := rfl
  janus_run
  all_goals
    refine rtReturn_of R0 2 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl ?_ ((show Env0 s.mem (s.regs 28) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
    · simp only [rtWrites, calleeStack, R0_priv, R0_depth, List.append_nil, List.cons_append,
        List.nil_append]
      janus_frame
    · simp only [BoxWords, setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat,
        List.length_cons, List.length_nil]
      refine ⟨by decide, ?_, inPriv (by decide) (by decide), fun i hi => ?_⟩
      · rw [Memory.accessible_writeLE, Memory.accessible_writeLE]
        exact acc_read_of_write (Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
      · simp at hi
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · rw [show 66304 % 2 ^ 64 + 8 * 0 = 66304 from rfl,
            Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
          split <;> simp [Nat.mod_eq_of_lt (s.regs 0).isLt]
        · rw [show 66304 % 2 ^ 64 + 8 * 1 = 66312 from rfl, Memory.readLE_writeLE_self]
          simp [Nat.mod_eq_of_lt (s.regs 1).isLt]

/-- Three words stored at `a`, `a + 8`, `a + 16`, read back. -/
theorem read3 (m : Memory) (a v0 v1 v2 i : Nat) (hi : i < 3) (h0 : v0 < 2 ^ 64) (h1 : v1 < 2 ^ 64)
    (h2 : v2 < 2 ^ 64) :
    (((m.writeLE a 8 v0).writeLE (a + 8) 8 v1).writeLE (a + 16) 8 v2).readLE (a + 8 * i) 8 =
      [v0, v1, v2][i]'(by simp; omega) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      show a + 8 * 0 = a by omega, Memory.readLE_writeLE_self]
    simpa using Nat.mod_eq_of_lt h0
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), show a + 8 * 1 = a + 8 by omega,
      Memory.readLE_writeLE_self]
    simpa using Nat.mod_eq_of_lt h1
  · rw [show a + 8 * 2 = a + 16 by omega, Memory.readLE_writeLE_self]
    simpa using Nat.mod_eq_of_lt h2

/-- `ConvTstring` is satisfiable. -/
theorem convTstring_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    ConvTstring (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ RTPre R 2 s :=
  ⟨R0, _, R0_laws, convTstring_impl, wstate fun _ => 0, rfl, wstate_rtpre _ 2 (by decide)⟩

/-- `movz x3, #0x300; movk x3, #1, lsl 16; cbz x0, nil; stp x0, x1, [x3]; str x2, [x3, #16];
mov x0, x3; ret; nil: stp xzr, xzr, [x3]; str xzr, [x3, #16]; mov x0, x3; ret`. -/
def convTsliceCode : List Nat :=
  [0xd2806003, 0xf2a00023, 0xb40000a0, 0xa9000460, 0xf9000862, 0xaa0303e0, 0xd65f03c0,
   0xa9007c7f, 0xf900087f, 0xaa0303e0, 0xd65f03c0]

theorem convTslice_impl : ConvTslice (toy.link (at0 convTsliceCode)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  all_goals
    refine rtReturn_of R0 3 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl ?_ ((((show Env0 s.mem (s.regs 28) from ⟨he1, he2, hd⟩).writeLE _
        (by simp [BOX])).writeLE _ (by simp [BOX])).writeLE _ (by simp [BOX])) ?_
    · simp only [rtWrites, calleeStack, R0_priv, R0_depth, List.append_nil, List.cons_append,
        List.nil_append]
      janus_frame
    · simp only [BoxWords, setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat,
        List.length_cons, List.length_nil]
      refine ⟨by decide, ?_, inPriv (by decide) (by decide), fun i hi => ?_⟩
      · rw [Memory.accessible_writeLE, Memory.accessible_writeLE, Memory.accessible_writeLE]
        exact acc_read_of_write (Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
      · simp only [show 66304 % 2 ^ 64 = 66304 from rfl]
        exact read3 _ 66304 _ _ _ i (by simpa using hi) (by first | decide | exact BitVec.isLt _)
          (by first | decide | exact BitVec.isLt _) (by first | decide | exact BitVec.isLt _)

/-- `ConvTslice` is satisfiable. -/
theorem convTslice_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    ConvTslice (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ RTPre R 3 s :=
  ⟨R0, _, R0_laws, convTslice_impl, wstate fun _ => 0, rfl, wstate_rtpre _ 3 (by decide)⟩

/-! ## Assertions and switches -/

/-- The model's itab is readable, for `(ID, TD)`. -/
theorem itabAt_TAB {m : Memory} {g : W64} (h : Env0 m g) : ItabAt R0.priv m TAB ID TD := by
  obtain ⟨h1, -, -, -, -, -, -, -, d7, d8⟩ := h
  exact ⟨by decide, Memory.accessible_mono _ h1 (by decide) (by decide), inPriv (by decide) (by decide),
    d7, d8⟩

/-- `movz x0, #0x200; movk x0, #1, lsl 16; ret`: the one itab. -/
def assertE2ICode : List Nat := [0xd2804000, 0xf2a00020, 0xd65f03c0]

theorem assertE2I_impl : AssertE2I (toy.link (at0 assertE2ICode)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hi, ht0, ht, hsome⟩ := hpre
  simp only [R0_isInter] at hi
  simp only [R0_itab, hi, true_and] at hsome
  have htd : (s.regs 1).toNat = TD := by
    by_cases hne : (s.regs 1).toNat = TD
    · exact hne
    · simp [hne] at hsome
  janus_run
  refine rtReturn_of R0 2 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
  simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
  refine ⟨?_, fun _ => ?_⟩
  · simp [htd, hi, TD, TAB]
  · rw [hi, htd]; exact itabAt_TAB (g := s.regs 28) ⟨he1, he2, hd⟩

/-- `AssertE2I` is satisfiable. -/
theorem assertE2I_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    AssertE2I (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ R.IsInter (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
        R.IsType (s.regs 1).toNat ∧ (R.itab (s.regs 0).toNat (s.regs 1).toNat).isSome) :=
  ⟨R0, _, R0_laws, assertE2I_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 ID else if i = 1 then BitVec.ofNat 64 TD else 0,
    rfl, wstate_rtpre _ 2 (by decide), rfl, by decide, Or.inl rfl, by decide⟩

/-- `movz x2, #0; movk x2, #1, lsl 16; movz x0, #0x200; movk x0, #1, lsl 16; cmp x1, x2;
csel x0, x0, xzr, eq; ret`: the itab for `TD`, `0` otherwise. -/
def assertE2I2Code : List Nat :=
  [0xd2800002, 0xf2a00022, 0xd2804000, 0xf2a00020, 0xeb02003f, 0x9a9f0000, 0xd65f03c0]

/-- What `assertE2I2Code` returns is `R0`'s answer for the interface `ID`. -/
theorem itabResult_R0 {m : Memory} {g : W64} (h : Env0 m g) (t : Nat) :
    ItabResult R0 m ID t (if t = TD then TAB else 0) := by
  refine ⟨?_, fun hne => ?_⟩
  · by_cases ht : t = TD
    · subst ht; simp [TD, TAB]
    · simp only [ht, ite_false]
      by_cases h0 : t = 0 <;> simp [h0, ht]
  · by_cases ht : t = TD
    · subst ht; simp only [ite_true]; exact itabAt_TAB h
    · simp [ht] at hne

theorem assertE2I2_impl : AssertE2I2 (toy.link (at0 assertE2I2Code)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hi, ht⟩ := hpre
  simp only [R0_isInter] at hi
  janus_run
  refine rtReturn_of R0 2 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
  have := itabResult_R0 (g := s.regs 28) ⟨he1, he2, hd⟩ (s.regs 1).toNat
  simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
  rw [hi]
  have heq : (if (s.regs 1).toNat = 65536 then 66048#64 else 0#64).toNat =
      (if (s.regs 1).toNat = TD then TAB else 0) := by
    simp only [TD, TAB]; split <;> simp_all
  rw [heq]; exact this

/-- `AssertE2I2` is satisfiable. -/
theorem assertE2I2_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    AssertE2I2 (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ R.IsInter (s.regs 0).toNat ∧ ((s.regs 1).toNat ≠ 0 → R.IsType (s.regs 1).toNat)) :=
  ⟨R0, _, R0_laws, assertE2I2_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 ID else if i = 1 then BitVec.ofNat 64 TD else 0,
    rfl, wstate_rtpre _ 2 (by decide), rfl, fun _ => Or.inl rfl⟩

theorem typeAssert_impl : TypeAssert (toy.link (at0 assertE2I2Code)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hdesc, -, -⟩ := hpre
  have hi : taInter s.mem (s.regs 0).toNat = ID := hdesc.2.2.2.1
  janus_run
  refine rtReturn_of R0 2 _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
  have := itabResult_R0 (g := s.regs 28) ⟨he1, he2, hd⟩ (s.regs 1).toNat
  refine ⟨?_, hdesc, rfl, rfl⟩
  simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
  rw [hi]
  have heq : (if (s.regs 1).toNat = 65536 then 66048#64 else 0#64).toNat =
      (if (s.regs 1).toNat = TD then TAB else 0) := by
    simp only [TD, TAB]; split <;> simp_all
  rw [heq]; exact this

/-- `TypeAssert` is satisfiable. -/
theorem typeAssert_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    TypeAssert (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ TADescOK R s.mem (s.regs 0).toNat ∧
        ((s.regs 1).toNat = 0 → taCanFail s.mem (s.regs 0).toNat = true) ∧
        ((s.regs 1).toNat ≠ 0 → R.IsType (s.regs 1).toNat ∧
          (taCanFail s.mem (s.regs 0).toNat = true ∨
            (R.itab (taInter s.mem (s.regs 0).toNat) (s.regs 1).toNat).isSome))) :=
  ⟨R0, _, R0_laws, typeAssert_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 DTA else if i = 1 then BitVec.ofNat 64 TD else 0,
    rfl, wstate_rtpre _ 2 (by decide), wmem_taDesc, by decide, fun _ => ⟨Or.inl rfl, Or.inl (by decide)⟩⟩

/-- `ldr x2, [x0, #8]; movz x3, #0; movk x3, #1, lsl 16; cmp x1, x3; b.ne no; cbz x2, no;
mov x0, xzr; movz x1, #0x200; movk x1, #1, lsl 16; ret; no: mov x0, x2; mov x1, xzr; ret`:
case `0` and the itab for `TD` and a non-empty case list, else `(NCases, 0)`. -/
def interfaceSwitchCode : List Nat :=
  [0xf9400402, 0xd2800003, 0xf2a00023, 0xeb03003f, 0x540000c1, 0xb40000a2, 0xaa1f03e0,
   0xd2804001, 0xf2a00021, 0xd65f03c0, 0xaa0203e0, 0xaa1f03e1, 0xd65f03c0]

theorem interfaceSwitch_impl : InterfaceSwitch (toy.link (at0 interfaceSwitchCode)) A0 R0 := by
  rw [link_at0]
  intro cs s hpc hpre
  obtain ⟨⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hdesc, ht0, ht⟩ := hpre
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, -, hn, -, hcs, -⟩ := hdesc'
  have hcs' : ∀ c ∈ cs, c = ID := hcs
  have hsw := switchCase_R0 (s.regs 1).toNat cs hcs'
  have hlen : cs.length < 2 ^ 48 := by omega
  janus_run
  all_goals
    refine rtReturn_of R0 2 _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
    refine ⟨?_, ?_, ?_, hdesc⟩
  all_goals (try rw [hn] at *)
  all_goals (try rw [switchCase_R0 _ cs hcs'])
  all_goals (try simp only [BitVec.toNat_ofNat])
  all_goals first
    | (simp_all [TD, TAB]; done)
    | (intro hne
       obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
         cases cs with
         | nil => simp_all
         | cons c cs' => exact ⟨c, cs', rfl⟩
       rw [hcs' c (by simp)]
       simpa [TD, TAB] using itabAt_TAB (g := s.regs 28) ⟨he1, he2, hd⟩)
    | (rw [ite_eq_right (fun h => by simp only [TD] at h; omega)]; exact Nat.mod_eq_of_lt (by omega))
    | done

/-- `InterfaceSwitch` is satisfiable (shown for the case list `[ID]`). -/
theorem interfaceSwitch_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    InterfaceSwitch (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ ISDescOK R s.mem (s.regs 0).toNat [ID] ∧ (s.regs 1).toNat ≠ 0 ∧
        R.IsType (s.regs 1).toNat) :=
  ⟨R0, _, R0_laws, interfaceSwitch_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 DIS else if i = 1 then BitVec.ofNat 64 TD else 0,
    rfl, wstate_rtpre _ 2 (by decide), wmem_isDesc, by decide, Or.inl rfl⟩

/-! ## Comparison -/

/-- `cbz x0, nil; ldr x3, [x1]; ldr x4, [x2]; cmp x3, x4; cset x0, eq; ret; nil: movz x0, #1;
ret`: compare the 8-byte values (`TD`'s equality), `true` for a nil type or itab. -/
def efaceeqCode : List Nat :=
  [0xb40000c0, 0xf9400023, 0xf9400044, 0xeb04007f, 0x9a9f17e0, 0xd65f03c0, 0xd2800020, 0xd65f03c0]

/-- `R0`'s comparison of `TD`-values. -/
theorem efaceEqual_R0 {m : Memory} {g : W64} (h : Env0 m g) (x y : Nat) :
    efaceEqual R0 m TD x y = (m.readLE x 8 == m.readLE y 8) := by
  obtain ⟨-, -, -, -, d3, -⟩ := h
  have hnd : isDirectIface m TD = false := by simp only [isDirectIface, tyTFlag, d3]; decide
  simp only [efaceEqual, hnd]
  simp [TD]

theorem efaceeq_impl : Efaceeq (toy.link (at0 efaceeqCode)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hok⟩ := hpre
  by_cases h0 : (s.regs 0).toNat = 0
  · janus_run
    refine rtReturn_of R0 3 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
    simp [setReg, efaceEqual, h0]
  · obtain ⟨-, htd, hx, hy⟩ := hok h0
    janus_run
    all_goals
      refine rtReturn_of R0 3 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
        rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
      rw [htd, efaceEqual_R0 (g := s.regs 28) ⟨he1, he2, hd⟩]
      simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      split
      · rename_i heq; simp [heq]
      · rename_i hne; simp [beq_false_of_ne hne]

/-- `Efaceeq` is satisfiable. -/
theorem efaceeq_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    Efaceeq (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre R 3 s ∧ EqOK R s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) :=
  ⟨R0, _, R0_laws, efaceeq_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 TD else if i = 1 ∨ i = 2 then BitVec.ofNat 64 VAL else 0,
    rfl, wstate_rtpre _ 3 (by decide), fun _ => ⟨Or.inl rfl, rfl, by decide, by decide⟩⟩

theorem ifaceeq_impl : Ifaceeq (toy.link (at0 efaceeqCode)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hok⟩ := hpre
  by_cases h0 : (s.regs 0).toNat = 0
  · janus_run
    refine rtReturn_of R0 3 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
    simp [setReg, ifaceEqual, h0]
  · obtain ⟨-, -, ht0, hok⟩ := hok h0
    obtain ⟨-, ht, hx, hy⟩ := hok ht0
    janus_run
    all_goals
      refine rtReturn_of R0 3 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
        rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
      simp only [ifaceEqual, ht]
      rw [efaceEqual_R0 (g := s.regs 28) ⟨he1, he2, hd⟩]
      simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      split
      · rename_i heq; simp [heq]
      · rename_i hne; simp [beq_false_of_ne hne, beq_false_of_ne h0]

/-- `Ifaceeq` is satisfiable. -/
theorem ifaceeq_satisfiable : ∃ (R : IfaceModel) (impl : List Segment), R.Laws ∧
    Ifaceeq (toy.link impl) A0 R ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (RTPre R 3 s ∧ ((s.regs 0).toNat ≠ 0 →
        (s.regs 0).toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 16 false = true ∧
        (s.mem.readLE ((s.regs 0).toNat + 8) 8 ≠ 0) ∧
        EqOK R s.mem (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.regs 1).toNat (s.regs 2).toNat)) :=
  ⟨R0, _, R0_laws, ifaceeq_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 TAB else if i = 1 ∨ i = 2 then BitVec.ofNat 64 VAL else 0,
    rfl, wstate_rtpre _ 3 (by decide), fun _ => ⟨by decide, by decide, by decide,
      fun _ => ⟨Or.inl (by decide), by decide, by decide, by decide⟩⟩⟩

end Janus.Contracts.IfaceSat
