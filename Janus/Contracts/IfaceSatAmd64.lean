import Janus.Contracts.IfaceAmd64
import Janus.Contracts.IfaceModel
import Janus.Contracts.IfaceSat

/-!
# The interface contracts are satisfiable (amd64)

As `Janus.Contracts.IfaceSat` for the amd64 contracts of `Janus.Contracts.IfaceAmd64`: x86-64
machine code (its bytes below, from GNU `as`) at the address `A0` of a program with no other
code, a proof that it satisfies the contract for the model `R0`
(`Janus.Contracts.IfaceModel`), and a call state (`wstate`) that satisfies the precondition.
-/

namespace Janus.Contracts.IfaceSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Type Janus.Contracts.IfaceAmd64
  Janus.Contracts.IfaceModel
open Janus (MemFrame InRanges Outside outside_cons outside_nil)
open Janus.Spec.Map (Agrees)
open Janus.Contracts.Iface (BoxCopy BoxWords BoxHolds ItabResult efaceEqual ifaceEqual EqOK)

/-- A program with no code, stubs or data of its own. -/
def toy : Janus.Amd64.Program := { segments := [], stubs := [], exitAddr := 0 }

/-- Where the model implementations are placed. -/
def A0 : Nat := 0x100000

/-- An implementation: the bytes `bs` at `A0`. -/
def at0 (bs : List Nat) : List Janus.Amd64.Segment := [{ name := "model", base := A0, bytes := bs }]

/-- `toy` with the implementation `bs`, as a program of its own. -/
def withCode (bs : List Nat) : Janus.Amd64.Program := { segments := at0 bs, stubs := [], exitAddr := 0 }

theorem link_at0 (bs : List Nat) : toy.link (at0 bs) = withCode bs := rfl

/-- The witness call state: the arguments `r`, `RSP = wsp` (its word, the return address, is
`0`), `R14 = wg`, memory `wmem`. -/
def wstate (r : Nat → W64) : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else r i,
    rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := wmem }

theorem wstate_rtpre (r : Nat → W64) (n : Nat) (hn : n ≤ 3) : RTPre R0 n (wstate r) := by
  have hw : wmem.accessible (wsp - 64) (64 + 8 + 8 * 3) true = true := by decide
  have h4 : (wstate r).regs 4 = BitVec.ofNat 64 wsp := rfl
  have h14 : (wstate r).regs 14 = BitVec.ofNat 64 wg := rfl
  have hm : (wstate r).mem = wmem := rfl
  refine ⟨wmem_env ((wstate r).regs 14), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [regG, stackguard0Offset, h14]; decide
  · simp only [regG, stackguard0Offset, h14, hm]; decide
  · simp only [stackguard0, regG, regSP, stackguard0Offset, h14, h4, hm, R0_depth]; decide
  · simp only [h4]; decide
  · simp only [h4, R0_depth]; decide
  · simp only [h4]; simp [wsp]; omega
  · simp only [h4, hm, R0_depth, BitVec.toNat_ofNat]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by simp [wsp]) (by simp [wsp]; omega)
  · simp only [h4, hm]; decide
  · simp only [h4, R0_depth, R0_priv, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [wsp]

/-- The return of a model implementation as `RTReturn` (amd64). -/
theorem rtReturn_of (R : IfaceModel) (nargs : Nat) (extra : List (Nat × Nat)) (s s' : Janus.Amd64.State)
    (P : (Nat → W64) → Janus.Arm64.Memory → Prop) (hrip : s'.rip = retAddrOf s)
    (h4 : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hmx : s'.mxcsr = s.mxcsr)
    (hfr : MemFrame s.mem s'.mem (Contracts.IfaceAmd64.rtWrites R s nargs ++ extra))
    (henv : R.Env s'.mem (s.regs 14)) (hp : P s'.regs s'.mem) : RTReturn R nargs extra s s' P := by
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mem, ?_, hfr, henv, hp⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx⟩ := s'
  simp only at hrip h4 h5 h14 hx hfs hdf hmx ⊢
  subst hrip hfs hdf hmx
  congr
  · funext i
    simp only [Contracts.MapAmd64.keepABI]
    split
    · rename_i hi; subst hi; exact h4
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [Contracts.MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-! ## Boxing -/

/-- `mov $0x10300, %edx; mov %rax, (%rdx); mov %rdx, %rax; ret`. -/
def convT64Code : List Nat := [0xba, 0x00, 0x03, 0x01, 0x00, 0x48, 0x89, 0x02, 0x48, 0x89, 0xd0, 0xc3]

theorem convT64_impl : ConvT64 (toy.link (at0 convT64Code)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  janus64_run
  refine rtReturn_of R0 1 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl ?_
    ((show Env0 s.mem (s.regs 14) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
  · simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, R0_priv, R0_depth,
      List.append_nil, List.cons_append, List.nil_append]
    janus_frame
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    refine ⟨by decide, ?_, inPriv (by decide) (by decide), ?_⟩
    · rw [Janus.Arm64.Memory.accessible_writeLE]
      exact acc_read_of_write (Janus.Arm64.Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
    · show (Janus.Arm64.Memory.writeLE s.mem 66304 8 _).readLE 66304 8 = _
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (s.regs 0).isLt

/-- `ConvT64` is satisfiable (amd64). -/
theorem convT64_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    ConvT64 (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧ RTPre R 1 s :=
  ⟨R0, _, R0_laws, convT64_impl, wstate fun _ => 0, rfl, wstate_rtpre _ 1 (by decide)⟩

/-- `mov $0x10300, %edx; mov %eax, (%rdx); mov %rdx, %rax; ret`. -/
def convT32Code : List Nat := [0xba, 0x00, 0x03, 0x01, 0x00, 0x89, 0x02, 0x48, 0x89, 0xd0, 0xc3]

theorem convT32_impl : ConvT32 (toy.link (at0 convT32Code)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  janus64_run
  refine rtReturn_of R0 1 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl ?_
    ((show Env0 s.mem (s.regs 14) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
  · simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, R0_priv, R0_depth,
      List.append_nil, List.cons_append, List.nil_append]
    janus_frame
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    refine ⟨by decide, ?_, inPriv (by decide) (by decide), ?_⟩
    · rw [Janus.Arm64.Memory.accessible_writeLE]
      exact acc_read_of_write (Janus.Arm64.Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
    · show (Janus.Arm64.Memory.writeLE s.mem 66304 4 _).readLE 66304 4 = _
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      simp

/-- `ConvT32` is satisfiable (amd64). -/
theorem convT32_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    ConvT32 (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧ RTPre R 1 s :=
  ⟨R0, _, R0_laws, convT32_impl, wstate fun _ => 0, rfl, wstate_rtpre _ 1 (by decide)⟩

/-- `mov $0x10300, %edx; mov %ax, (%rdx); mov %rdx, %rax; ret`. -/
def convT16Code : List Nat := [0xba, 0x00, 0x03, 0x01, 0x00, 0x66, 0x89, 0x02, 0x48, 0x89, 0xd0, 0xc3]

theorem convT16_impl : ConvT16 (toy.link (at0 convT16Code)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  janus64_run
  refine rtReturn_of R0 1 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl ?_
    ((show Env0 s.mem (s.regs 14) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
  · simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, R0_priv, R0_depth,
      List.append_nil, List.cons_append, List.nil_append]
    janus_frame
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    refine ⟨by decide, ?_, inPriv (by decide) (by decide), ?_⟩
    · rw [Janus.Arm64.Memory.accessible_writeLE]
      exact acc_read_of_write (Janus.Arm64.Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
    · show (Janus.Arm64.Memory.writeLE s.mem 66304 2 _).readLE 66304 2 = _
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      simp

/-- `ConvT16` is satisfiable (amd64). -/
theorem convT16_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    ConvT16 (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧ RTPre R 1 s :=
  ⟨R0, _, R0_laws, convT16_impl, wstate fun _ => 0, rfl, wstate_rtpre _ 1 (by decide)⟩

/-- `mov (%rbx), %rcx; mov $0x10300, %edx; mov %rcx, (%rdx); mov %rdx, %rax; ret`. -/
def convTCode : List Nat :=
  [0x48, 0x8b, 0x0b, 0xba, 0x00, 0x03, 0x01, 0x00, 0x48, 0x89, 0x0a, 0x48, 0x89, 0xd0, 0xc3]

/-- The model's types have 8-byte values. -/
theorem tySize_R0 {m : Janus.Arm64.Memory} {g : W64} (h : Env0 m g) {t : Nat} (ht : R0.IsType t) :
    tySize m t = 8 := by
  obtain ⟨-, -, d1, -, -, d4, -⟩ := h
  rcases ht with rfl | rfl
  · exact d1
  · exact d4

theorem convT_impl : ConvT (toy.link (at0 convTCode)) A0 R0 := by
  rw [link_at0]
  intro s hpc ⟨hpre, hty, hb, hacc⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  have hsz := tySize_R0 (g := s.regs 14) ⟨he1, he2, hd⟩ hty
  rw [hsz] at hb hacc
  janus64_run
  refine rtReturn_of R0 2 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl ?_
    ((show Env0 s.mem (s.regs 14) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])) ?_
  · simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, R0_priv, R0_depth,
      List.append_nil, List.cons_append, List.nil_append]
    janus_frame
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    rw [hsz]
    refine ⟨by decide, ?_, inPriv (by decide) (by decide), fun i hi => ?_⟩
    · rw [Janus.Arm64.Memory.accessible_writeLE]
      exact acc_read_of_write (Janus.Arm64.Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
    · show (Janus.Arm64.Memory.writeLE s.mem 66304 8 _).bytes (66304 + i) = _
      exact bytes_writeLE_readLE _ _ _ _ _ hi

/-- `ConvT` is satisfiable (amd64). -/
theorem convT_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    ConvT (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ R.IsType (s.regs 0).toNat ∧
        (s.regs 3).toNat + tySize s.mem (s.regs 0).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 3).toNat (tySize s.mem (s.regs 0).toNat) false = true) :=
  ⟨R0, _, R0_laws, convT_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 TD else if i = 3 then BitVec.ofNat 64 VAL else 0,
    rfl, wstate_rtpre _ 2 (by decide), Or.inl rfl, by decide, by decide⟩

theorem convTnoptr_impl : ConvTnoptr (toy.link (at0 convTCode)) A0 R0 :=
  Summary.mono convT_impl (fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩) fun _ _ _ h => h

/-- `ConvTnoptr` is satisfiable (amd64). -/
theorem convTnoptr_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    ConvTnoptr (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ R.IsType (s.regs 0).toNat ∧ tyPtrBytes s.mem (s.regs 0).toNat = 0 ∧
        (s.regs 3).toNat + tySize s.mem (s.regs 0).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 3).toNat (tySize s.mem (s.regs 0).toNat) false = true) :=
  ⟨R0, _, R0_laws, convTnoptr_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 TD else if i = 3 then BitVec.ofNat 64 VAL else 0,
    rfl, wstate_rtpre _ 2 (by decide), Or.inl rfl, by decide, by decide, by decide⟩

/-- `mov $0x10300, %edx; test %rbx, %rbx; jnz 1f; xor %eax, %eax; 1: mov %rax, (%rdx);
mov %rbx, 8(%rdx); mov %rdx, %rax; ret`. -/
def convTstringCode : List Nat :=
  [0xba, 0x00, 0x03, 0x01, 0x00, 0x48, 0x85, 0xdb, 0x75, 0x02, 0x31, 0xc0, 0x48, 0x89, 0x02,
   0x48, 0x89, 0x5a, 0x08, 0x48, 0x89, 0xd0, 0xc3]

theorem convTstring_impl : ConvTstring (toy.link (at0 convTstringCode)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  janus64_run
  all_goals
    refine rtReturn_of R0 2 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl ?_
      (((show Env0 s.mem (s.regs 14) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])).writeLE _
        (by simp [BOX])) ?_
    · simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, R0_priv, R0_depth,
        List.append_nil, List.cons_append, List.nil_append]
      janus_frame
    · simp only [BoxWords, setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat,
        List.length_cons, List.length_nil]
      refine ⟨by decide, ?_, inPriv (by decide) (by decide), fun i hi => ?_⟩
      · rw [Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.accessible_writeLE]
        exact acc_read_of_write (Janus.Arm64.Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
      · simp at hi
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · rw [show 66304 % 2 ^ 64 + 8 * 0 = 66304 from rfl,
            Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
            Janus.Arm64.Memory.readLE_writeLE_self]
          simp_all [Nat.mod_eq_of_lt (s.regs 0).isLt]
        · rw [show 66304 % 2 ^ 64 + 8 * 1 = 66312 from rfl, Janus.Arm64.Memory.readLE_writeLE_self]
          simp [Nat.mod_eq_of_lt (s.regs 3).isLt]

/-- `ConvTstring` is satisfiable (amd64). -/
theorem convTstring_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    ConvTstring (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      RTPre R 2 s :=
  ⟨R0, _, R0_laws, convTstring_impl, wstate fun _ => 0, rfl, wstate_rtpre _ 2 (by decide)⟩

/-- `mov $0x10300, %edx; test %rax, %rax; jz nil; mov %rax, (%rdx); mov %rbx, 8(%rdx);
mov %rcx, 16(%rdx); mov %rdx, %rax; ret; nil: movq $0, (%rdx); movq $0, 8(%rdx);
movq $0, 16(%rdx); mov %rdx, %rax; ret`. -/
def convTsliceCode : List Nat :=
  [0xba, 0x00, 0x03, 0x01, 0x00, 0x48, 0x85, 0xc0, 0x74, 0x0f, 0x48, 0x89, 0x02, 0x48, 0x89, 0x5a,
   0x08, 0x48, 0x89, 0x4a, 0x10, 0x48, 0x89, 0xd0, 0xc3, 0x48, 0xc7, 0x02, 0x00, 0x00, 0x00, 0x00,
   0x48, 0xc7, 0x42, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x42, 0x10, 0x00, 0x00, 0x00, 0x00,
   0x48, 0x89, 0xd0, 0xc3]

theorem convTslice_impl : ConvTslice (toy.link (at0 convTsliceCode)) A0 R0 := by
  rw [link_at0]
  intro s hpc hpre
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  janus64_run
  all_goals
    refine rtReturn_of R0 3 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl ?_
      ((((show Env0 s.mem (s.regs 14) from ⟨he1, he2, hd⟩).writeLE _ (by simp [BOX])).writeLE _
        (by simp [BOX])).writeLE _ (by simp [BOX])) ?_
    · simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, R0_priv, R0_depth,
        List.append_nil, List.cons_append, List.nil_append]
      janus_frame
    · simp only [BoxWords, setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat,
        List.length_cons, List.length_nil]
      refine ⟨by decide, ?_, inPriv (by decide) (by decide), fun i hi => ?_⟩
      · rw [Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.accessible_writeLE,
          Janus.Arm64.Memory.accessible_writeLE]
        exact acc_read_of_write (Janus.Arm64.Memory.accessible_mono _ he2 (Nat.le_refl _) (by decide))
      · simp only [show 66304 % 2 ^ 64 = 66304 from rfl]
        exact Janus.Contracts.IfaceSat.read3 _ 66304 _ _ _ i (by simpa using hi)
          (by first | decide | exact BitVec.isLt _) (by first | decide | exact BitVec.isLt _)
          (by first | decide | exact BitVec.isLt _)

/-- `ConvTslice` is satisfiable (amd64). -/
theorem convTslice_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    ConvTslice (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      RTPre R 3 s :=
  ⟨R0, _, R0_laws, convTslice_impl, wstate fun _ => 0, rfl, wstate_rtpre _ 3 (by decide)⟩

/-! ## Assertions and switches -/

/-- `mov $0x10200, %eax; ret`: the one itab. -/
def assertE2ICode : List Nat := [0xb8, 0x00, 0x02, 0x01, 0x00, 0xc3]

theorem assertE2I_impl : AssertE2I (toy.link (at0 assertE2ICode)) A0 R0 := by
  rw [link_at0]
  intro s hpc ⟨hpre, hi, ht0, ht, hsome⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  simp only [R0_isInter] at hi
  simp only [R0_itab, hi, true_and] at hsome
  have htd : (s.regs 3).toNat = TD := by
    by_cases hne : (s.regs 3).toNat = TD
    · exact hne
    · simp [hne] at hsome
  janus64_run
  refine rtReturn_of R0 2 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
  refine ⟨?_, fun _ => ?_⟩
  · simp [htd, hi, TD, TAB]
  · rw [hi, htd]; exact Janus.Contracts.IfaceSat.itabAt_TAB (g := s.regs 14) ⟨he1, he2, hd⟩

/-- `AssertE2I` is satisfiable (amd64). -/
theorem assertE2I_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    AssertE2I (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ R.IsInter (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧
        R.IsType (s.regs 3).toNat ∧ (R.itab (s.regs 0).toNat (s.regs 3).toNat).isSome) :=
  ⟨R0, _, R0_laws, assertE2I_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 ID else if i = 3 then BitVec.ofNat 64 TD else 0,
    rfl, wstate_rtpre _ 2 (by decide), rfl, by decide, Or.inl rfl, by decide⟩

/-- `xor %eax, %eax; cmp $0x10000, %rbx; jne 1f; mov $0x10200, %eax; 1: ret`: the itab for
`TD`, `0` otherwise. -/
def assertE2I2Code : List Nat :=
  [0x31, 0xc0, 0x48, 0x81, 0xfb, 0x00, 0x00, 0x01, 0x00, 0x75, 0x05, 0xb8, 0x00, 0x02, 0x01, 0x00, 0xc3]

theorem assertE2I2_impl : AssertE2I2 (toy.link (at0 assertE2I2Code)) A0 R0 := by
  rw [link_at0]
  intro s hpc ⟨hpre, hi, ht⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  simp only [R0_isInter] at hi
  have := Janus.Contracts.IfaceSat.itabResult_R0 (g := s.regs 14) ⟨he1, he2, hd⟩ (s.regs 3).toNat
  janus64_run
  all_goals
    rw [hi]
    refine rtReturn_of R0 2 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    simp only [TD, TAB] at this
    have hlt := (s.regs 3).isLt
    first
      | (have h3 : (s.regs 3).toNat = 65536 := by omega
         simpa [h3] using this)
      | (have h3 : (s.regs 3).toNat ≠ 65536 := by omega
         simpa [h3] using this)

/-- `AssertE2I2` is satisfiable (amd64). -/
theorem assertE2I2_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    AssertE2I2 (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ R.IsInter (s.regs 0).toNat ∧ ((s.regs 3).toNat ≠ 0 → R.IsType (s.regs 3).toNat)) :=
  ⟨R0, _, R0_laws, assertE2I2_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 ID else if i = 3 then BitVec.ofNat 64 TD else 0,
    rfl, wstate_rtpre _ 2 (by decide), rfl, fun _ => Or.inl rfl⟩

theorem typeAssert_impl : TypeAssert (toy.link (at0 assertE2I2Code)) A0 R0 := by
  rw [link_at0]
  intro s hpc ⟨hpre, hdesc, _, _⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  have hi : taInter s.mem (s.regs 0).toNat = ID := hdesc.2.2.2.1
  have := Janus.Contracts.IfaceSat.itabResult_R0 (g := s.regs 14) ⟨he1, he2, hd⟩ (s.regs 3).toNat
  janus64_run
  all_goals
    refine rtReturn_of R0 2 _ s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
    refine ⟨?_, hdesc, rfl, rfl⟩
    rw [hi]
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    simp only [TD, TAB] at this
    have hlt := (s.regs 3).isLt
    first
      | (have h3 : (s.regs 3).toNat = 65536 := by omega
         simpa [h3] using this)
      | (have h3 : (s.regs 3).toNat ≠ 65536 := by omega
         simpa [h3] using this)

/-- `TypeAssert` is satisfiable (amd64). -/
theorem typeAssert_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    TypeAssert (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ TADescOK R s.mem (s.regs 0).toNat ∧
        ((s.regs 3).toNat = 0 → taCanFail s.mem (s.regs 0).toNat = true) ∧
        ((s.regs 3).toNat ≠ 0 → R.IsType (s.regs 3).toNat ∧
          (taCanFail s.mem (s.regs 0).toNat = true ∨
            (R.itab (taInter s.mem (s.regs 0).toNat) (s.regs 3).toNat).isSome))) :=
  ⟨R0, _, R0_laws, typeAssert_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 DTA else if i = 3 then BitVec.ofNat 64 TD else 0,
    rfl, wstate_rtpre _ 2 (by decide), wmem_taDesc, by decide, fun _ => ⟨Or.inl rfl, Or.inl (by decide)⟩⟩

/-- `mov 8(%rax), %rcx; cmp $0x10000, %rbx; jne no; test %rcx, %rcx; jz no; xor %eax, %eax;
mov $0x10200, %ebx; ret; no: mov %rcx, %rax; xor %ebx, %ebx; ret`. -/
def interfaceSwitchCode : List Nat :=
  [0x48, 0x8b, 0x48, 0x08, 0x48, 0x81, 0xfb, 0x00, 0x00, 0x01, 0x00, 0x75, 0x0d, 0x48, 0x85, 0xc9,
   0x74, 0x08, 0x31, 0xc0, 0xbb, 0x00, 0x02, 0x01, 0x00, 0xc3, 0x48, 0x89, 0xc8, 0x31, 0xdb, 0xc3]

theorem interfaceSwitch_impl : InterfaceSwitch (toy.link (at0 interfaceSwitchCode)) A0 R0 := by
  rw [link_at0]
  intro cs s hpc ⟨hpre, hdesc, ht0, ht⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, -, hn, -, hcs, -⟩ := hdesc'
  have hcs' : ∀ c ∈ cs, c = ID := hcs
  have hlen : cs.length < 2 ^ 48 := by omega
  have hsw := Janus.Contracts.IfaceModel.switchCase_R0 (s.regs 3).toNat cs hcs'
  have hlt3 := (s.regs 3).isLt
  by_cases htd : (s.regs 3).toNat = 65536 <;> by_cases hc0 : cs.length = 0
  all_goals
    janus64_run [hn]
    refine rtReturn_of R0 2 _ s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
    simp only [setRegF, reduceIte, Nat.reduceEqDiff]
    refine ⟨?_, ?_, ?_, hdesc⟩
  all_goals (try rw [htd]) <;> (try rw [hsw]) <;> (try rw [htd] at hsw)
  all_goals (try simp only [BitVec.toNat_ofNat])
  all_goals first
    | (simp_all [TD, TAB]; done)
    | (intro hne
       obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
         cases cs with
         | nil => simp_all
         | cons c cs' => exact ⟨c, cs', rfl⟩
       rw [hcs' c (by simp)]
       simpa [TD, TAB, htd] using Janus.Contracts.IfaceSat.itabAt_TAB (g := s.regs 14) ⟨he1, he2, hd⟩)
    | (rw [if_neg (fun h => by simp only [TD] at h; omega)]; exact Nat.mod_eq_of_lt (by omega))
    | done

/-- `InterfaceSwitch` is satisfiable (amd64; shown for the case list `[ID]`). -/
theorem interfaceSwitch_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    InterfaceSwitch (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre R 2 s ∧ ISDescOK R s.mem (s.regs 0).toNat [ID] ∧ (s.regs 3).toNat ≠ 0 ∧
        R.IsType (s.regs 3).toNat) :=
  ⟨R0, _, R0_laws, interfaceSwitch_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 DIS else if i = 3 then BitVec.ofNat 64 TD else 0,
    rfl, wstate_rtpre _ 2 (by decide), wmem_isDesc, by decide, Or.inl rfl⟩

/-! ## Comparison -/

/-- `test %rax, %rax; jz nil; mov (%rbx), %rdx; cmp (%rcx), %rdx; sete %al; ret; nil: mov $1, %eax;
ret`: compare the 8-byte values (`TD`'s equality), `true` for a nil type or itab. -/
def efaceeqCode : List Nat :=
  [0x48, 0x85, 0xc0, 0x74, 0x0a, 0x48, 0x8b, 0x13, 0x48, 0x3b, 0x11, 0x0f, 0x94, 0xc0, 0xc3,
   0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]

theorem efaceeq_impl : Efaceeq (toy.link (at0 efaceeqCode)) A0 R0 := by
  rw [link_at0]
  intro s hpc ⟨hpre, hok⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  by_cases h0 : (s.regs 0).toNat = 0
  · janus64_run
    all_goals
      refine rtReturn_of R0 3 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
        (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
      simp [setRegF, efaceEqual, h0]
  · obtain ⟨-, htd, hx, hy⟩ := hok h0
    janus64_run
    all_goals
      refine rtReturn_of R0 3 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
        (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
      rw [htd, Janus.Contracts.IfaceSat.efaceEqual_R0 (g := s.regs 14) ⟨he1, he2, hd⟩]
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, setcc_low_byte]
      have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 1).toNat 8
      have hb := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
      simp only [Nat.reducePow] at ha hb
      split
      · rename_i h
        have : Janus.Arm64.Memory.readLE s.mem (s.regs 3).toNat 8 =
            Janus.Arm64.Memory.readLE s.mem (s.regs 1).toNat 8 := by omega
        simp [this]
      · rename_i h
        have : Janus.Arm64.Memory.readLE s.mem (s.regs 3).toNat 8 ≠
            Janus.Arm64.Memory.readLE s.mem (s.regs 1).toNat 8 := by omega
        simp [beq_false_of_ne this]

/-- `Efaceeq` is satisfiable (amd64). -/
theorem efaceeq_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    Efaceeq (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre R 3 s ∧ EqOK R s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) :=
  ⟨R0, _, R0_laws, efaceeq_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 TD else if i = 3 ∨ i = 1 then BitVec.ofNat 64 VAL else 0,
    rfl, wstate_rtpre _ 3 (by decide), fun _ => ⟨Or.inl rfl, rfl, by decide, by decide⟩⟩

theorem ifaceeq_impl : Ifaceeq (toy.link (at0 efaceeqCode)) A0 R0 := by
  rw [link_at0]
  intro s hpc ⟨hpre, hok⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  by_cases h0 : (s.regs 0).toNat = 0
  · janus64_run
    all_goals
      refine rtReturn_of R0 3 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
        (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
      simp [setRegF, ifaceEqual, h0]
  · obtain ⟨-, -, ht0, hok⟩ := hok h0
    obtain ⟨-, ht, hx, hy⟩ := hok ht0
    janus64_run
    all_goals
      refine rtReturn_of R0 3 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
        (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
      simp only [ifaceEqual, ht]
      rw [Janus.Contracts.IfaceSat.efaceEqual_R0 (g := s.regs 14) ⟨he1, he2, hd⟩]
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, setcc_low_byte, beq_false_of_ne h0,
        Bool.false_or]
      have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 1).toNat 8
      have hb := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
      simp only [Nat.reducePow] at ha hb
      split
      · rename_i h
        have : Janus.Arm64.Memory.readLE s.mem (s.regs 3).toNat 8 =
            Janus.Arm64.Memory.readLE s.mem (s.regs 1).toNat 8 := by omega
        simp [this]
      · rename_i h
        have : Janus.Arm64.Memory.readLE s.mem (s.regs 3).toNat 8 ≠
            Janus.Arm64.Memory.readLE s.mem (s.regs 1).toNat 8 := by omega
        simp [beq_false_of_ne this]

/-- `Ifaceeq` is satisfiable (amd64). -/
theorem ifaceeq_satisfiable : ∃ (R : IfaceModel) (impl : List Janus.Amd64.Segment), R.Laws ∧
    Ifaceeq (toy.link impl) A0 R ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (RTPre R 3 s ∧ ((s.regs 0).toNat ≠ 0 →
        (s.regs 0).toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 16 false = true ∧
        (s.mem.readLE ((s.regs 0).toNat + 8) 8 ≠ 0) ∧
        EqOK R s.mem (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.regs 3).toNat (s.regs 1).toNat)) :=
  ⟨R0, _, R0_laws, ifaceeq_impl,
    wstate fun i => if i = 0 then BitVec.ofNat 64 TAB else if i = 3 ∨ i = 1 then BitVec.ofNat 64 VAL else 0,
    rfl, wstate_rtpre _ 3 (by decide), fun _ => ⟨by decide, by decide, by decide,
      fun _ => ⟨Or.inl (by decide), by decide, by decide, by decide⟩⟩⟩

end Janus.Contracts.IfaceSatAmd64
