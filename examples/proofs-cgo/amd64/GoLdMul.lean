import Extracted

/-!
# `MulLD(a, b, r *[16]byte)` (Go) → `c_ldmul` → `ld_mul` (C, x87 `long double`) → Go, end to end (amd64)

```go
func MulLD(a, b, r *[16]byte) {
	C.c_ldmul((*C.ld16)(unsafe.Pointer(a)), (*C.ld16)(unsafe.Pointer(b)), (*C.ld16)(unsafe.Pointer(r)))
}
```
```c
__attribute__((noinline)) long double ld_mul(long double a, long double b) { return a * b; }
void c_ldmul(const ld16 *a, const ld16 *b, ld16 *r) {
	*(long double *)r = ld_mul(*(const long double *)a, *(const long double *)b);
}
```

**Guarantee (`correctness`).** For all pointers `a`, `b`, `r` and every Go call of
`example.com/cgo.MulLD` satisfying `GoPre` — the stack-growth checks fall through, the stack
window is writable, the TLS `g` slot holds `g`, the x87 FPU is idle (`X87.Idle`: empty register
stack, nothing pending) with the Linux control word (`fpucw = 0x037F`), 16 readable bytes at `a`
and `b` and 10 writable ones at `r` away from the stack, the `g` struct and the TLS slot, and
the cgo globals hold their static values — every run returns and the 10 bytes at `r` are
`prod s.mem a b`: the x87 product of the double-extended values in the low 10 bytes of `a` and
`b`, rounded to nearest at 64-bit precision (`X87.binop .mul 64 .rne`; by
`X87.binop_mul_ieee`, IEEE 754 multiplication on the format (15, 63) for supported operands).

The statement is under the trusted `CgoCall Extracted.program` only: the Go code, the cgo
wrapper, `c_ldmul` (which `push`es the two operands, calls `ld_mul` and stores `ST(0)` with
`fstpt`) and `ld_mul` (`fldt; fldt; fmulp`) are executed by the model, x87 included.
`wrapper_spec` (the C side, for every value of `TOP`), `go_spec` (the Go side under
`CgoSpec wrapper G E`), `refines` and `correctness` compose them as in `GoSum.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Spec
  Janus.Amd64.FFI

namespace Proof

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_ad79fd856801_Cfunc_c_ldmul"

abbrev frameA (m : Memory) (a : Nat) : Nat := m.readLE a 8
abbrev frameB (m : Memory) (a : Nat) : Nat := m.readLE (a + 8) 8
abbrev frameR (m : Memory) (a : Nat) : Nat := m.readLE (a + 16) 8

/-- `[x, x + n)` is away from the C stack window of `t`. -/
abbrev Away (t : State) (x n : Nat) : Prop :=
  x + n ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ x

/-- The product the C code stores. -/
def prod (m : Memory) (pa pb : Nat) : Nat :=
  (X87.binop .mul 64 .rne (m.readLE pa 10) (m.readLE pb 10)).res

theorem prod_lt (m : Memory) (pa pb : Nat) : prod m pa pb < 2 ^ 80 :=
  X87.binop_lt _ _ _ _ _ (Janus.Arm64.Memory.readLE_lt _ _ _) (Janus.Arm64.Memory.readLE_lt _ _ _)

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 8 ∧ a.toNat + 24 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 24 false = true ∧ Away t a.toNat 24 ∧
    frameA t.mem a.toNat + 16 ≤ 2 ^ 48 ∧ t.mem.accessible (frameA t.mem a.toNat) 16 false = true ∧
    Away t (frameA t.mem a.toNat) 16 ∧
    frameB t.mem a.toNat + 16 ≤ 2 ^ 48 ∧ t.mem.accessible (frameB t.mem a.toNat) 16 false = true ∧
    Away t (frameB t.mem a.toNat) 16 ∧
    frameR t.mem a.toNat + 10 ≤ 2 ^ 48 ∧ t.mem.accessible (frameR t.mem a.toNat) 10 true = true ∧
    Away t (frameR t.mem a.toNat) 10 ∧ X87.Idle t.x87 ∧ t.fpucw = 0x37F

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (frameR t.mem a.toNat) 10
      (prod t.mem (frameA t.mem a.toNat) (frameB t.mem a.toNat))) t'.mem
    [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]

/-- A 10-byte read as its low 8 and high 2 bytes. -/
theorem readLE_ten (m : Memory) (x : Nat) : m.readLE x 10 = m.readLE x 8 + 2 ^ 64 * m.readLE (x + 8) 2 :=
  Janus.Arm64.Memory.readLE_add m x 8 2

theorem readLE_two_of_eight (m : Memory) (x : Nat) : m.readLE x 8 % 65536 = m.readLE x 2 :=
  Janus.Arm64.Memory.readLE_mod m x 8 2 (by decide)

/-- The same 10-byte store, of equal values, on both sides keeps a frame. -/
theorem frame_store10 {m m' : Memory} {rs : List (Nat × Nat)} {a v v' : Nat} (h : MemFrame m m' rs)
    (hv : v' = v) : MemFrame (m.writeLE a 10 v) (m'.writeLE a 10 v') rs :=
  hv ▸ h.writeLE_both a 10 v

set_option maxHeartbeats 4000000 in
theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd, hab, haa, had, hbb, hba, hbd, hrb, hra, hrd,
    ⟨htags, hes, htp⟩, hcw⟩
  apply ReturnsC.of_reaches
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : t.regs 7 = a := hs.reg (i := 0) (by simp)
  simp only [Amd64.Program.withExit] at h_ret
  simp only [CABI.regSP, frameA, frameB, frameR, Away] at hal hb htop hacc haa hab had hbb hba hbd hrb hra hrd
  janus64_run [hcw, htags, hes]
  simp only [WPost, prod, frameA, frameB, frameR]
  apply frame_store10
  · janus_frame
  · rw [readLE_ten, readLE_ten, readLE_ten t.mem, readLE_ten t.mem]
    janus64_simp
    have e1 : (t.regs 4).toNat - 48 + 8 + 8 - ((t.regs 4).toNat - 32) = 0 := by omega
    have e2 : (t.regs 4).toNat - 48 + 24 + 8 - ((t.regs 4).toNat - 16) = 0 := by omega
    rw [e1, e2, Nat.pow_zero, Nat.div_one, Nat.div_one, readLE_two_of_eight, readLE_two_of_eight]


/-! ## The Go side: `MulLD` → `_Cfunc_c_ldmul` → `runtime.cgocall` -/

def fnVar : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo._Cfunc_c_ldmul.abi0" + 0x25)

def alwaysFalse : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo._Cfunc_c_ldmul.abi0" + 0x3e)

/-- The return address of `MulLD`'s call of `_Cfunc_c_ldmul`, reloaded after the C call. -/
def retMul : Nat := segAddr Extracted.program "example.com/cgo.MulLD" + 0x25

/-- At the `cgocall`: the frame `RBX` and the three operands it points at are Go memory the
runtime leaves alone, and the x87 FPU is in its call state. -/
def G (s : State) : Prop :=
  (s.regs 3).toNat + 24 ≤ 2 ^ 48 ∧ GoKept s (s.regs 3).toNat 24 false ∧
    frameA s.mem (s.regs 3).toNat + 16 ≤ 2 ^ 48 ∧ GoKept s (frameA s.mem (s.regs 3).toNat) 16 false ∧
    frameB s.mem (s.regs 3).toNat + 16 ≤ 2 ^ 48 ∧ GoKept s (frameB s.mem (s.regs 3).toNat) 16 false ∧
    frameR s.mem (s.regs 3).toNat + 10 ≤ 2 ^ 48 ∧ GoKept s (frameR s.mem (s.regs 3).toNat) 10 true ∧
    X87.Idle s.x87 ∧ s.fpucw = 0x37F

def E (s : State) : Memory :=
  s.mem.writeLE (frameR s.mem (s.regs 3).toNat) 10
    (prod s.mem (frameA s.mem (s.regs 3).toNat) (frameB s.mem (s.regs 3).toNat))

/-- The stack window of `MulLD` and its callees up to `cgocall`, the `g` struct, the TLS slot. -/
abbrev Shared (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 1104, (s.regs 4).toNat + 8), ((s.regs 14).toNat, (s.regs 14).toNat + 456),
    (s.fsBase.toNat - 8, s.fsBase.toNat)]

def GoPre (a b r : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 40 ∧ StackWritable s 80 8 ∧ TlsG s ∧ X87.Idle s.x87 ∧ s.fpucw = 0x37F ∧
  a.toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible a.toNat 16 false = true ∧
  b.toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible b.toNat 16 false = true ∧
  r.toNat + 10 ≤ 2 ^ 48 ∧ s.mem.accessible r.toNat 10 true = true ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 = 0 ∧
  Outside (s.regs 14).toNat 456 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat - 8) 8 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 8)] ∧
  Outside fnVar 8 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 8)] ∧
  Outside alwaysFalse 1 (Shared s) ∧
  Outside a.toNat 16 (Shared s) ∧ Outside b.toNat 16 (Shared s) ∧ Outside r.toNat 10 (Shared s) ∧
  Outside r.toNat 10 [(alwaysFalse, alwaysFalse + 1)]

/-- An address range away from `Shared` is away from the clobber list of the `cgocall` state. -/
theorem outside_clobber (x n sp g fs : Nat) (hsp : 80 ≤ sp)
    (h : (x + n ≤ sp - 1104 ∨ sp + 8 ≤ x) ∧ (x + n ≤ g ∨ g + 456 ≤ x) ∧ (x + n ≤ fs - 8 ∨ fs ≤ x)) :
    Outside x n [(sp - 80 - 1024, sp - 80), (sp - 80 + 8, sp - 80 + 24), (g, g + 456), (fs - 8, fs)] := by
  simp only [outside_cons, outside_nil, and_true]
  obtain ⟨h1 | h1, h2 | h2, h3 | h3⟩ := h <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- A proposition kept folded. -/
def Keep (p : Prop) : Prop := p

set_option maxHeartbeats 20000000 in
theorem go_spec (a b r : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [a, b, r] (GoPre a b r)
      (fun s s' => s'.mem.readLE r.toNat 10 = prod s.mem a.toNat b.toNat) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, htop, hst⟩, ⟨hfs, hfsr, hfsg⟩, hx87, hfcw, hab, haa, hbb, hba,
    hrb, hra, hfa, hfv, haf, hav, hdg, hdt, hdf, hda, hdA, hdB, hdR, hdRA⟩
  apply ReturnsC.of_reaches
  janus64_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  janus_eval_nat h_ra : retMul
  -- the operand facts stay folded (`Keep`) during the runs: as disjunctions in the context they
  -- would make every `omega` call of the symbolic executor split exponentially
  have hKeep : Keep (Outside a.toNat 16 (Shared s) ∧ Outside b.toNat 16 (Shared s) ∧
      Outside r.toNat 10 (Shared s) ∧ Outside r.toNat 10 [(alwaysFalse, alwaysFalse + 1)]) :=
    ⟨hdA, hdB, hdR, hdRA⟩
  clear hdA hdB hdR hdRA
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haf hav hda
  simp only [Shared, outside_cons, outside_nil, and_true, Janus.Amd64.GoABI.regSP,
    Janus.Amd64.GoABI.regG, stackguard0, stackguard0Offset] at *
  have hfsa : (s.fsBase + BitVec.ofNat 64 18446744073709551608).toNat = s.fsBase.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h32 : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h80 : (s.regs 4 - 80#64).toNat = (s.regs 4).toNat - 80 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hO1 : Outside alwaysFalse 1 [((s.regs 4).toNat - 80 - 1024, (s.regs 4).toNat - 80),
      ((s.regs 4).toNat - 80 + 8, (s.regs 4).toNat - 80 + 24), ((s.regs 14).toNat, (s.regs 14).toNat + 456),
      (s.fsBase.toNat - 8, s.fsBase.toNat)] := by rw [h_af]; exact outside_clobber _ _ _ _ _ hb hda
  have hO2 : Outside r.toNat 10 [((s.regs 4).toNat - 80 - 1024, (s.regs 4).toNat - 80),
      ((s.regs 4).toNat - 80 + 8, (s.regs 4).toNat - 80 + 24), ((s.regs 14).toNat, (s.regs 14).toNat + 456),
      (s.fsBase.toNat - 8, s.fsBase.toNat)] := by
    have hdR := hKeep.2.2.1
    try simp only [Shared, outside_cons, outside_nil, and_true] at hdR
    exact outside_clobber _ _ _ _ _ hb hdR
  janus64_run [hfsa]
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · simp only [G, GoKept, frameA, frameB, frameR, cgoClobber, Janus.Amd64.GoABI.regSP,
      Janus.Amd64.GoABI.regG, cgoStackScratch, gStructSize, outside_cons, outside_nil, and_true]
    janus64_simp [h32, h80]
    obtain ⟨hdA, hdB, hdR, -⟩ := hKeep
    try simp only [Shared, outside_cons, outside_nil, and_true] at hdA hdB hdR
    refine ⟨by omega, ⟨?_, by omega, by omega, by omega, by omega⟩, by omega,
      ⟨haa, by omega, by omega, by omega, by omega⟩, by omega, ⟨hba, by omega, by omega, by omega, by omega⟩,
      by omega, ⟨hra, by omega, by omega, by omega, by omega⟩, hx87, hfcw⟩
    janus64_disch
  rintro s' ⟨-, m, ⟨regs, fl, xm, yh, fs, mx, x87, zh, kr, rfl, h4, h5, h14, h15, ⟨⟨hfs1, hfs2⟩, hfsr', hfsg'⟩, -⟩, hmf⟩
  simp only [E, frameA, frameB, frameR, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    Janus.Amd64.GoABI.regFP, Janus.Amd64.GoABI.xmmZero, cgoStackScratch, gStructSize, setRegF,
    ↓reduceIte, Nat.reduceEqDiff, h32, h80] at hmf h4 h5 h14 h15 hfs1 hfs2 hfsr' hfsg'
  have hfsa' : (fs + BitVec.ofNat 64 18446744073709551608).toNat = fs.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- the frame words (and so the result pointer) as plain values
  revert hmf
  janus64_simp [h32, h80]
  intro hmf
  -- the two facts the rest of the run needs from the C call: the cgo global is still false and
  -- the result is at `r`; then the frame is no longer needed
  have hAF : m.readLE alwaysFalse 1 = 0 := by
    rw [hmf.readLE _ 1 hO1, h_af]
    have hdRA := hKeep.2.2.2
    rw [h_af] at hdRA
    try simp only [outside_cons, outside_nil, and_true] at hdRA
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hav
  have hAFacc : m.accessible alwaysFalse 1 false = true := by
    rw [hmf.accessible, h_af]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact haf
  rw [h_af] at hAF hAFacc
  have hR : m.readLE r.toNat 10 = prod s.mem a.toNat b.toNat := by
    rw [hmf.readLE r.toNat 10 hO2,
      Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (by rw [show (256 : Nat) ^ 10 = 2 ^ 80 by decide]; exact prod_lt _ _ _)]
    unfold prod
    obtain ⟨hdA, hdB, -, -⟩ := hKeep
    try simp only [Shared, outside_cons, outside_nil, and_true] at hdA hdB
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  -- the stack words the epilogues of `_Cfunc_c_ldmul` and `MulLD` reload (outside the clobbered
  -- range, so `cgocall` kept them), and the stack's accessibility
  have hdR := hKeep.2.2.1
  try simp only [Shared, outside_cons, outside_nil, and_true] at hdR
  have hS8 : m.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hmf.readLE _ 8 (by simp only [outside_cons, outside_nil, and_true]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    have := (s.regs 5).isLt; simp only [Nat.reducePow]; omega
  have hS40 : m.readLE ((s.regs 4).toNat - 40) 8 = retMul := by
    rw [h_ra]
    rw [hmf.readLE _ 8 (by simp only [outside_cons, outside_nil, and_true]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  have hS48 : m.readLE ((s.regs 4).toNat - 48) 8 = (s.regs 4).toNat - 8 := by
    rw [hmf.readLE _ 8 (by simp only [outside_cons, outside_nil, and_true]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    have := (s.regs 4).isLt; simp only [Nat.reducePow]; omega
  have hS0 : m.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hmf.readLE _ 8 (by simp only [outside_cons, outside_nil, and_true]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  clear hdR
  have hSacc : m.accessible ((s.regs 4).toNat - 80) (80 + 8) true = true := by
    rw [hmf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hst
  rw [h_ra] at hS40
  clear hmf
  apply ReturnsC.of_reaches
  janus64_run [h4, h5, h14, h15, hfsa', hfsg', hAF, hAFacc, hS0, hS8, hS40, hS48]

/-! ## Composition -/

set_option maxHeartbeats 4000000 in
theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, ⟨hacc, hout⟩, hab, ⟨haacc, haout⟩, hbb, ⟨hbacc, hbout⟩, hrb, ⟨hracc, hrout⟩, hx, hc⟩ he
    have hsep := he.stackSep _ _ _ hacc
    have hasep := he.stackSep _ _ _ haacc
    have hbsep := he.stackSep _ _ _ hbacc
    have hrsep := he.stackSep _ _ _ hracc
    have hk : ∀ c n, (s.regs 3).toNat ≤ c → c + n ≤ (s.regs 3).toNat + 24 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    have hk0 := hk _ 8 (Nat.le_refl _) (by omega)
    have hk1 := hk ((s.regs 3).toNat + 8) 8 (by omega) (by omega)
    have hk2 := hk ((s.regs 3).toNat + 16) 8 (by omega) (by omega)
    simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP]
      at hsep hasep hbsep hrsep
    simp only [WPre, frameA, frameB, frameR, Away] at hab haacc haout hbb hbacc hbout hrb hracc hrout hasep hbsep hrsep ⊢
    rw [hk0, hk1, hk2, he.x87, he.fpucw]
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by omega, hab,
      he.keptAcc _ _ _ ⟨haacc, haout⟩, by omega, hbb, he.keptAcc _ _ _ ⟨hbacc, hbout⟩, by omega,
      hrb, he.keptAcc _ _ _ ⟨hracc, hrout⟩, by omega, hx, hc⟩
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, ⟨hacc, hout⟩, hab, ⟨haacc, haout⟩, hbb, ⟨hbacc, hbout⟩, hrb, ⟨hracc, hrout⟩, _, _⟩
      he _ hpost b hb' hbacc'
    have hsep := he.stackSep b 1 false hbacc'
    have h1 := hpost.readLE b 1 (by
      simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep ⊢; omega)
    simp only [Janus.Arm64.Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 3).toNat ≤ c → c + n ≤ (s.regs 3).toNat + 24 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    have e0 := hk _ 8 (Nat.le_refl _) (by omega)
    have e1 := hk ((s.regs 3).toNat + 8) 8 (by omega) (by omega)
    have e2 := hk ((s.regs 3).toNat + 16) 8 (by omega) (by omega)
    simp only [frameA, frameB, frameR] at hab haacc haout hbb hbacc hbout hrb hracc hrout ⊢
    have ea : t.mem.readLE (s.mem.readLE (s.regs 3).toNat 8) 10 = s.mem.readLE (s.mem.readLE (s.regs 3).toNat 8) 10 :=
      he.kept _ 10 ⟨Janus.Arm64.Memory.accessible_sub _ haacc (Or.inl rfl) (Nat.le_refl _) (by omega),
        Outside.of_sub haout (Nat.le_refl _) (by omega)⟩
    have eb : t.mem.readLE (s.mem.readLE ((s.regs 3).toNat + 8) 8) 10 =
        s.mem.readLE (s.mem.readLE ((s.regs 3).toNat + 8) 8) 10 :=
      he.kept _ 10 ⟨Janus.Arm64.Memory.accessible_sub _ hbacc (Or.inl rfl) (Nat.le_refl _) (by omega),
        Outside.of_sub hbout (Nat.le_refl _) (by omega)⟩
    rw [e0, e1, e2]
    simp only [prod]
    rw [ea, eb]
    split
    · rfl
    · have := he.kept b 1 ⟨hbacc', hb'⟩
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, hab, -, hbb, -, hrb, ⟨hracc, hrout⟩, _, _⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hracc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`MulLD` end to end**: for every Go call of `example.com/cgo.MulLD(a, b, r)` satisfying
`GoPre` (in particular the x87 FPU idle, `X87.Idle`), every run returns and the 10 bytes at
`r` are the double-extended product of the 10 bytes at `a` and at `b`, rounded to nearest at
64-bit precision (`X87.binop_mul_ieee`: IEEE 754 multiplication on (15, 63) for supported
operands), under the trusted `CgoCall` only. -/
theorem correctness (a b r : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [a, b, r] (GoPre a b r)
      (fun s s' => s'.mem.readLE r.toNat 10 = prod s.mem a.toNat b.toNat) :=
  (go_spec a b r).refine refines

end Proof
