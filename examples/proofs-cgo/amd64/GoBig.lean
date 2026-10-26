import Extracted

/-!
# `Big(x, y int64) (int64, int64, int64, int64)` (Go) → `k_big` (C, a 32-byte MEMORY-class
# struct returned through the hidden `RDI` pointer) → back to Go, end to end (amd64)

```go
func Big(x, y int64) (int64, int64, int64, int64) {
	r := C.k_big(C.int64_t(x), C.int64_t(y))
	return int64(r.a), int64(r.b), int64(r.c), int64(r.d)
}
```

**Guarantee (`correctness`).** For all 64-bit `x`, `y`, every Go call of
`example.com/cgo/cabi.Big` with `x`, `y` in `RAX`, `RBX` (Go's ABIInternal) satisfying `GoPre`
(the stack checks fall through, 104 bytes of stack writable, the cgo globals as statically
initialised, the stack-protector guard at `FS:0x28` readable away from the stack) returns,
restores `RSP`, `RBP`, `R14`, and returns `x + y`, `x - y`, `x * y`, `x ^ y` (mod 2^64) in `RAX`,
`RBX`, `RCX`, `RDI`, under the trusted `CgoCall` contract only.

**How.** The C wrapper reserves the 32-byte result in its own frame and passes its address as
the hidden first argument in `RDI` — the System V classification of the 32-byte struct is
MEMORY (`SysV.result … = .indirect (.gpr 7)`) — and then copies it into the cgo frame with two
16-byte `movdqa`/`movups` pairs. The wrapper is compiled with gcc's stack protector: its canary
check reads the guard at `FS:0x28` twice and passes, since neither the guard nor the canary slot
changes. `wrapper_spec` uses the callee contract `summary` of `k_big`, whose precondition is the
classified call including the result buffer (`RetBuf`), proved at the call site.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Spec
  Janus.Amd64.FFI Janus.C

namespace Proof

/-! ## The C function `k_big` (as in `KBig.lean`), as a callee summary -/

abbrev kb : Nat := segAddr Extracted.program "k_big"

def big : CType := .struct [.int 8 true, .int 8 true, .int 8 true, .int 8 true]
def sig : SysV.Sig := ⟨some big, [.int 8 true, .int 8 true], none⟩

theorem passing : sig.passing = [.direct [⟨0, 8, .gpr 6⟩], .direct [⟨0, 8, .gpr 2⟩]] := by decide
theorem result : SysV.result big = .indirect (.gpr 7) := by decide
theorem size_big : CType.size big = 32 := by decide

def quad (a b c d : BitVec 64) : Nat :=
  a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + 2 ^ 192 * d.toNat

/-- The memory after `k_big` wrote the struct at `a` (its four stores, in gcc's order). -/
def bigMem (m : Memory) (a : Nat) (x y : BitVec 64) : Memory :=
  (((m.writeLE a 8 (x.toNat + y.toNat)).writeLE (a + 8) 8 (18446744073709551616 - y.toNat + x.toNat)).writeLE
    (a + 24) 8 (x ^^^ y).toNat).writeLE (a + 16) 8 (x * y).toNat

theorem bigMem_read (m : Memory) (a : Nat) (x y : BitVec 64) :
    (bigMem m a x y).readLE a 32 = quad (x + y) (x - y) (x * y) (x ^^^ y) := by
  simp only [bigMem, readLE_32]
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  simp only [quad, BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow]
  have := (x ^^^ y).isLt
  have := (x * y).isLt
  omega

def vals (x y : BitVec 64) : List Nat := [x.toNat, y.toNat]

def SPre (vs : List Nat) (s : State) : Prop :=
  ArgsAt s sig.args vs sig.passing ∧ RetBuf s sig ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.df = false

theorem spre_iff (x y : BitVec 64) (s : State) :
    SPre (vals x y) s ↔ s.regs 6 = x ∧ s.regs 2 = y ∧ (s.regs 7).toNat + 32 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 7).toNat 32 true = true ∧
      ((s.regs 7).toNat + 32 ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 8 ≤ (s.regs 7).toNat) ∧
      (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
      s.df = false := by
  unfold SPre
  have hrb : RetBuf s sig ↔ (s.regs 7).toNat + 32 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 7).toNat 32 true = true ∧
      ((s.regs 7).toNat + 32 ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 8 ≤ (s.regs 7).toNat) := by
    constructor
    · intro h; have := h big rfl result; rwa [size_big] at this
    · intro h t ht _; cases ht; rw [size_big]; exact h
  rw [passing, hrb]
  simp only [vals, sig, ArgsAt, ArgAt, PiecesAt, and_true, pieceAt_gpr_word, and_assoc]

abbrev SPost (x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 3 = s.regs 3 ∧ s'.regs 5 = s.regs 5 ∧
    s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    s'.regs 15 = s.regs 15 ∧ s'.df = false ∧ s'.mxcsr = s.mxcsr ∧ s'.fpucw = s.fpucw ∧
    s'.mem = bigMem s.mem (s.regs 7).toNat x y ∧ s'.regs 0 = s.regs 7 ∧ s'.fsBase = s.fsBase

theorem summary (x y : BitVec 64) :
    Summary Extracted.program kb (SPre (vals x y)) (SPost x y) := by
  intro s hpc hpre
  obtain ⟨h6, h2, hb, hacc, hdisj, hsb, hsa, hra, hdf⟩ := (spre_iff x y s).1 hpre
  janus64_run
  simp only [SPost, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, true_and]
  exact ⟨rfl, rfl, trivial⟩


/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_a66fe0e77ed3_Cfunc_k_big"

/-- The cgo frame at `a`: `p0` at `a`, `p1` at `a + 8`, the 32-byte result at `a + 16`. -/
def fw (m : Memory) (a k : Nat) : BitVec 64 := BitVec.ofNat 64 (m.readLE (a + 8 * k) 8)

/-- The result struct's bytes, in two 16-byte halves (`{x + y, x - y}`, `{x * y, x ^ y}`). -/
def lo (m : Memory) (a : Nat) : Nat := pair (fw m a 0 + fw m a 1) (fw m a 0 - fw m a 1)
def hi (m : Memory) (a : Nat) : Nat := pair (fw m a 0 * fw m a 1) (fw m a 0 ^^^ fw m a 1)

/-- The wrapper's precondition: the cgo frame, and the stack-protector guard at `FS:0x28`
readable, off the C stack and the frame. -/
def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 8 ∧ a.toNat + 48 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 48 true = true ∧
    (a.toNat + 48 ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ a.toNat) ∧
    t.fsBase.toNat + 48 ≤ 2 ^ 48 ∧ t.mem.accessible (t.fsBase.toNat + 40) 8 false = true ∧
    (t.fsBase.toNat + 48 ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ t.fsBase.toNat + 40) ∧
    (t.fsBase.toNat + 48 ≤ a.toNat ∨ a.toNat + 48 ≤ t.fsBase.toNat + 40)

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame ((t.mem.writeLE (a.toNat + 16) 16 (lo t.mem a.toNat)).writeLE (a.toNat + 32) 16
    (hi t.mem a.toNat)) t'.mem [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]

set_option maxHeartbeats 4000000 in
theorem wrapper_spec (T a : BitVec 64)
    (hex : s'.excl = s.excl := by first | rfl | simp_all) (hep : s'.exclPass = s.exclPass := by first | rfl | simp_all) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd, hgb, hga, hgo, hgf⟩
  apply ReturnsC.of_reaches
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : t.regs 7 = a := hs.reg (i := 0) (by simp)
  simp only [Amd64.Program.withExit] at h_ret
  simp only [CABI.regSP] at hal hb htop hacc hd hgo
  have h72 : (t.regs 4 - 72#64).toNat = (t.regs 4).toNat - 72 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h80 : (t.regs 4 - 80#64).toNat = (t.regs 4).toNat - 80 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hfs : (t.fsBase + 40#64).toNat = t.fsBase.toNat + 40 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run [hfs]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h80]; omega
  · janus64_simp [h80]; janus64_disch
  rintro s₁ ⟨-, f₁, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run [spre_iff, fw, BitVec.toNat_ofNat, hfs, h72, bigMem] until [wrapper + 0x32]
    calls [summary (fw t.mem a.toNat 0) (fw t.mem a.toNat 1)]
  dsimp only at *
  obtain ⟨regs', rip', fl', xm', mem', yh', fsb', df', mx', x87', fcw', ex, ep⟩ := s'
  dsimp only at *
  subst mem' fsb' rip' hex hep
  simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, bigMem] at *
  have h4' : regs' 4 = t.regs 4 - 80#64 + 8 := by assumption
  have h3' : regs' 3 = a := by assumption
  have h5' : regs' 5 = T := by assumption
  have h0' : regs' 0 = t.regs 4 - 72#64 := by assumption
  have h12' : regs' 12 = t.regs 12 := by assumption
  have h13' : regs' 13 = t.regs 13 := by assumption
  have h14' : regs' 14 = t.regs 14 := by assumption
  have h15' : regs' 15 = t.regs 15 := by assumption
  have hdf' : df' = false := by assumption
  have hmx' : mx' = t.mxcsr := by assumption
  have hfw' : fcw' = t.fpucw := by assumption
  subst hdf' hmx' hfw'
  have h4'' : regs' 4 = t.regs 4 - 72#64 := by
    rw [h4']; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.reduceToNat,
      Nat.reducePow, Nat.mod_add_mod]
    omega
  have hT : (18446744073709551616 - T.toNat + T.toNat) % 18446744073709551616 = 0 := by
    have := T.isLt; omega
  have h3n : (regs' 3).toNat = a.toNat := by rw [h3']
  have h5n : (regs' 5).toNat = T.toNat := by rw [h5']
  janus64_run [h4'', h3', h5', h0', h72, h80, hfs, hT]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h80]; omega
  · janus64_simp [h80]; janus64_disch
  rintro s₂ ⟨-, f₂, rfl⟩
  apply ReturnsC.of_reaches
  have hal72 : ((t.regs 4).toNat - 72) % 16 = 0 := by omega
  have hal56 : ((t.regs 4).toNat - 56) % 16 = 0 := by omega
  janus64_run [readLE_16, hal72, hal56, hfs, h72]
  refine ⟨⟨by assumption, by assumption, by assumption, by assumption⟩, ?_⟩
  have elo : ((fw t.mem a.toNat 0).toNat + (fw t.mem a.toNat 1).toNat) % 18446744073709551616 +
      18446744073709551616 *
        ((18446744073709551616 - (fw t.mem a.toNat 1).toNat + (fw t.mem a.toNat 0).toNat) %
          18446744073709551616) = lo t.mem a.toNat := by
    simp only [lo, pair, BitVec.toNat_add, BitVec.toNat_sub, Nat.reducePow]
  have ehi : (fw t.mem a.toNat 0 * fw t.mem a.toNat 1).toNat +
      18446744073709551616 * (fw t.mem a.toNat 0 ^^^ fw t.mem a.toNat 1).toNat = hi t.mem a.toNat := by
    simp only [hi, pair, Nat.reducePow]
  simp only [WPost, h3n, h5n, hT, Nat.add_zero, elo, ehi]
  apply Janus.MemFrame.writeLE_both
  apply Janus.MemFrame.writeLE_both
  janus_frame

/-! ## The Go side: `Big` → `_Cfunc_k_big` → `runtime.cgocall` -/

def fnVar : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_big.abi0" + 0x39)

def alwaysFalse : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_big.abi0" + 0x52)

/-- At the `cgocall`: the 48-byte frame and the guard at `FS:0x28` are Go memory the runtime
leaves alone, and the guard is not in the frame. -/
def G (s : State) : Prop :=
  (s.regs 3).toNat + 48 ≤ 2 ^ 48 ∧ GoKept s (s.regs 3).toNat 48 true ∧
    s.fsBase.toNat + 48 ≤ 2 ^ 48 ∧ GoKept s (s.fsBase.toNat + 40) 8 false ∧
    (s.fsBase.toNat + 48 ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 48 ≤ s.fsBase.toNat + 40)

def E (s : State) : Memory :=
  (s.mem.writeLE ((s.regs 3).toNat + 16) 16 (lo s.mem (s.regs 3).toNat)).writeLE
    ((s.regs 3).toNat + 32) 16 (hi s.mem (s.regs 3).toNat)

def GoPre (s : State) : Prop :=
  StackGuardOK s 64 ∧ StackWritable s 104 8 ∧ TlsG s ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 = 0 ∧
  s.fsBase.toNat + 48 ≤ 2 ^ 48 ∧ s.mem.accessible (s.fsBase.toNat + 40) 8 false = true ∧
  Outside (s.regs 14).toNat 456 [((s.regs 4).toNat - 104, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat - 8) 8 [((s.regs 4).toNat - 104, (s.regs 4).toNat + 8)] ∧
  Outside fnVar 8 [((s.regs 4).toNat - 104, (s.regs 4).toNat + 8)] ∧
  Outside alwaysFalse 1 [((s.regs 4).toNat - 1128, (s.regs 4).toNat + 8),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)] ∧
  Outside (s.fsBase.toNat + 40) 8 [((s.regs 4).toNat - 1128, (s.regs 4).toNat + 8),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)]

set_option maxHeartbeats 4000000 in
theorem go_spec (x y : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [x, y] GoPre
      (fun _ s' => s'.regs 0 = x + y ∧ s'.regs 3 = x - y ∧ s'.regs 1 = x * y ∧ s'.regs 7 = x ^^^ y) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, htop, hst⟩, ⟨hfs, hfsr, hfsg⟩, hfa, hfv, haa, hav,
    hcb, hca, hdg, hdt, hdf, hda, hdc⟩
  apply ReturnsC.of_reaches
  janus64_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  simp only [outside_cons, outside_nil, and_true, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    stackguard0, stackguard0Offset] at *
  have hfsa : (s.fsBase + BitVec.ofNat 64 18446744073709551608).toNat = s.fsBase.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h56 : (s.regs 4 - 56#64).toNat = (s.regs 4).toNat - 56 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h104 : (s.regs 4 - 104#64).toNat = (s.regs 4).toNat - 104 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run [hfsa]
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · simp only [G, GoKept, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
      cgoStackScratch, gStructSize, outside_cons, outside_nil, and_true]
    janus64_simp [h56, h104]
    repeat' (apply And.intro)
    all_goals first | omega | janus64_disch | assumption
  rintro s' ⟨-, m, ⟨regs, fl, xm, yh, _, mx, x87, zh, kr, rfl, h4, h5, h14, h15, ⟨⟨hfs1, hfs2⟩, hfsr', hfsg'⟩, -⟩, hmf⟩
  rename_i fsb
  simp only [E, lo, hi, fw, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    Janus.Amd64.GoABI.regFP, Janus.Amd64.GoABI.xmmZero, cgoStackScratch, gStructSize, setRegF,
    ↓reduceIte, Nat.reduceEqDiff, h56, h104] at hmf h4 h5 h14 h15 hfs1 hfs2 hfsr' hfsg'
  have hfsa' : (fsb + BitVec.ofNat 64 18446744073709551608).toNat = fsb.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hmf.accessible] at hfsr'
  simp only [Janus.Arm64.Memory.accessible_writeLE] at hfsr'
  have hr : m.readLE (s.regs 4).toNat 8 = ret := by
    rw [hmf.readLE (s.regs 4).toNat 8 (by simp only [outside_cons, outside_nil, and_true]; omega)]
    janus64_simp [h_ret]
  apply ReturnsC.of_reaches
  janus64_run [h4, h5, h14, h15, hfsa', hfsg', hr, readLE_writeLE_pair_lo, readLE_writeLE_pair_hi]
  refine ⟨rfl, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub, Nat.mod_mod]

/-! ## Composition -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, ⟨hacc, hout⟩, hgb, ⟨hga, hgout⟩, hgf⟩ he
    have hsep := he.stackSep _ _ _ hacc
    have hgsep := he.stackSep _ _ _ hga
    simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep hgsep
    unfold WPre; rw [he.fs]
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by omega, hgb,
      he.keptAcc _ _ _ ⟨hga, hgout⟩, by omega, hgf⟩
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, ⟨hacc, hout⟩, _⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by
      simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep ⊢; omega)
    simp only [Janus.Arm64.Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE,
      Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 3).toNat ≤ c → c + n ≤ (s.regs 3).toNat + 48 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    have hr : lo t.mem (s.regs 3).toNat = lo s.mem (s.regs 3).toNat ∧
        hi t.mem (s.regs 3).toNat = hi s.mem (s.regs 3).toNat := by
      simp only [lo, hi, fw, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
      rw [hk (s.regs 3).toNat 8 (Nat.le_refl _) (by omega),
        hk ((s.regs 3).toNat + 8) 8 (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    rw [hr.1, hr.2]
    split
    · rfl
    · split
      · rfl
      · have := he.kept b 1 ⟨hbacc, hb'⟩
        simp only [Janus.Arm64.Memory.readLE_one] at this
        exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, _⟩ b _ hna
    have hb1 : ¬ ((s.regs 3).toNat ≤ b ∧ b < (s.regs 3).toNat + 48) := by
      intro ⟨h1, h2⟩
      have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
      rw [this] at hna; cases hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE, if_neg (by omega),
      if_neg (by omega)]

/-- **`Big` end to end**, under the trusted `CgoCall` contract only. -/
theorem correctness (x y : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [x, y] GoPre
      (fun _ s' => s'.regs 0 = x + y ∧ s'.regs 3 = x - y ∧ s'.regs 1 = x * y ∧ s'.regs 7 = x ^^^ y) :=
  (go_spec x y).refine refines

end Proof
