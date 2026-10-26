import Extracted

/-!
# `Big(x, y int64) (int64, int64, int64, int64)` (Go) → `k_big` (C, a 32-byte struct returned
# through `X8`) → back to Go, end to end (arm64)

```go
func Big(x, y int64) (int64, int64, int64, int64) {
	r := C.k_big(C.int64_t(x), C.int64_t(y))
	return int64(r.a), int64(r.b), int64(r.c), int64(r.d)
}
```

**Guarantee (`correctness`).** For all 64-bit `x`, `y`, every Go call of
`example.com/cgo/cabi.Big` satisfying `GoPre` (the stack checks fall through, 128 bytes of stack
writable, the cgo globals as statically initialised, the GOT slot of `__stack_chk_guard` and the
guard readable Go memory away from the stack) returns, restores `SP`, `g` and the frame pointer,
and returns `x + y`, `x - y`, `x * y`, `x ^ y` (mod 2^64) in `X0`–`X3`, under the trusted
`CgoCall` contract only.

**How.** The C wrapper reserves the 32-byte result in its own frame, passes its address in `X8`
— the indirect result location the classification of the 32-byte non-HFA result asks for
(`AAPCS64.result … = .indirect (.gpr 8)`) — and copies it into the cgo frame after the call. The
wrapper is compiled with gcc's stack protector: its canary check reads the guard through the GOT
and passes, since neither the guard nor the canary slot changes. `wrapper_spec` uses the callee
contract `summary` of `k_big`, whose precondition is the classified call including the result
buffer (`RetBuf`), proved at the call site.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.Spec Janus.FFI Janus.C

namespace Proof

/-! ## The C function `k_big` (as in `KBig.lean`), as a callee summary -/

abbrev kb : Nat := segAddr Extracted.program "k_big"

def big : CType := .struct [.int 8 true, .int 8 true, .int 8 true, .int 8 true]
def sig : AAPCS64.Sig := ⟨some big, [.int 8 true, .int 8 true], none⟩

theorem passing : sig.passing = [.direct [⟨0, 8, .gpr 0⟩], .direct [⟨0, 8, .gpr 1⟩]] := by decide
theorem result : AAPCS64.result big = .indirect (.gpr 8) := by decide
theorem size_big : CType.size big = 32 := by decide

/-- The bytes of a `struct k_big`. -/
def quad (a b c d : BitVec 64) : Nat :=
  a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + 2 ^ 192 * d.toNat

/-- The memory after `k_big` wrote the struct at `a` (the four stores of its two `STP`s). -/
def bigMem (m : Memory) (a : Nat) (x y : BitVec 64) : Memory :=
  (((m.writeLE a 8 (x.toNat + y.toNat)).writeLE (a + 8) 8 (18446744073709551616 - y.toNat + x.toNat)).writeLE
    (a + 16) 8 (x.toNat * y.toNat)).writeLE (a + 24) 8 (x.toNat ^^^ y.toNat)

/-- The 32 bytes of the result in `bigMem`. -/
theorem bigMem_read (m : Memory) (a : Nat) (x y : BitVec 64) :
    (bigMem m a x y).readLE a 32 = quad (x + y) (x - y) (x * y) (x ^^^ y) := by
  simp only [bigMem, readLE_32]
  simp (disch := omega) only [Memory.readLE_writeLE_self, Memory.readLE_writeLE_of_disjoint]
  simp only [quad, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_xor,
    Nat.reducePow]
  have := (x ^^^ y).isLt
  rw [BitVec.toNat_xor] at this
  omega

/-- The argument values of `k_big(x, y)`. -/
def vals (x y : BitVec 64) : List Nat := [x.toNat, y.toNat]

/-- What `k_big` needs: its arguments where the classification puts them, the result buffer
(`X8`) and a return address. -/
def SPre (vs : List Nat) (s : State) : Prop :=
  ArgsAt s sig.args vs sig.passing ∧ RetBuf s sig ∧ (s.regs 30).toNat % 4 = 0 ∧
    (s.regs 30).toNat < 2 ^ 56

theorem spre_iff (x y : BitVec 64) (s : State) :
    SPre (vals x y) s ↔ s.regs 0 = x ∧ s.regs 1 = y ∧ (s.regs 8).toNat + 32 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 8).toNat 32 true = true ∧ (s.regs 30).toNat % 4 = 0 ∧
      (s.regs 30).toNat < 2 ^ 56 := by
  unfold SPre
  have hrb : RetBuf s sig ↔ (s.regs 8).toNat + 32 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 8).toNat 32 true = true := by
    constructor
    · intro h; have := h big rfl result; rwa [size_big] at this
    · intro h t ht _; cases ht; rw [size_big]; exact h
  rw [passing, hrb]
  simp only [vals, sig, ArgsAt, ArgAt, PiecesAt, and_true, pieceAt_gpr_word, and_assoc]

/-- What it guarantees: the callee-saved state, the struct written at `X8` and nothing else. -/
abbrev SPost (x y : BitVec 64) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 19 = s.regs 19 ∧ s'.regs 20 = s.regs 20 ∧ s'.regs 21 = s.regs 21 ∧
    s'.regs 22 = s.regs 22 ∧ s'.regs 23 = s.regs 23 ∧ s'.regs 24 = s.regs 24 ∧
    s'.regs 25 = s.regs 25 ∧ s'.regs 26 = s.regs 26 ∧ s'.regs 27 = s.regs 27 ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.fpcr = s.fpcr ∧ s'.vregs = s.vregs ∧
    s'.mem = bigMem s.mem (s.regs 8).toNat x y

theorem summary (x y : BitVec 64) :
    Summary Extracted.program kb (SPre (vals x y)) (SPost x y) := by
  intro s hpc hpre
  obtain ⟨h0, h1, hb, hacc, hlra, hlrb⟩ := (spre_iff x y s).1 hpre
  janus_run
  simp only [SPost, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, true_and]
  rfl


/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_a66fe0e77ed3_Cfunc_k_big"

/-- The GOT slot of `__stack_chk_guard` the wrapper reads (`adrp`+`ldr` at `wrapper+0x18`). -/
def got : Nat :=
  adrpLdTarget (wrapper + 0x18) (segWord Extracted.program "_cgo_a66fe0e77ed3_Cfunc_k_big" 6)
    (segWord Extracted.program "_cgo_a66fe0e77ed3_Cfunc_k_big" 7) 3

/-- The cgo frame at `a`: `p0` at `a`, `p1` at `a + 8`, the 32-byte result at `a + 16`. -/
def fw (m : Memory) (a k : Nat) : BitVec 64 := BitVec.ofNat 64 (m.readLE (a + 8 * k) 8)

/-- The result struct's bytes, in two 16-byte halves (`{x + y, x - y}`, `{x * y, x ^ y}`). -/
def lo (m : Memory) (a : Nat) : Nat := pair (fw m a 0 + fw m a 1) (fw m a 0 - fw m a 1)
def hi (m : Memory) (a : Nat) : Nat := pair (fw m a 0 * fw m a 1) (fw m a 0 ^^^ fw m a 1)

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 0 ∧ a.toNat + 48 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 48 true = true ∧
    (a.toNat + 48 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ a.toNat) ∧
    got + 8 ≤ 2 ^ 48 ∧ t.mem.accessible got 8 false = true ∧
    (got + 8 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ got) ∧
    t.mem.readLE got 8 + 8 ≤ 2 ^ 48 ∧ t.mem.accessible (t.mem.readLE got 8) 8 false = true ∧
    (t.mem.readLE got 8 + 8 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ t.mem.readLE got 8) ∧
    (t.mem.readLE got 8 + 8 ≤ a.toNat ∨ a.toNat + 48 ≤ t.mem.readLE got 8)

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame ((t.mem.writeLE (a.toNat + 16) 16 (lo t.mem a.toNat)).writeLE (a.toNat + 32) 16
    (hi t.mem a.toNat)) t'.mem [(t.sp.toNat - 4096, t.sp.toNat)]

set_option maxHeartbeats 4000000 in
theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd, hgb, hga, hgo, hGb, hGa, hGo, hGf⟩
  apply ReturnsC.of_reaches
  janus_intro hs.call
  simp only [Nat.add_zero] at htop hacc
  janus_eval_nat h_got : got
  rw [h_got] at hgb hga hgo hGb hGa hGo hGf
  have hT : (18446744073709551616 - T.toNat + T.toNat) % 18446744073709551616 = 0 := by
    have := T.isLt; omega
  janus_run
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₁ ⟨-, f₁, m₁, rfl, hm₁⟩
  have h96 : (t.sp - 96#64).toNat = t.sp.toNat - 96 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  apply ReturnsC.of_reaches
  janus_run [spre_iff, fw, BitVec.toNat_ofNat] until [wrapper + 0x44]
    calls [summary (fw t.mem a.toNat 0) (fw t.mem a.toNat 1)]
  dsimp only at *
  obtain ⟨regs', sp', pc', fl', mem', dz', vr', tp', fc', fsr'⟩ := s'
  dsimp only at *
  subst sp' pc' mem' fc' vr'
  simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, bigMem] at *
  have h19' : regs' 19 = a := by assumption
  have h20' : regs' 20 = t.sp - 88#64 := by assumption
  have h21' : regs' 21 = T := by assumption
  have h29' : regs' 29 = t.sp - 48#64 := by assumption
  have h88 : (t.sp - 88#64).toNat = t.sp.toNat - 88 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run [h19', h20', h21', h29', h96, h88]
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp [h96]
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₂ ⟨-, f₂, m₂, rfl, hm₂⟩
  dsimp only at hm₁ hm₂
  apply ReturnsC.of_reaches
  janus_run [h19', h20', h21', h29', h96, h88, hT]
  refine ⟨?_, ?_⟩
  · repeat' (apply And.intro)
    all_goals assumption
  have hlo : (((m₁.writeLE (t.sp.toNat - 88) 8 ((fw t.mem a.toNat 0).toNat + (fw t.mem a.toNat 1).toNat)).writeLE
      (t.sp.toNat - 88 + 8) 8
      (18446744073709551616 - (fw t.mem a.toNat 1).toNat + (fw t.mem a.toNat 0).toNat)).readLE
      (t.sp.toNat - 88) 16) = lo t.mem a.toNat := by
    rw [readLE_16]
    simp (disch := omega) only [Memory.readLE_writeLE_self, Memory.readLE_writeLE_of_disjoint]
    simp only [lo, pair, BitVec.toNat_add, BitVec.toNat_sub]
    try omega
  have hhi : ((((m₁.writeLE (t.sp.toNat - 88) 8 ((fw t.mem a.toNat 0).toNat + (fw t.mem a.toNat 1).toNat)).writeLE
      (t.sp.toNat - 88 + 8) 8
      (18446744073709551616 - (fw t.mem a.toNat 1).toNat + (fw t.mem a.toNat 0).toNat)).writeLE
      (t.sp.toNat - 88 + 16) 8 ((fw t.mem a.toNat 0).toNat * (fw t.mem a.toNat 1).toNat)).writeLE
      (t.sp.toNat - 88 + 24) 8 ((fw t.mem a.toNat 0).toNat ^^^ (fw t.mem a.toNat 1).toNat)).readLE
      (t.sp.toNat - 72) 16 = hi t.mem a.toNat := by
    rw [readLE_16]
    simp (disch := omega) only [Memory.readLE_writeLE_self, Memory.readLE_writeLE_of_disjoint,
      show t.sp.toNat - 72 = t.sp.toNat - 88 + 16 by omega,
      show t.sp.toNat - 88 + 16 + 8 = t.sp.toNat - 88 + 24 by omega]
    simp only [hi, pair, BitVec.toNat_mul, BitVec.toNat_xor]
    have := (fw t.mem a.toNat 0 ^^^ fw t.mem a.toNat 1).isLt
    rw [BitVec.toNat_xor] at this
    omega
  simp only [WPost, hlo, hhi]
  have hf : MemFrame t.mem m₂ [(t.sp.toNat - 4096, t.sp.toNat)] := by
    refine MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)])
      (MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)])
        (rs' := [(t.sp.toNat - 4096, t.sp.toNat)])
        (MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)]) ?_ hm₁ ?_) ?_ ?_) hm₂ ?_
    all_goals first
      | janus_frame
      | (intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  exact (hf.writeLE_both _ _ _).writeLE_both _ _ _

/-! ## The Go side: `Big` → `_Cfunc_k_big` → `runtime.cgocall` -/

def fnVar : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_big.abi0" + 0x28)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_big.abi0" 10)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_big.abi0" 11) 3

def alwaysFalse : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_big.abi0" + 0x34)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_big.abi0" 13)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_big.abi0" 14) 0

/-- At the `cgocall`: the 48-byte frame, the GOT slot and the guard are Go memory the runtime
leaves alone, and the guard is not in the frame. -/
def G (s : State) : Prop :=
  (s.regs 1).toNat + 48 ≤ 2 ^ 48 ∧ GoKept s (s.regs 1).toNat 48 true ∧
    got + 8 ≤ 2 ^ 48 ∧ GoKept s got 8 false ∧
    s.mem.readLE got 8 + 8 ≤ 2 ^ 48 ∧ GoKept s (s.mem.readLE got 8) 8 false ∧
    (s.mem.readLE got 8 + 8 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat + 48 ≤ s.mem.readLE got 8)

def E (s : State) : Memory :=
  (s.mem.writeLE ((s.regs 1).toNat + 16) 16 (lo s.mem (s.regs 1).toNat)).writeLE
    ((s.regs 1).toNat + 32) 16 (hi s.mem (s.regs 1).toNat)

def GoPre (s : State) : Prop :=
  GuardOK s 64 ∧ StackOK s 128 0 ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 % 2 = 0 ∧
  got + 8 ≤ 2 ^ 48 ∧ s.mem.accessible got 8 false = true ∧
  s.mem.readLE got 8 + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.mem.readLE got 8) 8 false = true ∧
  Outside (s.regs 28).toNat 456 [(s.sp.toNat - 128, s.sp.toNat)] ∧
  Outside (s.tpidr.toNat + 16) 8 [(s.sp.toNat - 128, s.sp.toNat)] ∧
  Outside fnVar 8 [(s.sp.toNat - 128, s.sp.toNat)] ∧
  Outside alwaysFalse 1 [(s.sp.toNat - 1136, s.sp.toNat), ((s.regs 28).toNat, (s.regs 28).toNat + 456),
    (s.tpidr.toNat + 16, s.tpidr.toNat + 24)] ∧
  Outside got 8 [(s.sp.toNat - 1136, s.sp.toNat), ((s.regs 28).toNat, (s.regs 28).toNat + 456),
    (s.tpidr.toNat + 16, s.tpidr.toNat + 24)] ∧
  Outside (s.mem.readLE got 8) 8 [(s.sp.toNat - 1136, s.sp.toNat),
    ((s.regs 28).toNat, (s.regs 28).toNat + 456), (s.tpidr.toNat + 16, s.tpidr.toNat + 24)]

set_option maxHeartbeats 4000000 in
theorem go_spec (x y : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [x, y] GoPre
      (fun _ s' => s'.regs 0 = x + y ∧ s'.regs 1 = x - y ∧ s'.regs 2 = x * y ∧ s'.regs 3 = x ^^^ y) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, htop, hst⟩, hfa, hfv, haa, hav, hgb, hga, hGb, hGa,
    hdg, hdt, hdf, hda, hdgot, hdG⟩
  apply ReturnsC.of_reaches
  janus_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  janus_eval_nat h_got : got
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  rw [h_got] at hgb hga hGb hGa hdgot hdG
  simp only [outside_cons, outside_nil, and_true, Nat.add_zero] at *
  have h56 : (s.sp - 56#64).toNat = s.sp.toNat - 56 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h112 : (s.sp - 112#64).toNat = s.sp.toNat - 112 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus_simp [hfv]
  · simp only [G, GoKept, cgoClobber, GoABI.regG, cgoStackScratch, gStructSize, tlsGOffset,
      outside_cons, outside_nil, and_true, h_got]
    janus_simp [h56, h112]
    repeat' (apply And.intro)
    all_goals first | omega | janus_disch | assumption
  rintro s' ⟨-, m, ⟨regs, fl, vr, tp, fs', ex, rfl, hg, hfp⟩, hmf⟩
  simp only [E, lo, hi, fw, cgoClobber, GoABI.regG, GoABI.regFP, cgoStackScratch, gStructSize,
    tlsGOffset, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h56, h112] at hmf hg hfp
  apply ReturnsC.of_reaches
  janus_run [hg, hfp, readLE_writeLE_pair_lo, readLE_writeLE_pair_hi]
  have hx := (x ^^^ y).isLt
  rw [BitVec.toNat_xor] at hx
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_xor,
      Nat.mod_mod]
  exact Nat.mod_eq_of_lt hx

/-! ## Composition -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, ⟨hacc, hout⟩, hgb, ⟨hga, hgout⟩, hGb, ⟨hGa, hGout⟩, hGf⟩ he
    have hsep := he.stackSep _ _ _ hacc
    have hgsep := he.stackSep _ _ _ hga
    have hGsep := he.stackSep _ _ _ hGa
    have hk := he.kept got 8 ⟨hga, hgout⟩
    simp only [outside_cons, outside_nil, and_true, cgoCStack] at hsep hgsep hGsep
    refine ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by omega, hgb, he.keptAcc _ _ _ ⟨hga, hgout⟩,
      by omega, ?_, ?_, ?_, ?_⟩ <;> rw [hk]
    · exact hGb
    · exact he.keptAcc _ _ _ ⟨hGa, hGout⟩
    · omega
    · omega
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, ⟨hacc, hout⟩, _⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by simpa [cgoCStack] using hsep)
    simp only [Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Memory.bytes_writeLE, Memory.bytes_writeLE,
      Memory.bytes_writeLE, Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 1).toNat ≤ c → c + n ≤ (s.regs 1).toNat + 48 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    have hr : lo t.mem (s.regs 1).toNat = lo s.mem (s.regs 1).toNat ∧
        hi t.mem (s.regs 1).toNat = hi s.mem (s.regs 1).toNat := by
      simp only [lo, hi, fw, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
      rw [hk (s.regs 1).toNat 8 (Nat.le_refl _) (by omega),
        hk ((s.regs 1).toNat + 8) 8 (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    rw [hr.1, hr.2]
    split
    · rfl
    · split
      · rfl
      · have := he.kept b 1 ⟨hbacc, hb'⟩
        simp only [Memory.readLE_one] at this
        exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, _⟩ b _ hna
    have hb1 : ¬ ((s.regs 1).toNat ≤ b ∧ b < (s.regs 1).toNat + 48) := by
      intro ⟨h1, h2⟩
      have := Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
      rw [this] at hna; cases hna
    rw [E, Memory.bytes_writeLE, Memory.bytes_writeLE, if_neg (by omega), if_neg (by omega)]

/-- **`Big` end to end**, under the trusted `CgoCall` contract only. -/
theorem correctness (x y : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [x, y] GoPre
      (fun _ s' => s'.regs 0 = x + y ∧ s'.regs 1 = x - y ∧ s'.regs 2 = x * y ∧ s'.regs 3 = x ^^^ y) :=
  (go_spec x y).refine refines

end Proof
