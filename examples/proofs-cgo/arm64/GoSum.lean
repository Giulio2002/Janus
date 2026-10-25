import Extracted

/-!
# `Sum(xs []uint64) uint64` (Go) → `c_sum` (a C loop) → back to Go, end to end (arm64)

```go
func Sum(xs []uint64) uint64 {
	if len(xs) == 0 {
		return 0
	}
	return uint64(C.c_sum((*C.uint64_t)(unsafe.Pointer(&xs[0])), C.uint64_t(len(xs))))
}
```

**Guarantee (`correctness`).** For every slice header `(ptr, len, cap)` and every Go call of
`example.com/cgo.Sum` satisfying `GoPre ptr len` — the stack checks fall through, the stack window
(and the spill slot above `SP`) is writable, the `8·len` bytes at `ptr` are readable, below `2^48`
and away from the stack window, the `g` struct and the TLS `g` slot; and the cgo globals hold their
static values — every run returns, restores `SP`, `g` and the frame pointer, and leaves
`(xs[0] + … + xs[len-1]) mod 2^64` in `X0`, for every length (the C loop terminates).

The statement is under the trusted `CgoCall Extracted.program` only: `Sum`, `_Cfunc_c_sum`, the C
wrapper and the C loop `c_sum` are executed by the model (the loop by induction, `csum_loop`).

**How.** `csum_summary` is the callee contract of `c_sum` (as in `CSum.lean`); `wrapper_spec`
uses it at the wrapper's `bl c_sum`; `go_spec` is `Sum` under `CgoSpec wrapper G E` (the frame and
the slice are Go memory the runtime leaves alone, the result slot gets the sum); `refines` and
`correctness` compose them as for `GoAdd.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.Spec Janus.FFI

namespace Proof

/-! ## The C function `c_sum` (as in `CSum.lean`), as a callee summary -/

abbrev csum : Nat := segAddr Extracted.program "c_sum"

/-- The loop head `ldr x3, [x2], #8`. -/
abbrev head : Nat := csum + 0x18

/-- What `c_sum` guarantees to a caller: `SP`, `X19`–`X29` and memory unchanged, the sum in
`X0` (stated as plain equations, so that a caller's `janus_run` can use them). -/
abbrev SumPost (p n : BitVec 64) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 19 = s.regs 19 ∧ s'.regs 20 = s.regs 20 ∧ s'.regs 21 = s.regs 21 ∧
    s'.regs 22 = s.regs 22 ∧ s'.regs 23 = s.regs 23 ∧ s'.regs 24 = s.regs 24 ∧
    s'.regs 25 = s.regs 25 ∧ s'.regs 26 = s.regs 26 ∧ s'.regs 27 = s.regs 27 ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.fpcr = s.fpcr ∧ s'.vregs = s.vregs ∧
    s'.mem = s.mem ∧
    s'.regs 0 = BitVec.ofNat 64 (sumWords s.mem p.toNat n.toNat)

/-- The precondition of the summary: the buffer, and a return address `RET` can branch to. -/
abbrev SumPre (p n : BitVec 64) (s : State) : Prop :=
  s.regs 0 = p ∧ s.regs 1 = n ∧ p.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧
    s.mem.accessible p.toNat (8 * n.toNat) false = true ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56

/-- `S` agrees with `s` on everything `c_sum` must keep: `SP`, memory, `X19`–`X30`, `FPCR`. -/
abbrev Kept (s S : State) : Prop :=
  S.sp = s.sp ∧ S.mem = s.mem ∧ S.regs 19 = s.regs 19 ∧ S.regs 20 = s.regs 20 ∧
    S.regs 21 = s.regs 21 ∧ S.regs 22 = s.regs 22 ∧ S.regs 23 = s.regs 23 ∧
    S.regs 24 = s.regs 24 ∧ S.regs 25 = s.regs 25 ∧ S.regs 26 = s.regs 26 ∧
    S.regs 27 = s.regs 27 ∧ S.regs 28 = s.regs 28 ∧ S.regs 29 = s.regs 29 ∧
    S.regs 30 = s.regs 30 ∧ S.fpcr = s.fpcr ∧ S.vregs = s.vregs

/-- The loop invariant at `head`, after `i` of the `n` iterations: `X2 = p + 8i`, `X1 = p + 8n`,
`X0` the sum of the first `i` words. -/
theorem csum_loop (p n : BitVec 64) (s : State) (hpre : SumPre p n s) :
    ∀ k (S : State) (i acc : BitVec 64), i.toNat + (k + 1) = n.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = acc →
      S.regs 1 = BitVec.ofNat 64 (p.toNat + 8 * n.toNat) →
      S.regs 2 = BitVec.ofNat 64 (p.toNat + 8 * i.toNat) → Kept s S →
      acc.toNat = sumWords s.mem p.toNat i.toNat % 2 ^ 64 →
      ReachesRet Extracted.program (s.regs 30) S (SumPost p n s) := by
  obtain ⟨h0, h1, hb, hacc, hal, htag⟩ := hpre
  intro k
  induction k with
  | zero =>
    intro S i acc hk hpc hS0 hS1 hS2 ⟨hsp, hm, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hfc, hv⟩ hs
    janus_run
    janus_simp [SumPost, sumWords_succ, show n.toNat = i.toNat + 1 by omega, hfc, hv]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs]
    omega
  | succ k ih =>
    intro S i acc hk hpc hS0 hS1 hS2 ⟨hsp, hm, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hfc, hv⟩ hs
    janus_run until [head]
    have hi : (i + 1#64).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    apply ih _ (i + 1#64) _ (by omega) (by janus_simp) rfl (by janus_simp) ?_
      (by simp only [Kept]; janus_simp [hfc, hv])
      (by janus_simp [sumWords_succ, hi]; omega)
    · janus_simp
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

/-- The callee contract of `c_sum`, used by the cgo wrapper's proof. -/
theorem csum_summary (p n : BitVec 64) :
    Summary Extracted.program csum (SumPre p n) (SumPost p n) := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨h0, h1, hb, hacc, hal, htag⟩ := hpre
  janus_run until [head]
  · janus_simp [SumPost, sumWords_zero]
  · have he : p + n <<< 3 = BitVec.ofNat 64 (p.toNat + 8 * n.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    exact csum_loop p n s hpre' (n.toNat - 1) _ 0#64 0#64 (by simp; omega) (by janus_simp)
      (by janus_simp) (by janus_simp [he]) (by janus_simp) (by simp only [Kept]; janus_simp)
      (by simp)


/-- The sum of `n` words at `p` is the same in two memories that agree outside `rs`. -/
theorem sumWords_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) (p : Nat) :
    ∀ n, Outside p (8 * n) rs → sumWords m' p n = sumWords m p n
  | 0, _ => rfl
  | n + 1, ho => by
    rw [sumWords_succ, sumWords_succ, sumWords_frame h p n (Outside.of_sub ho (Nat.le_refl _) (by omega)),
      h.readLE _ _ (Outside.of_sub ho (by omega) (by omega))]

/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_b947fb19b420_Cfunc_c_sum"

/-- The slice pointer and length in the cgo frame at `a`. -/
abbrev frameP (m : Memory) (a : Nat) : Nat := m.readLE a 8
abbrev frameN (m : Memory) (a : Nat) : Nat := m.readLE (a + 8) 8

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 0 ∧ a.toNat + 24 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 24 true = true ∧
    (a.toNat + 24 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ a.toNat) ∧
    frameP t.mem a.toNat + 8 * frameN t.mem a.toNat ≤ 2 ^ 48 ∧
    t.mem.accessible (frameP t.mem a.toNat) (8 * frameN t.mem a.toNat) false = true ∧
    (frameP t.mem a.toNat + 8 * frameN t.mem a.toNat ≤ t.sp.toNat - 4096 ∨
      t.sp.toNat ≤ frameP t.mem a.toNat)

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 16) 8
      (sumWords t.mem (frameP t.mem a.toNat) (frameN t.mem a.toNat) % 2 ^ 64)) t'.mem
    [(t.sp.toNat - 4096, t.sp.toNat)]

theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd, hpb, hpa, hpd⟩
  apply ReturnsC.of_reaches
  janus_intro hs.call
  simp only [Nat.add_zero, frameP, frameN] at htop hacc hpb hpa hpd
  janus_run
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₁ ⟨-, f₁, m₁, rfl, hm₁⟩
  have h48 : (t.sp - 48#64).toNat = t.sp.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  dsimp only at hm₁
  rw [h48] at hm₁
  apply ReturnsC.of_reaches
  janus_run calls [csum_summary (BitVec.ofNat 64 (t.mem.readLE a.toNat 8))
    (BitVec.ofNat 64 (t.mem.readLE (a.toNat + 8) 8))]
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp [h48]
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₂ ⟨-, f₂, m₂, rfl, hm₂⟩
  dsimp only at hm₂
  rw [h48] at hm₂
  apply ReturnsC.of_reaches
  janus_run
  simp only [WPost, frameP, frameN, Nat.reducePow, writeLE_mod_8]
  have hT : (18446744073709551616 - T.toNat + T.toNat) % 18446744073709551616 = 0 := by
    have := T.isLt; omega
  simp only [hT, Nat.add_zero]
  have hf₁ : MemFrame t.mem m₁ [(t.sp.toNat - 4096, t.sp.toNat)] := by
    refine MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)]) ?_ hm₁ ?_
    · janus_frame
    · intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hf : MemFrame t.mem m₂ [(t.sp.toNat - 4096, t.sp.toNat)] := by
    refine MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)]) hf₁ hm₂ ?_
    intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  rw [sumWords_frame hf₁ _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  refine ⟨?_, hf.writeLE_both _ _ _⟩
  have hv : s'.vregs = t.vregs := by assumption
  simp only [hv, and_self]

/-! ## The Go side: `Sum` → `_Cfunc_c_sum` → `runtime.cgocall` -/

def fnVar : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo._Cfunc_c_sum.abi0" + 0x24)
    (segWord Extracted.program "example.com/cgo._Cfunc_c_sum.abi0" 9)
    (segWord Extracted.program "example.com/cgo._Cfunc_c_sum.abi0" 10) 3

def alwaysFalse : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo._Cfunc_c_sum.abi0" + 0x30)
    (segWord Extracted.program "example.com/cgo._Cfunc_c_sum.abi0" 12)
    (segWord Extracted.program "example.com/cgo._Cfunc_c_sum.abi0" 13) 0

/-- At the `cgocall`: the frame `X1` and the slice it points at are Go memory the runtime leaves
alone. -/
def G (s : State) : Prop :=
  (s.regs 1).toNat + 24 ≤ 2 ^ 48 ∧ GoKept s (s.regs 1).toNat 24 true ∧
    frameP s.mem (s.regs 1).toNat + 8 * frameN s.mem (s.regs 1).toNat ≤ 2 ^ 48 ∧
    GoKept s (frameP s.mem (s.regs 1).toNat) (8 * frameN s.mem (s.regs 1).toNat) false

def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 1).toNat + 16) 8
    (sumWords s.mem (frameP s.mem (s.regs 1).toNat) (frameN s.mem (s.regs 1).toNat) % 2 ^ 64)

def GoPre (ptr len : BitVec 64) (s : State) : Prop :=
  GuardOK s 48 ∧ StackOK s 112 16 ∧
  ptr.toNat + 8 * len.toNat ≤ 2 ^ 48 ∧ s.mem.accessible ptr.toNat (8 * len.toNat) false = true ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 % 2 = 0 ∧
  Outside (s.regs 28).toNat 456 [(s.sp.toNat - 112, s.sp.toNat + 16)] ∧
  Outside (s.tpidr.toNat + 16) 8 [(s.sp.toNat - 112, s.sp.toNat + 16)] ∧
  Outside fnVar 8 [(s.sp.toNat - 112, s.sp.toNat + 16)] ∧
  Outside alwaysFalse 1 [(s.sp.toNat - 1120, s.sp.toNat + 16), ((s.regs 28).toNat, (s.regs 28).toNat + 456),
    (s.tpidr.toNat + 16, s.tpidr.toNat + 24)] ∧
  Outside ptr.toNat (8 * len.toNat) [(s.sp.toNat - 1120, s.sp.toNat + 16),
    ((s.regs 28).toNat, (s.regs 28).toNat + 456), (s.tpidr.toNat + 16, s.tpidr.toNat + 24)]

set_option maxHeartbeats 2000000 in
theorem go_spec (ptr len cap : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [ptr, len, cap] (GoPre ptr len)
      (fun s s' => (s'.regs 0).toNat = sumWords s.mem ptr.toNat len.toNat % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, htop, hst⟩, hpb, hpa, hfa, hfv, haa, hav, hdg, hdt,
    hdf, hda, hdp⟩
  apply ReturnsC.of_reaches
  janus_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  simp only [outside_cons, outside_nil, and_true] at *
  have h40 : (s.sp - 40#64).toNat = s.sp.toNat - 40 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h96 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run
  · simp [sumWords_zero]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus_simp [hfv]
  · simp only [G, GoKept, cgoClobber, frameP, frameN, GoABI.regG, cgoStackScratch, gStructSize,
      tlsGOffset, outside_cons, outside_nil, and_true]
    janus_simp [h40, h96]
    refine ⟨by omega, ⟨?_, by omega, by omega, by omega, by omega⟩, by omega, hpa, by omega, by omega,
      by omega, by omega⟩
    janus_disch
  rintro s' ⟨-, m, ⟨regs, fl, vr, tp, fs, rfl, hg, hfp⟩, hmf⟩
  simp only [E, frameP, frameN, cgoClobber, GoABI.regG, GoABI.regFP, cgoStackScratch, gStructSize,
    tlsGOffset, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h40, h96] at hmf hg hfp
  apply ReturnsC.of_reaches
  janus_run [hg, hfp]
  -- the slice was read through the stack stores of `Sum` and `_Cfunc_c_sum`
  refine congrArg (· % 18446744073709551616) ?_
  apply sumWords_frame (rs := [(s.sp.toNat - 112, s.sp.toNat + 16)])
  · clear hmf; janus_frame
  · simp only [outside_cons, outside_nil, and_true]; omega

/-! ## Composition -/

theorem sumWords_congr {m m' : Memory} (p : Nat) :
    ∀ n, (∀ i, i < n → m'.readLE (p + 8 * i) 8 = m.readLE (p + 8 * i) 8) →
      sumWords m' p n = sumWords m p n
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumWords_succ, sumWords_succ, sumWords_congr p n fun i hi => h i (by omega), h n (by omega)]

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, ⟨hacc, hout⟩, hpb, hpacc, hpout⟩ he
    have hsep := he.stackSep _ _ _ hacc
    have hpsep := he.stackSep _ _ _ hpacc
    have hk0 := he.kept _ 8 ⟨Memory.accessible_sub _ hacc (Or.inl rfl) (Nat.le_refl _) (by omega),
      Outside.of_sub hout (Nat.le_refl _) (by omega)⟩
    have hk1 := he.kept ((s.regs 1).toNat + 8) 8 ⟨Memory.accessible_sub _ hacc (Or.inl rfl) (by omega)
      (by omega), Outside.of_sub hout (by omega) (by omega)⟩
    simp only [outside_cons, outside_nil, and_true, cgoCStack] at hsep hpsep
    simp only [WPre, frameP, frameN] at hpb hpacc hpout hpsep ⊢
    rw [hk0, hk1]
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by omega, hpb,
      he.keptAcc _ _ _ ⟨hpacc, hpout⟩, by omega⟩
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, ⟨hacc, hout⟩, hpb, hpacc, hpout⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by simpa [cgoCStack] using hsep)
    simp only [Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Memory.bytes_writeLE, Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 1).toNat ≤ c → c + n ≤ (s.regs 1).toNat + 24 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · have e0 := hk _ 8 (Nat.le_refl _) (by omega)
      have e1 := hk ((s.regs 1).toNat + 8) 8 (by omega) (by omega)
      simp only [frameP, frameN] at hpb hpacc hpout ⊢
      rw [e0, e1, sumWords_congr _ _ fun i hi =>
        he.kept _ 8 ⟨Memory.accessible_sub _ hpacc (Or.inl rfl) (by omega) (by omega),
          Outside.of_sub hpout (by omega) (by omega)⟩]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, _⟩ b _ hna
    rw [E, Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`Sum` end to end.** -/
theorem correctness (ptr len cap : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [ptr, len, cap]
      (GoPre ptr len) (fun s s' => (s'.regs 0).toNat = sumWords s.mem ptr.toNat len.toNat % 2 ^ 64) :=
  (go_spec ptr len cap).refine refines

end Proof
