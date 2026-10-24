import Extracted

/-!
# `Sum(xs []uint64) uint64` (Go) → `c_sum` (a C loop) → back to Go, end to end (amd64)

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
(and the spill slot above the return address) is writable, the TLS `g` slot holds `g`, the
`8·len` bytes at `ptr` are readable, below `2^48` and away from the stack window, the `g` struct
and the TLS slot; and the cgo globals hold their static values — every run returns, restores
`RSP + 8`, `RBP`, `R14` and `X15`, and leaves `(xs[0] + … + xs[len-1]) mod 2^64` in `RAX`, for
every length (the C loop terminates).

The statement is under the trusted `CgoCall Extracted.program` only: `Sum`, `_Cfunc_c_sum`, the C
wrapper and the C loop `c_sum` are executed by the model (the loop by induction, `csum_loop`).

**How.** `csum_summary` is the callee contract of `c_sum` (as in `CSum.lean`); `wrapper_spec`
uses it at the wrapper's `call c_sum`; `go_spec` is `Sum` under `CgoSpec wrapper G E`; `refines`
and `correctness` compose them as in `GoAdd.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Spec
  Janus.Amd64.FFI

namespace Proof

/-! ## The C function `c_sum` (as in `CSum.lean`), as a callee summary -/

abbrev csum : Nat := segAddr Extracted.program "c_sum"

/-- The loop head `add (%rdi),%rax`. -/
abbrev head : Nat := csum + 0x10

/-- What `c_sum` guarantees to a caller, as plain equations. -/
abbrev SumPost (p n : BitVec 64) (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 3 = s.regs 3 ∧ s'.regs 5 = s.regs 5 ∧
    s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    s'.regs 15 = s.regs 15 ∧ s'.df = false ∧ s'.mem = s.mem ∧
    s'.regs 0 = BitVec.ofNat 64 (sumWords s.mem p.toNat n.toNat)

/-- The precondition of the summary: the arguments, the buffer, and the return address slot. -/
abbrev SumPre (p n : BitVec 64) (s : State) : Prop :=
  s.regs 7 = p ∧ s.regs 6 = n ∧ p.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧
    s.mem.accessible p.toNat (8 * n.toNat) false = true ∧
    (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 4).toNat 8 false = true ∧
    s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.df = false

/-- `S` agrees with `s` on everything `c_sum` must keep. -/
abbrev Kept (s S : State) : Prop :=
  S.regs 4 = s.regs 4 ∧ S.mem = s.mem ∧ S.regs 3 = s.regs 3 ∧ S.regs 5 = s.regs 5 ∧
    S.regs 12 = s.regs 12 ∧ S.regs 13 = s.regs 13 ∧ S.regs 14 = s.regs 14 ∧
    S.regs 15 = s.regs 15 ∧ S.df = s.df

/-- The loop invariant at `head` after `i` of the `n` iterations. -/
theorem csum_loop (p n : BitVec 64) (s : State) (hpre : SumPre p n s) :
    ∀ k (S : State) (i acc : BitVec 64), i.toNat + (k + 1) = n.toNat →
      S.rip = BitVec.ofNat 64 head → S.regs 0 = acc →
      S.regs 2 = BitVec.ofNat 64 (p.toNat + 8 * n.toNat) →
      S.regs 7 = BitVec.ofNat 64 (p.toNat + 8 * i.toNat) → Kept s S →
      acc.toNat = sumWords s.mem p.toNat i.toNat % 2 ^ 64 →
      ReachesRet Extracted.program (retAddrOf s) S (SumPost p n s) := by
  obtain ⟨h7, h6, hb, hacc, hsb, hsa, hra, hdf0⟩ := hpre
  intro k
  induction k with
  | zero =>
    intro S i acc hk hpc hS0 hS2 hS7 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf⟩ hs
    janus64_run
    janus64_simp [SumPost, sumWords_succ, show n.toNat = i.toNat + 1 by omega]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs]
    omega
  | succ k ih =>
    intro S i acc hk hpc hS0 hS2 hS7 ⟨h4, hm, h3, h5, h12, h13, h14, h15, hdf⟩ hs
    janus64_run until [head]
    have hi : (i + 1#64).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    apply ih _ (i + 1#64) _ (by omega) (by janus64_simp) rfl (by janus64_simp) ?_
      (by simp only [Kept]; janus64_simp) (by janus64_simp [sumWords_succ, hi]; omega)
    · janus64_simp
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

/-- The callee contract of `c_sum`, used by the cgo wrapper's proof. -/
theorem csum_summary (p n : BitVec 64) :
    Summary Extracted.program csum (SumPre p n) (SumPost p n) := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨h7, h6, hb, hacc, hsb, hsa, hra, hdf0⟩ := hpre
  janus64_run until [head]
  · janus64_simp [SumPost, sumWords_zero]
  · have he : p + n <<< 3 = BitVec.ofNat 64 (p.toNat + 8 * n.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    exact csum_loop p n s hpre' (n.toNat - 1) _ 0#64 0#64 (by simp; omega) (by janus64_simp)
      (by janus64_simp) (by janus64_simp [he]) (by janus64_simp) (by simp only [Kept]; janus64_simp)
      (by simp)


/-- The sum of `n` words at `p` is the same in two memories that agree outside `rs`. -/
theorem sumWords_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) (p : Nat) :
    ∀ n, Outside p (8 * n) rs → sumWords m' p n = sumWords m p n
  | 0, _ => rfl
  | n + 1, ho => by
    rw [sumWords_succ, sumWords_succ, sumWords_frame h p n (Outside.of_sub ho (Nat.le_refl _) (by omega)),
      h.readLE _ _ (Outside.of_sub ho (by omega) (by omega))]

theorem sumWords_congr {m m' : Memory} (p : Nat) :
    ∀ n, (∀ i, i < n → m'.readLE (p + 8 * i) 8 = m.readLE (p + 8 * i) 8) →
      sumWords m' p n = sumWords m p n
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumWords_succ, sumWords_succ, sumWords_congr p n fun i hi => h i (by omega), h n (by omega)]

/-- The same store, of equal values, on both sides keeps a frame. -/
theorem frame_store {m m' : Memory} {rs : List (Nat × Nat)} {a v v' : Nat} (h : MemFrame m m' rs)
    (hv : v' = v) : MemFrame (m.writeLE a 8 v) (m'.writeLE a 8 v') rs :=
  hv ▸ h.writeLE_both a 8 v

/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_b947fb19b420_Cfunc_c_sum"

/-- The slice pointer and length in the cgo frame at `a`. -/
abbrev frameP (m : Memory) (a : Nat) : Nat := m.readLE a 8
abbrev frameN (m : Memory) (a : Nat) : Nat := m.readLE (a + 8) 8

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 8 ∧ a.toNat + 24 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 24 true = true ∧
    (a.toNat + 24 ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ a.toNat) ∧
    frameP t.mem a.toNat + 8 * frameN t.mem a.toNat ≤ 2 ^ 48 ∧
    t.mem.accessible (frameP t.mem a.toNat) (8 * frameN t.mem a.toNat) false = true ∧
    (frameP t.mem a.toNat + 8 * frameN t.mem a.toNat ≤ (t.regs 4).toNat - 4096 ∨
      (t.regs 4).toNat + 8 ≤ frameP t.mem a.toNat)

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 16) 8
      (sumWords t.mem (frameP t.mem a.toNat) (frameN t.mem a.toNat) % 2 ^ 64)) t'.mem
    [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]

theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd, hpb, hpa, hpd⟩
  apply ReturnsC.of_reaches
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : t.regs 7 = a := hs.reg (i := 0) (by simp)
  simp only [Amd64.Program.withExit] at h_ret
  simp only [CABI.regSP, frameP, frameN] at hal hb htop hacc hpb hpa hpd
  have h32 : (t.regs 4 - 32#64).toNat = (t.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h32]; omega
  · janus64_simp [h32]; janus64_disch
  rintro s₁ ⟨-, f₁, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run calls [csum_summary (BitVec.ofNat 64 (t.mem.readLE a.toNat 8))
    (BitVec.ofNat 64 (t.mem.readLE (a.toNat + 8) 8))]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h32]; omega
  · janus64_simp [h32]; janus64_disch
  rintro s₂ ⟨-, f₂, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run
  simp only [WPost, frameP, frameN, Nat.reducePow, writeLE_mod_8]
  apply frame_store
  · janus_frame
  · apply sumWords_frame (rs := [((t.regs 4).toNat - 4096, (t.regs 4).toNat)])
    · janus_frame
    · simp only [outside_cons, outside_nil, and_true]; omega

/-! ## The Go side: `Sum` → `_Cfunc_c_sum` → `runtime.cgocall` -/

def fnVar : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo._Cfunc_c_sum.abi0" + 0x2e)

def alwaysFalse : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo._Cfunc_c_sum.abi0" + 0x47)

/-- At the `cgocall`: the frame `RBX` and the slice it points at are Go memory the runtime leaves
alone. -/
def G (s : State) : Prop :=
  (s.regs 3).toNat + 24 ≤ 2 ^ 48 ∧ GoKept s (s.regs 3).toNat 24 true ∧
    frameP s.mem (s.regs 3).toNat + 8 * frameN s.mem (s.regs 3).toNat ≤ 2 ^ 48 ∧
    GoKept s (frameP s.mem (s.regs 3).toNat) (8 * frameN s.mem (s.regs 3).toNat) false

def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 3).toNat + 16) 8
    (sumWords s.mem (frameP s.mem (s.regs 3).toNat) (frameN s.mem (s.regs 3).toNat) % 2 ^ 64)

def GoPre (ptr len : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 40 ∧ StackWritable s 80 16 ∧ TlsG s ∧
  ptr.toNat + 8 * len.toNat ≤ 2 ^ 48 ∧ s.mem.accessible ptr.toNat (8 * len.toNat) false = true ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 = 0 ∧
  Outside (s.regs 14).toNat 456 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 16)] ∧
  Outside (s.fsBase.toNat - 8) 8 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 16)] ∧
  Outside fnVar 8 [((s.regs 4).toNat - 80, (s.regs 4).toNat + 16)] ∧
  Outside alwaysFalse 1 [((s.regs 4).toNat - 1104, (s.regs 4).toNat + 16),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)] ∧
  Outside ptr.toNat (8 * len.toNat) [((s.regs 4).toNat - 1104, (s.regs 4).toNat + 16),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)]

set_option maxHeartbeats 2000000 in
theorem go_spec (ptr len cap : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [ptr, len, cap] (GoPre ptr len)
      (fun s s' => (s'.regs 0).toNat = sumWords s.mem ptr.toNat len.toNat % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, htop, hst⟩, ⟨hfs, hfsr, hfsg⟩, hpb, hpa, hfa, hfv, haa, hav, hdg,
    hdt, hdf, hda, hdp⟩
  apply ReturnsC.of_reaches
  janus64_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  simp only [outside_cons, outside_nil, and_true, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG, stackguard0, stackguard0Offset] at *
  have hfsa : (s.fsBase + BitVec.ofNat 64 18446744073709551608).toNat = s.fsBase.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h32 : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h80 : (s.regs 4 - 80#64).toNat = (s.regs 4).toNat - 80 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run [hfsa]
  · simp [sumWords_zero]
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · simp only [G, GoKept, frameP, frameN, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
      cgoStackScratch, gStructSize, outside_cons, outside_nil, and_true]
    janus64_simp [h32, h80]
    refine ⟨by omega, ⟨?_, by omega, by omega, by omega, by omega⟩, by omega, hpa, by omega, by omega,
      by omega, by omega⟩
    janus64_disch
  rintro s' ⟨-, m, ⟨regs, fl, xm, yh, fs, rfl, h4, h5, h14, h15, ⟨⟨hfs1, hfs2⟩, hfsr', hfsg'⟩⟩, hmf⟩
  simp only [E, frameP, frameN, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    Janus.Amd64.GoABI.regFP, Janus.Amd64.GoABI.xmmZero, cgoStackScratch, gStructSize, setRegF,
    ↓reduceIte, Nat.reduceEqDiff, h32, h80] at hmf h4 h5 h14 h15 hfs1 hfs2 hfsr' hfsg'
  have hfsa' : (fs + BitVec.ofNat 64 18446744073709551608).toNat = fs.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hmf.accessible] at hfsr'
  simp only [Janus.Arm64.Memory.accessible_writeLE] at hfsr'
  apply ReturnsC.of_reaches
  janus64_run [h4, h5, h14, h15, hfsa', hfsg']
  -- the slice was read through the stack stores of `Sum` and `_Cfunc_c_sum`
  refine ⟨rfl, congrArg (· % 18446744073709551616) ?_⟩
  apply sumWords_congr
  intro i hi
  clear hmf
  janus64_simp


/-! ## Composition -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, ⟨hacc, hout⟩, hpb, hpacc, hpout⟩ he
    have hsep := he.stackSep _ _ _ hacc
    have hpsep := he.stackSep _ _ _ hpacc
    have hk0 := he.kept _ 8 ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (Nat.le_refl _) (by omega),
      Outside.of_sub hout (Nat.le_refl _) (by omega)⟩
    have hk1 := he.kept ((s.regs 3).toNat + 8) 8 ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega)
      (by omega), Outside.of_sub hout (by omega) (by omega)⟩
    simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep hpsep
    simp only [WPre, frameP, frameN] at hpb hpacc hpout hpsep ⊢
    rw [hk0, hk1]
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by omega, hpb,
      he.keptAcc _ _ _ ⟨hpacc, hpout⟩, by omega⟩
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, ⟨hacc, hout⟩, hpb, hpacc, hpout⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by
      simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep ⊢; omega)
    simp only [Janus.Arm64.Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 3).toNat ≤ c → c + n ≤ (s.regs 3).toNat + 24 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · have e0 := hk _ 8 (Nat.le_refl _) (by omega)
      have e1 := hk ((s.regs 3).toNat + 8) 8 (by omega) (by omega)
      simp only [frameP, frameN] at hpb hpacc hpout ⊢
      rw [e0, e1, sumWords_congr _ _ fun i hi =>
        he.kept _ 8 ⟨Janus.Arm64.Memory.accessible_sub _ hpacc (Or.inl rfl) (by omega) (by omega),
          Outside.of_sub hpout (by omega) (by omega)⟩]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, _⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`Sum` end to end.** -/
theorem correctness (ptr len cap : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [ptr, len, cap]
      (GoPre ptr len) (fun s s' => (s'.regs 0).toNat = sumWords s.mem ptr.toNat len.toNat % 2 ^ 64) :=
  (go_spec ptr len cap).refine refines

end Proof
