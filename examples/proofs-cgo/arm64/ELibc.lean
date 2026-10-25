import Extracted

/-!
# `int64_t e_libc(const char *s, char *d)` (C, arm64): libc through the PLT

```c
int64_t e_libc(const char *s, char *d) {
	size_t n = strlen(s);
	char *m = malloc(n + 1);
	if (!m)
		return -1;
	memcpy(m, s, n + 1);   /* __memcpy_chk(m, s, n + 1, n + 1) under _FORTIFY_SOURCE */
	memcpy(d, m, n + 1);
	free(m);
	return (int64_t)n;
}
```

**Guarantee.** For every string `s` of length `n` and every buffer `d` of `n + 1` writable bytes
apart from it, every AAPCS64 call of the gcc-compiled `e_libc` with a stack window for libc
returns without faulting, restores the callee-saved state, and either returns `n` with the
string (and its terminator) copied to `d`, or returns `-1` (when `malloc` fails) with `d`
unchanged. Every other byte the caller can access is unchanged (apart from the stack below
`SP`), and so is what it can access: the heap block is freed again. This holds under the trusted
libc contract `Janus.Contracts.Libc.Libc` only: every instruction of `e_libc` is executed by
the model, and the five calls (`strlen@plt`, `malloc@plt`, `__memcpy_chk@plt`, `memcpy@plt`,
`free@plt`, PLT entries the extractor recognised) are the contract's.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI Janus.Contracts.Libc

namespace Proof

/-- What the caller provides. -/
def Pre (src d : BitVec 64) (n : Nat) (s : State) : Prop :=
  CStr s.mem src.toNat n ∧ d.toNat + (n + 1) ≤ 2 ^ 48 ∧ s.mem.accessible d.toNat (n + 1) true = true ∧
    (d.toNat + (n + 1) ≤ src.toNat ∨ src.toNat + (n + 1) ≤ d.toNat) ∧ CStack s (libcStack + 64) 0 ∧
    Outside src.toNat (n + 1) [(s.sp.toNat - (libcStack + 64), s.sp.toNat)] ∧
    Outside d.toNat (n + 1) [(s.sp.toNat - (libcStack + 64), s.sp.toNat)] ∧
    ∀ r ∈ s.mem.regions, 0 < r.size

/-- What it gets. -/
def Post (src d : BitVec 64) (n : Nat) (s s' : State) : Prop :=
  ((s'.regs 0 = BitVec.ofNat 64 n ∧ ∀ i, i ≤ n → s'.mem.bytes (d.toNat + i) = s.mem.bytes (src.toNat + i)) ∨
    (s'.regs 0 = BitVec.ofInt 64 (-1) ∧ ∀ i, i ≤ n → s'.mem.bytes (d.toNat + i) = s.mem.bytes (d.toNat + i))) ∧
  (∀ a k w, s'.mem.accessible a k w = s.mem.accessible a k w) ∧
  ∀ a, s.mem.accessible a 1 false = true →
    Outside a 1 [(d.toNat, d.toNat + (n + 1)), (s.sp.toNat - (libcStack + 64), s.sp.toNat)] →
    s'.mem.bytes a = s.mem.bytes a

set_option maxHeartbeats 8000000 in
theorem correctness (src d : BitVec 64) (n : Nat) :
    CEnsuresC Extracted.program Libc Extracted.entry [src, d] (Pre src d n) (Post src d n) := by
  intro ret hret s hs ⟨hstr, hdb, hda, hdisj, ⟨hal, hb, ha, hw⟩, hos, hod, hne⟩
  apply ReturnsC.of_reaches
  janus_intro hs.call
  simp only [outside_cons, outside_nil, and_true, libcStack] at hos hod hb hw ⊢
  have hcs : CStack s (libcStack + 64) 0 := ⟨hal, hb, ha, hw⟩
  have h64 : (s.sp - 64#64).toNat = s.sp.toNat - 64 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run
  -- strlen(s)
  refine libc_call (sp := strlenSpec) (by simp [libcSpecs]) ⟨?_, n, ?_⟩ ?_
  · exact libcCall_of (rs := [(s.sp.toNat - 64, s.sp.toNat)]) hcs (by omega) h64 (by janus_frame)
  · janus_simp
    exact CStr.of_frame (rs := [(s.sp.toNat - 64, s.sp.toNat)]) hstr (by janus_frame) (by simp; omega)
  rintro s1 ⟨n', hn', h1⟩
  have hnn : n' = n := CStr.unique hn' (by
    janus_simp
    exact CStr.of_frame (rs := [(s.sp.toNat - 64, s.sp.toNat)]) hstr (by janus_frame) (by simp; omega))
  subst hnn
  have V1 := h1.cret
  obtain ⟨hpc1, hx01, hcr1, htp1, hdz1, hreg1, hmf1⟩ := h1
  have F1 := memFrame_trans (m₀ := s.mem) (rs := [(s.sp.toNat - 64, s.sp.toNat)]) (by janus_frame) hmf1
  simp only [cReturn_iff, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h64, libcStack, Nat.reducePow] at hcr1 hpc1 hx01 hmf1 hreg1 htp1 hdz1 F1
  obtain_cret hcr1
  apply ReturnsC.of_reaches
  janus_run
  -- malloc(n + 1)
  refine libc_call (sp := mallocSpec) (by simp [libcSpecs])
    (libcCall_of (rs := _) hcs (by omega) h64 F1) ?_
  rintro s2 (h2 | ⟨p, junk, hp0, hp16, hfr, h2⟩)
  · -- malloc failed
    have V2 := h2.cret
    obtain ⟨hpc2, hx02, hcr2, htp2, hdz2, hreg2, hmf2⟩ := h2
    simp only [cReturn_iff, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h64, libcStack, Nat.reducePow] at hcr2 hpc2 hx02 hmf2 hreg2
    obtain_cret hcr2
    have F2 := memFrame_trans F1 hmf2
    apply ReturnsC.of_reaches
    janus_run
    refine ⟨V1.vlow_trans V2 rfl, .inr ⟨rfl, fun i hi => F2.bytes (by simp; omega)⟩,
      fun a k w => F2.accessible a k w, fun a _ ho => F2.bytes (by simp [libcStack] at ho ⊢; omega)⟩
  · have V2 := h2.cret
    obtain ⟨hpc2, hx02, hcr2, htp2, hdz2, hreg2, hmf2⟩ := h2
    simp only [cReturn_iff, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h64, libcStack, Nat.reducePow]
      at hcr2 hpc2 hx02 hmf2 hreg2 hfr
    obtain_cret hcr2
    have hn48 := hstr.1
    have hsz : (BitVec.ofNat 64 n' + 1#64).toNat = n' + 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    rw [hsz] at hfr hmf2 hreg2
    have hpb := hfr.1
    -- the block is away from the stack, the string and `d`
    have hpst : p + (n' + 1) ≤ s.sp.toNat - 32832 ∨ s.sp.toNat ≤ p := by
      have := hfr.disjoint (by omega) (F1.accessible _ _ _ ▸ hw); omega
    have hpsrc := hfr.disjoint (by omega) (F1.accessible _ _ _ ▸ hstr.2.1)
    have hpd := hfr.disjoint (by omega) (F1.accessible _ _ _ ▸ hda)
    -- the stack window libc may use, at every call (all at `SP - 64`)
    have hstk : ∀ S : State, S.sp = s.sp - 64#64 →
        S.mem.accessible (s.sp.toNat - 64 - 32768) 32768 true = true → LibcCall S := by
      intro S h1 h2
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [h1, h64, libcStack, Nat.add_zero]
      all_goals first | omega | (rw [show s.sp.toNat - 64 - 32768 = s.sp.toNat - 64 - 32768 from rfl]; exact h2)
    have hacc1 : ∀ a k w, s1.mem.accessible a k w = s.mem.accessible a k w := F1.accessible
    have hacc2 : ∀ a k w, 0 < k → (a + k ≤ p ∨ p + (n' + 1) ≤ a) →
        s2.mem.accessible a k w = s.mem.accessible a k w := fun a k w hk h => by
      rw [hmf2.accessible, heapAlloc_accessible_out hk h, hacc1]
    have hwin : s.mem.accessible (s.sp.toNat - 64 - 32768) 32768 true = true :=
      Memory.accessible_mono _ hw (by omega) (by omega)
    apply ReturnsC.of_reaches
    janus_run [heapAlloc_readLE_out, heapAlloc_accessible_out]
    -- __memcpy_chk(m, s, n + 1, n + 1)
    refine libc_call (sp := memcpyChkSpec) (by simp [libcSpecs]) ⟨⟨hstk _ rfl ?_, ?_, ?_, ?_⟩, ?_⟩ ?_
    · rw [hacc2 _ _ _ (by omega) (by omega)]; exact hwin
    all_goals try simp only [Buffer, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, hx02, hsz, BitVec.toNat_ofNat]
    · have hp64 : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
      rw [hp64, hmf2.accessible]
      exact ⟨by omega, accessible_heapAlloc_block hfr (Nat.le_refl _) (Nat.le_refl _) true⟩
    · rw [hacc2 _ _ _ (by omega) (by omega)]; exact ⟨by have := hstr.1; omega, hstr.2.1⟩
    · have hp64 : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
      rw [hp64]; omega
    · exact Nat.le_refl _
    intro s3 h3
    have V3 := h3.cret
    obtain ⟨hpc3, hx03, hcr3, htp3, hdz3, hreg3, hmf3⟩ := h3
    simp only [cReturn_iff, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h64, libcStack, Nat.reducePow,
      hx02, hsz, BitVec.toNat_ofNat] at hcr3 hpc3 hx03 hmf3 hreg3
    obtain_cret hcr3
    have hp64 : p % 18446744073709551616 = p := Nat.mod_eq_of_lt (by omega)
    rw [hp64] at hmf3
    apply ReturnsC.of_reaches
    janus_run [copyMem_readLE_out, accessible_copyMem, heapAlloc_readLE_out, heapAlloc_accessible_out]
    have hacc3 : ∀ a k w, s3.mem.accessible a k w = s2.mem.accessible a k w := fun a k w => by
      rw [hmf3.accessible, accessible_copyMem]
    -- memcpy(d, m, n + 1)
    refine libc_call (sp := memcpySpec) (by simp [libcSpecs]) ⟨hstk _ rfl ?_, ?_, ?_, ?_⟩ ?_
    · rw [hacc3, hacc2 _ _ _ (by omega) (by omega)]; exact hwin
    all_goals try simp only [Buffer, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, hsz, BitVec.toNat_ofNat, hp64]
    · rw [hacc3, hacc2 _ _ _ (by omega) (by omega)]; exact ⟨hdb, hda⟩
    · rw [hacc3, hmf2.accessible]
      exact ⟨by omega, accessible_heapAlloc_block hfr (Nat.le_refl _) (Nat.le_refl _) false⟩
    · omega
    intro s4 h4
    have V4 := h4.cret
    obtain ⟨hpc4, hx04, hcr4, htp4, hdz4, hreg4, hmf4⟩ := h4
    simp only [cReturn_iff, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h64, libcStack, Nat.reducePow,
      hsz, BitVec.toNat_ofNat, hp64] at hcr4 hpc4 hx04 hmf4 hreg4
    obtain_cret hcr4
    apply ReturnsC.of_reaches
    janus_run [copyMem_readLE_out, accessible_copyMem, heapAlloc_readLE_out, heapAlloc_accessible_out]
    -- free(m)
    have hreg1' : s1.mem.regions = s.mem.regions := by rw [hreg1]; simp
    have hR : s4.mem.regions = s.mem.regions ++ [⟨p, n' + 1, true⟩, heapToken p (n' + 1)] := by
      rw [hreg4, copyMem_regions, hreg3, copyMem_regions, hreg2, heapAlloc_regions, hreg1']
    have hfr0 : Fresh s.mem p (n' + 1) := ⟨hfr.1, fun r hr => hfr.2 r (by rw [hreg1']; exact hr)⟩
    have hacc4 : ∀ a k w, s4.mem.accessible a k w = s3.mem.accessible a k w := fun a k w => by
      rw [hmf4.accessible, accessible_copyMem]
    refine libc_call (sp := freeSpec) (by simp [libcSpecs]) ⟨hstk _ rfl ?_, .inr ⟨n' + 1, ?_⟩⟩ ?_
    · rw [hacc4, hacc3, hacc2 _ _ _ (by omega) (by omega)]; exact hwin
    · simp only [HeapBlock, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hp64, hR]
      simp
    rintro s5 (⟨h0, -⟩ | ⟨n0, junk', hblk, h5⟩)
    · exfalso
      have := congrArg BitVec.toNat h0
      simp [setReg, hp64] at this
      exact hp0 this
    simp only [HeapBlock, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hp64, hR] at hblk
    have hn0 : n0 = n' + 1 := heapBlock_size hfr0 (by omega) hne hblk.1
    subst hn0
    have V5 := h5.cret
    obtain ⟨hpc5, -, hcr5, htp5, hdz5, hreg5, hmf5⟩ := h5
    simp only [cReturn_iff, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h64, libcStack, Nat.reducePow,
      BitVec.toNat_ofNat, hp64] at hcr5 hpc5 hmf5 hreg5
    obtain_cret hcr5
    have hacc5 : ∀ a k w, 0 < k → (a + k ≤ p ∨ p + (n' + 1) ≤ a) →
        s5.mem.accessible a k w = s.mem.accessible a k w := fun a k w hk h => by
      rw [hmf5.accessible, heapFree_accessible_out hk h, hacc4, hacc3, hacc2 _ _ _ hk h]
    have hfacc : (heapFree s4.mem p (n' + 1) junk').accessible (s.sp.toNat - 64) 64 true = true := by
      rw [heapFree_accessible_out (by omega) (by omega), hacc4, hacc3, hacc2 _ _ _ (by omega) (by omega)]
      exact Memory.accessible_mono _ hw (by omega) (by omega)
    have hfaccR := Memory.accessible_read_of_write _ hfacc
    apply ReturnsC.of_reaches
    janus_run [heapFree_readLE_out, heapFree_accessible_out, copyMem_readLE_out, accessible_copyMem,
      heapAlloc_readLE_out, heapAlloc_accessible_out]
    have VL := (((V1.vlow.trans V2.vlow rfl).trans V3.vlow rfl).trans V4.vlow rfl).trans V5.vlow rfl
    -- the bytes of the final memory, step by step back to `s.mem`
    have hsc : ∀ a, a < s.sp.toNat - 64 - 32768 ∨ s.sp.toNat ≤ a →
        Outside a 1 [(s.sp.toNat - 64 - 32768, s.sp.toNat - 64)] := fun a h => by simp; omega
    have hsc1 : ∀ a, a < s.sp.toNat - 64 - 32768 ∨ s.sp.toNat ≤ a →
        Outside a 1 ([(s.sp.toNat - 64, s.sp.toNat)] ++ [(s.sp.toNat - 64 - 32768, s.sp.toNat - 64)]) :=
      fun a h => by simp; omega
    have b5 : ∀ a, (a < s.sp.toNat - 64 - 32768 ∨ s.sp.toNat ≤ a) → (a < p ∨ p + (n' + 1) ≤ a) →
        s5.mem.bytes a = s4.mem.bytes a := fun a h1 h2 => by
      rw [hmf5.bytes (hsc a h1), heapFree_bytes_out h2]
    have b4 : ∀ a, (a < s.sp.toNat - 64 - 32768 ∨ s.sp.toNat ≤ a) → (a < d.toNat ∨ d.toNat + (n' + 1) ≤ a) →
        s4.mem.bytes a = s3.mem.bytes a := fun a h1 h2 => by
      rw [hmf4.bytes (hsc a h1), copyMem_bytes_out h2]
    have b3 : ∀ a, (a < s.sp.toNat - 64 - 32768 ∨ s.sp.toNat ≤ a) → (a < p ∨ p + (n' + 1) ≤ a) →
        s3.mem.bytes a = s2.mem.bytes a := fun a h1 h2 => by
      rw [hmf3.bytes (hsc a h1), copyMem_bytes_out h2]
    have b2 : ∀ a, (a < s.sp.toNat - 64 - 32768 ∨ s.sp.toNat ≤ a) → (a < p ∨ p + (n' + 1) ≤ a) →
        s2.mem.bytes a = s.mem.bytes a := fun a h1 h2 => by
      rw [hmf2.bytes (hsc a h1), heapAlloc_bytes_out h2, F1.bytes (hsc1 a h1)]
    refine ⟨VL.goal, .inl ⟨by simp [setReg], fun i hi => ?_⟩, fun a k w => ?_, fun a ha ho => ?_⟩
    · show s5.mem.bytes (d.toNat + i) = s.mem.bytes (src.toNat + i)
      rw [b5 _ (by omega) (by omega), hmf4.bytes (hsc _ (by omega)), copyMem_bytes_in (by omega) (by omega),
        show p + (d.toNat + i - d.toNat) = p + i by omega, hmf3.bytes (hsc _ (by omega)),
        copyMem_bytes_in (by omega) (by omega), show src.toNat + (p + i - p) = src.toNat + i by omega,
        b2 _ (by omega) (by omega)]
    · show s5.mem.accessible a k w = s.mem.accessible a k w
      rw [hmf5.accessible, accessible_heapFree_of hR hfr0 (by omega) hp0]
    · show s5.mem.bytes a = s.mem.bytes a
      simp only [outside_cons, outside_nil, and_true, libcStack] at ho
      have hpa := hfr0.disjoint (by omega) ha
      rw [b5 _ (by omega) (by omega), b4 _ (by omega) (by omega), b3 _ (by omega) (by omega),
        b2 _ (by omega) (by omega)]

end Proof
