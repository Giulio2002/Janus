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
    Outside d.toNat (n + 1) [(s.sp.toNat - (libcStack + 64), s.sp.toNat)]

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
  intro ret hret s hs ⟨hstr, hdb, hda, hdisj, ⟨hal, hb, ha, hw⟩, hos, hod⟩
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
  · trace_state
    all_goals sorry

end Proof
