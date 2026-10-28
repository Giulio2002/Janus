import Extracted

/-!
# `int64_t e_libc(const char *s, char *d)` (C, amd64): libc through the PLT

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
apart from it, every System V call of the gcc-compiled `e_libc` with a stack window for libc
returns without faulting, restores the callee-saved state, and either returns `n` with the
string (and its terminator) copied to `d`, or returns `-1` (when `malloc` fails) with `d`
unchanged. Every other byte the caller can access is unchanged (apart from the stack below
`RSP`), and so is what it can access: the heap block is freed again. This holds under the
trusted libc contract `Janus.Contracts.LibcAmd64.Libc` only: every instruction of `e_libc` is
executed by the model, and the five calls (`strlen@plt`, `malloc@plt`, `__memcpy_chk@plt`,
`memcpy@plt`, `free@plt`: `.plt.sec` entries the extractor recognised) are the contract's.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI
open Janus.Contracts.LibcAmd64
open Janus.Contracts.Libc (libcStack CStr heapAlloc heapFree heapToken HeapBlock Fresh copyMem memFrame_trans)

namespace Proof

abbrev sp (s : State) : Nat := (s.regs 4).toNat

def Pre (src d : BitVec 64) (n : Nat) (s : State) : Prop :=
  CStr s.mem src.toNat n ∧ d.toNat + (n + 1) ≤ 2 ^ 48 ∧ s.mem.accessible d.toNat (n + 1) true = true ∧
    (d.toNat + (n + 1) ≤ src.toNat ∨ src.toNat + (n + 1) ≤ d.toNat) ∧ CStack s (libcStack + 48) 8 ∧
    Outside src.toNat (n + 1) [(sp s - (libcStack + 48), sp s + 8)] ∧
    Outside d.toNat (n + 1) [(sp s - (libcStack + 48), sp s + 8)] ∧
    ∀ r ∈ s.mem.regions, 0 < r.size

def Post (src d : BitVec 64) (n : Nat) (s s' : State) : Prop :=
  ((s'.regs 0 = BitVec.ofNat 64 n ∧ ∀ i, i ≤ n → s'.mem.bytes (d.toNat + i) = s.mem.bytes (src.toNat + i)) ∨
    (s'.regs 0 = BitVec.ofInt 64 (-1) ∧ ∀ i, i ≤ n → s'.mem.bytes (d.toNat + i) = s.mem.bytes (d.toNat + i))) ∧
  (∀ a k w, s'.mem.accessible a k w = s.mem.accessible a k w) ∧
  ∀ a, s.mem.accessible a 1 false = true →
    Outside a 1 [(d.toNat, d.toNat + (n + 1)), (sp s - (libcStack + 48), sp s)] →
    s'.mem.bytes a = s.mem.bytes a

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem correctness (src d : BitVec 64) (n : Nat) :
    CEnsuresC Extracted.program Libc Extracted.entry [src, d] (Pre src d n) (Post src d n) := by
  intro ret hret s hs ⟨hstr, hdb, hda, hdisj, ⟨hal, hb, ha, hw⟩, hos, hod, hne⟩
  apply ReturnsC.of_reaches
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = src := hs.reg (i := 0) (by simp)
  have h_a1 : s.regs 6 = d := hs.reg (i := 1) (by simp)
  simp only [sp, CABI.regSP, Amd64.Program.withExit, libcStack] at hos hod hb hw ha h_ret hal
  simp only [outside_cons, outside_nil, and_true] at hos hod
  have h48 : (s.regs 4 - 48#64).toNat = (s.regs 4).toNat - 48 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  -- the stack window libc may use, at every call (all at `RSP - 48`)
  have hstk : ∀ S : State, S.regs 4 = s.regs 4 - 48#64 →
      S.mem.accessible ((s.regs 4).toNat - 48 - 32768) 32776 true = true → LibcCall S := by
    intro S h1 h2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [CABI.regSP, h1, h48, libcStack]
    all_goals first | omega | exact h2
  have hwin : s.mem.accessible ((s.regs 4).toNat - 48 - 32768) 32776 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  janus64_run
  -- strlen(s)
  refine libc_call (sp := strlenSpec) (by simp [libcSpecs]) ⟨hstk _ (by simp [setRegF_apply]) (by janus64_simp; exact hwin), n, ?_⟩ ?_
  · janus64_simp
    exact CStr.of_frame (rs := [((s.regs 4).toNat - 48, (s.regs 4).toNat)]) hstr (by janus_frame) (by simp; omega)
  rintro s1 ⟨n', hn', h1⟩
  have hnn : n' = n := CStr.unique hn' (by
    janus64_simp
    exact CStr.of_frame (rs := [((s.regs 4).toNat - 48, (s.regs 4).toNat)]) hstr (by janus_frame) (by simp; omega))
  subst hnn
  obtain ⟨hpc1, hx01, hcr1, hfs1, hreg1, hmf1⟩ := h1
  have F1 := memFrame_trans (m₀ := s.mem) (rs := [((s.regs 4).toNat - 48, (s.regs 4).toNat)]) (by janus_frame) hmf1
  simp only [cReturn_iff, retAddrOf_eq, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h48, libcStack, Nat.reducePow,
    Janus.Arm64.Memory.readLE_writeLE_self] at hcr1 hpc1 hx01 hmf1 hreg1 hfs1 F1
  obtain ⟨c1sp, c1bx, c1bp, c112, c113, c114, c115, c1df, c1mx, c1cw⟩ := hcr1
  apply ReturnsC.of_reaches
  janus64_run
  have hB1 : ∀ a, a < (s.regs 4).toNat - 48 - 32768 ∨ (s.regs 4).toNat ≤ a → s1.mem.bytes a = s.mem.bytes a :=
    fun a h => F1.bytes (by simp; omega)
  have hacc1 : ∀ a k w, s1.mem.accessible a k w = s.mem.accessible a k w := F1.accessible
  have hsz : (BitVec.ofNat 64 (n' + 1)).toNat = n' + 1 := by
    have := hstr.1; simp only [BitVec.toNat_ofNat]; omega
  -- malloc(n + 1)
  refine libc_call (sp := mallocSpec) (by simp [libcSpecs])
    (hstk _ (by simp [setRegF_apply]) (by simp only [Janus.Arm64.Memory.accessible_writeLE, hacc1]; exact hwin)) ?_
  rintro s2 (h2 | ⟨p, junk, hp0, hp16, hfr, h2⟩)
  · -- malloc failed
    obtain ⟨hpc2, hx02, hcr2, hfs2, hreg2, hmf2⟩ := h2
    simp only [cReturn_iff, retAddrOf_eq, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h48, libcStack, Nat.reducePow,
      Janus.Arm64.Memory.readLE_writeLE_self] at hcr2 hpc2 hx02 hmf2 hreg2 hfs2
    obtain ⟨c2sp, c2bx, c2bp, c212, c213, c214, c215, c2df, c2mx, c2cw⟩ := hcr2
    apply ReturnsC.of_reaches
    janus64_run
    have hB2 : ∀ a, a < (s.regs 4).toNat - 48 - 32768 ∨ (s.regs 4).toNat ≤ a → s2.mem.bytes a = s.mem.bytes a :=
      fun a h => by
        rw [hmf2.bytes (by simp; omega), Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega), hB1 a h]
    refine ⟨⟨by rw [c2mx, c1mx], by rw [c2cw, c1cw]⟩, .inr ⟨by simp [setRegF_apply],
      fun i hi => hB2 _ (by omega)⟩, fun a k w => ?_, fun a _ ho => hB2 _ (by simp [sp, libcStack] at ho; omega)⟩
    show s2.mem.accessible a k w = s.mem.accessible a k w
    rw [hmf2.accessible, Janus.Arm64.Memory.accessible_writeLE, hacc1]
  · obtain ⟨hpc2, hx02, hcr2, hfs2, hreg2, hmf2⟩ := h2
    simp only [cReturn_iff, retAddrOf_eq, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h48, libcStack, Nat.reducePow,
      Janus.Arm64.Memory.readLE_writeLE_self, hsz] at hcr2 hpc2 hx02 hmf2 hreg2 hfs2 hfr
    obtain ⟨c2sp, c2bx, c2bp, c212, c213, c214, c215, c2df, c2mx, c2cw⟩ := hcr2
    have hn48 := hstr.1
    have hpb := hfr.1
    have hacc1' : ∀ a k w, (Janus.Arm64.Memory.writeLE s1.mem ((s.regs 4).toNat - 48) 8 (janus_eval% (Extracted.entry + 0x23))).accessible a k w =
        s.mem.accessible a k w := fun a k w => by rw [Janus.Arm64.Memory.accessible_writeLE, hacc1]
    -- the block is away from the stack, the string and `d`
    have hpst : p + (n' + 1) ≤ (s.regs 4).toNat - (32768 + 48) ∨ (s.regs 4).toNat + 8 ≤ p := by
      have := hfr.disjoint (by omega) ((hacc1' _ _ _).trans hw); omega
    have hpsrc := hfr.disjoint (by omega) ((hacc1' _ _ _).trans hstr.2.1)
    have hpd := hfr.disjoint (by omega) ((hacc1' _ _ _).trans hda)
    have hacc2 : ∀ a k w, 0 < k → (a + k ≤ p ∨ p + (n' + 1) ≤ a) →
        s2.mem.accessible a k w = s.mem.accessible a k w := fun a k w hk h => by
      rw [hmf2.accessible, Janus.Contracts.Libc.heapAlloc_accessible_out hk h, hacc1']
    have hwin2 : s2.mem.accessible ((s.regs 4).toNat - 48) 8 true = true :=
      (hacc2 _ _ _ (by omega) (by omega)).trans (Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega))
    have hmf2x : True ∧ _ := ⟨trivial, hmf2⟩
    clear hmf2
    apply ReturnsC.of_reaches
    janus64_run
    obtain ⟨-, hmf2⟩ := hmf2x
    have hp64 : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
    have hp64' : p % 18446744073709551616 = p := hp64
    -- __memcpy_chk(m, s, n + 1, n + 1)
    refine libc_call (sp := memcpyChkSpec) (by simp [libcSpecs]) ⟨⟨hstk _ (by simp [setRegF_apply]) ?_, ?_, ?_, ?_⟩, ?_⟩ ?_
    · rw [Janus.Arm64.Memory.accessible_writeLE, hacc2 _ _ _ (by omega) (by omega)]; exact hwin
    · simp only [Janus.Contracts.LibcAmd64.Buffer, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, hsz, BitVec.toNat_ofNat, hp64',
        Janus.Arm64.Memory.accessible_writeLE]
      rw [hmf2.accessible]
      exact ⟨by omega, Janus.Contracts.Libc.accessible_heapAlloc_block hfr (Nat.le_refl _) (Nat.le_refl _) true⟩
    · simp only [Janus.Contracts.LibcAmd64.Buffer, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, hsz, BitVec.toNat_ofNat, hp64',
        Janus.Arm64.Memory.accessible_writeLE]
      rw [hacc2 _ _ _ (by omega) (by omega)]; exact ⟨by omega, hstr.2.1⟩
    · simp only [Janus.Contracts.LibcAmd64.Buffer, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, hsz, BitVec.toNat_ofNat, hp64',
        Janus.Arm64.Memory.accessible_writeLE]
      omega
    · simp [setRegF_apply]
    intro s3 h3
    obtain ⟨hpc3, hx03, hcr3, hfs3, hreg3, hmf3⟩ := h3
    simp only [cReturn_iff, retAddrOf_eq, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h48, libcStack, Nat.reducePow,
      Janus.Arm64.Memory.readLE_writeLE_self, hsz, BitVec.toNat_ofNat, hp64'] at hcr3 hpc3 hx03 hmf3 hreg3 hfs3
    obtain ⟨c3sp, c3bx, c3bp, c312, c313, c314, c315, c3df, c3mx, c3cw⟩ := hcr3
    have hacc3 : ∀ a k w, s3.mem.accessible a k w = s2.mem.accessible a k w := fun a k w => by
      rw [hmf3.accessible, Janus.Contracts.Libc.accessible_copyMem, Janus.Arm64.Memory.accessible_writeLE]
    have hwin3 : s3.mem.accessible ((s.regs 4).toNat - 48) 8 true = true := by
      rw [hacc3]; exact hwin2
    have hmf3x : True ∧ _ := ⟨trivial, hmf3⟩
    clear hmf3
    apply ReturnsC.of_reaches
    janus64_run
    obtain ⟨-, hmf3⟩ := hmf3x
    -- memcpy(d, m, n + 1)
    refine libc_call (sp := memcpySpec) (by simp [libcSpecs]) ⟨hstk _ (by simp [setRegF_apply]) ?_, ?_, ?_, ?_⟩ ?_
    · rw [Janus.Arm64.Memory.accessible_writeLE, hacc3, hacc2 _ _ _ (by omega) (by omega)]; exact hwin
    · simp only [Janus.Contracts.LibcAmd64.Buffer, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, hsz, BitVec.toNat_ofNat, hp64',
        Janus.Arm64.Memory.accessible_writeLE]
      rw [hacc3, hacc2 _ _ _ (by omega) (by omega)]; exact ⟨hdb, hda⟩
    · simp only [Janus.Contracts.LibcAmd64.Buffer, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, hsz, BitVec.toNat_ofNat, hp64',
        Janus.Arm64.Memory.accessible_writeLE]
      rw [hacc3, hmf2.accessible]
      exact ⟨by omega, Janus.Contracts.Libc.accessible_heapAlloc_block hfr (Nat.le_refl _) (Nat.le_refl _) false⟩
    · simp only [Janus.Contracts.LibcAmd64.Buffer, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, hsz, BitVec.toNat_ofNat, hp64',
        Janus.Arm64.Memory.accessible_writeLE]
      omega
    intro s4 h4
    obtain ⟨hpc4, hx04, hcr4, hfs4, hreg4, hmf4⟩ := h4
    simp only [cReturn_iff, retAddrOf_eq, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h48, libcStack, Nat.reducePow,
      Janus.Arm64.Memory.readLE_writeLE_self, hsz, BitVec.toNat_ofNat, hp64'] at hcr4 hpc4 hx04 hmf4 hreg4 hfs4
    obtain ⟨c4sp, c4bx, c4bp, c412, c413, c414, c415, c4df, c4mx, c4cw⟩ := hcr4
    have hacc4 : ∀ a k w, s4.mem.accessible a k w = s3.mem.accessible a k w := fun a k w => by
      rw [hmf4.accessible, Janus.Contracts.Libc.accessible_copyMem, Janus.Arm64.Memory.accessible_writeLE]
    have hwin4 : s4.mem.accessible ((s.regs 4).toNat - 48) 8 true = true := by
      rw [hacc4]; exact hwin3
    have hmf4x : True ∧ _ := ⟨trivial, hmf4⟩
    clear hmf4
    apply ReturnsC.of_reaches
    janus64_run
    obtain ⟨-, hmf4⟩ := hmf4x
    -- free(m)
    have hreg1' : s1.mem.regions = s.mem.regions := by rw [hreg1]; simp
    have hR : s4.mem.regions = s.mem.regions ++ [⟨p, n' + 1, true⟩, heapToken p (n' + 1)] := by
      rw [hreg4, Janus.Contracts.Libc.copyMem_regions, Janus.Arm64.Memory.regions_writeLE, hreg3,
        Janus.Contracts.Libc.copyMem_regions, Janus.Arm64.Memory.regions_writeLE, hreg2,
        Janus.Contracts.Libc.heapAlloc_regions, Janus.Arm64.Memory.regions_writeLE, hreg1']
    have hfr0 : Fresh s.mem p (n' + 1) := ⟨hfr.1, fun r hr => hfr.2 r (by
      rw [Janus.Arm64.Memory.regions_writeLE, hreg1']; exact hr)⟩
    refine libc_call (sp := freeSpec) (by simp [libcSpecs]) ⟨hstk _ (by simp [setRegF_apply]) ?_, .inr ⟨n' + 1, ?_⟩⟩ ?_
    · rw [Janus.Arm64.Memory.accessible_writeLE, hacc4, hacc3, hacc2 _ _ _ (by omega) (by omega)]; exact hwin
    · simp only [HeapBlock, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hp64',
        Janus.Arm64.Memory.regions_writeLE, hR]
      simp
    rintro s5 (⟨h0, -⟩ | ⟨n0, junk', hblk, h5⟩)
    · exfalso
      have := congrArg BitVec.toNat h0
      simp [setRegF_apply, hp64'] at this
      exact hp0 this
    simp only [HeapBlock, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hp64',
      Janus.Arm64.Memory.regions_writeLE, hR] at hblk
    have hn0 : n0 = n' + 1 := Janus.Contracts.Libc.heapBlock_size hfr0 (by omega) hne hblk.1
    subst hn0
    obtain ⟨hpc5, -, hcr5, hfs5, hreg5, hmf5⟩ := h5
    simp only [cReturn_iff, retAddrOf_eq, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h48, libcStack, Nat.reducePow,
      Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, hp64'] at hcr5 hpc5 hmf5 hreg5 hfs5
    obtain ⟨c5sp, c5bx, c5bp, c512, c513, c514, c515, c5df, c5mx, c5cw⟩ := hcr5
    -- the saved registers and the return address, back through every call
    have hchain : ∀ a k, (s.regs 4).toNat - 40 ≤ a → a + k ≤ (s.regs 4).toNat + 8 →
        s5.mem.readLE a k = s1.mem.readLE a k := by
      intro a k h1 h2
      rw [hmf5.readLE a k (by simp; omega), Janus.Contracts.Libc.heapFree_readLE_out,
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hmf4.readLE a k (by simp; omega),
        Janus.Contracts.Libc.copyMem_readLE_out, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        hmf3.readLE a k (by simp; omega), Janus.Contracts.Libc.copyMem_readLE_out,
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hmf2.readLE a k (by simp; omega),
        Janus.Contracts.Libc.heapAlloc_readLE_out, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      all_goals omega
    have hacc5 : ∀ a k w, 0 < k → (a + k ≤ p ∨ p + (n' + 1) ≤ a) →
        s5.mem.accessible a k w = s.mem.accessible a k w := fun a k w hk h => by
      rw [hmf5.accessible, Janus.Contracts.Libc.heapFree_accessible_out hk h, Janus.Arm64.Memory.accessible_writeLE,
        hacc4, hacc3, hacc2 _ _ _ hk h]
    have hracc : s5.mem.accessible ((s.regs 4).toNat - 40) 48 false = true := by
      rw [hacc5 _ _ _ (by omega) (by omega)]
      exact Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega))
    have r0 := hchain ((s.regs 4).toNat) 8 (by omega) (by omega)
    have r1 := hchain ((s.regs 4).toNat - 8) 8 (by omega) (by omega)
    have r2 := hchain ((s.regs 4).toNat - 16) 8 (by omega) (by omega)
    have r3 := hchain ((s.regs 4).toNat - 24) 8 (by omega) (by omega)
    have r4 := hchain ((s.regs 4).toNat - 32) 8 (by omega) (by omega)
    have r5 := hchain ((s.regs 4).toNat - 40) 8 (by omega) (by omega)
    rw [hmf1.readLE ((s.regs 4).toNat) 8 (by simp <;> omega)] at r0
    rw [hmf1.readLE ((s.regs 4).toNat - 8) 8 (by simp <;> omega)] at r1
    rw [hmf1.readLE ((s.regs 4).toNat - 16) 8 (by simp <;> omega)] at r2
    rw [hmf1.readLE ((s.regs 4).toNat - 24) 8 (by simp <;> omega)] at r3
    rw [hmf1.readLE ((s.regs 4).toNat - 32) 8 (by simp <;> omega)] at r4
    rw [hmf1.readLE ((s.regs 4).toNat - 40) 8 (by simp <;> omega)] at r5
    have hmf5x : True ∧ _ := ⟨trivial, hmf5⟩
    clear hmf5
    apply ReturnsC.of_reaches
    janus64_run
    obtain ⟨-, hmf5⟩ := hmf5x
    -- the bytes of the final memory, step by step back to `s.mem`
    have hsc : ∀ a, a < (s.regs 4).toNat - 48 - 32768 ∨ (s.regs 4).toNat ≤ a →
        Outside a 1 [((s.regs 4).toNat - 48 - 32768, (s.regs 4).toNat - 48)] := fun a h => by simp; omega
    have b5 : ∀ a, (a < (s.regs 4).toNat - 48 - 32768 ∨ (s.regs 4).toNat ≤ a) → (a < p ∨ p + (n' + 1) ≤ a) →
        s5.mem.bytes a = s4.mem.bytes a := fun a h1 h2 => by
      rw [hmf5.bytes (hsc a h1), Janus.Contracts.Libc.heapFree_bytes_out h2,
        Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]
    have b4 : ∀ a, (a < (s.regs 4).toNat - 48 - 32768 ∨ (s.regs 4).toNat ≤ a) →
        (a < d.toNat ∨ d.toNat + (n' + 1) ≤ a) → s4.mem.bytes a = s3.mem.bytes a := fun a h1 h2 => by
      rw [hmf4.bytes (hsc a h1), Janus.Contracts.Libc.copyMem_bytes_out h2,
        Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]
    have b3 : ∀ a, (a < (s.regs 4).toNat - 48 - 32768 ∨ (s.regs 4).toNat ≤ a) → (a < p ∨ p + (n' + 1) ≤ a) →
        s3.mem.bytes a = s2.mem.bytes a := fun a h1 h2 => by
      rw [hmf3.bytes (hsc a h1), Janus.Contracts.Libc.copyMem_bytes_out h2,
        Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]
    have b2 : ∀ a, (a < (s.regs 4).toNat - 48 - 32768 ∨ (s.regs 4).toNat ≤ a) → (a < p ∨ p + (n' + 1) ≤ a) →
        s2.mem.bytes a = s.mem.bytes a := fun a h1 h2 => by
      rw [hmf2.bytes (hsc a h1), Janus.Contracts.Libc.heapAlloc_bytes_out h2,
        Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega), hB1 a h1]
    refine ⟨⟨by rw [c5mx, c4mx, c3mx, c2mx, c1mx], by rw [c5cw, c4cw, c3cw, c2cw, c1cw]⟩,
      .inl ⟨by simp [setRegF_apply], fun i hi => ?_⟩, fun a k w => ?_, fun a ha ho => ?_⟩
    · show s5.mem.bytes (d.toNat + i) = s.mem.bytes (src.toNat + i)
      rw [b5 _ (by omega) (by omega), hmf4.bytes (hsc _ (by omega)),
        Janus.Contracts.Libc.copyMem_bytes_in (by omega) (by omega),
        show p + (d.toNat + i - d.toNat) = p + i by omega,
        Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega), hmf3.bytes (hsc _ (by omega)),
        Janus.Contracts.Libc.copyMem_bytes_in (by omega) (by omega),
        show src.toNat + (p + i - p) = src.toNat + i by omega,
        Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega), b2 _ (by omega) (by omega)]
    · show s5.mem.accessible a k w = s.mem.accessible a k w
      rw [hmf5.accessible, Janus.Contracts.Libc.accessible_heapFree_of
        (by rw [Janus.Arm64.Memory.regions_writeLE, hR]) hfr0 (by omega) hp0]
    · show s5.mem.bytes a = s.mem.bytes a
      simp only [outside_cons, outside_nil, and_true, sp, libcStack] at ho
      have hpa := hfr0.disjoint (by omega) ha
      rw [b5 _ (by omega) (by omega), b4 _ (by omega) (by omega), b3 _ (by omega) (by omega),
        b2 _ (by omega) (by omega)]

end Proof
