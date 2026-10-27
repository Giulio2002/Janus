import Extracted

/-!
# `uint64_t c_count(const uint8_t *p, uint64_t n, uint8_t c)` (C, arm64): a byte count, auto-vectorised by gcc -O2

```c
uint64_t c_count(const uint8_t *p, uint64_t n, uint8_t c) {
	uint64_t k = 0;
	for (uint64_t i = 0; i < n; i++)
		k += p[i] == c;
	return k;
}
```

**Guarantee.** For every pointer `p`, count `n` and byte `c` such that the `n` bytes at `p` are
readable (and below `2^48`), every AAPCS64 call of the gcc-compiled `c_count` returns without
faulting, restores `SP` and `X19`–`X29`, leaves memory unchanged, and returns in `X0` the number of
the `n` bytes equal to `c` (`countOf`, the scalar spec; only the low byte of `X2` is the argument,
hence `c.toNat % 256`). This holds for every `n`: both loops terminate.

**The code.** cgo compiles `examples/cgo/neon/cneon.c` with gcc 15.2.0 at its default `-O2`, and the vectoriser
turns the loop into a 16-byte loop — `LDR Q` with post-increment, `CMEQ .16B` against `DUP`ed `c`,
`AND` with `MOVI .16B, #1`, the widening ladder `ZIP1`/`ZIP2` with a zero vector (`.16B` → `.8H` →
`.4S`), `UADDW`/`UADDW2` into 64-bit lanes and `ADD .2D` into the accumulator `v26` — then `ADDP D`
and `FMOV`, and a scalar loop (`LDRB`, `CMP`, `CINC`) over the last `n mod 16` bytes, or all of
them when `n < 16`. The same words as `examples/proofs/A64CountByte.lean` (`v_count` of the
coverage corpus).

**How.** `vloop` is the invariant of the vector loop (the two lanes of `v26` add up to the count
of the first `16 k` bytes, modulo `2^64`; one iteration is evaluated lane by lane with the element
lemmas of `Janus.Tactic.Neon`, and `countOf_add16` matches the sixteen byte tests), `tail` that of
the scalar loop, both by induction on the iterations left; `summary` is the callee contract the
cgo wrapper uses (`GoCount.lean`), and `correctness` follows from it by `CEnsures.of_summary`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.Spec Janus.FFI

namespace Proof

abbrev vhead : Nat := Extracted.entry + 0x40
abbrev thead : Nat := Extracted.entry + 0xa4

abbrev Kept (s S : State) : Prop :=
  S.sp = s.sp ∧ S.mem = s.mem ∧ S.regs 19 = s.regs 19 ∧ S.regs 20 = s.regs 20 ∧
    S.regs 21 = s.regs 21 ∧ S.regs 22 = s.regs 22 ∧ S.regs 23 = s.regs 23 ∧
    S.regs 24 = s.regs 24 ∧ S.regs 25 = s.regs 25 ∧ S.regs 26 = s.regs 26 ∧
    S.regs 27 = s.regs 27 ∧ S.regs 28 = s.regs 28 ∧ S.regs 29 = s.regs 29 ∧
    S.regs 30 = s.regs 30 ∧ S.fpcr = s.fpcr ∧
    S.vregs 8 = s.vregs 8 ∧
    S.vregs 9 = s.vregs 9 ∧
    S.vregs 10 = s.vregs 10 ∧
    S.vregs 11 = s.vregs 11 ∧
    S.vregs 12 = s.vregs 12 ∧
    S.vregs 13 = s.vregs 13 ∧
    S.vregs 14 = s.vregs 14 ∧
    S.vregs 15 = s.vregs 15

abbrev CountPre (p n c : BitVec 64) (s : State) : Prop :=
  s.regs 0 = p ∧ s.regs 1 = n ∧ s.regs 2 = c ∧ p.toNat + n.toNat ≤ 2 ^ 48 ∧
    s.mem.accessible p.toNat n.toNat false = true ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56

abbrev CountPost (p n c : BitVec 64) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 19 = s.regs 19 ∧ s'.regs 20 = s.regs 20 ∧ s'.regs 21 = s.regs 21 ∧
    s'.regs 22 = s.regs 22 ∧ s'.regs 23 = s.regs 23 ∧ s'.regs 24 = s.regs 24 ∧
    s'.regs 25 = s.regs 25 ∧ s'.regs 26 = s.regs 26 ∧ s'.regs 27 = s.regs 27 ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.fpcr = s.fpcr ∧
    (s'.vregs 8).toNat % 2 ^ 64 = (s.vregs 8).toNat % 2 ^ 64 ∧
    (s'.vregs 9).toNat % 2 ^ 64 = (s.vregs 9).toNat % 2 ^ 64 ∧
    (s'.vregs 10).toNat % 2 ^ 64 = (s.vregs 10).toNat % 2 ^ 64 ∧
    (s'.vregs 11).toNat % 2 ^ 64 = (s.vregs 11).toNat % 2 ^ 64 ∧
    (s'.vregs 12).toNat % 2 ^ 64 = (s.vregs 12).toNat % 2 ^ 64 ∧
    (s'.vregs 13).toNat % 2 ^ 64 = (s.vregs 13).toNat % 2 ^ 64 ∧
    (s'.vregs 14).toNat % 2 ^ 64 = (s.vregs 14).toNat % 2 ^ 64 ∧
    (s'.vregs 15).toNat % 2 ^ 64 = (s.vregs 15).toNat % 2 ^ 64 ∧ s'.mem = s.mem ∧
    (s'.regs 0).toNat = countOf s.mem p.toNat (c.toNat % 256) n.toNat

/-- `c` as the C code sees it: `and w2, w2, #0xff`. -/
abbrev cw (c : BitVec 64) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 c &&& 255#32)

theorem cw_toNat (c : BitVec 64) : (cw c).toNat = c.toNat % 256 := by
  have h : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  simp [cw, h]

/-- One step of the scalar loop: `cmp w4, w2; cinc x0, x0, eq`. -/
theorem acc_step (m : Memory) (p : Nat) (c i acc : BitVec 64)
    (hacc : acc.toNat = countOf m p (c.toNat % 256) i.toNat) (hi : i.toNat < 2 ^ 63) :
    (if (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE (p + i.toNat) 1))).toNat =
        (BitVec.setWidth 32 (cw c)).toNat then acc + 1#64 else acc).toNat =
      countOf m p (c.toNat % 256) (i.toNat + 1) := by
  have hr : m.readLE (p + i.toNat) 1 < 256 := by simpa using Memory.readLE_lt m (p + i.toNat) 1
  have hle := countOf_le m p (c.toNat % 256) i.toNat
  have hc : (BitVec.setWidth 32 c &&& 255#32).toNat % 2 ^ 64 % 2 ^ 32 = c.toNat % 256 := by
    have h : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
    simp [h]; omega
  simp only [countOf, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [hc]
  by_cases hm : m.readLE (p + i.toNat) 1 = c.toNat % 256
  · rw [if_pos (by rw [hm]; omega), if_pos hm, BitVec.toNat_add]; simp; omega
  · rw [if_neg (by omega), if_neg hm]; omega

/-- The scalar loop at `thead` (`ldrb w4, [x5, x3]`), from index `i` with `X0` the count of the
first `i` bytes. -/
theorem tail (p n c : BitVec 64) (s : State) (hpre : CountPre p n c s) :
    ∀ k (S : State) (i acc : BitVec 64), i.toNat + k + 1 = n.toNat →
      S.pc = BitVec.ofNat 64 thead → S.regs 0 = acc → S.regs 1 = n → S.regs 2 = cw c →
      S.regs 3 = i → S.regs 5 = p → acc.toNat = countOf s.mem p.toNat (c.toNat % 256) i.toNat →
      Kept s S → ReachesRet Extracted.program (s.regs 30) S (CountPost p n c s) := by
  obtain ⟨h0, h1, h2, hb, hacc, hal, htag⟩ := hpre
  intro k
  induction k with
  | zero =>
    intro S i acc hk hpc hS0 hS1 hS2 hS3 hS5 hs ⟨hsp, hm, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hfc, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15⟩
    janus_run
    janus_simp [CountPost, hfc, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    rw [show n.toNat = i.toNat + 1 by omega]
    exact acc_step _ _ _ _ _ hs (by omega)
  | succ k ih =>
    intro S i acc hk hpc hS0 hS1 hS2 hS3 hS5 hs ⟨hsp, hm, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hfc, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15⟩
    janus_run until [thead]
    refine ih _ (i + 1#64) _ (by janus_simp; omega) (by janus_simp) rfl (by janus_simp) (by janus_simp)
      (by janus_simp) (by janus_simp) ?_ (by simp only [Kept]; janus_simp [hfc, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15])
    janus_simp
    exact acc_step _ _ _ _ _ hs (by omega)

theorem ite255_and1 (P : Prop) [Decidable P] : ((if P then 255 else 0) &&& 1 : Nat) = if P then 1 else 0 := by
  split <;> rfl

/-- The vector loop at `vhead` (`ldr q31, [x4], #16`): after `k` blocks the two 64-bit lanes of
`v26` add up to the count of the first `16 k` bytes (modulo `2^64`). -/
set_option maxHeartbeats 1000000 in
theorem vloop (p n c : BitVec 64) (s : State) (hpre : CountPre p n c s) :
    ∀ r (S : State) (k : Nat), k + r + 1 = n.toNat / 16 →
      S.pc = BitVec.ofNat 64 vhead → S.regs 0 = p + (n &&& 18446744073709551600#64) →
      S.regs 1 = n → S.regs 2 = cw c → S.regs 3 = (n &&& 18446744073709551600#64) →
      S.regs 4 = p + BitVec.ofNat 64 (16 * k) → S.regs 5 = p →
      S.vregs 23 = BitVec.ofNat 128 (ofElems 8 16 fun _ => (cw c).toNat) →
      S.vregs 24 = BitVec.ofNat 128 ones8 → S.vregs 29 = 0 →
      (elem (S.vregs 26).toNat 64 0 + elem (S.vregs 26).toNat 64 1) % 2 ^ 64 =
        countOf s.mem p.toNat (c.toNat % 256) (16 * k) % 2 ^ 64 →
      Kept s S → ReachesRet Extracted.program (s.regs 30) S (CountPost p n c s) := by
  have hpre' := hpre
  obtain ⟨h0, h1, h2, hb, hacc, hal, htag⟩ := hpre
  have hn16 := and_mask16_toNat n
  have hlen := n.isLt
  have hc' : (cw c).toNat % 256 = c.toNat % 256 := by rw [cw_toNat, Nat.mod_mod]
  intro r
  induction r with
  | zero =>
    intro S k hk hpc hS0 hS1 hS2 hS3 hS4 hS5 hv23 hv24 hv29 hv26 ⟨hsp, hm, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hfc, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15⟩
    janus_run [hv23, hv24, hv29, elem_ones8] until [vhead, thead]
    · -- the last block, and no tail
      rename_i _ hl0 _
      janus_simp [CountPost, hfc, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
      rw [hc']
      have hl : n.toNat = 16 * k + 16 := by rw [and_mask16 _ hlen] at hl0; omega
      have hcl := countOf_le s.mem p.toNat (c.toNat % 256) n.toNat
      rw [hl, countOf_add16] at hcl ⊢
      have := elem_lt (S.vregs 26).toNat 64 0
      have := elem_lt (S.vregs 26).toNat 64 1
      omega
    · -- the last block, then the scalar tail from `16 (k + 1)`
      rename_i hbr'
      rw [and_mask16 _ hlen] at hbr hbr'
      refine tail p n c s hpre' (n.toNat - (16 * k + 16) - 1) _
        (n &&& 18446744073709551600#64) _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (try janus_simp)
      all_goals (try (rw [and_mask16 _ hlen]; omega))
      · rw [hc', and_mask16 _ hlen, show n.toNat / 16 * 16 = 16 * k + 16 by omega, countOf_add16]
        have := elem_lt (S.vregs 26).toNat 64 0
        have := elem_lt (S.vregs 26).toNat 64 1
        have hcl := countOf_le s.mem p.toNat (c.toNat % 256) (16 * k + 16)
        rw [countOf_add16] at hcl
        omega
      · simp only [Kept]; janus_simp [hfc, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · -- a further iteration is impossible: this was the last block
      rw [and_mask16 _ hlen] at hbr
      exfalso; apply hbr; omega
  | succ r ih =>
    intro S k hk hpc hS0 hS1 hS2 hS3 hS4 hS5 hv23 hv24 hv29 hv26 ⟨hsp, hm, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, hfc, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15⟩
    janus_run [hv23, hv24, hv29, elem_ones8] until [vhead, thead]
    · rename_i hx; rw [and_mask16 _ hlen] at hx; omega
    · refine ih _ (k + 1) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (try janus_simp [elem_ones8])
      · rw [show 16 * (k + 1) = 16 * k + 16 by omega]
      · exact hv23
      · exact hv24
      · simpa using hv29
      · rw [hc', show 16 * (k + 1) = 16 * k + 16 by omega, countOf_add16]
        omega
      · simp only [Kept]; janus_simp [hfc, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]

/-- The callee contract of `c_count`, used by the cgo wrapper's proof. -/
theorem summary (p n c : BitVec 64) :
    Summary Extracted.program Extracted.entry (CountPre p n c) (CountPost p n c) := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨h0, h1, h2, hb, hacc, hal, htag⟩ := hpre
  have hn16 := and_mask16_toNat n
  janus_run [modImmOp_movi0, modImmOp_movi1] until [vhead, thead]
  · janus_simp [CountPost]; rfl
  · refine tail p n c s hpre' (n.toNat - 1) _ 0#64 0#64 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try janus_simp)
    all_goals (try omega)
    · rfl
    · simp only [Kept]; janus_simp
  · refine vloop p n c s hpre' (n.toNat / 16 - 1) _ 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try janus_simp)
    all_goals (try omega)
    · congr 1; exact Nat.mod_eq_of_lt (ofElems_lt 8 16 _)
    · rfl
    · simp only [Kept]; janus_simp

theorem correctness (p n c : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p, n, c]
      (fun s => p.toNat + n.toNat ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat n.toNat false = true)
      (fun s s' => (s'.regs 0).toNat = countOf s.mem p.toNat (c.toNat % 256) n.toNat ∧ s'.mem = s.mem) :=
  CEnsures.of_summary (summary p n c)
    (fun ret s hret hs ⟨hb, hacc⟩ => by
      have h0 := hs.call.reg (i := 0) (by simp)
      have h1 := hs.call.reg (i := 1) (by simp)
      have h2 := hs.call.reg (i := 2) (by simp)
      have hlr := hs.call.lr
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, Program.withExit] at h0 h1 h2 hlr
      refine ⟨h0, h1, h2, hb, hacc, ?_, ?_⟩ <;> rw [hlr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hret.lt64]
      · exact hret.aligned
      · have := hret.user; omega)
    (fun s s' _ h => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, v8, v9, v10, v11, v12, v13,
        v14, v15, h14, h15⟩ := h
      exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, v8, v9, v10, v11, v12, v13,
        v14, v15⟩, h15, h14⟩)

end Proof
