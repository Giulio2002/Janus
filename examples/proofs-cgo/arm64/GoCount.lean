import Extracted

/-!
# `Count(b []byte, c byte) uint64` (Go) → `c_count` (a gcc -O2 auto-vectorised C loop) → back to Go (arm64)

```go
func Count(b []byte, c byte) uint64 {
	if len(b) == 0 {
		return 0
	}
	return uint64(C.c_count((*C.uint8_t)(unsafe.Pointer(&b[0])), C.uint64_t(len(b)), C.uint8_t(c)))
}
```

**Guarantee (`correctness`).** For every slice header `(ptr, len, cap)`, every byte `c` and every Go
call of `example.com/cgo/neon.Count` satisfying `GoPre ptr len` — the stack checks fall through, the
stack window (and the spill slot above `SP`) is writable, the `len` bytes at `ptr` are readable,
below `2^48` and away from the stack window, the `g` struct and the TLS `g` slot; and the cgo globals
hold their static values — every run returns, restores `SP`, `g` and the frame pointer, and leaves
in `X0` the number of the `len` bytes equal to `c` (`countOf`, the scalar loop), for every length.

The statement is under the trusted `CgoCall Extracted.program` only: `Count`, `_Cfunc_c_count`, the
C wrapper and the vectorised C loop `c_count` are executed by the model.

**How.** The C part is `CCount.lean` (the vector loop `vloop`, the scalar loop `tail`, the callee
contract `summary`), restated with the count as an equation for `X0` (`summaryR`); `wrapper_spec`
uses it at the wrapper's `bl c_count` (the wrapper loads `p`, `n` and the byte `c` from the cgo
frame and stores the count at offset 24); `go_spec` is `Count` under `CgoSpec wrapper G E`;
`refines` and `correctness` compose them as `GoSum.lean` does.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.Spec Janus.FFI

namespace Proof

abbrev ccount : Nat := segAddr Extracted.program "c_count"

/-- The vector and the scalar loop heads of `c_count`. -/
abbrev vhead : Nat := ccount + 0x40
abbrev thead : Nat := ccount + 0xa4

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

set_option maxHeartbeats 4000000 in
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

set_option maxHeartbeats 4000000 in
/-- The vector loop at `vhead` (`ldr q31, [x4], #16`): after `k` blocks the two 64-bit lanes of
`v26` add up to the count of the first `16 k` bytes (modulo `2^64`). -/
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

set_option maxHeartbeats 4000000 in
/-- The callee contract of `c_count`, used by the cgo wrapper's proof. -/
theorem summary (p n c : BitVec 64) :
    Summary Extracted.program ccount (CountPre p n c) (CountPost p n c) := by
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


/-- The contract in the form a caller's `janus_run` uses: the count as an equation for `X0`. -/
abbrev CountPostR (p n c : BitVec 64) (s s' : State) : Prop :=
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
    s'.regs 0 = BitVec.ofNat 64 (countOf s.mem p.toNat (c.toNat % 256) n.toNat)

theorem summaryR (p n c : BitVec 64) :
    Summary Extracted.program ccount (CountPre p n c) (CountPostR p n c) :=
  (summary p n c).mono (fun _ h => h) fun s s' _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      v8, v9, v10, v11, v12, v13, v14, v15, h14, h15⟩ =>
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, v8, v9, v10, v11, v12, v13, v14, v15, h14,
      by rw [← h15, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩

/-- The count of `n` bytes at `p` is the same in two memories that agree outside `rs`. -/
theorem countOf_frame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) (p c : Nat) :
    ∀ n, Outside p n rs → countOf m' p c n = countOf m p c n
  | 0, _ => rfl
  | n + 1, ho => by
    simp only [countOf]
    rw [countOf_frame h p c n (Outside.of_sub ho (Nat.le_refl _) (by omega)),
      h.readLE _ _ (Outside.of_sub ho (by omega) (by omega))]

/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_d35559c3ee2a_Cfunc_c_count"

/-- The slice pointer, the length and the byte in the cgo frame at `a`. -/
abbrev frameP (m : Memory) (a : Nat) : Nat := m.readLE a 8
abbrev frameN (m : Memory) (a : Nat) : Nat := m.readLE (a + 8) 8
abbrev frameC (m : Memory) (a : Nat) : Nat := m.readLE (a + 16) 1

/-- The count the wrapper stores in the frame's result slot. -/
abbrev frameCount (m : Memory) (a : Nat) : Nat := countOf m (frameP m a) (frameC m a) (frameN m a)

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 0 ∧ a.toNat + 32 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 32 true = true ∧
    (a.toNat + 32 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ a.toNat) ∧
    frameP t.mem a.toNat + frameN t.mem a.toNat ≤ 2 ^ 48 ∧
    t.mem.accessible (frameP t.mem a.toNat) (frameN t.mem a.toNat) false = true ∧
    (frameP t.mem a.toNat + frameN t.mem a.toNat ≤ t.sp.toNat - 4096 ∨
      t.sp.toNat ≤ frameP t.mem a.toNat)

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 24) 8 (frameCount t.mem a.toNat)) t'.mem
    [(t.sp.toNat - 4096, t.sp.toNat)]

theorem readLE1_mod (m : Memory) (a : Nat) : m.readLE a 1 % 256 = m.readLE a 1 :=
  Nat.mod_eq_of_lt (by simpa using Memory.readLE_lt m a 1)

set_option maxHeartbeats 4000000 in
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
  janus_run calls [summaryR (BitVec.ofNat 64 (t.mem.readLE a.toNat 8))
    (BitVec.ofNat 64 (t.mem.readLE (a.toNat + 8) 8)) (BitVec.ofNat 64 (t.mem.readLE (a.toNat + 16) 1))]
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp [h48]
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₂ ⟨-, f₂, m₂, rfl, hm₂⟩
  dsimp only at hm₂
  rw [h48] at hm₂
  apply ReturnsC.of_reaches
  janus_run
  refine ⟨?_, ?_⟩
  · repeat' (apply And.intro)
    all_goals assumption
  simp only [WPost, frameCount, frameP, frameN, frameC, Nat.reducePow, writeLE_mod_8]
  have hT : (18446744073709551616 - T.toNat + T.toNat) % 18446744073709551616 = 0 := by
    have := T.isLt; omega
  have hc : t.mem.readLE (a.toNat + 16) 1 % 18446744073709551616 % 256 = t.mem.readLE (a.toNat + 16) 1 := by
    have h1 : t.mem.readLE (a.toNat + 16) 1 < 256 := by simpa using Memory.readLE_lt t.mem (a.toNat + 16) 1
    omega
  simp only [hT, Nat.add_zero, hc]
  have hf₁ : MemFrame t.mem m₁ [(t.sp.toNat - 4096, t.sp.toNat)] := by
    refine MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)]) ?_ hm₁ ?_
    · janus_frame
    · intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hf : MemFrame t.mem m₂ [(t.sp.toNat - 4096, t.sp.toNat)] := by
    refine MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)]) hf₁ hm₂ ?_
    intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  rw [countOf_frame hf₁ _ _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  refine ⟨?_, hf.writeLE_both _ _ _⟩
  -- `V8`–`V15`: the C summary keeps them, the wrapper does not touch them
  simp_all

/-! ## The Go side: `Count` → `_Cfunc_c_count` → `runtime.cgocall` -/

def fnVar : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/neon._Cfunc_c_count.abi0" + 0x24)
    (segWord Extracted.program "example.com/cgo/neon._Cfunc_c_count.abi0" 9)
    (segWord Extracted.program "example.com/cgo/neon._Cfunc_c_count.abi0" 10) 3

def alwaysFalse : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/neon._Cfunc_c_count.abi0" + 0x30)
    (segWord Extracted.program "example.com/cgo/neon._Cfunc_c_count.abi0" 12)
    (segWord Extracted.program "example.com/cgo/neon._Cfunc_c_count.abi0" 13) 0

/-- At the `cgocall`: the frame `X1` and the bytes it points at are Go memory the runtime leaves
alone. -/
def G (s : State) : Prop :=
  (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ GoKept s (s.regs 1).toNat 32 true ∧
    frameP s.mem (s.regs 1).toNat + frameN s.mem (s.regs 1).toNat ≤ 2 ^ 48 ∧
    GoKept s (frameP s.mem (s.regs 1).toNat) (frameN s.mem (s.regs 1).toNat) false

def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 1).toNat + 24) 8 (frameCount s.mem (s.regs 1).toNat)

def GoPre (ptr len : BitVec 64) (s : State) : Prop :=
  GuardOK s 48 ∧ StackOK s 112 16 ∧
  ptr.toNat + len.toNat ≤ 2 ^ 48 ∧ s.mem.accessible ptr.toNat len.toNat false = true ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 % 2 = 0 ∧
  Outside (s.regs 28).toNat 456 [(s.sp.toNat - 112, s.sp.toNat + 16)] ∧
  Outside (s.tpidr.toNat + 16) 8 [(s.sp.toNat - 112, s.sp.toNat + 16)] ∧
  Outside fnVar 8 [(s.sp.toNat - 112, s.sp.toNat + 16)] ∧
  Outside alwaysFalse 1 [(s.sp.toNat - 1120, s.sp.toNat + 16), ((s.regs 28).toNat, (s.regs 28).toNat + 456),
    (s.tpidr.toNat + 16, s.tpidr.toNat + 24)] ∧
  Outside ptr.toNat len.toNat [(s.sp.toNat - 1120, s.sp.toNat + 16),
    ((s.regs 28).toNat, (s.regs 28).toNat + 456), (s.tpidr.toNat + 16, s.tpidr.toNat + 24)]

set_option maxHeartbeats 2000000 in
theorem go_spec (ptr len cap c : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [ptr, len, cap, c] (GoPre ptr len)
      (fun s s' => (s'.regs 0).toNat = countOf s.mem ptr.toNat (c.toNat % 256) len.toNat) := by
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
  · simp [countOf]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus_simp [hfv]
  · simp only [G, GoKept, cgoClobber, frameP, frameN, GoABI.regG, cgoStackScratch, gStructSize,
      tlsGOffset, outside_cons, outside_nil, and_true]
    janus_simp [h40, h96]
    refine ⟨by omega, ⟨?_, by omega, by omega, by omega, by omega⟩, by omega, hpa, by omega, by omega,
      by omega, by omega⟩
    janus_disch
  rintro s' ⟨-, m, ⟨regs, fl, vr, tp, fs, rfl, hg, hfp⟩, hmf⟩
  simp only [E, frameCount, frameP, frameN, frameC, cgoClobber, GoABI.regG, GoABI.regFP, cgoStackScratch, gStructSize,
    tlsGOffset, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h40, h96] at hmf hg hfp
  apply ReturnsC.of_reaches
  janus_run [hg, hfp]
  -- the bytes were read through the stack stores of `Count` and `_Cfunc_c_count`
  have hle := countOf_le s.mem ptr.toNat (c.toNat % 256) len.toNat
  have hl := len.isLt
  rw [countOf_frame (rs := [(s.sp.toNat - 112, s.sp.toNat + 16)])]
  · exact Nat.mod_eq_of_lt (by omega)
  · clear hmf; janus_frame
  · simp only [outside_cons, outside_nil, and_true]; omega

/-! ## Composition -/

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
    have hk : ∀ c n, (s.regs 1).toNat ≤ c → c + n ≤ (s.regs 1).toNat + 32 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · have e0 := hk _ 8 (Nat.le_refl _) (by omega)
      have e1 := hk ((s.regs 1).toNat + 8) 8 (by omega) (by omega)
      have e2 := hk ((s.regs 1).toNat + 16) 1 (by omega) (by omega)
      simp only [frameCount, frameP, frameN, frameC] at hpb hpacc hpout ⊢
      rw [e0, e1, e2, countOf_congr _ _ _ fun i hi =>
        he.kept _ 1 ⟨Memory.accessible_sub _ hpacc (Or.inl rfl) (by omega) (by omega),
          Outside.of_sub hpout (by omega) (by omega)⟩]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, _⟩ b _ hna
    rw [E, Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`Count` end to end.** -/
theorem correctness (ptr len cap c : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [ptr, len, cap, c]
      (GoPre ptr len) (fun s s' => (s'.regs 0).toNat = countOf s.mem ptr.toNat (c.toNat % 256) len.toNat) :=
  (go_spec ptr len cap c).refine refines

end Proof
