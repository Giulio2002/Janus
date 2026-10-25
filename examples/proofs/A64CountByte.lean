import Extracted

/-!
# `A64CountByte(b []byte, c byte)`: a gcc -O2 auto-vectorised C loop, proved against its scalar spec

**Guarantee.** For every slice `b` (pointer `p`, length `len`, capacity `cap`), every byte `c` and
every Go call state `s` of `example.com/basic.A64CountByte` such that
* the stack-growth prologue falls through (`GuardOK s 0`), `SP` is aligned and the bytes from 88
  below to 16 above `SP` are writable (the frames of `A64CountByte` and of the ABI0 shim, and the
  spill slot of `p` in the caller's argument area),
* the `len` bytes at `p` are readable and do not overlap that stack window,

the call returns (never faulting or panicking), obeys the ABI, and returns in `X0` the number of
the `len` bytes that equal `c` (`countOf`, the scalar C loop
`for (i = 0; i < n; i++) k += p[i] == c;`). Only the low byte of `X3` is the argument `c`, so
the statement uses `c.toNat % 256`. It holds for **every** length (`len < 2^48` follows from
the readable range), so both loops terminate and nothing is read outside the slice.

**What this covers.** `A64CountByte` calls `vCount` (an ABI0 assembly shim, `countbyte_arm64.s`),
which loads the arguments into `X0`–`X2` and calls `vCountC`: the 53 instruction words that
gcc 15.2.0 emits at cgo's default `-O2` (`-fPIC -pthread -g`) for `v_count` of
`scripts/coverage/ccorpus/vec.c`, copied verbatim (`WORD`). The proof executes all three
functions instruction by instruction from the extracted words. gcc vectorises the loop into a
16-byte block loop — `LDR Q` with post-increment, `CMEQ .16B` against `DUP`ed `c`, `AND` with
`MOVI .16B, #1`, the widening ladder `ZIP1`/`ZIP2` with a zero vector (`.16B` → `.8H` → `.4S`),
`UADDW`/`UADDW2` into 64-bit lanes and `ADD .2D` into the accumulator `v26` — followed by
`ADDP D` and `FMOV`, then a scalar loop (`LDRB`, `CMP`, `CINC`) over the last `len mod 16`
bytes (or all of them when `len < 16`). `ZIP1`, `ZIP2`, `UADDW`, `UADDW2` and scalar `ADDP` are
modelled by `Janus.Arm64.NeonInstr` (`DecodeNeon`, `ExecNeon`), the rest by the original SIMD
subset; each is checked against qemu and the Arm ASL (Sail) (`docs/ORACLE.md`).

**How.** `vloop` is the invariant of the vector loop: after `k` blocks the two 64-bit lanes of
`v26` add up to the count of the first `16 k` bytes (modulo `2^64`); one iteration is executed
symbolically, and the element lemmas of `Janus.Tactic.Neon` (`elem_zip_zero_*`, `elem_uaddw_64`,
`elem_add`) reduce the new lanes to sums of the sixteen byte tests, which `countOf_add16` matches.
`tail` is the invariant of the scalar loop. Both are proved by induction on the iterations left.

**Layout.** The loop heads and the return addresses inside the callees are offsets from the
callees' extracted segments (`segAddr`), so the proof does not depend on where the linker puts them.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- The shim and the C code (`segAddr`: their addresses in the extracted program). -/
abbrev sbase : Nat := segAddr Extracted.program "example.com/basic.vCount.abi0"
abbrev cbase : Nat := segAddr Extracted.program "example.com/basic.vCountC"

/-- The return address in the shim after its `BL vCountC`, and in `A64CountByte` after its call. -/
abbrev sret : Nat := sbase + 0x1c
abbrev gret : Nat := Extracted.entry + 0x28

/-- The vector loop head (`ldr q31, [x4], #16`) and the scalar loop head (`ldrb w4, [x5, x3]`). -/
abbrev vhead : Nat := cbase + 0x40
abbrev thead : Nat := cbase + 0xa4

/-- `c` as the C code sees it: the byte the shim loads, `and w2, w2, #0xff`. -/
abbrev cw (c : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (c.toNat % 256)) &&& 255#32)

theorem cw32_toNat (c : BitVec 64) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 (c.toNat % 256)) &&& 255#32).toNat = c.toNat % 256 := by
  have h : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  simp [h]

theorem cw_toNat (c : BitVec 64) : (cw c).toNat = c.toNat % 256 := by
  have h : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  simp [cw, h]

/-- The memory inside `vCountC`: the frames of A64CountByte and of the shim. -/
abbrev frameMem (s : State) (ret : Nat) (p len c : BitVec 64) : Memory :=
  (((((((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8
    (s.regs 29).toNat).writeLE (s.sp.toNat + 8) 8 p.toNat).writeLE (s.sp.toNat - 40) 8 p.toNat).writeLE
    (s.sp.toNat - 32) 8 len.toNat).writeLE (s.sp.toNat - 24) 1 c.toNat).writeLE
    (s.sp.toNat - 80) 8 gret).writeLE (s.sp.toNat - 88) 8 (s.sp.toNat - 56)

/-- One step of the scalar loop: `cmp w4, w2; cinc x0, x0, eq`. -/
theorem acc_step (m : Memory) (p : Nat) (c i acc : BitVec 64)
    (hacc : acc.toNat = countOf m p (c.toNat % 256) i.toNat) (hi : i.toNat < 2 ^ 63) :
    (if (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE (p + i.toNat) 1))).toNat =
        (BitVec.setWidth 32 (cw c)).toNat then acc + 1#64 else acc).toNat =
      countOf m p (c.toNat % 256) (i.toNat + 1) := by
  have hr := Memory.readLE_lt m (p + i.toNat) 1
  have hle := countOf_le m p (c.toNat % 256) i.toNat
  simp only [countOf, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [cw32_toNat]
  by_cases hc : m.readLE (p + i.toNat) 1 = c.toNat % 256
  · have : m.readLE (p + i.toNat) 1 % 2 ^ 64 % 2 ^ 32 = c.toNat % 256 % 2 ^ 64 % 2 ^ 32 := by rw [hc]
    simp only [ite_true, hc, BitVec.toNat_add]; simp; omega
  · have : ¬ m.readLE (p + i.toNat) 1 % 2 ^ 64 % 2 ^ 32 = c.toNat % 256 % 2 ^ 64 % 2 ^ 32 := by omega
    simp only [this, ite_false, hc]; omega

set_option maxHeartbeats 4000000 in
/-- The scalar loop: from index `i` (with `acc` the count of the first `i` bytes), the call
returns the count of all `len` bytes. -/
theorem tail (p len c : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hal : s.sp.toNat % 16 = 0) (hb : 88 ≤ s.sp.toNat) (ha : s.sp.toNat + 16 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 88) (88 + 16) true = true)
    (hP : s.mem.accessible p.toNat len.toNat false = true) (hP' : p.toNat + len.toNat ≤ 2 ^ 48)
    (hd : p.toNat + len.toNat ≤ s.sp.toNat - 88 ∨ s.sp.toNat - 88 + 104 ≤ p.toNat) :
    ∀ k (S : State) (i acc : BitVec 64), i.toNat + k + 1 = len.toNat →
      S.pc = BitVec.ofNat 64 thead → S.regs 0 = acc → S.regs 1 = len → S.regs 2 = cw c →
      S.regs 3 = i → S.regs 5 = p → acc.toNat = countOf s.mem p.toNat (c.toNat % 256) i.toNat →
      S.regs 29 = s.sp - 88#64 → S.regs 30 = BitVec.ofNat 64 sret → S.sp = s.sp - 80#64 →
      S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = frameMem s ret p len c →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = countOf s.mem p.toNat (c.toNat % 256) len.toNat) := by
  intro k
  induction k with
  | zero =>
    intro S i acc hn hpc h0 h1 h2 h3 h5 hacc h29 h30 hsp h28 h18 hm
    janus_eval_nat hsret : sret
    janus_eval_nat hgret : gret
    janus_eval_nat hvh : vhead
    janus_eval_nat hth : thead
    janus_run [hsret, hgret]
    rw [show len.toNat = i.toNat + 1 by omega]
    exact acc_step _ _ _ _ _ hacc (by omega)
  | succ k ih =>
    intro S i acc hn hpc h0 h1 h2 h3 h5 hacc h29 h30 hsp h28 h18 hm
    janus_eval_nat hsret : sret
    janus_eval_nat hgret : gret
    janus_eval_nat hvh : vhead
    janus_eval_nat hth : thead
    janus_run [hsret, hgret] until [thead]
    refine ih _ (i + 1#64) _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try janus_simp [hsret, hgret, hvh, hth])
    all_goals (try omega)
    exact acc_step _ _ _ _ _ hacc (by omega)

theorem ite255_and1 (P : Prop) [Decidable P] : ((if P then 255 else 0) &&& 1 : Nat) = if P then 1 else 0 := by
  split <;> rfl

set_option maxHeartbeats 8000000 in
/-- The vector loop: after `k` blocks the two 64-bit lanes of `v26` add up to the count of the
first `16 k` bytes (modulo `2^64`). -/
theorem vloop (p len c : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hal : s.sp.toNat % 16 = 0) (hb : 88 ≤ s.sp.toNat) (ha : s.sp.toNat + 16 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 88) (88 + 16) true = true)
    (hP : s.mem.accessible p.toNat len.toNat false = true) (hP' : p.toNat + len.toNat ≤ 2 ^ 48)
    (hd : p.toNat + len.toNat ≤ s.sp.toNat - 88 ∨ s.sp.toNat - 88 + 104 ≤ p.toNat) :
    ∀ r (S : State) (k : Nat), k + r + 1 = len.toNat / 16 →
      S.pc = BitVec.ofNat 64 vhead → S.regs 0 = p + (len &&& 18446744073709551600#64) →
      S.regs 1 = len → S.regs 2 = cw c → S.regs 3 = (len &&& 18446744073709551600#64) →
      S.regs 4 = p + BitVec.ofNat 64 (16 * k) → S.regs 5 = p →
      S.vregs 23 = BitVec.ofNat 128 (ofElems 8 16 fun _ => (cw c).toNat) →
      S.vregs 24 = BitVec.ofNat 128 ones8 → S.vregs 29 = 0 →
      (elem (S.vregs 26).toNat 64 0 + elem (S.vregs 26).toNat 64 1) % 2 ^ 64 =
        countOf s.mem p.toNat (c.toNat % 256) (16 * k) % 2 ^ 64 →
      S.regs 29 = s.sp - 88#64 → S.regs 30 = BitVec.ofNat 64 sret → S.sp = s.sp - 80#64 →
      S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = frameMem s ret p len c →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = countOf s.mem p.toNat (c.toNat % 256) len.toNat) := by
  have hn16 := and_mask16_toNat len
  intro r
  induction r with
  | zero =>
    intro S k hn hpc h0 h1 h2 h3 h4 h5 h23 h24 h29 h26 h29' h30 hsp h28 h18 hm
    have hlen := len.isLt
    have hc' : (cw c).toNat % 256 = c.toNat % 256 := by rw [cw_toNat, Nat.mod_mod]
    janus_eval_nat hsret : sret
    janus_eval_nat hgret : gret
    janus_eval_nat hvh : vhead
    janus_eval_nat hth : thead
    janus_run [h23, h24, h29, elem_ones8, hsret, hgret] until [vhead, thead]
    · -- the last block, and no tail
      rename_i hbr'
      rw [hc']
      have hl : len.toNat = 16 * k + 16 := by rw [and_mask16 _ hlen] at hbr; omega
      have hcl := countOf_le s.mem p.toNat (c.toNat % 256) len.toNat
      rw [hl, countOf_add16] at hcl ⊢
      have := elem_lt (S.vregs 26).toNat 64 0
      have := elem_lt (S.vregs 26).toNat 64 1
      omega
    · -- the last block, then the scalar tail from `n16`
      rename_i hbr'
      rw [hc']
      rw [and_mask16 _ hlen] at hbr hbr'
      refine tail p len c ret hret s hal hb ha hw hP hP' hd (len.toNat - (16 * k + 16) - 1) _
        (len &&& 18446744073709551600#64) _ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (try janus_simp [hsret, hgret, hvh, hth])
      all_goals (try (rw [and_mask16 _ hlen]; omega))
      rw [and_mask16 _ hlen, show len.toNat / 16 * 16 = 16 * k + 16 by omega, countOf_add16]
      have := elem_lt (S.vregs 26).toNat 64 0
      have := elem_lt (S.vregs 26).toNat 64 1
      have hcl := countOf_le s.mem p.toNat (c.toNat % 256) (16 * k + 16)
      rw [countOf_add16] at hcl
      omega
    · -- a further iteration is impossible: this was the last block
      rw [and_mask16 _ hlen] at hbr
      exfalso; apply hbr; omega
  | succ r ih =>
    intro S k hn hpc h0 h1 h2 h3 h4 h5 h23 h24 h29 h26 h29' h30 hsp h28 h18 hm
    have hlen := len.isLt
    janus_eval_nat hsret : sret
    janus_eval_nat hgret : gret
    janus_eval_nat hvh : vhead
    janus_eval_nat hth : thead
    janus_run [h23, h24, h29, elem_ones8, hsret, hgret] until [vhead, thead]
    · rename_i hx; rw [and_mask16 _ hlen] at hx; omega
    · have hc' : (cw c).toNat % 256 = c.toNat % 256 := by rw [cw_toNat, Nat.mod_mod]
      refine ih _ (k + 1) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (try janus_simp [elem_ones8, hsret, hgret, hvh, hth])
      · rw [show 16 * (k + 1) = 16 * k + 16 by omega]
      · exact h23
      · exact h24
      · simpa using h29
      · rw [hc', show 16 * (k + 1) = 16 * k + 16 by omega, countOf_add16]
        omega

set_option maxHeartbeats 8000000 in
/-- **The theorem.** -/
theorem correctness (p len cap c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, len, cap, c]
      (fun s => GuardOK s 0 ∧ StackOK s 88 16 ∧ Ptr s.mem p len.toNat false ∧
        Disjoint p.toNat len.toNat (s.sp.toNat - 88) 104)
      (fun s s' => (s'.regs 0).toNat = countOf s.mem p.toNat (c.toNat % 256) len.toNat) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hP, hP'⟩, hd⟩
  janus_intro hs
  simp only [Disjoint] at hd
  have hlen := len.isLt
  have hn16 := and_mask16_toNat len
  janus_eval_nat hsret : sret
  janus_eval_nat hgret : gret
  janus_eval_nat hvh : vhead
  janus_eval_nat hth : thead
  janus_run [modImmOp_movi0, modImmOp_movi1, hsret, hgret] until [vhead, thead]
  · -- `len = 0`: `cbz x1` returns 0
    rfl
  · -- fewer than 16 bytes: the scalar loop from 0
    refine tail p len c ret hret s hal hb ha hw hP hP' hd (len.toNat - 1) _ 0#64 0#64 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try janus_simp [hsret, hgret, hvh, hth])
    all_goals (try omega)
    all_goals rfl
  · -- the vector loop from block 0
    refine vloop p len c ret hret s hal hb ha hw hP hP' hd (len.toNat / 16 - 1) _ 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try janus_simp [hsret, hgret, hvh, hth])
    all_goals (try omega)
    · congr 1; exact Nat.mod_eq_of_lt (ofElems_lt 8 16 _)
    · rfl
    · simp only [frameMem, hgret]

end Proof
