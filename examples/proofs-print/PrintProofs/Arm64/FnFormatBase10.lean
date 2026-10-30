import PrintProofs.Arm64.FnHead

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

namespace PrintFn

/-! ## `internal/strconv.formatBase10` and `printuint(v)` -/

/-- The table `internal/strconv.smalls` ("00010203…99", `ADRP`+`ADD` in `formatBase10`). -/
def SM : Nat := adrpLdTarget (segAddr P "internal/strconv.formatBase10" + 168)
  (segWord P "internal/strconv.formatBase10" 42) (segWord P "internal/strconv.formatBase10" 43) 0

/-- Byte `j` of `smalls`: the two decimal digits of every number below 100, in order. -/
def smallsByte (j : Nat) : Nat := if j % 2 = 0 then 48 + j / 20 else 48 + j / 2 % 10

theorem smalls_data : ∀ j, j < 200 → dataRead P (SM + j) 1 = some (smallsByte j) := by
  janus_eval_nat h : SM
  rw [h]
  have hall : (List.range 200).all (fun j => dataRead P (SM + j) 1 == some (smallsByte j)) = true := by
    rw [h]; decide +kernel
  intro j hj
  have := List.all_eq_true.mp hall j (List.mem_range.mpr hj)
  rw [h] at this
  simpa using this

/-! The bitfield moves of `formatBase10` (`UBFX #1, #31`, `LSR #37`, `LSR #29`, `UBFIZ #1, #31`). -/
theorem ubfx1_31 (x : BitVec 64) :
    x.rotateRight 1 &&& 9223372039002259455#64 &&& 2147483647#64 = BitVec.ofNat 64 (x.toNat / 2 % 2 ^ 31) :=
  ubfm_low x 1 31 _ _ (by decide) (by decide) (by decide)
theorem lsr37 (x : BitVec 64) :
    x.rotateRight 37 &&& 18446744073709551615#64 &&& 134217727#64 = x >>> 37 := by
  rw [ubfm_low x 37 27 _ _ (by decide) (by decide) (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem magic100' (x : Nat) (h : x < 2 ^ 32) :
    x / 2 % 2147483648 * 2748779070 % 18446744073709551616 / 137438953472 % 134217728 = x / 100 := by
  rw [Nat.mod_eq_of_lt (show x / 2 % 2147483648 * 2748779070 < 18446744073709551616 by omega)]
  exact magic100 x h

theorem magic100s (x : Nat) (h : x < 2 ^ 32) :
    x / 2 % 2147483648 * 2748779070 / 137438953472 = x / 100 := by
  rw [Nat.mod_eq_of_lt (show x / 2 < 2147483648 by omega), magic50 (x / 2) (by omega)]
  omega

/-- `lo % 100` as `MSUB W` computes it (`lo - (lo / 100) * 100`, 32 bits), doubled (`UBFIZ #1`). -/
theorem mod100_w (x : Nat) (h : x < 2 ^ 32) :
    (4294967296 - x / 100 * 100 % 4294967296 + x) % 4294967296 % 2147483648 * 2 % 4294967296 =
      x % 100 * 2 := by
  omega

theorem mod100_w' (x : Nat) (h : x < 2 ^ 32) :
    (4294967296 - x / 100 * 100 % 4294967296 + x) % 4294967296 = x % 100 := by
  omega

theorem mod100_idx (x : Nat) : x % 100 % 2147483648 * 2 % 4294967296 = x % 100 * 2 := by omega

/-- `MUL` by the magic constant and `LSR #37` at the bit-vector level (rewritten before any
`toNat` of the product: `simp` with `BitVec.toNat_mul` and `BitVec.toNat_ofNat` does not terminate
on this product). -/
theorem mul_lsr37 (y : Nat) (h : y < 2 ^ 31) :
    (BitVec.ofNat 64 y * 2748779070#64) >>> 37 = BitVec.ofNat 64 (y / 50) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 2748779070 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show y * 2748779070 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show y / 50 < 2 ^ 64 by omega)]
  exact magic50 y h

theorem div2_div50 (x : Nat) (h : x < 2 ^ 32) : x / 2 % 2147483648 / 50 = x / 100 := by omega

theorem smalls_hi (k : Nat) (hk : k < 100) :
    BitVec.ofNat 8 (smallsByte (k * 2)) = Janus.Spec.Print.digit (k / 10) := by
  unfold smallsByte Janus.Spec.Print.digit
  rw [if_pos (by omega)]; congr 1; omega

theorem smalls_lo (k : Nat) (hk : k < 100) :
    BitVec.ofNat 8 (smallsByte (k * 2 + 1)) = Janus.Spec.Print.digit (k % 10) := by
  unfold smallsByte Janus.Spec.Print.digit
  rw [if_neg (by omega)]; congr 1; omega

theorem smallsByte_mod64 (j : Nat) (h : j < 200) : smallsByte j % 18446744073709551616 = smallsByte j := by
  unfold smallsByte; split <;> omega

theorem lo_idx (x : Nat) (h : x < 2 ^ 31) : x % 2147483648 * 2 % 4294967296 = x * 2 := by omega

theorem lsr29 (x : BitVec 64) :
    x.rotateRight 29 &&& 18446744073709551615#64 &&& 34359738367#64 = x >>> 29 := by
  rw [ubfm_low x 29 35 _ _ (by decide) (by decide) (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem lsr1 (x : BitVec 64) :
    x.rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 = x >>> 1 := by
  rw [ubfm_low x 1 63 _ _ (by decide) (by decide) (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem lsr28 (x : BitVec 64) :
    x.rotateRight 28 &&& 18446744073709551615#64 &&& 68719476735#64 = x >>> 28 := by
  rw [ubfm_low x 28 36 _ _ (by decide) (by decide) (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- `LSR #1`, `UMULH`, `LSR #28` and the `MSUB` after it: `U / 10^9` and `U % 10^9`. -/
theorem umulh_1e9 (U : Nat) (hU : U < 2 ^ 64) :
    BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 U >>> 1) * 9903520314283042200#128) >>> 28 =
      BitVec.ofNat 64 (U / 1000000000) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, umulh_lit _ _ (by decide), BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hU, Nat.mod_eq_of_lt (show U / 1000000000 < 2 ^ 64 by omega),
    Nat.div_div_eq_div_mul, show (2 : Nat) ^ 64 * 2 ^ 28 = 2 ^ 92 by decide,
    show (2 : Nat) ^ 1 = 2 by rfl, magic5e8 _ (by omega)]
  omega
theorem msub_1e9 (U : Nat) :
    BitVec.ofNat 64 U - 1000000000#64 * BitVec.ofNat 64 (U / 1000000000) = BitVec.ofNat 64 (U % 1000000000) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

theorem ofNat8_smalls_mod (j : Nat) (h : j < 200) :
    BitVec.ofNat 8 (smallsByte j % 18446744073709551616) = BitVec.ofNat 8 (smallsByte j) := by
  rw [smallsByte_mod64 j h]

theorem twice_mod32' (x : Nat) (h : x < 100) : (x + (x + 1)) % 4294967296 = x * 2 + 1 := by omega

theorem twice_mod32 (x : Nat) (h : x < 100) : (x + x + 1) % 4294967296 = x * 2 + 1 := by omega

theorem and_sshr_20 (x : Nat) (hx : x < 20) :
    BitVec.ofNat 64 x &&& (BitVec.ofNat 64 x - 20#64).sshiftRight 63 = BitVec.ofNat 64 x :=
  and_sshr_lt_bv x 20 hx (by decide)

theorem ubfiz1_31 (x : BitVec 64) : (x.rotateRight 63).toNat &&& 4294967294 = x.toNat % 2 ^ 31 * 2 := by
  rw [natAnd_toNat _ _ (by decide), and2_of_and3,
    ubfm_shl x 63 31 1 _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  simp only [BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- What the rest of `formatBase10` from the final chunk's loop head guarantees: it returns
`i - |decimal lo|` with the digits of `lo` written in front of the bytes already at `[a + i, a + 20)`. -/
def FbTail (s : State) (SP a i lo : Nat) (m0 : Memory) (s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
    s' = retStateX s junk [BitVec.ofNat 64 (i - (Janus.Spec.Print.decimal lo).length)] f v m ex ep ∧
    MemFrame s.mem m [(SP - 24, SP - 8), (SP + 8, SP + 16), (a, a + 20)] ∧
    readBytes m (a + (i - (Janus.Spec.Print.decimal lo).length))
        (20 - (i - (Janus.Spec.Print.decimal lo).length)) =
      Janus.Spec.Print.decimal lo ++ readBytes m0 (a + i) (20 - i)

set_option hygiene false in
/-- The nine digit bytes of a chunk (`chunk_bytes`) against `digits9`. -/
macro "chunk_digits" : tactic => `(tactic| (
  rw [show a + (i - 2) = a + (i - 9) + 7 by omega, show a + (i - 1) = a + (i - 9) + 8 by omega,
    show a + (i - 4) = a + (i - 9) + 5 by omega, show a + (i - 3) = a + (i - 9) + 6 by omega,
    show a + (i - 6) = a + (i - 9) + 3 by omega, show a + (i - 5) = a + (i - 9) + 4 by omega,
    show a + (i - 8) = a + (i - 9) + 1 by omega, show a + (i - 7) = a + (i - 9) + 2 by omega,
    show 20 - (i - 9) = 20 - i + 9 by omega, chunk_bytes, show a + (i - 9) + 9 = a + i by omega]
  rw [List.append_cancel_right_eq]
  simp (disch := omega) only [ofNat8_smalls_mod, twice_mod32', smalls_hi, smalls_lo]
  simp only [digits9, List.range_succ, List.range_zero, List.map, List.reverse_nil, List.reverse_cons,
    List.nil_append, List.cons_append, Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul, Nat.pow_zero,
    Nat.div_one, List.cons.injEq, and_true]
  repeat' apply And.intro
  all_goals first | exact True.intro | exact congrArg Janus.Spec.Print.digit (by omega)))

set_option hygiene false in
macro "fin_eq" : tactic => `(tactic| first | (with_reducible rfl) | rfl | (simp [setReg, callRegs, hg', h18, h_rd2, hsp', hsp, hdz, htp, hfc, hfs]; done))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem formatBase10 (impl : List Segment) :
    Summary (P.link impl) (segAddr P "internal/strconv.formatBase10")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ StackOK s 24 16 ∧ GuardOK s 0 ∧
        (s.regs 1).toNat = 20 ∧ (s.regs 2).toNat = 20 ∧ (s.regs 0).toNat + 20 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 0).toNat 20 true = true ∧
        Apart (s.sp.toNat - 24) 40 (s.regs 0).toNat 20 ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.regs 0).toNat 20 ∧
        s.mem.accessible SM 200 false = true ∧ Apart (s.regs 0).toNat 20 SM 200 ∧
        Apart (s.sp.toNat - 24) 40 SM 200 ∧
        ∀ j, j < 200 → s.mem.readLE (SM + j) 1 = smallsByte j)
      (fun s s' => ∃ (i : Nat) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
        s' = retStateX s junk [BitVec.ofNat 64 i] f v m ex ep ∧ i ≤ 20 ∧
        MemFrame s.mem m [(s.sp.toNat - 24, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16),
          ((s.regs 0).toNat, (s.regs 0).toNat + 20)] ∧
        readBytes m ((s.regs 0).toNat + i) (20 - i) = Janus.Spec.Print.decimal (s.regs 3).toNat) := by
  -- PROOF formatBase10
  intro s hpc ⟨h30a, h30b, ⟨hal, hb, ha, hw⟩, ⟨hg1, hg2, hg3⟩, hx1, hx2, hab, hacc, ap1, ap2, hsma, ap3, ap4, h_sm⟩
  have hsp : s.sp = BitVec.ofNat 64 s.sp.toNat := by simp
  have hx0 : s.regs 0 = BitVec.ofNat 64 (s.regs 0).toNat := by simp
  have hx3 : s.regs 3 = BitVec.ofNat 64 (s.regs 3).toNat := by simp
  have hx1' : s.regs 1 = 20#64 := by apply BitVec.eq_of_toNat_eq; simp [hx1]
  have hx2' : s.regs 2 = 20#64 := by apply BitVec.eq_of_toNat_eq; simp [hx2]
  have hspl := s.sp.isLt
  have hul := (s.regs 3).isLt
  have hx0l := (s.regs 0).isLt
  generalize s.sp.toNat = SP at *
  generalize (s.regs 0).toNat = a at *
  generalize (s.regs 3).toNat = u at *
  janus_eval_nat h_smv : SM
  rw [h_smv] at h_sm hsma ap3 ap4
  have hdat : ∀ j, j < 200 → s.mem.readLE (823223 + j) 1 = smallsByte j := h_sm
  -- the final chunk (`lo < 2^29`), two digits at a time, ending at `i`
  have tail : ∀ lo (S : State) (i : Nat), lo < 2 ^ 29 → (Janus.Spec.Print.decimal lo).length ≤ i →
      i ≤ 20 → S.pc = BitVec.ofNat 64 (segAddr P "internal/strconv.formatBase10" + 0x118) →
      S.sp = BitVec.ofNat 64 SP - 16#64 → S.regs 0 = BitVec.ofNat 64 a → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 2 = 20#64 → S.regs 3 = BitVec.ofNat 64 lo → S.regs 28 = s.regs 28 →
      S.regs 18 = s.regs 18 →
      MemFrame s.mem S.mem [(SP - 24, SP - 8), (SP + 8, SP + 16), (a, a + 20)] →
      S.mem.readLE (SP - 16) 8 = (s.regs 30).toNat → S.mem.readLE (SP - 24) 8 = (s.regs 29).toNat →
      S.dczid = s.dczid → S.tpidr = s.tpidr → S.fpcr = s.fpcr → S.fpsr = s.fpsr →
      S.mem.accessible 823223 200 false = true →
      (∀ j, j < 200 → S.mem.readLE (823223 + j) 1 = smallsByte j) →
      ReachesRet (P.link impl) (s.regs regLR) S (FbTail s SP a i lo S.mem) := by
    intro lo
    induction lo using Nat.strongRecOn with
    | _ lo ih =>
    intro S i hlo hlen hi20 hpc' hsp' h0 h1 h2 h3 hg' h18 hf h_rd1 h_rd2 hdz htp hfc hfs hsmS h_rdsm
    have hsep3 : a + 20 ≤ 823223 ∨ 823223 + 200 ≤ a := ap3
    by_cases h100 : 100 ≤ lo
    · have hl3 : 3 ≤ i := by
        have := Janus.Spec.Print.decimal_append_two h100
        have := Janus.Spec.Print.length_decimal_pos (lo / 100)
        rw [‹Janus.Spec.Print.decimal lo = _›] at hlen; simp at hlen; omega
      janus_run [ubfx1_31, lsr37, mul_lsr37, div2_div50, ubfiz1_31, BitVec.toNat_setWidth,
        BitVec.toNat_mul, mod100_w, mod100_w', mod100_idx, twice_mod32]
        until [segAddr P "internal/strconv.formatBase10" + 0x118]
      have hlen' := Janus.Spec.Print.decimal_append_two h100
      refine ReachesRet.mono' (ih (lo / 100) (Nat.div_lt_self (by omega) (by decide)) _ (i - 2) (by omega) ?_ (by omega) ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
      · rw [hlen'] at hlen; simp at hlen; omega
      all_goals try kobl
      all_goals try (intro j hj; janus_simp; first | done | exact h_rdsm j hj)
      all_goals try (dsimp only; simp only [setReg_apply]; apply BitVec.eq_of_toNat_eq; simp; omega)
      rintro s' ⟨junk, f, v, m, ex, ep, rfl, hfm, hrb⟩
      unfold FbTail
      have hl : (Janus.Spec.Print.decimal lo).length = (Janus.Spec.Print.decimal (lo / 100)).length + 2 := by
        rw [hlen']; simp
      have hi' : i - (Janus.Spec.Print.decimal lo).length = i - 2 - (Janus.Spec.Print.decimal (lo / 100)).length := by
        omega
      refine ⟨junk, f, v, m, ex, ep, by rw [hi'], hfm, ?_⟩
      rw [hi', hrb, hlen', List.append_assoc]
      rw [List.append_cancel_left_eq]
      dsimp only
      rw [show a + (i - 1) = a + (i - 2) + 1 by omega, show 20 - (i - 2) = 20 - i + 2 by omega,
        readBytes_two_writes, show a + (i - 2) + 2 = a + i by omega,
        smallsByte_mod64 _ (by omega), smallsByte_mod64 _ (by omega),
        smalls_hi _ (by omega), smalls_lo _ (by omega), Nat.mod_mod_of_dvd _ (by decide)]
    · by_cases h10 : lo < 10
      · have hl : Janus.Spec.Print.decimal lo = [Janus.Spec.Print.digit lo] :=
          Janus.Spec.Print.decimal_lt10 h10
        have hi1 : 1 ≤ i := by rw [hl] at hlen; simpa using hlen
        janus_run [ubfx1_31, lsr37, mul_lsr37, div2_div50, ubfiz1_31, BitVec.toNat_setWidth,
          BitVec.toNat_mul, mod100_w, mod100_w', mod100_idx, twice_mod32, lo_idx]
        unfold FbTail
        refine ⟨_, _, _, _, _, _, by
          refine eq_retState_res (r := BitVec.ofNat 64 (i - (Janus.Spec.Print.decimal lo).length))
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
          first | fin_eq | (simp only [setReg_apply, hl, List.length_cons, List.length_nil]; apply BitVec.eq_of_toNat_eq; simp; omega),
          by janus_frame, ?_⟩
        rw [hl]
        simp only [List.length_cons, List.length_nil, Nat.zero_add]
        rw [show 20 - (i - 1) = 20 - i + 1 by omega, readBytes_one_write,
          show a + (i - 1) + 1 = a + i by omega, show (lo + (lo + 1)) % 4294967296 = lo * 2 + 1 by omega,
          smallsByte_mod64 _ (by omega), smalls_lo _ (by omega), Nat.mod_eq_of_lt h10]
      · have hl : Janus.Spec.Print.decimal lo =
            [Janus.Spec.Print.digit (lo / 10), Janus.Spec.Print.digit (lo % 10)] := by
          rw [Janus.Spec.Print.decimal_ge10 (by omega), Janus.Spec.Print.decimal_lt10 (by omega)]; rfl
        have hi2 : 2 ≤ i := by rw [hl] at hlen; simpa using hlen
        janus_run [ubfx1_31, lsr37, mul_lsr37, div2_div50, ubfiz1_31, BitVec.toNat_setWidth,
          BitVec.toNat_mul, mod100_w, mod100_w', mod100_idx, twice_mod32, lo_idx]
        unfold FbTail
        refine ⟨_, _, _, _, _, _, by
          refine eq_retState_res (r := BitVec.ofNat 64 (i - (Janus.Spec.Print.decimal lo).length))
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
          first | fin_eq | (simp only [setReg_apply, hl, List.length_cons, List.length_nil]; apply BitVec.eq_of_toNat_eq; simp; omega),
          by janus_frame, ?_⟩
        rw [hl]
        simp only [List.length_cons, List.length_nil, Nat.zero_add]
        rw [show i - (1 + 1) = i - 1 - 1 by omega, show a + (i - 1) = a + (i - 1 - 1) + 1 by omega,
          show 20 - (i - 1 - 1) = 20 - i + 2 by omega, readBytes_two_writes',
          show a + (i - 1 - 1) + 2 = a + i by omega, show (lo + (lo + 1)) % 4294967296 = lo * 2 + 1 by omega,
          smallsByte_mod64 _ (by omega), smallsByte_mod64 _ (by omega), smalls_hi _ (by omega),
          smalls_lo _ (by omega)]
  -- the chunks of nine digits (`u >>> 29 ≠ 0`), then the final chunk
  have outer : ∀ U (S : State) (i : Nat), (Janus.Spec.Print.decimal U).length ≤ i →
      i ≤ 20 → S.pc = BitVec.ofNat 64 (segAddr P "internal/strconv.formatBase10" + 0x28) →
      S.sp = BitVec.ofNat 64 SP - 16#64 → S.regs 0 = BitVec.ofNat 64 a → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 2 = 20#64 → S.regs 3 = BitVec.ofNat 64 U → S.regs 28 = s.regs 28 →
      S.regs 18 = s.regs 18 →
      MemFrame s.mem S.mem [(SP - 24, SP - 8), (SP + 8, SP + 16), (a, a + 20)] →
      S.mem.readLE (SP - 16) 8 = (s.regs 30).toNat → S.mem.readLE (SP - 24) 8 = (s.regs 29).toNat →
      S.dczid = s.dczid → S.tpidr = s.tpidr → S.fpcr = s.fpcr → S.fpsr = s.fpsr →
      S.mem.accessible 823223 200 false = true →
      (∀ j, j < 200 → S.mem.readLE (823223 + j) 1 = smallsByte j) → U < 2 ^ 64 →
      ReachesRet (P.link impl) (s.regs regLR) S (FbTail s SP a i U S.mem) := by
    intro U
    induction U using Nat.strongRecOn with
    | _ U ih =>
    intro S i hlen hi20 hpc' hsp' h0 h1 h2 h3 hg' h18 hf h_rd1 h_rd2 hdz htp hfc hfs hsmS h_rdsm hU
    by_cases h29 : U < 2 ^ 29
    · janus_run [lsr29, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] until
        [segAddr P "internal/strconv.formatBase10" + 0x118]
      refine tail U _ i h29 hlen hi20 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | (with_reducible rfl) | (with_reducible assumption) | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; with_reducible assumption) | rfl | (simp only [setReg_apply]; assumption)
    · have hi9 : 9 ≤ i := by
        have := length_decimal_ge 8 U (by omega)
        omega
      janus_run [lsr29, lsr1, lsr28, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, umulh_1e9,
        msub_1e9, ubfx1_31, lsr37, mul_lsr37, div2_div50, ubfiz1_31, BitVec.toNat_setWidth,
        BitVec.toNat_mul, mod100_w, mod100_w', mod100_idx, twice_mod32, lo_idx]
        until [segAddr P "internal/strconv.formatBase10" + 0x28]
      -- back at the loop head: the next chunk
      all_goals first
        | (refine ReachesRet.mono' (ih (U / 1000000000) (by omega) _ (i - 9) ?_ (by omega) ?_ ?_ ?_ ?_ ?_ ?_
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega)) ?_
           · have hc := decimal_chunk U (by omega)
             rw [hc] at hlen; simp [digits9] at hlen; omega
           all_goals try kobl
           all_goals try (intro j hj; janus_simp; first | done | exact h_rdsm j hj)
           all_goals try (dsimp only; simp only [setReg_apply]; apply BitVec.eq_of_toNat_eq; simp; omega)
           rintro s' ⟨junk, f, v, m, ex, ep, rfl, hfm, hrb⟩
           unfold FbTail
           have hc := decimal_chunk U (by omega)
           have hl : (Janus.Spec.Print.decimal U).length =
               (Janus.Spec.Print.decimal (U / 1000000000)).length + 9 := by rw [hc]; simp [digits9]
           have hi' : i - (Janus.Spec.Print.decimal U).length =
               i - 9 - (Janus.Spec.Print.decimal (U / 1000000000)).length := by omega
           refine ⟨junk, f, v, m, ex, ep, by rw [hi'], hfm, ?_⟩
           rw [hi', hrb, hc, List.append_assoc]
           rw [List.append_cancel_left_eq]
           dsimp only
           chunk_digits)
        | skip
      -- the last chunk (`U < 10^9`): return
      all_goals
        unfold FbTail
        have hc := decimal_nine U (by omega) (by omega)
        refine ⟨_, _, _, _, _, _, by
          refine eq_retState_res (r := BitVec.ofNat 64 (i - (Janus.Spec.Print.decimal U).length))
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
          first | fin_eq | (simp only [setReg_apply, hc, digits9, List.length_map, List.length_reverse, List.length_range]; apply BitVec.eq_of_toNat_eq; simp; omega),
          by janus_frame, ?_⟩
        rw [hc]
        simp only [digits9, List.length_map, List.length_reverse, List.length_range]
        rw [show U % 1000000000 = U by omega] at *
        chunk_digits
  -- the entry: the prologue, then the loop head with `i = 20`
  have hsep4 : SP - 24 + 40 ≤ 823223 ∨ 823223 + 200 ≤ SP - 24 := ap4
  janus_run until [segAddr P "internal/strconv.formatBase10" + 0x28]
  refine ReachesRet.mono' (outer u _ 20 (length_decimal_le 19 u (by omega)) (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hul) ?_
  all_goals try kobl
  all_goals try (intro j hj; janus_simp; first | done | exact h_sm j hj)
  all_goals try (dsimp only; simp only [setReg_apply]; apply BitVec.eq_of_toNat_eq; simp; omega)
  rintro s' ⟨junk, f, v, m, ex, ep, rfl, hfm, hrb⟩
  have hl20 := length_decimal_le 19 u (by omega)
  refine ⟨20 - (Janus.Spec.Print.decimal u).length, junk, f, v, m, ex, ep, ?_, by omega, ?_, ?_⟩
  · simp only [hsp, hx0, hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspl]
  · simpa [hsp, hx0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspl, Nat.mod_eq_of_lt hx0l] using hfm
  · rw [show 20 - (20 - (Janus.Spec.Print.decimal u).length) = (Janus.Spec.Print.decimal u).length by omega] at hrb ⊢
    simp only [readBytes_zero, Nat.sub_self, List.append_nil] at hrb
    simpa [hx0, hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx0l, Nat.mod_eq_of_lt hul] using hrb

/-! ## `printuint(v)` -/

end PrintFn
