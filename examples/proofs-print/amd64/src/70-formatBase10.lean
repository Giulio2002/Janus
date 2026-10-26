/-! ## `internal/strconv.formatBase10` -/

/-- The table `internal/strconv.smalls` ("00010203…99", `LEAQ` in `formatBase10`). -/
def SM : Nat := ripTarget P (segAddr P "internal/strconv.formatBase10" + 0x91)

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

theorem smalls_hi (k : Nat) (hk : k < 100) :
    BitVec.ofNat 8 (smallsByte (k * 2)) = Janus.Spec.Print.digit (k / 10) := by
  unfold smallsByte Janus.Spec.Print.digit
  rw [if_pos (by omega)]; congr 1; omega

theorem smalls_lo (k : Nat) (hk : k < 100) :
    BitVec.ofNat 8 (smallsByte (k * 2 + 1)) = Janus.Spec.Print.digit (k % 10) := by
  unfold smallsByte Janus.Spec.Print.digit
  rw [if_neg (by omega)]; congr 1; omega

theorem smallsByte_mod256 (j : Nat) (h : j < 200) : smallsByte j % 256 = smallsByte j := by
  unfold smallsByte; split <;> omega

/-! The magic multiplications of `formatBase10` (at the bit-vector level: `simp` with
`BitVec.toNat_mul` and `BitVec.toNat_ofNat` does not terminate on these products). -/

theorem mul_lsr37 (y : Nat) (h : y < 2 ^ 31) :
    (BitVec.ofNat 64 y * 2748779070#64) >>> 37 = BitVec.ofNat 64 (y / 50) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 2748779070 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show y * 2748779070 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show y / 50 < 2 ^ 64 by omega)]
  exact magic50 y h

/-- `MOVL` (zero-extend the low 32 bits), `SHRQ $1`, `IMULQ $0xa3d70a3e`, `SHRQ $37`: `x / 100`. -/
theorem div100_magic64 (x : Nat) (h : x < 2 ^ 32) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x)) >>> 1 * 2748779070#64) >>> 37 =
      BitVec.ofNat 64 (x / 100) := by
  have e : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x)) >>> 1 = BitVec.ofNat 64 (x / 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  rw [e, mul_lsr37 (x / 2) (by omega)]
  congr 1; omega

theorem mul100_32 (q : Nat) (h : q * 100 < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 q) * 100#32).toNat = q * 100 := by
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- What the rest of `formatBase10` from the final chunk's loop head guarantees: it returns
`i - |decimal lo|` with the digits of `lo` written in front of the bytes already at `[a + i, a + 20)`. -/
def FbTail (s : State) (SP a i lo : Nat) (m0 : Memory) (s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory),
    s' = retState64 s junk [BitVec.ofNat 64 (i - (Janus.Spec.Print.decimal lo).length)] f x yh m ∧
    MemFrame s.mem m [(SP - 8, SP), (SP + 8, SP + 16), (a, a + 20)] ∧
    readBytes m (a + (i - (Janus.Spec.Print.decimal lo).length))
        (20 - (i - (Janus.Spec.Print.decimal lo).length)) =
      Janus.Spec.Print.decimal lo ++ readBytes m0 (a + i) (20 - i)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem formatBase10 (impl : List Amd64.Segment) :
    Summary (P.link impl) (segAddr P "internal/strconv.formatBase10")
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ 8 ≤ (s.regs 4).toNat ∧
        (s.regs 4).toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 4).toNat - 8) 24 true = true ∧
        (s.regs 3).toNat = 20 ∧ (s.regs 1).toNat = 20 ∧ (s.regs 0).toNat + 20 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 0).toNat 20 true = true ∧
        Apart ((s.regs 4).toNat - 8) 24 (s.regs 0).toNat 20 ∧
        s.mem.accessible SM 200 false = true ∧ Apart (s.regs 0).toNat 20 SM 200 ∧
        Apart ((s.regs 4).toNat - 8) 24 SM 200 ∧
        ∀ j, j < 200 → s.mem.readLE (SM + j) 1 = smallsByte j)
      (fun s s' => ∃ (i : Nat) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory),
        s' = retState64 s junk [BitVec.ofNat 64 i] f x yh m ∧ i ≤ 20 ∧
        MemFrame s.mem m [((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16),
          ((s.regs 0).toNat, (s.regs 0).toNat + 20)] ∧
        readBytes m ((s.regs 0).toNat + i) (20 - i) = Janus.Spec.Print.decimal (s.regs 7).toNat) := by
  -- PROOF formatBase10
  intro s hpc ⟨hra, hb, ha, hw, hx3, hx1, hab, hacc, ap1, hsma, ap3, ap4, h_sm⟩
  have hsp : s.regs 4 = BitVec.ofNat 64 (s.regs 4).toNat := by simp
  have hx0 : s.regs 0 = BitVec.ofNat 64 (s.regs 0).toNat := by simp
  have hx7 : s.regs 7 = BitVec.ofNat 64 (s.regs 7).toNat := by simp
  have hx3' : s.regs 3 = 20#64 := by apply BitVec.eq_of_toNat_eq; simp [hx3]
  have hx1' : s.regs 1 = 20#64 := by apply BitVec.eq_of_toNat_eq; simp [hx1]
  have hspl := (s.regs 4).isLt
  have hul := (s.regs 7).isLt
  have hx0l := (s.regs 0).isLt
  generalize (s.regs 4).toNat = SP at *
  generalize (s.regs 0).toNat = a at *
  generalize (s.regs 7).toNat = u at *
  janus_eval_nat h_smv : SM
  -- `smalls`' address as a variable: the code computes it as a literal (`LEAQ`), on which the
  -- address arithmetic would otherwise be evaluated
  obtain ⟨SMv, hSMv⟩ : ∃ v, SM = v := ⟨_, rfl⟩
  have hlit : (BitVec.ofNat 64 SM : BitVec 64) = BitVec.ofNat 64 SMv := by rw [hSMv]
  rw [h_smv] at hlit
  have hSMb : SM ≤ SMv ∧ SMv ≤ SM := by omega
  rw [h_smv] at hSMb
  rw [hSMv] at h_sm hsma ap3 ap4
  clear h_smv hSMv
  have tail : ∀ lo (S : State) (i : Nat), lo < 2 ^ 29 → (Janus.Spec.Print.decimal lo).length ≤ i →
      i ≤ 20 → S.rip = BitVec.ofNat 64 (segAddr P "internal/strconv.formatBase10" + 0x109) →
      S.regs 4 = BitVec.ofNat 64 SP - 8#64 → S.regs 5 = BitVec.ofNat 64 SP - 8#64 →
      S.regs 0 = BitVec.ofNat 64 a → S.regs 3 = BitVec.ofNat 64 i →
      S.regs 1 = 20#64 → S.regs 2 = BitVec.ofNat 64 lo → S.regs 14 = s.regs 14 →
      MemFrame s.mem S.mem [(SP - 8, SP), (SP + 8, SP + 16), (a, a + 20)] →
      S.mem.readLE (SP - 8) 8 = (s.regs 5).toNat →
      S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df → S.mxcsr = s.mxcsr →
      (∀ j, j < 200 → S.mem.readLE (SMv + j) 1 = smallsByte j) →
      ReachesRet (P.link impl) (retAddrOf s) S (FbTail s SP a i lo S.mem) := by
    intro lo
    induction lo using Nat.strongRecOn with
    | _ lo ih =>
    intro S i hlo hlen hi20 hpc' hsp' hbp' h0 h3 h1 h2 hg' hf h_rd1 hx15 hfs hdf hmx h_rdsm
    by_cases h100 : 100 ≤ lo
    · have hl3 : 3 ≤ i := by
        have := Janus.Spec.Print.decimal_append_two h100
        have := Janus.Spec.Print.length_decimal_pos (lo / 100)
        rw [‹Janus.Spec.Print.decimal lo = _›] at hlen; simp at hlen; omega
      have ea2 : (i + (18446744073709551614 + a) % 18446744073709551616) % 18446744073709551616 = a + (i - 2) := by omega
      have ea1 : (i + (18446744073709551615 + a) % 18446744073709551616) % 18446744073709551616 = a + (i - 1) := by omega
      have em : (4294967296 - lo / 100 * 100 % 4294967296 + lo % 4294967296) % 4294967296 = lo % 100 := by omega
      janus64_run [hlit, div100_magic64 lo (by omega), mul100_32 (lo / 100) (by omega), ea2, ea1, em] until [segAddr P "internal/strconv.formatBase10" + 0x109]
      have hlen' := Janus.Spec.Print.decimal_append_two h100
      refine Janus.Amd64.Tactic.ReachesRet.mono (ih (lo / 100) (Nat.div_lt_self (by omega) (by decide)) _ (i - 2)
        (by omega) ?_ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
      · rw [hlen'] at hlen; simp at hlen; omega
      case refine_2 => dsimp only; rfl
      all_goals try kobl64
      all_goals try (intro j hj; janus64_simp; first | done | exact h_rdsm j hj)
      rintro s' ⟨junk, f, x, yh, m, rfl, hfm, hrb⟩
      unfold FbTail
      have hl : (Janus.Spec.Print.decimal lo).length = (Janus.Spec.Print.decimal (lo / 100)).length + 2 := by
        rw [hlen']; simp
      have hi' : i - (Janus.Spec.Print.decimal lo).length = i - 2 - (Janus.Spec.Print.decimal (lo / 100)).length := by
        omega
      refine ⟨junk, f, x, yh, m, by rw [hi'], hfm, ?_⟩
      rw [hi', hrb, hlen', List.append_assoc]
      rw [List.append_cancel_left_eq]
      dsimp only
      rw [show a + (i - 1) = a + (i - 2) + 1 by omega, show 20 - (i - 2) = 20 - i + 2 by omega,
        readBytes_two_writes, show a + (i - 2) + 2 = a + i by omega,
        show (lo % 100 + lo % 100) % 4294967296 = lo % 100 * 2 by omega,
        show (lo % 100 * 2 + 1) % 4294967296 + SMv = SMv + (lo % 100 * 2 + 1) by omega,
        h_sm _ (by omega), smallsByte_mod256 _ (by omega),
        smalls_hi _ (by omega), smalls_lo _ (by omega), Nat.mod_mod_of_dvd _ (by decide)]
    · by_cases h10 : lo < 10
      · have hl : Janus.Spec.Print.decimal lo = [Janus.Spec.Print.digit lo] :=
          Janus.Spec.Print.decimal_lt10 h10
        have hi1 : 1 ≤ i := by rw [hl] at hlen; simpa using hlen
        have ea1 : (i + (18446744073709551615 + a) % 18446744073709551616) % 18446744073709551616 = a + (i - 1) := by omega
        janus64_run [hlit, ea1]
        unfold FbTail
        refine ⟨?_, ?_, ?_, ?_, ?_, ?eq, ?fr, ?_⟩
        case eq =>
          refine eq_retState64 [BitVec.ofNat 64 (i - (Janus.Spec.Print.decimal lo).length)] ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          all_goals first
            | (simp [setRegF, retAddrOf, hsp, hg', hx15, hfs, hdf, hmx, Nat.mod_eq_of_lt hspl]; done)
            | (simp only [setRegF, hl, List.length_cons, List.length_nil, List.getD_cons_zero, reduceIte]; apply BitVec.eq_of_toNat_eq; simp; omega)
            | rfl
        case fr => janus_frame
        rw [hl]
        simp only [List.length_cons, List.length_nil, Nat.zero_add]
        rw [show 20 - (i - 1) = 20 - i + 1 by omega, readBytes_one_write,
          show a + (i - 1) + 1 = a + i by omega,
          show ((lo + lo) % 4294967296 + 1) % 4294967296 + SMv = SMv + (lo * 2 + 1) by omega,
          h_sm _ (by omega), smalls_lo _ (by omega), Nat.mod_eq_of_lt h10]
      · have hl : Janus.Spec.Print.decimal lo =
            [Janus.Spec.Print.digit (lo / 10), Janus.Spec.Print.digit (lo % 10)] := by
          rw [Janus.Spec.Print.decimal_ge10 (by omega), Janus.Spec.Print.decimal_lt10 (by omega)]; rfl
        have hi2 : 2 ≤ i := by rw [hl] at hlen; simpa using hlen
        have ea1 : (i + (18446744073709551615 + a) % 18446744073709551616) % 18446744073709551616 = a + (i - 1) := by omega
        have ea2 : (i + (18446744073709551614 + a) % 18446744073709551616) % 18446744073709551616 = a + (i - 2) := by omega
        janus64_run [hlit, ea1, ea2]
        unfold FbTail
        refine ⟨?_, ?_, ?_, ?_, ?_, ?eq, ?fr, ?_⟩
        case eq =>
          refine eq_retState64 [BitVec.ofNat 64 (i - (Janus.Spec.Print.decimal lo).length)] ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          all_goals first
            | (simp [setRegF, retAddrOf, hsp, hg', hx15, hfs, hdf, hmx, Nat.mod_eq_of_lt hspl]; done)
            | (simp only [setRegF, hl, List.length_cons, List.length_nil, List.getD_cons_zero, reduceIte]; apply BitVec.eq_of_toNat_eq; simp; omega)
            | rfl
        case fr => janus_frame
        rw [hl]
        simp only [List.length_cons, List.length_nil, Nat.zero_add]
        rw [show i - (1 + 1) = i - 1 - 1 by omega,
          show a + (i - 1) = a + (i - 1 - 1) + 1 by omega,
          show 20 - (i - 1 - 1) = 20 - i + 2 by omega, readBytes_two_writes',
          show a + (i - 1 - 1) + 2 = a + i by omega,
          show ((lo + lo) % 4294967296 + 1) % 4294967296 + SMv = SMv + (lo * 2 + 1) by omega,
          show (lo % 4294967296 + lo % 4294967296) % 4294967296 + SMv = SMv + lo * 2 by omega,
          h_sm _ (by omega), h_sm _ (by omega), smalls_hi _ (by omega), smalls_lo _ (by omega)]
  sorry
