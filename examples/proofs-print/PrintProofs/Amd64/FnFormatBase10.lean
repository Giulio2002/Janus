import PrintProofs.Amd64.FnFmtInner

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

namespace PrintFn

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
      (fun s s' => ∃ (i : Nat) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256) (kr : Nat → W64),
        s' = retState64 s junk [BitVec.ofNat 64 i] f x yh m zh kr ∧ i ≤ 20 ∧
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
  have h_sm' : ∀ j, j < 200 → s.mem.readLE (j + SMv) 1 = smallsByte j := fun j hj => by
    rw [Nat.add_comm]; exact h_sm j hj
  have tail : ∀ lo (S : State) (i : Nat), lo < 2 ^ 29 → (Janus.Spec.Print.decimal lo).length ≤ i →
      i ≤ 20 → S.rip = BitVec.ofNat 64 (segAddr P "internal/strconv.formatBase10" + 0x109) →
      S.regs 4 = BitVec.ofNat 64 SP - 8#64 → S.regs 5 = BitVec.ofNat 64 SP - 8#64 →
      S.regs 0 = BitVec.ofNat 64 a → S.regs 3 = BitVec.ofNat 64 i →
      S.regs 1 = 20#64 → S.regs 2 = BitVec.ofNat 64 lo → S.regs 14 = s.regs 14 →
      MemFrame s.mem S.mem [(SP - 8, SP), (SP + 8, SP + 16), (a, a + 20)] →
      S.mem.readLE (SP - 8) 8 = (s.regs 5).toNat →
      S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df → S.mxcsr = s.mxcsr → S.x87 = s.x87 → S.fpucw = s.fpucw →
      (∀ j, j < 200 → S.mem.readLE (SMv + j) 1 = smallsByte j) →
      ReachesRet (P.link impl) (retAddrOf s) S (FbTail s SP a i lo S.mem) := by
    intro lo
    induction lo using Nat.strongRecOn with
    | _ lo ih =>
    intro S i hlo hlen hi20 hpc' hsp' hbp' h0 h3 h1 h2 hg' hf h_rd1 hx15 hfs hdf hmx hx87 hfw h_rdsm
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
        (by omega) ?_ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
      · rw [hlen'] at hlen; simp at hlen; omega
      case refine_2 => dsimp only; rfl
      all_goals try kobl64
      all_goals try (intro j hj; janus64_simp; first | done | exact h_rdsm j hj)
      rintro s' ⟨junk, f, x, yh, m, zh, kr, rfl, hfm, hrb⟩
      unfold FbTail
      have hl : (Janus.Spec.Print.decimal lo).length = (Janus.Spec.Print.decimal (lo / 100)).length + 2 := by
        rw [hlen']; simp
      have hi' : i - (Janus.Spec.Print.decimal lo).length = i - 2 - (Janus.Spec.Print.decimal (lo / 100)).length := by
        omega
      refine ⟨junk, f, x, yh, m, zh, kr, by rw [hi'], hfm, ?_⟩
      rw [hi', hrb, hlen', List.append_assoc]
      rw [List.append_cancel_left_eq]
      dsimp only
      rw [show a + (i - 1) = a + (i - 2) + 1 by omega, show 20 - (i - 2) = 20 - i + 2 by omega,
        readBytes_two_writes, show a + (i - 2) + 2 = a + i by omega,
        show (lo % 100 + lo % 100) % 4294967296 = lo % 100 * 2 by omega]
      congr 1
      simp only [List.cons.injEq, and_true]
      have e1 := bhi (lo % 100 * 2) (lo % 100) (by omega) rfl
      have e2 := blo ((lo % 100 * 2 + 1) % 4294967296) (lo % 100) (by omega) (by omega)
      rw [Nat.mod_mod_of_dvd _ (by decide : 10 ∣ 100)] at e2
      exact ⟨e1, e2⟩
    · by_cases h10 : lo < 10
      · have hl : Janus.Spec.Print.decimal lo = [Janus.Spec.Print.digit lo] :=
          Janus.Spec.Print.decimal_lt10 h10
        have hi1 : 1 ≤ i := by rw [hl] at hlen; simpa using hlen
        have ea1 : (i + (18446744073709551615 + a) % 18446744073709551616) % 18446744073709551616 = a + (i - 1) := by omega
        janus64_run [hlit, ea1]
        unfold FbTail
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?eq, ?fr, ?_⟩
        case eq =>
          refine eq_retState64 [BitVec.ofNat 64 (i - (Janus.Spec.Print.decimal lo).length)] ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          all_goals first
            | (simp [setRegF, retAddrOf, hsp, hg', hx15, hfs, hdf, hmx, hx87, hfw, Nat.mod_eq_of_lt hspl]; done)
            | (simp only [setRegF, hl, List.length_cons, List.length_nil, List.getD_cons_zero, reduceIte]; apply BitVec.eq_of_toNat_eq; simp; omega)
            | rfl
        case fr => janus_frame
        rw [hl]
        simp only [List.length_cons, List.length_nil, Nat.zero_add]
        rw [show 20 - (i - 1) = 20 - i + 1 by omega, readBytes_one_write,
          show a + (i - 1) + 1 = a + i by omega]
        congr 1
        simp only [List.cons.injEq, and_true]
        have e := blo (((lo + lo) % 4294967296 + 1) % 4294967296) lo (by omega) (by omega)
        rwa [Nat.mod_eq_of_lt h10] at e
      · have hl : Janus.Spec.Print.decimal lo =
            [Janus.Spec.Print.digit (lo / 10), Janus.Spec.Print.digit (lo % 10)] := by
          rw [Janus.Spec.Print.decimal_ge10 (by omega), Janus.Spec.Print.decimal_lt10 (by omega)]; rfl
        have hi2 : 2 ≤ i := by rw [hl] at hlen; simpa using hlen
        have ea1 : (i + (18446744073709551615 + a) % 18446744073709551616) % 18446744073709551616 = a + (i - 1) := by omega
        have ea2 : (i + (18446744073709551614 + a) % 18446744073709551616) % 18446744073709551616 = a + (i - 2) := by omega
        janus64_run [hlit, ea1, ea2]
        unfold FbTail
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?eq, ?fr, ?_⟩
        case eq =>
          refine eq_retState64 [BitVec.ofNat 64 (i - (Janus.Spec.Print.decimal lo).length)] ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          all_goals first
            | (simp [setRegF, retAddrOf, hsp, hg', hx15, hfs, hdf, hmx, hx87, hfw, Nat.mod_eq_of_lt hspl]; done)
            | (simp only [setRegF, hl, List.length_cons, List.length_nil, List.getD_cons_zero, reduceIte]; apply BitVec.eq_of_toNat_eq; simp; omega)
            | rfl
        case fr => janus_frame
        rw [hl]
        simp only [List.length_cons, List.length_nil, Nat.zero_add]
        rw [show i - (1 + 1) = i - 1 - 1 by omega,
          show a + (i - 1) = a + (i - 1 - 1) + 1 by omega,
          show 20 - (i - 1 - 1) = 20 - i + 2 by omega, readBytes_two_writes',
          show a + (i - 1 - 1) + 2 = a + i by omega]
        congr 1
        simp only [List.cons.injEq, and_true]
        exact ⟨bhi ((lo % 4294967296 + lo % 4294967296) % 4294967296) lo (by omega) (by omega),
          blo (((lo + lo) % 4294967296 + 1) % 4294967296) lo (by omega) (by omega)⟩
  have outer : ∀ U (S : State) (i : Nat), (Janus.Spec.Print.decimal U).length ≤ i →
      i ≤ 20 → S.rip = BitVec.ofNat 64 (segAddr P "internal/strconv.formatBase10" + 0x17) →
      S.regs 4 = BitVec.ofNat 64 SP - 8#64 → S.regs 5 = BitVec.ofNat 64 SP - 8#64 →
      S.regs 0 = BitVec.ofNat 64 a → S.regs 3 = BitVec.ofNat 64 i →
      S.regs 1 = 20#64 → S.regs 7 = BitVec.ofNat 64 U → S.regs 14 = s.regs 14 →
      MemFrame s.mem S.mem [(SP - 8, SP), (SP + 8, SP + 16), (a, a + 20)] →
      S.mem.readLE (SP - 8) 8 = (s.regs 5).toNat →
      S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df → S.mxcsr = s.mxcsr → S.x87 = s.x87 → S.fpucw = s.fpucw →
      (∀ j, j < 200 → S.mem.readLE (SMv + j) 1 = smallsByte j) → U < 2 ^ 64 →
      ReachesRet (P.link impl) (retAddrOf s) S (FbTail s SP a i U S.mem) := by
    intro U
    induction U using Nat.strongRecOn with
    | _ U ih =>
    intro S i hlen hi20 hpc' hsp' hbp' h0 h3 h1 h7 hg' hf h_rd1 hx15 hfs hdf hmx hx87 hfw h_rdsm hU
    by_cases h29 : U < 2 ^ 29
    · have hs : BitVec.ofNat 64 U >>> 29 = 0#64 := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
      janus64_run [hs] until [segAddr P "internal/strconv.formatBase10" + 0x109]
      refine tail U _ i h29 hlen hi20 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | rfl | (with_reducible assumption) | (simp only [setRegF_apply]; assumption)
    · have hi9 : 9 ≤ i := by
        have := length_decimal_ge 8 U (by omega)
        omega
      have hs : (BitVec.ofNat 64 U >>> 29 = 0#64) = False := by
        simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this; omega
      obtain ⟨y, hyv⟩ : ∃ y, U % 1000000000 = y := ⟨_, rfl⟩
      have hyl : y < 1000000000 := by omega
      have hap0 : a + 20 ≤ SMv ∨ SMv + 200 ≤ a := ap3
      have hacc0 : S.mem.accessible a 20 true = true := by rw [hf.accessible]; exact hacc
      have hsma0 : S.mem.accessible SMv 200 false = true := by rw [hf.accessible]; exact hsma
      janus64_run [hlit, hs, div1e9_64 U hU, mod1e9_64 U hU, hyv] until [segAddr P "internal/strconv.formatBase10" + 0x60]
      refine fb_inner impl (retAddrOf s) SMv a i y (U / 1000000000) S.mem hi9 hi20 hyl (by omega) hlit hSMb hab hap0
        hacc0 hsma0 h_rdsm 4 0 rfl _ y (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ ?_
      all_goals try (dsimp only; simp [setRegF_apply, h3, h1]; done)
      all_goals try (dsimp only; rfl)
      all_goals try (dsimp only; exact MemFrame.refl _ _)
      all_goals try (dsimp only; simp [pairsOf_zero]; done)
      rintro S' hpc' h0' h3' h7' h6' h2' h1' hr hx15' hfs' hdf' hmx' hx87' hfw' hf' hrb'
      dsimp only at hr hx15' hfs' hdf' hmx'
      have hz4 : y / 100 ^ 4 < 10 := by show y / 100000000 < 10; omega
      obtain ⟨z, hz⟩ : ∃ z, y / 100 ^ 4 = z := ⟨_, rfl⟩
      rw [hz] at h6'
      rw [hz] at hz4
      have hzy : z = y / 100000000 := hz.symm
      have e1 : (i - 8 + (18446744073709551615 + a) % 18446744073709551616) % 18446744073709551616 = a + (i - 9) := by omega
      have hS4 : S'.regs 4 = BitVec.ofNat 64 SP - 8#64 := by
        have := hr 4 (Or.inl rfl); simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff] at this; rw [this]; exact hsp'
      have hS5 : S'.regs 5 = BitVec.ofNat 64 SP - 8#64 := by
        have := hr 5 (Or.inr (Or.inl rfl)); simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff] at this; rw [this]; exact hbp'
      have hS14 : S'.regs 14 = s.regs 14 := by
        have := hr 14 (Or.inr (Or.inr rfl)); simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff] at this; rw [this]; exact hg'
      have hfS : MemFrame s.mem S'.mem [(SP - 8, SP), (SP + 8, SP + 16), (a, a + 20)] :=
        MemFrame.trans hf hf' (by
          intro a' n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
      have hrd1 : S'.mem.readLE (SP - 8) 8 = (s.regs 5).toNat := by
        rw [hf'.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at ap1; omega)]; exact h_rd1
      have h_sm0 : ∀ j, j < 200 → S.mem.readLE (SMv + j) 1 = smallsByte j := h_rdsm
      have hs8 : S'.mem.readLE (SMv + (z * 2 + 1)) 1 = smallsByte (z * 2 + 1) := by
        rw [hf'.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h_sm0 _ (by omega)
      have hK : readBytes (S'.mem.writeLE (a + (i - 9)) 1 (smallsByte (((z + z) % 4294967296 + 1) % 4294967296) % 256))
          (a + (i - 9)) (9 + (20 - i)) = digits9 y ++ readBytes S.mem (a + i) (20 - i) := by
        rw [show 9 + (20 - i) = (8 + (20 - i)) + 1 by omega, readBytes_one_write,
          show a + (i - 9) + 1 = a + (i - 8) by omega, hrb', digits9_eq, List.cons_append]
        congr 1
        have e := blo (((z + z) % 4294967296 + 1) % 4294967296) z (by omega) (by omega)
        rw [e, hzy]
      have hx15S : S'.xmm 15 = s.xmm 15 := hx15'.trans hx15
      have hfsS : S'.fsBase = s.fsBase := hfs'.trans hfs
      janus64_run [hlit, e1, hs8] until [segAddr P "internal/strconv.formatBase10" + 0x17]
      · -- the last chunk (`U < 10^9`): return
        have hc := decimal_nine U (by omega) (by omega)
        have hUy : y = U := by omega
        subst hUy
        have hlen9 : (Janus.Spec.Print.decimal y).length = 9 := by rw [hc]; simp [digits9]
        unfold FbTail
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?eq, ?fr, ?rb⟩
        case eq =>
          refine eq_retState64 [BitVec.ofNat 64 (i - (Janus.Spec.Print.decimal y).length)] ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          all_goals first
            | (simp [setRegF, retAddrOf, hsp, hS14, hx15S, hfsS, hdf', hmx', hx87', hfw', hx87, hfw, hmx, hdf, Nat.mod_eq_of_lt hspl]; done)
            | (simp only [setRegF, hlen9, List.getD_cons_zero, reduceIte]; apply BitVec.eq_of_toNat_eq; simp; omega)
            | rfl
        case fr => janus_frame
        case rb =>
          dsimp only
          rw [hlen9, hc, show 20 - (i - 9) = 9 + (20 - i) by omega]
          exact hK
      · -- back at the loop head: the next chunk
        have hDl : U / 1000000000 < U := Nat.div_lt_self (by omega) (by decide)
        have hc := decimal_chunk U (by omega)
        have hl : (Janus.Spec.Print.decimal U).length = (Janus.Spec.Print.decimal (U / 1000000000)).length + 9 := by
          rw [hc]; simp [digits9]
        refine Janus.Amd64.Tactic.ReachesRet.mono (ih (U / 1000000000) hDl _ (i - 9) (by omega) (by omega)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega)) ?_
        all_goals try (dsimp only; simp [setRegF_apply, hS4, hS5, hS14, hx15S, hfsS, hdf', hmx', hx87', hfw', hx87, hfw, hmx, hdf, h1']; done)
        all_goals try rfl
        all_goals try (dsimp only; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega)
        all_goals try janus_frame
        all_goals try (dsimp only; rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at ap1; omega)]; exact hrd1)
        all_goals (first | (intro j hj; dsimp only; rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; rw [hf'.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact h_sm0 j hj) | skip)
        rintro s' ⟨junk, f, x, yh, m, zh, kr, rfl, hfm, hrb⟩
        unfold FbTail
        have hi' : i - (Janus.Spec.Print.decimal U).length = i - 9 - (Janus.Spec.Print.decimal (U / 1000000000)).length := by
          omega
        refine ⟨junk, f, x, yh, m, zh, kr, by rw [hi'], hfm, ?_⟩
        rw [hi', hrb, hc, List.append_assoc]
        rw [List.append_cancel_left_eq]
        dsimp only
        rw [show 20 - (i - 9) = 9 + (20 - i) by omega, hyv]
        exact hK
  -- the entry: the prologue, then the loop head with `i = 20`
  janus64_run until [segAddr P "internal/strconv.formatBase10" + 0x17]
  refine Janus.Amd64.Tactic.ReachesRet.mono (outer u _ 20 (length_decimal_le 19 u (by omega)) (Nat.le_refl _)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hul) ?_
  all_goals try (dsimp only; simp [setRegF_apply, hsp, hx0, hx3', hx1', hx7]; done)
  all_goals try rfl
  all_goals try janus_frame
  all_goals try (dsimp only; rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by have := (s.regs 5).isLt; simpa using this))
  all_goals try (intro j hj; dsimp only; rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at ap4; omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at ap4; omega)]; exact h_sm j hj)
  rintro s' ⟨junk, f, x, yh, m, zh, kr, rfl, hfm, hrb⟩
  have e4 : (s.regs 4).toNat = SP := by rw [hsp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspl]
  have e0 : (s.regs 0).toNat = a := by rw [hx0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx0l]
  have e7 : (s.regs 7).toNat = u := by rw [hx7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
  simp only [e4, e0, e7]
  have hl20 := length_decimal_le 19 u (by omega)
  refine ⟨20 - (Janus.Spec.Print.decimal u).length, junk, f, x, yh, m, zh, kr, ?_, by omega, hfm, ?_⟩
  · rfl
  · rw [show 20 - (20 - (Janus.Spec.Print.decimal u).length) = (Janus.Spec.Print.decimal u).length by omega] at hrb ⊢
    simp only [readBytes_zero, Nat.sub_self, List.append_nil] at hrb
    simpa using hrb
