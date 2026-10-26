/-- `runtime.printlock` with the M's print count already `c ≥ 1`: no `lock2`. -/
theorem printlock_held (impl : List Amd64.Segment) :
    Summary (P.link impl) (segAddr P "runtime.printlock")
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ 24 ≤ (s.regs 4).toNat ∧
        (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 4).toNat - 24) 32 true = true ∧
        (s.regs 14).toNat + 56 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
        s.mem.readLE ((s.regs 14).toNat + 16) 8 < (s.regs 4).toNat ∧
        s.mem.accessible ((s.regs 14).toNat + 48) 8 false = true ∧
        s.mem.readLE ((s.regs 14).toNat + 48) 8 + 280 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264) 16 true = true ∧
        1 ≤ s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 279) 1 ∧
        s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 279) 1 ≤ 126 ∧
        s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264) 4 + 1 < 2 ^ 31 ∧
        Sep ((s.regs 4).toNat - 24) 32 [((s.regs 14).toNat + 16, 8), ((s.regs 14).toNat + 48, 8),
          (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264, 16)])
      (fun s s' => ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory),
        s' = retState64 s junk [] f x yh m ∧
        MemFrame s.mem m [((s.regs 4).toNat - 24, (s.regs 4).toNat),
          (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264, s.mem.readLE ((s.regs 14).toNat + 48) 8 + 268),
          (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 279, s.mem.readLE ((s.regs 14).toNat + 48) 8 + 280)] ∧
        m.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 279) 1 =
          s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 279) 1 + 1 ∧
        m.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264) 4 =
          s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264) 4) := by
  -- PROOF printlock_held
  intro s hpc ⟨hra, hb, ha, hw, hg1, hg2, hg3, hgm2, hm1, hm2, hc1, hc2, hl31, hout⟩
  simp only [sep_cons, sep_nil, and_true] at hout
  split_ands
  have hnz : (s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 279) 1 % 256 = 0) = False := by
    simp only [eq_iff_iff, iff_false]; omega
  janus64_run [zx8_chain, ofNat8_eq_zero_iff, hnz]
  refine ⟨_, _, _, _, _, by ret_state64 [], by janus_frame, ?_, ?_⟩
  all_goals dsimp only
  all_goals janus64_simp
  all_goals omega
