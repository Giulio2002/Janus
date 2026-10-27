import PrintProofs.Arm64.FnHead

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

namespace PrintFn

/-- `runtime.printlock` with the M's print count already `c ≥ 1`: no `lock2`. -/
theorem printlock_held (impl : List Segment) :
    Summary (P.link impl) (segAddr P "runtime.printlock")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ StackOK s 40 0 ∧ GuardOK s 0 ∧
        (s.regs 28).toNat + 56 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 28).toNat + 48) 8 false = true ∧
        s.mem.readLE ((s.regs 28).toNat + 48) 8 + 280 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 true = true ∧
        1 ≤ s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 ∧
        s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 ≤ 126 ∧
        Sep (s.sp.toNat - 40) 32 [((s.regs 28).toNat + 16, 8), ((s.regs 28).toNat + 48, 8),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, 16)])
      (fun s s' => ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
        s' = retStateX s junk [] f v m ex ep ∧
        MemFrame s.mem m [(s.sp.toNat - 40, s.sp.toNat - 8),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, s.mem.readLE ((s.regs 28).toNat + 48) 8 + 268),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279, s.mem.readLE ((s.regs 28).toNat + 48) 8 + 280)] ∧
        m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 =
          s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 + 1 ∧
        m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 =
          s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4) := by
  -- PROOF printlock_held
  intro s hpc ⟨h30a, h30b, ⟨hal, hb, ha, hw⟩, ⟨hg1, hg2, hg3⟩, hgm1, hgm2, hm1, hm2, hc1, hc2, hout⟩
  simp only [sep_cons, sep_nil, and_true] at hout
  split_ands
  have hlt : s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 < 128 := by omega
  janus_run [rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat, ofNat32_eq_zero, sext32_add_mod, sext8_add_mod, sext8_add_mod', hlt]
  refine ⟨_, _, _, _, _, _, by ret_state, by janus_frame, ?_, ?_⟩
  all_goals (janus_simp; first | omega | (split <;> janus_arith))

end PrintFn
