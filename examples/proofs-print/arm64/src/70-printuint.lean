/-! ## `internal/strconv.formatBase10` and `printuint(v)` -/

/-- The table `internal/strconv.smalls` ("00010203…99", `ADRP`+`ADD` in `formatBase10`). -/
def SM : Nat := adrpLdTarget (segAddr P "internal/strconv.formatBase10" + 168)
  (segWord P "internal/strconv.formatBase10" 42) (segWord P "internal/strconv.formatBase10" 43) 0

/-- Byte `j` of `smalls`: the two decimal digits of every number below 100, in order. -/
def smallsByte (j : Nat) : Nat := if j % 2 = 0 then 48 + j / 20 else 48 + j / 2 % 10

set_option maxRecDepth 100000 in
theorem smalls_data : ∀ j, j < 200 → dataRead P (SM + j) 1 = some (smallsByte j) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem formatBase10 (impl : List Segment) :
    Summary (P.link impl) (segAddr P "internal/strconv.formatBase10")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ StackOK s 24 16 ∧ GuardOK s 0 ∧
        (s.regs 1).toNat = 20 ∧ (s.regs 2).toNat = 20 ∧ (s.regs 0).toNat + 20 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 0).toNat 20 true = true ∧
        Apart (s.sp.toNat - 24) 40 (s.regs 0).toNat 20 ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.regs 0).toNat 20 ∧
        s.mem.accessible SM 200 false = true ∧ ∀ j, j < 200 → s.mem.readLE (SM + j) 1 = smallsByte j)
      (fun s s' => ∃ (i : Nat) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
        s' = retState s junk [BitVec.ofNat 64 i] f v m ∧ i ≤ 20 ∧
        MemFrame s.mem m [(s.sp.toNat - 24, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16),
          ((s.regs 0).toNat, (s.regs 0).toNat + 20)] ∧
        readBytes m ((s.regs 0).toNat + i) (20 - i) = Janus.Spec.Print.decimal (s.regs 3).toNat) := by
  -- PROOF formatBase10
  intro s hpc ⟨h30a, h30b, ⟨hal, hb, ha, hw⟩, ⟨hg1, hg2, hg3⟩, hx1, hx2, hab, hacc, ap1, ap2, hsma, h_sm⟩
  have hsp : s.sp = BitVec.ofNat 64 s.sp.toNat := by simp
  have hx0 : s.regs 0 = BitVec.ofNat 64 (s.regs 0).toNat := by simp
  have hx3 : s.regs 3 = BitVec.ofNat 64 (s.regs 3).toNat := by simp
  have hx1' : s.regs 1 = 20#64 := by apply BitVec.eq_of_toNat_eq; simp [hx1]
  have hx2' : s.regs 2 = 20#64 := by apply BitVec.eq_of_toNat_eq; simp [hx2]
  have hspl := s.sp.isLt
  have hul := (s.regs 3).isLt
  generalize s.sp.toNat = SP at *
  generalize (s.regs 0).toNat = a at *
  generalize (s.regs 3).toNat = u at *
  janus_eval_nat h_smv : SM
  rw [h_smv] at h_sm hsma
  janus_run [reduceUbfm, reduceUbfm2, reduceUbfmNat, BitVec.toNat_setWidth, BitVec.toNat_mul, magic100, magic1e9, umulh_lit]
  trace_state
  all_goals sorry
