import Janus.Contracts.CmpstringSat
import Janus.Contracts.CmpstringSatAmd64

/-!
# `runtime.cmpstring` stub for witnesses, at the program's own contract address

`CmpstringSat` shows that `CmpstringContract` is satisfiable by a byte loop at `A0` of a program
with no other code. A witness for a theorem about an extracted function that calls
`runtime.cmpstring` needs the contract for `Extracted.program.link impl` at
`Extracted.program.contractAddr "runtime.cmpstring"`. `janus_cmpstring_witness` (arm64) and
`janus64_cmpstring_witness` (amd64) define, in a namespace `CmpW` of the caller, that loop as
`CmpW.impl` placed at `CmpW.cA`, the closed program `CmpW.linked`, and `CmpW.hcmp`, the contract
proved by the same symbolic execution as `CmpstringSat.impl_ok` (the loop is position independent;
only its address changes). Nothing is trusted: `hcmp` is an ordinary kernel-checked theorem.
-/

open Lean in
set_option hygiene false in
macro "janus_cmpstring_witness" : command =>
  `(namespace CmpW
    open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Contracts.Cmpstring

    def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")
    def impl : List Segment := [{ name := "witness.cmpstring", base := (janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")), words := Janus.Contracts.CmpstringSat.code }]
    def linked : Program := Extracted.program.link impl

    theorem addr : Extracted.program.contractAddr "runtime.cmpstring" = (janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")) := by decide

    theorem loop (s : State) (hr1 : (s.regs 30).toNat % 4 = 0) (hr2 : (s.regs 30).toNat < 2 ^ 48) :
        ∀ la (R : Nat → W64) (F : Flags) (a b lb : Nat),
          R 0 = BitVec.ofNat 64 a → R 1 = BitVec.ofNat 64 la → R 2 = BitVec.ofNat 64 b →
          R 3 = BitVec.ofNat 64 lb → la < 2 ^ 64 → lb < 2 ^ 64 →
          R 18 = s.regs 18 → R 28 = s.regs 28 → R 29 = s.regs 29 → R 30 = s.regs 30 →
          StrOK s.mem a la → StrOK s.mem b lb →
          strCmp s.mem a b la lb = strCmp s.mem (s.regs 0).toNat (s.regs 2).toNat (s.regs 1).toNat (s.regs 3).toNat →
          ReachesRet linked (s.regs 30) { s with regs := R, flags := F, pc := BitVec.ofNat 64 (janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")) } (CmpRet 16 s) := by
      intro la
      induction la with
      | zero =>
        intro R F a b lb h0 h1 h2 h3 hla hlb h18 h28 h29 h30 hsa hsb hc
        janus_run [h0, h1, h2, h3, h30]
        all_goals
          apply Janus.Contracts.CmpstringSat.ret_of
          all_goals try (simp only [setReg]; simp [h18, h28, h29])
          simp only [cmpResult]
          rw [← hc]
          clear hc
          cases lb <;> simp_all [strCmp] <;> decide
      | succ la ih =>
        intro R F a b lb h0 h1 h2 h3 hla hlb h18 h28 h29 h30 hsa hsb hc
        rcases hsa with hsa | ⟨hsa1, hsa2⟩
        · omega
        have ha1 : s.mem.accessible a 1 false = true := Memory.accessible_mono _ hsa1 (Nat.le_refl _) (by omega)
        cases lb with
        | zero =>
          janus_run [h0, h1, h2, h3, h30]
          all_goals
            apply Janus.Contracts.CmpstringSat.ret_of
            all_goals try (simp only [setReg]; simp [h18, h28, h29])
            simp only [cmpResult]
            rw [← hc]
            clear hc
            simp [strCmp]
        | succ lb =>
          rcases hsb with hsb | ⟨hsb1, hsb2⟩
          · omega
          have hb1 : s.mem.accessible b 1 false = true := Memory.accessible_mono _ hsb1 (Nat.le_refl _) (by omega)
          have hx : s.mem.readLE a 1 < 256 := by simpa using Memory.readLE_lt s.mem a 1
          have hy : s.mem.readLE b 1 < 256 := by simpa using Memory.readLE_lt s.mem b 1
          janus_run [h0, h1, h2, h3, h30] until [(janus_eval% (Extracted.program.contractAddr "runtime.cmpstring"))]
          all_goals first
            | (apply Janus.Contracts.CmpstringSat.ret_of
               all_goals try (simp only [setReg]; simp [h18, h28, h29])
               simp only [cmpResult]
               rw [← hc]
               clear hc
               simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
               rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 64),
                 Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 64)] at *
               rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 32),
                 Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 32)] at *
               simp only [strCmp]
               split <;> (try split) <;> first | rfl | omega | decide)
            | skip
          rename_i hle
          have heq := hbr
          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hle heq
          rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 64)] at heq
          rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 32),
            Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 32)] at heq
          apply ih _ _ (a + 1) (b + 1) lb
          all_goals try (simp only [setReg]; simp [h18, h28, h29, h30])
          · apply BitVec.eq_of_toNat_eq; simp <;> omega
          · apply BitVec.eq_of_toNat_eq; simp <;> omega
          · apply BitVec.eq_of_toNat_eq; simp <;> omega
          · apply BitVec.eq_of_toNat_eq; simp <;> omega
          · omega
          · omega
          · by_cases hl : la = 0
            · exact Or.inl hl
            · exact Or.inr ⟨Memory.accessible_mono _ hsa1 (by omega) (by omega), by omega⟩
          · by_cases hl : lb = 0
            · exact Or.inl hl
            · exact Or.inr ⟨Memory.accessible_mono _ hsb1 (by omega) (by omega), by omega⟩
          · rw [← hc]
            simp only [strCmp, heq, Nat.lt_irrefl, ite_false]

    theorem hcmp : CmpstringContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.cmpstring") 16 := by
      rw [addr]
      intro s hpc ⟨⟨hr1, hr2, _⟩, hsa, hsb⟩
      have key := loop s hr1 hr2 (s.regs 1).toNat s.regs s.flags (s.regs 0).toNat (s.regs 2).toNat
        (s.regs 3).toNat (by simp) (by simp) (by simp) (by simp) (s.regs 1).isLt (s.regs 3).isLt rfl rfl rfl rfl
        hsa hsb rfl
      have hs : ({ s with regs := s.regs, flags := s.flags, pc := BitVec.ofNat 64 (janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")) } : State) = s := by
        cases s; simp only at hpc ⊢; rw [hpc]
      rw [hs] at key
      exact key
    end CmpW)

open Lean in
set_option hygiene false in
/-- amd64 twin of `janus_cmpstring_witness`. -/
macro "janus64_cmpstring_witness" : command =>
  `(namespace CmpW
    open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Cmpstring

    def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")
    def impl : List Janus.Amd64.Segment := [{ name := "witness.cmpstring", base := (janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")), bytes := Janus.Contracts.CmpstringSatAmd64.code }]
    def linked : Janus.Amd64.Program := Extracted.program.link impl

    theorem addr : Extracted.program.contractAddr "runtime.cmpstring" = (janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")) := by decide

    theorem loop (s : State) (hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
        (hacc : s.mem.accessible (s.regs 4).toNat 8 false = true) (hnw : (s.regs 4).toNat + 8 ≤ 2 ^ 48) :
        ∀ la (R : Nat → W64) (F : Flags) (a b lb : Nat),
          R 0 = BitVec.ofNat 64 a → R 3 = BitVec.ofNat 64 la → R 1 = BitVec.ofNat 64 b →
          R 7 = BitVec.ofNat 64 lb → la < 2 ^ 64 → lb < 2 ^ 64 →
          R 4 = s.regs 4 → R 5 = s.regs 5 → R 14 = s.regs 14 →
          StrOK s.mem a la → StrOK s.mem b lb →
          strCmp s.mem a b la lb = strCmp s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 3).toNat (s.regs 7).toNat →
          ReachesRet linked (retAddrOf s) { s with regs := R, flags := F, rip := BitVec.ofNat 64 (janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")) } (CmpRet64 16 s) := by
      intro la
      induction la with
      | zero =>
        intro R F a b lb h0 h3 h1 h7 hla hlb h4 h5 h14 hsa hsb hc
        janus64_run [h0, h1, h3, h7, h4]
        all_goals
          apply Janus.Contracts.CmpstringSatAmd64.ret_of
          all_goals try (simp only [setRegF]; simp [h4, h5, h14])
          simp only [cmpResult64]
          rw [← hc]
          clear hc
          cases lb <;> simp_all [strCmp] <;> decide
      | succ la ih =>
        intro R F a b lb h0 h3 h1 h7 hla hlb h4 h5 h14 hsa hsb hc
        rcases hsa with hsa | ⟨hsa1, hsa2⟩
        · omega
        have ha1 : s.mem.accessible a 1 false = true :=
          Janus.Arm64.Memory.accessible_mono _ hsa1 (Nat.le_refl _) (by omega)
        cases lb with
        | zero =>
          janus64_run [h0, h1, h3, h7, h4]
          all_goals
            apply Janus.Contracts.CmpstringSatAmd64.ret_of
            all_goals try (simp only [setRegF]; simp [h4, h5, h14])
            simp only [cmpResult64]
            rw [← hc]
            clear hc
            simp [strCmp]
        | succ lb =>
          rcases hsb with hsb | ⟨hsb1, hsb2⟩
          · omega
          have hb1 : s.mem.accessible b 1 false = true :=
            Janus.Arm64.Memory.accessible_mono _ hsb1 (Nat.le_refl _) (by omega)
          have hx : s.mem.readLE a 1 < 256 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem a 1
          have hy : s.mem.readLE b 1 < 256 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem b 1
          have e : ∀ x, x < 256 → BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x)))
              = BitVec.ofNat 32 x := by
            intro x hx; apply BitVec.eq_of_toNat_eq; simp; omega
          have hsub : (BitVec.ofNat 32 (s.mem.readLE a 1) - BitVec.ofNat 32 (s.mem.readLE b 1) = 0#32) ↔
              s.mem.readLE a 1 = s.mem.readLE b 1 := by
            constructor
            · intro h; have := congrArg BitVec.toNat h
              simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
            · intro h; rw [h]; simp
          janus64_run [h0, h1, h3, h7, h4] until [(janus_eval% (Extracted.program.contractAddr "runtime.cmpstring"))]
          all_goals simp only [e _ hx, e _ hy, hsub, Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 4294967296),
            Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 4294967296)] at *
          all_goals first
            | (apply Janus.Contracts.CmpstringSatAmd64.ret_of
               all_goals try (simp only [setRegF]; simp [h4, h5, h14])
               simp only [cmpResult64]
               rw [← hc]
               clear hc
               simp only [strCmp]
               split <;> (try split) <;> first | rfl | omega | decide)
            | skip
          apply ih _ _ (a + 1) (b + 1) lb
          all_goals try (simp only [setRegF]; simp [h4, h5, h14])
          all_goals first
            | (apply BitVec.eq_of_toNat_eq; simp <;> omega)
            | omega
            | (by_cases hl : la = 0
               · exact Or.inl hl
               · exact Or.inr ⟨Janus.Arm64.Memory.accessible_mono _ hsa1 (by omega) (by omega), by omega⟩)
            | (by_cases hl : lb = 0
               · exact Or.inl hl
               · exact Or.inr ⟨Janus.Arm64.Memory.accessible_mono _ hsb1 (by omega) (by omega), by omega⟩)
            | (rw [← hc]; simp only [strCmp, hbr, Nat.lt_irrefl, ite_false])

    theorem hcmp : CmpstringContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.cmpstring") 16 := by
      rw [addr]
      intro s hpc ⟨⟨hr, _, hst, _, hw⟩, hsa, hsb⟩
      have hacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
        Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)
      have key := loop s hr hacc (by omega) (s.regs 3).toNat s.regs s.flags (s.regs 0).toNat (s.regs 1).toNat
        (s.regs 7).toNat (by simp) (by simp) (by simp) (by simp) (s.regs 3).isLt (s.regs 7).isLt rfl rfl rfl
        hsa hsb rfl
      have hs : ({ s with regs := s.regs, flags := s.flags, rip := BitVec.ofNat 64 (janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")) } : State) = s := by
        cases s; simp only at hpc ⊢; rw [hpc]
      rw [hs] at key
      exact key
    end CmpW)
