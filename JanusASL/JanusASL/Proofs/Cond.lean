import JanusASL.Proofs.Ops

/-! `ConditionHolds` of the generated model against Janus' `conditionHolds`. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_ConditionHolds_0 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 0)).run s = .ok (Janus.Arm64.conditionHolds 0 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 0) 3 1 = BitVec.ofNat 3 0 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 0) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 0 != 0b1111#4) =
      false := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_1 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 1)).run s = .ok (Janus.Arm64.conditionHolds 1 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 1) 3 1 = BitVec.ofNat 3 0 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 1) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 1 != 0b1111#4) =
      true := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_2 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 2)).run s = .ok (Janus.Arm64.conditionHolds 2 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 2) 3 1 = BitVec.ofNat 3 1 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 2) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 2 != 0b1111#4) =
      false := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_3 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 3)).run s = .ok (Janus.Arm64.conditionHolds 3 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 3) 3 1 = BitVec.ofNat 3 1 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 3) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 3 != 0b1111#4) =
      true := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_4 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 4)).run s = .ok (Janus.Arm64.conditionHolds 4 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 4) 3 1 = BitVec.ofNat 3 2 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 4) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 4 != 0b1111#4) =
      false := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_5 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 5)).run s = .ok (Janus.Arm64.conditionHolds 5 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 5) 3 1 = BitVec.ofNat 3 2 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 5) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 5 != 0b1111#4) =
      true := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_6 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 6)).run s = .ok (Janus.Arm64.conditionHolds 6 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 6) 3 1 = BitVec.ofNat 3 3 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 6) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 6 != 0b1111#4) =
      false := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_7 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 7)).run s = .ok (Janus.Arm64.conditionHolds 7 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 7) 3 1 = BitVec.ofNat 3 3 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 7) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 7 != 0b1111#4) =
      true := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_8 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 8)).run s = .ok (Janus.Arm64.conditionHolds 8 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 8) 3 1 = BitVec.ofNat 3 4 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 8) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 8 != 0b1111#4) =
      false := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_9 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 9)).run s = .ok (Janus.Arm64.conditionHolds 9 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 9) 3 1 = BitVec.ofNat 3 4 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 9) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 9 != 0b1111#4) =
      true := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_10 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 10)).run s = .ok (Janus.Arm64.conditionHolds 10 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 10) 3 1 = BitVec.ofNat 3 5 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 10) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 10 != 0b1111#4) =
      false := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_11 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 11)).run s = .ok (Janus.Arm64.conditionHolds 11 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 11) 3 1 = BitVec.ofNat 3 5 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 11) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 11 != 0b1111#4) =
      true := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_12 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 12)).run s = .ok (Janus.Arm64.conditionHolds 12 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 12) 3 1 = BitVec.ofNat 3 6 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 12) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 12 != 0b1111#4) =
      false := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_13 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 13)).run s = .ok (Janus.Arm64.conditionHolds 13 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 13) 3 1 = BitVec.ofNat 3 6 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 13) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 13 != 0b1111#4) =
      true := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_14 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 14)).run s = .ok (Janus.Arm64.conditionHolds 14 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 14) 3 1 = BitVec.ofNat 3 7 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 14) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 14 != 0b1111#4) =
      false := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds_15 {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) :
    (ConditionHolds (BitVec.ofNat 4 15)).run s = .ok (Janus.Arm64.conditionHolds 15 f) s := by
  obtain ⟨_, _, _, hn, hz, hc, hv⟩ := hps
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 4 15) 3 1 = BitVec.ofNat 3 7 := by decide
  have e2 : ((Sail.BitVec.access (BitVec.ofNat 4 15) 0 : BitVec 1) == 1#1 && BitVec.ofNat 4 15 != 0b1111#4) =
      false := by decide
  simp only [ConditionHolds, run_bind, run_undefined_bool, run_pure, run_readReg hp, hn, hz, hc, hv, e1, e2,
    andM, toBool, ite_true, ite_false, Bool.false_eq_true]
  cases f with | mk n z c v => cases n <;> cases z <;> cases c <;> cases v <;>
    simp [run_bind, run_map, run_readReg hp, hn, hz, hc, hv, run_pure, andM, toBool, Janus.Arm64.conditionHolds]

theorem run_ConditionHolds {s : SState} {p : ProcState} (hp : s.regs.get? .PSTATE = some p)
    {f : Janus.Arm64.Flags} (hps : PState f p) (cond : BitVec 4) :
    (ConditionHolds cond).run s = .ok (Janus.Arm64.conditionHolds cond.toNat f) s := by
  have e : cond = BitVec.ofNat 4 cond.toNat := by simp
  have hl := cond.isLt
  rw [e]
  generalize cond.toNat = c at hl
  match c, hl with
  | 0, _ => simpa using run_ConditionHolds_0 hp hps
  | 1, _ => simpa using run_ConditionHolds_1 hp hps
  | 2, _ => simpa using run_ConditionHolds_2 hp hps
  | 3, _ => simpa using run_ConditionHolds_3 hp hps
  | 4, _ => simpa using run_ConditionHolds_4 hp hps
  | 5, _ => simpa using run_ConditionHolds_5 hp hps
  | 6, _ => simpa using run_ConditionHolds_6 hp hps
  | 7, _ => simpa using run_ConditionHolds_7 hp hps
  | 8, _ => simpa using run_ConditionHolds_8 hp hps
  | 9, _ => simpa using run_ConditionHolds_9 hp hps
  | 10, _ => simpa using run_ConditionHolds_10 hp hps
  | 11, _ => simpa using run_ConditionHolds_11 hp hps
  | 12, _ => simpa using run_ConditionHolds_12 hp hps
  | 13, _ => simpa using run_ConditionHolds_13 hp hps
  | 14, _ => simpa using run_ConditionHolds_14 hp hps
  | 15, _ => simpa using run_ConditionHolds_15 hp hps
  | _ + 16, hl => exact absurd hl (by omega)

end JanusASL.Proofs
