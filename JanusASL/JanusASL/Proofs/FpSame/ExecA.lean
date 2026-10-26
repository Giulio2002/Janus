import JanusASL.Proofs.FpSame.Base

namespace JanusASL.FpS
open Janus.Arm64

theorem fp_execAddSubImm (N : Nat) (s : State) (op S sh : Bool) (imm12 rn rd : Nat) :
    FpSame s (execAddSubImm N s op S sh imm12 rn rd) := by
  unfold execAddSubImm; fp_same

@[simp] theorem execAddSubImm_vregs (N : Nat) (s : State) (op S sh : Bool) (imm12 rn rd : Nat) : (execAddSubImm N s op S sh imm12 rn rd).vregs = s.vregs := (fp_execAddSubImm N s op S sh imm12 rn rd).1
@[simp] theorem execAddSubImm_fpcr (N : Nat) (s : State) (op S sh : Bool) (imm12 rn rd : Nat) : (execAddSubImm N s op S sh imm12 rn rd).fpcr = s.fpcr := (fp_execAddSubImm N s op S sh imm12 rn rd).2.1
@[simp] theorem execAddSubImm_fpsr (N : Nat) (s : State) (op S sh : Bool) (imm12 rn rd : Nat) : (execAddSubImm N s op S sh imm12 rn rd).fpsr = s.fpsr := (fp_execAddSubImm N s op S sh imm12 rn rd).2.2

theorem fp_execAddSubShifted (N : Nat) (s : State) (op S : Bool) (shift : ShiftType) (rm imm6 rn rd : Nat) :
    FpSame s (execAddSubShifted N s op S shift rm imm6 rn rd) := by
  unfold execAddSubShifted; fp_same

@[simp] theorem execAddSubShifted_vregs (N : Nat) (s : State) (op S : Bool) (shift : ShiftType) (rm imm6 rn rd : Nat) : (execAddSubShifted N s op S shift rm imm6 rn rd).vregs = s.vregs := (fp_execAddSubShifted N s op S shift rm imm6 rn rd).1
@[simp] theorem execAddSubShifted_fpcr (N : Nat) (s : State) (op S : Bool) (shift : ShiftType) (rm imm6 rn rd : Nat) : (execAddSubShifted N s op S shift rm imm6 rn rd).fpcr = s.fpcr := (fp_execAddSubShifted N s op S shift rm imm6 rn rd).2.1
@[simp] theorem execAddSubShifted_fpsr (N : Nat) (s : State) (op S : Bool) (shift : ShiftType) (rm imm6 rn rd : Nat) : (execAddSubShifted N s op S shift rm imm6 rn rd).fpsr = s.fpsr := (fp_execAddSubShifted N s op S shift rm imm6 rn rd).2.2

theorem fp_execAddSubExt (N : Nat) (s : State) (op S : Bool) (rm : Nat) (option : ExtendType) (imm3 rn rd : Nat) :
    FpSame s (execAddSubExt N s op S rm option imm3 rn rd) := by
  unfold execAddSubExt; fp_same

@[simp] theorem execAddSubExt_vregs (N : Nat) (s : State) (op S : Bool) (rm : Nat) (option : ExtendType) (imm3 rn rd : Nat) : (execAddSubExt N s op S rm option imm3 rn rd).vregs = s.vregs := (fp_execAddSubExt N s op S rm option imm3 rn rd).1
@[simp] theorem execAddSubExt_fpcr (N : Nat) (s : State) (op S : Bool) (rm : Nat) (option : ExtendType) (imm3 rn rd : Nat) : (execAddSubExt N s op S rm option imm3 rn rd).fpcr = s.fpcr := (fp_execAddSubExt N s op S rm option imm3 rn rd).2.1
@[simp] theorem execAddSubExt_fpsr (N : Nat) (s : State) (op S : Bool) (rm : Nat) (option : ExtendType) (imm3 rn rd : Nat) : (execAddSubExt N s op S rm option imm3 rn rd).fpsr = s.fpsr := (fp_execAddSubExt N s op S rm option imm3 rn rd).2.2

theorem fp_execAddSubCarry (N : Nat) (s : State) (op S : Bool) (rm rn rd : Nat) :
    FpSame s (execAddSubCarry N s op S rm rn rd) := by
  unfold execAddSubCarry; fp_same

@[simp] theorem execAddSubCarry_vregs (N : Nat) (s : State) (op S : Bool) (rm rn rd : Nat) : (execAddSubCarry N s op S rm rn rd).vregs = s.vregs := (fp_execAddSubCarry N s op S rm rn rd).1
@[simp] theorem execAddSubCarry_fpcr (N : Nat) (s : State) (op S : Bool) (rm rn rd : Nat) : (execAddSubCarry N s op S rm rn rd).fpcr = s.fpcr := (fp_execAddSubCarry N s op S rm rn rd).2.1
@[simp] theorem execAddSubCarry_fpsr (N : Nat) (s : State) (op S : Bool) (rm rn rd : Nat) : (execAddSubCarry N s op S rm rn rd).fpsr = s.fpsr := (fp_execAddSubCarry N s op S rm rn rd).2.2

theorem fp_execLogicalImm (N : Nat) (s : State) (opc : LogicOp) (Nbit : Bool) (immr imms rn rd : Nat) :
    FpSame s (execLogicalImm N s opc Nbit immr imms rn rd) := by
  unfold execLogicalImm; fp_same

@[simp] theorem execLogicalImm_vregs (N : Nat) (s : State) (opc : LogicOp) (Nbit : Bool) (immr imms rn rd : Nat) : (execLogicalImm N s opc Nbit immr imms rn rd).vregs = s.vregs := (fp_execLogicalImm N s opc Nbit immr imms rn rd).1
@[simp] theorem execLogicalImm_fpcr (N : Nat) (s : State) (opc : LogicOp) (Nbit : Bool) (immr imms rn rd : Nat) : (execLogicalImm N s opc Nbit immr imms rn rd).fpcr = s.fpcr := (fp_execLogicalImm N s opc Nbit immr imms rn rd).2.1
@[simp] theorem execLogicalImm_fpsr (N : Nat) (s : State) (opc : LogicOp) (Nbit : Bool) (immr imms rn rd : Nat) : (execLogicalImm N s opc Nbit immr imms rn rd).fpsr = s.fpsr := (fp_execLogicalImm N s opc Nbit immr imms rn rd).2.2

theorem fp_execLogicalShifted (N : Nat) (s : State) (opc : LogicOp) (shift : ShiftType) (invert : Bool) (rm imm6 rn rd : Nat) :
    FpSame s (execLogicalShifted N s opc shift invert rm imm6 rn rd) := by
  unfold execLogicalShifted; fp_same

@[simp] theorem execLogicalShifted_vregs (N : Nat) (s : State) (opc : LogicOp) (shift : ShiftType) (invert : Bool) (rm imm6 rn rd : Nat) : (execLogicalShifted N s opc shift invert rm imm6 rn rd).vregs = s.vregs := (fp_execLogicalShifted N s opc shift invert rm imm6 rn rd).1
@[simp] theorem execLogicalShifted_fpcr (N : Nat) (s : State) (opc : LogicOp) (shift : ShiftType) (invert : Bool) (rm imm6 rn rd : Nat) : (execLogicalShifted N s opc shift invert rm imm6 rn rd).fpcr = s.fpcr := (fp_execLogicalShifted N s opc shift invert rm imm6 rn rd).2.1
@[simp] theorem execLogicalShifted_fpsr (N : Nat) (s : State) (opc : LogicOp) (shift : ShiftType) (invert : Bool) (rm imm6 rn rd : Nat) : (execLogicalShifted N s opc shift invert rm imm6 rn rd).fpsr = s.fpsr := (fp_execLogicalShifted N s opc shift invert rm imm6 rn rd).2.2

end JanusASL.FpS
