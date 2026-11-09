import JanusASL.Proofs.FpSame.Base

namespace JanusASL.FpS
open Janus.Arm64

theorem fp_execMoveWide (N : Nat) (s : State) (opc : MoveWideOp) (hw imm16 rd : Nat) :
    FpSame s (execMoveWide N s opc hw imm16 rd) := by
  unfold execMoveWide; fp_same

@[simp] theorem execMoveWide_vregs (N : Nat) (s : State) (opc : MoveWideOp) (hw imm16 rd : Nat) : (execMoveWide N s opc hw imm16 rd).vregs = s.vregs := (fp_execMoveWide N s opc hw imm16 rd).1
@[simp] theorem execMoveWide_fpcr (N : Nat) (s : State) (opc : MoveWideOp) (hw imm16 rd : Nat) : (execMoveWide N s opc hw imm16 rd).fpcr = s.fpcr := (fp_execMoveWide N s opc hw imm16 rd).2.1
@[simp] theorem execMoveWide_fpsr (N : Nat) (s : State) (opc : MoveWideOp) (hw imm16 rd : Nat) : (execMoveWide N s opc hw imm16 rd).fpsr = s.fpsr := (fp_execMoveWide N s opc hw imm16 rd).2.2

theorem fp_execBitfield (N : Nat) (s : State) (opc : BitfieldOp) (Nbit : Bool) (immr imms rn rd : Nat) :
    FpSame s (execBitfield N s opc Nbit immr imms rn rd) := by
  unfold execBitfield; fp_same

@[simp] theorem execBitfield_vregs (N : Nat) (s : State) (opc : BitfieldOp) (Nbit : Bool) (immr imms rn rd : Nat) : (execBitfield N s opc Nbit immr imms rn rd).vregs = s.vregs := (fp_execBitfield N s opc Nbit immr imms rn rd).1
@[simp] theorem execBitfield_fpcr (N : Nat) (s : State) (opc : BitfieldOp) (Nbit : Bool) (immr imms rn rd : Nat) : (execBitfield N s opc Nbit immr imms rn rd).fpcr = s.fpcr := (fp_execBitfield N s opc Nbit immr imms rn rd).2.1
@[simp] theorem execBitfield_fpsr (N : Nat) (s : State) (opc : BitfieldOp) (Nbit : Bool) (immr imms rn rd : Nat) : (execBitfield N s opc Nbit immr imms rn rd).fpsr = s.fpsr := (fp_execBitfield N s opc Nbit immr imms rn rd).2.2

theorem fp_execExtr (N : Nat) (s : State) (rm imms rn rd : Nat) :
    FpSame s (execExtr N s rm imms rn rd) := by
  unfold execExtr; fp_same

@[simp] theorem execExtr_vregs (N : Nat) (s : State) (rm imms rn rd : Nat) : (execExtr N s rm imms rn rd).vregs = s.vregs := (fp_execExtr N s rm imms rn rd).1
@[simp] theorem execExtr_fpcr (N : Nat) (s : State) (rm imms rn rd : Nat) : (execExtr N s rm imms rn rd).fpcr = s.fpcr := (fp_execExtr N s rm imms rn rd).2.1
@[simp] theorem execExtr_fpsr (N : Nat) (s : State) (rm imms rn rd : Nat) : (execExtr N s rm imms rn rd).fpsr = s.fpsr := (fp_execExtr N s rm imms rn rd).2.2

theorem fp_execCondSel (N : Nat) (s : State) (op : Bool) (rm cond : Nat) (o2 : Bool) (rn rd : Nat) :
    FpSame s (execCondSel N s op rm cond o2 rn rd) := by
  unfold execCondSel; fp_same

@[simp] theorem execCondSel_vregs (N : Nat) (s : State) (op : Bool) (rm cond : Nat) (o2 : Bool) (rn rd : Nat) : (execCondSel N s op rm cond o2 rn rd).vregs = s.vregs := (fp_execCondSel N s op rm cond o2 rn rd).1
@[simp] theorem execCondSel_fpcr (N : Nat) (s : State) (op : Bool) (rm cond : Nat) (o2 : Bool) (rn rd : Nat) : (execCondSel N s op rm cond o2 rn rd).fpcr = s.fpcr := (fp_execCondSel N s op rm cond o2 rn rd).2.1
@[simp] theorem execCondSel_fpsr (N : Nat) (s : State) (op : Bool) (rm cond : Nat) (o2 : Bool) (rn rd : Nat) : (execCondSel N s op rm cond o2 rn rd).fpsr = s.fpsr := (fp_execCondSel N s op rm cond o2 rn rd).2.2

theorem fp_execCondCmp {N : Nat} (s : State) (op : Bool) (x y : BitVec N) (cond nzcv : Nat) :
    FpSame s (execCondCmp s op x y cond nzcv) := by
  unfold execCondCmp; fp_same

@[simp] theorem execCondCmp_vregs {N : Nat} (s : State) (op : Bool) (x y : BitVec N) (cond nzcv : Nat) : (execCondCmp s op x y cond nzcv).vregs = s.vregs := (fp_execCondCmp s op x y cond nzcv).1
@[simp] theorem execCondCmp_fpcr {N : Nat} (s : State) (op : Bool) (x y : BitVec N) (cond nzcv : Nat) : (execCondCmp s op x y cond nzcv).fpcr = s.fpcr := (fp_execCondCmp s op x y cond nzcv).2.1
@[simp] theorem execCondCmp_fpsr {N : Nat} (s : State) (op : Bool) (x y : BitVec N) (cond nzcv : Nat) : (execCondCmp s op x y cond nzcv).fpsr = s.fpsr := (fp_execCondCmp s op x y cond nzcv).2.2

theorem fp_execMadd (N : Nat) (s : State) (o0 : Bool) (rm ra rn rd : Nat) :
    FpSame s (execMadd N s o0 rm ra rn rd) := by
  unfold execMadd; fp_same

@[simp] theorem execMadd_vregs (N : Nat) (s : State) (o0 : Bool) (rm ra rn rd : Nat) : (execMadd N s o0 rm ra rn rd).vregs = s.vregs := (fp_execMadd N s o0 rm ra rn rd).1
@[simp] theorem execMadd_fpcr (N : Nat) (s : State) (o0 : Bool) (rm ra rn rd : Nat) : (execMadd N s o0 rm ra rn rd).fpcr = s.fpcr := (fp_execMadd N s o0 rm ra rn rd).2.1
@[simp] theorem execMadd_fpsr (N : Nat) (s : State) (o0 : Bool) (rm ra rn rd : Nat) : (execMadd N s o0 rm ra rn rd).fpsr = s.fpsr := (fp_execMadd N s o0 rm ra rn rd).2.2

end JanusASL.FpS
