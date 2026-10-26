import JanusASL.Proofs.FpSame.Base

namespace JanusASL.FpS
open Janus.Arm64

theorem fp_execMaddl (s : State) (U o0 : Bool) (rm ra rn rd : Nat) :
    FpSame s (execMaddl s U o0 rm ra rn rd) := by
  unfold execMaddl; fp_same

@[simp] theorem execMaddl_vregs (s : State) (U o0 : Bool) (rm ra rn rd : Nat) : (execMaddl s U o0 rm ra rn rd).vregs = s.vregs := (fp_execMaddl s U o0 rm ra rn rd).1
@[simp] theorem execMaddl_fpcr (s : State) (U o0 : Bool) (rm ra rn rd : Nat) : (execMaddl s U o0 rm ra rn rd).fpcr = s.fpcr := (fp_execMaddl s U o0 rm ra rn rd).2.1
@[simp] theorem execMaddl_fpsr (s : State) (U o0 : Bool) (rm ra rn rd : Nat) : (execMaddl s U o0 rm ra rn rd).fpsr = s.fpsr := (fp_execMaddl s U o0 rm ra rn rd).2.2

theorem fp_execMulh (s : State) (U : Bool) (rm rn rd : Nat) :
    FpSame s (execMulh s U rm rn rd) := by
  unfold execMulh; fp_same

@[simp] theorem execMulh_vregs (s : State) (U : Bool) (rm rn rd : Nat) : (execMulh s U rm rn rd).vregs = s.vregs := (fp_execMulh s U rm rn rd).1
@[simp] theorem execMulh_fpcr (s : State) (U : Bool) (rm rn rd : Nat) : (execMulh s U rm rn rd).fpcr = s.fpcr := (fp_execMulh s U rm rn rd).2.1
@[simp] theorem execMulh_fpsr (s : State) (U : Bool) (rm rn rd : Nat) : (execMulh s U rm rn rd).fpsr = s.fpsr := (fp_execMulh s U rm rn rd).2.2

theorem fp_execDiv (N : Nat) (s : State) (signed : Bool) (rm rn rd : Nat) :
    FpSame s (execDiv N s signed rm rn rd) := by
  unfold execDiv; fp_same

@[simp] theorem execDiv_vregs (N : Nat) (s : State) (signed : Bool) (rm rn rd : Nat) : (execDiv N s signed rm rn rd).vregs = s.vregs := (fp_execDiv N s signed rm rn rd).1
@[simp] theorem execDiv_fpcr (N : Nat) (s : State) (signed : Bool) (rm rn rd : Nat) : (execDiv N s signed rm rn rd).fpcr = s.fpcr := (fp_execDiv N s signed rm rn rd).2.1
@[simp] theorem execDiv_fpsr (N : Nat) (s : State) (signed : Bool) (rm rn rd : Nat) : (execDiv N s signed rm rn rd).fpsr = s.fpsr := (fp_execDiv N s signed rm rn rd).2.2

theorem fp_execShiftV (N : Nat) (s : State) (t : ShiftType) (rm rn rd : Nat) :
    FpSame s (execShiftV N s t rm rn rd) := by
  unfold execShiftV; fp_same

@[simp] theorem execShiftV_vregs (N : Nat) (s : State) (t : ShiftType) (rm rn rd : Nat) : (execShiftV N s t rm rn rd).vregs = s.vregs := (fp_execShiftV N s t rm rn rd).1
@[simp] theorem execShiftV_fpcr (N : Nat) (s : State) (t : ShiftType) (rm rn rd : Nat) : (execShiftV N s t rm rn rd).fpcr = s.fpcr := (fp_execShiftV N s t rm rn rd).2.1
@[simp] theorem execShiftV_fpsr (N : Nat) (s : State) (t : ShiftType) (rm rn rd : Nat) : (execShiftV N s t rm rn rd).fpsr = s.fpsr := (fp_execShiftV N s t rm rn rd).2.2

theorem fp_execRbit (N : Nat) (s : State) (rn rd : Nat) :
    FpSame s (execRbit N s rn rd) := by
  unfold execRbit; fp_same

@[simp] theorem execRbit_vregs (N : Nat) (s : State) (rn rd : Nat) : (execRbit N s rn rd).vregs = s.vregs := (fp_execRbit N s rn rd).1
@[simp] theorem execRbit_fpcr (N : Nat) (s : State) (rn rd : Nat) : (execRbit N s rn rd).fpcr = s.fpcr := (fp_execRbit N s rn rd).2.1
@[simp] theorem execRbit_fpsr (N : Nat) (s : State) (rn rd : Nat) : (execRbit N s rn rd).fpsr = s.fpsr := (fp_execRbit N s rn rd).2.2

theorem fp_execRev (N : Nat) (s : State) (opc rn rd : Nat) :
    FpSame s (execRev N s opc rn rd) := by
  unfold execRev; fp_same

@[simp] theorem execRev_vregs (N : Nat) (s : State) (opc rn rd : Nat) : (execRev N s opc rn rd).vregs = s.vregs := (fp_execRev N s opc rn rd).1
@[simp] theorem execRev_fpcr (N : Nat) (s : State) (opc rn rd : Nat) : (execRev N s opc rn rd).fpcr = s.fpcr := (fp_execRev N s opc rn rd).2.1
@[simp] theorem execRev_fpsr (N : Nat) (s : State) (opc rn rd : Nat) : (execRev N s opc rn rd).fpsr = s.fpsr := (fp_execRev N s opc rn rd).2.2

theorem fp_execClz (N : Nat) (s : State) (rn rd : Nat) :
    FpSame s (execClz N s rn rd) := by
  unfold execClz; fp_same

@[simp] theorem execClz_vregs (N : Nat) (s : State) (rn rd : Nat) : (execClz N s rn rd).vregs = s.vregs := (fp_execClz N s rn rd).1
@[simp] theorem execClz_fpcr (N : Nat) (s : State) (rn rd : Nat) : (execClz N s rn rd).fpcr = s.fpcr := (fp_execClz N s rn rd).2.1
@[simp] theorem execClz_fpsr (N : Nat) (s : State) (rn rd : Nat) : (execClz N s rn rd).fpsr = s.fpsr := (fp_execClz N s rn rd).2.2

theorem fp_execCls (N : Nat) (s : State) (rn rd : Nat) :
    FpSame s (execCls N s rn rd) := by
  unfold execCls; fp_same

@[simp] theorem execCls_vregs (N : Nat) (s : State) (rn rd : Nat) : (execCls N s rn rd).vregs = s.vregs := (fp_execCls N s rn rd).1
@[simp] theorem execCls_fpcr (N : Nat) (s : State) (rn rd : Nat) : (execCls N s rn rd).fpcr = s.fpcr := (fp_execCls N s rn rd).2.1
@[simp] theorem execCls_fpsr (N : Nat) (s : State) (rn rd : Nat) : (execCls N s rn rd).fpsr = s.fpsr := (fp_execCls N s rn rd).2.2

end JanusASL.FpS
