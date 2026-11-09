import Extracted

/-! R1 `ensures`: "Add returns 42" — false, provable only if `Janus.GoABI.Ensures` means `True`. -/

namespace R1.Ensures

theorem claim (x y : BitVec 64) :
    Janus.GoABI.Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = 42) := trivial

end R1.Ensures
