import PrintProofs.Arm64.Code

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

namespace PrintFn

abbrev P := PrintCode.program

/-! ## The runtime's print globals (`.noptrbss`/`.bss`), at the addresses the code computes -/

/-- `runtime.panicking` (`atomic.Uint32`): `ADRP`+`ADD` in `recordForPanic`. -/
def PK : Nat := adrpLdTarget (segAddr P "runtime.recordForPanic" + 40)
  (segWord P "runtime.recordForPanic" 10) (segWord P "runtime.recordForPanic" 11) 0
/-- `runtime.printBacklogIndex` (`int`): `ADRP`+`LDR` in `recordForPanic`. -/
def BI : Nat := adrpLdTarget (segAddr P "runtime.recordForPanic" + 140)
  (segWord P "runtime.recordForPanic" 35) (segWord P "runtime.recordForPanic" 36) 3
/-- `runtime.printBacklog` (`[512]byte`): `ADRP`+`ADD` in `recordForPanic`. -/
def BL : Nat := adrpLdTarget (segAddr P "runtime.recordForPanic" + 220)
  (segWord P "runtime.recordForPanic" 55) (segWord P "runtime.recordForPanic" 56) 0
/-- `runtime.debuglock` (`mutex`): `ADRP`+`ADD` in `printlock`. -/
def DL : Nat := adrpLdTarget (segAddr P "runtime.printlock" + 72)
  (segWord P "runtime.printlock" 18) (segWord P "runtime.printlock" 19) 0
/-- `runtime.overrideWrite` (`func`): `ADRP`+`LDR` in `write`. -/
def OW : Nat := adrpLdTarget (segAddr P "runtime.write" + 12)
  (segWord P "runtime.write" 3) (segWord P "runtime.write" 4) 3


/-- The string `"\n"` `printnl` prints (`ADRP`+`ADD`). -/
def NL : Nat := adrpLdTarget (segAddr P "runtime.printnl" + 24)
  (segWord P "runtime.printnl" 6) (segWord P "runtime.printnl" 7) 0
/-- The strings `"true"` and `"false"` `printbool` prints. -/
def TR : Nat := adrpLdTarget (segAddr P "runtime.printbool" + 28)
  (segWord P "runtime.printbool" 7) (segWord P "runtime.printbool" 8) 0
def FA : Nat := adrpLdTarget (segAddr P "runtime.printbool" + 48)
  (segWord P "runtime.printbool" 12) (segWord P "runtime.printbool" 13) 0

end PrintFn
