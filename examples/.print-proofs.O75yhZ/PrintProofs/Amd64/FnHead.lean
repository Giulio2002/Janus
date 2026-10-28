import PrintProofs.Amd64.Code

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

namespace PrintFn

abbrev P := PrintCode.program

/-! ## The runtime's print globals (`.noptrbss`/`.bss`), at the addresses the code computes
(the RIP-relative operands) -/

/-- `runtime.panicking` (`atomic.Uint32`): `MOVL panicking(SB), AX` in `recordForPanic`. -/
def PK : Nat := ripTarget P (segAddr P "runtime.recordForPanic" + 0x26)
/-- `runtime.printBacklogIndex` (`int`): `MOVQ printBacklogIndex(SB), CX` in `recordForPanic`. -/
def BI : Nat := ripTarget P (segAddr P "runtime.recordForPanic" + 0xa6)
/-- `runtime.printBacklog` (`[512]byte`): `LEAQ printBacklog(SB), R10` in `recordForPanic`. -/
def BL : Nat := ripTarget P (segAddr P "runtime.recordForPanic" + 0xcb)
/-- `runtime.debuglock` (`mutex`): `LEAQ debuglock(SB), AX` in `printlock`. -/
def DL : Nat := ripTarget P (segAddr P "runtime.printlock" + 0x33)
/-- `runtime.overrideWrite` (`func`): `MOVQ overrideWrite(SB), DX` in `write`. -/
def OW : Nat := ripTarget P (segAddr P "runtime.write" + 0x8)

/-- The string `"\n"` `printnl` prints (`LEAQ`). -/
def NL : Nat := ripTarget P (segAddr P "runtime.printnl" + 0xe)
/-- The strings `"true"` and `"false"` `printbool` prints. -/
def TR : Nat := ripTarget P (segAddr P "runtime.printbool" + 0x12)
def FA : Nat := ripTarget P (segAddr P "runtime.printbool" + 0x27)

end PrintFn
