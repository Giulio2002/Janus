import JanusASL.Proofs.AddSubImmClass
import JanusASL.Proofs.AddSubCarry
import JanusASL.Proofs.CondSel
import JanusASL.Proofs.CondCmp
import JanusASL.Proofs.Madd
import JanusASL.Proofs.AddSubShifted
import JanusASL.Proofs.LogicalShifted
import JanusASL.Proofs.ShiftV
import JanusASL.Proofs.MoveWide
import JanusASL.Proofs.Maddl
import JanusASL.Proofs.Mulh
import JanusASL.Proofs.Div
import JanusASL.Proofs.LogicalImm
import JanusASL.Proofs.Bitfield
import JanusASL.Proofs.Extr
import JanusASL.Proofs.PcRel
import JanusASL.Proofs.AddSubExt
import JanusASL.Proofs.DP1
import JanusASL.Proofs.Rev
import JanusASL.Proofs.Branch
import JanusASL.Proofs.Run
import JanusASL.Proofs.Examples
import JanusASL.Proofs.LdStUImm
import JanusASL.Proofs.LdStImm9
import JanusASL.Proofs.LdStReg
import JanusASL.Proofs.LdStLit
import JanusASL.Proofs.LdStPair
import JanusASL.Proofs.LdStExcl
import JanusASL.Proofs.LdStAtomicCls
import JanusASL.Proofs.Witness
import JanusASL.Proofs.FP.FCmpCls
import JanusASL.Proofs.FP.Round64
import JanusASL.Proofs.FP.Prim3
import JanusASL.Proofs.FP.VSet
import JanusASL.Proofs.FP.Exec
import JanusASL.Proofs.FP.Unpack2
import JanusASL.Proofs.FP.Div
import JanusASL.Proofs.FP.AgreeArith
import JanusASL.Proofs.FP.AgreeCcmp
import JanusASL.Proofs.FPDecodeB
import JanusASL.Proofs.FP.Sqrt
import JanusASL.Proofs.FP.Exec2
import JanusASL.Proofs.FPDecodeA
import JanusASL.Proofs.FPChain.Basic

/-! # JanusASL proofs: Janus' `step` against the generated ASL, per encoding class

Each `*_agree` theorem states: for every word of the encoding class and every pair of states
related by `Rel` (the Sail state holds Janus' X0-X30, SP, PC and NZCV, at EL0 with SP_EL0), Janus'
`step` succeeds, the generated ASL step (`janus_step`) completes with outcome `Janus_OK`, and the
results are related again. See docs/ASL.md. -/
