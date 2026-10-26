import Extracted
import PrintProofs.Arm64.MainBool
import PrintProofs.Arm64.Equiv

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

/-!
# `println(b)` for a `bool` (arm64)

```go
func PrintBool(b bool) { println(b) }
```

Lowered to `printlock(); printbool(b); printnl(); printunlock()`, all executed by the model from
the binary (contracts and kernel as in `PrintX`). **Guarantee (`correctness`)**: from every call
state ready to print (`Print.PrintReady`), with the read-only data loaded and outside `rt`, the call
returns and the trace gains what one `write(2, b)` per piece of `fmtBool b` (`"true"`/`"false"`),
`"\n"` may append. **`full_output`**: if fd 2 grew by as many bytes as the pieces hold, it grew by
exactly `fmtBool b ++ "\n"`.
-/

namespace Proof

abbrev P := Extracted.program

/-- The code the proofs of `PrintProofs.Arm64.Fn*` and `MainBool` are about, `PrintCode.program`, has the
same code as `Extracted.program` (the segments in another order): the guarantees transport. -/
theorem equiv : Program.Equiv P PrintCode.program :=
  ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, rfl⟩

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


theorem pk_eq : PK = PrintFn.PK := by decide +kernel
theorem bi_eq : BI = PrintFn.BI := by decide +kernel
theorem bl_eq : BL = PrintFn.BL := by decide +kernel
theorem dl_eq : DL = PrintFn.DL := by decide +kernel
theorem ow_eq : OW = PrintFn.OW := by decide +kernel
theorem nl_eq : NL = PrintFn.NL := by decide +kernel


set_option maxRecDepth 100000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (b : Bool) :
    EnsuresK (P.link impl) E Extracted.entry [BitVec.ofNat 64 b.toNat]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ P.DataLoaded s.mem ∧
        DataOutside P rt)
      (fun _ k _ k' => ∃ es, k' = k.appendTrace es ∧
        Emits 2 [Janus.Spec.Print.fmtBool b, [10#8]] es) := by
  have h := PrintFn.Bool.correctness impl rt E (Lock2Contract.of_equiv equiv impl rt 1024 hl) (Unlock2Contract.of_equiv equiv impl rt 1024 hu) (MemmoveContract.of_equiv equiv impl hmm) b
  refine Janus.Kernel.EnsuresK.of_equiv equiv impl h (fun s k hp => ?_) (fun _ _ _ _ hq => hq)
  rw [← pk_eq, ← bi_eq, ← bl_eq, ← ow_eq, ← dl_eq]
  exact ⟨hp.1, equiv.dataLoaded hp.2.1, Janus.Print.DataOutside.of_equiv equiv hp.2.2.1⟩


/-- **Full output**: if fd 2 grew by as many bytes as the pieces hold, it grew by exactly them. -/
theorem full_output (impl : List Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (b : Bool) :
    EnsuresK (P.link impl) E Extracted.entry [BitVec.ofNat 64 b.toNat]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ P.DataLoaded s.mem ∧
        DataOutside P rt)
      (fun s k _ k' => (k'.output 2).length = (k.output 2).length + (Janus.Spec.Print.fmtBool b ++ [10#8]).length →
        k'.output 2 = k.output 2 ++ (Janus.Spec.Print.fmtBool b ++ [10#8])) := by
  intro ret hret s k hs hpre
  refine (correctness impl rt E hl hu hmm b ret hret s k hs hpre).mono ?_ (fun _ _ h => h)
  rintro s' k' ⟨habi, es, rfl, hem⟩
  refine ⟨habi, fun hlen => ?_⟩
  have h := hem.full (k := k) (by simpa [List.append_assoc] using hlen)
  simpa [List.append_assoc] using h


namespace Witness

/-- The witness of `PrintProofs.Arm64.FnWitness`, over this program: the code at its contract
addresses, its read-only data in the witness memory, the witness call state. -/
abbrev ret : Nat := PrintFn.Witness.ret

def implAt : List Segment :=
  PrintFn.Witness.implAtOf (P.contractAddr "runtime.lock2") (P.contractAddr "runtime.unlock2")
    (P.contractAddr "runtime.memmove")

def wmem : Memory := PrintFn.Witness.wmemOf OW BL P.data

def wstate (r : Nat → W64) : State := PrintFn.Witness.wstateMem wmem Extracted.entry r

theorem implAt_eq : implAt = PrintFn.Witness.implAt := rfl

theorem wmem_eq : wmem = PrintFn.Witness.wmem := by
  unfold wmem PrintFn.Witness.wmem; rw [ow_eq, bl_eq]; rfl

theorem wstate_eq (r : Nat → W64) : wstate r = PrintFn.Witness.wstate PrintCode.entryPrintBool r := by
  unfold wstate PrintFn.Witness.wstate; rw [wmem_eq]; rfl


/-- All hypotheses of `correctness` hold together: the witness code at the three contract
addresses, the ranges `wrt`, an admissible return address and a call state ready to print. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (ret : Nat) (s : State),
    Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024 ∧
    Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024 ∧
    MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove") ∧
    RetAddr (P.link impl) ret ∧ CallSetup ((P.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 true.toNat] s ∧
    (PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ P.DataLoaded s.mem ∧ DataOutside P rt) := by
  obtain ⟨impl, rt, ret, s, h1, h2, h3, h4, h5, hp⟩ := PrintFn.Bool.Witness.nonvacuous
  refine ⟨impl, rt, ret, s, Lock2Contract.of_equiv equiv.symm impl rt 1024 h1, Unlock2Contract.of_equiv equiv.symm impl rt 1024 h2,
    MemmoveContract.of_equiv equiv.symm impl h3, equiv.symm.retAddr impl h4, ?_, ?_⟩
  · exact ⟨h5.pc, h5.lr, h5.args⟩
  · rw [pk_eq, bi_eq, bl_eq, ow_eq, dl_eq]
    exact ⟨hp.1, equiv.symm.dataLoaded hp.2.1, Janus.Print.DataOutside.of_equiv equiv.symm hp.2.2.1⟩


/-- So the guarantee is reached: from the witness state, for every kernel, `println(true)` returns and the trace gains what the two writes may append. -/
theorem returns (E : KEnv) (k : Kern) :
    ReturnsK ((Extracted.program.link implAt).withExit ret) E
      (fun s' k' => FFI.ABIReturnC (wstate (fun i => if i = 0 then BitVec.ofNat 64 true.toNat else 0)) s' ∧
        ∃ es, k' = k.appendTrace es ∧ Emits 2 [Janus.Spec.Print.fmtBool true, [10#8]] es)
      (fun _ _ => False) (wstate (fun i => if i = 0 then BitVec.ofNat 64 true.toNat else 0)) k := by
  rw [implAt_eq, wstate_eq, wmem_eq]
  exact (((equiv.sim PrintFn.Witness.implAt).withExit ret).symm).returnsK (PrintFn.Bool.Witness.returns E k)

end Witness

end Proof
