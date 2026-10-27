import Extracted
import PrintProofs.Amd64.MainX
import PrintProofs.Amd64.Equiv

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

/-!
# `println("x =", x)` for a `uint64` (amd64)

```go
func PrintX(x uint64) { println("x =", x) }
```

The compiler lowers it to `printlock(); printstring("x = "); printuint(x); printnl();
printunlock()`. Every one of those runtime functions is executed by the model from the binary
(`printlock`/`printunlock`, `printstring`, `printuint` and `internal/strconv.formatBase10`,
`printnl`, `gwrite`, `recordForPanic`, `writeErr`/`write`/`write1` down to the `SVC #0`); the
contracts are `runtime.lock2`/`runtime.unlock2` (`Print.Lock2Contract`, `Print.Unlock2Contract`: the
mutex `debuglock`, taken when the M's print count is 0) and `runtime.memmove`
(`Print.MemmoveContract`: the copy into `printBacklog`). The kernel is the environment of
`Kernel.EnsuresK`: each `write(2, …)` may write any prefix of its buffer or fail.

**Guarantee (`correctness`).** From every Go call state ready to print (`Print.PrintReady`:
single-threaded, outside any other print, the stack window `[SP-1088, SP+16)` and the M/`g`/global
fields the print path touches, apart and outside the runtime-owned ranges `rt`), with the
program's read-only data loaded and outside `rt`, the call returns and the trace gains exactly
what one `write(2, b)` per piece `b` of `"x = "`, `decimal(x)`, `"\n"` may append
(`Print.Emits`). **`full_output`**: if the output of fd 2 grew by as many bytes as the three pieces
hold, it grew by exactly `"x = " ++ decimal(x) ++ "\n"`.
-/

namespace Proof

abbrev P := Extracted.program

/-- The code the proofs of `PrintProofs.Amd64.Fn*` and `MainX` are about, `PrintCode.program`, has the
same code as `Extracted.program` (the segments in another order): the guarantees transport. -/
theorem equiv : Janus.Amd64.Program.Equiv P PrintCode.program :=
  ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, rfl⟩

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


theorem pk_eq : PK = PrintFn.PK := by decide +kernel
theorem bi_eq : BI = PrintFn.BI := by decide +kernel
theorem bl_eq : BL = PrintFn.BL := by decide +kernel
theorem dl_eq : DL = PrintFn.DL := by decide +kernel
theorem ow_eq : OW = PrintFn.OW := by decide +kernel
theorem nl_eq : NL = PrintFn.NL := by decide +kernel


set_option maxRecDepth 100000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (x : BitVec 64) :
    Amd64.Kernel.EnsuresK (P.link impl) E Extracted.entry [x]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ Amd64.Program.DataLoaded P s.mem ∧
        DataOutside P rt)
      (fun _ k _ k' => ∃ es, k' = k.appendTrace es ∧
        Emits 2 [Janus.Spec.Print.ofString "x = ", Janus.Spec.Print.decimal x.toNat, [10#8]] es) := by
  have h := PrintFn.X.correctness impl rt E (Amd64.Print.Lock2Contract.of_equiv equiv impl rt 1024 hl) (Amd64.Print.Unlock2Contract.of_equiv equiv impl rt 1024 hu) (Amd64.Print.MemmoveContract.of_equiv equiv impl hmm) x
  refine Janus.Amd64.Kernel.EnsuresK.of_equiv equiv impl h (fun s k hp => ?_) (fun _ _ _ _ hq => hq)
  rw [← pk_eq, ← bi_eq, ← bl_eq, ← ow_eq, ← dl_eq]
  exact ⟨hp.1, equiv.dataLoaded hp.2.1, Janus.Amd64.Print.DataOutside.of_equiv equiv hp.2.2⟩


/-- **Full output**: if fd 2 grew by as many bytes as the pieces hold, it grew by exactly them. -/
theorem full_output (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (x : BitVec 64) :
    Amd64.Kernel.EnsuresK (P.link impl) E Extracted.entry [x]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ Amd64.Program.DataLoaded P s.mem ∧
        DataOutside P rt)
      (fun s k _ k' => (k'.output 2).length = (k.output 2).length + (Janus.Spec.Print.ofString "x = " ++ Janus.Spec.Print.decimal x.toNat ++ [10#8]).length →
        k'.output 2 = k.output 2 ++ (Janus.Spec.Print.ofString "x = " ++ Janus.Spec.Print.decimal x.toNat ++ [10#8])) := by
  intro ret hret s k hs hpre
  refine (correctness impl rt E hl hu hmm x ret hret s k hs hpre).mono ?_ (fun _ _ h => h)
  rintro s' k' ⟨habi, es, rfl, hem⟩
  refine ⟨habi, fun hlen => ?_⟩
  have h := hem.full (k := k) (by simpa [List.append_assoc] using hlen)
  simpa [List.append_assoc] using h


namespace Witness

/-- The witness of `PrintProofs.Amd64.FnWitness`, over this program: the code at its contract
addresses, its read-only data in the witness memory, the witness call state. -/
abbrev ret : Nat := PrintFn.Witness.ret

def implAt : List Amd64.Segment :=
  PrintFn.Witness.implAtOf (P.contractAddr "runtime.lock2") (P.contractAddr "runtime.unlock2")
    (P.contractAddr "runtime.memmove")

def wmem : Memory := PrintFn.Witness.wmemOf OW BL P.data

def wstate (r : Nat → W64) : State := PrintFn.Witness.wstateMem wmem Extracted.entry r

theorem implAt_eq : implAt = PrintFn.Witness.implAt := rfl

theorem wmem_eq : wmem = PrintFn.Witness.wmem := by
  unfold wmem PrintFn.Witness.wmem; rw [ow_eq, bl_eq]; rfl

theorem wstate_eq (r : Nat → W64) : wstate r = PrintFn.Witness.wstate PrintCode.entryPrintX r := by
  unfold wstate PrintFn.Witness.wstate; rw [wmem_eq]; rfl


/-- All hypotheses of `correctness` hold together: the witness code at the three contract
addresses, the ranges `wrt`, an admissible return address and a call state ready to print. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (ret : Nat) (s : State),
    Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024 ∧
    Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024 ∧
    MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove") ∧
    GoABI.RetAddr (P.link impl) ret ∧ GoABI.CallSetup ((P.link impl).withExit ret) Extracted.entry [42#64] s ∧
    (PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ Amd64.Program.DataLoaded P s.mem ∧ DataOutside P rt) := by
  obtain ⟨impl, rt, ret, s, h1, h2, h3, h4, h5, hp⟩ := PrintFn.X.Witness.nonvacuous
  refine ⟨impl, rt, ret, s, Amd64.Print.Lock2Contract.of_equiv equiv.symm impl rt 1024 h1, Amd64.Print.Unlock2Contract.of_equiv equiv.symm impl rt 1024 h2,
    Amd64.Print.MemmoveContract.of_equiv equiv.symm impl h3, equiv.symm.retAddr impl h4, ?_, ?_⟩
  · exact ⟨h5.rip, h5.ret, h5.zero, h5.len, h5.args, h5.df⟩
  · rw [pk_eq, bi_eq, bl_eq, ow_eq, dl_eq]
    exact ⟨hp.1, equiv.symm.dataLoaded hp.2.1, Janus.Amd64.Print.DataOutside.of_equiv equiv.symm hp.2.2⟩


/-- So the guarantee is reached: from the witness state, for every kernel, `println("x =", 42)` returns and the trace gains what the three writes may append. -/
theorem returns (E : KEnv) (k : Kern) :
    Amd64.Kernel.ReturnsK ((Extracted.program.link implAt).withExit ret) E
      (fun s' k' => ABIReturn (wstate (fun i => if i = 0 then 42#64 else 0)) s' ∧
        ∃ es, k' = k.appendTrace es ∧
          Emits 2 [Janus.Spec.Print.ofString "x = ", Janus.Spec.Print.decimal 42, [10#8]] es)
      (fun _ _ => False) (wstate (fun i => if i = 0 then 42#64 else 0)) k := by
  rw [implAt_eq, wstate_eq]
  
  exact (((equiv.sim PrintFn.Witness.implAt).withExit ret).symm).returnsK (PrintFn.X.Witness.returns E k)

end Witness

end Proof
