import Extracted
import PrintProofs.Amd64.MainStr
import PrintProofs.Amd64.Equiv

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

/-!
# `println(s)` for a `string` (amd64)

```go
func PrintStr(s string) { println(s) }
```

Lowered to `printlock(); printstring(s); printnl(); printunlock()`, all executed by the model from
the binary (contracts and kernel as in `PrintX`). **Guarantee (`correctness`)**: from every call
state ready to print (`Print.PrintReady`), with the read-only data loaded and outside `rt`, and a
string `(ptr, len)` (`len < 2^31`) whose bytes are readable, outside `rt` and apart from the stack
window, the M's fields and the print backlog, the call returns and the trace gains what one
`write(2, b)` per piece of `s` (its bytes in memory at the call), `"\n"` may append.
**`full_output`**: if fd 2 grew by `len + 1` bytes, it grew by exactly the bytes of `s` and `"\n"`.
-/

namespace Proof

abbrev P := Extracted.program

/-- The code the proofs of `PrintProofs.Amd64.Fn*` and `MainStr` are about, `PrintCode.program`, has the
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
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (ptr len : BitVec 64) :
    Amd64.Kernel.EnsuresK (P.link impl) E Extracted.entry [ptr, len]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 24 256 s ∧ Amd64.Program.DataLoaded P s.mem ∧
        DataOutside P rt ∧ s.mem.accessible ptr.toNat len.toNat false = true ∧
        ptr.toNat + len.toNat ≤ 2 ^ 48 ∧ len.toNat < 2 ^ 31 ∧ Outside ptr.toNat len.toNat rt ∧
        Sep ptr.toNat len.toNat [((s.regs 4).toNat - 1088, 1112),
          (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264, 16), (BI, 8), (BL, 512)])
      (fun s k _ k' => ∃ es, k' = k.appendTrace es ∧
        Emits 2 [readBytes s.mem ptr.toNat len.toNat, [10#8]] es) := by
  have h := PrintFn.Str.correctness impl rt E (Amd64.Print.Lock2Contract.of_equiv equiv impl rt 1024 hl) (Amd64.Print.Unlock2Contract.of_equiv equiv impl rt 1024 hu) (Amd64.Print.MemmoveContract.of_equiv equiv impl hmm) ptr len
  refine Janus.Amd64.Kernel.EnsuresK.of_equiv equiv impl h (fun s k hp => ?_) (fun _ _ _ _ hq => hq)
  rw [← pk_eq, ← bi_eq, ← bl_eq, ← ow_eq, ← dl_eq]
  exact ⟨hp.1, equiv.dataLoaded hp.2.1, Janus.Amd64.Print.DataOutside.of_equiv equiv hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2⟩


/-- **Full output**: if fd 2 grew by as many bytes as the pieces hold, it grew by exactly them. -/
theorem full_output (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (ptr len : BitVec 64) :
    Amd64.Kernel.EnsuresK (P.link impl) E Extracted.entry [ptr, len]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 24 256 s ∧ Amd64.Program.DataLoaded P s.mem ∧
        DataOutside P rt ∧ s.mem.accessible ptr.toNat len.toNat false = true ∧
        ptr.toNat + len.toNat ≤ 2 ^ 48 ∧ len.toNat < 2 ^ 31 ∧ Outside ptr.toNat len.toNat rt ∧
        Sep ptr.toNat len.toNat [((s.regs 4).toNat - 1088, 1112),
          (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264, 16), (BI, 8), (BL, 512)])
      (fun s k _ k' => (k'.output 2).length = (k.output 2).length + (readBytes s.mem ptr.toNat len.toNat ++ [10#8]).length →
        k'.output 2 = k.output 2 ++ (readBytes s.mem ptr.toNat len.toNat ++ [10#8])) := by
  intro ret hret s k hs hpre
  refine (correctness impl rt E hl hu hmm ptr len ret hret s k hs hpre).mono ?_ (fun _ _ h => h)
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

theorem wstate_eq (r : Nat → W64) : wstate r = PrintFn.Witness.wstate PrintCode.entryPrintStr r := by
  unfold wstate PrintFn.Witness.wstate; rw [wmem_eq]; rfl


/-- All hypotheses of `correctness` hold together: the witness code at the three contract
addresses, the ranges `wrt`, an admissible return address and a call state ready to print. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (ret : Nat) (s : State),
    Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024 ∧
    Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024 ∧
    MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove") ∧
    GoABI.RetAddr (P.link impl) ret ∧ GoABI.CallSetup ((P.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 NL, 1#64] s ∧
    (PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 24 256 s ∧ Amd64.Program.DataLoaded P s.mem ∧
      DataOutside P rt ∧ s.mem.accessible (BitVec.ofNat 64 NL : BitVec 64).toNat (1#64 : BitVec 64).toNat false = true ∧
      (BitVec.ofNat 64 NL : BitVec 64).toNat + (1#64 : BitVec 64).toNat ≤ 2 ^ 48 ∧ (1#64 : BitVec 64).toNat < 2 ^ 31 ∧
      Outside (BitVec.ofNat 64 NL : BitVec 64).toNat (1#64 : BitVec 64).toNat rt ∧
      Sep (BitVec.ofNat 64 NL : BitVec 64).toNat (1#64 : BitVec 64).toNat [((s.regs 4).toNat - 1088, 1112),
        (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264, 16), (BI, 8), (BL, 512)]) := by
  obtain ⟨impl, rt, ret, s, h1, h2, h3, h4, h5, hp⟩ := PrintFn.Str.Witness.nonvacuous
  refine ⟨impl, rt, ret, s, Amd64.Print.Lock2Contract.of_equiv equiv.symm impl rt 1024 h1, Amd64.Print.Unlock2Contract.of_equiv equiv.symm impl rt 1024 h2,
    Amd64.Print.MemmoveContract.of_equiv equiv.symm impl h3, equiv.symm.retAddr impl h4, ?_, ?_⟩
  · rw [nl_eq]; exact ⟨h5.rip, h5.ret, h5.zero, h5.len, h5.args, h5.df⟩
  · rw [pk_eq, bi_eq, bl_eq, ow_eq, dl_eq, nl_eq]
    exact ⟨hp.1, equiv.symm.dataLoaded hp.2.1, Janus.Amd64.Print.DataOutside.of_equiv equiv.symm hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2⟩


/-- So the guarantee is reached: from the witness state, for every kernel, `println(s)` for the one-byte string at the program's `"\n"` returns and the trace gains what the two writes may append. -/
theorem returns (E : KEnv) (k : Kern) :
    Amd64.Kernel.ReturnsK ((Extracted.program.link implAt).withExit ret) E
      (fun s' k' => ABIReturn (wstate (fun i => if i = 0 then BitVec.ofNat 64 NL else if i = 3 then 1#64 else 0)) s' ∧
        ∃ es, k' = k.appendTrace es ∧
          Emits 2 [readBytes wmem NL 1, [10#8]] es)
      (fun _ _ => False) (wstate (fun i => if i = 0 then BitVec.ofNat 64 NL else if i = 3 then 1#64 else 0)) k := by
  rw [implAt_eq, wstate_eq]
  rw [nl_eq, wmem_eq]
  exact (((equiv.sim PrintFn.Witness.implAt).withExit ret).symm).returnsK (PrintFn.Str.Witness.returns E k)

end Witness

end Proof
