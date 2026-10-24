import Janus
import Extracted

/-!
# `Box(x uint64) any` boxes `x` into an interface (amd64)

**Guarantee.** For every `x`, every model `R` of the interface runtime satisfying its laws, every
implementation of `runtime.convT64` satisfying the `ConvT64` contract
(`Janus/Contracts/IfaceAmd64.lean`) and every Go call state in which the runtime is usable and
has `R.depth` bytes of stack below `Box`'s frame (`CallerOK`), the call returns, obeys the ABI,
and the result is the interface value `(uint64Type, ptr)` in `RAX`, `RBX`: the type word is the
address of the `uint64` type descriptor the code loads (`LEAQ`, recomputed from the extracted
bytes), and `ptr` points to a readable 8-byte box in the runtime's memory holding `x`. Memory
changes only in the runtime's memory and the stack window, and the runtime stays usable.

**Assumptions (all in the statement).** `R` is *any* model satisfying `R.Laws`, and the code at
`runtime.convT64` is *any* code that behaves as `ConvT64` says (docs/RUNTIME-CONTRACTS.md,
"Interfaces").
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Type Janus.Contracts.Iface Janus.Contracts.IfaceAmd64

namespace Proof

/-- The type word of the result: the RIP-relative `LEAQ` at `Box+0x16` (`type:uint64`). -/
def uint64Type : Nat := ripTarget Extracted.program (Extracted.entry + 0x16)

theorem correctness (impl : List Janus.Amd64.Segment) (R : IfaceModel) (hl : R.Laws)
    (hconv : ConvT64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") R)
    (x : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [x]
      (fun s => CallerOK R s 24 8)
      (fun s s' => (s'.regs 0).toNat = uint64Type ∧ BoxHolds R s'.mem (s'.regs 3).toNat 8 x.toNat ∧
        MemFrame s.mem s'.mem (R.priv ++ [((s.regs 4).toNat - (R.depth + 24), (s.regs 4).toNat + 8)]) ∧
        R.Env s'.mem (s.regs 14)) := by
  intro ret hret s hs hc
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : uint64Type
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp24 : (s.regs 4 - 24#64).toNat = (s.regs 4).toNat - 24 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.convT64"]
  refine Reaches.call (Summary.withExit hconv hret) rfl
    (RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp24]) (by simp [setRegF])
      (by simpa using hs.zero) (by simpa using hs.df)
      (by simp [setRegF, hsp24, Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide)) ?_
  intro s' hpc' ⟨r, x', y, fl, m', hs', hfr, henv', hbox⟩
  subst hs'
  simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, List.append_nil, setRegF,
    reduceIte, Nat.reduceEqDiff, hsp24] at hfr
  janus64_run
  refine ⟨hT.symm, ?_, ?_, ?_⟩
  · simpa [setRegF, h_a0] using hbox
  · janus_frame
  · simpa [setRegF] using henv'

end Proof
