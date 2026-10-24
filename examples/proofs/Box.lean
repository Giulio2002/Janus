import Extracted

/-!
# `Box(x uint64) any` boxes `x` into an interface (arm64)

**Guarantee.** For every `x`, every model `R` of the interface runtime satisfying its laws, every
implementation of `runtime.convT64` satisfying the `ConvT64` contract
(`Janus/Contracts/Iface.lean`) and every Go call state in which the runtime is usable and has
`R.depth` bytes of stack below `Box`'s 32-byte frame (`CallerOK`), the call returns, obeys the
ABI, and the result is the interface value `(uint64Type, ptr)`: the type word is the address of
the `uint64` type descriptor the code loads (`ADRP`+`ADD`, recomputed from the extracted words),
and the data word `ptr` points to a readable 8-byte box in the runtime's memory holding `x`.
Memory changes only in the runtime's memory and the stack window, and the runtime stays usable.

**Assumptions (all in the statement).** `R` is *any* model satisfying `R.Laws`, and the code at
`runtime.convT64` is *any* code that behaves as `ConvT64` says (docs/RUNTIME-CONTRACTS.md,
"Interfaces").
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Iface

namespace Proof

/-- The type word of the result: the address `ADRP`+`ADD` at `Box+0x20` compute (`type:uint64`). -/
def uint64Type : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.Box" 8)
    (segWord Extracted.program "example.com/basic.Box" 9) 0

theorem correctness (impl : List Segment) (R : IfaceModel) (hl : R.Laws)
    (hconv : ConvT64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") R)
    (x : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [x]
      (fun s => CallerOK R s 32 0)
      (fun s s' => (s'.regs 0).toNat = uint64Type ∧ BoxHolds R s'.mem (s'.regs 1).toNat 8 x.toNat ∧
        MemFrame s.mem s'.mem (R.priv ++ [(s.sp.toNat - (R.depth + 32), s.sp.toNat)]) ∧
        R.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs hc
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : uint64Type
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.convT64"]
  refine Reaches.call (Summary.withExit hconv hret) rfl
    (RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg])
      (by simp [setReg]) (by decide) (by decide)) ?_
  intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hbox⟩
  subst hs'
  simp only [rtWrites, calleeStack, List.append_nil] at hfr
  janus_run
  refine ⟨hT.symm, ?_, ?_, ?_⟩
  · simpa [setReg, h_x0] using hbox
  · janus_frame
  · simpa [setReg] using henv'

end Proof
