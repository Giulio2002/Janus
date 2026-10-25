import Janus
import Extracted

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Contracts.Mem

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = x.toNat ∧
        (s.xmm 1).toNat % 2 ^ 64 = y.toNat ∧ GoMXCSR s)
      (fun _ s' => (s'.regs 0).toNat % 256 = (feq binary64 x.toNat y.toNat).toNat) := by
  intro ret hret s hs ⟨hst, ha, hb, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [ha, hb, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]

end Proof
