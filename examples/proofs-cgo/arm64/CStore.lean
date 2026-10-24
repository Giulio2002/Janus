import Extracted

/-!
# `void c_store(uint64_t *p, uint64_t v)` (C, arm64): `*p = v`

**Guarantee.** For every pointer `p` to 8 writable bytes (below `2^48`) and every value `v`,
every AAPCS64 call of the gcc-compiled `c_store` returns without faulting, restores `SP` and
`X19`–`X29`, and the only change to memory is the word at `p`, which becomes `v`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic

namespace Proof

theorem correctness (p v : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p, v]
      (fun s => p.toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 8 true = true)
      (fun s s' => s'.mem = s.mem.writeLE p.toNat 8 v.toNat) := by
  intro ret hret s hs ⟨hb, hacc⟩
  janus_intro hs.call
  janus_run

end Proof
