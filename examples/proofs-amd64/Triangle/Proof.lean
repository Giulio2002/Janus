import Janus
import Extracted

/-! `example.com/basic.Triangle(n uint64) uint64` on amd64: an expression switch with
`fallthrough`, compiled to a jump table.

For every 64-bit `n` and every call state whose memory holds the function's read-only jump table
(`DataLoaded`), the result `RAX` is (`Tri`) the triangular number `n·(n+1)/2 = 0 + 1 + … + n` when `n ≤ 8`
and `0` otherwise. The nine dense cases become `CMPQ AX, $8; JA default` and an indirect jump
through a table of code addresses in `.rodata` (`LEAQ table(IP), CX; JMP 0(CX)(AX*8)`); the
`fallthrough` chain is straight-line code that each case enters at a different point. The proof
splits on the nine in-range values; for each, the jump target is read from the extracted table. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `v` is `0 + 1 + … + n` for `n ≤ 8`, and `0` otherwise. -/
def Tri (n v : BitVec 64) : Prop := v.toNat = if n.toNat ≤ 8 then n.toNat * (n.toNat + 1) / 2 else 0

theorem correctness (n : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [n] 1
      (fun s => StackWritable s 0 8 ∧ Extracted.program.DataLoaded s.mem)
      (fun r => ∃ v, r = [v] ∧ Tri n v) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, hd⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  by_cases hn : n.toNat ≤ 8
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 9 ∧ n = BitVec.ofNat 64 k :=
      ⟨n.toNat, by omega, by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt n.isLt]⟩
    janus64_cases hk
    all_goals
      janus64_data hd
      set_option maxRecDepth 4000 in janus64_run
      all_goals exact ⟨_, rfl, by unfold Tri; decide⟩
  · janus64_data hd
    janus64_run
    exact ⟨_, rfl, by unfold Tri; simp [hn]⟩

end Proof
