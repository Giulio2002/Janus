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

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def n : BitVec 64 := 4#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then n else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := withData Extracted.program.data wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [n] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩
set_option maxRecDepth 100000 in
theorem hpre : (fun s => StackWritable s 0 8 ∧ Extracted.program.DataLoaded s.mem) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [n] s ∧ (StackWritable s 0 8 ∧ Extracted.program.DataLoaded s.mem) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ∃ v, (results 1 s') = [v] ∧ Tri n v) :=
  ⟨ret, s0, n, hret, setup, hpre, correctness n ret hret s0 setup hpre⟩

end Witness

end Proof
