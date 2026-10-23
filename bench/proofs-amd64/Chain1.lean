import Janus
import Extracted

/-!
# Benchmark `Chain1(x)` on amd64: a call chain five levels deep, with summaries

The amd64 version of `bench/proofs-arm64/Chain1.lean`: each callee is proved once as a
`Summary` (from any state at its entry, returning to the address on top of the stack,
`retAddrOf s`), using the summary of the next level (`janus64_run calls [...]` on a
`ReachesRet` goal). A summary says that `RAX` gets the result, `RSP` is popped past the
return address, `RBP` is restored, the flags change, and memory changes only in the stack
frames written (`MemFrame`: the saved `RBP`, the return addresses the nested `CALL`s push,
and `Chain2`'s spill into its caller's frame).
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The return-address slot of a callee: readable, holding an address below `2^47`. -/
abbrev RetSlot (s : State) : Prop :=
  s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47

/-- The precondition of a non-leaf level: `[RSP - below, RSP + above)` writable, the stack
guard `adj` bytes below `RSP`, the guard slot outside the stack window. -/
abbrev Pre (s : State) (below above adj : Nat) : Prop :=
  RetSlot s ∧ StackGuardOK s adj ∧ StackWritable s below above ∧
    ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - below ∨
      (s.regs 4).toNat + above ≤ (s.regs 14).toNat + 16)

/-- The state after a level returns: `RAX := r`, `RSP := RSP + 8`, flags and memory changed. -/
abbrev Ret (s s' : State) (r : W64) (rs : List (Nat × Nat)) : Prop :=
  ∃ f m, s' = { s with regs := setRegF (setRegF s.regs 0 r) 4 (s.regs 4 + 8), rip := retAddrOf s,
                       flags := f, mem := m } ∧ MemFrame s.mem m rs

/-- `Ret` with `RCX` clobbered too (`Chain2` reloads its spilled argument into it). -/
abbrev RetC (s s' : State) (r : W64) (rs : List (Nat × Nat)) : Prop :=
  ∃ v1 f m, s' = { s with regs := setRegF (setRegF (setRegF s.regs 0 r) 1 v1) 4 (s.regs 4 + 8),
                          rip := retAddrOf s, flags := f, mem := m } ∧ MemFrame s.mem m rs

theorem chain5 :
    Summary Extracted.program (segAddr Extracted.program "example.com/bench.Chain5")
      (fun s => RetSlot s)
      (fun s s' => s' = { s with regs := setRegF (setRegF s.regs 0 (s.regs 0 * 3 + 1)) 4
                                   (s.regs 4 + 8), rip := retAddrOf s }) := by
  intro s hpc ⟨h1, h2⟩
  janus64_run
  have : s.regs 0 + s.regs 0 <<< 1 + 1#64 = s.regs 0 * 3#64 + 1#64 := by bv_omega
  rw [this]

theorem chain4 :
    Summary Extracted.program (segAddr Extracted.program "example.com/bench.Chain4")
      (fun s => Pre s 24 8 0)
      (fun s s' => Ret s s' (s.regs 0 * 3 + 1 + 4) [((s.regs 4).toNat - 24, (s.regs 4).toNat)]) := by
  intro s hpc ⟨⟨h1, h2⟩, ⟨hg1, hg2, hg3⟩, ⟨hb, ha, hw⟩, hd⟩
  simp only [regSP, regG, stackguard0Offset, stackguard0] at *
  janus64_run calls [chain5]
  exact ⟨_, _, rfl, by janus_frame⟩

theorem chain3 :
    Summary Extracted.program (segAddr Extracted.program "example.com/bench.Chain3")
      (fun s => Pre s 48 8 24)
      (fun s s' => Ret s s' ((s.regs 0 * 3 + 1 + 4) ^^^ 3) [((s.regs 4).toNat - 48, (s.regs 4).toNat)]) := by
  intro s hpc ⟨⟨h1, h2⟩, ⟨hg1, hg2, hg3⟩, ⟨hb, ha, hw⟩, hd⟩
  simp only [regSP, regG, stackguard0Offset, stackguard0] at *
  janus64_run calls [chain4]
  exact ⟨_, _, rfl, by janus_frame⟩

theorem chain2 :
    Summary Extracted.program (segAddr Extracted.program "example.com/bench.Chain2")
      (fun s => Pre s 72 16 48)
      (fun s s' => RetC s s' (((s.regs 0 + 2) * 3 + 1 + 4 ^^^ 3) + s.regs 0)
        [((s.regs 4).toNat - 72, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)]) := by
  intro s hpc ⟨⟨h1, h2⟩, ⟨hg1, hg2, hg3⟩, ⟨hb, ha, hw⟩, hd⟩
  simp only [regSP, regG, stackguard0Offset, stackguard0] at *
  janus64_run calls [chain3]
  exact ⟨_, _, _, rfl, by janus_frame⟩

theorem correctness (x : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x] 1
      (fun s => StackGuardOK s 72 ∧ StackWritable s 96 8 ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 96 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16))
      (fun r => r = [((x + 2) * 3 + 1 + 4 ^^^ 3) + x + 1]) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, ha, hw⟩, hd⟩
  janus64_intro hs
  simp only [regSP, regG, stackguard0Offset, stackguard0] at *
  janus64_run calls [chain2]

end Proof
