import Extracted

/-!
# Benchmark `Chain1(x)` on arm64: a call chain five levels deep, with summaries

```go
func Chain5(x uint64) uint64 { return x*3 + 1 }
func Chain4(x uint64) uint64 { return Chain5(x) + 4 }
func Chain3(x uint64) uint64 { return Chain4(x) ^ 3 }
func Chain2(x uint64) uint64 { return Chain3(x+2) + x }
func Chain1(x uint64) uint64 { return Chain2(x) + 1 }
```

Each callee is proved once as a `Summary` from any state at its entry, using the summary of the
next level (`janus_run calls [...]` on a `ReachesRet` goal), and `Chain1` is proved with the
summary of `Chain2`; no instruction of a callee is executed twice. A summary's postcondition
says which registers change (`X0`, and the scratch `X1`/`X16` as existentials), that `SP`, `X29`,
`X30` are restored, and that memory changes only in the stack frames written (`MemFrame`). The
preconditions grow with the depth: `StackOK s below above` covers the frames of all deeper
levels, and `GuardOK s adj` the stack-guard checks of the deeper prologues.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- A well-formed return address in `X30`. -/
abbrev LR (s : State) : Prop := (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56

/-- The precondition of a non-leaf level: `[SP - below, SP + above)` writable, the stack guard
`adj` bytes below `SP`, and the guard slot outside the stack window. -/
abbrev Pre (s : State) (below above adj : Nat) : Prop :=
  LR s ∧ GuardOK s adj ∧ StackOK s below above ∧
    Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - below) (below + above)

/-- The state after a level returns: `X0 := r`, `X1`/`X16`/flags/memory changed. -/
abbrev Ret (s s' : State) (r : W64) (rs : List (Nat × Nat)) : Prop :=
  ∃ v1 v16 f m, s' = { s with regs := setReg (setReg (setReg s.regs 0 r) 1 v1) 16 v16,
                              pc := s.regs 30, flags := f, mem := m } ∧ MemFrame s.mem m rs

theorem chain5 :
    Summary Extracted.program (segAddr Extracted.program "example.com/bench.Chain5")
      (fun s => LR s)
      (fun s s' => ∃ v, s' = { s with regs := setReg (setReg s.regs 0 (s.regs 0 * 3 + 1)) 1 v,
                                      pc := s.regs 30 }) := by
  intro s hpc ⟨h1, h2⟩
  janus_run
  have : s.regs 0 + s.regs 0 <<< 1 + 1#64 = s.regs 0 * 3#64 + 1#64 := by bv_omega
  exact ⟨_, by rw [this]⟩

theorem chain4 :
    Summary Extracted.program (segAddr Extracted.program "example.com/bench.Chain4")
      (fun s => Pre s 40 0 0)
      (fun s s' => Ret s s' (s.regs 0 * 3 + 1 + 4) [(s.sp.toNat - 40, s.sp.toNat - 24)]) := by
  intro s hpc ⟨⟨h1, h2⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd⟩
  simp only [Disjoint] at hd
  janus_run calls [chain5]
  exact ⟨_, _, _, _, rfl, by janus_frame⟩

theorem chain3 :
    Summary Extracted.program (segAddr Extracted.program "example.com/bench.Chain3")
      (fun s => Pre s 72 0 32)
      (fun s s' => Ret s s' ((s.regs 0 * 3 + 1 + 4) ^^^ 3) [(s.sp.toNat - 72, s.sp.toNat - 24)]) := by
  intro s hpc ⟨⟨h1, h2⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd⟩
  simp only [Disjoint] at hd
  janus_run calls [chain4]
  exact ⟨_, _, _, _, rfl, by janus_frame⟩

theorem chain2 :
    Summary Extracted.program (segAddr Extracted.program "example.com/bench.Chain2")
      (fun s => Pre s 104 16 64)
      (fun s s' => Ret s s' (((s.regs 0 + 2) * 3 + 1 + 4 ^^^ 3) + s.regs 0)
        [(s.sp.toNat - 104, s.sp.toNat - 24), (s.sp.toNat + 8, s.sp.toNat + 16)]) := by
  intro s hpc ⟨⟨h1, h2⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd⟩
  simp only [Disjoint] at hd
  janus_run calls [chain3]
  exact ⟨_, _, _, _, rfl, by janus_frame⟩

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 96 ∧ StackOK s 136 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 136) 136)
      (fun _ s' => s'.regs 0 = (((x + 2) * 3 + 1 + 4 ^^^ 3) + x) + 1) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd⟩
  janus_intro hs
  simp only [Disjoint] at hd
  janus_run calls [chain2]

end Proof
