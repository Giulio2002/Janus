import Janus

/-! # `janus_run … join [pc, …]` / `janus64_run … join [pc, …]` (S12)

At the listed addresses the paths that arrive there are merged into one (`Common.tryMergeRel`): the registers/flags the paths gave
different values are generalised to fresh variables `jv₀ …`, and the merged goal keeps what distinguished the paths as one hypothesis,

  `hjoin : (P_1 ∧ jv₀ = a₀ ∧ …) ∨ (P_2 ∧ jv₀ = b₀ ∧ …)`,

`P_i` the branch conditions only path i had. The code after the join runs ONCE; its proof splits `hjoin`. Paths whose memories differ
(a store on one only) are not merged: they continue separately (still sound). Without `join` nothing changes. -/

namespace JanusTests.Join

/-! ### arm64: `x1 := if x = 0 then 2 else 1; x2 := x1 + 1` (a diamond that reconverges at `0x1014`) -/
namespace Arm
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

def seg : Segment := ⟨"f", 0x1000, [0xf100001f, 0x54000060, 0xd2800021, 0x14000002, 0xd2800041, 0x91000422, 0xd65f03c0]⟩
def P : Program := { segments := [seg], stubs := [], exitAddr := 0 }

/-- The continuation needs the branch fact: `x2 = x1 + 1` and `x1` depends on the arm. One continuation run, then `hjoin` splits. -/
theorem diamond (x : W64) :
    Ensures P 0x1000 [x] (fun _ => True) (fun _ s' => s'.regs 2 = if x = 0 then 3 else 2) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run join [0x1014]
  rcases hjoin with ⟨⟨hx, -⟩, rfl, -⟩ | ⟨⟨hx, -⟩, rfl, -⟩ <;> simp_all [BitVec.toNat_eq]

/-- Both arms reach `0x1014`: exactly one goal is left after the join (two without it). -/
example (x : W64) :
    Ensures P 0x1000 [x] (fun _ => True) (fun _ s' => s'.regs 2 = if x = 0 then 3 else 2) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run join [0x1014]
  run_tac do
    unless (← Lean.Elab.Tactic.getGoals).length == 1 do Lean.throwError "expected one merged goal"
  rcases hjoin with ⟨⟨hx, -⟩, rfl, -⟩ | ⟨⟨hx, -⟩, rfl, -⟩ <;> simp_all [BitVec.toNat_eq]

/- The disjunct carries the branch fact: the global merger (`janus.merge`, which drops the branch conditions) leaves a goal that
no longer knows which arm it is on, so the same proof fails. -/
set_option janus.merge true in
example (x : W64) : True := by
  fail_if_success
    have : Ensures P 0x1000 [x] (fun _ => True) (fun _ s' => s'.regs 2 = if x = 0 then 3 else 2) := by
      intro ret hret s hs _
      janus_intro hs
      janus_run
      all_goals simp_all [BitVec.toNat_eq]
  trivial

/-- A store on one path only: the memories differ (`antiUnify` never generalises a memory), the paths are NOT merged and continue
separately; the proof still goes through. -/
def seg2 : Segment := ⟨"g", 0x1000, [0xf100001f, 0x54000040, 0xf9000041, 0xd65f03c0]⟩
def P2 : Program := { segments := [seg2], stubs := [], exitAddr := 0 }

theorem storeOne (x v p : W64) :
    Ensures P2 0x1000 [x, v, p] (fun s => s.mem.accessible p.toNat 8 true = true ∧ p.toNat % 8 = 0)
      (fun _ s' => s'.regs 0 = x) := by
  intro ret hret s hs ⟨hp, hal⟩
  janus_intro hs
  janus_run join [0x100c]

end Arm

/-! ### amd64: `rbx := if rax = 0 then 2 else 1; rbx := rbx + 1` (reconverges at `0x1011`) -/
namespace Amd
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

def seg : Janus.Amd64.Segment :=
  ⟨"f", 0x1000, [0x48, 0x85, 0xc0, 0x74, 0x07, 0xbb, 0x01, 0x00, 0x00, 0x00, 0xeb, 0x05, 0xbb, 0x02, 0x00, 0x00, 0x00,
    0x48, 0x83, 0xc3, 0x01, 0xc3]⟩
def P : Janus.Amd64.Program := { segments := [seg], stubs := [], exitAddr := 0 }

theorem diamond (x : W64) :
    Ensures P 0x1000 [x] (fun s => StackWritable s 0 8) (fun _ s' => s'.regs 3 = if x = 0 then 3 else 2) := by
  intro ret hret s hs ⟨hb, ha, hw⟩
  janus64_intro hs
  simp only [regSP] at hb ha hw
  janus64_run join [0x1011]
  run_tac do
    unless (← Lean.Elab.Tactic.getGoals).length == 1 do Lean.throwError "expected one merged goal"
  rcases hjoin with ⟨⟨hx, -⟩, rfl, -⟩ | ⟨⟨hx, -⟩, rfl, -⟩ <;> simp_all [BitVec.toNat_eq]

/-- A store on one path only: not merged, still proved. -/
def seg2 : Janus.Amd64.Segment := ⟨"g", 0x1000, [0x48, 0x85, 0xc0, 0x74, 0x03, 0x48, 0x89, 0x0b, 0xc3]⟩
def P2 : Janus.Amd64.Program := { segments := [seg2], stubs := [], exitAddr := 0 }

theorem storeOne (x p v : W64) :
    Ensures P2 0x1000 [x, p, v] (fun s => StackWritable s 0 8 ∧ s.mem.accessible p.toNat 8 true = true ∧
      (p.toNat + 8 ≤ (s.regs regSP).toNat ∨ (s.regs regSP).toNat + 8 ≤ p.toNat))
      (fun _ s' => s'.regs 0 = x) := by
  intro ret hret s hs ⟨⟨hb, ha, hw⟩, hp, hd⟩
  janus64_intro hs
  simp only [regSP] at hb ha hw hd
  janus64_run join [0x1008]

/-- Branch pruning knows that a read is below `2^64`: `ja` after `cmp rcx, [rbx]` is refuted by `x ≤ y` alone
(the flag condition is `(2^64 - y + x) % 2^64 ≠ 0`, which `omega` cannot refute for unbounded naturals). -/
def seg3 : Janus.Amd64.Segment :=
  ⟨"h", 0x1000, [0x48, 0x8b, 0x08, 0x48, 0x3b, 0x0b, 0x77, 0x01, 0xc3, 0xba, 0x01, 0x00, 0x00, 0x00, 0xc3]⟩
def P3 : Janus.Amd64.Program := { segments := [seg3], stubs := [], exitAddr := 0 }

theorem pruneLimb (p q : W64) :
    Ensures P3 0x1000 [p, q] (fun s => StackWritable s 0 8 ∧ s.mem.accessible p.toNat 8 false = true ∧
      s.mem.accessible q.toNat 8 false = true ∧ s.mem.readLE p.toNat 8 ≤ s.mem.readLE q.toNat 8 ∧
      s.mem.readLE q.toNat 8 ≠ 0)
      (fun s s' => s'.regs 2 = s.regs 2) := by
  intro ret hret s hs ⟨⟨hb, ha, hw⟩, hp, hq, hle, hne⟩
  janus64_intro hs
  simp only [regSP] at hb ha hw
  janus64_run

end Amd

end JanusTests.Join
