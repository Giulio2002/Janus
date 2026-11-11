import Janus
open Janus Janus.Tactic Janus.Contracts

/-! Round ALLOC (v0.3.1), kernel-checked: the allocation contracts' preconditions exclude a call
state in which the type descriptor lies inside the callee's stack window.

The pinned go1.26.10 `runtime.makeslice` pushes its frame before it reads `et.Size_` (arm64
`MOVD.W R30, -48(RSP)`, `MOVD R29, -8(RSP)`; amd64 `PUSHQ BP`), so in such a state the real
runtime does not do what the contract says (`typSize s.mem et`). Before v0.3.1 the preconditions
held there (`Old*Pre` below are the pre-v0.3.1 definitions, verbatim), so every theorem assuming
the contract was vacuous for the real binary. Now the precondition is false there: a proof that
needs `et` (or `growslice`'s old elements) inside the callee's window has no state to talk about.

Rows: `*_old_holds` (the old precondition holds in a window state: the gap), `*_excluded` (the new
one does not, for EVERY state with the descriptor in the window), `*_ctl` (a rodata descriptor
satisfies it: the contracts are still satisfiable, see also the `*_satisfiable` witnesses). -/

namespace RAlloc

/-- Pre-v0.3.1 `NewobjectPre`/`MakeslicePre`/`GrowsliceArgs`/`MallocgcPre` (arm64). -/
def OldNewobjectPre (stack : Nat) (s : Janus.Arm64.State) : Prop :=
  CallOK s stack 1 ∧ TypeOK s.mem (s.regs 0).toNat ∧ typSize s.mem (s.regs 0).toNat ≤ maxAlloc
def OldMakeslicePre (stack : Nat) (s : Janus.Arm64.State) : Prop :=
  CallOK s stack 3 ∧ TypeOK s.mem (s.regs 0).toNat ∧
    (s.regs 1).toNat ≤ (s.regs 2).toNat ∧ (s.regs 2).toNat < 2 ^ 63 ∧
    typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat ≤ maxAlloc

/-! ### arm64: any state with the descriptor in the window falsifies the new preconditions -/

section arm64
variable (stack : Nat) (s : Janus.Arm64.State)

theorem inwin1 {et n : Nat} (h1 : s.sp.toNat - stack ≤ et) (h2 : et + 16 ≤ s.sp.toNat - 8) :
    ¬ Outside et 16 (calleeStack s stack n) := by
  simp only [calleeStack, outside_cons, outside_nil, and_true]; omega

theorem newobject_excluded (h1 : s.sp.toNat - stack ≤ (s.regs 0).toNat)
    (h2 : (s.regs 0).toNat + 16 ≤ s.sp.toNat - 8) : ¬ NewobjectPre stack s :=
  fun h => inwin1 stack s h1 h2 h.2.2.2
theorem makeslice_excluded (h1 : s.sp.toNat - stack ≤ (s.regs 0).toNat)
    (h2 : (s.regs 0).toNat + 16 ≤ s.sp.toNat - 8) : ¬ MakeslicePre stack s :=
  fun h => inwin1 stack s h1 h2 h.2.2.2.2.2
theorem growslice_excluded (h1 : s.sp.toNat - stack ≤ (s.regs 4).toNat)
    (h2 : (s.regs 4).toNat + 16 ≤ s.sp.toNat - 8) : ¬ GrowslicePre stack s :=
  fun h => inwin1 stack s h1 h2 h.1.2.2.2.2.2.2.2.2
theorem mallocgc_excluded (hT : (s.regs 1).toNat ≠ 0) (h1 : s.sp.toNat - stack ≤ (s.regs 1).toNat)
    (h2 : (s.regs 1).toNat + 16 ≤ s.sp.toNat - 8) : ¬ MallocgcPre stack s := fun h => by
  rcases h.2.2 with h0 | ⟨-, -, ho⟩
  · exact hT h0
  · exact inwin1 stack s h1 h2 ho
/-- the old elements of `growslice` (`oldLen > 0`) inside the window falsify the precondition -/
theorem growslice_old_excluded (hlen : 0 < (s.regs 1).toNat - (s.regs 3).toNat)
    (h1 : s.sp.toNat - stack ≤ (s.regs 0).toNat)
    (h2 : (s.regs 0).toNat + 8 * ((s.regs 1).toNat - (s.regs 3).toNat) ≤ s.sp.toNat - 8) :
    ¬ GrowslicePre stack s := fun h => by
  have ho := (h.2 hlen).2.2
  simp only [calleeStack, outside_cons, outside_nil, and_true] at ho
  omega
end arm64

/-! ### amd64 -/

section amd64
variable (stack : Nat) (s : Janus.Amd64.State)

theorem inwin1_64 {et n : Nat} (h1 : (s.regs 4).toNat - stack ≤ et) (h2 : et + 16 ≤ (s.regs 4).toNat) :
    ¬ Outside et 16 (calleeStack64 s stack n) := by
  simp only [calleeStack64, outside_cons, outside_nil, and_true]; omega

theorem newobject64_excluded (h1 : (s.regs 4).toNat - stack ≤ (s.regs 0).toNat)
    (h2 : (s.regs 0).toNat + 16 ≤ (s.regs 4).toNat) : ¬ NewobjectPre64 stack s :=
  fun h => inwin1_64 stack s h1 h2 h.2.2.2
theorem makeslice64_excluded (h1 : (s.regs 4).toNat - stack ≤ (s.regs 0).toNat)
    (h2 : (s.regs 0).toNat + 16 ≤ (s.regs 4).toNat) : ¬ MakeslicePre64 stack s :=
  fun h => inwin1_64 stack s h1 h2 h.2.2.2.2.2
theorem growslice64_excluded (h1 : (s.regs 4).toNat - stack ≤ (s.regs 6).toNat)
    (h2 : (s.regs 6).toNat + 16 ≤ (s.regs 4).toNat) : ¬ GrowslicePre64 stack s :=
  fun h => inwin1_64 stack s h1 h2 h.1.2.2.2.2.2.2.2.2
theorem mallocgc64_excluded (hT : (s.regs 3).toNat ≠ 0) (h1 : (s.regs 4).toNat - stack ≤ (s.regs 3).toNat)
    (h2 : (s.regs 3).toNat + 16 ≤ (s.regs 4).toNat) : ¬ MallocgcPre64 stack s := fun h => by
  rcases h.2.2 with h0 | ⟨-, -, ho⟩
  · exact hT h0
  · exact inwin1_64 stack s h1 h2 ho
theorem growslice64_old_excluded (hlen : 0 < (s.regs 3).toNat - (s.regs 7).toNat)
    (h1 : (s.regs 4).toNat - stack ≤ (s.regs 0).toNat)
    (h2 : (s.regs 0).toNat + 8 * ((s.regs 3).toNat - (s.regs 7).toNat) ≤ (s.regs 4).toNat) :
    ¬ GrowslicePre64 stack s := fun h => by
  have ho := (h.2 hlen).2.2
  simp only [calleeStack64, outside_cons, outside_nil, and_true] at ho
  omega
end amd64

/-! ### the gap was real: a concrete window state met the old precondition (arm64 newobject) -/

def SP : Nat := 0x100000
/-- the descriptor at `SP - 56` (where `makeslice`'s first push writes), inside the stack window -/
def ET : Nat := SP - 56
def wmem : Janus.Arm64.Memory :=
  ⟨fun a => if a = ET then 16 else 0, [⟨SP - 4096, 4096 + 16, true⟩]⟩
def wst : Janus.Arm64.State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 ET else if i = 30 then BitVec.ofNat 64 0x1000 else 0,
    sp := BitVec.ofNat 64 SP, pc := BitVec.ofNat 64 0x100000, flags := ⟨false, false, false, false⟩, mem := wmem }

theorem newobject_old_holds : OldNewobjectPre 4096 wst := by
  simp only [OldNewobjectPre, CallOK, TypeOK, wst, wmem, ET, SP, typSize, maxAlloc]
  decide
theorem newobject_window_excluded : ¬ NewobjectPre 4096 wst :=
  newobject_excluded 4096 wst (by simp only [wst, SP, ET]; decide) (by simp only [wst, SP, ET]; decide)

/-! ### control: the same descriptor in rodata satisfies the new precondition (see also
`AllocSat.newobject_satisfiable` and the `*Live_satisfiable` witnesses of `Janus.Contracts.LiveSat`) -/

def TY : Nat := 0x30000
def cmem : Janus.Arm64.Memory :=
  ⟨fun a => if a = TY then 16 else 0, [⟨SP - 4096, 4096 + 16, true⟩, ⟨TY, 16, false⟩]⟩
def cst : Janus.Arm64.State := { wst with regs := fun i => if i = 0 then BitVec.ofNat 64 TY else if i = 30 then BitVec.ofNat 64 0x1000 else 0, mem := cmem }

theorem newobject_ctl : NewobjectPre 4096 cst := by
  simp only [NewobjectPre, CallOK, TypeOK, cst, wst, cmem, TY, SP, typSize, maxAlloc, calleeStack, outside_cons, outside_nil]
  decide

end RAlloc
