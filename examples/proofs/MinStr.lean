import Extracted

/-!
# `MinStr(s, t string) string`: Go's `min` on strings through `runtime.strmin`

**Guarantee.** For every implementation `impl` of `runtime.cmpstring` that meets its contract
(`Janus.Contracts.Cmpstring.CmpstringContract`: `X0` is the bytewise lexicographic comparison `strCmp`
of the two strings, `-1`/`0`/`1`, nothing else observable changes), every pair of strings
`s = (a, la)`, `t = (b, lb)` whose bytes are readable and outside the stack window, and every Go call
state whose stack-growth prologues (`MinStr`, `runtime.strmin`) fall through with the stack window
writable, the call of `example.com/basic.MinStr` in the linked program returns, obeys the ABI, and
returns `t` if `t < s` bytewise (`strCmp t s < 0`) and `s` otherwise: Go's `min(s, t)`, which
returns the first argument on a tie.

**What is executed and what is assumed.** `MinStr` and `runtime.strmin` (Go code in
`runtime/minmax.go`: `if y < x { return y }; return x`) are executed from the binary;
`runtime.cmpstring` (assembly) is left out with `--contract runtime.cmpstring`
(scripts/example-targets.sh) and assumed by the hypothesis. The contract is satisfiable
(`Janus.Contracts.CmpstringSat.cmpstring_satisfiable`), so the theorem is not vacuous. The proof shows that the stores of the two frames do not
touch the string bytes (`strCmp_writeLE`), and reads the sign of the result off the
branch on it (`cmp_msb`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Cmpstring

namespace Proof

theorem correctness (impl : List Segment) (a la b lb : BitVec 64)
    (hcmp : CmpstringContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, la, b, lb]
      (fun s => GuardOK s 80 ∧ StackOK s 144 40 ∧ StrOK s.mem a.toNat la.toNat ∧
        StrOK s.mem b.toNat lb.toNat ∧
        (la.toNat = 0 ∨ Disjoint a.toNat la.toNat (s.sp.toNat - 144) 184) ∧
        (lb.toNat = 0 ∨ Disjoint b.toNat lb.toNat (s.sp.toNat - 144) 184) ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 144) 184)
      (fun s s' => if strCmp s.mem b.toNat a.toNat lb.toNat la.toNat < 0
        then s'.regs 0 = b ∧ s'.regs 1 = lb else s'.regs 0 = a ∧ s'.regs 1 = la) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hsa, hsb, hda, hdb, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hgd hda hdb
  simp only [StrOK] at hsa hsb
  janus_run calls [hcmp]
  all_goals
    simp (disch := omega) only [strCmp_writeLE] at *
    have hc := strCmp_cases s.mem b.toNat a.toNat lb.toNat la.toNat
    simp only [cmp_msb _ hc] at *
    intro h; simp_all

/-! ## Non-vacuity witness

`janus_cmpstring_witness` (`Janus/Contracts/LiveStubStr.lean`) puts a concrete `runtime.cmpstring` (a byte
loop) at the contract address and proves the contract `hcmp` for it. Below, a concrete call state
of `MinStr("", "")` satisfies the whole precondition and the call returns what the theorem
describes. -/

namespace Witness

janus_cmpstring_witness

open CmpW (impl linked hcmp)

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 144, 184, true⟩, ⟨g0, 0x100, false⟩]⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [0, 0, 0, 0] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem pre : GuardOK s0 80 ∧ StackOK s0 144 40 ∧ StrOK s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat ∧
    StrOK s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat ∧
    ((0 : BitVec 64).toNat = 0 ∨ Disjoint (0 : BitVec 64).toNat (0 : BitVec 64).toNat (s0.sp.toNat - 144) 184) ∧
    ((0 : BitVec 64).toNat = 0 ∨ Disjoint (0 : BitVec 64).toNat (0 : BitVec 64).toNat (s0.sp.toNat - 144) 184) ∧
    Disjoint ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 144) 184 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, by simp [Disjoint, s0, sp0, g0]⟩

def cAddr : Nat := Extracted.program.contractAddr "runtime.cmpstring"

/-- The call state at `runtime.cmpstring`'s entry (`cmpstring("", "")`). -/
def wsCall : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 cAddr,
    flags := ⟨false, false, false, false⟩, mem := s0.mem }

theorem wsCall_pre : Janus.Contracts.Cmpstring.CmpstringPre 16 wsCall :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, Or.inl rfl, Or.inl rfl⟩

/-- The theorem fires: `MinStr("", "")` returns the first string. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    (if strCmp s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat (0 : BitVec 64).toNat (0 : BitVec 64).toNat < 0
      then s'.regs 0 = (0 : BitVec 64) ∧ s'.regs 1 = (0 : BitVec 64)
      else s'.regs 0 = (0 : BitVec 64) ∧ s'.regs 1 = (0 : BitVec 64)) :=
  correctness impl 0 0 0 0 hcmp ret hret s0 setup pre

/-- The hypotheses are satisfiable: a `runtime.cmpstring` meeting the contract (`hcmp`) and a call
state of `MinStr("", "")` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (ret : Nat) (s : State),
    CmpstringContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 0, 0, 0] s ∧
    (GuardOK s 80 ∧ StackOK s 144 40 ∧ StrOK s.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat ∧
      StrOK s.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat ∧
      ((0 : BitVec 64).toNat = 0 ∨ Disjoint (0 : BitVec 64).toNat (0 : BitVec 64).toNat (s.sp.toNat - 144) 184) ∧
      ((0 : BitVec 64).toNat = 0 ∨ Disjoint (0 : BitVec 64).toNat (0 : BitVec 64).toNat (s.sp.toNat - 144) 184) ∧
      Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 144) 184) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧
      Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
    (if strCmp s.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat (0 : BitVec 64).toNat (0 : BitVec 64).toNat < 0
      then s'.regs 0 = (0 : BitVec 64) ∧ s'.regs 1 = (0 : BitVec 64)
      else s'.regs 0 = (0 : BitVec 64) ∧ s'.regs 1 = (0 : BitVec 64)) :=
  ⟨impl, ret, s0, hcmp, hret, setup, pre, ⟨wsCall, rfl, wsCall_pre⟩, returns⟩

end Witness

end Proof
