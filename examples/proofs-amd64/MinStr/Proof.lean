import Janus
import Extracted

/-!
# `MinStr(s, t string) string` on amd64: Go's `min` on strings through `runtime.strmin`

**Guarantee.** For every implementation `impl` of `runtime.cmpstring` that meets its contract
(`Janus.Contracts.Cmpstring.CmpstringContract64`: `RAX` is the bytewise lexicographic comparison `strCmp`
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
(`Janus.Contracts.CmpstringSatAmd64.cmpstring64_satisfiable`), so the theorem is not vacuous. The proof shows that the stores of the two frames do not
touch the string bytes (`strCmp_writeLE`), and reads the sign of the result off the
branch on it (`cmp_msb`).
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Cmpstring

theorem correctness (impl : List Janus.Amd64.Segment) (a la b lb : BitVec 64)
    (hcmp : CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, la, b, lb]
      (fun s => StackGuardOK s 64 ∧ StackWritable s 128 40 ∧ (s.regs 4).toNat % 8 = 0 ∧ StrOK s.mem a.toNat la.toNat ∧
        StrOK s.mem b.toNat lb.toNat ∧
        (la.toNat = 0 ∨ a.toNat + la.toNat ≤ (s.regs 4).toNat - 128 ∨ (s.regs 4).toNat + 40 ≤ a.toNat) ∧
        (lb.toNat = 0 ∨ b.toNat + lb.toNat ≤ (s.regs 4).toNat - 128 ∨ (s.regs 4).toNat + 40 ≤ b.toNat) ∧
        ((s.regs 4).toNat + 40 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 128))
      (fun s s' => if strCmp s.mem b.toNat a.toNat lb.toNat la.toNat < 0
        then s'.regs 0 = b ∧ s'.regs 3 = lb else s'.regs 0 = a ∧ s'.regs 3 = la) := by
  intro ret hret s hs ⟨hg, ⟨hle, hnw, hacc⟩, hal, hsa, hsb, hda, hdb, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr hal
  simp only [StrOK] at hsa hsb
  janus64_run calls [hcmp]
  all_goals
    simp (disch := omega) only [strCmp_writeLE] at *
    have hc := strCmp_cases s.mem b.toNat a.toNat lb.toNat la.toNat
    simp only [cmp_msb' _ hc] at *
    intro h; simp_all

/-! ## Non-vacuity witness

`janus64_cmpstring_witness` (`Janus/Contracts/LiveStubStr.lean`) puts a concrete `runtime.cmpstring` (a
byte loop) at the contract address and proves the contract `hcmp` for it. Below, a concrete call
state of `MinStr("", "")` satisfies the whole precondition and the call returns what the theorem
describes. -/

namespace Witness

janus64_cmpstring_witness

open CmpW (impl linked hcmp)

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000

def bytes (a : Nat) : Byte := if a = sp0 + 2 then 0x20 else 0

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 128, 128 + 40, true⟩, ⟨g0, 0x100, false⟩]⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [0, 0, 0, 0] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem pre : StackGuardOK s0 64 ∧ StackWritable s0 128 40 ∧ (s0.regs 4).toNat % 8 = 0 ∧
    StrOK s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat ∧
    StrOK s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat ∧
    ((0 : BitVec 64).toNat = 0 ∨ (0 : BitVec 64).toNat + (0 : BitVec 64).toNat ≤ (s0.regs 4).toNat - 128 ∨
      (s0.regs 4).toNat + 40 ≤ (0 : BitVec 64).toNat) ∧
    ((0 : BitVec 64).toNat = 0 ∨ (0 : BitVec 64).toNat + (0 : BitVec 64).toNat ≤ (s0.regs 4).toNat - 128 ∨
      (s0.regs 4).toNat + 40 ≤ (0 : BitVec 64).toNat) ∧
    ((s0.regs 4).toNat + 40 ≤ (s0.regs 14).toNat + 16 ∨ (s0.regs 14).toNat + 24 ≤ (s0.regs 4).toNat - 128) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, by decide, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
    Or.inl (by decide)⟩

/-- The hypotheses are satisfiable: a `runtime.cmpstring` meeting the contract (`hcmp`) and a call
state of `MinStr("", "")` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (ret : Nat) (s : Janus.Amd64.State),
    CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 0, 0, 0] s ∧
    (StackGuardOK s 64 ∧ StackWritable s 128 40 ∧ (s.regs 4).toNat % 8 = 0 ∧
      StrOK s.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat ∧
      StrOK s.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat ∧
      ((0 : BitVec 64).toNat = 0 ∨ (0 : BitVec 64).toNat + (0 : BitVec 64).toNat ≤ (s.regs 4).toNat - 128 ∨
        (s.regs 4).toNat + 40 ≤ (0 : BitVec 64).toNat) ∧
      ((0 : BitVec 64).toNat = 0 ∨ (0 : BitVec 64).toNat + (0 : BitVec 64).toNat ≤ (s.regs 4).toNat - 128 ∨
        (s.regs 4).toNat + 40 ≤ (0 : BitVec 64).toNat) ∧
      ((s.regs 4).toNat + 40 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 128)) :=
  ⟨impl, ret, s0, hcmp, hret, setup, pre⟩

/-- The theorem fires: `MinStr("", "")` returns the first string. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    (if strCmp s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat (0 : BitVec 64).toNat (0 : BitVec 64).toNat < 0
      then s'.regs 0 = (0 : BitVec 64) ∧ s'.regs 3 = (0 : BitVec 64)
      else s'.regs 0 = (0 : BitVec 64) ∧ s'.regs 3 = (0 : BitVec 64)) :=
  correctness impl 0 0 0 0 hcmp ret hret s0 setup pre

end Witness

end Proof
