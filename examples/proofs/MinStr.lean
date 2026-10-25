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

end Proof
