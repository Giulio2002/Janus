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
(`Janus.Contracts.CmpstringSatAmd64.cmpstring_satisfiable`), so the theorem is not vacuous. The proof shows that the stores of the two frames do not
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

end Proof
