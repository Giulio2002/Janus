import Extracted

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
