import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

def u64Type : Nat := 0x96400
def cellType : Nat := 0x9b2c0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (n x : BitVec 64)
    (hmk : MakesliceLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hnew : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Ensures (Extracted.program.link impl) Extracted.entry [n, x]
      (fun s => GuardOK s 4160 ∧ StackOK s 4168 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4168) 4192 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4168) 4192 ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
        s.mem.accessible 0x15dc20 4 false = true ∧ Outside 0x96400 16 R.rt ∧ Outside 0x9b2c0 16 R.rt ∧
        0 < n.toNat ∧ n.toNat < 2 ^ 40 ∧
        R.ok (Extracted.program.contractAddr "runtime.makeslice") [0x96400, n.toNat, n.toNat] ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [0x9b2c0] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
        R.inv b [] (s.regs 28).toNat (view R.rt [] s.mem) ∧
        blockSize (8 * n.toNat) true + 16 + blockSize (8 * n.toNat) true ≤ b)
      (fun s s' => ∃ pa pb pc : Nat, (s'.regs 0).toNat = pa ∧ (s'.regs 3).toNat = pb ∧ (s'.regs 6).toNat = pc ∧
        s'.regs 1 = n ∧ s'.regs 2 = n ∧ s'.regs 4 = n ∧ s'.regs 5 = n ∧
        InRanges pa (blockSize (8 * n.toNat) true) R.rt ∧ InRanges pb (blockSize (8 * n.toNat) true) R.rt ∧
        InRanges pc 16 R.rt ∧
        Apart pa (blockSize (8 * n.toNat) true) pb (blockSize (8 * n.toNat) true) ∧
        Apart pa (blockSize (8 * n.toNat) true) pc 16 ∧ Apart pb (blockSize (8 * n.toNat) true) pc 16 ∧
        s'.mem.readLE pa 8 = x.toNat ∧ s'.mem.readLE pc 8 = pb ∧
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4168, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty1, hty2, hn, hn2, hok1, hok2, hok3, hinv, hbud⟩
  janus_intro hs
  janus_data hd [hw]
  janus_run calls [hmk.pos, hnew.pos, hwb]
  all_goals (refine ⟨_, _, _, rfl, rfl, rfl, ?_⟩)
  all_goals (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals janus_split_and
  all_goals first | janus_live_disch | (unfold Apart; janus_apart) | janus_simp | janus_frame
  all_goals done

end Proof
