import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

def u64Type : Nat := 0x96400
def cellType : Nat := 0x9b2c0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
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
      (fun s s' => True) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty1, hty2, hn, hn2, hok1, hok2, hok3, hinv, hbud⟩
  janus_intro hs
  janus_data hd [hw]
  janus_run until [Extracted.entry + 0x8c] calls [hmk.pos, hnew.pos, hwb]
  set_option trace.Meta.Tactic.simp.rewrite true in
  janus_run calls [hmk.pos, hnew.pos, hwb]
  done

end Proof
