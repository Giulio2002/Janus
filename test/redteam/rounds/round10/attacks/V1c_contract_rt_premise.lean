import Extracted

/-! Round 10 V1c: as V1b, with `rt` a variable of the statement pinned to `[]` by a premise. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The address of `Pair`'s type descriptor, the argument NewPair passes to `runtime.newobject`
(the `ADRP` + `ADD` pair at `NewPair+0x20`), recomputed from the extracted words. -/
def pairType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.NewPair" 8)
    (segWord Extracted.program "example.com/basic.NewPair" 9) 0

@[janus_exec, janus_post] theorem rtView_nil_writeLE (m : Memory) (a n v : Nat) :
    rtView [] (m.writeLE a n v) = rtView [] m := rtView_writeLE trivial

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (hrt : rt = []) (H : RtReady) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun _ s' => s'.regs 0 = 42) := by
  subst hrt
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : pairType
  rw [h_pt] at hH
  janus_data hd [hw]
  janus_run until [Extracted.entry + 0x34] calls [hnew.pos]
  exfalso
  obtain ⟨r, hr, -⟩ := ‹InRanges _ 16 []›
  simp at hr

end Proof
