import Janus
import Extracted

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

def lit : Janus.DataSegment := Extracted.data[0]
theorem lit_mem : lit ∈ Extracted.program.data := List.mem_cons_self

theorem correctness (x : BitVec 64) (i : Int) (hi : truncInt binary64 x.toNat = some i)
    (h0 : 0 ≤ i) (h1 : i < 2 ^ 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ Extracted.program.DataLoaded s.mem ∧
        (s.xmm 0).toNat % 2 ^ 64 = x.toNat ∧ s.mxcsr = 0x1F80)
      (fun _ s' => (results 1 s').map BitVec.toNat = [i.toNat]) := by
  intro ret hret s hs ⟨hst, hdl, hx, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  have hrd := DataLoaded.accessible hdl lit_mem
  have hlen : lit.bytes.length = 8 := by decide
  have hb : lit.base = 0x4b5ef0 := rfl
  rw [hlen, hb] at hrd
  have hc := DataLoaded.readLE hdl lit_mem 0 8 (by rw [hlen])
  rw [hb, show listLE (lit.bytes.drop 0) 8 = 0x43e0000000000000 by decide] at hc
  janus64_run [hx, hm]
  all_goals trace_state
  all_goals sorry

end Proof
