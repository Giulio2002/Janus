import Janus.Spec.SoftFloat
import Janus.Contracts.MapAmd64

/-!
# amd64 helpers for the soft-float and runtime-function proofs

`LeafRet64`: the return of an amd64 leaf function under the Go ABI, the shape of the callee
summaries the proofs of `runtime.f32to64`, `runtime.fpack64`, … use (`Janus.Spec.SoftFloat` has
the arm64 one).
-/

namespace Janus.Spec.SoftFloat

open Janus.Amd64 Janus.Amd64.Tactic

/-- The return of an amd64 leaf function that obeys the Go ABI from `s` to `s'` with result `v`
in `RAX`: back at the return address `[RSP]` with `RSP + 8`, `RBP`, `R14`, memory and the vector
registers unchanged, every other general register and the flags arbitrary. -/
abbrev LeafRet64 (s s' : State) (v : BitVec 64) : Prop :=
  ∃ (r : Nat → BitVec 64) (f : Flags),
    s' = { s with regs := Contracts.MapAmd64.keepABI s.regs r, flags := f, rip := retAddrOf s } ∧ r 0 = v

theorem leafRet64_of (s s' : State) (v : BitVec 64) (hrip : s'.rip = retAddrOf s)
    (h4 : s'.regs 4 = s.regs 4 + 8#64) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hm : s'.mem = s.mem) (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (hmx : s'.mxcsr = s.mxcsr) (h0 : s'.regs 0 = v) : LeafRet64 s s' v := by
  refine ⟨s'.regs, s'.flags, ?_, h0⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx⟩ := s'
  simp only at hrip h4 h5 h14 hm hx hy hfs hdf hmx ⊢
  subst hrip hm hx hy hfs hdf hmx
  congr
  funext i
  simp only [Contracts.MapAmd64.keepABI]
  split
  · rename_i hi; subst hi; exact h4
  · split
    · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
    · rfl

end Janus.Spec.SoftFloat
