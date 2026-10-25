import Extracted

/-!
# `StrEq(s, t string) bool`: `s == t` (arm64)

**Guarantee.** For all strings `s = (p1, l1)`, `t = (p2, l2)`, every implementation of
`runtime.memequal` satisfying `Mem.Memequal` with stack bound `d`, and every Go call state with
`d` bytes of stack below `StrEq`'s 16-byte frame (`CallerOK`) whose strings' bytes are readable
and outside that window, the call returns, obeys the ABI, and the `bool` result is Go's `s == t`:
equal lengths and equal bytes. Different lengths answer `false` without a call; otherwise the
compiled code calls `memequal(p1, p2, l1)`.

**Assumptions.** The `memequal` contract (hypothesis `hmem`), pinned to the runtime's code. On
arm64 the machine code of `runtime.memequal` is itself proved to meet it
(`examples/proofs/AlgMemequal.lean`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Mem

namespace Proof

/-- The precondition: `CallerOK` for `memequal` with stack bound `d` from `StrEq`'s 16-byte frame,
with `StrEq`'s four argument spill slots (up to `SP + 40`), and the two strings' bytes readable
and outside that window. -/
def pre (d : Nat) (p1 l1 p2 l2 : BitVec 64) (s : State) : Prop :=
  CallerOK s d 16 40 ∧ Ptr s.mem p1 l1.toNat false ∧ Ptr s.mem p2 l2.toNat false ∧
    Outside p1.toNat l1.toNat (callerWindow s d 16 40) ∧ Outside p2.toNat l2.toNat (callerWindow s d 16 40)

theorem correctness (impl : List Segment) (d : Nat)
    (hmem : Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d)
    (p1 l1 p2 l2 : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p1, l1, p2, l2] (pre d p1 l1 p2 l2)
      (fun s s' => (s'.regs 0).toNat % 256 =
        (l1 == l2 && s.mem.readLE p1.toNat l1.toNat == s.mem.readLE p2.toNat l2.toNat).toNat) := by
  intro ret hret s hs ⟨hc, ⟨hP1, hP1'⟩, ⟨hP2, hP2'⟩, ho1, ho2⟩
  have hc' := hc
  obtain ⟨⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hog⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  simp only [outside_cons, outside_nil, and_true] at hog
  by_cases hl : l1 = l2
  · subst hl
    janus_run until [Extracted.program.contractAddr "runtime.memequal"]
    refine Reaches.call (Summary.withExit hmem hret) rfl
      ⟨EqPre.of_caller hc (by simp only [callerWindow]; janus_frame) (by simp; omega) (by simp [setReg])
        (by simp [setReg]) (by simp [setReg]) (by decide) (by decide),
       Input.of_caller (s := s) (d := d) (frame := 16) (above := 40)
         (by simp only [callerWindow]; janus_frame) (by simp; omega) (by decide) (by omega)
         (by simpa [setReg, h_x0] using hP1') (by simpa [setReg, h_x0] using hP1)
         (by simpa [setReg, h_x0] using ho1),
       Input.of_caller (s := s) (d := d) (frame := 16) (above := 40)
         (by simp only [callerWindow]; janus_frame) (by simp; omega) (by decide) (by omega)
         (by simpa [setReg, h_x2] using hP2') (by simpa [setReg, h_x2] using hP2)
         (by simpa [setReg, h_x2] using ho2)⟩ ?_
    intro s' hpc' ⟨r, v, fl, fs, m', hs', hfr, hres⟩
    subst hs'
    have hsp : (s.sp - 16#64).toNat = s.sp.toNat - 16 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; try simp
    try simp only [calleeStack, hsp] at hfr
    try simp only [BoolRes, setReg_apply, reduceIte, Nat.reduceEqDiff, h_x0, h_x2] at hres
    janus_run
    have hfw : MemFrame s.mem ((((s.mem.writeLE (BitVec.toNat s.sp - 16) 8 ret).writeLE
        (BitVec.toNat s.sp - 24) 8 (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 8) 8
        p1.toNat).writeLE (BitVec.toNat s.sp + 24) 8 p2.toNat) (callerWindow s d 16 40) := by
      simp only [callerWindow]; janus_frame
    rw [hfw.readLE _ _ ho1, hfw.readLE _ _ ho2] at hres
    simpa using hres
  · janus_run
    simp [beq_false_of_ne hl]

end Proof
