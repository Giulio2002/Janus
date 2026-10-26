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

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

Code that meets the `Memequal` contract for every stack bound (`MemSat.memequalCode`, a byte loop,
at `IfaceSat.A0`, reached from `runtime.memequal`'s address by a branch), an admissible return
address and a call state comparing the 8-byte string `VAL` with itself through two headers:
`correctness` applies, and `StrEq` returns `true`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MemSat

def cAddr : Nat := Extracted.program.contractAddr "runtime.memequal"
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := memequalCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model (d : Nat) : Memequal (Extracted.program.link implAt) cAddr d := by
  have hA : Memequal (Extracted.program.link implAt) A0 d := by
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (memequal_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨⟨g1, g2, g3⟩, hcall, hgo⟩, i1, i2⟩ := hpre
  exact hA _ rfl ⟨⟨⟨g1, g2, g3⟩, hcall, hgo⟩, i1, i2⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- The string `VAL` (8 bytes), twice. -/
def p : BitVec 64 := BitVec.ofNat 64 VAL
def l : BitVec 64 := 8#64

def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 2 then p else if i = 1 ∨ i = 3 then l
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [p, l, p, l] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem hpre : pre 64 p l p l s0 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, ?_⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_⟩ <;>
    simp only [callerWindow, outside_cons, outside_nil, and_true] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Segment) (d ret : Nat) (s : State) (p1 l1 p2 l2 : BitVec 64),
    Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [p1, l1, p2, l2] s ∧
    pre d p1 l1 p2 l2 s :=
  ⟨implAt, 64, ret, s0, p, l, p, l, model 64, hret, setup, hpre⟩

/-- So the guarantee is reached: a string equals itself. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness implAt 64 (model 64) p l p l ret hret s0 setup hpre).mono ?_
  intro s' h
  exact ⟨h.1, by rw [h.2]; simp⟩

end Witness

end Proof
