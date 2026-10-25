import Extracted

/-!
# `type:.eq.FKey`: the compiler-generated `==` of `struct { F float64; S string }` (arm64)

**Guarantee.** With a `memequal` satisfying `Mem.Memequal`, for keys at `p` and `q` readable with
their strings: the result is `keyEq`, the floats `feq` (`FCMPD`) and the strings equal (lengths
inline, bytes by `memequal`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Mem
  Janus.Float

namespace Proof

/-- Go's `==` on the `FKey`s at `p` and `q` in `m`: the floats `feq`, then the strings. -/
def keyEq (m : Memory) (p q : Nat) : Bool :=
  feq binary64 (m.readLE p 8) (m.readLE q 8) && strEq m (p + 8) (q + 8)

/-- The stack window of the equality function and its `memequal` call. -/
def window (d : Nat) (s : State) : List (Nat × Nat) := callerWindow s d 16 0

/-- A key at `p` is an input: its 24 bytes and its string's bytes readable and outside the
window. -/
def KeyInput (d : Nat) (s : State) (p : Nat) : Prop :=
  p + 24 ≤ 2 ^ 48 ∧ s.mem.accessible p 24 false = true ∧ Outside p 24 (window d s) ∧
    strPtr s.mem (p + 8) + strLen s.mem (p + 8) ≤ 2 ^ 48 ∧
    s.mem.accessible (strPtr s.mem (p + 8)) (strLen s.mem (p + 8)) false = true ∧
    Outside (strPtr s.mem (p + 8)) (strLen s.mem (p + 8)) (window d s)

theorem correctness (impl : List Segment) (d : Nat)
    (hmem : Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d)
    (p q : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p, q]
      (fun s => CallerOK s d 16 0 ∧ s.fpcr = 0 ∧ KeyInput d s p.toNat ∧ KeyInput d s q.toNat)
      (fun s s' => (s'.regs 0).toNat % 256 = (keyEq s.mem p.toNat q.toNat).toNat) := by
  intro ret hret s hs ⟨hc, hfp, ⟨hpb, hpa, hpo, hpsb, hpsa, hpso⟩, ⟨hqb, hqa, hqo, hqsb, hqsa, hqso⟩⟩
  have hc' := hc
  obtain ⟨⟨hg1, hg2, hg3⟩, hal, hd8, hdd, hb, hst, hog⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  simp only [window, callerWindow, outside_cons, outside_nil, and_true] at hog hpo hqo hpso hqso
  have hm : ∀ a, s.mem.readLE a 8 % 340282366920938463463374607431768211456 = s.mem.readLE a 8 :=
    fun a => Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Memory.readLE_lt _ _ 8) (by decide))
  have hsp : (s.sp - 16#64).toNat = s.sp.toNat - 16 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; try simp
  janus_run until [Extracted.program.contractAddr "runtime.memequal"]
  all_goals simp only [hm] at *
  · simp [keyEq, hbr]
  · rename_i hlen
    have hptrp : s.mem.readLE (p.toNat + 8) 8 = strPtr s.mem (p.toNat + 8) := rfl
    have hptrq : s.mem.readLE (q.toNat + 8) 8 = strPtr s.mem (q.toNat + 8) := rfl
    have hlp : s.mem.readLE (p.toNat + 16) 8 = strLen s.mem (p.toNat + 8) := rfl
    have hfw : MemFrame s.mem ((s.mem.writeLE (BitVec.toNat s.sp - 16) 8 ret).writeLE
        (BitVec.toNat s.sp - 24) 8 (BitVec.toNat (s.regs 29))) (callerWindow s d 16 0) := by
      simp only [callerWindow]; janus_frame
    have hfw0 := hfw
    simp only [callerWindow, outside_cons, outside_nil, and_true] at hfw
    refine Reaches.call (Summary.withExit hmem hret) rfl ⟨?_, ?_, ?_⟩ ?_
    · exact EqPre.of_caller hc hfw0 (by simp [hsp]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
        (by decide) (by decide)
    · refine Input.of_caller (s := s) (d := d) (frame := 16) (above := 0) hfw0 (by simp [hsp]) (by decide)
        (by omega) ?_ ?_ ?_ <;> dsimp only <;>
        simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hptrp, hlp, hlen,
          Nat.mod_eq_of_lt (show strPtr s.mem (p.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8),
          Nat.mod_eq_of_lt (show strLen s.mem (p.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8)]
      · exact hpsb
      · exact hpsa
      · simp only [callerWindow, outside_cons, outside_nil, and_true]; exact hpso
    · have hlq : strLen s.mem (p.toNat + 8) = strLen s.mem (q.toNat + 8) := hlen.symm
      refine Input.of_caller (s := s) (d := d) (frame := 16) (above := 0) hfw0 (by simp [hsp]) (by decide)
        (by omega) ?_ ?_ ?_ <;> dsimp only <;>
        simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hptrq, hlp, hlq,
          Nat.mod_eq_of_lt (show strPtr s.mem (q.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8),
          Nat.mod_eq_of_lt (show strLen s.mem (q.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8)]
      · exact hqsb
      · exact hqsa
      · simp only [callerWindow, outside_cons, outside_nil, and_true]; exact hqso
    · intro s' hpc' ⟨r, v, fl, fs, m', hs', hfr, hres⟩
      subst hs'
      simp only [calleeStack, hsp] at hfr
      janus_run
      have hb1 := hfw.readLE (strPtr s.mem (p.toNat + 8)) (strLen s.mem (p.toNat + 8))
        (by simp only [outside_cons, outside_nil, and_true]; exact hpso)
      have hb2 := hfw.readLE (strPtr s.mem (q.toNat + 8)) (strLen s.mem (q.toNat + 8))
        (by simp only [outside_cons, outside_nil, and_true]; exact hqso)
      have hlq : strLen s.mem (q.toNat + 8) = strLen s.mem (p.toNat + 8) := hlen
      simp only [BoolRes, setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hptrp, hptrq, hlp,
        Nat.mod_eq_of_lt (show strPtr s.mem (p.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8),
        Nat.mod_eq_of_lt (show strPtr s.mem (q.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8),
        Nat.mod_eq_of_lt (show strLen s.mem (p.toNat + 8) < 2 ^ 64 from Memory.readLE_lt _ _ 8)] at hres
      rw [hb1, ← hlq, hb2, hlq] at hres
      have hf' : feq binary64 (s.mem.readLE p.toNat 8) (s.mem.readLE q.toNat 8) = true := by
        simpa using hbr
      simp only [keyEq, strEq, hf', hlq, beq_self_eq_true, Bool.true_and]
      exact hres
  · rename_i hlen
    have hne : (strLen s.mem (p.toNat + 8) == strLen s.mem (q.toNat + 8)) = false := by
      simp only [strLen, Nat.add_assoc, Nat.reduceAdd, beq_eq_false_iff_ne, ne_eq]
      exact fun h => hlen h.symm
    simp [keyEq, strEq, hne]

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The `memequal` model code behind a branch (as in `StrEq`), and a call comparing the key at
`STR - 8` (the float `+0`, then the string header `STR` = the 8 bytes at `VAL`) with itself:
`EqFKey` returns `true`. -/

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

/-- The key at `STR - 8`. -/
def k : BitVec 64 := BitVec.ofNat 64 (STR - 8)

def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 1 then k
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [k, k] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem keyInput : KeyInput 64 s0 k.toNat := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, ?_⟩ <;>
    simp only [window, callerWindow, outside_cons, outside_nil, and_true] <;> decide

theorem hpre : CallerOK s0 64 16 0 ∧ s0.fpcr = 0 ∧ KeyInput 64 s0 k.toNat ∧ KeyInput 64 s0 k.toNat :=
  ⟨⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    by simp only [outside_cons, outside_nil, and_true]; decide⟩, rfl, keyInput, keyInput⟩

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Segment) (d ret : Nat) (s : State) (p q : BitVec 64),
    Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [p, q] s ∧
    (CallerOK s d 16 0 ∧ s.fpcr = 0 ∧ KeyInput d s p.toNat ∧ KeyInput d s q.toNat) :=
  ⟨implAt, 64, ret, s0, k, k, model 64, hret, setup, hpre⟩

/-- So the guarantee is reached: the key equals itself. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness implAt 64 (model 64) k k ret hret s0 setup hpre).mono ?_
  intro s' h
  exact ⟨h.1, by rw [h.2]; decide⟩

end Witness

end Proof
