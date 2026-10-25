import Janus
import Extracted

/-!
# `type:.eq.FKey` on amd64: the compiler-generated `==` of `struct { F float64; S string }`

As on arm64 (`UCOMISD`, `JNE`/`JP`, `MemAmd64.Memequal`).
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Mem Janus.Float
open Janus (MemFrame Outside outside_cons outside_nil outside_append)

namespace Proof

/-- Go's `==` on the `FKey`s at `p` and `q` in `m` (as on arm64). -/
def keyEq (m : Janus.Arm64.Memory) (p q : Nat) : Bool :=
  feq binary64 (m.readLE p 8) (m.readLE q 8) && strEq m (p + 8) (q + 8)

/-- The stack window of the equality function and its `memequal` call (amd64). -/
def window (d : Nat) (s : State) : List (Nat × Nat) := MemAmd64.callerWindow s d 40 8

/-- A key at `p` is an input (amd64). -/
def KeyInput (d : Nat) (s : State) (p : Nat) : Prop :=
  p + 24 ≤ 2 ^ 48 ∧ s.mem.accessible p 24 false = true ∧ Outside p 24 (window d s) ∧
    strPtr s.mem (p + 8) + strLen s.mem (p + 8) ≤ 2 ^ 48 ∧
    s.mem.accessible (strPtr s.mem (p + 8)) (strLen s.mem (p + 8)) false = true ∧
    Outside (strPtr s.mem (p + 8)) (strLen s.mem (p + 8)) (window d s)

theorem correctness (impl : List Segment) (d : Nat)
    (hmem : MemAmd64.Memequal (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memequal") d)
    (p q : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p, q]
      (fun s => MemAmd64.CallerOK s d 40 8 ∧ GoMXCSR s ∧ KeyInput d s p.toNat ∧ KeyInput d s q.toNat)
      (fun s s' => (s'.regs 0).toNat % 256 = (keyEq s.mem p.toNat q.toNat).toNat) := by
  intro ret hret s hs ⟨hc, hm, ⟨hpb, hpa, hpo, hpsb, hpsa, hpso⟩, ⟨hqb, hqa, hqo, hqsb, hqsa, hqso⟩⟩
  janus64_intro hs
  have hc' := hc
  obtain ⟨hg, hal, hdd, hb, hst, hog⟩ := hc'
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  simp only [window, MemAmd64.callerWindow, outside_cons, outside_nil, and_true] at hog hpo hqo hpso hqso
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hm8 : ∀ a, Janus.Arm64.Memory.readLE s.mem a 8 % 340282366920938463463374607431768211456 =
      Janus.Arm64.Memory.readLE s.mem a 8 :=
    fun a => Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Janus.Arm64.Memory.readLE_lt _ _ 8) (by decide))
  have hfe := MemAmd64.comis_feq false binary64 (s.mem.readLE p.toNat 8) (s.mem.readLE q.toNat 8)
  janus64_run [GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm] until [Extracted.program.contractAddr "runtime.memequal"]
  all_goals simp only [hm8] at *
  -- a false path: the floats are not `==` (`ZF` clear or `PF` set), or the lengths differ
  all_goals try (simp only [keyEq, ← hfe]; simp [hbr]; done)
  all_goals try (
    have hne : (strLen s.mem (p.toNat + 8) == strLen s.mem (q.toNat + 8)) = false := by
      have l1 := Janus.Arm64.Memory.readLE_lt s.mem (p.toNat + 16) 8
      have l2 := Janus.Arm64.Memory.readLE_lt s.mem (q.toNat + 16) 8
      simp only [strLen, Nat.add_assoc, Nat.reduceAdd, beq_eq_false_iff_ne, ne_eq]
      simp only [Nat.reducePow] at l1 l2
      omega
    simp [keyEq, strEq, hne]; done)
  -- the call of `memequal` on the two strings' bytes
  have hlen : Janus.Arm64.Memory.readLE s.mem (q.toNat + 16) 8 = Janus.Arm64.Memory.readLE s.mem (p.toNat + 16) 8 := by
    have l1 := Janus.Arm64.Memory.readLE_lt s.mem (p.toNat + 16) 8
    have l2 := Janus.Arm64.Memory.readLE_lt s.mem (q.toNat + 16) 8
    simp only [Nat.reducePow] at l1 l2
    rename_i hl _ _ _; omega
  have hf' : feq binary64 (s.mem.readLE p.toNat 8) (s.mem.readLE q.toNat 8) = true := by
    rw [← hfe]; rename_i _ _ hz; simp [hz, hbr]
  have hptrp : s.mem.readLE (p.toNat + 8) 8 = strPtr s.mem (p.toNat + 8) := rfl
  have hptrq : s.mem.readLE (q.toNat + 8) 8 = strPtr s.mem (q.toNat + 8) := rfl
  have hlp : s.mem.readLE (p.toNat + 16) 8 = strLen s.mem (p.toNat + 8) := rfl
  have hlq : strLen s.mem (q.toNat + 8) = strLen s.mem (p.toNat + 8) := hlen
  have hfw : MemFrame s.mem ((Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 4745333)
      (MemAmd64.callerWindow s d 40 8) := by
    simp only [MemAmd64.callerWindow]; janus_frame
  have hfw0 := hfw
  simp only [MemAmd64.callerWindow, outside_cons, outside_nil, and_true] at hfw
  refine Reaches.call (Summary.withExit hmem hret) rfl ⟨?_, ?_, ?_⟩ ?_
  · exact MemAmd64.EqPre.of_caller hc hfw0 (by simp [setRegF, hsp40]) (by simp [setRegF])
      (by simpa [setXmmF] using hs.zero) (by simpa using hs.df)
      (by simp [setRegF, hsp40, Janus.Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide)
  · refine MemAmd64.Input.of_caller hfw0 (by simp [setRegF, hsp40]) (by decide) (by omega) ?_ ?_ ?_ <;>
      dsimp only <;>
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hptrp, hlp,
        Nat.mod_eq_of_lt (show strPtr s.mem (p.toNat + 8) < 2 ^ 64 from Janus.Arm64.Memory.readLE_lt _ _ 8),
        Nat.mod_eq_of_lt (show strLen s.mem (p.toNat + 8) < 2 ^ 64 from Janus.Arm64.Memory.readLE_lt _ _ 8)]
    · exact hpsb
    · exact hpsa
    · simp only [MemAmd64.callerWindow, outside_cons, outside_nil, and_true]; exact hpso
  · refine MemAmd64.Input.of_caller hfw0 (by simp [setRegF, hsp40]) (by decide) (by omega) ?_ ?_ ?_ <;>
      dsimp only <;>
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hptrq, hlp, ← hlq,
        Nat.mod_eq_of_lt (show strPtr s.mem (q.toNat + 8) < 2 ^ 64 from Janus.Arm64.Memory.readLE_lt _ _ 8),
        Nat.mod_eq_of_lt (show strLen s.mem (q.toNat + 8) < 2 ^ 64 from Janus.Arm64.Memory.readLE_lt _ _ 8)]
    · exact hqsb
    · exact hqsa
    · simp only [MemAmd64.callerWindow, outside_cons, outside_nil, and_true]; exact hqso
  · intro s' hpc' ⟨r, x, y, fl, mx, m', hs', hmx, hfr, hres⟩
    subst hs'
    simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    janus64_run
    have hb1 := hfw.readLE (strPtr s.mem (p.toNat + 8)) (strLen s.mem (p.toNat + 8))
      (by simp only [outside_cons, outside_nil, and_true]; exact hpso)
    have hb2 := hfw.readLE (strPtr s.mem (q.toNat + 8)) (strLen s.mem (q.toNat + 8))
      (by simp only [outside_cons, outside_nil, and_true]; exact hqso)
    simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hptrp, hptrq, hlp,
      Nat.mod_eq_of_lt (show strPtr s.mem (p.toNat + 8) < 2 ^ 64 from Janus.Arm64.Memory.readLE_lt _ _ 8),
      Nat.mod_eq_of_lt (show strPtr s.mem (q.toNat + 8) < 2 ^ 64 from Janus.Arm64.Memory.readLE_lt _ _ 8),
      Nat.mod_eq_of_lt (show strLen s.mem (p.toNat + 8) < 2 ^ 64 from Janus.Arm64.Memory.readLE_lt _ _ 8)] at hres
    rw [hb1, ← hlq, hb2, hlq] at hres
    simp only [keyEq, strEq, hf', hlq, beq_self_eq_true, Bool.true_and]
    exact hres

end Proof
