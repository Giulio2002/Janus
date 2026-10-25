import Janus
import Extracted

/-!
# `runtime.strequal` (amd64) meets the `Strequal` contract, with `runtime.memequal` as a contract

**Guarantee.** For every stack bound `d` of `runtime.memequal` and every code `impl` linked at
the contract addresses, if `runtime.memequal` meets `MemAmd64.Memequal … d`, the amd64 machine
code of Go 1.26's `runtime.strequal(a, b)` (the equality function of `string`) satisfies
`Janus.Contracts.MemAmd64.Strequal … (d + 40)`: from every call state with the contract's
precondition (the stack guard and ABI conditions, both string headers and the bytes they point to
readable) it returns to `[RSP]` without faulting, with `RSP + 8`, `RBP`, `R14`, `X15`, `DF`,
`FS` and the control bits of `MXCSR` kept, memory changed only in its stack window, and `AL` is
`strEq` (equal lengths and equal bytes).

**What the code does.** The stack check (`CMPQ SP, 16(R14)`; the `morestack` path is excluded by
`StackGuardOK`), `PUSHQ BP; SUBQ $0x18, SP`, then: lengths differ, `false`; else
`memequal(a.ptr, b.ptr, a.len)` and its result. At the call, `RSP` is 40 bytes below the entry
`RSP` (saved `RBP`, the 24-byte frame, the return address of the `CALL`), so `memequal` with
bound `d` stays within the caller's bound `d + 40` (`MemAmd64.EqPre.of_caller`,
`Input.of_caller` with the window `callerWindow s d 40 0`).

**Assumptions.** The contract's precondition and the `Memequal` contract of `runtime.memequal`.
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts.MemAmd64
open Janus.Contracts.Mem (BoolRes strEq strPtr strLen)

namespace Proof

set_option maxHeartbeats 4000000 in
/-- **`runtime.strequal` (amd64) meets its contract**, given `runtime.memequal`'s. -/
theorem correctness (impl : List Janus.Amd64.Segment) (d : Nat)
    (hmeq : Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d) :
    Strequal (Extracted.program.link impl) Extracted.entry (d + 40) := by
  intro s hpc ⟨⟨hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hgo⟩, ⟨⟨hA1, hA2, hA3⟩, ⟨hP1, hP2, hP3⟩⟩,
    ⟨⟨hB1, hB2, hB3⟩, ⟨hQ1, hQ2, hQ3⟩⟩⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    at hA3 hP3 hB3 hQ3 hgo
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hc : CallerOK s d 40 0 := ⟨hg, hal, by omega, by omega,
    Arm64.Memory.accessible_mono _ hacc (by omega) (by omega),
    by simp only [outside_cons, outside_nil, and_true]; omega⟩
  have la := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + 8) 8
  have lb := Arm64.Memory.readLE_lt s.mem ((s.regs 3).toNat + 8) 8
  have pa := Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  have pb := Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
  simp only [strPtr, strLen] at hP1 hP2 hP3 hQ1 hQ2 hQ3 ⊢
  janus64_run until [Extracted.program.contractAddr "runtime.memequal"]
  · have hlen : s.mem.readLE ((s.regs 0).toNat + 8) 8 = s.mem.readLE ((s.regs 3).toNat + 8) 8 := by
      simp only [Nat.reducePow] at la lb; omega
    have hfw : ∀ v, MemFrame s.mem ((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
        (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 v)
        (callerWindow s d 40 0) := by
      intro v; simp only [callerWindow]; janus_frame
    have e0 : (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8)).toNat = s.mem.readLE (s.regs 0).toNat 8 :=
      by rw [BitVec.toNat_ofNat]; omega
    have e1 : (BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 8) 8)).toNat =
        s.mem.readLE ((s.regs 0).toNat + 8) 8 := by rw [BitVec.toNat_ofNat]; omega
    have e3 : (BitVec.ofNat 64 (s.mem.readLE (s.regs 3).toNat 8)).toNat = s.mem.readLE (s.regs 3).toNat 8 :=
      by rw [BitVec.toNat_ofNat]; omega
    refine ReachesRet.call hmeq rfl ⟨?_, ?_, ?_⟩ ?_
    · exact EqPre.of_caller hc (hfw _) (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40])
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]) (by exact hx) rfl
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]
            rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide) (by decide) (by decide)
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, e0, e1]
      refine Input.of_caller (hfw _) (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40])
        (by decide) (by omega) (by omega) hP2 ?_
      simp only [callerWindow, outside_cons, outside_nil, and_true]; omega
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, e3, e1]
      refine Input.of_caller (hfw _) (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40])
        (by decide) (by omega) (by omega) (by rw [hlen]; exact hQ2) ?_
      simp only [callerWindow, outside_cons, outside_nil, and_true]; omega
    intro s' hpc' ⟨r, x, y, fl, mx, m', hs', hmx, hfr, hres⟩
    subst hs'
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
      Nat.reduceEqDiff, hsp40] at hfr
    simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff] at hres
    simp only [e0, e1, e3] at hres
    rw [(hfw _).readLE _ _ (by simp only [callerWindow, outside_cons, outside_nil, and_true]; omega),
      (hfw _).readLE _ _ (by simp only [callerWindow, outside_cons, outside_nil, and_true]; omega)] at hres
    janus64_run
    refine EqRet.intro ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?q10
    case q8 => simp only at hmx ⊢; exact hmx
    case q9 =>
      refine (hfw _).trans hfr ?_
      intro a n h
      simp only [callerWindow, calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons,
        outside_nil, and_true] at h ⊢
      omega
    case q10 =>
      simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, Janus.Contracts.MapAmd64.keepABI, or_self]
      rw [hres]; simp [strEq, strPtr, strLen, hlen]
    case q7 => exact hdf.symm
    all_goals simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI,
      Janus.Contracts.MapAmd64.keepX15]
  · refine EqRet.intro ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10
    case r7 => exact hdf.symm
    case r9 => simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame
    case r10 =>
      have hne : s.mem.readLE ((s.regs 0).toNat + 8) 8 ≠ s.mem.readLE ((s.regs 3).toNat + 8) 8 := by
        simp only [Nat.reducePow] at la lb; omega
      simp [BoolRes, setRegF, strEq, strLen, beq_false_of_ne hne]
    all_goals simp [setRegF, retAddrOf]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MemSatAmd64

/-- `runtime.memequal` is the model `memequalCode` (at `A0`, behind a jump at the contract
address). -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.memequal"
def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := memequalCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model (d : Nat) : Memequal (Extracted.program.link implAt) cAddr d := by
  have hA : Memequal (Extracted.program.link implAt) A0 d := by
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (memequal_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨⟨g1, g2, g3⟩, hcall, hgo⟩, i1, i2⟩ := hpre
  exact hA _ rfl ⟨⟨⟨g1, g2, g3⟩, hcall, hgo⟩, i1, i2⟩

/-- The witness call state: `strequal(STR, STR)` on `EqHashModel.wmem64` (`STR` is the string
header `(VAL, 8)`; return address `wret` at `[wsp]`), goroutine `wg`, `RSP = wsp`. -/
def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 3 then BitVec.ofNat 64 STR
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

/-- The precondition holds at `s0` (`memequal`'s bound 64, `strequal`'s 104). -/
theorem pre : EqPre (64 + 40) 2 s0 ∧ StrInput s0 (64 + 40) 2 (s0.regs 0).toNat ∧
    StrInput s0 (64 + 40) 2 (s0.regs 3).toNat := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [CallOK, StrInput, Input, calleeStack, Janus.Contracts.MapAmd64.calleeStack,
      outside_cons, outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (d : Nat) (s : State),
    Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d ∧
    s.rip = BitVec.ofNat 64 Extracted.entry ∧
    (EqPre (d + 40) 2 s ∧ StrInput s (d + 40) 2 (s.regs 0).toNat ∧ StrInput s (d + 40) 2 (s.regs 3).toNat) :=
  ⟨implAt, 64, s0, model 64, rfl, pre⟩

/-- So the guarantee is reached: a string equals itself. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (retAddrOf s0) s0
    (fun s' => EqRet (64 + 40) 2 s0 s' fun r => BoolRes r true) := by
  have h03 : s0.regs 3 = s0.regs 0 := rfl
  refine (correctness implAt 64 (model 64) s0 rfl pre).mono ?_
  intro s' h; simpa only [h03, strEq, beq_self_eq_true, Bool.and_self] using h

end Witness

end Proof
