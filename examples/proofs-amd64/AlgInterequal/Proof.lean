import Janus
import Extracted

/-!
# `runtime.interequal` (amd64) meets the `Interequal` contract, with `runtime.ifaceeq` as a contract

**Guarantee.** For every interface model `R` with its laws and every code `impl` linked at the
contract addresses, if `runtime.ifaceeq` meets `IfaceAmd64.Ifaceeq … R` (stack bound
`R.depth`), the amd64 machine code of Go 1.26's `runtime.interequal(a, b)` (the equality
function of non-empty interfaces) satisfies `Janus.Contracts.MemAmd64.Interequal … R (R.depth + 40)`: from
every call state with the contract's precondition it returns to `[RSP]` without faulting, with
`RSP + 8`, `RBP`, `R14`, `X15`, `DF`, `FS` and the control bits of `MXCSR` kept, memory changed
only in `R.priv` and its stack window, `R.Env` kept, and `AL` is "same type word and
`ifaceEqual`" (a nil itab, or `efaceEqual` of the itab's type).

**What the code does.** The stack check (the `morestack` path is excluded by `StackGuardOK`),
`PUSHQ BP; SUBQ $0x18, SP`, then: the type words differ, `false`; else
`ifaceeq(a.tab, a.data, b.data)` and its result. At the call `RSP` is 40 bytes below the entry
`RSP`, so `ifaceeq` (bound `R.depth`) stays within `R.depth + 40`. The comparison facts the
precondition grants at entry (`EqOK`) carry to the call state and the result back by the
contract's `EqFrame` (the caller's writes are inside its stack window).

**Assumptions.** The contract's precondition, `R.Laws` (its environment lives in `R.priv`), and
the `Ifaceeq` contract of `runtime.ifaceeq`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Type Janus.Contracts.MemAmd64
open Janus.Contracts.Mem (BoolRes)

namespace Proof

/-- Name the state a run stopped in. -/
theorem reach_name {p : Janus.Amd64.Program} {ret : BitVec 64} {S : State} {Q : State → Prop}
    (h : ∀ S', S' = S → ReachesRet p ret S' Q) : ReachesRet p ret S Q := h S rfl

/-- A final state that keeps `RBP`, `R14`, `X15`, `DF` and `FS`, has `RSP + 8` and is at the
return address is `retState` of its own registers, flags and memory (the state part of
`MemAmd64.EqRet.intro`). -/
theorem retState_of {s s' : State} (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all) (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) :
    s' = retState s s'.regs s'.xmm s'.ymmHi s'.flags s'.mxcsr s'.mem := by
  obtain ⟨r, rip, fl, xmm, mem, yh, fsb, df, mx, x8, fw⟩ := s'
  simp only at hsp h5 h14 hx hrip hfs hdf hx87 hfw ⊢
  subst hrip hfs hdf hx87 hfw
  simp only [retState, State.mk.injEq, and_true, true_and]
  refine ⟨?_, ?_⟩
  · funext i
    simp only [Janus.Contracts.MapAmd64.keepABI]
    split
    · rename_i hi; subst hi; exact hsp
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [Janus.Contracts.MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Janus.Amd64.Segment) (R : IfaceModel) (hR : R.Laws)
    (hcall : Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.ifaceeq") R) :
    Interequal (Extracted.program.link impl) Extracted.entry R (R.depth + 40) := by
  intro s hpc ⟨⟨he, hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hout, hgo⟩, ⟨hA1, hA2, hA3⟩,
    ⟨hB1, hB2, hB3⟩, hok⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  have hA3' := hA3
  have hB3' := hB3
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    at hA3 hB3 hgo
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hc : CallerOK s R.depth 40 0 := ⟨hg, hal, by omega, by omega,
    Arm64.Memory.accessible_mono _ hacc (by omega) (by omega),
    by simp only [outside_cons, outside_nil, and_true]; omega⟩
  have t0 := Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  have t1 := Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
  have x0 := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + 8) 8
  have y0 := Arm64.Memory.readLE_lt s.mem ((s.regs 3).toNat + 8) 8
  have et : (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8)).toNat = s.mem.readLE (s.regs 0).toNat 8 := by
    rw [BitVec.toNat_ofNat]; omega
  have ex : (BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 8) 8)).toNat =
      s.mem.readLE ((s.regs 0).toNat + 8) 8 := by rw [BitVec.toNat_ofNat]; omega
  have ey : (BitVec.ofNat 64 (s.mem.readLE ((s.regs 3).toNat + 8) 8)).toNat =
      s.mem.readLE ((s.regs 3).toNat + 8) 8 := by rw [BitVec.toNat_ofNat]; omega
  janus64_run until [Extracted.program.contractAddr "runtime.ifaceeq"]
  · have htt : s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 3).toNat 8 := by
      simp only [Nat.reducePow] at t0 t1; omega
    have hfw : ∀ v, MemFrame s.mem ((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
        (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 v)
        [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 0)] := by
      intro v; janus_frame
    have hwide : ∀ v, MemFrame s.mem ((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
        (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 v)
        (calleeStack s (R.depth + 40) 2) := by
      intro v; refine (hfw v).mono ?_; intro a n h
      simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
        and_true] at h ⊢
      omega
    refine reach_name ?_
    intro S hS
    have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 40 := by
      subst hS; simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]
    have hSf : MemFrame s.mem S.mem (callerWindow s R.depth 40 0) := by subst hS; exact hfw _
    obtain ⟨q1, ⟨c1, c2, c3, c4, c5, c6, c7⟩, q3⟩ := EqPre.of_caller (nargs := 3) hc hSf hS4
      (by subst hS; rfl) (by subst hS; exact hx) (by subst hS; rfl)
      (by rw [hS4]; subst hS; rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide)
      (by decide) (by decide)
    subst hS
    refine ReachesRet.call hcall rfl ⟨⟨?env, q1, c1, c2, c3, c4, c5, c6, c7, ?op⟩, ?ok⟩ ?_
    case env =>
      simp only [setRegF, reduceIte, Nat.reduceEqDiff]
      exact hR.env_frame _ _ _ he (Agrees.of_window (hfw _) (Outside.of_sub hout (by omega) (by omega)))
    case op =>
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]
      exact Outside.of_sub hout (by omega) (by omega)
    case ok =>
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, et, ex, ey]
      intro htab
      obtain ⟨⟨hT1, hT2, hT3⟩, hT8, hok1, hfr0⟩ := hok htt htab
      have hT8' : ∀ v, ((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
          (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 v).readLE
          (s.mem.readLE (s.regs 0).toNat 8 + 8) 8 = s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8 :=
        fun v => (hwide v).readLE _ _ (Outside.of_sub hT3 (by omega) (by omega))
      refine ⟨hT1, by rw [(hwide _).accessible]; exact hT2, by rw [hT8']; exact hT8, ?_⟩
      rw [hT8']
      exact Janus.Contracts.Iface.EqFrame.eqOK hfr0 hok1 (hwide _)
    intro s' hpc' ⟨r, x, y, fl, m', _, _, hs', hfr, he', hres⟩
    subst hs'
    simp only [Janus.Contracts.IfaceAmd64.rtWrites, Janus.Contracts.MapAmd64.calleeStack, setRegF,
      reduceIte, Nat.reduceEqDiff, hsp40, List.append_nil] at hfr
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, et, ex, ey] at hres he'
    have hres' : (r 0).toNat % 256 = (Janus.Contracts.Iface.ifaceEqual R s.mem
        (s.mem.readLE (s.regs 0).toNat 8) (s.mem.readLE ((s.regs 0).toNat + 8) 8)
        (s.mem.readLE ((s.regs 3).toNat + 8) 8)).toNat := by
      rw [hres]
      by_cases htab : s.mem.readLE (s.regs 0).toNat 8 = 0
      · simp [Janus.Contracts.Iface.ifaceEqual, htab]
      · obtain ⟨⟨hT1, hT2, hT3⟩, hT8, hok1, hfr0⟩ := hok htt htab
        simp only [Janus.Contracts.Iface.ifaceEqual]
        rw [(hwide _).readLE _ _ (Outside.of_sub hT3 (by omega) (by omega)),
          Janus.Contracts.Iface.EqFrame.efaceEqual hfr0 (hwide _)]
    janus64_run
    refine ⟨_, _, _, _, _, _, _, _, retState_of ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7, ?q8, ?q9, ?q10, ?q11⟩
    case q7 => exact hdf.symm
    case q8 => rfl
    case q9 =>
      refine (hfw _).trans hfr ?_
      intro a n h
      simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_append, outside_cons,
        outside_nil, and_true] at h ⊢
      obtain ⟨hp, h1, h2⟩ := h
      exact ⟨by omega, hp, by omega, by omega⟩
    case q10 => exact he'
    case q11 =>
      simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, Janus.Contracts.MapAmd64.keepABI, or_self]
      rw [hres', htt]
    all_goals simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI,
      Janus.Contracts.MapAmd64.keepX15]
  · have htt : s.mem.readLE (s.regs 0).toNat 8 ≠ s.mem.readLE (s.regs 3).toNat 8 := by
      simp only [Nat.reducePow] at t0 t1; omega
    refine ⟨_, _, _, _, _, _, _, _, retState_of ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7, ?r8, ?r9, ?r10, ?r11⟩
    case r7 => exact hdf.symm
    case r8 => rfl
    case r9 => simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame
    case r10 =>
      exact hR.env_frame _ _ _ he (Agrees.of_window (lo := (s.regs 4).toNat - 8)
        (hi := (s.regs 4).toNat) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
    case r11 => simp [BoolRes, setRegF, beq_false_of_ne htt]
    all_goals simp [setRegF, retAddrOf]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
open Janus (InRanges)

/-- `runtime.ifaceeq` is `IfaceSatAmd64.efaceeqCode` (at `A0`, behind a jump at the contract
address). -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.ifaceeq"
def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := efaceeqCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model : Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link implAt) cAddr R0 := by
  have hA : Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link implAt) A0 R0 := by
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) ifaceeq_impl
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

theorem eqOK_wit64 : Janus.Contracts.Iface.EqOK R0 wmem64 TD VAL VAL :=
  fun _ => ⟨Or.inl rfl, rfl, by decide, by decide⟩

theorem eqFrame_wit64 (ws : List (Nat × Nat)) (hws : ∀ a n, InRanges a n R0.priv → Outside a n ws)
    (hv : Outside VAL 8 ws) : EqFrame R0 TD wmem64 VAL VAL ws := by
  have h8 : tySize wmem64 TD = 8 := by decide
  exact EqFrame.of_regular R0_laws (g := 0) (wmem64_env0 0) (Or.inl rfl) (by decide) (by decide)
    (by rw [h8]; decide) (by rw [h8]; decide) (by rw [h8]; exact hv) (by rw [h8]; exact hv) hws

/-- The witness call state: `interequal(IFV, IFV)` on `EqHashModel.wmem64` (model `R0`; `IFV = (TAB, VAL)`, `TAB.Type = TD`),
goroutine `wg`, `RSP = wsp`. -/
def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 3 then BitVec.ofNat 64 IFV
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem hpriv : ∀ a n, InRanges a n R0.priv → Outside a n (calleeStack s0 (R0.depth + 40) 2) := by
  intro a n ⟨q, hq, h1, h2⟩
  simp only [R0_priv, List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
  simp [s0, wsp] at h1 h2 ⊢; omega

/-- The precondition holds at `s0`. -/
theorem pre : IfacePre R0 (R0.depth + 40) s0 ∧ Input s0 (R0.depth + 40) 2 (s0.regs 0).toNat 16 ∧
    Input s0 (R0.depth + 40) 2 (s0.regs 3).toNat 16 ∧
    (s0.mem.readLE (s0.regs 0).toNat 8 = s0.mem.readLE (s0.regs 3).toNat 8 →
      s0.mem.readLE (s0.regs 0).toNat 8 ≠ 0 →
      Input s0 (R0.depth + 40) 2 (s0.mem.readLE (s0.regs 0).toNat 8) 16 ∧
      s0.mem.readLE (s0.mem.readLE (s0.regs 0).toNat 8 + 8) 8 ≠ 0 ∧
      Janus.Contracts.Iface.EqOK R0 s0.mem (s0.mem.readLE (s0.mem.readLE (s0.regs 0).toNat 8 + 8) 8)
        (s0.mem.readLE ((s0.regs 0).toNat + 8) 8) (s0.mem.readLE ((s0.regs 3).toNat + 8) 8) ∧
      EqFrame R0 (s0.mem.readLE (s0.mem.readLE (s0.regs 0).toNat 8 + 8) 8) s0.mem
        (s0.mem.readLE ((s0.regs 0).toNat + 8) 8) (s0.mem.readLE ((s0.regs 3).toNat + 8) 8)
        (calleeStack s0 (R0.depth + 40) 2)) := by
  refine ⟨⟨wmem64_env0 (s0.regs 14), ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_⟩, ?_, ?_, fun _ _ => ?_⟩
  rotate_left 5
  · have e1 : s0.mem.readLE (s0.regs 0).toNat 8 = TAB := by decide
    have e2 : s0.mem.readLE ((s0.regs 0).toNat + 8) 8 = VAL := by decide
    have e3 : s0.mem.readLE ((s0.regs 3).toNat + 8) 8 = VAL := by decide
    have e4 : s0.mem.readLE (TAB + 8) 8 = TD := by decide
    rw [e1, e2, e3, e4]
    refine ⟨?_, by decide, eqOK_wit64, eqFrame_wit64 _ hpriv ?_⟩ <;>
      simp only [Input, calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons,
        outside_nil] <;> decide
  all_goals simp only [CallOK, Input, R0_priv, R0_depth, calleeStack,
      Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : IfaceModel) (s : State), R.Laws ∧
    Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R ∧
    s.rip = BitVec.ofNat 64 Extracted.entry ∧ (IfacePre R (R.depth + 40) s ∧ Input s (R.depth + 40) 2 (s.regs 0).toNat 16 ∧
    Input s (R.depth + 40) 2 (s.regs 3).toNat 16 ∧
    (s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 3).toNat 8 →
      s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
      Input s (R.depth + 40) 2 (s.mem.readLE (s.regs 0).toNat 8) 16 ∧
      s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8 ≠ 0 ∧
      Janus.Contracts.Iface.EqOK R s.mem (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8)
        (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8) ∧
      EqFrame R (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8) s.mem
        (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8)
        (calleeStack s (R.depth + 40) 2))) :=
  ⟨implAt, R0, s0, R0_laws, model, rfl, pre⟩

/-- `correctness` at `s0`: the call returns. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (retAddrOf s0) s0
    (fun s' => IfaceRet R0 (R0.depth + 40) s0 s' fun r => Janus.Contracts.Mem.BoolRes r
      (s0.mem.readLE (s0.regs 0).toNat 8 == s0.mem.readLE (s0.regs 3).toNat 8 &&
        Janus.Contracts.Iface.ifaceEqual R0 s0.mem (s0.mem.readLE (s0.regs 0).toNat 8)
          (s0.mem.readLE ((s0.regs 0).toNat + 8) 8) (s0.mem.readLE ((s0.regs 3).toNat + 8) 8))) :=
  correctness implAt R0 R0_laws model s0 rfl pre

end Witness

end Proof
