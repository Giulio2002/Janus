import Janus
import Extracted

/-!
# `runtime.memhash_varlen` (amd64) meets the `MemhashVarlen` contract, with `runtime.memhash` as a contract

**Guarantee.** For every hash model `H` with its laws, every stack bound `d` of `runtime.memhash`
and every code `impl` linked at the contract addresses, if `runtime.memhash` meets
`HashAmd64.Memhash … H d`, the amd64 machine code of Go 1.26's `runtime.memhash_varlen(p, h)`
(the closure-based hash of memory types whose size is in the closure) satisfies
`Janus.Contracts.HashAmd64.MemhashVarlen … H (d + 40)`: from every call state with the contract's
precondition it returns to `[RSP]` without faulting, with `RSP + 8`, `RBP`, `R14`, `X15`, `DF`,
`FS` and the control bits of `MXCSR` kept, memory changed only in `H.priv` and its stack window,
`H.Env` kept, and `RAX = H.mem h n v` for the size `n = 8(RDX)` and the `n` bytes `v` at `p`.

**What the code does.** No stack check (the function is `NOSPLIT`); `PUSHQ BP; SUBQ $0x18, SP;
ADDQ $8, DX; MOVQ 0(DX), CX; CALL runtime.memhash`, then `ADDQ; POPQ BP; RET`. At the call `RSP`
is 40 bytes below the entry `RSP`, so `memhash` with bound `d` stays within the caller's bound
`d + 40`.

**Assumptions.** The contract's precondition, `H.Laws`, and the `Memhash` contract of
`runtime.memhash`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts.MemAmd64 Janus.Contracts.HashAmd64
open Janus.Contracts.Hash (HashModel)

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
/-- **`runtime.memhash_varlen` (amd64) meets its contract**, given `runtime.memhash`'s. -/
theorem correctness (impl : List Janus.Amd64.Segment) (H : HashModel) (hH : H.Laws) (d : Nat)
    (hmh : Memhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memhash") H d) :
    MemhashVarlen (Extracted.program.link impl) Extracted.entry H (d + 40) := by
  intro s hpc ⟨⟨he, hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hout, hgo, hgp⟩, ⟨hV1, hV2, hV3⟩, ⟨hA1, hA2, hA3⟩⟩
  simp only [varlenSize] at hA1 hA2 hA3 ⊢
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    at hA3 hV3 hgo
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hc : CallerOK s d 40 0 := ⟨hg, hal, by omega, by omega,
    Arm64.Memory.accessible_mono _ hacc (by omega) (by omega),
    by simp only [outside_cons, outside_nil, and_true]; omega⟩
  have hdx : (s.regs 2 + 8#64).toNat = (s.regs 2).toNat + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  have hn := Arm64.Memory.readLE_lt s.mem ((s.regs 2).toNat + 8) 8
  have hn' : (BitVec.ofNat 64 (s.mem.readLE ((s.regs 2).toNat + 8) 8)).toNat =
      s.mem.readLE ((s.regs 2).toNat + 8) 8 := by rw [BitVec.toNat_ofNat]; omega
  janus64_run until [Extracted.program.contractAddr "runtime.memhash"]
  have hfw : ∀ v, MemFrame s.mem ((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 v)
      [((s.regs 4).toNat - (d + 40), (s.regs 4).toNat + 0)] := by
    intro v; janus_frame
  refine reach_name ?_
  intro S hS
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 40 := by
    subst hS; simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]
  have hSf : MemFrame s.mem S.mem (callerWindow s d 40 0) := by subst hS; exact hfw _
  obtain ⟨q1, q2, q3⟩ := EqPre.of_caller (nargs := 3) hc hSf hS4 (by subst hS; rfl) (by subst hS; exact hx)
    (by subst hS; rfl) (by rw [hS4]; subst hS; rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide)
    (by decide) (by decide)
  subst hS
  refine ReachesRet.call hmh rfl ⟨⟨?env, q1, q2, ?op, q3, ?gp⟩, ?inp⟩ ?_
  case env =>
    simp only [setRegF, reduceIte, Nat.reduceEqDiff]
    exact hH.env_frame _ _ _ he (Agrees.of_window (hfw _) (Outside.of_sub hout (by omega) (by omega)))
  case op =>
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]
    exact Outside.of_sub hout (by omega) (by omega)
  case gp => simp only [setRegF, reduceIte, Nat.reduceEqDiff]; exact hgp
  case inp =>
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, hn']
    refine Input.of_caller (hfw _) (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40])
      (by decide) (by omega) hA1 hA2 ?_
    simp only [callerWindow, outside_cons, outside_nil, and_true, hn']; omega
  intro s' hpc' ⟨r, x, y, fl, mx, m', _, _, hs', hmx, hfr, he', hres⟩
  subst hs'
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
    Nat.reduceEqDiff, hsp40] at hfr
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, hn'] at hres he'
  rw [(hfw _).readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; simp; omega)] at hres
  janus64_run
  refine ⟨_, _, _, _, _, _, _, _, retState_of ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7, ?q8, ?q9, ?q10, ?q11⟩
  case q7 => exact hdf.symm
  case q8 => simp only at hmx ⊢; exact hmx
  case q9 =>
    refine (hfw _).trans hfr ?_
    intro a n h
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_append, outside_cons,
      outside_nil, and_true] at h ⊢
    obtain ⟨hp, h1, h2⟩ := h
    exact ⟨by omega, hp, by omega, by omega⟩
  case q10 => exact he'
  case q11 =>
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, Janus.Contracts.MapAmd64.keepABI, or_self]
    exact hres
  all_goals simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI,
    Janus.Contracts.MapAmd64.keepX15]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.HashSatAmd64

/-- `runtime.memhash` is the model `seedCode` of `H0` (at `A0`, behind a jump at the contract
address). -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.memhash"
def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := seedCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model (d : Nat) : Memhash (Extracted.program.link implAt) cAddr H0 d := by
  have hA : Memhash (Extracted.program.link implAt) A0 H0 d := by
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (memhash_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

/-- The witness call state: `memhash_varlen(VAL, 7)` on `EqHashModel.wmem64` (model `H0`; return
address `wret` at `[wsp]`) and the closure `VLEN` (size 8) in `RDX`, goroutine `wg`, `RSP = wsp`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 VAL else if i = 3 then 7 else if i = 2 then BitVec.ofNat 64 VLEN
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

/-- The precondition holds at `s0` (`memhash`'s bound 64). -/
theorem pre : HPre H0 (64 + 40) 2 s0 ∧ Input s0 (64 + 40) 2 ((s0.regs 2).toNat + 8) 8 ∧
    Input s0 (64 + 40) 2 (s0.regs 0).toNat (varlenSize s0) := by
  refine ⟨⟨wmem64_henv _, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [CallOK, Input, H0_priv, calleeStack, Janus.Contracts.MapAmd64.calleeStack,
      outside_cons, outside_nil, varlenSize] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (H : HashModel) (d : Nat) (s : State), H.Laws ∧
    Memhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memhash") H d ∧
    s.rip = BitVec.ofNat 64 Extracted.entry ∧ (HPre H (d + 40) 2 s ∧ Input s (d + 40) 2 ((s.regs 2).toNat + 8) 8 ∧
      Input s (d + 40) 2 (s.regs 0).toNat (varlenSize s)) :=
  ⟨implAt, H0, 64, s0, H0_laws, model 64, rfl, pre⟩

/-- So the guarantee is reached: in `H0` every hash is its seed. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (retAddrOf s0) s0
    (fun s' => HRet H0 (64 + 40) 2 s0 s' fun r => (r 0).toNat = 7) := by
  have h3 : (s0.regs 3).toNat % 18446744073709551616 = 7 := by decide
  refine (correctness implAt H0 H0_laws 64 (model 64) s0 rfl pre).mono ?_
  intro s' h; simpa [h3] using h

end Witness

end Proof
