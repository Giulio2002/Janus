import Extracted

/-!
# `ErrWrap() error`: `fmt.Errorf("%w: have %d, want %d bytes", errBadLen, 64, 32)` (amd64)

The amd64 counterpart of `examples/proofs/ErrWrap.lean` (see it for the Go source and the guarantee), against the amd64
contract `ErrorfAmd64.ErrorfLive` (docs/RUNTIME-CONTRACTS.md, "fmt.Errorf"). The stack window is `[RSP-4200, RSP+8)`:
the return address, the saved `RBP`, the 48-byte argument array, the callee's return-address slot and the 4096 bytes
the runtime may use.

**`RetLow` is discharged inside the proof.** The contract's precondition asks the saved return address `[RSP]` to be
below `2^46` (`ErrorfAmd64.RetLow`: a stub placed above it, `RelocAmd64`, cannot be returned into). This theorem does
not assume it: `key` proves it from the return address the function's own `call` pushes, the code address
`0x4a54a8` (`Extracted.entry + 0x88`) of the instruction after the call. It appears nowhere in `Pre`
(the auditor flags a theorem statement that mentions `RetLow`, `Janus/Tools/Audit.lean`).

`R15` is not preserved by the call (the stub's return jumps through it), and this proof never relies on it.
-/

open Janus Janus.Tactic Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf
  Janus.Contracts Janus.Contracts.Errorf Janus.Contracts.ErrorfAmd64 Janus.Contracts.PoolAmd64
  Janus.Contracts.ErrorfRealFmt

namespace Proof

/-- **The precondition of a live call** (amd64) made from a function that owns the stack window
`[lo, hi)`: the call state `S` has `RSP` `fr` bytes below the entry state's `s`, has changed memory
only in `R.rt` and the window, holds a return address below `2^47` at `[RSP]`, and the invariant
holds for `S.mem`. Everything the standard preconditions (`CallOK64`, `StackRoom64`, `LiveAt`) ask
for follows. -/
theorem call_pre64 (R : RtInv) (L : List (Nat × Nat)) (b cost : Nat) (addr : Nat) (args : List Nat)
    {s S : State} {lo hi stack nargs fr : Nat}
    (hg1 : (s.regs 14).toNat + 16 + 8 ≤ 2 ^ 48)
    (hg2 : s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 14).toNat + 16) 8 + (stack + fr) < (s.regs 4).toNat)
    (hgo : Outside ((s.regs 14).toNat + 16) 8 ((lo, hi) :: R.rt))
    (hfr : MemFrame s.mem S.mem (R.rt ++ [(lo, hi)])) (hg : S.regs 14 = s.regs 14)
    (hsp : (S.regs 4).toNat + fr = (s.regs 4).toNat) (hal : (S.regs 4).toNat % 8 = 0)
    (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hstk : stack ≤ (S.regs 4).toNat) (hlo : lo ≤ (S.regs 4).toNat - stack)
    (hhi : (S.regs 4).toNat + 8 + 8 * nargs ≤ hi) (hhi48 : hi ≤ 2 ^ 48)
    (hacc : s.mem.accessible lo (hi - lo) true = true)
    (hwrt : LiveSep [(lo, hi)] R.rt) (hwL : LiveSep L [(lo, hi)])
    (hok : R.ok addr args) (hinv : R.inv b L (S.regs 14).toNat (view R.rt L S.mem)) (hcost : cost ≤ b) :
    CallOK64 S stack nargs ∧ StackRoom64 S stack nargs ∧
      LiveAt R addr args L b cost (S.regs 14).toNat S.mem (liveWin64 S stack nargs) := by
  have hgw : Outside ((s.regs 14).toNat + 16) 8 (R.rt ++ [(lo, hi)]) := by
    simp only [outside_cons, outside_append, outside_nil, and_true] at hgo ⊢
    exact ⟨hgo.2, hgo.1⟩
  refine ⟨⟨hra, hal, hstk, by omega, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hok, hinv, hcost, ?_, ?_⟩
  · rw [hfr.accessible]
    exact Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg]; rw [hfr.accessible]; exact hg2
  · simp only [regG, regSP, stackguard0Offset, stackguard0, hg]
    rw [hfr.readLE _ _ hgw]; omega
  · rw [hg]
    simp only [calleeStack64, outside_cons, outside_nil, and_true]
    simp only [outside_cons, outside_nil, and_true] at hgo
    omega
  · intro r hr
    have := hwL r hr
    simp only [liveWin64, calleeStack64, outside_append, outside_cons, outside_nil, and_true] at this ⊢
    omega
  · intro r hr
    have := hwrt (lo, hi) (List.mem_singleton_self _)
    simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> exact Outside.of_sub this (by simp <;> omega) (by simp <;> omega)

macro "frame_sub" : tactic =>
  `(tactic| (intro a n h; simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack64] at h ⊢; grind))

abbrev ev : Nat := Extracted.dataAddr.«example.com/basic.errBadLen»
abbrev evType : Nat := Extracted.dataAddr.«example.com/basic.errBadLen→type»
abbrev evData : Nat := Extracted.dataAddr.«example.com/basic.errBadLen→data»
abbrev tErr : Nat := Extracted.dataAddr.«type:*errors.errorString»
abbrev iErr : Nat := Extracted.dataAddr.«go:itab.*errors.errorString,error»
abbrev tInt : Nat := Extracted.dataAddr.«type:int»
abbrev iWrap : Nat := Extracted.dataAddr.«go:itab.*fmt.wrapError,error»

def fmtAddr : Nat := ripTarget Extracted.program (Extracted.entry + 0x6f)

/-- Addresses of the binary's symbols, evaluated from the extraction (`janus_eval%`), never copied. -/
local macro "adrFmt" : term => `(janus_eval% fmtAddr)
local macro "adrEvData" : term => `(janus_eval% evData)
local macro "adrTInt" : term => `(janus_eval% tInt)
local macro "adrTErr" : term => `(janus_eval% tErr)
local macro "adrQ1" : term => `(janus_eval% Extracted.dataAddr.«.rodata#4de38626»)
local macro "adrQ2" : term => `(janus_eval% Extracted.dataAddr.«.rodata#b4a1072f»)
/-- The return address the `call` of `fmt.errorf` pushes: the instruction after it, `ErrWrap + 0x88`. -/
local macro "adrRet" : term => `(janus_eval% (Extracted.entry + 0x88))

def ErrHolds (m : Janus.Arm64.Memory) (tp tl : Nat) : Prop :=
  m.accessible ev 16 false = true ∧ m.readLE ev 8 = evType ∧ m.readLE (ev + 8) 8 = evData ∧
    m.accessible evData 16 false = true ∧ m.readLE evData 8 = tp ∧ m.readLE (evData + 8) 8 = tl ∧
    tl + 60 ≤ 2 ^ 32 ∧ tp + tl ≤ 2 ^ 48 ∧ (tl = 0 ∨ m.accessible tp tl false = true)

def Pre (R : RtInv) (L : List (Nat × Nat)) (bud tp tl : Nat) (s : State) : Prop :=
  StackGuardOK s 4200 ∧ StackWritable s 4200 8 ∧ (s.regs 4).toNat % 8 = 0 ∧
    Extracted.program.DataLoaded s.mem ∧ ErrHolds s.mem tp tl ∧
    Outside ((s.regs 14).toNat + 16) 8 (((s.regs 4).toNat - 4200, (s.regs 4).toNat + 8) :: R.rt) ∧
    LiveSep [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 8)] R.rt ∧
    LiveSep L [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 8)] ∧
    R.ok (Extracted.program.contractAddr "fmt.errorf") [fmtAddr, 26, (s.regs 4).toNat - 56, 3, 3] ∧
    R.inv bud L (s.regs 14).toNat (view R.rt L s.mem) ∧ 2 * (tl + 24) + 48 ≤ bud ∧
    (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length R.rt) ∧
    Outside ev 16 R.rt ∧ Outside evData 16 R.rt ∧
    (ev + 16 ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 8 ≤ ev) ∧
    (evData + 16 ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 8 ≤ evData) ∧
    (tp + tl ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 8 ≤ tp) ∧
    (tl = 0 ∨ Outside tp tl R.rt ∨ InRanges tp tl L)

def Post (R : RtInv) (L : List (Nat × Nat)) (bud tp tl : Nat) (s s' : State) : Prop :=
  (s'.regs 0).toNat = iWrap ∧ ∃ d, (s'.regs 3).toNat = d ∧ d + 32 ≤ 2 ^ 48 ∧
        s'.mem.accessible d 32 true = true ∧ s'.mem.readLE (d + 8) 8 = tl + 24 ∧
        strBytes s'.mem (s'.mem.readLE d 8) (tl + 24) = strBytes s.mem tp tl ++ [58, 32, 104, 97, 118, 101, 32, 54, 52, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115] ∧
        s'.mem.readLE (d + 16) 8 = evType ∧ s'.mem.readLE (d + 24) 8 = evData ∧
        FreshFrom [(d, d + 32)] L ∧ InRanges d 32 R.rt ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 8)]) ∧ LiveFrame s.mem s'.mem L [] ∧
        R.inv (bud - (2 * (tl + 24) + 48)) (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (tl + 24)))
          (s.regs 14).toNat (view R.rt (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (tl + 24))) s'.mem)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv)
    (hf : ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R
      tErr iErr tInt iWrap 26 fmtNum 4294967296)
    (L : List (Nat × Nat)) (bud tp tl : Nat) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (Pre R L bud tp tl)
      (Post R L bud tp tl) := by
  intro ret hret s hs ⟨hg, ⟨hb4, ha4, hw4⟩, hal, hd, ⟨hv1, hv2, hv3, hv4, hv5, hv6, htl, htpb, htx⟩, hgo, hwrt, hwL, hok,
    hinv, hbud, hdataO, hevO, hevDO, hevW, hevDW, htW, htO⟩
  janus64_intro hs
  janus_eval_nat hFA : fmtAddr
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb4 ha4 hw4 hal
  janus64_data hd [hw4]
  simp only [ev, evType, evData, Extracted.dataAddr.«example.com/basic.errBadLen»,
    Extracted.dataAddr.«example.com/basic.errBadLen→type», Extracted.dataAddr.«example.com/basic.errBadLen→data»] at hv1 hv2 hv3 hv4 hv5 hv6 hevO hevDO hevW hevDW
  rw [hFA] at hok
  have hsp104 : (s.regs 4 - 104#64).toNat = (s.regs 4).toNat - 104 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hsp56 : (s.regs 4 - 56#64).toNat = (s.regs 4).toNat - 56 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl

  have hO2 : Outside adrFmt 256 R.rt := hdataO _ (List.getElem_mem (l := Extracted.program.data) (n := 2) (by decide))
  have hO3 : Outside adrQ1 16 R.rt := hdataO _ (List.getElem_mem (l := Extracted.program.data) (n := 3) (by decide))
  have facts : ∀ M : Arm64.Memory, MemFrame s.mem M [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 8)] →
      M.readLE ((s.regs 4).toNat - 56) 8 = adrTErr → M.readLE ((s.regs 4).toNat - 48) 8 = adrEvData →
      M.readLE ((s.regs 4).toNat - 40) 8 = adrTInt → M.readLE ((s.regs 4).toNat - 32) 8 = adrQ1 →
      M.readLE ((s.regs 4).toNat - 24) 8 = adrTInt → M.readLE ((s.regs 4).toNat - 16) 8 = adrQ2 →
      ArgsOK (Env.mk tErr iErr tInt iWrap) 26 fmtNum 4294967296 M adrFmt 26 ((s.regs 4).toNat - 56) 3 3 ∧
      errorfReads M adrFmt 26 ((s.regs 4).toNat - 56) =
        [(adrFmt, 26), ((s.regs 4).toNat - 56, 48), (adrEvData, 16), (tp, tl), (adrQ1, 8), (adrQ2, 8)] ∧
      msgOf M adrFmt 26 ((s.regs 4).toNat - 56) = strBytes s.mem tp tl ++ [58, 32, 104, 97, 118, 101, 32, 54, 52, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115] ∧
      errorfCost M adrFmt 26 ((s.regs 4).toNat - 56) = 2 * (tl + 24) + 48 ∧ operandD M ((s.regs 4).toNat - 56) 0 = adrEvData := by
    intro M hf' hA0 hA1 hA2 hA3 hA4 hA5
    have hrd : ∀ a n, Outside a n [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 8)] → M.readLE a n = s.mem.readLE a n :=
      fun a n h => hf'.readLE a n h
    have hacc : ∀ a n w, M.accessible a n w = s.mem.accessible a n w := fun a n w => hf'.accessible a n w
    have hW1 : ∀ a n, a + n ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 8 ≤ a → Outside a n [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 8)] := by
      intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
    have hfm : M.readLE adrFmt 26 = fmtNum := by
      rw [hrd _ _ (hW1 _ _ (by omega)), h_rodata adrFmt 26 (by decide +kernel)]; decide +kernel
    have hv64 : M.readLE adrQ1 8 = 64 := by
      rw [hrd _ _ (hW1 _ _ (by omega)), h_rodata adrQ1 8 (by decide +kernel)]; decide +kernel
    have hv32 : M.readLE adrQ2 8 = 32 := by
      rw [hrd _ _ (hW1 _ _ (by omega)), h_rodata adrQ2 8 (by decide +kernel)]; decide +kernel
    have hfR : Readable M adrFmt 26 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Arm64.Memory.accessible_mono _ h_data2 (by omega) (by omega)⟩
    have hsR : Readable M ((s.regs 4).toNat - 56) 48 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ hw4 (by omega) (by omega))⟩
    have heR : Readable M adrEvData 16 := ⟨by omega, fun _ => by rw [hacc]; exact hv4⟩
    have htR : Readable M tp tl :=
      ⟨htpb, fun hpos => by rw [hacc]; rcases htx with h | h; omega; exact h⟩
    have hq1R : Readable M adrQ1 8 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Arm64.Memory.accessible_mono _ h_data3 (by omega) (by omega)⟩
    have hq2R : Readable M adrQ2 8 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Arm64.Memory.accessible_mono _ h_data3 (by omega) (by omega)⟩
    have hA1' : M.readLE ((s.regs 4).toNat - 56 + 8) 8 = adrEvData := by
      rw [show (s.regs 4).toNat - 56 + 8 = (s.regs 4).toNat - 48 by omega]; exact hA1
    have hA2' : M.readLE ((s.regs 4).toNat - 56 + 16) 8 = adrTInt := by
      rw [show (s.regs 4).toNat - 56 + 16 = (s.regs 4).toNat - 40 by omega]; exact hA2
    have hA3' : M.readLE ((s.regs 4).toNat - 56 + 24) 8 = adrQ1 := by
      rw [show (s.regs 4).toNat - 56 + 24 = (s.regs 4).toNat - 32 by omega]; exact hA3
    have hA4' : M.readLE ((s.regs 4).toNat - 56 + 32) 8 = adrTInt := by
      rw [show (s.regs 4).toNat - 56 + 32 = (s.regs 4).toNat - 24 by omega]; exact hA4
    have hA5' : M.readLE ((s.regs 4).toNat - 56 + 40) 8 = adrQ2 := by
      rw [show (s.regs 4).toNat - 56 + 40 = (s.regs 4).toNat - 16 by omega]; exact hA5
    have htp' : M.readLE adrEvData 8 = tp := by rw [hrd _ _ (hW1 _ _ (by omega))]; exact hv5
    have htl' : M.readLE (adrEvData + 8) 8 = tl := by rw [hrd _ _ (hW1 _ _ (by omega))]; exact hv6
    have hargs := ErrorfConsumer.argsOK_real (Env.mk tErr iErr tInt iWrap) 4294967296 M adrFmt ((s.regs 4).toNat - 56)
      adrEvData tp tl adrQ1 adrQ2 (by decide) hfm hfR hsR hA0 hA1' (by decide) heR htp' htl' htR hA2' hA3' (by decide)
      hq1R hA4' hA5' (by decide) hq2R (by omega)
    have hn : nDec (segsOf M adrFmt 26) = 2 := by rw [segsOf_real _ _ _ rfl hfm]; decide
    have hstr : strBytes M tp tl = strBytes s.mem tp tl := by
      apply strBytes_congr
      intro i hi
      exact hf'.bytes (hW1 _ _ (by omega))
    have hmsg : msgOf M adrFmt 26 ((s.regs 4).toNat - 56) = strBytes s.mem tp tl ++ [58, 32, 104, 97, 118, 101, 32, 54, 52, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115] := by
      rw [msgOf_real _ _ _ _ rfl hfm, hA1', htp', htl', hA3', hA5', hv64, hv32, hstr]
      have d64 : decBytes (toSigned 64) = [54, 52] := by decide
      have d32 : decBytes (toSigned 32) = [51, 50] := by decide
      rw [d64, d32]; rfl
    have hmlen : (msgOf M adrFmt 26 ((s.regs 4).toNat - 56)).length = tl + 24 := by
      rw [hmsg]; simp [strBytes]
    have hcost : errorfCost M adrFmt 26 ((s.regs 4).toNat - 56) = 2 * (tl + 24) + 48 := by
      unfold errorfCost; rw [hmlen, if_neg (by omega)]; simp only [wrapBytes]; omega
    have hreads : errorfReads M adrFmt 26 ((s.regs 4).toNat - 56) =
        [(adrFmt, 26), ((s.regs 4).toNat - 56, 48), (adrEvData, 16), (tp, tl), (adrQ1, 8), (adrQ2, 8)] := by
      unfold errorfReads
      rw [hn]
      simp [operandD, hA1', htp', htl', hA3', hA5', List.range_succ]
    exact ⟨hargs, hreads, hmsg, hcost, by unfold operandD; exact hA1'⟩
  have key : ∀ S : State, MemFrame s.mem S.mem [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 8)] → S.regs 14 = s.regs 14 →
      (S.regs 4).toNat + 104 = (s.regs 4).toNat →
      S.regs 0 = (BitVec.ofNat 64 adrFmt) → S.regs 3 = 26#64 → S.regs 1 = s.regs 4 - 56#64 → S.regs 7 = 3#64 → S.regs 6 = 3#64 →
      S.mem.readLE (S.regs 4).toNat 8 = adrRet →
      S.mem.readLE ((s.regs 4).toNat - 56) 8 = adrTErr → S.mem.readLE ((s.regs 4).toNat - 48) 8 = adrEvData →
      S.mem.readLE ((s.regs 4).toNat - 40) 8 = adrTInt → S.mem.readLE ((s.regs 4).toNat - 32) 8 = adrQ1 →
      S.mem.readLE ((s.regs 4).toNat - 24) 8 = adrTInt → S.mem.readLE ((s.regs 4).toNat - 16) 8 = adrQ2 →
      (CallOK64 S 4096 5 ∧ RetLow S ∧ StackRoom64 S 4096 5 ∧
        ArgsOK (Env.mk tErr iErr tInt iWrap) 26 fmtNum 4294967296 S.mem (S.regs 0).toNat (S.regs 3).toNat
          (S.regs 1).toNat (S.regs 7).toNat (S.regs 6).toNat ∧
        ReadsOutside (errorfReads S.mem (S.regs 0).toNat (S.regs 3).toNat (S.regs 1).toNat) (liveWin64 S 4096 5) ∧
        ReadsSafe R L (errorfReads S.mem (S.regs 0).toNat (S.regs 3).toNat (S.regs 1).toNat) ∧
        LiveAt R (Extracted.program.contractAddr "fmt.errorf")
          [(S.regs 0).toNat, (S.regs 3).toNat, (S.regs 1).toNat, (S.regs 7).toNat, (S.regs 6).toNat] L bud
          (errorfCost S.mem (S.regs 0).toNat (S.regs 3).toNat (S.regs 1).toNat) (S.regs 14).toNat S.mem
          (liveWin64 S 4096 5)) := by
    intro S hf' hg' hsp h0 h3 h1 h7 h6 hra hA0 hA1 hA2 hA3 hA4 hA5
    have e0 : (S.regs 0).toNat = adrFmt := by rw [h0]; rfl
    have e3 : (S.regs 3).toNat = 26 := by rw [h3]; rfl
    have e1 : (S.regs 1).toNat = (s.regs 4).toNat - 56 := by rw [h1]; exact hsp56
    have e7 : (S.regs 7).toNat = 3 := by rw [h7]; rfl
    have e6 : (S.regs 6).toNat = 3 := by rw [h6]; rfl
    rw [e0, e3, e1, e7, e6]
    obtain ⟨hargs, hreads, hmsg, hcosteq, hop⟩ := facts S.mem hf' hA0 hA1 hA2 hA3 hA4 hA5
    have hc := call_pre64 R L bud (errorfCost S.mem adrFmt 26 ((s.regs 4).toNat - 56))
      (Extracted.program.contractAddr "fmt.errorf") [adrFmt, 26, (s.regs 4).toNat - 56, 3, 3]
      (s := s) (S := S) (lo := (s.regs 4).toNat - 4200) (hi := (s.regs 4).toNat + 8) (stack := 4096) (nargs := 5) (fr := 104)
      hnw2 hgr (by omega) hgo (hf'.widen R.rt) hg' hsp (by omega) (by omega) (by omega) (by omega) (by omega) ha4
      (by rw [show (s.regs 4).toNat + 8 - ((s.regs 4).toNat - 4200) = 4200 + 8 by omega]; exact hw4) hwrt hwL hok
      (by rw [hg']; exact RtInv.inv_frame hf' hwrt hinv) (by omega)
    refine ⟨hc.1, ?_, hc.2.1, hargs, ?_, ?_, hc.2.2⟩
    · show S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 46
      rw [hra]; decide
    · rw [hreads]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [liveWin64, calleeStack64, outside_append, outside_cons, outside_nil, and_true]
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [] <;> omega
    · rw [hreads]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hwin : ∀ a n, (s.regs 4).toNat - 4200 ≤ a → a + n ≤ (s.regs 4).toNat + 8 → Outside a n R.rt := fun a n h1 h2 =>
        Outside.of_sub (hwrt _ (List.mem_singleton_self _)) h1 (by simp only; omega)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl (Outside.of_sub hO2 (by omega) (by omega)))
      · exact Or.inr (Or.inl (hwin _ _ (by omega) (by omega)))
      · exact Or.inr (Or.inl hevDO)
      · rcases htO with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (Outside.of_sub hO3 (by omega) (by omega)))
      · exact Or.inr (Or.inl (Outside.of_sub hO3 (by omega) (by omega)))

  have post_facts : ∀ (M m1 : Arm64.Memory), MemFrame M m1 (R.rt ++ [((s.regs 4).toNat - 104 - 4096, (s.regs 4).toNat - 104), ((s.regs 4).toNat - 104 + 8, (s.regs 4).toNat - 104 + 8 + 8 * 5)]) →
      MemFrame s.mem M [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 8)] →
      M.readLE ((s.regs 4).toNat - 56) 8 = adrTErr → M.readLE ((s.regs 4).toNat - 48) 8 = adrEvData →
      M.readLE ((s.regs 4).toNat - 40) 8 = adrTInt → M.readLE ((s.regs 4).toNat - 32) 8 = adrQ1 →
      M.readLE ((s.regs 4).toNat - 24) 8 = adrTInt → M.readLE ((s.regs 4).toNat - 16) 8 = adrQ2 →
      M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat → M.readLE (s.regs 4).toNat 8 = ret →
      LiveFrame M m1 L [] → ∀ a b : Nat,
      ErrorfPost (Env.mk tErr iErr tInt iWrap) R M adrFmt 26 ((s.regs 4).toNat - 56) [((s.regs 4).toNat - 104 - 4096, (s.regs 4).toNat - 104), ((s.regs 4).toNat - 104 + 8, (s.regs 4).toNat - 104 + 8 + 8 * 5), ((s.regs 4).toNat - 104, (s.regs 4).toNat - 104 + 8)] L bud (s.regs 14).toNat a b m1 →
      m1.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧ m1.readLE (s.regs 4).toNat 8 = ret ∧
        m1.accessible ((s.regs 4).toNat - 8) 8 false = true ∧ m1.accessible (s.regs 4).toNat 8 false = true ∧
        a = iWrap ∧ b + 32 ≤ 2 ^ 48 ∧ m1.accessible b 32 true = true ∧ m1.readLE (b + 8) 8 = tl + 24 ∧
        strBytes m1 (m1.readLE b 8) (tl + 24) = strBytes s.mem tp tl ++ [58, 32, 104, 97, 118, 101, 32, 54, 52, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115] ∧
        m1.readLE (b + 16) 8 = iErr ∧ m1.readLE (b + 24) 8 = evData ∧ FreshFrom [(b, b + 32)] L ∧
        InRanges b 32 R.rt ∧ MemFrame s.mem m1 (R.rt ++ [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 8)]) ∧
        LiveFrame s.mem m1 L [] ∧
        R.inv (bud - (2 * (tl + 24) + 48)) (L ++ ((b, b + 32) :: range0 (m1.readLE b 8) (tl + 24)))
          (s.regs 14).toNat (view R.rt (L ++ ((b, b + 32) :: range0 (m1.readLE b 8) (tl + 24))) m1) := by
    intro M m1 hfr hMF hA0 hA1 hA2 hA3 hA4 hA5 h29 h30 hlf a b hp
    obtain ⟨hargs, hreads, hmsgM, hcostM, hopM⟩ := facts M hMF hA0 hA1 hA2 hA3 hA4 hA5
    obtain ⟨hiw, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hfresh, hinr, hsep1, hsep2, hinv'⟩ := hp
    have hwin2 : ∀ a n, (s.regs 4).toNat - 8 ≤ a → a + n ≤ (s.regs 4).toNat + 8 → Outside a n R.rt := fun a n h1 h2 =>
      Outside.of_sub (hwrt _ (List.mem_singleton_self _)) (by omega) (by simp only; omega)
    have hs29 : m1.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
      rw [hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hwin2 _ _ (by omega) (by omega), by omega, by omega⟩)]
      exact h29
    have hs30 : m1.readLE (s.regs 4).toNat 8 = ret := by
      rw [hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hwin2 _ _ (by omega) (by omega), by omega, by omega⟩)]
      exact h30
    have hacc : ∀ a n w, m1.accessible a n w = s.mem.accessible a n w := fun a n w => by
      rw [hfr.accessible, hMF.accessible]
    have hmlen : (msgOf M adrFmt 26 ((s.regs 4).toNat - 56)).length = tl + 24 := by
      rw [hmsgM]; simp [strBytes]
    refine ⟨hs29, hs30, ?_, ?_, hiw, ?_, ?_, ?_, ?_, ?_, ?_, hfresh, hinr, ?_, ?_, ?_⟩
    · rw [hacc]; exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ hw4 (by omega) (by omega))
    · rw [hacc]; exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ hw4 (by omega) (by omega))
    · simpa [wrapBytes] using hd1
    · exact hd2
    · rw [hmlen] at hd3; exact hd3
    · rw [hmlen, hmsgM] at hd4; exact hd4
    · simp only [wrapErrOffset] at hd6; exact hd6
    · simp only [wrapErrOffset] at hd7; rw [hopM] at hd7; exact hd7
    · exact MemFrame.trans hMF hfr (by frame_sub)
    · exact LiveFrame.trans (LiveFrame.of_win (ws := [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 8)]) hMF hwL) hlf (fun _ _ h => h)
    · rw [hcostM] at hinv'; rw [hmlen] at hinv'; exact hinv'

  janus64_run [hv2, hv3] until [Extracted.program.contractAddr "fmt.errorf"]
  refine Reaches.call (Summary.withExit (hf L bud) hret) rfl
    (key _ (by janus_frame) (by simp [setRegF]) (by simp [setRegF, hsp104]; omega) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF, hsp104, Arm64.Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self]) (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self]) (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self]) (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self]) (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self]) (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self])) ?_
  intro s' hpc' ⟨r, x, y, fl, m1, zh, kr, hs1, hfr1, hlf1, hpost⟩
  subst hs1
  simp only [liveWin64, calleeStack64, List.cons_append, List.nil_append, setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    hsp104, hsp56] at hfr1 hlf1 hpost
  have hr := post_facts _ _ hfr1 (by janus_frame)
      (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self]) (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self]) (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self]) (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self]) (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self]) (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Arm64.Memory.readLE_writeLE_self];
          exact Nat.mod_eq_of_lt (by have h := (s.regs 5).isLt; have : (256 : Nat) ^ 8 = 2 ^ 64 := (by decide); omega))
      (by (try dsimp only); (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]); exact h_ret)
      hlf1 _ _ (by simpa using hpost)
  obtain ⟨hs29, hs30, hacc29, hacc30, hiw, hrest⟩ := hr
  have hr0 : r 0 ≠ 0#64 := fun h => by
    rw [h] at hiw
    exact absurd hiw (by decide)
  unfold Post
  janus64_run [hs29, hs30, hr0, hacc29, hacc30]
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hMf, hLf, hInv⟩ := hrest
  refine ⟨hiw, (r 3).toNat, rfl, by omega, by rw [← hMf.accessible]; exact hB, hC, hD, hE, hF, ?_, hH, hMf, hLf, ?_⟩
  · simpa [freshFrom_cons, freshFrom_nil] using hG
  · simpa [range0] using hInv

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The stub of `ErrorfRealImpl64` placed at `fmt.errorf`'s contract address (`errorf_live_at64`), the toy runtime with the
constants cell (`errR`), a state with `errBadLen` holding its link-time image and the text `"bad length"`, an admissible
return address: `correctness` applies (`nonvacuous`) and `ErrWrap` returns the wrapped error (`returns`). -/

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.ErrorfRealRt

def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000
def retA : Nat := 0x1000
def textAddr : Nat := 0x500000
def txtNum : Nat := 493273389536941829284194

/-- The byte of the program's static data at `a`. -/
def dat (a : Nat) : Option Nat :=
  Extracted.data.findSome? fun d =>
    if d.base ≤ a ∧ a < d.base + d.bytes.length then some (d.bytes.getD (a - d.base) 0) else none

def regions0 : List Arm64.Region :=
  [⟨sp0 - 4200, 4208, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨ev, 0x40, true⟩,
    ⟨textAddr, 0x10, false⟩] ++
    Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩

def base : Arm64.Memory :=
  ((((((((((⟨fun _ => 0, regions0⟩ : Arm64.Memory).writeLE ev 8 evType).writeLE (ev + 8) 8 evData).writeLE evData 8 textAddr).writeLE
    (evData + 8) 8 10).writeLE textAddr 10 txtNum).writeLE BUMP 8 HEAP).writeLE CELL 8 iErr).writeLE (CELL + 8) 8 iWrap).writeLE
    (g0 + 16) 8 0x1000).writeLE sp0 8 retA

def mem0 : Arm64.Memory := ⟨fun a => match dat a with | some b => BitVec.ofNat 8 b | none => base.bytes a, regions0⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded mem0 := by
  unfold Amd64.Program.DataLoaded
  decide +kernel

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

abbrev cAddr : Nat := Extracted.program.contractAddr "fmt.errorf"
def implAt : List Amd64.Segment := [Janus.Contracts.ErrorfRealLive64.errorfSeg64 cAddr]
def R0 : RtInv := errR [] iErr iWrap (fun _ _ => True)

theorem tysOK : TysOK ([] : Tys) := by intro t ht; simp at ht

theorem hf0 : ErrorfLive (Extracted.program.link implAt) cAddr 4096 R0 tErr iErr tInt iWrap 26 fmtNum 4294967296 :=
  Janus.Contracts.ErrorfRealLive64.errorf_live_at64 _ cAddr [] tysOK tErr tInt iErr iWrap (by decide) (by decide)
    (by decide)
    (Janus.Contracts.ErrorfRealLive64.fetchedAt_link64 Extracted.program cAddr (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem hret0 : RetAddr (Extracted.program.link implAt) retA := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link implAt).withExit retA) Extracted.entry [] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h, rfl⟩

theorem dat_none (i : Nat) (h : 6000000 ≤ i) : dat i = none := by
  unfold dat
  rw [List.findSome?_eq_none_iff]
  intro d hd
  have hb : ∀ d ∈ Extracted.data, d.base + d.bytes.length ≤ 6000000 := by decide +kernel
  have := hb d hd
  simp only [ite_eq_right_iff]
  intro hc; omega

theorem base_zero (i : Nat) (h : 268435456 ≤ i) : base.bytes i = 0 := by
  unfold base
  repeat rw [Arm64.Memory.bytes_writeLE_outside]
  all_goals first
    | rfl
    | (simp only [ev, evType, evData, Extracted.dataAddr.«example.com/basic.errBadLen»,
        Extracted.dataAddr.«example.com/basic.errBadLen→type», Extracted.dataAddr.«example.com/basic.errBadLen→data», textAddr,
        BUMP, HEAP, CELL, g0, sp0]
       omega)

theorem mem0_zero (i : Nat) (h : 268435456 ≤ i) : mem0.bytes i = 0 := by
  unfold mem0
  simp only [dat_none i (by omega)]
  exact base_zero i h

theorem rinv0 (g : Nat) : R0.inv 116 [] g (view R0.rt [] mem0) := by
  show errInv [] iErr iWrap 116 [] g (view (errRt []) [] mem0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [view_toy_err]
    refine ⟨HEAP, ?_, by decide, by decide, by decide, by intro r hr; simp at hr, ?_, ?_, ?_, ?_, by intro t ht; simp at ht⟩
    · rw [readLE_view (inRanges_bump []) (by simp [outside_nil])]; decide
    · intro i h1 h2
      rw [readLE_view (inRanges_heap (n := 1) (by simp [HEAP] at *; omega) (by simp [HEND, HEAP, HSIZE] at *; omega)) (by simp [outside_nil])]
      simp only [Arm64.Memory.readLE, Nat.mul_zero, Nat.add_zero]
      rw [mem0_zero i (by simp [HEAP, HEND, HSIZE] at *; omega)]; rfl
    · decide
    · decide
    · decide
  · rw [readLE_view (inRanges_cell [] (Nat.le_refl _) (by omega)) (by simp [outside_nil])]; decide
  · rw [readLE_view (inRanges_cell [] (by omega) (by omega)) (by simp [outside_nil])]; decide
  · rw [view_accessible]; decide

theorem s0_sp : (s0.regs 4).toNat = sp0 := by simp [s0, sp0]
theorem s0_g : (s0.regs 14).toNat = g0 := by simp [s0, g0]

theorem guard0 : StackGuardOK s0 4200 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [regG, stackguard0Offset, s0_g]; simp [g0]
  · simp only [regG, stackguard0Offset, s0_g]; decide
  · simp only [stackguard0, regG, regSP, stackguard0Offset, s0_g, s0_sp]; decide

theorem stack0 : StackWritable s0 4200 8 := by
  unfold StackWritable
  simp only [regSP, s0_sp]
  exact ⟨by decide, by decide, by decide⟩

theorem pre0 : Pre R0 [] 116 textAddr 10 s0 := by
  have hrt : R0.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64), (CELL, CELL + 16)] := rfl
  unfold Pre
  rw [s0_sp, s0_g]
  have hsp : (s0.regs 4).toNat = sp0 := s0_sp
  refine ⟨guard0, stack0, by simp [sp0], dataLoaded, ?_, ?_, ?_, ?_, ?_, rinv0 _, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ErrHolds; refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL, sp0, g0]; decide
  · rw [hrt]; intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL, sp0]; decide
  · intro r hr; simp at hr
  · show True; trivial
  · rw [hrt]
    intro d hd
    have : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length
        [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64), (CELL, CELL + 16)] := by
      simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]
      decide +kernel
    exact this d hd
  · rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL, ev,
      Extracted.dataAddr.«example.com/basic.errBadLen»]; decide
  · rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL, evData,
      Extracted.dataAddr.«example.com/basic.errBadLen→data»]; decide
  · simp only [ev, Extracted.dataAddr.«example.com/basic.errBadLen», sp0]; decide
  · simp only [evData, Extracted.dataAddr.«example.com/basic.errBadLen→data», sp0]; decide
  · simp only [textAddr, sp0]; decide
  · right; left
    rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL, textAddr]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (L : List (Nat × Nat)) (bud tp tl : Nat) (ret : Nat) (s : State),
    ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R tErr iErr tInt iWrap 26
      fmtNum 4294967296 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [] s ∧ Pre R L bud tp tl s :=
  ⟨implAt, R0, [], 116, textAddr, 10, retA, s0, hf0, hret0, setup, pre0⟩

/-- The guarantee fires: `ErrWrap()` from the witness state returns the wrapped error. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit retA) s0 fun s' =>
    ABIReturn s0 s' ∧ Post R0 [] 116 textAddr 10 s0 s' :=
  correctness implAt R0 hf0 [] 116 textAddr 10 retA hret0 s0 setup pre0

end Witness

end Proof
