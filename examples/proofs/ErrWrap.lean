import Extracted

/-!
# `ErrWrap() error`: `fmt.Errorf("%w: have %d, want %d bytes", errBadLen, 64, 32)` (arm64)

```go
var errBadLen = errors.New("bad length")

func ErrWrap() error { return fmt.Errorf("%w: have %d, want %d bytes", errBadLen, 64, 32) }
```

**Guarantee.** For every runtime `R` (`Janus.Contracts.Live`) and every implementation of `fmt.errorf` satisfying
`ErrorfLive` for `R` (docs/RUNTIME-CONTRACTS.md, "fmt.Errorf"), with the contract's four machine constants being the
link-time addresses of the binary's own symbols (`Extracted.dataAddr`), every live set `L` and budget `bud` at which the
runtime's invariant holds and every Go call state in which the package variable `errBadLen` holds its link-time image
(the `*errors.errorString` itab and the static string `"bad length"`), the call returns the `*fmt.wrapError`
`{msg = text ++ ": have 64, want 32 bytes", err = errBadLen}`: `X0` is the `wrapError` itab, `X1` a fresh readable
32-byte object whose `err` field is the variable's own interface value (so `errors.Is(err, errBadLen)` holds) and
whose message block is a fresh readable block with exactly those bytes. Memory changes only in the runtime's ranges
and the stack window and no object of `L` changes.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.Errorf
  Janus.Contracts.ErrorfRealFmt

namespace Proof

/-- A frame in the window of the caller is a frame in the window of the caller plus the runtime. -/
macro "frame_sub" : tactic =>
  `(tactic| (intro a n h; simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack] at h ⊢; grind))

abbrev ev : Nat := Extracted.dataAddr.«example.com/basic.errBadLen»
abbrev evType : Nat := Extracted.dataAddr.«example.com/basic.errBadLen→type»
abbrev evData : Nat := Extracted.dataAddr.«example.com/basic.errBadLen→data»
abbrev tErr : Nat := Extracted.dataAddr.«type:*errors.errorString»
abbrev iErr : Nat := Extracted.dataAddr.«go:itab.*errors.errorString,error»
abbrev tInt : Nat := Extracted.dataAddr.«type:int»
abbrev iWrap : Nat := Extracted.dataAddr.«go:itab.*fmt.wrapError,error»

/-- The format string's address (`ADRP`+`ADD` at `ErrWrap+0x60`). -/
def fmtAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0x60) (segWord Extracted.program "example.com/basic.ErrWrap" 24)
    (segWord Extracted.program "example.com/basic.ErrWrap" 25) 0

/-- Addresses of the binary's symbols, evaluated from the extraction (`janus_eval%`), never copied. -/
local macro "adrFmt" : term => `(janus_eval% fmtAddr)
local macro "adrEvData" : term => `(janus_eval% evData)
local macro "adrTInt" : term => `(janus_eval% tInt)
local macro "adrTErr" : term => `(janus_eval% tErr)
local macro "adrQ1" : term => `(janus_eval% Extracted.dataAddr.«.rodata#4de38626»)
local macro "adrQ2" : term => `(janus_eval% Extracted.dataAddr.«.rodata#df6f96c5»)

/-- The `errBadLen` variable holds its link-time image: the itab word and the data word (the static errorString whose
header `(text, length)` is in writable `.data`), a short readable text. -/
def ErrHolds (m : Janus.Arm64.Memory) (tp tl : Nat) : Prop :=
  m.accessible ev 16 false = true ∧ m.readLE ev 8 = evType ∧ m.readLE (ev + 8) 8 = evData ∧
    m.accessible evData 16 false = true ∧ m.readLE evData 8 = tp ∧ m.readLE (evData + 8) 8 = tl ∧
    tl + 60 ≤ 2 ^ 32 ∧ tp + tl ≤ 2 ^ 48 ∧ (tl = 0 ∨ m.accessible tp tl false = true)

/-- The precondition: the stack window, the static data, `errBadLen` as linked, the runtime's invariant for the live set and
budget, and what the call reads outside the runtime's ranges. -/
def Pre (R : RtInv) (L : List (Nat × Nat)) (bud tp tl : Nat) (s : State) : Prop :=
  GuardOK s 4208 ∧ StackOK s 4208 0 ∧ Extracted.program.DataLoaded s.mem ∧ ErrHolds s.mem tp tl ∧
        Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - 4208, s.sp.toNat) :: R.rt) ∧
        LiveSep [(s.sp.toNat - 4208, s.sp.toNat)] R.rt ∧ LiveSep L [(s.sp.toNat - 4208, s.sp.toNat)] ∧
        R.ok (Extracted.program.contractAddr "fmt.errorf") [fmtAddr, 26, s.sp.toNat - 56, 3, 3] ∧
        R.inv bud L (s.regs 28).toNat (view R.rt L s.mem) ∧ 2 * (tl + 24) + 48 ≤ bud ∧
        (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length R.rt) ∧
        Outside ev 16 R.rt ∧ Outside evData 16 R.rt ∧
        (ev + 16 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat ≤ ev) ∧ (evData + 16 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat ≤ evData) ∧
        (tp + tl ≤ s.sp.toNat - 4208 ∨ s.sp.toNat ≤ tp) ∧
        (tl = 0 ∨ Outside tp tl R.rt ∨ InRanges tp tl L)

/-- The postcondition: `X0` is the `wrapError` itab; `X1` points at a fresh readable 32-byte object whose `err` field is
`errBadLen`'s own interface value and whose message block holds the text and `": have 64, want 32 bytes"`; memory changed
only in the runtime's ranges and the stack window, no object of `L` changed, the runtime's invariant holds again. -/
def Post (R : RtInv) (L : List (Nat × Nat)) (bud tp tl : Nat) (s s' : State) : Prop :=
  (s'.regs 0).toNat = iWrap ∧ ∃ d, (s'.regs 1).toNat = d ∧ d + 32 ≤ 2 ^ 48 ∧
        s'.mem.accessible d 32 true = true ∧ s'.mem.readLE (d + 8) 8 = tl + 24 ∧
        strBytes s'.mem (s'.mem.readLE d 8) (tl + 24) = strBytes s.mem tp tl ++ [58, 32, 104, 97, 118, 101, 32, 54, 52, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115] ∧
        s'.mem.readLE (d + 16) 8 = evType ∧ s'.mem.readLE (d + 24) 8 = evData ∧
        FreshFrom [(d, d + 32)] L ∧ InRanges d 32 R.rt ∧
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4208, s.sp.toNat)]) ∧ LiveFrame s.mem s'.mem L [] ∧
        R.inv (bud - (2 * (tl + 24) + 48)) (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (tl + 24)))
          (s.regs 28).toNat (view R.rt (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (tl + 24))) s'.mem)

/-- The precondition of the `fmt.errorf` call at its entry `S`. -/
@[reducible] def erSite (R : RtInv) (L : List (Nat × Nat)) (bud : Nat) (S : State) : Prop :=
  (CallOK S 4096 5 ∧ StackRoom S 4096 5 ∧
        ArgsOK (Env.mk tErr iErr tInt iWrap) 26 fmtNum 4294967296 S.mem (S.regs 0).toNat (S.regs 1).toNat
          (S.regs 2).toNat (S.regs 3).toNat (S.regs 4).toNat ∧
        ReadsOutside (errorfReads S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) (calleeStack S 4096 5) ∧
        ReadsSafe R L (errorfReads S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) ∧
        LiveAt R (Extracted.program.contractAddr "fmt.errorf")
          [(S.regs 0).toNat, (S.regs 1).toNat, (S.regs 2).toNat, (S.regs 3).toNat, (S.regs 4).toNat] L bud
          (errorfCost S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) (S.regs 28).toNat S.mem
          (calleeStack S 4096 5))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The call-site precondition of `fmt.errorf`, for every state `S` that is the call's entry from `s`. -/
theorem siteKey (R : RtInv) (L : List (Nat × Nat)) (bud tp tl : Nat) (s : State) (hP : Pre R L bud tp tl s) :
    ∀ S : State, MemFrame s.mem S.mem [(s.sp.toNat - 4208, s.sp.toNat)] → S.regs 28 = s.regs 28 →
      S.sp.toNat + 112 = s.sp.toNat → (S.regs 30).toNat % 4 = 0 → (S.regs 30).toNat < 2 ^ 48 →
      S.regs 0 = (BitVec.ofNat 64 adrFmt) → S.regs 1 = 26#64 → S.regs 2 = s.sp - 56#64 → S.regs 3 = 3#64 → S.regs 4 = 3#64 →
      S.mem.readLE (s.sp.toNat - 56) 8 = adrTErr → S.mem.readLE (s.sp.toNat - 48) 8 = adrEvData →
      S.mem.readLE (s.sp.toNat - 40) 8 = adrTInt → S.mem.readLE (s.sp.toNat - 32) 8 = adrQ1 →
      S.mem.readLE (s.sp.toNat - 24) 8 = adrTInt → S.mem.readLE (s.sp.toNat - 16) 8 = adrQ2 → erSite R L bud S := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, ⟨hv1, hv2, hv3, hv4, hv5, hv6, htl, htpb, htx⟩, hgo, hwrt, hwL, hok,     hinv, hbud, hdataO, hevO, hevDO, hevW, hevDW, htW, htO⟩ := hP
  janus_data hd [hw4]
  janus_eval_nat hFA : fmtAddr
  simp only [ev, evType, evData, Extracted.dataAddr.«example.com/basic.errBadLen»,
    Extracted.dataAddr.«example.com/basic.errBadLen→type», Extracted.dataAddr.«example.com/basic.errBadLen→data»] at hv1 hv2 hv3 hv4 hv5 hv6 hevO hevDO hevW hevDW
  rw [hFA] at hok
  have hO2 : Outside adrFmt 256 R.rt := hdataO _ (List.getElem_mem (l := Extracted.program.data) (n := 2) (by decide))
  have hO3 : Outside adrQ1 80 R.rt := hdataO _ (List.getElem_mem (l := Extracted.program.data) (n := 3) (by decide))
  have hsp112 : (s.sp - 112#64).toNat = s.sp.toNat - 112 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hsp56 : (s.sp - 56#64).toNat = s.sp.toNat - 56 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have facts : ∀ M : Memory, MemFrame s.mem M [(s.sp.toNat - 4208, s.sp.toNat)] →
      M.readLE (s.sp.toNat - 56) 8 = adrTErr → M.readLE (s.sp.toNat - 48) 8 = adrEvData →
      M.readLE (s.sp.toNat - 40) 8 = adrTInt → M.readLE (s.sp.toNat - 32) 8 = adrQ1 →
      M.readLE (s.sp.toNat - 24) 8 = adrTInt → M.readLE (s.sp.toNat - 16) 8 = adrQ2 →
      ArgsOK (Env.mk tErr iErr tInt iWrap) 26 fmtNum 4294967296 M adrFmt 26 (s.sp.toNat - 56) 3 3 ∧
      errorfReads M adrFmt 26 (s.sp.toNat - 56) =
        [(adrFmt, 26), (s.sp.toNat - 56, 48), (adrEvData, 16), (tp, tl), (adrQ1, 8), (adrQ2, 8)] ∧
      msgOf M adrFmt 26 (s.sp.toNat - 56) = strBytes s.mem tp tl ++ [58, 32, 104, 97, 118, 101, 32, 54, 52, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115] ∧
      errorfCost M adrFmt 26 (s.sp.toNat - 56) = 2 * (tl + 24) + 48 ∧ operandD M (s.sp.toNat - 56) 0 = adrEvData := by
    intro M hf' hA0 hA1 hA2 hA3 hA4 hA5
    have hrd : ∀ a n, Outside a n [(s.sp.toNat - 4208, s.sp.toNat)] → M.readLE a n = s.mem.readLE a n :=
      fun a n h => hf'.readLE a n h
    have hacc : ∀ a n w, M.accessible a n w = s.mem.accessible a n w := fun a n w => hf'.accessible a n w
    have hW1 : ∀ a n, a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat ≤ a → Outside a n [(s.sp.toNat - 4208, s.sp.toNat)] := by
      intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
    have hfm : M.readLE adrFmt 26 = fmtNum := by
      rw [hrd _ _ (hW1 _ _ (by omega)), h_rodata adrFmt 26 (by decide +kernel)]; decide +kernel
    have hv64 : M.readLE adrQ1 8 = 64 := by
      rw [hrd _ _ (hW1 _ _ (by omega)), h_rodata adrQ1 8 (by decide +kernel)]; decide +kernel
    have hv32 : M.readLE adrQ2 8 = 32 := by
      rw [hrd _ _ (hW1 _ _ (by omega)), h_rodata adrQ2 8 (by decide +kernel)]; decide +kernel
    have hfR : Readable M adrFmt 26 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Memory.accessible_mono _ h_data2 (by omega) (by omega)⟩
    have hsR : Readable M (s.sp.toNat - 56) 48 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hw4 (by omega) (by omega))⟩
    have heR : Readable M adrEvData 16 := ⟨by omega, fun _ => by rw [hacc]; exact hv4⟩
    have htR : Readable M tp tl :=
      ⟨htpb, fun hpos => by rw [hacc]; rcases htx with h | h; omega; exact h⟩
    have hq1R : Readable M adrQ1 8 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Memory.accessible_mono _ h_data3 (by omega) (by omega)⟩
    have hq2R : Readable M adrQ2 8 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Memory.accessible_mono _ h_data3 (by omega) (by omega)⟩
    have hA1' : M.readLE (s.sp.toNat - 56 + 8) 8 = adrEvData := by
      rw [show s.sp.toNat - 56 + 8 = s.sp.toNat - 48 by omega]; exact hA1
    have hA2' : M.readLE (s.sp.toNat - 56 + 16) 8 = adrTInt := by
      rw [show s.sp.toNat - 56 + 16 = s.sp.toNat - 40 by omega]; exact hA2
    have hA3' : M.readLE (s.sp.toNat - 56 + 24) 8 = adrQ1 := by
      rw [show s.sp.toNat - 56 + 24 = s.sp.toNat - 32 by omega]; exact hA3
    have hA4' : M.readLE (s.sp.toNat - 56 + 32) 8 = adrTInt := by
      rw [show s.sp.toNat - 56 + 32 = s.sp.toNat - 24 by omega]; exact hA4
    have hA5' : M.readLE (s.sp.toNat - 56 + 40) 8 = adrQ2 := by
      rw [show s.sp.toNat - 56 + 40 = s.sp.toNat - 16 by omega]; exact hA5
    have htp' : M.readLE adrEvData 8 = tp := by rw [hrd _ _ (hW1 _ _ (by omega))]; exact hv5
    have htl' : M.readLE (adrEvData + 8) 8 = tl := by rw [hrd _ _ (hW1 _ _ (by omega))]; exact hv6
    have hargs := ErrorfConsumer.argsOK_real (Env.mk tErr iErr tInt iWrap) 4294967296 M adrFmt (s.sp.toNat - 56)
      adrEvData tp tl adrQ1 adrQ2 (by decide) hfm hfR hsR hA0 hA1' (by decide) heR htp' htl' htR hA2' hA3' (by decide)
      hq1R hA4' hA5' (by decide) hq2R (by omega)
    have hn : nDec (segsOf M adrFmt 26) = 2 := by rw [segsOf_real _ _ _ rfl hfm]; decide
    have hstr : strBytes M tp tl = strBytes s.mem tp tl := by
      apply strBytes_congr
      intro i hi
      exact hf'.bytes (hW1 _ _ (by omega))
    have hmsg : msgOf M adrFmt 26 (s.sp.toNat - 56) = strBytes s.mem tp tl ++ [58, 32, 104, 97, 118, 101, 32, 54, 52, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115] := by
      rw [msgOf_real _ _ _ _ rfl hfm, hA1', htp', htl', hA3', hA5', hv64, hv32, hstr]
      have d64 : decBytes (toSigned 64) = [54, 52] := by decide
      have d32 : decBytes (toSigned 32) = [51, 50] := by decide
      rw [d64, d32]; rfl
    have hmlen : (msgOf M adrFmt 26 (s.sp.toNat - 56)).length = tl + 24 := by
      rw [hmsg]; simp [strBytes]
    have hcost : errorfCost M adrFmt 26 (s.sp.toNat - 56) = 2 * (tl + 24) + 48 := by
      unfold errorfCost; rw [hmlen, if_neg (by omega)]; simp only [wrapBytes]; omega
    have hreads : errorfReads M adrFmt 26 (s.sp.toNat - 56) =
        [(adrFmt, 26), (s.sp.toNat - 56, 48), (adrEvData, 16), (tp, tl), (adrQ1, 8), (adrQ2, 8)] := by
      unfold errorfReads
      rw [hn]
      simp [operandD, hA1', htp', htl', hA3', hA5', List.range_succ]
    exact ⟨hargs, hreads, hmsg, hcost, by unfold operandD; exact hA1'⟩
  have key : ∀ S : State, MemFrame s.mem S.mem [(s.sp.toNat - 4208, s.sp.toNat)] → S.regs 28 = s.regs 28 →
      S.sp.toNat + 112 = s.sp.toNat → (S.regs 30).toNat % 4 = 0 → (S.regs 30).toNat < 2 ^ 48 →
      S.regs 0 = (BitVec.ofNat 64 adrFmt) → S.regs 1 = 26#64 → S.regs 2 = s.sp - 56#64 → S.regs 3 = 3#64 → S.regs 4 = 3#64 →
      S.mem.readLE (s.sp.toNat - 56) 8 = adrTErr → S.mem.readLE (s.sp.toNat - 48) 8 = adrEvData →
      S.mem.readLE (s.sp.toNat - 40) 8 = adrTInt → S.mem.readLE (s.sp.toNat - 32) 8 = adrQ1 →
      S.mem.readLE (s.sp.toNat - 24) 8 = adrTInt → S.mem.readLE (s.sp.toNat - 16) 8 = adrQ2 →
      (CallOK S 4096 5 ∧ StackRoom S 4096 5 ∧
        ArgsOK (Env.mk tErr iErr tInt iWrap) 26 fmtNum 4294967296 S.mem (S.regs 0).toNat (S.regs 1).toNat
          (S.regs 2).toNat (S.regs 3).toNat (S.regs 4).toNat ∧
        ReadsOutside (errorfReads S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) (calleeStack S 4096 5) ∧
        ReadsSafe R L (errorfReads S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) ∧
        LiveAt R (Extracted.program.contractAddr "fmt.errorf")
          [(S.regs 0).toNat, (S.regs 1).toNat, (S.regs 2).toNat, (S.regs 3).toNat, (S.regs 4).toNat] L bud
          (errorfCost S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) (S.regs 28).toNat S.mem
          (calleeStack S 4096 5)) := by
    intro S hf' hg hsp h30a h30b h0 h1 h2 h3 h4 hA0 hA1 hA2 hA3 hA4 hA5
    have e0 : (S.regs 0).toNat = adrFmt := by rw [h0]; rfl
    have e1 : (S.regs 1).toNat = 26 := by rw [h1]; rfl
    have e2 : (S.regs 2).toNat = s.sp.toNat - 56 := by rw [h2]; exact hsp56
    have e3 : (S.regs 3).toNat = 3 := by rw [h3]; rfl
    have e4 : (S.regs 4).toNat = 3 := by rw [h4]; rfl
    rw [e0, e1, e2, e3, e4]
    obtain ⟨hargs, hreads, hmsg, hcosteq, hop⟩ := facts S.mem hf' hA0 hA1 hA2 hA3 hA4 hA5
    have hc := call_pre R L bud (errorfCost S.mem adrFmt 26 (s.sp.toNat - 56))
      (Extracted.program.contractAddr "fmt.errorf") [adrFmt, 26, s.sp.toNat - 56, 3, 3]
      (s := s) (S := S) (lo := s.sp.toNat - 4208) (hi := s.sp.toNat) (stack := 4096) (nargs := 5) (fr := 112)
      hg1 hg2 (by omega) hgo (hf'.widen R.rt) hg hsp (by omega) h30a h30b (by decide) (by omega) (by omega) (by omega) ha4
      (by rw [show s.sp.toNat - (s.sp.toNat - 4208) = 4208 + 0 by omega]; exact hw4) hwrt hwL hok
      (by rw [hg]; exact RtInv.inv_frame hf' hwrt hinv) (by omega)
    refine ⟨hc.1, hc.2.1, hargs, ?_, ?_, hc.2.2⟩
    · rw [hreads]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [calleeStack, outside_cons, outside_nil, and_true]
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [] <;> omega
    · rw [hreads]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hwin : ∀ a n, s.sp.toNat - 4208 ≤ a → a + n ≤ s.sp.toNat → Outside a n R.rt := fun a n h1 h2 =>
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
  exact key

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (R : RtInv)
    (hf : ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R
      tErr iErr tInt iWrap 26 fmtNum 4294967296)
    (L : List (Nat × Nat)) (bud tp tl : Nat) :
    Ensures (Extracted.program.link impl) Extracted.entry [] (Pre R L bud tp tl)
      (Post R L bud tp tl) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, ⟨hv1, hv2, hv3, hv4, hv5, hv6, htl, htpb, htx⟩, hgo, hwrt, hwL, hok,
    hinv, hbud, hdataO, hevO, hevDO, hevW, hevDW, htW, htO⟩
  janus_intro hs
  janus_data hd [hw4]
  janus_eval_nat hFA : fmtAddr
  simp only [ev, evType, evData, Extracted.dataAddr.«example.com/basic.errBadLen»,
    Extracted.dataAddr.«example.com/basic.errBadLen→type», Extracted.dataAddr.«example.com/basic.errBadLen→data»] at hv1 hv2 hv3 hv4 hv5 hv6 hevO hevDO hevW hevDW
  rw [hFA] at hok
  have hO2 : Outside adrFmt 256 R.rt := hdataO _ (List.getElem_mem (l := Extracted.program.data) (n := 2) (by decide))
  have hO3 : Outside adrQ1 80 R.rt := hdataO _ (List.getElem_mem (l := Extracted.program.data) (n := 3) (by decide))
  have hsp112 : (s.sp - 112#64).toNat = s.sp.toNat - 112 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hsp56 : (s.sp - 56#64).toNat = s.sp.toNat - 56 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have facts : ∀ M : Memory, MemFrame s.mem M [(s.sp.toNat - 4208, s.sp.toNat)] →
      M.readLE (s.sp.toNat - 56) 8 = adrTErr → M.readLE (s.sp.toNat - 48) 8 = adrEvData →
      M.readLE (s.sp.toNat - 40) 8 = adrTInt → M.readLE (s.sp.toNat - 32) 8 = adrQ1 →
      M.readLE (s.sp.toNat - 24) 8 = adrTInt → M.readLE (s.sp.toNat - 16) 8 = adrQ2 →
      ArgsOK (Env.mk tErr iErr tInt iWrap) 26 fmtNum 4294967296 M adrFmt 26 (s.sp.toNat - 56) 3 3 ∧
      errorfReads M adrFmt 26 (s.sp.toNat - 56) =
        [(adrFmt, 26), (s.sp.toNat - 56, 48), (adrEvData, 16), (tp, tl), (adrQ1, 8), (adrQ2, 8)] ∧
      msgOf M adrFmt 26 (s.sp.toNat - 56) = strBytes s.mem tp tl ++ [58, 32, 104, 97, 118, 101, 32, 54, 52, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115] ∧
      errorfCost M adrFmt 26 (s.sp.toNat - 56) = 2 * (tl + 24) + 48 ∧ operandD M (s.sp.toNat - 56) 0 = adrEvData := by
    intro M hf' hA0 hA1 hA2 hA3 hA4 hA5
    have hrd : ∀ a n, Outside a n [(s.sp.toNat - 4208, s.sp.toNat)] → M.readLE a n = s.mem.readLE a n :=
      fun a n h => hf'.readLE a n h
    have hacc : ∀ a n w, M.accessible a n w = s.mem.accessible a n w := fun a n w => hf'.accessible a n w
    have hW1 : ∀ a n, a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat ≤ a → Outside a n [(s.sp.toNat - 4208, s.sp.toNat)] := by
      intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
    have hfm : M.readLE adrFmt 26 = fmtNum := by
      rw [hrd _ _ (hW1 _ _ (by omega)), h_rodata adrFmt 26 (by decide +kernel)]; decide +kernel
    have hv64 : M.readLE adrQ1 8 = 64 := by
      rw [hrd _ _ (hW1 _ _ (by omega)), h_rodata adrQ1 8 (by decide +kernel)]; decide +kernel
    have hv32 : M.readLE adrQ2 8 = 32 := by
      rw [hrd _ _ (hW1 _ _ (by omega)), h_rodata adrQ2 8 (by decide +kernel)]; decide +kernel
    have hfR : Readable M adrFmt 26 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Memory.accessible_mono _ h_data2 (by omega) (by omega)⟩
    have hsR : Readable M (s.sp.toNat - 56) 48 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hw4 (by omega) (by omega))⟩
    have heR : Readable M adrEvData 16 := ⟨by omega, fun _ => by rw [hacc]; exact hv4⟩
    have htR : Readable M tp tl :=
      ⟨htpb, fun hpos => by rw [hacc]; rcases htx with h | h; omega; exact h⟩
    have hq1R : Readable M adrQ1 8 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Memory.accessible_mono _ h_data3 (by omega) (by omega)⟩
    have hq2R : Readable M adrQ2 8 :=
      ⟨by omega, fun _ => by rw [hacc]; exact Memory.accessible_mono _ h_data3 (by omega) (by omega)⟩
    have hA1' : M.readLE (s.sp.toNat - 56 + 8) 8 = adrEvData := by
      rw [show s.sp.toNat - 56 + 8 = s.sp.toNat - 48 by omega]; exact hA1
    have hA2' : M.readLE (s.sp.toNat - 56 + 16) 8 = adrTInt := by
      rw [show s.sp.toNat - 56 + 16 = s.sp.toNat - 40 by omega]; exact hA2
    have hA3' : M.readLE (s.sp.toNat - 56 + 24) 8 = adrQ1 := by
      rw [show s.sp.toNat - 56 + 24 = s.sp.toNat - 32 by omega]; exact hA3
    have hA4' : M.readLE (s.sp.toNat - 56 + 32) 8 = adrTInt := by
      rw [show s.sp.toNat - 56 + 32 = s.sp.toNat - 24 by omega]; exact hA4
    have hA5' : M.readLE (s.sp.toNat - 56 + 40) 8 = adrQ2 := by
      rw [show s.sp.toNat - 56 + 40 = s.sp.toNat - 16 by omega]; exact hA5
    have htp' : M.readLE adrEvData 8 = tp := by rw [hrd _ _ (hW1 _ _ (by omega))]; exact hv5
    have htl' : M.readLE (adrEvData + 8) 8 = tl := by rw [hrd _ _ (hW1 _ _ (by omega))]; exact hv6
    have hargs := ErrorfConsumer.argsOK_real (Env.mk tErr iErr tInt iWrap) 4294967296 M adrFmt (s.sp.toNat - 56)
      adrEvData tp tl adrQ1 adrQ2 (by decide) hfm hfR hsR hA0 hA1' (by decide) heR htp' htl' htR hA2' hA3' (by decide)
      hq1R hA4' hA5' (by decide) hq2R (by omega)
    have hn : nDec (segsOf M adrFmt 26) = 2 := by rw [segsOf_real _ _ _ rfl hfm]; decide
    have hstr : strBytes M tp tl = strBytes s.mem tp tl := by
      apply strBytes_congr
      intro i hi
      exact hf'.bytes (hW1 _ _ (by omega))
    have hmsg : msgOf M adrFmt 26 (s.sp.toNat - 56) = strBytes s.mem tp tl ++ [58, 32, 104, 97, 118, 101, 32, 54, 52, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115] := by
      rw [msgOf_real _ _ _ _ rfl hfm, hA1', htp', htl', hA3', hA5', hv64, hv32, hstr]
      have d64 : decBytes (toSigned 64) = [54, 52] := by decide
      have d32 : decBytes (toSigned 32) = [51, 50] := by decide
      rw [d64, d32]; rfl
    have hmlen : (msgOf M adrFmt 26 (s.sp.toNat - 56)).length = tl + 24 := by
      rw [hmsg]; simp [strBytes]
    have hcost : errorfCost M adrFmt 26 (s.sp.toNat - 56) = 2 * (tl + 24) + 48 := by
      unfold errorfCost; rw [hmlen, if_neg (by omega)]; simp only [wrapBytes]; omega
    have hreads : errorfReads M adrFmt 26 (s.sp.toNat - 56) =
        [(adrFmt, 26), (s.sp.toNat - 56, 48), (adrEvData, 16), (tp, tl), (adrQ1, 8), (adrQ2, 8)] := by
      unfold errorfReads
      rw [hn]
      simp [operandD, hA1', htp', htl', hA3', hA5', List.range_succ]
    exact ⟨hargs, hreads, hmsg, hcost, by unfold operandD; exact hA1'⟩
  have key : ∀ S : State, MemFrame s.mem S.mem [(s.sp.toNat - 4208, s.sp.toNat)] → S.regs 28 = s.regs 28 →
      S.sp.toNat + 112 = s.sp.toNat → (S.regs 30).toNat % 4 = 0 → (S.regs 30).toNat < 2 ^ 48 →
      S.regs 0 = (BitVec.ofNat 64 adrFmt) → S.regs 1 = 26#64 → S.regs 2 = s.sp - 56#64 → S.regs 3 = 3#64 → S.regs 4 = 3#64 →
      S.mem.readLE (s.sp.toNat - 56) 8 = adrTErr → S.mem.readLE (s.sp.toNat - 48) 8 = adrEvData →
      S.mem.readLE (s.sp.toNat - 40) 8 = adrTInt → S.mem.readLE (s.sp.toNat - 32) 8 = adrQ1 →
      S.mem.readLE (s.sp.toNat - 24) 8 = adrTInt → S.mem.readLE (s.sp.toNat - 16) 8 = adrQ2 →
      (CallOK S 4096 5 ∧ StackRoom S 4096 5 ∧
        ArgsOK (Env.mk tErr iErr tInt iWrap) 26 fmtNum 4294967296 S.mem (S.regs 0).toNat (S.regs 1).toNat
          (S.regs 2).toNat (S.regs 3).toNat (S.regs 4).toNat ∧
        ReadsOutside (errorfReads S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) (calleeStack S 4096 5) ∧
        ReadsSafe R L (errorfReads S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) ∧
        LiveAt R (Extracted.program.contractAddr "fmt.errorf")
          [(S.regs 0).toNat, (S.regs 1).toNat, (S.regs 2).toNat, (S.regs 3).toNat, (S.regs 4).toNat] L bud
          (errorfCost S.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat) (S.regs 28).toNat S.mem
          (calleeStack S 4096 5)) := by
    intro S hf' hg hsp h30a h30b h0 h1 h2 h3 h4 hA0 hA1 hA2 hA3 hA4 hA5
    have e0 : (S.regs 0).toNat = adrFmt := by rw [h0]; rfl
    have e1 : (S.regs 1).toNat = 26 := by rw [h1]; rfl
    have e2 : (S.regs 2).toNat = s.sp.toNat - 56 := by rw [h2]; exact hsp56
    have e3 : (S.regs 3).toNat = 3 := by rw [h3]; rfl
    have e4 : (S.regs 4).toNat = 3 := by rw [h4]; rfl
    rw [e0, e1, e2, e3, e4]
    obtain ⟨hargs, hreads, hmsg, hcosteq, hop⟩ := facts S.mem hf' hA0 hA1 hA2 hA3 hA4 hA5
    have hc := call_pre R L bud (errorfCost S.mem adrFmt 26 (s.sp.toNat - 56))
      (Extracted.program.contractAddr "fmt.errorf") [adrFmt, 26, s.sp.toNat - 56, 3, 3]
      (s := s) (S := S) (lo := s.sp.toNat - 4208) (hi := s.sp.toNat) (stack := 4096) (nargs := 5) (fr := 112)
      hg1 hg2 (by omega) hgo (hf'.widen R.rt) hg hsp (by omega) h30a h30b (by decide) (by omega) (by omega) (by omega) ha4
      (by rw [show s.sp.toNat - (s.sp.toNat - 4208) = 4208 + 0 by omega]; exact hw4) hwrt hwL hok
      (by rw [hg]; exact RtInv.inv_frame hf' hwrt hinv) (by omega)
    refine ⟨hc.1, hc.2.1, hargs, ?_, ?_, hc.2.2⟩
    · rw [hreads]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [calleeStack, outside_cons, outside_nil, and_true]
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [] <;> omega
    · rw [hreads]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hwin : ∀ a n, s.sp.toNat - 4208 ≤ a → a + n ≤ s.sp.toNat → Outside a n R.rt := fun a n h1 h2 =>
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
  have post_facts : ∀ (M m1 : Memory), MemFrame M m1 (R.rt ++ [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8), (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 8 * 5)]) →
      MemFrame s.mem M [(s.sp.toNat - 4208, s.sp.toNat)] →
      M.readLE (s.sp.toNat - 56) 8 = adrTErr → M.readLE (s.sp.toNat - 48) 8 = adrEvData →
      M.readLE (s.sp.toNat - 40) 8 = adrTInt → M.readLE (s.sp.toNat - 32) 8 = adrQ1 →
      M.readLE (s.sp.toNat - 24) 8 = adrTInt → M.readLE (s.sp.toNat - 16) 8 = adrQ2 →
      M.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat → M.readLE (s.sp.toNat - 112) 8 = ret →
      LiveFrame M m1 L [] → ∀ a b : Nat,
      ErrorfPost (Env.mk tErr iErr tInt iWrap) R M adrFmt 26 (s.sp.toNat - 56) [(s.sp.toNat - 112 - 4096, s.sp.toNat - 112 - 8), (s.sp.toNat - 112 + 8, s.sp.toNat - 112 + 8 + 8 * 5)] L bud (s.regs 28).toNat a b m1 →
      m1.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat ∧ m1.readLE (s.sp.toNat - 112) 8 = ret ∧
        m1.accessible (s.sp.toNat - 120) 8 false = true ∧ m1.accessible (s.sp.toNat - 112) 8 false = true ∧
        a = iWrap ∧ b + 32 ≤ 2 ^ 48 ∧ m1.accessible b 32 true = true ∧ m1.readLE (b + 8) 8 = tl + 24 ∧
        strBytes m1 (m1.readLE b 8) (tl + 24) = strBytes s.mem tp tl ++ [58, 32, 104, 97, 118, 101, 32, 54, 52, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115] ∧
        m1.readLE (b + 16) 8 = iErr ∧ m1.readLE (b + 24) 8 = evData ∧ FreshFrom [(b, b + 32)] L ∧
        InRanges b 32 R.rt ∧ MemFrame s.mem m1 (R.rt ++ [(s.sp.toNat - 4208, s.sp.toNat)]) ∧
        LiveFrame s.mem m1 L [] ∧
        R.inv (bud - (2 * (tl + 24) + 48)) (L ++ ((b, b + 32) :: range0 (m1.readLE b 8) (tl + 24)))
          (s.regs 28).toNat (view R.rt (L ++ ((b, b + 32) :: range0 (m1.readLE b 8) (tl + 24))) m1) := by
    intro M m1 hfr hMF hA0 hA1 hA2 hA3 hA4 hA5 h29 h30 hlf a b hp
    obtain ⟨hargs, hreads, hmsgM, hcostM, hopM⟩ := facts M hMF hA0 hA1 hA2 hA3 hA4 hA5
    obtain ⟨hiw, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hfresh, hinr, hsep1, hsep2, hinv'⟩ := hp
    have hwin : ∀ a n, s.sp.toNat - 4208 ≤ a → a + n ≤ s.sp.toNat - 120 → Outside a n R.rt := fun a n h1 h2 =>
      Outside.of_sub (hwrt _ (List.mem_singleton_self _)) h1 (by simp only; omega)
    have hwin2 : ∀ a n, s.sp.toNat - 120 ≤ a → a + n ≤ s.sp.toNat → Outside a n R.rt := fun a n h1 h2 =>
      Outside.of_sub (hwrt _ (List.mem_singleton_self _)) (by omega) (by simp only; omega)
    have hs29 : m1.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat := by
      rw [hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hwin2 _ _ (by omega) (by omega), by omega, by omega⟩)]
      exact h29
    have hs30 : m1.readLE (s.sp.toNat - 112) 8 = ret := by
      rw [hfr.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hwin2 _ _ (by omega) (by omega), by omega, by omega⟩)]
      exact h30
    have hacc : ∀ a n w, m1.accessible a n w = s.mem.accessible a n w := fun a n w => by
      rw [hfr.accessible, hMF.accessible]
    have hmlen : (msgOf M adrFmt 26 (s.sp.toNat - 56)).length = tl + 24 := by
      rw [hmsgM]; simp [strBytes]
    refine ⟨hs29, hs30, ?_, ?_, hiw, ?_, ?_, ?_, ?_, ?_, ?_, hfresh, hinr, ?_, ?_, ?_⟩
    · rw [hacc]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hw4 (by omega) (by omega))
    · rw [hacc]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hw4 (by omega) (by omega))
    · simpa [wrapBytes] using hd1
    · exact hd2
    · rw [hmlen] at hd3; exact hd3
    · rw [hmlen, hmsgM] at hd4; exact hd4
    · simp only [wrapErrOffset] at hd6; exact hd6
    · simp only [wrapErrOffset] at hd7; rw [hopM] at hd7; exact hd7
    · exact MemFrame.trans hMF hfr (by frame_sub)
    · exact LiveFrame.trans (LiveFrame.of_win (ws := [(s.sp.toNat - 4208, s.sp.toNat)]) hMF hwL) hlf (fun _ _ h => h)
    · rw [hcostM] at hinv'; rw [hmlen] at hinv'; exact hinv'
  janus_run [hv2, hv3] until [Extracted.program.contractAddr "fmt.errorf"]
  refine Reaches.call (Summary.withExit (hf L bud) hret) rfl
    (key _ (by janus_frame) (by simp [setReg]) (by simp [hsp112]; omega) (by simp [setReg]) (by simp [setReg])
      (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])) ?_
  intro s' hpc' ⟨r, vr, fl, m1, ex1, ep1, hs1, hfr1, hlf1, hpost⟩
  subst hs1
  simp only [calleeStack, setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    hsp112, hsp56] at hfr1 hlf1 hpost
  have hr := post_facts _ _ hfr1 (by janus_frame)
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self])
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self];
          exact Nat.mod_eq_of_lt (by have h := (s.regs 29).isLt; have : (256 : Nat) ^ 8 = 2 ^ 64 := (by decide); omega))
      (by (try dsimp only); (repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]); rw [Memory.readLE_writeLE_self];
          exact Nat.mod_eq_of_lt (by have h := hret.user; have : (256 : Nat) ^ 8 = 2 ^ 64 := (by decide); omega))
      hlf1 _ _ hpost
  obtain ⟨hs29, hs30, hacc29, hacc30, hiw, hrest⟩ := hr
  have hr0 : r 0 ≠ 0#64 := fun h => by
    rw [h] at hiw
    exact absurd hiw (by decide)
  unfold Post
  janus_run [hs29, hs30, hr0]
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hMf, hLf, hInv⟩ := hrest
  refine ⟨hiw, (r 1).toNat, rfl, by omega, by rw [← hMf.accessible]; exact hB, hC, hD, hE, hF, ?_, hH, hMf, hLf, ?_⟩
  · simpa [freshFrom_cons, freshFrom_nil] using hG
  · simpa [range0] using hInv

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The stub of `ErrorfRealImpl` placed at `fmt.errorf`'s contract address (`errorf_live_at`), the toy runtime with the constants
cell (`errR`), a state with `errBadLen` holding its link-time image and the text `"bad length"`, an admissible return address:
`correctness` applies (`nonvacuous`) and `ErrWrap` returns the wrapped error (`returns`). -/

namespace Witness

open Janus.Contracts.Toy Janus.Contracts.ErrorfRealRt

def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000
def retA : Nat := 0x1000
def textAddr : Nat := ev + 0x30
def txtNum : Nat := 493273389536941829284194

/-- The byte of the program's static data at `a`. -/
def dat (a : Nat) : Option Nat :=
  Extracted.data.findSome? fun d =>
    if d.base ≤ a ∧ a < d.base + d.bytes.length then some (d.bytes.getD (a - d.base) 0) else none

def regions0 : List Region :=
  [⟨sp0 - 4208, 4208, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨ev, 0x40, true⟩] ++
    Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩

def base : Memory :=
  (((((((((⟨fun _ => 0, regions0⟩ : Memory).writeLE ev 8 evType).writeLE (ev + 8) 8 evData).writeLE evData 8 textAddr).writeLE
    (evData + 8) 8 10).writeLE textAddr 10 txtNum).writeLE BUMP 8 HEAP).writeLE CELL 8 iErr).writeLE (CELL + 8) 8 iWrap).writeLE
    (g0 + 16) 8 0x1000

def mem0 : Memory := ⟨fun a => match dat a with | some b => BitVec.ofNat 8 b | none => base.bytes a, regions0⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded mem0 := by
  unfold Program.DataLoaded
  decide +kernel


def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 retA else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry, flags := ⟨false, false, false, false⟩, mem := mem0 }

abbrev cAddr : Nat := Extracted.program.contractAddr "fmt.errorf"
def implAt : List Segment := [Janus.Contracts.ErrorfRealLive.errorfSeg cAddr]
def R0 : RtInv := errR [] iErr iWrap (fun _ _ => True)

theorem tysOK : TysOK ([] : Tys) := by intro t ht; simp at ht

theorem hf0 : ErrorfLive (Extracted.program.link implAt) cAddr 4096 R0 tErr iErr tInt iWrap 26 fmtNum 4294967296 :=
  Janus.Contracts.ErrorfRealLive.errorf_live_at _ cAddr [] tysOK tErr tInt iErr iWrap (by decide) (by decide) (by decide)
    (Janus.Contracts.ErrorfRealLive.fetchedAt_link Extracted.program cAddr (by decide +kernel) (by decide +kernel)
      (by decide +kernel))

theorem hret0 : RetAddr (Extracted.program.link implAt) retA := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link implAt).withExit retA) Extracted.entry [] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h⟩


set_option maxRecDepth 100000

theorem dat_none (i : Nat) (h : 2000000 ≤ i) : dat i = none := by
  unfold dat
  rw [List.findSome?_eq_none_iff]
  intro d hd
  have hb : ∀ d ∈ Extracted.data, d.base + d.bytes.length ≤ 2000000 := by decide +kernel
  have := hb d hd
  simp only [ite_eq_right_iff]
  intro hc; omega

theorem base_zero (i : Nat) (h : 268435456 ≤ i) : base.bytes i = 0 := by
  unfold base
  repeat rw [Memory.bytes_writeLE_outside]
  all_goals first
    | rfl
    | (simp only [ev, evType, evData, Extracted.dataAddr.«example.com/basic.errBadLen»,
        Extracted.dataAddr.«example.com/basic.errBadLen→type», Extracted.dataAddr.«example.com/basic.errBadLen→data», textAddr,
        BUMP, HEAP, CELL, g0]
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
      simp only [Memory.readLE, Nat.mul_zero, Nat.add_zero]
      rw [mem0_zero i (by simp [HEAP, HEND, HSIZE] at *; omega)]; rfl
    · decide
    · decide
    · decide
  · rw [readLE_view (inRanges_cell [] (Nat.le_refl _) (by omega)) (by simp [outside_nil])]; decide
  · rw [readLE_view (inRanges_cell [] (by omega) (by omega)) (by simp [outside_nil])]; decide
  · rw [view_accessible]; decide


theorem pre0 : Pre R0 [] 116 textAddr 10 s0 := by
  have hrt : R0.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64), (CELL, CELL + 16)] := rfl
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_, ?_, ?_,
    rinv0 _, by decide, ?_, ?_, ?_, by decide, by decide, by decide, ?_⟩
  · unfold ErrHolds; refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · rw [hrt]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [hrt]; intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  · intro r hr; simp at hr
  · show True; trivial
  · rw [hrt]
    intro d hd
    have : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length
        [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64), (CELL, CELL + 16)] := by
      simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]
      decide +kernel
    exact this d hd
  · rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  · rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide
  · right; left
    rw [hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF, CELL]; decide

/-- The call state at `fmt.errorf`'s entry: `ErrWrap`'s frame (112 below), the three `any` operands in place. -/
def mC : Memory :=
  ((((((mem0.writeLE (sp0 - 56) 8 tErr).writeLE (sp0 - 48) 8 evData).writeLE (sp0 - 40) 8 tInt).writeLE (sp0 - 32) 8
    Extracted.dataAddr.«.rodata#4de38626»).writeLE (sp0 - 24) 8 tInt).writeLE (sp0 - 16) 8
    Extracted.dataAddr.«.rodata#df6f96c5»)

def wsC : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 fmtAddr else if i = 1 then 26#64 else if i = 2 then BitVec.ofNat 64 (sp0 - 56)
      else if i = 3 then 3#64 else if i = 4 then 3#64 else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 (Extracted.entry + 0x68) else 0,
    sp := BitVec.ofNat 64 (sp0 - 112), pc := BitVec.ofNat 64 cAddr, flags := ⟨false, false, false, false⟩, mem := mC }

theorem fr_step {m : Memory} {a v : Nat} (h : MemFrame mem0 m [(sp0 - 4208, sp0)]) (h1 : sp0 - 4208 ≤ a) (h2 : a + 8 ≤ sp0) :
    MemFrame mem0 (m.writeLE a 8 v) [(sp0 - 4208, sp0)] := h.writeLE v (List.mem_singleton.2 rfl) h1 h2

theorem mC_frame : MemFrame s0.mem wsC.mem [(s0.sp.toNat - 4208, s0.sp.toNat)] := by
  show MemFrame mem0 mC [(sp0 - 4208, sp0)]
  unfold mC sp0
  exact fr_step (fr_step (fr_step (fr_step (fr_step (fr_step (MemFrame.refl _ _) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)

theorem mC_rd0 : wsC.mem.readLE (s0.sp.toNat - 56) 8 = adrTErr := by
  show mC.readLE (sp0 - 56) 8 = _
  unfold mC sp0
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (by decide +kernel)

theorem mC_rd1 : wsC.mem.readLE (s0.sp.toNat - 48) 8 = adrEvData := by
  show mC.readLE (sp0 - 48) 8 = _
  unfold mC sp0
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (by decide +kernel)

theorem mC_rd2 : wsC.mem.readLE (s0.sp.toNat - 40) 8 = adrTInt := by
  show mC.readLE (sp0 - 40) 8 = _
  unfold mC sp0
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (by decide +kernel)

theorem mC_rd3 : wsC.mem.readLE (s0.sp.toNat - 32) 8 = adrQ1 := by
  show mC.readLE (sp0 - 32) 8 = _
  unfold mC sp0
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (by decide +kernel)

theorem mC_rd4 : wsC.mem.readLE (s0.sp.toNat - 24) 8 = adrTInt := by
  show mC.readLE (sp0 - 24) 8 = _
  unfold mC sp0
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (by decide +kernel)

theorem mC_rd5 : wsC.mem.readLE (s0.sp.toNat - 16) 8 = adrQ2 := by
  show mC.readLE (sp0 - 16) 8 = _
  unfold mC sp0
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (by decide +kernel)

theorem wsC_pre : erSite R0 [] 116 wsC :=
  siteKey R0 [] 116 textAddr 10 s0 pre0 wsC mC_frame rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) mC_rd0 mC_rd1 mC_rd2 mC_rd3 mC_rd4 mC_rd5

/-- The guarantee fires: `ErrWrap()` from the witness state returns the wrapped error. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit retA) s0 fun s' =>
    ABIReturn s0 s' ∧ Post R0 [] 116 textAddr 10 s0 s' :=
  correctness implAt R0 hf0 [] 116 textAddr 10 retA hret0 s0 setup pre0

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (L : List (Nat × Nat)) (bud tp tl : Nat) (ret : Nat) (s : State),
    ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R tErr iErr tInt iWrap 26
      fmtNum 4294967296 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [] s ∧ Pre R L bud tp tl s ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.errorf") ∧
      erSite R L bud s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R L bud tp tl s s' :=
  ⟨implAt, R0, [], 116, textAddr, 10, retA, s0, hf0, hret0, setup, pre0, ⟨wsC, rfl, wsC_pre⟩, returns⟩

end Witness

end Proof
