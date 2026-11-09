import Janus
import Janus.Contracts.LiveStubConvT
import Janus.Contracts.LiveStubConvTAmd64
import Janus.Contracts.ErrorfRealLive64

/-! # Red team round n9: today's new contracts (U14 live convT, U-GROWMULTI, ErrorfLive amd64)

Each claim below is FALSE or NOT ENTAILED by the contract it targets, and is refuted by Lean: a countermodel
(`∃ …` of a state the contract allows where the claim fails), a contradiction from the contract's own
precondition or postcondition, or `fail_if_success` on the natural proof. If one of these ever becomes provable, a
contract has become unsound. Rows named in `test/redteam/rounds/roundn9/run-roundn9.sh`. -/

namespace JanusTests.RedTeamN9

open Janus Janus.Arm64 Janus.Spec Janus.Contracts

/-! ## 1. U14 live `convTstring` / `convT64` (`IfaceLive`) -/

/-- A region [0x100, 0x110): writable, zero-initialised: the static `zeroVal`-like box. -/
def m0 : Memory := ⟨fun _ => 0, [⟨0x100, 0x10, true⟩]⟩
def rt0 : List (Nat × Nat) := [(0x100, 0x110)]

theorem box0 : BoxWords' rt0 m0 0x100 [0, 0] := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · exact ⟨(0x100, 0x110), by simp [rt0], by decide, by decide⟩
  · intro i hi
    have : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases this with rfl | rfl <;> (simp only [List.getElem_cons_zero, List.getElem_cons_succ]; decide)

/-- C1: "the empty-string box is preserved across a later runtime call" is NOT entailed: a later call may write the
runtime's ranges (`MemFrame … rt`), which contain the static box. A state where the box held `(0,0)` and holds `(1,0)`
after a frame-respecting call. -/
theorem c1_empty_box_not_preserved :
    ∃ m', MemFrame m0 m' rt0 ∧ ¬ BoxWords' rt0 m' 0x100 [0, 0] := by
  refine ⟨m0.writeLE 0x100 8 1, MemFrame.of_writeLE m0 1 (r := (0x100, 0x110)) (by simp [rt0]) (by decide) (by decide), ?_⟩
  intro h
  have := h.2.2.2 0 (by decide)
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at this
  rw [Memory.readLE_writeLE_self] at this
  revert this; decide

/-- C2: "a box outside the live set survives a later call" is NOT entailed: `LiveFrame` protects only the objects of
the live set; the static box is not in it, and the allocating branch's fresh box joins the live set only after the call. -/
theorem c2_box_outside_live_set_not_protected :
    ∃ m', LiveFrame m0 m' ([] : List (Nat × Nat)) [] ∧ ¬ BoxWords' rt0 m' 0x100 [0, 0] := by
  refine ⟨m0.writeLE 0x100 8 1, ⟨fun a n h _ => absurd h (by simp [InRanges])⟩, ?_⟩
  intro h
  have := h.2.2.2 0 (by decide)
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at this
  rw [Memory.readLE_writeLE_self] at this
  revert this; decide

/-- C3: a wrong length: the post pins both words, so a box cannot hold two different lengths. -/
theorem c3_wrong_length (rt : List (Nat × Nat)) (m : Memory) (p r0 len : Nat) :
    ¬ (BoxWords' rt m r0 [p, len] ∧ BoxWords' rt m r0 [p, len + 1]) := by
  rintro ⟨⟨-, -, -, h1⟩, ⟨-, -, -, h2⟩⟩
  have a := h1 1 (by simp); have b := h2 1 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at a b
  omega

/-- C3': the empty string's box holds length 0 (`arg a 1 = 0`), so a box claimed to hold length 5 contradicts the post. -/
theorem c3_empty_len_nonzero (rt : List (Nat × Nat)) (m : Memory) (a : List Nat) (r0 : Nat)
    (h0 : arg a 1 = 0) (hpost : BoxWords' rt m r0 [if arg a 1 = 0 then 0 else arg a 0, arg a 1])
    (hclaim : BoxWords' rt m r0 [0, 5]) : False := by
  have x := hpost.2.2.2 1 (by simp); have y := hclaim.2.2.2 1 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at x y
  omega

/-- C4: a stub charging cost 0 for `v ≥ 256` is not the live spec: its cost is a positive block. -/
theorem c4_cost_zero_big (m : Memory) : convT64Live.cost [256] m ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (convT64Live_cost_pos _ _ (by decide))

theorem c4_cost_zero_str (m : Memory) : convTstringLive.cost [7, 1] m ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (convTstringLive_cost_pos _ _ (by decide))

/-- C4': the allocating branch adds a fresh box to the live set (so a stub cannot treat it as static) -/
theorem c4_big_adds_box (m : Memory) (r0 r1 r2 : Nat) : liveAdds convT64Live [256] m r0 r1 r2 ≠ [] := by
  simp [liveAdds, convT64Live, arg]

-- A convT64 stub that advances the bump pointer by 0 (cost 0 for `v ≥ 256`) is not the live contract.
namespace Cost0
open Janus.Contracts.Toy Janus.Contracts.LiveStub

def P : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }
def tys : Tys := []
def ok : Nat → List Nat → Prop := fun a args => a = 0x62000 ∧ args = [300]
def R : RtInv := toyR tys ok
def linkedZero : Program := P.link [convT64Seg 0x62000 0]

theorem hok_6 : ∀ args, ok 0x62000 args → args = [300] := fun _ h => h.2

set_option maxHeartbeats 4000000 in
theorem rt_cost0_big : True := by
  fail_if_success
    have : RtLiveContract linkedZero 0x62000 4096 R convT64Spec convT64Live := by
      janus_live_convt64 300 0 hok_6
  trivial
end Cost0

/-! ## 2. U-GROWMULTI: `growsliceSpec` bounds -/

/-- G1: an old array whose end exceeds `2^48` violates the precondition. -/
theorem g1_old_end_bound (a : List Nat) (m : Memory) (h : growsliceSpec.pre a m) :
    arg a 0 + (arg a 1 - arg a 3) * typSize m (arg a 4) ≤ 2 ^ 48 := h.2.2.2.2.2.1

theorem g1_wrap_refuted (a : List Nat) (m : Memory)
    (hwrap : 2 ^ 48 < arg a 0 + (arg a 1 - arg a 3) * typSize m (arg a 4)) : ¬ growsliceSpec.pre a m :=
  fun h => absurd (g1_old_end_bound a m h) (Nat.not_le.mpr hwrap)

/-- G2: `newLen < oldLen` (`oldLen = newLen - num`) and `num > newLen` are both outside the precondition. -/
theorem g2_newlen_lt_oldlen (a : List Nat) (m : Memory) (h : growsliceSpec.pre a m) :
    ¬ arg a 1 < arg a 1 - arg a 3 := by have := h.2.1; omega

theorem g2_num_gt_newlen (a : List Nat) (m : Memory) (h : growsliceSpec.pre a m) : ¬ arg a 1 < arg a 3 := by
  have := h.2.1; omega

/-- G3: a cap overflow: the returned array fits below `2^48`, and the request is bounded below `2^46`. -/
theorem g3_cap_overflow_refuted (rt : List (Nat × Nat)) (m0 m : Memory) (old oldLen newLen size r0 cap : Nat) (noscan : Bool)
    (h : GrownArray rt m0 m old oldLen newLen size noscan r0 cap) (hbig : 2 ^ 48 < r0 + cap * size) : False :=
  absurd h.2.1 (Nat.not_le.mpr hbig)

theorem g3_request_bound (a : List Nat) (m : Memory) (h : growsliceSpec.pre a m) :
    arg a 1 * typSize m (arg a 4) < 2 ^ 46 := h.2.2.2.2.1

/-- G4: a stub that copies fewer bytes than the old length: the post copies every old byte. -/
theorem g4_short_copy_refuted (rt : List (Nat × Nat)) (m0 m : Memory) (old oldLen newLen size r0 cap : Nat) (noscan : Bool)
    (h : GrownArray rt m0 m old oldLen newLen size noscan r0 cap)
    (hshort : ∃ i, i < oldLen * size ∧ m.bytes (r0 + i) ≠ m0.bytes (old + i)) : False :=
  let ⟨i, hi, hne⟩ := hshort
  hne (h.2.2.2.1 i hi)

/-- G5: the capacity returned holds the new length (a stub returning cap < newLen is not the contract). -/
theorem g5_cap_lt_newlen (size : Nat) (noscan : Bool) (newLen oldCap : Nat) (h : 0 < size) :
    ¬ growCap size noscan newLen oldCap < newLen := Nat.not_lt.mpr (le_growCap size noscan newLen oldCap h)

/-! ## 3. `ErrorfLive` amd64 -/

namespace Errorf64
open Janus.Amd64 Janus.Contracts.ErrorfAmd64 Janus.Contracts.PoolAmd64 Janus.Contracts.ErrorfRealLive64 Janus.Contracts.Toy

/-- E2: the post shape of every amd64 live contract (`LiveRet`, hence `ErrorfLive`) does NOT preserve `R15`: a call
state where `R15` changes satisfies it. A consumer (or a callee summary derived from it) claiming `R15` survives is
refuted. -/
theorem e2_r15_not_preserved (R : RtInv) (stack nargs : Nat) (L : List (Nat × Nat)) (s : Janus.Amd64.State)
    (h : s.regs 15 = 0) :
    ∃ s', LiveRet R stack nargs L s s' (fun _ _ => True) ∧ s'.regs 15 ≠ s.regs 15 := by
  refine ⟨_, ⟨fun _ => 1, s.xmm, s.ymmHi, s.flags, s.mem, s.zmmHi, s.kreg, rfl, MemFrame.refl _ _, LiveFrame.refl _ _ _,
    trivial⟩, ?_⟩
  simp [MapAmd64.keepABI, h]

/-- E1: `RetLow` is `[RSP] < 2^46`, so every equivalent spelling is the same fact; a caller whose return address is
`2^46` or above is outside the precondition of `ErrorfLive` (so a stub placed above `2^46` can never be returned into). -/
theorem e1_retlow_alias_same (s : Janus.Amd64.State) :
    RetLow s ↔ s.mem.readLE (s.regs 4).toNat 8 + 1 ≤ 2 ^ 46 := by unfold RetLow; omega

theorem e1_retlow_false_for_high_ret (s : Janus.Amd64.State) (h : 2 ^ 46 ≤ s.mem.readLE (s.regs 4).toNat 8) : ¬ RetLow s :=
  fun hl => absurd hl (Nat.not_lt.mpr h)

/-- E3: `errorf_live_at64` needs the stub's bytes to be what the program fetches at the address (`FetchedAt64`) and the
copy to end below `2^47`: a stub that would not fit is rejected. -/
theorem e3_no_fit_rejected (p : Janus.Amd64.Program) (tys : Tys) (hty : TysOK tys) (tErr tInt iE iW : Nat)
    (hiE : iE < 2 ^ 64) (hiW : iW < 2 ^ 64) (hf : FetchedAt64 p (2 ^ 47 - 100)) : True := by
  fail_if_success
    refine (errorf_live_at64 p (2 ^ 47 - 100) tys hty tErr tInt iE iW hiE hiW ?_ hf :
      ErrorfLive p (2 ^ 47 - 100) 4096 (ErrorfRealRt.errR tys iE iW (fun _ _ => True)) tErr iE tInt iW 26
        ErrorfRealFmt.fmtNum 4294967296)
    omega
  trivial

end Errorf64

/-! ## 5. `janus_grab`: it only ever names an existing hypothesis, so it cannot prove a false goal; the risk is binding the
wrong one. Ambiguity warns; every positional renamer after `janus_run` is flagged. -/

namespace Grab
open Janus.Arm64 Janus.GoABI Janus.Tactic

/-- P1: with no matching hypothesis it fails (it never invents one): `False` is not provable by grabbing. -/
example : True := by
  fail_if_success
    have : False := by
      janus_grab MemFrame as h
      exact h
  trivial

/-- P2: the grabbed hypothesis is the existing one, not a stronger statement: a goal about a different frame is not
closed by `janus_grab 112` when the first match is another frame. -/
example (s st st2 : Janus.Arm64.State) (a : Nat) (_h1 : MemFrame s.mem st.mem [(a - 112 - 4096, a - 112)])
    (_h2 : MemFrame s.mem st2.mem [(a - 112 - 4096, a - 112)]) : True := by
  fail_if_success
    have : MemFrame s.mem st2.mem [(a - 112 - 4096, a - 112)] := by
      janus_grab 112 as f
      exact f
  trivial

-- P3: two hypotheses match: the first is bound and a warning says so.
/-- warning: janus_grab 112: 2 hypotheses match; `f` is the first. Select the one you mean by a more specific pattern (another constant, numeral or projection) -/
#guard_msgs in
example (s st st2 : Janus.Arm64.State) (a : Nat) (_h1 : MemFrame s.mem st.mem [(a - 112 - 4096, a - 112)])
    (_h2 : MemFrame s.mem st2.mem [(a - 112 - 4096, a - 112)]) : True := by
  janus_grab 112 as f
  trivial

def seg : Segment := ⟨"f", 0x1000, [0xf100001f, 0x54000060, 0xd2800021, 0x14000002, 0xd2800041, 0x91000422, 0xd65f03c0]⟩
def P : Program := { segments := [seg], stubs := [], exitAddr := 0 }

-- P4: `next x =>` and `case _ x =>` rename by position too: both are flagged after `janus_run`.
/-- warning: positional `rename_i`/`next x`/`case _ x` after `janus_run` re-binds names silently when a callee's contract gains or reorders a conjunct: select the hypothesis by content with `janus_grab c as h`, `janus_grab 112 as h` or `janus_grab fr f i as h`

Note: This linter can be disabled with `set_option linter.janusRenameI false`
-/
#guard_msgs in
theorem next_flagged (x : W64) (_h : x.toNat < 5) :
    Ensures P 0x1000 [x] (fun _ => True) (fun _ s' => s'.regs 2 = if x = 0 then 3 else 2) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run join [0x1014]
  rcases hjoin with ⟨⟨hx, -⟩, rfl, -⟩ | ⟨⟨hx, -⟩, rfl, -⟩
  next y => simp_all [BitVec.toNat_eq]
  all_goals simp_all [BitVec.toNat_eq]

/-- P5 (KNOWN GAP, documented): a user macro wrapping `rename_i` is not seen by the syntax-level linter. The proof is
still sound (a renamed hypothesis is the same hypothesis); only the positional-fragility hint is lost. -/
macro "ren_hidden" : tactic => `(tactic| rename_i _y)

#guard_msgs in
theorem hidden_not_flagged (x : W64) (_h : x.toNat < 5) :
    Ensures P 0x1000 [x] (fun _ => True) (fun _ s' => s'.regs 2 = if x = 0 then 3 else 2) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run join [0x1014]
  rcases hjoin with ⟨⟨hx, -⟩, rfl, -⟩ | ⟨⟨hx, -⟩, rfl, -⟩
  all_goals (try ren_hidden)
  all_goals simp_all [BitVec.toNat_eq]

end Grab

end JanusTests.RedTeamN9
