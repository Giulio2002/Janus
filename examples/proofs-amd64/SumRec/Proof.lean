import Janus
import Extracted

/-!
# `SumRec(n uint64) uint64` on amd64: recursion proved with stack growth at every depth (R7)

```go
func SumRec(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return n + SumRec(n-1)
}
```

The amd64 counterpart of `examples/proofs/SumRec.lean`. Each level pushes `RBP`, reserves 8 bytes
(the callee's argument spill slot), spills `n` to its own slot `8(SP)` at entry, and calls itself:
24 bytes per level with the return address.

**Guarantee** (`correctness`). For every frame table agreeing with the binary's frame record,
every stack pool, runtime memory and readiness, and every runtime that meets the amd64 `morestack`
contract (`MorestackContract64`), and every call state whose goroutine stack `[lo, hi)` is
described by `g.stack` — **with no assumption that the recursion fits** (`Pre` asks only for the
`maxstacksize` bound of `n + 1` frames) — `SumRec(n)` returns `0 + 1 + … + n`. The stack may grow
at any depth, which moves every frame of the recursion so far.

**How.** `gsum` is a grown callee summary (`GSummary64`) by induction on `n`. At one level
(`room_case`), when the prologue falls through, the code runs to the recursive `CALL` (`callPre`),
the induction hypothesis covers the callee — which may grow the stack and move this frame — and
the epilogue (`epi`) reads this frame back on the moved stack: the spilled `n` copied (a scalar to
the stack maps), the saved `RBP` adjusted (the frame's saved-frame-pointer slot), the return
address copied (a code address). `Post` states that move (`Moved` along the caller's walk) and the
adjusted `RBP` (`adjustWord`; `BPOK`: the caller's `RBP` points into the stack or outside every
stack), so it composes level by level. When the prologue does not fall through (`grow_branch`),
the contract grows the stack once, the glue reloads `n`, and `room_case` applies on the new stack;
the two moves compose into one (`Moved.trans'`, `adjustWord_trans`).
-/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Stack
  Janus.Contracts Janus.Contracts.Stack Janus.Contracts.StackAmd64

namespace Proof

/-- The return pc of the recursive call, and the glue pc after the `morestack` call. -/
abbrev callRet : Nat := Extracted.entry + 0x28
abbrev gluePc : Nat := Extracted.entry + 0x45

/-- The base case `n = 0` on a stack with room: push `RBP`, return `0`. -/
theorem base : ∀ t : State, t.rip = BitVec.ofNat 64 Extracted.entry →
    (t.regs 14).toNat + 24 ≤ 2 ^ 48 → t.mem.accessible ((t.regs 14).toNat + 16) 8 false = true →
    t.mem.readLE ((t.regs 14).toNat + 16) 8 < (t.regs 4).toNat →
    16 ≤ (t.regs 4).toNat → (t.regs 4).toNat + 8 ≤ 2 ^ 48 →
    t.mem.accessible ((t.regs 4).toNat - 16) 24 true = true →
    t.mem.readLE (t.regs 4).toNat 8 < 2 ^ 47 → t.regs 0 = 0 →
    ReachesRet Extracted.program (retAddrOf t) t (fun t' => t'.regs 0 = 0 ∧
      t'.regs 4 = t.regs 4 + 8 ∧ t'.regs 5 = t.regs 5 ∧ t'.regs 14 = t.regs 14 ∧
      t'.mem = t.mem.writeLE ((t.regs 4).toNat - 8) 8 (t.regs 5).toNat) := by
  intro t hpc h1 h2 h3 h4 h5 h6 h7 h0
  janus64_run

/-- The recursive case up to the callee's entry: push `RBP`, spill `n` to `8(SP)`, `CALL` with
`n - 1` (pushing `callRet`). -/
theorem callPre : ∀ t : State, t.rip = BitVec.ofNat 64 Extracted.entry →
    (t.regs 14).toNat + 24 ≤ 2 ^ 48 → t.mem.accessible ((t.regs 14).toNat + 16) 8 false = true →
    t.mem.readLE ((t.regs 14).toNat + 16) 8 < (t.regs 4).toNat →
    24 ≤ (t.regs 4).toNat → (t.regs 4).toNat + 16 ≤ 2 ^ 48 →
    t.mem.accessible ((t.regs 4).toNat - 24) 40 true = true → (t.regs 0).toNat ≠ 0 →
    ReachesRet Extracted.program (BitVec.ofNat 64 Extracted.entry) t (fun t' =>
      t'.regs 4 = t.regs 4 - 24 ∧ t'.regs 0 = t.regs 0 - 1 ∧ t'.regs 5 = t.regs 4 - 8 ∧
      t'.regs 14 = t.regs 14 ∧
      t'.mem = ((t.mem.writeLE ((t.regs 4).toNat - 8) 8 (t.regs 5).toNat).writeLE
        ((t.regs 4).toNat + 8) 8 (t.regs 0).toNat).writeLE ((t.regs 4).toNat - 24) 8 callRet) := by
  intro t hpc h3 h4 h5 h6 h7 h8 h0
  janus64_run until [Extracted.entry]
  exact ReachesRet.done rfl ⟨by simp [setRegF], by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl⟩

/-- After the recursive call: add the spilled `n`, pop the frame and `RBP`, return. -/
theorem epi : ∀ t : State, t.rip = BitVec.ofNat 64 callRet →
    (t.regs 4).toNat + 32 ≤ 2 ^ 48 → t.mem.accessible ((t.regs 4).toNat + 8) 24 false = true →
    t.mem.readLE ((t.regs 4).toNat + 16) 8 < 2 ^ 47 →
    ReachesRet Extracted.program (BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 16) 8)) t (fun t' =>
      t'.regs 0 = t.regs 0 + BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 24) 8) ∧
      t'.regs 4 = t.regs 4 + 24 ∧ t'.regs 5 = BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 8) 8) ∧
      t'.regs 14 = t.regs 14 ∧ t'.mem = t.mem) := by
  intro t hpc h1 h2 h3
  janus64_run

/-- The glue after the `morestack` call (`MOVQ 8(SP), AX; JMP SumRec`). -/
theorem glue : ∀ t : State, t.rip = BitVec.ofNat 64 gluePc →
    t.mem.accessible ((t.regs 4).toNat + 8) 8 false = true → (t.regs 4).toNat + 16 ≤ 2 ^ 48 →
    ReachesRet Extracted.program (BitVec.ofNat 64 Extracted.entry) t (fun t' =>
      t'.rip = BitVec.ofNat 64 Extracted.entry ∧ t'.regs 4 = t.regs 4 ∧ t'.mem = t.mem ∧
      t'.regs 0 = BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 8) 8) ∧
      (∀ r, r ≠ 0 → t'.regs r = t.regs r)) := by
  intro t hpc hacc hsp
  janus64_run until [Extracted.entry]
  exact ReachesRet.done rfl ⟨rfl, by simp [setRegF], rfl, by simp [setRegF], fun r h0 => by simp [setRegF, h0]⟩

/-- `0 + 1 + … + n`. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

/-- What the binary's frame record says about `SumRec` (`tableOK_of`): at the glue (no frame,
largest frame 16 bytes, a scalar argument) and at the recursive call's return pc (a 16-byte
frame with no pointer locals, a scalar argument, no stack objects). -/
def TableOK (FT : FrameTable) : Prop :=
  FT.valid gluePc = true ∧ FT.stop gluePc = false ∧ FT.injected gluePc = false ∧
  FT.spdelta gluePc = 0 ∧ FT.maxspd gluePc = 16 ∧ (∀ j, (FT.args gluePc).getD j false = false) ∧
  FT.objs gluePc = [] ∧
  FT.valid callRet = true ∧ FT.stop callRet = false ∧ FT.injected callRet = false ∧
  FT.spdelta callRet = 16 ∧ (∀ j, (FT.locals callRet).getD j false = false) ∧
  (∀ j, (FT.args callRet).getD j false = false) ∧ FT.objs callRet = []

/-- `TableOK`, read off the binary's frame record of `SumRec`. -/
theorem tableOK_of {FT : FrameTable} (h : FT.Agrees Extracted.frames) : TableOK FT := by
  obtain ⟨a1, -, a3, a4, a5, a6, -, a8, a9⟩ := h _ (List.mem_cons_self ..) gluePc (by decide) (by decide)
  obtain ⟨b1, -, b3, -, b5, b6, b7, b8, b9⟩ := h _ (List.mem_cons_self ..) callRet (by decide) (by decide)
  refine ⟨a1, ?_, ?_, ?_, ?_, fun j => ?_, ?_, b1, ?_, ?_, ?_, fun j => ?_, fun j => ?_, ?_⟩
  · rw [a5] <;> rfl
  · rw [a6] <;> rfl
  · rw [a3] <;> rfl
  · rw [a4] <;> rfl
  · rw [a8]; cases j <;> rfl
  · rw [a9] <;> rfl
  · rw [b5] <;> rfl
  · rw [b6] <;> rfl
  · rw [b3] <;> rfl
  · rw [b7]; cases j <;> rfl
  · rw [b8]; cases j <;> rfl
  · rw [b9] <;> rfl

/-- The environment: the frame table agrees with the binary's frame records, the laws of every
pclntab (frame words inside the frame, aligned frames, code outside the stack pools), and the
stack pools apart from the runtime's own memory. -/
def Env (FT : FrameTable) (pool rt : List (Nat × Nat)) : Prop :=
  FT.Agrees Extracted.frames ∧ FT.InFrame Arch.amd64 ∧ FT.Aligned ∧ FT.CodeOutside pool ∧
    (∀ a n, InRanges a n pool → Outside a n rt)

/-- A frame pointer the move can adjust: into the stack, or outside every stack. -/
def BPOK (pool : List (Nat × Nat)) (lo hi v : Nat) : Prop := (lo ≤ v ∧ v < hi) ∨ Outside v 1 pool

/-- The precondition of a call `SumRec(n)` (no room assumed): the goroutine stack `[lo, hi)`,
the caller's `RBP` (`BPOK`), the return address, the caller's walk (its return-address slots above
the spill slot, which its stack maps do not mark), the pools, the `maxstacksize` bound for `n + 1`
frames, and the runtime's readiness. -/
def Pre (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s : State) : Prop :=
  ∃ lo hi, GStack s.mem (s.regs 14).toNat lo hi ∧ Outside (s.regs 14).toNat 24 pool ∧
    4096 ≤ lo ∧ lo + 8 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 16 ≤ hi ∧ hi ≤ 2 ^ 48 ∧
    lo % 16 = 0 ∧ hi % 16 = 0 ∧ (s.regs 4).toNat % 8 = 0 ∧
    InRanges lo (hi - lo) pool ∧ PoolOK s.mem pool ∧ BPOK pool lo hi (s.regs 5).toNat ∧
    s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    (∃ fs, Chain Arch.amd64 FT s.mem hi (s.mem.readLE (s.regs 4).toNat 8) ((s.regs 4).toNat + 8) none fs ∧
      (∀ f ∈ fs, FT.stop f.pc = false → (s.regs 4).toNat + 16 ≤ f.fp - 8) ∧
      framesCls Arch.amd64 FT fs ((s.regs 4).toNat + 8) = false) ∧
    2 * ((hi - (s.regs 4).toNat) + 24 * (s.regs 0).toNat + 24 + stackGuard) ≤ maxstacksize ∧
    H [] (s.regs 14).toNat 0 (rtView rt s.mem) ∧ NoStackPtr s.mem pool rt

/-- What a call `SumRec(n)` does, through any number of growths: it returns `sumTo n` with the
stack `[lo, hi)` grown to `[lo', hi')` (possibly the same), `RSP` popped and moved, `RBP` restored
and adjusted, `g` kept, the caller's frames moved (`Moved` from `RSP + 8`, the spill slot free),
nothing outside the pools and the runtime memory changed, the runtime ready again. -/
def Post (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s s' : State) : Prop :=
  ∃ lo hi lo' hi', GStack s.mem (s.regs 14).toNat lo hi ∧ GStack s'.mem (s.regs 14).toNat lo' hi' ∧
    hi - lo ≤ hi' - lo' ∧ 4096 ≤ lo' ∧ lo' % 16 = 0 ∧ hi' % 16 = 0 ∧ hi' ≤ 2 ^ 48 ∧
    InRanges lo' (hi' - lo') pool ∧
    s'.regs 0 = BitVec.ofNat 64 (sumTo (s.regs 0).toNat) ∧
    s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat + 8 + hi' - hi) ∧
    s'.regs 5 = BitVec.ofNat 64 (adjustWord lo hi hi' (s.regs 5).toNat) ∧
    s'.regs 14 = s.regs 14 ∧
    (∀ fs, Chain Arch.amd64 FT s.mem hi (s.mem.readLE (s.regs 4).toNat 8) ((s.regs 4).toNat + 8) none fs →
      Moved (framesCls Arch.amd64 FT fs) pool lo hi hi' ((s.regs 4).toNat + 8)
        [((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] s.mem s'.mem) ∧
    MemFrame s.mem s'.mem (pool ++ rt) ∧ H [] (s.regs 14).toNat 0 (rtView rt s'.mem)

/-- A bitmap with no bits set marks nothing. -/
theorem bitsAt_false {bs : List Bool} (h : ∀ j, bs.getD j false = false) (b : Int) (a : Nat) :
    bitsAt b bs a = false := by
  simp only [bitsAt, h, Bool.and_false]

/-- `SumRec`'s frame suspended at the recursive call (`RSP = r - 16`, `fp = r + 8`) marks exactly
its saved frame pointer slot `r - 8`. -/
theorem frameF {FT : FrameTable} (hT : TableOK FT) {r : Nat} (h16 : 16 ≤ r) (a : Nat) :
    frameCls Arch.amd64 FT callRet (r - 16) (r + 8) a = (a == r - 8) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hl, ha, ho⟩ := hT
  have hv : Arch.amd64.varp (r - 16) (r + 8) = r - 8 := by simp [Arch.varp]; omega
  simp only [frameCls, hv, Arch.argp, ho, List.any_nil, Bool.or_false, bitsAt_false hl,
    bitsAt_false ha, Bool.and_false]
  rw [show decide (r + 8 = r - 8 + 16) = true by simp; omega, Bool.true_and]

/-- The frame at the glue (`RSP = r`, no frame yet) marks nothing. -/
theorem frame0 {FT : FrameTable} (hT : TableOK FT) (r a : Nat) :
    frameCls Arch.amd64 FT gluePc r (r + 8) a = false := by
  obtain ⟨-, -, -, -, -, ha, ho, -⟩ := hT
  have hv : Arch.amd64.varp r (r + 8) = r := by simp [Arch.varp]
  simp only [frameCls, hv, Arch.argp, ho, List.any_nil, Bool.or_false, bitsAt_false ha]
  have e1 : decide (r + 8 = r + 16) = false := decide_eq_false (by omega)
  have e2 : decide (Arch.amd64.minLocals + r < r) = false :=
    decide_eq_false (by unfold Arch.minLocals; omega)
  rw [e1, e2, Bool.false_and, Bool.false_and, Bool.false_or]

/-- Two moves adjust a frame pointer as one. -/
theorem adjustWord_trans {pool : List (Nat × Nat)} {lo hi lo1 hi1 hi2 v : Nat}
    (hin : InRanges lo (hi - lo) pool) (hin1 : InRanges lo1 (hi1 - lo1) pool) (hsz : hi - lo ≤ hi1 - lo1)
    (hlh : lo ≤ hi) (hlh1 : lo1 ≤ hi1) (hv : BPOK pool lo hi v) :
    adjustWord lo1 hi1 hi2 (adjustWord lo hi hi1 v) = adjustWord lo hi hi2 v := by
  rcases hv with ⟨h1, h2⟩ | hout
  · have e1 : adjustWord lo hi hi1 v = v + hi1 - hi := by simp only [adjustWord]; exact if_pos ⟨h1, h2⟩
    have e2 : adjustWord lo hi hi2 v = v + hi2 - hi := by simp only [adjustWord]; exact if_pos ⟨h1, h2⟩
    rw [e1, e2]; simp only [adjustWord]; rw [if_pos ⟨by omega, by omega⟩]; omega
  · have hn : ¬ (lo ≤ v ∧ v < hi) := fun ⟨h1, h2⟩ => by
      have := InRanges.disjoint (InRanges.sub hin (a := v) (n := 1) h1 (by omega)) hout; omega
    have hn1 : ¬ (lo1 ≤ v ∧ v < hi1) := fun ⟨h1, h2⟩ => by
      have := InRanges.disjoint (InRanges.sub hin1 (a := v) (n := 1) h1 (by omega)) hout; omega
    have e1 : adjustWord lo hi hi1 v = v := by simp only [adjustWord]; exact if_neg hn
    have e2 : adjustWord lo hi hi2 v = v := by simp only [adjustWord]; exact if_neg hn
    rw [e1, e2]; simp only [adjustWord]; exact if_neg hn1

/-- `BPOK` survives a move. -/
theorem BPOK.mv {pool : List (Nat × Nat)} {lo hi lo1 hi1 v : Nat}
    (hin : InRanges lo (hi - lo) pool) (hsz : hi - lo ≤ hi1 - lo1) (hlh : lo ≤ hi) (hlh1 : lo1 ≤ hi1)
    (hv : BPOK pool lo hi v) : BPOK pool lo1 hi1 (adjustWord lo hi hi1 v) := by
  rcases hv with ⟨h1, h2⟩ | hout
  · left
    have e1 : adjustWord lo hi hi1 v = v + hi1 - hi := by simp only [adjustWord]; exact if_pos ⟨h1, h2⟩
    rw [e1]; omega
  · right
    have hn : ¬ (lo ≤ v ∧ v < hi) := fun ⟨h1, h2⟩ => by
      have := InRanges.disjoint (InRanges.sub hin (a := v) (n := 1) h1 (by omega)) hout; omega
    have e1 : adjustWord lo hi hi1 v = v := by simp only [adjustWord]; exact if_neg hn
    rw [e1]; exact hout

set_option maxHeartbeats 4000000 in
/-- `SumRec` on a stack whose prologue check falls through. The recursive call uses the induction
hypothesis (the callee may grow the stack, moving this frame); the epilogue runs on the moved
stack. -/
theorem room_case (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (henv : Env FT pool rt) (n : Nat)
    (ih : GSummary64 Extracted.program reloc Extracted.entry
      (fun s => Pre FT pool rt H s ∧ (s.regs 0).toNat < n) (Post FT pool rt H))
    (t : State) (hpc : t.rip = BitVec.ofNat 64 Extracted.entry) (hp : Pre FT pool rt H t)
    (hn : (t.regs 0).toNat = n)
    (hroom : t.mem.readLE ((t.regs 14).toNat + 16) 8 < (t.regs 4).toNat) :
    GrownRet64 Extracted.program reloc (retAddrOf t) t (Post FT pool rt H t) := by
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hinp, hpok, hbp, hr47,
    ⟨fs, hch, hfsp, hc8⟩, hfit, hH, hNP⟩ := hp
  obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv
  have hT := tableOK_of hA
  have hgs' := hgs
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
  have hacc := hpok.accessible hinp
  have hspL : lo + 928 < (t.regs 4).toNat := by rw [hgg] at hroom; exact hroom
  have hsp64 := (t.regs 4).isLt
  have hinw : ∀ a k, lo ≤ a → a + k ≤ hi → InRanges a k pool := fun a k h1 h2 => hinp.sub h1 (by omega)
  have hinr : ∀ a k, lo ≤ a → a + k ≤ hi → InRanges a k (pool ++ rt) := fun a k h1 h2 =>
    (hinw a k h1 h2).append_left rt
  by_cases hz : t.regs 0 = 0
  · obtain ⟨k, t', hst, hpc', hb0, hb4, hb5, hb14, hbm⟩ := base t hpc hg24
      (Arm64.Memory.accessible_mono _ hgacc (by omega) (by omega)) hroom (by omega) (by omega)
      (Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hr47 hz
    have hadj : adjustWord lo hi hi (t.regs 5).toNat = (t.regs 5).toNat := by
      simp only [adjustWord]; split <;> omega
    refine .done hst hpc' ⟨lo, hi, lo, hi, hgs, ?_, Nat.le_refl _, h4k, hal1, hal2, hhi48, hinp,
      ?_, ?_, ?_, hb14, ?_, ?_, ?_⟩
    · rw [hbm]; exact GStack.writeLE hgs hgo (hinw _ _ (by omega) (by omega))
    · rw [hb0, hz]; rfl
    · rw [hb4]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · rw [hb5, hadj, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · intro fs0 _
      rw [hbm]
      refine Moved.of_agree _ pool ⟨by omega, by omega⟩ h4k (by omega) (by omega) fun a h1 h2 _ => ?_
      rw [Arm64.Memory.bytes_writeLE_outside _ (by omega)]
    · rw [hbm]; exact (MemFrame.refl t.mem _).writeLE_inRanges _ (hinr _ _ (by omega) (by omega))
    · rw [hbm, rtView_writeLE (hPA _ _ (hinw _ _ (by omega) (by omega)))]; exact hH
  · -- the recursive case
    have hz' : (t.regs 0).toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
    have hx0 := (t.regs 0).isLt
    obtain ⟨k1, v, hst1, hvpc, hv4, hv0, hv5, hv14, hvm⟩ := callPre t hpc hg24
      (Arm64.Memory.accessible_mono _ hgacc (by omega) (by omega)) hroom (by omega) (by omega)
      (Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hz'
    obtain ⟨M1, hM1⟩ : ∃ M1, M1 = ((t.mem.writeLE ((t.regs 4).toNat - 8) 8 (t.regs 5).toNat).writeLE
        ((t.regs 4).toNat + 8) 8 (t.regs 0).toNat).writeLE ((t.regs 4).toNat - 24) 8 callRet := ⟨_, rfl⟩
    have hvmem : v.mem = M1 := by rw [hvm, hM1]
    have hv4n : (v.regs 4).toNat = (t.regs 4).toNat - 24 := by
      rw [hv4, BitVec.toNat_sub, show (24 : BitVec 64).toNat = 24 from rfl]; omega
    have hv0n : (v.regs 0).toNat = (t.regs 0).toNat - 1 := by
      rw [hv0, BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]; omega
    have hagM1 : ∀ a k, (a + k ≤ (t.regs 4).toNat - 24 ∨ (t.regs 4).toNat - 16 ≤ a) →
        (a + k ≤ (t.regs 4).toNat - 8 ∨ (t.regs 4).toNat ≤ a) →
        (a + k ≤ (t.regs 4).toNat + 8 ∨ (t.regs 4).toNat + 16 ≤ a) → M1.readLE a k = t.mem.readLE a k := by
      intro a k h1 h2 h3
      rw [hM1, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have haccM1 : ∀ a k w, M1.accessible a k w = t.mem.accessible a k w := by
      intro a k w; rw [hM1, Arm64.Memory.accessible_writeLE, Arm64.Memory.accessible_writeLE,
        Arm64.Memory.accessible_writeLE]
    have hM1ra : M1.readLE ((t.regs 4).toNat - 24) 8 = callRet := by
      rw [hM1, Arm64.Memory.readLE_writeLE_self]; rfl
    have hM1fp : M1.readLE ((t.regs 4).toNat - 8) 8 = (t.regs 5).toNat := by
      rw [hM1, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (t.regs 5).isLt
    have hM1x : M1.readLE ((t.regs 4).toNat + 8) 8 = (t.regs 0).toNat := by
      rw [hM1, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt hx0
    have hM1r : M1.readLE (t.regs 4).toNat 8 = t.mem.readLE (t.regs 4).toNat 8 :=
      hagM1 _ _ (by omega) (by omega) (by omega)
    have hgsM1 : GStack M1 (t.regs 14).toNat lo hi := by
      rw [hM1]
      exact GStack.writeLE (GStack.writeLE (GStack.writeLE hgs hgo (hinw _ _ (by omega) (by omega))) hgo
        (hinw _ _ (by omega) (by omega))) hgo (hinw _ _ (by omega) (by omega))
    have hfb := hch.bounds
    have hchM1 : Chain Arch.amd64 FT M1 hi (t.mem.readLE (t.regs 4).toNat 8) ((t.regs 4).toNat + 8) none fs :=
      Chain.congr hch (by omega) fun f hf hst => by
        have := hfsp f hf hst
        simp only [Arch.lrSlot]; exact hagM1 _ _ (by omega) (by omega) (by omega)
    have hT0 := hT
    obtain ⟨hTv, hTs, hTi, -, -, -, -, hTv', hTs', hTi', hTd', -, -, -⟩ := hT0
    have hfpF : Arch.amd64.fp FT callRet ((t.regs 4).toNat - 16) = (t.regs 4).toNat + 8 := by
      simp [Arch.fp, hTd']; omega
    have hchv : Chain Arch.amd64 FT M1 hi callRet ((t.regs 4).toNat - 16) none
        (⟨callRet, (t.regs 4).toNat - 16, (t.regs 4).toNat + 8⟩ :: fs) := by
      have hlr : Arch.amd64.lrOf M1 ((t.regs 4).toNat - 16) ((t.regs 4).toNat + 8) none =
          t.mem.readLE (t.regs 4).toNat 8 := by
        simp only [Arch.lrOf, Nat.add_sub_cancel]; exact hM1r
      have := Chain.cons (A := Arch.amd64) (FT := FT) (m := M1) (hi := hi) (pc := callRet)
        (sp := (t.regs 4).toNat - 16) (lr0 := none) (fs := fs) hTv' hTs' hTi' (by omega)
        (by rw [hfpF]; omega) (by rw [hfpF, hlr]; exact hchM1)
      rw [hfpF] at this; exact this
    have hclsF : ∀ a, framesCls Arch.amd64 FT
        (⟨callRet, (t.regs 4).toNat - 16, (t.regs 4).toNat + 8⟩ :: fs) a =
        ((a == (t.regs 4).toNat - 8) || framesCls Arch.amd64 FT fs a) := by
      intro a; simp only [framesCls_cons]; rw [frameF hT (by omega)]
    -- the precondition at the recursive call
    have hpv : Pre FT pool rt H v := by
      refine ⟨lo, hi, by rw [hv14, hvmem]; exact hgsM1, by rw [hv14]; exact hgo, h4k, by omega,
        by omega, hhi48, hal1, hal2, by omega, hinp, by rw [hvmem]; exact hpok.of_accessible haccM1,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · left; rw [hv5, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
      · rw [hv4n, hvmem, hM1ra]; decide
      · have hchv' : Chain Arch.amd64 FT v.mem hi (v.mem.readLE (v.regs 4).toNat 8) ((v.regs 4).toNat + 8) none
            (⟨callRet, (t.regs 4).toNat - 16, (t.regs 4).toNat + 8⟩ :: fs) := by
          rw [hv4n, hvmem, hM1ra, show (t.regs 4).toNat - 24 + 8 = (t.regs 4).toNat - 16 by omega]; exact hchv
        refine ⟨_, hchv', fun f hf hst => ?_, ?_⟩
        · rw [hv4n]
          rcases List.mem_cons.1 hf with rfl | hf
          · simp only; omega
          · have := hfsp f hf hst; omega
        · rw [hv4n, show (t.regs 4).toNat - 24 + 8 = (t.regs 4).toNat - 16 by omega, hclsF,
            hch.framesCls_below hIF (by omega)]
          simp; omega
      · rw [hv0n, hv4n]
        have : 1 ≤ (t.regs 0).toNat := by omega
        have h' := hfit
        rw [show 24 * ((t.regs 0).toNat - 1) = 24 * (t.regs 0).toNat - 24 by rw [Nat.mul_sub_one]] 
        omega
      · rw [hv14, hvmem, hM1, rtView_writeLE (hPA _ _ (hinw _ _ (by omega) (by omega))),
          rtView_writeLE (hPA _ _ (hinw _ _ (by omega) (by omega))),
          rtView_writeLE (hPA _ _ (hinw _ _ (by omega) (by omega)))]
        exact hH
      · rw [hvmem, hM1]
        exact ((hNP.writeLE _ (hinw _ _ (by omega) (by omega))).writeLE _ (hinw _ _ (by omega) (by omega))).writeLE _
          (hinw _ _ (by omega) (by omega))
    have hvn : (v.regs 0).toNat < n := by rw [hv0n]; omega
    refine GrownRet64.of_steps hst1 (GrownRet64.call ih hvpc ⟨hpv, hvn⟩ fun w hwpc hw => ?_)
    obtain ⟨lov, hiv, lo', hi', hgsv, hgsw, hsz, h4k', hal1', hal2', hhi48', hinp', hw0, hw4, hw5,
      hw14, hmv, hmf, hHw⟩ := hw
    rw [hv14, hvmem] at hgsv
    obtain ⟨e1, e2⟩ := GStack.unique hgsM1 hgsv
    subst e1 e2
    rw [hv14] at hgsw hHw
    have hmvF := hmv _ (by
      rw [hv4n, hvmem, hM1ra, show (t.regs 4).toNat - 24 + 8 = (t.regs 4).toNat - 16 by omega]; exact hchv)
    rw [hv4n, hvmem, show (t.regs 4).toNat - 24 + 8 = (t.regs 4).toNat - 16 by omega] at hmvF
    have hgro := hmvF.grows
    have hw4n : (w.regs 4).toNat = (t.regs 4).toNat - 16 + hi' - hi := by
      rw [hw4, hv4n, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hwpc' : w.rip = BitVec.ofNat 64 callRet := by rw [hwpc, retAddrOf, hv4n, hvmem, hM1ra]
    have hexo : ∀ a, (t.regs 4).toNat - 8 ≤ a → Outside a 8 [((t.regs 4).toNat - 16, (t.regs 4).toNat - 24 + 16)] := by
      intro a ha; simp only [outside_cons, outside_nil, and_true]; omega
    -- the frame read back on the (possibly moved) stack
    have rd24 : w.mem.readLE ((w.regs 4).toNat + 24) 8 = (t.regs 0).toNat := by
      rw [hw4n, show (t.regs 4).toNat - 16 + hi' - hi + 24 = ((t.regs 4).toNat + 8) + hi' - hi by omega,
        hmvF.readLE_scalar (by omega) (by omega) (fun j hj => by
          rw [show (t.regs 4).toNat + 8 + j - ((t.regs 4).toNat + 8 + j) % 8 = (t.regs 4).toNat + 8 by omega,
            hclsF, hc8]; simp; omega) (hexo _ (by omega)), hM1x]
    have rdBP : w.mem.readLE ((w.regs 4).toNat + 8) 8 = adjustWord lo hi hi' (t.regs 5).toNat := by
      rw [hw4n, show (t.regs 4).toNat - 16 + hi' - hi + 8 = ((t.regs 4).toNat - 8) + hi' - hi by omega]
      have hcl : framesCls Arch.amd64 FT (⟨callRet, (t.regs 4).toNat - 16, (t.regs 4).toNat + 8⟩ :: fs)
          ((t.regs 4).toNat - 8) = true := by rw [hclsF]; simp
      rcases hbp with ⟨h1, h2⟩ | hout
      · rw [hmvF.readLE_ptr (by omega) (by omega) (by omega) hcl (hexo _ (by omega)) (by rw [hM1fp]; exact h1)
          (by rw [hM1fp]; exact h2), hM1fp]
        simp only [adjustWord]; rw [if_pos ⟨h1, h2⟩]
      · rw [hmvF.readLE_ptr_out (by omega) (by omega) (by omega) hcl (hexo _ (by omega)) (by rw [hM1fp]; exact hout),
          hM1fp]
        have hn : ¬ (lo ≤ (t.regs 5).toNat ∧ (t.regs 5).toNat < hi) := fun ⟨h1, h2⟩ => by
          have := InRanges.disjoint (InRanges.sub hinp (a := (t.regs 5).toNat) (n := 1) h1 (by omega)) hout; omega
        simp only [adjustWord]; rw [if_neg hn]
    have hcode := hCO _ hch.valid_head
    have rdRA : w.mem.readLE ((w.regs 4).toNat + 16) 8 = t.mem.readLE (t.regs 4).toNat 8 := by
      rw [hw4n, show (t.regs 4).toNat - 16 + hi' - hi + 16 = (t.regs 4).toNat + hi' - hi by omega,
        hmvF.readLE_word_out (by omega) (by omega) (by omega) (hexo _ (by omega)) (by rw [hM1r]; exact hcode.1), hM1r]
    -- the epilogue
    have hpok_w : PoolOK w.mem pool := hpok.of_accessible fun a k w' => by rw [hmf.accessible, hvmem, haccM1]
    have haccw : w.mem.accessible ((w.regs 4).toNat + 8) 24 false = true :=
      Arm64.Memory.accessible_read_of_write _ (hpok_w.accessible (hinp'.sub (by omega) (by omega)))
    obtain ⟨k3, x, hst3, hxpc, hx0', hx4, hx5, hx14, hxm⟩ := epi w hwpc' (by omega) haccw
      (by rw [rdRA]; exact hr47)
    refine .done hst3 (by rw [hxpc, rdRA]; rfl)
      ⟨lo, hi, lo', hi', hgs, by rw [hxm]; exact hgsw, hsz, h4k', hal1', hal2', hhi48', hinp', ?_, ?_, ?_,
        by rw [hx14, hw14, hv14], ?_, ?_, by rw [hxm]; exact hHw⟩
    · -- the result: `sumTo (n - 1) + n`
      rw [hx0', hw0, rd24, hv0n, BitVec.ofNat_add_ofNat]
      obtain ⟨m, hm⟩ : ∃ m, (t.regs 0).toNat = m + 1 := ⟨(t.regs 0).toNat - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      show BitVec.ofNat 64 (sumTo m + (m + 1)) = BitVec.ofNat 64 ((m + 1) + sumTo m)
      rw [Nat.add_comm (sumTo m)]
    · rw [hx4]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hw4n, BitVec.toNat_ofNat, show (24 : BitVec 64).toNat = 24 from rfl]; omega
    · rw [hx5, rdBP]
    · intro fs0 hfs0
      rw [Chain.unique hfs0 hch, hxm]
      have h1 := hmvF.mono_base (base' := (t.regs 4).toNat + 8) (by omega) (by omega) (by omega)
      have h2 := h1.mono_ex' (ex' := [((t.regs 4).toNat + 8, (t.regs 4).toNat + 16)]) fun a k ha _ => by
        simp only [outside_cons, outside_nil, and_true]; omega
      have h3 := h2.cls_congr (cls' := framesCls Arch.amd64 FT fs) fun a ha _ => by
        rw [hclsF]
        have e : (a == (t.regs 4).toNat - 8) = false := by simp; omega
        rw [e, Bool.false_or]
      refine h3.congr_src fun a ha _ hx => ?_
      simp only [outside_cons, outside_nil, and_true] at hx
      rw [hM1, Arm64.Memory.bytes_writeLE_outside _ (by omega), Arm64.Memory.bytes_writeLE_outside _ (by omega),
        Arm64.Memory.bytes_writeLE_outside _ (by omega)]
    · rw [hxm]
      refine MemFrame.trans ?_ hmf fun a k h => ⟨h, h⟩
      rw [hvmem, hM1]
      exact (((MemFrame.refl t.mem _).writeLE_inRanges _ (hinr _ _ (by omega) (by omega))).writeLE_inRanges _
        (hinr _ _ (by omega) (by omega))).writeLE_inRanges _ (hinr _ _ (by omega) (by omega))

/-- The memory at the `morestack` call: the tail spilled `n` to `8(SP)`, and the `CALL` pushed the
glue address `v` at `-8(SP)`. -/
abbrev stubMem (s : State) (v : Nat) : Memory :=
  (s.mem.writeLE ((s.regs 4).toNat + 8) 8 (s.regs 0).toNat).writeLE ((s.regs 4).toNat - 8) 8 v

set_option maxHeartbeats 4000000 in
/-- The growth path at one level, from the `morestack` stub state `S`: the contract resumes on a
larger stack, the glue reloads `n`, and `room_case` applies; its postcondition composes with the
move into one on the old stack. -/
theorem grow_branch (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (n : Nat)
    (ih : GSummary64 Extracted.program reloc Extracted.entry
      (fun s => Pre FT pool rt H s ∧ (s.regs 0).toNat < n) (Post FT pool rt H))
    (s : State) (hn : (s.regs 0).toNat = n) (hp : Pre FT pool rt H s)
    (hnoroom : ¬ s.mem.readLE ((s.regs 14).toNat + 16) 8 < (s.regs 4).toNat)
    (S : State) (hstub : ∃ name, Extracted.program.stubAt S.rip.toNat = some ⟨name, S.rip.toNat, .morestack⟩)
    (h4 : S.regs 4 = s.regs 4 - 8) (h5 : S.regs 5 = s.regs 5) (h14 : S.regs 14 = s.regs 14)
    (hmem : S.mem = stubMem s gluePc) :
    ∃ s_r, reloc S s_r ∧ GrownRet64 Extracted.program reloc (retAddrOf s) s_r (Post FT pool rt H s) := by
  have hpre := hp
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hinp, hpok, hbp, hr47,
    ⟨fs, hch, hfsp, hc8⟩, hfit, hH, hNP⟩ := hp
  have henv' := henv
  obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv'
  have hT := tableOK_of hA
  have hT0 := hT
  obtain ⟨hv, hst, hinj, hspd, hmx, -, -⟩ := hT0
  have hgs' := hgs
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero] at hglo hghi hgg
  rw [hgg] at hnoroom
  simp only [stackGuard] at hnoroom
  have hsp := (s.regs 4).isLt
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 8 := by
    rw [h4, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
  have hgw : (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 16 ≤ (s.regs 14).toNat := by
    have := InRanges.disjoint (InRanges.sub hinp (a := (s.regs 4).toNat - 8) (n := 24) (by omega) (by omega)) hgo
    omega
  have hrdm : ∀ a k, (a + k ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat ≤ a) →
      (a + k ≤ (s.regs 4).toNat + 8 ∨ (s.regs 4).toNat + 16 ≤ a) → S.mem.readLE a k = s.mem.readLE a k := by
    intro a k h1 h2
    rw [hmem, stubMem, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have haccm : ∀ a k w, S.mem.accessible a k w = s.mem.accessible a k w := by
    intro a k w; rw [hmem, stubMem, Arm64.Memory.accessible_writeLE, Arm64.Memory.accessible_writeLE]
  have hglue : gluePcOf S = gluePc := by
    simp only [gluePcOf, regSP]
    rw [hS4, hmem, stubMem, Arm64.Memory.readLE_writeLE_self]; rfl
  have hfspS : fspOf S = (s.regs 4).toNat := by simp only [fspOf, regSP]; rw [hS4]; omega
  have hfb := hch.bounds
  have hchs : Chain Arch.amd64 FT S.mem hi (s.mem.readLE (s.regs 4).toNat 8) ((s.regs 4).toNat + 8) none fs :=
    Chain.congr hch (by omega) fun f hf hstp => by
      have := hfsp f hf hstp
      simp only [Arch.lrSlot]; exact hrdm _ _ (by omega) (by omega)
  have hfp0 : Arch.amd64.fp FT gluePc (s.regs 4).toNat = (s.regs 4).toNat + 8 := by
    simp [Arch.fp, hspd]
  have hchain : Chain Arch.amd64 FT S.mem hi gluePc (s.regs 4).toNat none
      (⟨gluePc, (s.regs 4).toNat, (s.regs 4).toNat + 8⟩ :: fs) := by
    have hlr : Arch.amd64.lrOf S.mem (s.regs 4).toNat ((s.regs 4).toNat + 8) none =
        s.mem.readLE (s.regs 4).toNat 8 := by
      simp only [Arch.lrOf, Nat.add_sub_cancel]; exact hrdm _ _ (by omega) (by omega)
    have := Chain.cons (A := Arch.amd64) (FT := FT) (m := S.mem) (hi := hi) (pc := gluePc)
      (sp := (s.regs 4).toNat) (lr0 := none) (fs := fs) hv hst hinj (by omega) (by rw [hfp0]; omega)
      (by rw [hfp0, hlr]; exact hchs)
    rw [hfp0] at this; exact this
  have hclsA : ∀ a, framesCls Arch.amd64 FT (⟨gluePc, (s.regs 4).toNat, (s.regs 4).toNat + 8⟩ :: fs) a =
      framesCls Arch.amd64 FT fs a := by
    intro a; simp only [framesCls_cons, frame0 hT, Bool.false_or]
  have hfit1 : 2 * (hi - lo) ≤ maxstacksize :=
    Nat.le_trans (by simp only [stackGuard] at hfit ⊢; omega) hfit
  have hm : MorestackPre64 Extracted.program FT pool rt H (s.regs 14).toNat lo hi S := by
    refine ⟨hstub, by simp only [regG]; rw [h14], ?_, hgo, ?_, ?_, ⟨hinp, hpok.of_accessible haccm⟩,
      ?_, ?_, ⟨hCO, hAl⟩, ?_, ?_⟩
    · refine ⟨hg24, by rw [haccm]; exact hgacc, ?_, ?_, ?_⟩ <;>
        simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero] <;>
        rw [hrdm _ _ (by omega) (by omega)]
      · exact hglo
      · exact hghi
      · exact hgg
    · simp only [regSP]; rw [hS4]; omega
    · simp only [regSP]; rw [hS4]; omega
    · rw [hglue, hfspS]; exact ⟨_, hchain⟩
    · rw [hglue, hfspS, hmx]; exact ⟨hfit1, Nat.le_trans (by omega) hfit⟩
    · rw [hmem, stubMem, rtView_writeLE (hPA _ _ (hinp.sub (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hinp.sub (by omega) (by omega)))]
      exact hH
    · rw [hmem, stubMem]
      exact (hNP.writeLE _ (hinp.sub (by omega) (by omega))).writeLE _ (hinp.sub (by omega) (by omega))
  obtain ⟨s_r, lo1, hi1, hre, hgr⟩ := hms _ lo hi S hm
  refine ⟨s_r, hre, ?_⟩
  obtain ⟨hg1, hg2, h4k1, hal1', hal2', hhi48', hinp1, happ⟩ := hgr.grows
  have hroom := hgr.room
  rw [hglue, hmx, hfspS] at hroom
  simp only [stackGuard] at hroom
  have hsp_r : (s_r.regs 4).toNat = (s.regs 4).toNat + hi1 - hi := by
    rw [show s_r.regs 4 = s_r.regs regSP from rfl, hgr.sp, hfspS, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hpok_r : PoolOK s_r.mem pool := hm.inPool.2.of_accessible hgr.frame.accessible
  have hacc_r : s_r.mem.accessible lo1 (hi1 - lo1) true = true := hpok_r.accessible hinp1
  have hpc_r : s_r.rip = BitVec.ofNat 64 gluePc := by rw [hgr.pc, retAddrOf, ← hglue]
  -- the glue
  obtain ⟨k, s_e, hstg, hepc, -, he4, hemem, he0, her⟩ := glue s_r hpc_r
    (Arm64.Memory.accessible_read_of_write _ (Arm64.Memory.accessible_mono _ hacc_r (by omega) (by omega)))
    (by omega)
  have he14 : s_e.regs 14 = s.regs 14 := by rw [her 14 (by decide), show s_r.regs 14 = s_r.regs regG from rfl,
    hgr.gkeep, h14]
  have he5 : s_e.regs 5 = BitVec.ofNat 64 (adjustWord lo hi hi1 (s.regs 5).toNat) := by
    rw [her 5 (by decide), show s_r.regs 5 = s_r.regs regFP from rfl, hgr.fp, show S.regs regFP = S.regs 5 from rfl, h5]
  have he4n : (s_e.regs 4).toNat = (s.regs 4).toNat + hi1 - hi := by rw [he4, hsp_r]
  -- the move
  have hmA := hgr.moved _ (by rw [hglue, hfspS]; exact hchain)
  rw [hfspS] at hmA
  have hcode := hCO _ hch.valid_head
  -- the caller's walk after the move
  have hche : Chain Arch.amd64 FT s_e.mem hi1 (s_e.mem.readLE (s_e.regs 4).toNat 8) ((s_e.regs 4).toNat + 8)
      none (fs.map (Frame.mv hi hi1)) := by
    have hra : s_e.mem.readLE (s_e.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
      rw [hemem, he4n, hmA.readLE_word_out (by omega) (by omega) (by omega) trivial
        (by rw [hrdm _ _ (by omega) (by omega)]; exact hcode.1), hrdm _ _ (by omega) (by omega)]
    rw [hra, hemem, he4n, show (s.regs 4).toNat + hi1 - hi + 8 = ((s.regs 4).toNat + 8) + hi1 - hi by omega]
    exact hchs.moved hmA hCO hAl (by omega) (by omega) fun _ _ _ => trivial
  have hcl : ∀ a, hi ≤ a + hi1 → framesCls Arch.amd64 FT (fs.map (Frame.mv hi hi1)) (a + hi1 - hi) =
      framesCls Arch.amd64 FT fs a := fun a ha => hch.framesCls_mv (by omega) (by omega) ha
  -- the argument read back
  have hx0e : (s_e.regs 0).toNat = (s.regs 0).toNat := by
    rw [he0, hsp_r, show (s.regs 4).toNat + hi1 - hi + 8 = ((s.regs 4).toNat + 8) + hi1 - hi by omega,
      hmA.readLE_scalar (by omega) (by omega) (fun j hj => by
        rw [show (s.regs 4).toNat + 8 + j - ((s.regs 4).toNat + 8 + j) % 8 = (s.regs 4).toNat + 8 by omega,
          hclsA, hc8]) trivial, hmem, stubMem, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)), Nat.mod_eq_of_lt (s.regs 0).isLt]
  obtain ⟨-, -, hge3, hge4, hge5⟩ := hgr.gstack
  simp only [gStackguard0, stackGuard] at hge5
  have hgse : GStack s_e.mem (s_e.regs 14).toNat lo1 hi1 := by
    rw [he14, hemem]; exact hgr.gstack
  -- the precondition on the new stack, which has room
  have hpe : Pre FT pool rt H s_e := by
    refine ⟨lo1, hi1, hgse, by rw [he14]; exact hgo, h4k1, by omega, by omega, hhi48', hal1', hal2',
      by omega, hinp1, by rw [hemem]; exact hpok_r, ?_, ?_, ⟨_, hche, fun f hf hstp => ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [he5, BitVec.toNat_ofNat]
      have := BPOK.mv (pool := pool) hinp (by omega) (by omega) (by omega) hbp (hi1 := hi1) (lo1 := lo1)
      rw [Nat.mod_eq_of_lt]; exact this
      simp only [adjustWord]; split <;> have := (s.regs 5).isLt <;> omega
    · rw [hemem, he4n, hmA.readLE_word_out (by omega) (by omega) (by omega) trivial
        (by rw [hrdm _ _ (by omega) (by omega)]; exact hcode.1), hrdm _ _ (by omega) (by omega)]
      exact hr47
    · obtain ⟨f0, hf0, rfl⟩ := List.mem_map.1 hf
      obtain ⟨h1, h2, -⟩ := hfb f0 hf0
      have := hfsp f0 hf0 hstp
      simp only [Frame.mv]; rw [he4n]; omega
    · rw [he4n, show (s.regs 4).toNat + hi1 - hi + 8 = ((s.regs 4).toNat + 8) + hi1 - hi by omega,
        hcl _ (by omega)]
      exact hc8
    · rw [hx0e, he4n, show hi1 - ((s.regs 4).toNat + hi1 - hi) = hi - (s.regs 4).toNat by omega]; exact hfit
    · rw [he14, hemem]; exact hgr.ready
    · rw [hemem]; exact hm.noptr.of_frame hgr.frame
  have hroome : s_e.mem.readLE ((s_e.regs 14).toNat + 16) 8 < (s_e.regs 4).toNat := by
    rw [he14, hemem, hge5, he4n]; omega
  have hret_e : retAddrOf s_e = retAddrOf s := by
    rw [retAddrOf, retAddrOf, hemem, he4n, hmA.readLE_word_out (by omega) (by omega) (by omega) trivial
        (by rw [hrdm _ _ (by omega) (by omega)]; exact hcode.1), hrdm _ _ (by omega) (by omega)]
  refine GrownRet64.of_steps hstg ?_
  rw [← hret_e]
  refine (room_case FT pool rt H reloc henv n ih s_e hepc hpe (by rw [hx0e, hn]) hroome).mono
    fun s'' hq => ?_
  obtain ⟨loe, hie, lo2, hi2, hgse', hgs2, hsz, h4k2, hal12, hal22, hhi482, hinp2, h0, hsp2, h52,
    h142, hmB, hmf, hH2⟩ := hq
  obtain ⟨e1, e2⟩ := GStack.unique hgse hgse'
  subst e1 e2
  refine ⟨lo, hi, lo2, hi2, hgs, by rw [← he14]; exact hgs2, by omega, h4k2, hal12, hal22, hhi482, hinp2,
    by rw [h0, hx0e], ?_, ?_, by rw [h142, he14], ?_, ?_, by rw [← he14]; exact hH2⟩
  · rw [hsp2, he4n]; congr 1; omega
  · rw [h52, he5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [adjustWord]; split <;>
      have := (s.regs 5).isLt <;> omega), adjustWord_trans hinp hinp1 (by omega) (by omega) (by omega) hbp]
  · intro fs0 hfs0
    rw [Chain.unique hfs0 hch]
    have hmB' := hmB _ hche
    rw [he4n, hemem] at hmB'
    have hB : Moved (framesCls Arch.amd64 FT (fs.map (Frame.mv hi hi1))) pool lo1 hi1 hi2
        (((s.regs 4).toNat + 8) + hi1 - hi) [((s.regs 4).toNat + hi1 - hi + 8, (s.regs 4).toNat + hi1 - hi + 16)]
        s_r.mem s''.mem := by
      rw [show (s.regs 4).toNat + 8 + hi1 - hi = (s.regs 4).toNat + hi1 - hi + 8 by omega]; exact hmB'
    have hA' := hmA.mono_base (base' := (s.regs 4).toNat + 8) (by omega) (by omega) (by omega)
    have hAB := hA'.trans' (ex₃ := [((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)]) hB
      (fun a ha _ => by rw [hclsA, hcl a (by omega)])
      (by omega)
      (fun a k ha hx => by
        simp only [outside_cons, outside_nil, and_true] at hx ⊢; exact ⟨trivial, by omega⟩)
    have hAB' := hAB.cls_congr (cls' := framesCls Arch.amd64 FT fs) fun a _ _ => (hclsA a).symm
    refine hAB'.congr_src fun a ha _ hx => ?_
    simp only [outside_cons, outside_nil, and_true] at hx
    rw [hmem, stubMem, Arm64.Memory.bytes_writeLE_outside _ (by omega),
      Arm64.Memory.bytes_writeLE_outside _ (by omega)]
  · refine MemFrame.trans ?_ (hemem ▸ hmf) fun a k h => ⟨h, h⟩
    refine MemFrame.trans ?_ hgr.frame fun a k h => ⟨h, h⟩
    rw [hmem, stubMem]
    exact ((MemFrame.refl s.mem _).writeLE_inRanges _ ((hinp.sub (by omega) (by omega)).append_left rt)).writeLE_inRanges _
      ((hinp.sub (by omega) (by omega)).append_left rt)

/-- **`SumRec` through stack growths, as a grown callee summary**, by induction on `n`. -/
theorem gsum (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) :
    GSummary64 Extracted.program reloc Extracted.entry (Pre FT pool rt H) (Post FT pool rt H) := by
  apply GSummary64.induction (fun s => (s.regs 0).toNat)
  intro n ih s hpc ⟨hpre, hn⟩
  by_cases hroom : s.mem.readLE ((s.regs 14).toNat + 16) 8 < (s.regs 4).toNat
  · exact room_case FT pool rt H reloc henv n ih s hpc hpre hn hroom
  · have hpre' := hpre
    obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hinp, hpok, hbp, hr47, -, hfit,
      hH, -⟩ := hpre'
    obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs
    simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
    have hacc := hpok.accessible hinp
    have hroom' : ¬ lo + 928 < (s.regs 4).toNat := by rw [hgg] at hroom; exact hroom
    apply GrownRet64.of_reaches_stub
    janus64_run
    exact grow_branch FT pool rt H reloc hms henv n ih s hn hpre hroom _ ⟨_, rfl⟩ (by simp [setRegF])
      (by simp [setRegF]) (by simp [setRegF]) rfl

/-- **`SumRec` is correct on a stack of any size, stack growth included** (amd64). -/
theorem correctness (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (n : BitVec 64) :
    EnsuresGrow64 Extracted.program reloc Extracted.entry [n] (Pre FT pool rt H)
      (fun _ s' => s'.regs 0 = BitVec.ofNat 64 (sumTo n.toNat)) := by
  intro ret hret s hs hpre
  janus64_intro hs
  have hg := gsum FT pool rt H reloc hms henv s (by rw [h_rip]; rfl) hpre
  rw [retAddrOf, h_ret] at hg
  refine ((hg.withExit hret.fetch_none fun st hst => hret.notStub st hst).toGrownReturns
    (by have := hret.user; omega)).mono fun s' h => ?_
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h0, _⟩ := h
  rw [h0, h_a0]

/-! ## The theorem is not vacuous -/

namespace Witness

open Janus.Contracts.StackSat (G0 SL SH BL BH pool rt H mem0 mem0_desc mem0_noptr)
open Janus.Contracts.StackSatAmd64 (reloc contract64)

/-- The caller's return address. -/
def ret : Nat := 0x200000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The witness frame table: the binary's frame record of `SumRec` and the caller, which stops
the walk. -/
def extraT : FrameTable :=
  { valid := fun pc => pc == ret, entry := id, spdelta := fun _ => 0, maxspd := fun _ => 0,
    stop := fun pc => pc == ret, injected := fun _ => false, locals := fun _ => [],
    args := fun _ => [], objs := fun _ => [] }

def FTs : FrameTable := FrameTable.ofRecs Extracted.frames extraT

theorem agrees : FTs.Agrees Extracted.frames :=
  FrameTable.ofRecs_agrees _ _ fun r hr pc h1 h2 => by
    replace hr := List.mem_singleton.1 hr
    subst hr
    exact List.find?_cons_of_pos (l := []) (by simpa using And.intro h1 h2)

theorem laws : FTs.Aligned ∧ FTs.InFrame Arch.amd64 :=
  FrameTable.ofRecs_laws_amd64 Extracted.frames extraT (fun r hr => by
    replace hr := List.mem_singleton.1 hr
    subst hr
    exact ⟨rfl, by decide⟩) (fun _ => rfl) (fun _ => rfl)

theorem code : FTs.CodeOutside pool := by
  intro pc hv
  unfold FTs FrameTable.ofRecs at hv
  dsimp only at hv
  cases h : Extracted.frames.find? (fun r => decide (r.entry ≤ pc ∧ pc < r.entry + r.size)) with
  | none =>
    rw [h] at hv
    simp only [extraT, beq_iff_eq] at hv
    subst hv
    exact ⟨by simp only [pool, outside_cons, outside_nil, and_true]; decide, by decide⟩
  | some r =>
    have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    replace hm := List.mem_singleton.1 hm
    subst hm
    simp only at hp
    refine ⟨?_, by omega⟩
    simp only [pool, outside_cons, outside_nil, and_true, SL, SH, BL, BH]; omega

theorem env : Env FTs pool rt := by
  refine ⟨agrees, laws.2, laws.1, code, ?_⟩
  intro a n hin
  obtain ⟨r, hr, h1, h2⟩ := hin
  simp only [pool, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [rt, outside_cons, outside_nil, and_true]
  rcases hr with rfl | rfl <;> simp only [SL, SH, BL, BH, G0] at h1 h2 ⊢ <;> omega

/-- The stack pointer: 64 bytes above the small slot's bottom, so not even the first frame fits. -/
def spw : Nat := SL + 64

/-- The memory: `StackSat`'s, with the return address at `[RSP]`. -/
def memw : Memory := mem0.writeLE spw 8 ret

/-- The call state `SumRec(3)` on the small 4 KiB stack of `StackSat` (`RBP = 0`). -/
def s0 : State :=
  { regs := fun i => if i = 14 then BitVec.ofNat 64 G0 else if i = 4 then BitVec.ofNat 64 spw
      else if i = 0 then 3#64 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := memw }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [3#64] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem memw_desc : memw.readLE G0 8 = SL ∧ memw.readLE (G0 + 8) 8 = SH ∧
    memw.readLE (G0 + 16) 8 = SL + stackGuard := by
  obtain ⟨d1, d2, d3⟩ := mem0_desc
  refine ⟨?_, ?_, ?_⟩ <;> unfold memw <;>
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by simp [G0, spw, SL])] <;> assumption

/-- The first frame does not fit: the prologue grows the stack at once. -/
theorem no_room : ¬ s0.mem.readLE ((s0.regs 14).toNat + 16) 8 < (s0.regs 4).toNat := by
  have hg : (s0.regs 14).toNat = G0 := by decide
  rw [hg, show s0.mem = memw from rfl, memw_desc.2.2, show (s0.regs 4).toNat = spw by decide]
  simp only [stackGuard, spw]; omega

theorem pre : Pre FTs pool rt H s0 := by
  obtain ⟨d1, d2, d3⟩ := memw_desc
  have hin0 : InRanges G0 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hin8 : InRanges (G0 + 8) 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hg : (s0.regs 14).toNat = G0 := by decide
  have hsp : (s0.regs 4).toNat = spw := by decide
  have hr : s0.mem.readLE spw 8 = ret := by decide
  refine ⟨SL, SH, ?_, ?_, by decide, ?_, ?_, by decide, by decide, by decide, ?_,
    ⟨(SL, SH), by simp [pool], Nat.le_refl _, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    mem0_noptr.writeLE _ ⟨(SL, SH), by simp [pool], by decide, by decide⟩⟩
  · rw [hg]; exact ⟨by decide, by decide, by simp only [gStackLo, Nat.add_zero]; exact d1, d2, d3⟩
  · rw [hg]; simp [pool, G0, SL, SH, BL, BH]
  · rw [hsp]; decide
  · rw [hsp]; decide
  · rw [hsp]; decide
  · intro r hr
    simp only [pool, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  · right; rw [show (s0.regs 5).toNat = 0 by decide]
    simp only [pool, outside_cons, outside_nil, and_true]; decide
  · rw [hsp, hr]; decide
  · have el : FTs.locals ret = [] := rfl
    have ea : FTs.args ret = [] := rfl
    have eo : FTs.objs ret = [] := rfl
    have e : Arch.amd64.fp FTs ret (spw + 8) = spw + 16 := by
      show spw + 8 + FTs.spdelta ret + 8 = spw + 16; rw [show FTs.spdelta ret = 0 from rfl]
    refine ⟨[⟨ret, spw + 8, spw + 16⟩], ?_, ?_, ?_⟩
    · rw [hsp, hr]
      have := Chain.stop (A := Arch.amd64) (FT := FTs) (m := s0.mem) (hi := SH) (pc := ret) (sp := spw + 8)
        (lr0 := none) rfl rfl rfl (by decide) (by rw [e]; decide)
      rw [e] at this; exact this
    · intro f hf hst; simp at hf; subst hf; exact absurd hst (by decide)
    · rw [hsp]; simp [frameCls, el, ea, eo, bitsAt, Arch.varp, Arch.argp, Arch.minLocals]
  · rw [hsp, show (s0.regs 0).toNat = 3 by decide]; simp only [stackGuard, maxstacksize, spw, SH, SL]; omega
  · rw [hg]; refine ⟨rfl, .inl ⟨?_, ?_⟩⟩
    · rw [readLE_rtView hin0]; exact d1
    · rw [readLE_rtView hin8]; exact d2

/-- All hypotheses of `correctness` hold together, for a call whose first frame does not fit. -/
theorem nonvacuous : ∃ (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (ret : Nat) (s : State),
    MorestackContract64 Extracted.program FT pool rt H reloc ∧ Env FT pool rt ∧
    RetAddr Extracted.program ret ∧ CallSetup (Extracted.program.withExit ret) Extracted.entry [3#64] s ∧
    Pre FT pool rt H s ∧ ¬ s.mem.readLE ((s.regs 14).toNat + 16) 8 < (s.regs 4).toNat :=
  ⟨FTs, pool, rt, H, reloc FTs, ret, s0, contract64 _ FTs, env, hret, setup, pre, no_room⟩

/-- So the guarantee is reached: from a stack where not even the first frame fits, `SumRec(3)`
grows the stack and returns `6`. -/
theorem returns : GrownReturns64 (Extracted.program.withExit ret) (reloc FTs) s0
    (fun s' => s'.regs 0 = 6#64) :=
  (correctness FTs pool rt H (reloc FTs) (contract64 _ FTs) env 3#64 ret hret s0 setup pre).mono
    fun s' h => by rw [h]; rfl

end Witness

end Proof
