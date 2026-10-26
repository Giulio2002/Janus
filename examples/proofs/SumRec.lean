import Extracted

/-!
# `SumRec(n uint64) uint64`: recursion proved with stack growth at every depth (R7)

```go
func SumRec(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return n + SumRec(n-1)
}
```

**Guarantee.** For every frame table `FT`, stack pools, runtime memory `rt`, readiness `H` and
every runtime that meets the `morestack` contract (`MorestackContract`), and every call state
whose goroutine stack `[lo, hi)` is described by `g.stack` — **with no assumption that the
recursion fits** (`Pre` asks only for the `maxstacksize` bound of `n + 1` frames) — `SumRec(n)`
returns `0 + 1 + … + n` (`correctness`, `EnsuresGrow`). The stack may grow at any depth: each
level's prologue may call `morestack`, which moves every frame of the recursion so far.

**How.** `gsum` is a grown callee summary (`GSummary`) by induction on `n`
(`GSummary.induction`). At one level (`room_case`), when the prologue falls through, the code
runs to the recursive call (`callPre`, `blStep`), the induction hypothesis covers the callee —
which may grow the stack and move this frame — and the epilogue (`epi`) reads this frame back on
the moved stack: the spilled `n` copied (the stack maps call it a scalar), the saved frame
pointer adjusted (a pointer into the stack), the saved return address copied (a code address).
`Post` states that move (`Moved` along the caller's walk), so it composes level by level
(`Moved.mono_base`, `cls_congr`, `congr_src`). When the prologue does not fall through
(`grow_branch`), the contract grows the stack once, the glue reloads `n`, and the frame now fits,
so `room_case` applies on the new stack; the two moves compose into one (`Moved.trans'`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Stack Janus.Contracts
  Janus.Contracts.Stack

namespace Proof

theorem base : ∀ t : State, t.pc = BitVec.ofNat 64 Extracted.entry →
    (t.regs 30).toNat % 4 = 0 → (t.regs 30).toNat < 2 ^ 56 →
    (t.regs 28).toNat + 24 ≤ 2 ^ 48 → t.mem.accessible ((t.regs 28).toNat + 16) 8 false = true →
    t.mem.readLE ((t.regs 28).toNat + 16) 8 < t.sp.toNat → t.sp.toNat % 16 = 0 →
    40 ≤ t.sp.toNat → t.sp.toNat ≤ 2 ^ 48 → t.mem.accessible (t.sp.toNat - 40) 16 true = true →
    t.regs 0 = 0 →
    ReachesRet Extracted.program (t.regs 30) t (fun t' => t'.regs 0 = 0 ∧ t'.sp = t.sp ∧
      t'.regs 29 = t.regs 29 ∧ t'.regs 28 = t.regs 28 ∧ t'.regs 18 = t.regs 18 ∧
      t'.mem = (t.mem.writeLE (t.sp.toNat - 32) 8 (t.regs 30).toNat).writeLE (t.sp.toNat - 40) 8
        (t.regs 29).toNat) := by
  intro t hpc h1 h2 h3 h4 h5 h6 h7 h8 h9 h0
  janus_run

theorem callPre : ∀ t : State, t.pc = BitVec.ofNat 64 Extracted.entry →
    (t.regs 28).toNat + 24 ≤ 2 ^ 48 → t.mem.accessible ((t.regs 28).toNat + 16) 8 false = true →
    t.mem.readLE ((t.regs 28).toNat + 16) 8 < t.sp.toNat → t.sp.toNat % 16 = 0 →
    40 ≤ t.sp.toNat → t.sp.toNat + 16 ≤ 2 ^ 48 → t.mem.accessible (t.sp.toNat - 40) 16 true = true →
    t.mem.accessible (t.sp.toNat + 8) 8 true = true → t.regs 0 ≠ 0 →
    ReachesRet Extracted.program (BitVec.ofNat 64 (Extracted.entry + 0x34)) t (fun t' =>
      t'.sp = t.sp - 32 ∧ t'.regs 0 = t.regs 0 - 1 ∧ t'.regs 29 = t.sp - 40 ∧
      t'.regs 30 = t.regs 30 ∧ t'.regs 28 = t.regs 28 ∧ t'.regs 18 = t.regs 18 ∧
      t'.mem = ((t.mem.writeLE (t.sp.toNat - 32) 8 (t.regs 30).toNat).writeLE (t.sp.toNat - 40) 8
        (t.regs 29).toNat).writeLE (t.sp.toNat + 8) 8 (t.regs 0).toNat) := by
  intro t hpc h3 h4 h5 h6 h7 h8 h9 h10 h0
  janus_run until [Extracted.entry + 0x34]
  exact ReachesRet.done rfl ⟨rfl, by simp [setReg], by simp [setReg], by simp [setReg],
    by simp [setReg], by simp [setReg], rfl⟩

theorem blStep : ∀ u : State, u.pc = BitVec.ofNat 64 (Extracted.entry + 0x34) →
    ReachesRet Extracted.program (BitVec.ofNat 64 Extracted.entry) u (fun u' =>
      u'.regs = setReg u.regs 30 (BitVec.ofNat 64 (Extracted.entry + 0x38)) ∧ u'.sp = u.sp ∧
        u'.mem = u.mem) := by
  intro u hpc
  janus_step
  exact ReachesRet.done rfl ⟨rfl, rfl, rfl⟩

theorem epi : ∀ t : State, t.pc = BitVec.ofNat 64 (Extracted.entry + 0x38) → t.sp.toNat % 16 = 0 →
    8 ≤ t.sp.toNat → t.sp.toNat + 48 ≤ 2 ^ 48 → t.mem.accessible (t.sp.toNat - 8) 56 false = true →
    t.mem.readLE t.sp.toNat 8 % 4 = 0 → t.mem.readLE t.sp.toNat 8 < 2 ^ 48 →
    ReachesRet Extracted.program (BitVec.ofNat 64 (t.mem.readLE t.sp.toNat 8)) t (fun t' =>
      t'.regs 0 = t.regs 0 + BitVec.ofNat 64 (t.mem.readLE (t.sp.toNat + 40) 8) ∧
      t'.sp = t.sp + 32 ∧ t'.regs 29 = BitVec.ofNat 64 (t.mem.readLE (t.sp.toNat - 8) 8) ∧
      t'.regs 28 = t.regs 28 ∧ t'.regs 18 = t.regs 18 ∧ t'.mem = t.mem) := by
  intro t hpc h1 h2 h3 h4 h5 h6
  janus_run

theorem glue : ∀ t : State, t.pc = BitVec.ofNat 64 (Extracted.entry + 0x58) →
    t.mem.accessible (t.sp.toNat + 8) 8 false = true → t.sp.toNat + 16 ≤ 2 ^ 48 →
    t.sp.toNat % 16 = 0 →
    ReachesRet Extracted.program (BitVec.ofNat 64 Extracted.entry) t (fun t' =>
      t'.pc = BitVec.ofNat 64 Extracted.entry ∧ t'.sp = t.sp ∧ t'.mem = t.mem ∧
      t'.regs 0 = BitVec.ofNat 64 (t.mem.readLE (t.sp.toNat + 8) 8) ∧
      (∀ r, r ≠ 0 → t'.regs r = t.regs r)) := by
  intro t hpc hacc hsp hal
  janus_run until [Extracted.entry]
  exact ReachesRet.done rfl ⟨rfl, rfl, rfl, by simp [setReg], fun r h0 => by simp [setReg, h0]⟩

/-- `0 + 1 + … + n`. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

/-- The glue pc after the `morestack` call, and the return pc of the recursive call. -/
abbrev gluePc : Nat := Extracted.entry + 0x58
abbrev callRet : Nat := Extracted.entry + 0x38

/-- What the binary's frame record says about `SumRec` (`tableOK_of`): at the glue (no frame yet,
largest frame 32 bytes, the argument a scalar) and at the recursive call's return pc (a 32-byte
frame with no pointer locals, a scalar argument, no stack objects). -/
def TableOK (FT : FrameTable) : Prop :=
  FT.valid gluePc = true ∧ FT.stop gluePc = false ∧ FT.injected gluePc = false ∧
  FT.spdelta gluePc = 0 ∧ FT.maxspd gluePc = 32 ∧ (∀ j, (FT.args gluePc).getD j false = false) ∧
  FT.objs gluePc = [] ∧
  FT.valid callRet = true ∧ FT.stop callRet = false ∧ FT.injected callRet = false ∧
  FT.spdelta callRet = 32 ∧ (∀ j, (FT.locals callRet).getD j false = false) ∧
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

/-- The environment: the frame table agrees with the binary's frame records (`Extracted.frames`,
`janus extract --frames`: SP deltas, stack maps and stack objects read from the pclntab), the
laws of every pclntab (frame words inside the frame, aligned frames, code outside the stack
pools), and the stack pools apart from the runtime's own memory. -/
def Env (FT : FrameTable) (pool rt : List (Nat × Nat)) : Prop :=
  FT.Agrees Extracted.frames ∧ FT.InFrame Arch.arm64 ∧ FT.Aligned ∧ FT.CodeOutside pool ∧
    (∀ a n, InRanges a n pool → Outside a n rt)

/-- The precondition of a call `SumRec(n)` (no room assumed): the goroutine stack `[lo, hi)`,
the caller's walk (its stack maps do not mark the argument slot), the stack pools, the
`maxstacksize` bound for `n + 1` frames, and the runtime's readiness. -/
def Pre (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s : State) : Prop :=
  ∃ lo hi, GStack s.mem (s.regs 28).toNat lo hi ∧ Outside (s.regs 28).toNat 24 pool ∧
    4096 ≤ lo ∧ lo + 8 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ hi ∧ hi ≤ 2 ^ 48 ∧
    lo % 16 = 0 ∧ hi % 16 = 0 ∧ s.sp.toNat % 16 = 0 ∧ s.regs 29 = s.sp - 8 ∧
    InRanges lo (hi - lo) pool ∧ PoolOK s.mem pool ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
    (∃ fs, Chain Arch.arm64 FT s.mem hi (s.regs 30).toNat s.sp.toNat none fs ∧
      (∀ f ∈ fs, f.sp = s.sp.toNat ∨ s.sp.toNat + 16 ≤ f.sp) ∧
      framesCls Arch.arm64 FT fs (s.sp.toNat + 8) = false) ∧
    2 * ((hi - s.sp.toNat) + 32 * (s.regs 0).toNat + 32 + stackGuard) ≤ maxstacksize ∧
    H [] (s.regs 28).toNat 0 (rtView rt s.mem)

/-- What a call `SumRec(n)` does, through any number of stack growths: it returns `sumTo n` with
the stack `[lo, hi)` grown to `[lo', hi')` (possibly the same), `SP` and `X29` moved, `g` and
`X18` kept, the caller's frames moved (`Moved` along the caller's walk, from `SP - 8`, the
argument slot free), nothing outside the pools and the runtime memory changed, the runtime
ready again. -/
def Post (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s s' : State) : Prop :=
  ∃ lo hi lo' hi', GStack s.mem (s.regs 28).toNat lo hi ∧ GStack s'.mem (s.regs 28).toNat lo' hi' ∧
    hi - lo ≤ hi' - lo' ∧ 4096 ≤ lo' ∧ lo' % 16 = 0 ∧ hi' % 16 = 0 ∧ hi' ≤ 2 ^ 48 ∧
    InRanges lo' (hi' - lo') pool ∧
    s'.regs 0 = BitVec.ofNat 64 (sumTo (s.regs 0).toNat) ∧
    s'.sp = BitVec.ofNat 64 (s.sp.toNat + hi' - hi) ∧
    s'.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 8 + hi' - hi) ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
    (∀ fs, Chain Arch.arm64 FT s.mem hi (s.regs 30).toNat s.sp.toNat none fs →
      Moved (fun a => decide (a = s.sp.toNat - 8) || framesCls Arch.arm64 FT fs a) pool lo hi hi'
        (s.sp.toNat - 8) [(s.sp.toNat + 8, s.sp.toNat + 16)] s.mem s'.mem) ∧
    MemFrame s.mem s'.mem (pool ++ rt) ∧ H [] (s.regs 28).toNat 0 (rtView rt s'.mem)

/-- A bitmap with no bits set marks nothing. -/
theorem bitsAt_false {bs : List Bool} (h : ∀ j, bs.getD j false = false) (b : Int) (a : Nat) :
    bitsAt b bs a = false := by
  simp only [bitsAt, h, Bool.and_false]

/-- `SumRec`'s frame suspended at the recursive call (`SP = sp - 32`, `fp = sp`) marks exactly
its saved frame pointer slot `sp - 8`. -/
theorem frameF {FT : FrameTable} (hT : TableOK FT) {sp : Nat} (h40 : 40 ≤ sp) (a : Nat) :
    frameCls Arch.arm64 FT callRet (sp - 32) sp a = (a == sp - 8) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hl, ha, ho⟩ := hT
  have hv : Arch.arm64.varp (sp - 32) sp = sp - 8 := by simp [Arch.varp]; omega
  simp only [frameCls, hv, Arch.argp, ho, List.any_nil, Bool.or_false, bitsAt_false hl,
    bitsAt_false ha, Bool.and_false]
  rw [show decide (sp + 8 = sp - 8 + 16) = true by simp; omega, Bool.true_and]

/-- The frame at the glue (`SP = fp = sp`, no frame yet) marks nothing. -/
theorem frame0 {FT : FrameTable} (hT : TableOK FT) (sp a : Nat) :
    frameCls Arch.arm64 FT gluePc sp sp a = false := by
  obtain ⟨-, -, -, -, -, ha, ho, -⟩ := hT
  have hv : Arch.arm64.varp sp sp = sp := by simp [Arch.varp]
  simp only [frameCls, hv, Arch.argp, ho, List.any_nil, Bool.or_false, bitsAt_false ha,
    Bool.and_false]
  have e1 : decide (sp + 8 = sp + 16) = false := decide_eq_false (by omega)
  have e2 : decide (Arch.arm64.minLocals + sp < sp) = false :=
    decide_eq_false (by unfold Arch.minLocals; omega)
  rw [e1, e2, Bool.false_and, Bool.false_and, Bool.false_or]

/-- `SumRec` on a stack whose prologue check falls through. The base case returns at once; the
recursive case runs to the recursive call, uses the induction hypothesis there (the callee may
grow the stack, moving this frame), and finishes on the possibly moved stack. -/
theorem room_case (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (henv : Env FT pool rt) (n : Nat)
    (ih : GSummary Extracted.program reloc Extracted.entry
      (fun s => Pre FT pool rt H s ∧ (s.regs 0).toNat < n) (Post FT pool rt H))
    (t : State) (hpc : t.pc = BitVec.ofNat 64 Extracted.entry) (hp : Pre FT pool rt H t)
    (hn : (t.regs 0).toNat = n)
    (hroom : t.mem.readLE ((t.regs 28).toNat + 16) 8 < t.sp.toNat) :
    GrownRet Extracted.program reloc (t.regs 30) t (Post FT pool rt H t) := by
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hfp, hinp, hpok, hr4, hr48,
    ⟨fs, hch, hfsp, hc8⟩, hfit, hH⟩ := hp
  obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv
  have hT := tableOK_of hA
  have hgs' := hgs
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
  have hacc := hpok.accessible hinp
  have hspL : lo + 928 < t.sp.toNat := by rw [hgg] at hroom; exact hroom
  have hsp64 := t.sp.isLt
  have hinw : ∀ a k, lo ≤ a → a + k ≤ hi → InRanges a k pool := fun a k h1 h2 => hinp.sub h1 (by omega)
  have hinr : ∀ a k, lo ≤ a → a + k ≤ hi → InRanges a k (pool ++ rt) := fun a k h1 h2 =>
    (hinw a k h1 h2).append_left rt
  by_cases hz : t.regs 0 = 0
  · obtain ⟨k, t', hst, hpc', hb0, hbsp, hb29, hb28, hb18, hbm⟩ := base t hpc hr4 (by omega) hg24
      (Memory.accessible_mono _ hgacc (by omega) (by omega)) hroom hal3 (by omega) (by omega)
      (Memory.accessible_mono _ hacc (by omega) (by omega)) hz
    refine .done hst hpc' ⟨lo, hi, lo, hi, hgs, ?_, Nat.le_refl _, h4k, hal1, hal2, hhi48, hinp,
      ?_, ?_, ?_, hb28, hb18, ?_, ?_, ?_⟩
    · rw [hbm]
      exact GStack.writeLE (GStack.writeLE hgs hgo (hinw _ _ (by omega) (by omega))) hgo
        (hinw _ _ (by omega) (by omega))
    · rw [hb0, hz]; rfl
    · rw [hbsp, Nat.add_sub_cancel, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [hb29, hfp, Nat.add_sub_cancel]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · intro fs0 _
      rw [hbm]
      refine Moved.of_agree _ pool ⟨by omega, by omega⟩ h4k (by omega) (by omega) fun a h1 h2 _ => ?_
      rw [Memory.bytes_writeLE_outside _ (by omega), Memory.bytes_writeLE_outside _ (by omega)]
    · rw [hbm]
      exact ((MemFrame.refl t.mem _).writeLE_inRanges _ (hinr _ _ (by omega) (by omega))).writeLE_inRanges _
        (hinr _ _ (by omega) (by omega))
    · rw [hbm, rtView_writeLE (hPA _ _ (hinw _ _ (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hinw _ _ (by omega) (by omega)))]
      exact hH
  · -- the recursive case
    have hz' : (t.regs 0).toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
    have hx0 := (t.regs 0).isLt
    have hx29 : (t.regs 29).toNat = t.sp.toNat - 8 := by
      rw [hfp, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    obtain ⟨k1, u, hst1, hupc, hu_sp, hu0, hu29, hu30, hu28, hu18, hum⟩ := callPre t hpc hg24
      (Memory.accessible_mono _ hgacc (by omega) (by omega)) hroom hal3 (by omega) (by omega)
      (Memory.accessible_mono _ hacc (by omega) (by omega))
      (Memory.accessible_mono _ hacc (by omega) (by omega)) hz
    obtain ⟨k2, v, hst2, hvpc, hvr, hvsp, hvm⟩ := blStep u hupc
    -- the memory at the recursive call
    obtain ⟨M1, hM1⟩ : ∃ M1, M1 = ((t.mem.writeLE (t.sp.toNat - 32) 8 (t.regs 30).toNat).writeLE
        (t.sp.toNat - 40) 8 (t.regs 29).toNat).writeLE (t.sp.toNat + 8) 8 (t.regs 0).toNat := ⟨_, rfl⟩
    have hvmem : v.mem = M1 := by rw [hvm, hum, hM1]
    have hv0 : v.regs 0 = t.regs 0 - 1 := by rw [hvr]; simp [setReg, hu0]
    have hv28 : v.regs 28 = t.regs 28 := by rw [hvr]; simp [setReg, hu28]
    have hv18 : v.regs 18 = t.regs 18 := by rw [hvr]; simp [setReg, hu18]
    have hv29 : v.regs 29 = t.sp - 40 := by rw [hvr]; simp [setReg, hu29]
    have hv30 : v.regs 30 = BitVec.ofNat 64 callRet := by rw [hvr]; simp [setReg]
    have hvspn : v.sp.toNat = t.sp.toNat - 32 := by
      rw [hvsp, hu_sp, BitVec.toNat_sub, show (32 : BitVec 64).toNat = 32 from rfl]; omega
    have hagM1 : ∀ a k, a + k ≤ t.sp.toNat - 40 ∨ t.sp.toNat - 24 ≤ a → a + k ≤ t.sp.toNat + 8 ∨
        t.sp.toNat + 16 ≤ a → M1.readLE a k = t.mem.readLE a k := by
      intro a k h1 h2
      rw [hM1, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have haccM1 : ∀ a k w, M1.accessible a k w = t.mem.accessible a k w := by
      intro a k w; rw [hM1, Memory.accessible_writeLE, Memory.accessible_writeLE, Memory.accessible_writeLE]
    have hM1lr : M1.readLE (t.sp.toNat - 32) 8 = (t.regs 30).toNat := by
      rw [hM1, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (t.regs 30).isLt
    have hM1fp : M1.readLE (t.sp.toNat - 40) 8 = t.sp.toNat - 8 := by
      rw [hM1, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, hx29]
      exact Nat.mod_eq_of_lt (by omega)
    have hM1x : M1.readLE (t.sp.toNat + 8) 8 = (t.regs 0).toNat := by
      rw [hM1, Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt hx0
    have hgsM1 : GStack M1 (t.regs 28).toNat lo hi := by
      rw [hM1]
      exact GStack.writeLE (GStack.writeLE (GStack.writeLE hgs hgo (hinw _ _ (by omega) (by omega))) hgo
        (hinw _ _ (by omega) (by omega))) hgo (hinw _ _ (by omega) (by omega))
    -- the walk at the recursive call: this frame, then the caller's
    have hfb := hch.bounds
    have hchM1 : Chain Arch.arm64 FT M1 hi (t.regs 30).toNat t.sp.toNat none fs :=
      Chain.congr hch (by omega) fun f hf _ => by
        obtain ⟨h1, -⟩ := hfb f hf
        simp only [Arch.lrSlot]
        exact hagM1 _ _ (by omega) (by rcases hfsp f hf with h | h <;> omega)
    have hT0 := hT
    obtain ⟨hTv, hTs, hTi, -, -, -, -, hTv', hTs', hTi', hTd', -, -, -⟩ := hT0
    have hfpF : Arch.arm64.fp FT callRet (t.sp.toNat - 32) = t.sp.toNat := by
      simp [Arch.fp, hTd']; omega
    have hchv : Chain Arch.arm64 FT v.mem hi callRet (t.sp.toNat - 32) none
        (⟨callRet, t.sp.toNat - 32, Arch.arm64.fp FT callRet (t.sp.toNat - 32)⟩ :: fs) := by
      rw [hvmem]
      refine .cons hTv' hTs' hTi' (by omega) (by rw [hfpF]; omega) ?_
      rw [hfpF]
      have : Arch.arm64.lrOf M1 (t.sp.toNat - 32) t.sp.toNat none = (t.regs 30).toNat := by
        simp only [Arch.lrOf]; rw [if_pos (by omega), hM1lr]
      rw [this]; exact hchM1
    have hclsF : ∀ a, framesCls Arch.arm64 FT
        (⟨callRet, t.sp.toNat - 32, Arch.arm64.fp FT callRet (t.sp.toNat - 32)⟩ :: fs) a =
        ((a == t.sp.toNat - 8) || framesCls Arch.arm64 FT fs a) := by
      intro a; simp only [framesCls_cons, hfpF]; rw [frameF hT (by omega)]
    -- the precondition at the recursive call
    have hpv : Pre FT pool rt H v := by
      refine ⟨lo, hi, by rw [hv28, hvmem]; exact hgsM1, by rw [hv28]; exact hgo, h4k, by omega,
        by omega, hhi48, hal1, hal2, by omega, ?_, hinp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hv29, hvsp, hu_sp]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub, show (40 : BitVec 64).toNat = 40 from rfl,
          show (32 : BitVec 64).toNat = 32 from rfl, show (8 : BitVec 64).toNat = 8 from rfl]; omega
      · rw [hvmem]; exact hpok.of_accessible haccM1
      · rw [hv30]; decide
      · rw [hv30]; decide
      · refine ⟨_, by rw [hv30, show (BitVec.ofNat 64 callRet).toNat = callRet by decide, hvspn]; exact hchv,
          fun f hf => ?_, ?_⟩
        · rcases List.mem_cons.1 hf with rfl | hf
          · left; rw [hvspn]
          · right; obtain ⟨h1, -⟩ := hfb f hf; rw [hvspn]; omega
        · rw [hvspn, hclsF, hch.framesCls_below hIF (by omega)]; simp; omega
      · rw [hv0, hvspn, BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]
        have : 1 ≤ (t.regs 0).toNat := by omega
        rw [show (2 ^ 64 - 1 + (t.regs 0).toNat) % 2 ^ 64 = (t.regs 0).toNat - 1 by omega]
        omega
      · rw [hv28, hvmem, hM1, rtView_writeLE (hPA _ _ (hinw _ _ (by omega) (by omega))),
          rtView_writeLE (hPA _ _ (hinw _ _ (by omega) (by omega))),
          rtView_writeLE (hPA _ _ (hinw _ _ (by omega) (by omega)))]
        exact hH
    have hvn : (v.regs 0).toNat < n := by
      rw [hv0, BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]; omega
    refine GrownRet.of_steps hst1 (GrownRet.of_steps hst2 (GrownRet.call ih hvpc ⟨hpv, hvn⟩ fun w hwpc hw => ?_))
    obtain ⟨lov, hiv, lo', hi', hgsv, hgsw, hsz, h4k', hal1', hal2', hhi48', hinp', hw0, hwsp, hw29,
      hw28, hw18, hmv, hmf, hHw⟩ := hw
    rw [hv28, hvmem] at hgsv
    obtain ⟨e1, e2⟩ := GStack.unique hgsM1 hgsv
    subst e1 e2
    rw [hv28] at hgsw hHw
    have hmvF := hmv _ (by rw [hv30, show (BitVec.ofNat 64 callRet).toNat = callRet by decide, hvspn]; exact hchv)
    rw [hvspn, hvmem] at hmvF
    have hwspn' : w.sp.toNat = t.sp.toNat - 32 + hi' - hi := by
      rw [hwsp, hvspn, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (show t.sp.toNat - 32 + hi' - hi < 2 ^ 64 by omega)
    have hgro := hmvF.grows
    -- the frame read back on the (possibly moved) stack
    have rd8 : w.mem.readLE (w.sp.toNat + 40) 8 = (t.regs 0).toNat := by
      rw [hwspn', show t.sp.toNat - 32 + hi' - hi + 40 = (t.sp.toNat + 8) + hi' - hi by omega,
        hmvF.readLE_scalar (by omega) (by omega) (fun j hj => by
          rw [show t.sp.toNat + 8 + j - (t.sp.toNat + 8 + j) % 8 = t.sp.toNat + 8 by omega, hclsF,
            hc8]; simp; omega) (by simp only [outside_cons, outside_nil, and_true]; omega), hM1x]
    have rdFP : w.mem.readLE (w.sp.toNat - 8) 8 = t.sp.toNat - 8 + hi' - hi := by
      rw [hwspn', show t.sp.toNat - 32 + hi' - hi - 8 = (t.sp.toNat - 32 - 8) + hi' - hi by omega,
        hmvF.readLE_ptr (by omega) (by omega) (by omega) (by simp)
          (by simp only [outside_cons, outside_nil, and_true]; omega)
          (by rw [show t.sp.toNat - 32 - 8 = t.sp.toNat - 40 by omega, hM1fp]; omega)
          (by rw [show t.sp.toNat - 32 - 8 = t.sp.toNat - 40 by omega, hM1fp]; omega),
        show t.sp.toNat - 32 - 8 = t.sp.toNat - 40 by omega, hM1fp]
    have hcode := hCO _ hch.valid_head
    have rdLR : w.mem.readLE w.sp.toNat 8 = (t.regs 30).toNat := by
      rw [hwspn', hmvF.readLE_word_out (by omega) (by omega) (by omega)
          (by simp only [outside_cons, outside_nil, and_true]; omega) (by rw [hM1lr]; exact hcode.1), hM1lr]
    -- the epilogue
    have hpok_w : PoolOK w.mem pool := hpok.of_accessible fun a k w' => by rw [hmf.accessible, hvmem, haccM1]
    have haccw : w.mem.accessible (w.sp.toNat - 8) 56 false = true :=
      Memory.accessible_read_of_write _ (hpok_w.accessible (hinp'.sub (by omega) (by omega)))
    obtain ⟨k3, x, hst3, hxpc, hx0', hxsp, hx29', hx28, hx18, hxm⟩ := epi w (hwpc.trans hv30)
      (by omega) (by omega) (by omega) haccw (by rw [rdLR]; exact hr4) (by rw [rdLR]; exact hr48)
    refine .done hst3 (by rw [hxpc, rdLR, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      ⟨lo, hi, lo', hi', hgs, by rw [hxm]; exact hgsw, hsz, h4k', hal1', hal2', hhi48', hinp', ?_, ?_, ?_,
        by rw [hx28, hw28, hv28], by rw [hx18, hw18, hv18], ?_, ?_, by rw [hxm]; exact hHw⟩
    · -- the result: `sumTo (n - 1) + n`
      have hv0n : (v.regs 0).toNat = (t.regs 0).toNat - 1 := by
        rw [hv0, BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]; omega
      rw [hx0', hw0, rd8, hv0n, BitVec.ofNat_add_ofNat]
      obtain ⟨m, hm⟩ : ∃ m, (t.regs 0).toNat = m + 1 := ⟨(t.regs 0).toNat - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      show BitVec.ofNat 64 (sumTo m + (m + 1)) = BitVec.ofNat 64 ((m + 1) + sumTo m)
      rw [Nat.add_comm (sumTo m)]
    · rw [hxsp]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hwspn', BitVec.toNat_ofNat, show (32 : BitVec 64).toNat = 32 from rfl]; omega
    · rw [hx29', rdFP]
    · intro fs0 hfs0
      rw [Chain.unique hfs0 hch, hxm]
      have h1 := hmvF.mono_base (base' := t.sp.toNat - 8) (by omega) (by omega) (by omega)
      have h2 := h1.mono_ex' (ex' := [(t.sp.toNat + 8, t.sp.toNat + 16)]) fun a k ha _ => by
        simp only [outside_cons, outside_nil, and_true]; omega
      have h3 := h2.cls_congr (cls' := fun a => decide (a = t.sp.toNat - 8) || framesCls Arch.arm64 FT fs a)
        fun a ha _ => by
          rw [hclsF]
          by_cases e : a = t.sp.toNat - 8
          · simp [e]
          · have e' : a ≠ t.sp.toNat - 32 - 8 := by omega
            simp [e, e']
      refine h3.congr_src fun a ha _ hx => ?_
      simp only [outside_cons, outside_nil, and_true] at hx
      rw [hM1, Memory.bytes_writeLE_outside _ (by omega), Memory.bytes_writeLE_outside _ (by omega),
        Memory.bytes_writeLE_outside _ (by omega)]
    · rw [hxm]
      refine MemFrame.trans ?_ (hvmem ▸ hmf) fun a k h => ⟨h, h⟩
      rw [hM1]
      exact (((MemFrame.refl t.mem _).writeLE_inRanges _ (hinr _ _ (by omega) (by omega))).writeLE_inRanges _
        (hinr _ _ (by omega) (by omega))).writeLE_inRanges _ (hinr _ _ (by omega) (by omega))




/-- The growth path at one level: from the prologue's `morestack` call, the contract resumes on a
larger stack, the glue reloads `n` (copied: the stack maps call the slot a scalar), and the stack
now has room for this frame, so `room_case` applies; its postcondition on the new stack composes
with the move into one on the old stack (`Moved.trans'`). -/
theorem grow_branch (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (n : Nat)
    (ih : GSummary Extracted.program reloc Extracted.entry
      (fun s => Pre FT pool rt H s ∧ (s.regs 0).toNat < n) (Post FT pool rt H))
    (s : State) (hn : (s.regs 0).toNat = n) (lo hi : Nat) (hgs : GStack s.mem (s.regs 28).toNat lo hi)
    (hgo : Outside (s.regs 28).toNat 24 pool) (h4k : 4096 ≤ lo) (hlo : lo + 8 ≤ s.sp.toNat)
    (hhi : s.sp.toNat + 16 ≤ hi) (hhi48 : hi ≤ 2 ^ 48) (hal1 : lo % 16 = 0) (hal2 : hi % 16 = 0)
    (hal3 : s.sp.toNat % 16 = 0) (hfp : s.regs 29 = s.sp - 8) (hinp : InRanges lo (hi - lo) pool)
    (hpok : PoolOK s.mem pool) (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48)
    (fs : List Frame) (hch : Chain Arch.arm64 FT s.mem hi (s.regs 30).toNat s.sp.toNat none fs)
    (hfsp : ∀ f ∈ fs, f.sp = s.sp.toNat ∨ s.sp.toNat + 16 ≤ f.sp)
    (hc8 : framesCls Arch.arm64 FT fs (s.sp.toNat + 8) = false)
    (hfit : 2 * ((hi - s.sp.toNat) + 32 * (s.regs 0).toNat + 32 + stackGuard) ≤ maxstacksize)
    (s_m : State) (hm : MorestackPre Extracted.program FT pool rt H (s.regs 28).toNat lo hi s_m)
    (hglue : s_m.regs 30 = BitVec.ofNat 64 gluePc) (hx3 : s_m.regs 3 = s.regs 30)
    (hsp_m : s_m.sp = s.sp) (h28 : s_m.regs 28 = s.regs 28) (h18 : s_m.regs 18 = s.regs 18)
    (hmem : s_m.mem = s.mem.writeLE (s.sp.toNat + 8) 8 (s.regs 0).toNat)
    (hchm : Chain Arch.arm64 FT s_m.mem hi (s_m.regs 30).toNat s_m.sp.toNat (some (s_m.regs 3).toNat)
      (⟨gluePc, s.sp.toNat, Arch.arm64.fp FT gluePc s.sp.toNat⟩ :: fs)) :
    ∃ s_r, reloc s_m s_r ∧ GrownRet Extracted.program reloc (s.regs 30) s_r (Post FT pool rt H s) := by
  have henv' := henv
  obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv'
  have hT := tableOK_of hA
  obtain ⟨s_r, lo1, hi1, hre, hgr⟩ := hms _ lo hi s_m hm
  refine ⟨s_r, hre, ?_⟩
  obtain ⟨hg1, hg2, h4k1, hal1', hal2', hhi48', hinp1, happ⟩ := hgr.grows
  have hroom := hgr.room
  have hT0 := hT
  obtain ⟨-, -, -, hspd, hmx, -, -⟩ := hT0
  have hgl : (s_m.regs 30).toNat = gluePc := by rw [hglue]; rfl
  rw [hgl, hmx, hsp_m] at hroom
  simp only [stackGuard] at hroom
  have hsp := s.sp.isLt
  have hspm : s_m.sp.toNat = s.sp.toNat := by rw [hsp_m]
  have hsp_r : s_r.sp.toNat = s.sp.toNat + hi1 - hi := by
    rw [hgr.sp, hspm, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hpok_r : PoolOK s_r.mem pool := hm.inPool.2.of_accessible hgr.frame.accessible
  have hacc_r : s_r.mem.accessible lo1 (hi1 - lo1) true = true := hpok_r.accessible hinp1
  -- the glue
  obtain ⟨k, s_e, hst, hepc, -, hesp, hemem, he0, her⟩ := glue s_r (hgr.pc.trans hglue)
    (Memory.accessible_read_of_write _ (Memory.accessible_mono _ hacc_r (by omega) (by omega)))
    (by omega) (by omega)
  have he30 : s_e.regs 30 = s.regs 30 := by rw [her 30 (by decide), hgr.lr, hx3]
  have he28 : s_e.regs 28 = s.regs 28 := by rw [her 28 (by decide), hgr.gkeep.1, h28]
  have he18 : s_e.regs 18 = s.regs 18 := by rw [her 18 (by decide), hgr.gkeep.2, h18]
  have he29 : s_e.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 8 + hi1 - hi) := by
    rw [her 29 (by decide), hgr.regs 29 rfl, hm.fp, hspm]
  have hesp' : s_e.sp.toNat = s.sp.toNat + hi1 - hi := by rw [hesp, hsp_r]
  -- the move
  have hfp0 : Arch.arm64.fp FT gluePc s.sp.toNat = s.sp.toNat := by simp [Arch.fp, hspd]
  have hmA := hgr.moved _ hchm
  rw [hspm] at hmA
  have hclsA : ∀ a, moveCls FT s.sp.toNat (⟨gluePc, s.sp.toNat, Arch.arm64.fp FT gluePc s.sp.toNat⟩ :: fs) a =
      (decide (a = s.sp.toNat - 8) || framesCls Arch.arm64 FT fs a) := by
    intro a; simp only [moveCls, framesCls_cons, hfp0, frame0 hT, Bool.false_or]
  -- the caller's walk, in the memory at the call and after the move
  have hfb := hch.bounds
  have hchs : Chain Arch.arm64 FT s_m.mem hi (s.regs 30).toNat s.sp.toNat none fs :=
    Chain.congr hch (by omega) fun f hf _ => by
      rw [hmem, Memory.readLE_writeLE_of_disjoint _ _ (by
        simp only [Arch.lrSlot]; rcases hfsp f hf with h | h <;> omega)]
  have hche : Chain Arch.arm64 FT s_e.mem hi1 (s_e.regs 30).toNat s_e.sp.toNat none
      (fs.map (Frame.mv hi hi1)) := by
    rw [hemem, he30, hesp']
    exact hchs.moved hmA hCO hAl (by omega) (by omega) fun _ _ _ => trivial
  -- the argument read back
  have hx0e : (s_e.regs 0).toNat = (s.regs 0).toNat := by
    rw [he0, hsp_r, show s.sp.toNat + hi1 - hi + 8 = (s.sp.toNat + 8) + hi1 - hi by omega,
      hmA.readLE_scalar (by omega) (by omega) (fun j hj => by
        rw [show s.sp.toNat + 8 + j - (s.sp.toNat + 8 + j) % 8 = s.sp.toNat + 8 by omega, hclsA, hc8]
        simp; omega) trivial, hmem, Memory.readLE_writeLE_self, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)), Nat.mod_eq_of_lt (s.regs 0).isLt]
  have hcl : ∀ a, hi ≤ a + hi1 → framesCls Arch.arm64 FT (fs.map (Frame.mv hi hi1)) (a + hi1 - hi) =
      framesCls Arch.arm64 FT fs a := fun a ha => hch.framesCls_mv (by omega) (by omega) ha
  obtain ⟨-, -, hge3, hge4, hge5⟩ := hgr.gstack
  simp only [gStackguard0, stackGuard] at hge5
  -- the precondition on the new stack, which has room
  have hpe : Pre FT pool rt H s_e := by
    refine ⟨lo1, hi1, by rw [he28, hemem, ← h28, hm.greg]; exact hgr.gstack, by rw [he28]; exact hgo, h4k1,
      by omega, by omega, hhi48', hal1', hal2', by omega, ?_, hinp1, by rw [hemem]; exact hpok_r,
      by rw [he30]; exact hr4, by rw [he30]; exact hr48, ⟨_, hche, fun f hf => ?_, ?_⟩, ?_, ?_⟩
    · rw [he29, hesp]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, hsp_r, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · obtain ⟨f0, hf0, rfl⟩ := List.mem_map.1 hf
      obtain ⟨h1, -⟩ := hfb f0 hf0
      simp only [Frame.mv]; rw [hesp']; rcases hfsp f0 hf0 with h | h <;> omega
    · rw [hesp', show s.sp.toNat + hi1 - hi + 8 = (s.sp.toNat + 8) + hi1 - hi by omega, hcl _ (by omega)]
      exact hc8
    · rw [hx0e, hesp']; omega
    · rw [he28, hemem, ← h28, hm.greg]; exact hgr.ready
  have hroome : s_e.mem.readLE ((s_e.regs 28).toNat + 16) 8 < s_e.sp.toNat := by
    rw [he28, hemem, ← h28, hm.greg, hge5, hesp']; omega
  refine GrownRet.of_steps hst ?_
  rw [← he30]
  refine (room_case FT pool rt H reloc henv n ih s_e hepc hpe (by rw [hx0e, hn]) hroome).mono
    fun s'' hq => ?_
  obtain ⟨loe, hie, lo2, hi2, hgse, hgs2, hsz, h4k2, hal12, hal22, hhi482, hinp2, h0, hsp2, h292, h282,
    h182, hmB, hmf, hH2⟩ := hq
  obtain ⟨e1, e2⟩ := GStack.unique (by rw [he28, hemem, ← h28, hm.greg]; exact hgr.gstack) hgse
  subst e1 e2
  have esp : s_e.sp.toNat + hi2 - hi1 = s.sp.toNat + hi2 - hi := by rw [hesp']; omega
  have efp : s_e.sp.toNat - 8 + hi2 - hi1 = s.sp.toNat - 8 + hi2 - hi := by rw [hesp']; omega
  refine ⟨lo, hi, lo2, hi2, hgs, by rw [← he28]; exact hgs2, by omega, h4k2, hal12, hal22, hhi482, hinp2,
    by rw [h0, hx0e], by rw [hsp2, esp], by rw [h292, efp],
    by rw [h282, he28], by rw [h182, he18], ?_, ?_, by rw [← he28]; exact hH2⟩
  · intro fs0 hfs0
    rw [Chain.unique hfs0 hch]
    have hmB' := hmB _ hche
    rw [hesp', hemem] at hmB'
    have hB : Moved (fun a => decide (a = s.sp.toNat + hi1 - hi - 8) ||
        framesCls Arch.arm64 FT (fs.map (Frame.mv hi hi1)) a) pool lo1 hi1 hi2
        (s.sp.toNat - 8 + hi1 - hi) [(s.sp.toNat + hi1 - hi + 8, s.sp.toNat + hi1 - hi + 16)] s_r.mem s''.mem := by
      rw [show s.sp.toNat - 8 + hi1 - hi = s.sp.toNat + hi1 - hi - 8 by omega]; exact hmB'
    have hAB := hmA.trans' (ex₃ := [(s.sp.toNat + 8, s.sp.toNat + 16)]) hB
      (fun a ha _ => by
        rw [hclsA, hcl a (by omega)]
        by_cases e : a = s.sp.toNat - 8
        · simp [e]; omega
        · have e' : a + hi1 - hi ≠ s.sp.toNat + hi1 - hi - 8 := by omega
          simp [e, e'])
      (by omega)
      (fun a k ha hx => by
        simp only [outside_cons, outside_nil, and_true] at hx ⊢; exact ⟨trivial, by omega⟩)
    have hAB' := hAB.cls_congr (cls' := fun a => decide (a = s.sp.toNat - 8) || framesCls Arch.arm64 FT fs a)
      fun a _ _ => (hclsA a).symm
    refine hAB'.congr_src fun a ha _ hx => ?_
    simp only [outside_cons, outside_nil, and_true] at hx
    rw [hmem, Memory.bytes_writeLE_outside _ (by omega)]
  · refine MemFrame.trans ?_ (hemem ▸ hmf) fun a k h => ⟨h, h⟩
    refine MemFrame.trans ?_ hgr.frame fun a k h => ⟨h, h⟩
    rw [hmem]
    exact (MemFrame.refl s.mem _).writeLE_inRanges _ ((hinp.sub (by omega) (by omega)).append_left rt)

/-- **`SumRec` through stack growths, as a grown callee summary.** By induction on `n`: at each
level the prologue either falls through (`room_case`: the recursive call uses the induction
hypothesis, and its growths move this frame) or grows the stack once (`grow_branch`), after which
this frame fits. -/
theorem gsum (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) :
    GSummary Extracted.program reloc Extracted.entry (Pre FT pool rt H) (Post FT pool rt H) := by
  apply GSummary.induction (fun s => (s.regs 0).toNat)
  intro n ih s hpc ⟨hpre, hn⟩
  by_cases hroom : s.mem.readLE ((s.regs 28).toNat + 16) 8 < s.sp.toNat
  · exact room_case FT pool rt H reloc henv n ih s hpc hpre hn hroom
  · have hpre' := hpre
    obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hfp, hinp, hpok, hr4, hr48,
      ⟨fs, hch, hfsp, hc8⟩, hfit, hH⟩ := hpre'
    have henv' := henv
    obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv'
    have hT := tableOK_of hA
    have hT0 := hT
    obtain ⟨hv, hst, hinj, hspd, hmx, -, -⟩ := hT0
    have hgs' := hgs
    obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
    simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
    have hacc := hpok.accessible hinp
    have hgw : (s.regs 28).toNat + 24 ≤ s.sp.toNat + 8 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat := by
      have := InRanges.disjoint (hinp.sub (a := s.sp.toNat + 8) (n := 8) (by omega) (by omega)) hgo
      omega
    obtain ⟨mm, hmm⟩ : ∃ mm, mm = s.mem.writeLE (s.sp.toNat + 8) 8 (s.regs 0).toNat := ⟨_, rfl⟩
    have hfp0 : Arch.arm64.fp FT gluePc s.sp.toNat = s.sp.toNat := by simp [Arch.fp, hspd]
    have hlrn : (s.regs 30).toNat = (s.regs 30).toNat := rfl
    have hcm : Chain Arch.arm64 FT mm hi (s.regs 30).toNat s.sp.toNat none fs :=
      Chain.congr hch (by omega) fun f hf _ => by
        rw [hmm, Memory.readLE_writeLE_of_disjoint _ _ (by
          simp only [Arch.lrSlot]; obtain ⟨h1, -⟩ := hch.bounds f hf; rcases hfsp f hf with h | h <;> omega)]
    have hchain : Chain Arch.arm64 FT mm hi gluePc s.sp.toNat (some (s.regs 30).toNat)
        (⟨gluePc, s.sp.toNat, Arch.arm64.fp FT gluePc s.sp.toNat⟩ :: fs) := by
      refine .cons hv hst hinj (by omega) (by rw [hfp0]; omega) ?_
      rw [hfp0]; simpa [Arch.lrOf] using hcm
    have hfit1 : 2 * (hi - lo) ≤ maxstacksize := by
      have h' := hfit; have hr := hroom; rw [hgg] at hr
      simp only [stackGuard] at h' ⊢; omega
    have hfit2 : 2 * ((hi - s.sp.toNat) + 32 + stackGuard) ≤ maxstacksize := by
      have h' := hfit; omega
    apply GrownRet.of_reaches_stub
    janus_run
    rw [← hmm]
    have e30 : (BitVec.ofNat 64 gluePc).toNat = gluePc := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by decide)
    refine grow_branch FT pool rt H reloc hms henv n ih s hn lo hi hgs hgo h4k hlo hhi hhi48 hal1 hal2
      hal3 hfp hinp hpok hr4 hr48 fs hch hfsp hc8 hfit _
      ⟨⟨"runtime.morestack_noctxt.abi0", rfl⟩, by simp [setReg, regG], ?_, hgo,
        ⟨h4k, hlo, show s.sp.toNat + 8 ≤ hi by omega, hhi48⟩, ⟨hal1, hal2, hal3⟩, ?_,
        ⟨hinp, hpok.of_accessible fun a k w => by rw [hmm, Memory.accessible_writeLE]⟩,
        ⟨⟨gluePc, s.sp.toNat, Arch.arm64.fp FT gluePc s.sp.toNat⟩ :: fs, ?_⟩, ⟨?_, ?_⟩,
        ⟨hCO, hAl⟩, ?_⟩ ?_ ?_ rfl ?_ ?_ ?_ ?_
    · rw [hmm]; exact GStack.writeLE hgs hgo (hinp.sub (by omega) (by omega))
    · show (s.regs 29).toNat = s.sp.toNat - 8
      rw [hfp, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · show Chain Arch.arm64 FT mm hi (BitVec.ofNat 64 gluePc).toNat s.sp.toNat
        (some ((setReg (setReg (setReg s.regs 3 (s.regs 30)) 16
          (BitVec.ofNat 64 (s.mem.readLE ((s.regs 28).toNat + 16) 8))) 30 (BitVec.ofNat 64 gluePc)) 3).toNat) _
      rw [e30]; simpa [setReg_apply] using hchain
    · exact hfit1
    · show 2 * ((hi - s.sp.toNat) + FT.maxspd (BitVec.ofNat 64 gluePc).toNat + stackGuard) ≤ maxstacksize
      rw [e30, hmx]; exact hfit2
    · show H [] _ 0 (rtView rt mm)
      rw [hmm, rtView_writeLE (hPA _ _ (hinp.sub (by omega) (by omega)))]
      simpa [setReg, regG] using hH
    · simp [setReg]; rfl
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · exact hmm
    · show Chain Arch.arm64 FT mm hi (BitVec.ofNat 64 gluePc).toNat s.sp.toNat
        (some ((setReg (setReg (setReg s.regs 3 (s.regs 30)) 16
          (BitVec.ofNat 64 (s.mem.readLE ((s.regs 28).toNat + 16) 8))) 30 (BitVec.ofNat 64 gluePc)) 3).toNat) _
      rw [e30]; simpa [setReg_apply] using hchain

/-- **`SumRec` is correct on a stack of any size, stack growth included** (at every depth of
the recursion). -/
theorem correctness (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (n : BitVec 64) :
    EnsuresGrow Extracted.program reloc Extracted.entry [n] (Pre FT pool rt H)
      (fun _ s' => s'.regs 0 = BitVec.ofNat 64 (sumTo n.toNat)) := by
  intro ret hret s hs hpre
  janus_intro hs
  have hg := gsum FT pool rt H reloc hms henv s (by rw [h_pc]; rfl) hpre
  rw [h_lr] at hg
  refine ((hg.withExit hret.fetch_none fun st hst => hret.notStub st hst).toGrownReturns
    (by have := hret.user; omega)).mono fun s' h => ?_
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h0, _⟩ := h
  rw [h0, h_x0]

/-! ## The theorem is not vacuous -/

namespace Witness

open Janus.Contracts.StackSat

def ret : Nat := 0x200000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The witness frame table: the binary's frame record of `SumRec` (`Extracted.frames`), and the
caller, which stops the walk (like `goexit`). -/
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

theorem laws : FTs.Aligned ∧ FTs.InFrame Arch.arm64 :=
  FrameTable.ofRecs_laws Arch.arm64 Extracted.frames extraT (fun r hr => by
    replace hr := List.mem_singleton.1 hr
    subst hr
    refine ⟨fun m hm => ?_, fun m hm => ?_, rfl, fun x hx => ?_⟩
    · simpa using hm
    · simpa using hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h <;> subst h <;> rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

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

/-- The call state `SumRec(3)` on the small 4 KiB stack of `StackSat`. -/
def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 G0 else if i = 29 then BitVec.ofNat 64 (spw - 8)
      else if i = 30 then BitVec.ofNat 64 ret else if i = 0 then 3#64 else 0,
    sp := BitVec.ofNat 64 spw, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [3#64] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

/-- The first frame does not fit: the prologue grows the stack at once. -/
theorem no_room : ¬ s0.mem.readLE ((s0.regs 28).toNat + 16) 8 < s0.sp.toNat := by
  have hg : (s0.regs 28).toNat = G0 := by decide
  rw [hg, show s0.mem = mem0 from rfl, mem0_desc.2.2, show s0.sp.toNat = spw by decide]
  simp only [stackGuard, spw]; omega

theorem pre : Pre FTs pool rt H s0 := by
  obtain ⟨d1, d2, d3⟩ := mem0_desc
  have hin0 : InRanges G0 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hin8 : InRanges (G0 + 8) 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hg : (s0.regs 28).toNat = G0 := by decide
  have hsp : s0.sp.toNat = spw := by decide
  have h30 : (s0.regs 30).toNat = ret := by decide
  refine ⟨SL, SH, ?_, ?_, by decide, ?_, ?_, by decide, by decide, by decide, ?_, rfl,
    ⟨(SL, SH), by simp [pool], Nat.le_refl _, by decide⟩, ?_, by rw [h30]; decide, by rw [h30]; decide,
    ⟨[⟨ret, spw, spw⟩], ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hg]; exact ⟨by decide, by decide, by simp only [gStackLo, Nat.add_zero]; exact d1, d2, d3⟩
  · rw [hg]; simp [pool, G0, SL, SH, BL, BH]
  · rw [hsp]; decide
  · rw [hsp]; decide
  · rw [hsp]; decide
  · intro r hr
    simp only [pool, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  · rw [hsp, h30]
    have e : Arch.arm64.fp FTs ret spw = spw := by
      show spw + FTs.spdelta ret = spw; rw [show FTs.spdelta ret = 0 from rfl, Nat.add_zero]
    have := Chain.stop (A := Arch.arm64) (FT := FTs) (m := s0.mem) (hi := SH) (pc := ret) (sp := spw)
      (lr0 := none) rfl rfl rfl (by decide) (by rw [e]; decide)
    rw [e] at this; exact this
  · intro f hf; simp at hf; subst hf; left; rw [hsp]
  · rw [hsp]
    simp only [framesCls_cons, framesCls_nil, Bool.or_false]
    have el : FTs.locals ret = [] := rfl
    have ea : FTs.args ret = [] := rfl
    have eo : FTs.objs ret = [] := rfl
    simp [frameCls, el, ea, eo, bitsAt, Arch.varp, Arch.argp, Arch.minLocals]
  · rw [hsp, show (s0.regs 0).toNat = 3 by decide]; simp only [stackGuard, maxstacksize, spw, SH, SL]; omega
  · rw [hg]; refine ⟨rfl, .inl ⟨?_, ?_⟩⟩
    · rw [readLE_rtView hin0]; exact d1
    · rw [readLE_rtView hin8]; exact d2

/-- All hypotheses of `correctness` hold together, for a call whose first frame does not fit. -/
theorem nonvacuous : ∃ (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (ret : Nat) (s : State),
    MorestackContract Extracted.program FT pool rt H reloc ∧ Env FT pool rt ∧
    RetAddr Extracted.program ret ∧ CallSetup (Extracted.program.withExit ret) Extracted.entry [3#64] s ∧
    Pre FT pool rt H s ∧ ¬ s.mem.readLE ((s.regs 28).toNat + 16) 8 < s.sp.toNat :=
  ⟨FTs, pool, rt, H, reloc FTs, ret, s0, contract _ FTs, env, hret, setup, pre, no_room⟩

/-- So the guarantee is reached: from a stack where not even the first frame fits, `SumRec(3)`
grows the stack and returns `6`. -/
theorem returns : GrownReturns (Extracted.program.withExit ret) (reloc FTs) s0
    (fun s' => s'.regs 0 = 6#64) :=
  (correctness FTs pool rt H (reloc FTs) (contract _ FTs) env 3#64 ret hret s0 setup pre).mono
    fun s' h => by rw [h]; rfl

end Witness

end Proof
