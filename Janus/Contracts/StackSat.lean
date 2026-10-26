import Janus.Contracts.Stack

/-!
# The `morestack` contract is satisfiable (arm64)

`MorestackContract` (`Janus/Contracts/Stack.lean`) is a claim about every state at a prologue's
`morestack` call that satisfies `MorestackPre`. This file shows it is not vacuous (round 9's SAT
row): a runtime that meets it for **every** program and **every** frame table, and a call state
that satisfies the whole precondition.

The runtime is a toy two-slot stack allocator, not the Go runtime: goroutine `G0`'s stack is either
the 4 KiB small slot `[SL, SH)` or the 512 MiB big slot `[BL, BH)` (the readiness predicate `H`
says which: it reads `g.stack` in the runtime-owned memory `rt`, `G0`'s descriptor). Growing the
small stack moves it to the big slot exactly as `copystack` does — the frames of the walk are
copied, every word the stack maps mark that points into the old stack is shifted by
`BH - SH` (`adjustWord`), every other byte copied — and writes the new `g.stack` and
`g.stackguard0`. Growing the big stack is not asked for: `MorestackPre`'s size bound
(`2 · (hi - lo) ≤ maxstacksize`) excludes it, as `newstack` throws `stack overflow` there.

* `contract`: the toy runtime (`reloc FT`) meets `MorestackContract p FT pool rt H` for every
  program `p` and frame table `FT`;
* `morestack_satisfiable`: with a call state `s0` that satisfies `MorestackPre`.

The examples' non-vacuity witnesses (`examples/proofs/BigLocal.lean`, `Proof.Witness`) reuse the
toy runtime for the real binary's `morestack` stub.
-/

namespace Janus.Contracts.StackSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Stack Janus.Contracts
  Janus.Contracts.Stack

/-! ## The toy stack allocator -/

/-- The goroutine's descriptor. -/
def G0 : Nat := 0x50000
/-- The small slot `[SL, SH)` (4 KiB) and the big slot `[BL, BH)` (512 MiB). -/
def SL : Nat := 2 ^ 40
def SH : Nat := 2 ^ 40 + 4096
def BL : Nat := 2 ^ 41
def BH : Nat := 2 ^ 41 + 2 ^ 29

/-- The stack pools: the two slots. -/
def pool : List (Nat × Nat) := [(SL, SH), (BL, BH)]
/-- The runtime-owned memory: the goroutine's stack descriptor. -/
def rt : List (Nat × Nat) := [(G0, G0 + 24)]

/-- The runtime is ready for a growth: the goroutine is `G0` and its stack is one of the slots. -/
def H : RtReady := fun _ g _ v => g = G0 ∧
  ((v.readLE g 8 = SL ∧ v.readLE (g + 8) 8 = SH) ∨ (v.readLE g 8 = BL ∧ v.readLE (g + 8) 8 = BH))

/-- The frames the runtime adjusts: the unwinder's walk from the call state, when the stack
unwinds. -/
noncomputable def clsFrames (FT : FrameTable) (s : State) : List Frame :=
  haveI := Classical.propDecidable
  if h : ∃ fs, Chain Arch.arm64 FT s.mem SH (s.regs 30).toNat s.sp.toNat (some (s.regs 3).toNat) fs
  then Classical.choose h else []

/-- The big slot's descriptor written over `m`: `stack.lo`, `stack.hi`, `stackguard0`. -/
def descMem (m : Memory) : Memory :=
  ((m.writeLE G0 8 BL).writeLE (G0 + 8) 8 BH).writeLE (G0 + 16) 8 (BL + stackGuard)

/-- The byte of the new stack that holds the old stack's byte `a`: a pointer word is adjusted,
every other byte copied. -/
noncomputable def movedByte (cls : Nat → Bool) (m : Memory) (a : Nat) : Byte :=
  if cls (a - a % 8) then
    (m.writeLE (a - a % 8 + BH - SH) 8 (adjustWord SL SH BH (m.readLE (a - a % 8) 8))).bytes (a + BH - SH)
  else m.bytes a

/-- The memory after the copy: the descriptor rewritten, `[sp - 8, SH)` moved to `[sp - 8 + BH - SH, BH)`,
everything else (the regions included) unchanged. -/
noncomputable def growMem (cls : Nat → Bool) (m : Memory) (sp : Nat) : Memory :=
  { bytes := fun a' => if G0 ≤ a' ∧ a' < G0 + 24 then (descMem m).bytes a'
      else if sp - 8 + BH - SH ≤ a' ∧ a' < BH then movedByte cls m (a' + SH - BH)
      else m.bytes a',
    regions := m.regions }

/-- The resumed state (`gogo`): `SP`, `X29` moved, `X30 := X3`, `X26 := 0`, at the glue `X30`. -/
noncomputable def growState (FT : FrameTable) (s : State) : State :=
  { s with
    regs := fun r => if r = 29 then BitVec.ofNat 64 ((s.regs 29).toNat + BH - SH)
      else if r = 30 then s.regs 3 else if r = 26 then 0 else s.regs r,
    sp := BitVec.ofNat 64 (s.sp.toNat + BH - SH), pc := s.regs 30,
    mem := growMem (moveCls FT s.sp.toNat (clsFrames FT s)) s.mem s.sp.toNat }

/-- The toy runtime's growth relation. -/
def reloc (FT : FrameTable) (s s' : State) : Prop := s' = growState FT s

/-! ## It meets the contract -/

theorem descMem_readLE (m : Memory) :
    (descMem m).readLE G0 8 = BL ∧ (descMem m).readLE (G0 + 8) 8 = BH ∧
      (descMem m).readLE (G0 + 16) 8 = BL + stackGuard := by
  simp only [descMem]
  refine ⟨?_, ?_, ?_⟩
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp [G0]), Memory.readLE_writeLE_of_disjoint _ _ (by simp [G0]),
      Memory.readLE_writeLE_self]; decide
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp [G0]), Memory.readLE_writeLE_self]; decide
  · rw [Memory.readLE_writeLE_self]; decide

theorem growMem_desc (cls : Nat → Bool) (m : Memory) (sp : Nat) (k : Nat) (hk : k + 8 ≤ 24) :
    (growMem cls m sp).readLE (G0 + k) 8 = (descMem m).readLE (G0 + k) 8 :=
  Memory.readLE_congr fun j hj => by
    simp only [growMem]; rw [if_pos (by omega)]

theorem growMem_out (cls : Nat → Bool) (m : Memory) (sp : Nat) {a n : Nat}
    (h1 : a + n ≤ G0 ∨ G0 + 24 ≤ a) (h2 : a + n ≤ BL ∨ BH ≤ a) (hsp : SL + 8 ≤ sp) :
    (growMem cls m sp).readLE a n = m.readLE a n :=
  Memory.readLE_congr fun j hj => by
    simp only [growMem]
    rw [if_neg (by omega), if_neg (by simp only [SL, SH, BL, BH] at *; omega)]

/-- **The toy runtime meets the `morestack` contract**, for every program and frame table. -/
theorem contract (p : Program) (FT : FrameTable) : MorestackContract p FT pool rt H (reloc FT) := by
  intro g lo hi s hm
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hm.gstack
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero] at hglo hghi hgg
  obtain ⟨hgG, hslot⟩ := hm.ready
  have hgreg := hm.greg
  subst hgG
  have hin : ∀ k, k + 8 ≤ 24 → InRanges (G0 + k) 8 rt := fun k hk =>
    ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp; omega⟩
  have hin0 : InRanges G0 8 rt := by simpa using hin 0 (by decide)
  rw [readLE_rtView hin0, readLE_rtView (hin 8 (by decide))] at hslot
  rw [hglo, hghi] at hslot
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hm.low
  obtain ⟨ha1, ha2, ha3⟩ := hm.aligned
  have hfit := hm.fits
  obtain ⟨rfl, rfl⟩ : lo = SL ∧ hi = SH := by
    rcases hslot with h | ⟨rfl, rfl⟩
    · exact h
    · exfalso; have := hfit.1; simp only [BL, BH, maxstacksize] at this; omega
  refine ⟨growState FT s, BL, BH, rfl, ?_⟩
  have hsp := s.sp.isLt
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide,
      ⟨(BL, BH), by simp [pool], Nat.le_refl _, by simp [BL, BH]⟩, .inl (by decide)⟩,
    ?_, rfl, rfl, ?_, ?_, ?_, ?_, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · have := hfit.2; simp only [maxstacksize, stackGuard, BL, BH, SH] at this ⊢; omega
  · intro i hi; subst hi; simp [growState, regFP]
  · simp [growState, regLR]
  · simp [growState, regG, regPlatform]
  · simp [growState, regClosure]
  · -- the new descriptor
    obtain ⟨d1, d2, d3⟩ := descMem_readLE s.mem
    refine ⟨by decide, ?_, ?_, ?_, ?_⟩
    · show (growMem _ s.mem _).accessible G0 24 false = true
      exact hgacc
    · simp only [gStackLo, Nat.add_zero]
      show (growMem _ s.mem _).readLE G0 8 = BL
      have := growMem_desc (moveCls FT s.sp.toNat (clsFrames FT s)) s.mem s.sp.toNat 0 (by decide)
      simp only [Nat.add_zero] at this; rw [this, d1]
    · simp only [gStackHi]
      show (growMem _ s.mem _).readLE (G0 + 8) 8 = BH
      rw [growMem_desc _ _ _ 8 (by decide), d2]
    · simp only [gStackguard0]
      show (growMem _ s.mem _).readLE (G0 + 16) 8 = BL + stackGuard
      rw [growMem_desc _ _ _ 16 (by decide), d3]
  · -- the frames moved along the walk
    intro fs hfs
    have hex : ∃ fs, Chain Arch.arm64 FT s.mem SH (s.regs 30).toNat s.sp.toNat (some (s.regs 3).toNat) fs :=
      ⟨fs, hfs⟩
    have hcls : clsFrames FT s = fs := by
      simp only [clsFrames, dif_pos hex]; exact Chain.unique (Classical.choose_spec hex) hfs
    show Moved _ pool SL SH BH (s.sp.toNat - 8) [] s.mem
      (growMem (moveCls FT s.sp.toNat (clsFrames FT s)) s.mem s.sp.toNat)
    rw [hcls]
    refine ⟨⟨by omega, by decide, by decide⟩, ⟨by decide, by decide, by omega, by omega⟩, ?_, ?_⟩
    · intro a h1 h2 h3 hc _
      have hrd : (growMem (moveCls FT s.sp.toNat fs) s.mem s.sp.toNat).readLE (a + BH - SH) 8 =
          adjustWord SL SH BH (s.mem.readLE a 8) := by
        rw [show adjustWord SL SH BH (s.mem.readLE a 8) =
            (s.mem.writeLE (a + BH - SH) 8 (adjustWord SL SH BH (s.mem.readLE a 8))).readLE (a + BH - SH) 8 by
          rw [Memory.readLE_writeLE_self]
          refine (Nat.mod_eq_of_lt ?_).symm
          have := Memory.readLE_lt s.mem a 8
          simp only [adjustWord]; split <;> simp only [SL, SH, BH] at * <;> omega]
        refine Memory.readLE_congr fun j hj => ?_
        simp only [growMem]
        rw [if_neg (by simp only [G0, SL, SH, BH] at *; omega),
          if_pos (by simp only [SH, BH] at *; omega)]
        simp only [movedByte]
        rw [show a + BH - SH + j + SH - BH = a + j by simp only [SH, BH] at *; omega,
          show a + j - (a + j) % 8 = a by omega, if_pos hc,
          show a + j + BH - SH = a + BH - SH + j by simp only [SH, BH] at *; omega]
      refine ⟨fun hl hh => ?_, fun hout => ?_⟩
      · rw [hrd]; simp only [adjustWord]; rw [if_pos ⟨hl, hh⟩]
      · rw [hrd]; simp only [adjustWord]
        have := MemFrame.outside_mem hout (show (SL, SH) ∈ pool by simp [pool])
        rw [if_neg (by simp only at this; omega)]
    · intro a h1 h2 hc _
      simp only [growMem]
      rw [if_neg (by simp only [G0, SL, SH, BH] at *; omega),
        if_pos (by simp only [SH, BH] at *; omega)]
      simp only [movedByte]
      rw [show a + BH - SH + SH - BH = a by simp only [SH, BH] at *; omega, if_neg (by simp [hc])]
  · -- nothing else changed
    refine ⟨fun a n hout => ?_, fun _ _ _ => rfl⟩
    simp only [pool, rt, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at hout
    exact growMem_out _ _ _ (by omega) (by omega) (by omega)
  · -- the runtime is ready again: the big slot
    refine ⟨rfl, .inr ⟨?_, ?_⟩⟩
    · rw [readLE_rtView hin0]
      show (growMem (moveCls FT s.sp.toNat (clsFrames FT s)) s.mem s.sp.toNat).readLE G0 8 = BL
      have := growMem_desc (moveCls FT s.sp.toNat (clsFrames FT s)) s.mem s.sp.toNat 0 (by decide)
      simp only [Nat.add_zero] at this; rw [this, (descMem_readLE s.mem).1]
    · rw [readLE_rtView (hin 8 (by decide))]
      show (growMem (moveCls FT s.sp.toNat (clsFrames FT s)) s.mem s.sp.toNat).readLE (G0 + 8) 8 = BH
      rw [growMem_desc _ _ _ 8 (by decide), (descMem_readLE s.mem).2.1]

/-! ## A call state that satisfies the precondition -/

/-- The `morestack_noctxt` stub, the glue after the call, and the caller's return address. -/
def A0 : Nat := 0x100000
def GLUE : Nat := 0x2000
def RET0 : Nat := 0x3000

/-- A program with only the stub. -/
def toyP : Program :=
  { segments := [], stubs := [⟨"runtime.morestack_noctxt.abi0", A0, .morestack⟩], exitAddr := 0 }

/-- A frame table with two functions: the one at the glue (no frame yet) and its caller, which
stops the walk (like `goexit`). -/
def FT0 : FrameTable :=
  { valid := fun pc => pc == GLUE || pc == RET0, entry := id, spdelta := fun _ => 0,
    maxspd := fun _ => 176, stop := fun pc => pc == RET0, injected := fun _ => false,
    locals := fun _ => [], args := fun _ => [], objs := fun _ => [] }

/-- The stack pointer at the call: 64 bytes below the small slot's top. -/
def sp0 : Nat := SH - 64

/-- Memory: the descriptor of the small slot, the two slots writable. -/
def mem0 : Memory :=
  { bytes := (((⟨fun _ => 0, []⟩ : Memory).writeLE G0 8 SL).writeLE (G0 + 8) 8 SH).writeLE
      (G0 + 16) 8 (SL + stackGuard) |>.bytes,
    regions := [⟨G0, 24, false⟩, ⟨SL, 4096, true⟩, ⟨BL, 2 ^ 29, true⟩] }

/-- The call state. -/
def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 G0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 GLUE else if i = 3 then BitVec.ofNat 64 RET0 else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := mem0 }

theorem mem0_desc : mem0.readLE G0 8 = SL ∧ mem0.readLE (G0 + 8) 8 = SH ∧
    mem0.readLE (G0 + 16) 8 = SL + stackGuard := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- No word outside the pools and the descriptor points into a pool: the memory is zero there. -/
theorem mem0_noptr : NoStackPtr mem0 pool rt := by
  intro a ha
  simp only [pool, rt, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ha
  have e : mem0.readLE a 8 = ((((⟨fun _ => 0, []⟩ : Memory).writeLE G0 8 SL).writeLE (G0 + 8) 8 SH).writeLE
      (G0 + 16) 8 (SL + stackGuard)).readLE a 8 := Memory.readLE_congr fun _ _ => rfl
  rw [e, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Memory.readLE_writeLE_of_disjoint _ _ (by omega), readLE_zeros]
  simp only [pool, outside_cons, outside_nil, and_true]; decide

theorem s0_chain : Chain Arch.arm64 FT0 s0.mem SH (s0.regs 30).toNat s0.sp.toNat
    (some (s0.regs 3).toNat) [⟨GLUE, sp0, sp0⟩, ⟨RET0, sp0, sp0⟩] := by
  have e30 : (s0.regs 30).toNat = GLUE := by decide
  have e3 : (s0.regs 3).toNat = RET0 := by decide
  have esp : s0.sp.toNat = sp0 := by decide
  rw [e30, e3, esp]
  exact .cons (by decide) (by decide) (by decide) (by decide) (by decide)
    (.stop (by decide) (by decide) (by decide) (by decide) (by decide))

theorem pre0 : MorestackPre toyP FT0 pool rt H G0 SL SH s0 := by
  obtain ⟨d1, d2, d3⟩ := mem0_desc
  have hin0 : InRanges G0 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hin8 : InRanges (G0 + 8) 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  refine ⟨⟨"runtime.morestack_noctxt.abi0", rfl⟩, by decide,
    ⟨by decide, by decide, by simp only [gStackLo, Nat.add_zero]; exact d1, d2, d3⟩,
    by simp [pool, G0, SL, SH, BL, BH], ⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by decide, ⟨⟨(SL, SH), by simp [pool], Nat.le_refl _, by decide⟩, ?_⟩,
    ⟨_, s0_chain⟩, ⟨by decide, by decide⟩,
    ⟨fun pc hv => ?_, fun _ => rfl⟩, ⟨rfl, .inl ⟨?_, ?_⟩⟩, mem0_noptr⟩
  · intro r hr
    simp only [pool, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  · simp only [FT0, Bool.or_eq_true, beq_iff_eq] at hv
    rcases hv with rfl | rfl <;> exact ⟨by simp [pool, GLUE, RET0, SL, SH, BL, BH], by decide⟩
  · rw [readLE_rtView hin0]; exact d1
  · rw [readLE_rtView hin8]; exact d2

/-- **The `morestack` contract is satisfiable**: the toy runtime meets it, and the call state `s0`
satisfies its whole precondition (round 9's SAT row). -/
theorem morestack_satisfiable : ∃ (p : Program) (FT : FrameTable) (pool rt : List (Nat × Nat))
    (H : RtReady) (reloc : State → State → Prop), MorestackContract p FT pool rt H reloc ∧
    ∃ g lo hi s, MorestackPre p FT pool rt H g lo hi s :=
  ⟨toyP, FT0, pool, rt, H, reloc FT0, contract toyP FT0, G0, SL, SH, s0, pre0⟩

end Janus.Contracts.StackSat
