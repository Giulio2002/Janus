import Janus.Contracts.StackAmd64
import Janus.Contracts.StackSat

/-!
# The amd64 `morestack` contract is satisfiable

The amd64 counterpart of `Janus/Contracts/StackSat.lean`, with the same toy two-slot stack
allocator (`StackSat.G0`, the small slot `[SL, SH)`, the big slot `[BL, BH)`, the readiness `H`,
the memory after the copy `growMem`). Growing the small stack copies its used part
`[RSP + 8, SH)` (from the function's stack pointer `gobuf.sp` up) to the top of the big slot,
adjusting every word the walk's stack maps mark that points into the old stack, and `gogo`
resumes at the glue `[RSP]` with `RSP` moved, `RBP` adjusted and `RDX = 0`.

* `contract64`: the toy runtime meets `MorestackContract64 p FT pool rt H` for every program
  `p` and frame table `FT`;
* `morestack64_satisfiable`: with a call state `s0` that satisfies `MorestackPre64`.
-/

namespace Janus.Contracts.StackSatAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Stack
  Janus.Contracts Janus.Contracts.Stack Janus.Contracts.StackAmd64
open Janus.Contracts.StackSat (G0 SL SH BL BH pool rt H descMem growMem descMem_readLE growMem_desc
  growMem_out movedByte)

/-- The frames the runtime adjusts: the walk from `(gobuf.pc, gobuf.sp) = ([RSP], RSP + 8)`. -/
noncomputable def clsFrames (FT : FrameTable) (s : State) : List Frame :=
  haveI := Classical.propDecidable
  if h : ∃ fs, Chain Arch.amd64 FT s.mem SH (gluePcOf s) (fspOf s) none fs
  then Classical.choose h else []

/-- The resumed state (`gogo`): at the glue, `RSP` moved, `RBP` adjusted, `RDX = 0`, `X15 = 0`,
the direction flag clear; the memory with `[RSP + 8, SH)` moved to the top of the big slot. -/
noncomputable def growState (FT : FrameTable) (s : State) : State :=
  { s with
    regs := fun r => if r = 4 then BitVec.ofNat 64 (fspOf s + BH - SH)
      else if r = 5 then BitVec.ofNat 64 (adjustWord SL SH BH (s.regs 5).toNat)
      else if r = 2 then 0 else s.regs r,
    rip := retAddrOf s, xmm := fun i => if i = 15 then 0 else s.xmm i, df := false,
    mem := growMem (framesCls Arch.amd64 FT (clsFrames FT s)) s.mem (fspOf s + 8) }

/-- The toy runtime's growth relation. -/
def reloc (FT : FrameTable) (s s' : State) : Prop := s' = growState FT s

/-- **The toy runtime meets the amd64 `morestack` contract**, for every program and frame
table. -/
theorem contract64 (p : Amd64.Program) (FT : FrameTable) :
    MorestackContract64 p FT pool rt H (reloc FT) := by
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
  simp only [regSP] at hl2 hl3 ha3
  have hfit := hm.fits
  obtain ⟨rfl, rfl⟩ : lo = SL ∧ hi = SH := by
    rcases hslot with h | ⟨rfl, rfl⟩
    · exact h
    · exfalso; have := hfit.1; simp only [BL, BH, maxstacksize] at this; omega
  refine ⟨growState FT s, BL, BH, rfl, ?_⟩
  have hsp := (s.regs 4).isLt
  have hfsp : fspOf s = (s.regs 4).toNat + 8 := rfl
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide,
      ⟨(BL, BH), by simp [pool], Nat.le_refl _, by simp [BL, BH]⟩, .inl (by decide)⟩,
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · have := hfit.2; simp only [maxstacksize, stackGuard, BL, BH, SH] at this ⊢; omega
  · -- the new descriptor
    obtain ⟨d1, d2, d3⟩ := descMem_readLE s.mem
    refine ⟨by decide, ?_, ?_, ?_, ?_⟩
    · show (growMem _ s.mem _).accessible G0 24 false = true
      exact hgacc
    · simp only [gStackLo, Nat.add_zero]
      show (growMem _ s.mem _).readLE G0 8 = BL
      have := growMem_desc (framesCls Arch.amd64 FT (clsFrames FT s)) s.mem (fspOf s + 8) 0 (by decide)
      simp only [Nat.add_zero] at this; rw [this, d1]
    · simp only [gStackHi]
      show (growMem _ s.mem _).readLE (G0 + 8) 8 = BH
      rw [growMem_desc _ _ _ 8 (by decide), d2]
    · simp only [gStackguard0]
      show (growMem _ s.mem _).readLE (G0 + 16) 8 = BL + stackGuard
      rw [growMem_desc _ _ _ 16 (by decide), d3]
  · -- the frames moved along the walk
    intro fs hfs
    have hex : ∃ fs, Chain Arch.amd64 FT s.mem SH (gluePcOf s) (fspOf s) none fs := ⟨fs, hfs⟩
    have hcls : clsFrames FT s = fs := by
      rw [clsFrames, dite_eq_left_of_eq_true (eq_true hex)]; exact Chain.unique (Classical.choose_spec hex) hfs
    show Moved _ pool SL SH BH (fspOf s) [] s.mem
      (growMem (framesCls Arch.amd64 FT (clsFrames FT s)) s.mem (fspOf s + 8))
    rw [hcls, hfsp]
    refine ⟨⟨by omega, by decide, by decide⟩, ⟨by decide, by decide, by omega, by omega⟩, ?_, ?_⟩
    · intro a h1 h2 h3 hc _
      have hrd : (growMem (framesCls Arch.amd64 FT fs) s.mem ((s.regs 4).toNat + 8 + 8)).readLE
          (a + BH - SH) 8 = adjustWord SL SH BH (s.mem.readLE a 8) := by
        rw [show adjustWord SL SH BH (s.mem.readLE a 8) =
            (s.mem.writeLE (a + BH - SH) 8 (adjustWord SL SH BH (s.mem.readLE a 8))).readLE (a + BH - SH) 8 by
          rw [Arm64.Memory.readLE_writeLE_self]
          refine (Nat.mod_eq_of_lt ?_).symm
          have := Arm64.Memory.readLE_lt s.mem a 8
          simp only [adjustWord]; split <;> simp only [SL, SH, BH] at * <;> omega]
        refine Arm64.Memory.readLE_congr fun j hj => ?_
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
    exact growMem_out _ _ _ (by omega) (by omega) (by rw [hfsp]; omega)
  · -- the runtime is ready again: the big slot
    refine ⟨rfl, .inr ⟨?_, ?_⟩⟩
    · rw [readLE_rtView hin0]
      show (growMem (framesCls Arch.amd64 FT (clsFrames FT s)) s.mem (fspOf s + 8)).readLE G0 8 = BL
      have := growMem_desc (framesCls Arch.amd64 FT (clsFrames FT s)) s.mem (fspOf s + 8) 0 (by decide)
      simp only [Nat.add_zero] at this; rw [this, (descMem_readLE s.mem).1]
    · rw [readLE_rtView (hin 8 (by decide))]
      show (growMem (framesCls Arch.amd64 FT (clsFrames FT s)) s.mem (fspOf s + 8)).readLE (G0 + 8) 8 = BH
      rw [growMem_desc _ _ _ 8 (by decide), (descMem_readLE s.mem).2.1]

/-! ## A call state that satisfies the precondition -/

/-- The `morestack_noctxt` stub, the glue after the call, and the caller's return address. -/
def A0 : Nat := 0x100000
def GLUE : Nat := 0x2000
def RET0 : Nat := 0x3000

/-- A program with only the stub. -/
def toyP : Amd64.Program :=
  { segments := [], stubs := [⟨"runtime.morestack_noctxt.abi0", A0, .morestack⟩], exitAddr := 0 }

/-- A frame table with two functions: the one at the glue (no frame yet) and its caller, which
stops the walk. -/
def FT0 : FrameTable :=
  { valid := fun pc => pc == GLUE || pc == RET0, entry := id, spdelta := fun _ => 0,
    maxspd := fun _ => 176, stop := fun pc => pc == RET0, injected := fun _ => false,
    locals := fun _ => [], args := fun _ => [], objs := fun _ => [] }

/-- `RSP` at the stub: 64 bytes below the small slot's top. -/
def sp0 : Nat := SH - 64

/-- Memory: the small slot's descriptor, the glue address at `[RSP]` (pushed by the stub's
`CALL`) and the caller's return address above it, the two slots writable. -/
def mem0 : Memory :=
  { bytes := (((((⟨fun _ => 0, []⟩ : Memory).writeLE G0 8 SL).writeLE (G0 + 8) 8 SH).writeLE
      (G0 + 16) 8 (SL + stackGuard)).writeLE sp0 8 GLUE |>.writeLE (sp0 + 8) 8 RET0).bytes,
    regions := [⟨G0, 24, false⟩, ⟨SL, 4096, true⟩, ⟨BL, 2 ^ 29, true⟩] }

/-- The call state. -/
def s0 : State :=
  { regs := fun i => if i = 14 then BitVec.ofNat 64 G0 else if i = 4 then BitVec.ofNat 64 sp0
      else 0,
    rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem mem0_desc : mem0.readLE G0 8 = SL ∧ mem0.readLE (G0 + 8) 8 = SH ∧
    mem0.readLE (G0 + 16) 8 = SL + stackGuard := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem s0_chain : Chain Arch.amd64 FT0 s0.mem SH (gluePcOf s0) (fspOf s0) none
    [⟨GLUE, sp0 + 8, sp0 + 16⟩, ⟨RET0, sp0 + 16, sp0 + 24⟩] := by
  have eg : gluePcOf s0 = GLUE := by decide
  have esp : fspOf s0 = sp0 + 8 := by decide
  rw [eg, esp]
  have e1 : Arch.amd64.fp FT0 GLUE (sp0 + 8) = sp0 + 16 := rfl
  have e2 : Arch.amd64.fp FT0 RET0 (sp0 + 16) = sp0 + 24 := rfl
  have e3 : Arch.amd64.lrOf s0.mem (sp0 + 8) (sp0 + 16) none = RET0 := by decide
  have := Chain.cons (A := Arch.amd64) (FT := FT0) (m := s0.mem) (hi := SH) (pc := GLUE)
    (sp := sp0 + 8) (lr0 := none) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by
      rw [e1, e3]
      have := Chain.stop (A := Arch.amd64) (FT := FT0) (m := s0.mem) (hi := SH) (pc := RET0)
        (sp := sp0 + 16) (lr0 := none) (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [e2] at this; exact this)
  rw [e1] at this; exact this

theorem pre0 : MorestackPre64 toyP FT0 pool rt H G0 SL SH s0 := by
  obtain ⟨d1, d2, d3⟩ := mem0_desc
  have hin0 : InRanges G0 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hin8 : InRanges (G0 + 8) 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  refine ⟨⟨"runtime.morestack_noctxt.abi0", rfl⟩, by decide,
    ⟨by decide, by decide, by simp only [gStackLo, Nat.add_zero]; exact d1, d2, d3⟩,
    by simp [pool, G0, SL, SH, BL, BH], ⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, ⟨⟨(SL, SH), by simp [pool], Nat.le_refl _, by decide⟩, ?_⟩,
    ⟨_, s0_chain⟩, ⟨by decide, by decide⟩,
    ⟨fun pc hv => ?_, fun _ => rfl⟩, ⟨rfl, .inl ⟨?_, ?_⟩⟩⟩
  · intro r hr
    simp only [pool, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  · simp only [FT0, Bool.or_eq_true, beq_iff_eq] at hv
    rcases hv with rfl | rfl <;> exact ⟨by simp [pool, GLUE, RET0, SL, SH, BL, BH], by decide⟩
  · rw [readLE_rtView hin0]; exact d1
  · rw [readLE_rtView hin8]; exact d2

/-- **The amd64 `morestack` contract is satisfiable**: the toy runtime meets it, and the call
state `s0` satisfies its whole precondition (round 9's SAT row). -/
theorem morestack64_satisfiable : ∃ (p : Amd64.Program) (FT : FrameTable)
    (pool rt : List (Nat × Nat)) (H : RtReady) (reloc : State → State → Prop),
    MorestackContract64 p FT pool rt H reloc ∧ ∃ g lo hi s, MorestackPre64 p FT pool rt H g lo hi s :=
  ⟨toyP, FT0, pool, rt, H, reloc FT0, contract64 toyP FT0, G0, SL, SH, s0, pre0⟩

end Janus.Contracts.StackSatAmd64
