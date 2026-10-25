import Extracted

/-!
# `runtime.memequal_varlen` meets the `MemequalVarlen` contract

**Guarantee.** For all stack bounds with `8 ≤ d'` and `d' ≤ d` and every code at `runtime.memequal`'s address
meeting `Memequal` with bound `d'`, the machine code of Go 1.26's `runtime.memequal_varlen(a, b)`
satisfies `Janus.Contracts.Mem.MemequalVarlen … d`: the low byte of `X0` says whether the `n`
bytes at `a` and `b` agree, `n` the closure's size `8(X26)`.

**What the code does.** `X2 = 8(X26)`; for `n = 0` it returns `true`, otherwise it tail-jumps (`B`) to `memequal` with
its own `SP` and `X30`, so `memequal`'s return is its return. `Memequal` has no spill slots, so
the callee's window `[SP - d', SP - 8)` is inside the caller's.

**Assumptions.** The callee's `Memequal` contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem Janus.Contracts.Hash

namespace Proof

/-! ## Calls from a frame (arm64)

The function pushes its frame record (`X30` at `SP - F`, `X29` at `SP - F - 8`) and calls a
callee with `SP - F`. These lemmas move the contract's precondition at the entry `s` to the call
site `S` (`EqPre`/`HPre` for the callee's bound `d'` with `d' + F ≤ d`), and the callee's frame
back to the caller's. -/

/-- A range inside `rs` and a range outside `rs` are apart. -/
theorem inRanges_apart {a k b j : Nat} {rs : List (Nat × Nat)} (hi : InRanges a k rs)
    (ho : Outside b j rs) : b + j ≤ a ∨ a + k ≤ b := by
  obtain ⟨r, hr, h1, h2⟩ := hi; have := MemFrame.outside_mem ho hr; omega

/-- The callee's window lies inside the caller's. -/
theorem sub_win {s S : State} {d n d' n' F : Nat} (hd : d' + F ≤ d) (hd1 : d ≤ s.sp.toNat)
    (hsp : S.sp.toNat = s.sp.toNat - F) (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) {a k : Nat}
    (h : Outside a k (calleeStack s d n)) : Outside a k (calleeStack S d' n') := by
  simp only [calleeStack, outside_cons, outside_nil, and_true, hsp] at h ⊢
  omega

theorem eqPre_call {s S : State} {d n d' n' F : Nat} (hp : EqPre d n s) (hF : F % 16 = 0)
    (hd : d' + F ≤ d) (hd8 : 8 ≤ d') (hsp : S.sp.toNat = s.sp.toNat - F) (hg : S.regs 28 = s.regs 28)
    (hm : MemFrame s.mem S.mem (calleeStack s d n)) (hlr : (S.regs 30).toNat % 4 = 0)
    (hlr' : (S.regs 30).toNat < 2 ^ 48) (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) : EqPre d' n' S := by
  obtain ⟨⟨g1, g2, g3⟩, ⟨l1, l2, al, dsp, d8, top, acc⟩, go⟩ := hp
  simp only [regG, stackguard0Offset, stackguard0] at g1 g2 g3
  refine ⟨⟨?_, ?_, ?_⟩, ⟨hlr, hlr', ?_, ?_, hd8, ?_, ?_⟩, sub_win hd dsp hsp hn (by rw [hg]; exact go)⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hm.accessible]; exact g2
  · simp only [stackguard0, regG, stackguard0Offset, hg, hsp]
    rw [hm.readLE _ _ go]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hm.accessible]; exact Memory.accessible_mono _ acc (by omega) (by omega)

/-- The callee's frame after the caller's frame pushes is the caller's frame. -/
theorem frame_ret0 {s S : State} {m : Memory} {d n d' n' F : Nat}
    (hd : d' + F ≤ d) (hd1 : d ≤ s.sp.toNat) (hsp : S.sp.toNat = s.sp.toNat - F)
    (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) (hm : MemFrame s.mem S.mem (calleeStack s d n))
    (h2 : MemFrame S.mem m (calleeStack S d' n')) : MemFrame s.mem m (calleeStack s d n) :=
  hm.trans h2 fun a k h => ⟨h, sub_win hd hd1 hsp hn h⟩

theorem toNat_ofNat_readLE8 (m : Memory) (a : Nat) :
    (BitVec.ofNat 64 (m.readLE a 8)).toNat = m.readLE a 8 := by
  have := m.readLE_lt a 8
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simpa using this)

theorem correctness (impl : List Segment) (d d' : Nat) (hd' : 8 ≤ d') (hd : d' ≤ d)
    (hm : Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d') :
    MemequalVarlen (Extracted.program.link impl) Extracted.entry d := by
  intro s hpc ⟨hpre, ⟨hv1, hv2, hv3⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  have hpre' := hpre
  obtain ⟨hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hgo⟩ := hpre'
  simp only [varlenSize] at ha1 ha2 ha3 hb1 hb2 hb3 ⊢
  janus_run until [Extracted.program.contractAddr "runtime.memequal"]
  · refine EqRet.intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
      (MemFrame.refl _ _) ?_
    simp [BoolRes, setReg]
  · refine ReachesRet.call hm rfl ?_ ?_
    refine ⟨eqPre_call (F := 0) hpre (by decide) (by omega) hd' (by simp)
      (by simp [setReg]) (MemFrame.refl _ _) hl1 hl2 (.inl ⟨rfl, by decide⟩), ?_, ?_⟩
    · simp only [Input, setReg_apply, Nat.reduceEqDiff, reduceIte, toNat_ofNat_readLE8]
      exact ⟨ha1, ha2, sub_win (by omega) hd1 (by simp) (.inl ⟨rfl, by decide⟩) ha3⟩
    · simp only [Input, setReg_apply, Nat.reduceEqDiff, reduceIte, toNat_ofNat_readLE8]
      exact ⟨hb1, hb2, sub_win (by omega) hd1 (by simp) (.inl ⟨rfl, by decide⟩) hb3⟩
    intro s' hpc' hq
    refine ReachesRet.done (by simpa [setReg, regLR] using hpc') ?_
    obtain ⟨r, v, fl, fs, m, rfl, hfr, hres⟩ := hq
    refine EqRet.intro rfl (by simp [setReg]) (by simp [setReg, Map.keepABI])
      (by simp [setReg, Map.keepABI]) (by simp [setReg, Map.keepABI]) rfl rfl rfl
      (hfr.mono fun a k h => sub_win (by omega) hd1 (by simp) (.inl ⟨rfl, by decide⟩) h) ?_
    simp only [BoolRes, setReg_apply, Map.keepABI, Nat.reduceEqDiff, reduceIte, toNat_ofNat_readLE8] at hres ⊢
    exact hres


namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MemSat

/-- `MemSat.memequalCode` (a byte loop that writes nothing) at `A0`, reached from
`runtime.memequal`'s address by a branch. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.memequal"
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := memequalCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model (d : Nat) : Memequal (Extracted.program.link implAt) cAddr d := by
  have hA : Memequal (Extracted.program.link implAt) A0 d := by
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (memequal_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨⟨g1, g2, g3⟩, hcall, hgo⟩, i1, i2⟩ := hpre
  exact hA _ rfl ⟨⟨⟨g1, g2, g3⟩, hcall, hgo⟩, i1, i2⟩

/-- The witness call state: `MemSat.wstate` at the entry, with `memequal_varlen(VAL, VAL)` and the closure `VLEN` (size 8) in `X26`. -/
def r : Nat → W64 := fun i => if i = 0 ∨ i = 1 then BitVec.ofNat 64 VAL else if i = 26 then BitVec.ofNat 64 VLEN else 0
def s0 : State := { MemSat.wstate r with pc := BitVec.ofNat 64 Extracted.entry }

theorem pre : EqPre 64 2 s0 ∧ Input s0 64 2 ((s0.regs 26).toNat + 8) 8 ∧
    Input s0 64 2 (s0.regs 0).toNat (varlenSize s0) ∧ Input s0 64 2 (s0.regs 1).toNat (varlenSize s0) := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp only [CallOK, Input, StrInput, strPtr, strLen, varlenSize, calleeStack, outside_cons,
      outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together (bounds `d' = 64`, `d = 64`). -/
theorem nonvacuous : ∃ (impl : List Segment) (d d' : Nat), 8 ≤ d' ∧ d' ≤ d ∧
    Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d' ∧
    ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧ (EqPre d 2 s ∧ Input s d 2 ((s.regs 26).toNat + 8) 8 ∧
    Input s d 2 (s.regs 0).toNat (varlenSize s) ∧ Input s d 2 (s.regs 1).toNat (varlenSize s)) :=
  ⟨implAt, 64, 64, by decide, by decide, model 64, s0, rfl, pre⟩

/-- `correctness` at `s0`. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (s0.regs 30) s0
    (fun s' => EqRet 64 2 s0 s' fun r => BoolRes r (s0.mem.readLE (s0.regs 0).toNat (varlenSize s0) == s0.mem.readLE (s0.regs 1).toNat (varlenSize s0))) :=
  correctness implAt 64 64 (by decide) (by decide) (model 64) s0 rfl pre

end Witness

end Proof
