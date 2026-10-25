import Extracted

/-!
# `runtime.strequal` meets the `Strequal` contract

**Guarantee.** For all stack bounds with `8 ≤ d'` and `d' + 16 ≤ d` and every code at `runtime.memequal`'s
address meeting `Memequal` with bound `d'`, the machine code of Go 1.26's `runtime.strequal(a, b)`
satisfies `Janus.Contracts.Mem.Strequal … d`: the low byte of `X0` is `strEq` of the string
headers at `a` and `b` (equal lengths and equal bytes), with the frame of the equality contracts.

**What the code does.** The stack check, a 16-byte frame, `LDP` of both headers; different lengths give `false`
without a call; equal lengths call `memequal(pa, pb, len)` from `SP - 16`. `Memequal` has no
spill slots (`nargs = 0`), so the callee writes only `[SP - 16 - d', SP - 24)`, inside the
caller's window (the 8 spare bytes of the frame are the caller's frame-pointer slot).

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

theorem correctness (impl : List Segment) (d d' : Nat) (hd' : 8 ≤ d') (hd : d' + 16 ≤ d)
    (hm : Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d') :
    Strequal (Extracted.program.link impl) Extracted.entry d := by
  intro s hpc ⟨hpre, ⟨⟨ha1, ha2, ha3⟩, ⟨hp1, hp2, hp3⟩⟩, ⟨⟨hb1, hb2, hb3⟩, ⟨hq1, hq2, hq3⟩⟩⟩
  have hpre' := hpre
  obtain ⟨hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hgo⟩ := hpre'
  have hg' := hg
  obtain ⟨hg1, hg2, hg3⟩ := hg'
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have ha3' := ha3
  have hb3' := hb3
  simp only [calleeStack, outside_cons, outside_nil, and_true] at ha3' hb3'
  simp only [strPtr, strLen] at hp1 hp2 hp3 hq1 hq2 hq3
  have hsp : (s.sp - 16#64).toNat = s.sp.toNat - 16 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hmf : MemFrame s.mem ((s.mem.writeLE (s.sp.toNat - 16) 8 (s.regs 30).toNat).writeLE
      (s.sp.toNat - 24) 8 (s.regs 29).toNat) (calleeStack s d 2) :=
    (MemFrame.of_writeLE _ _ (List.mem_cons_self ..) (by simp; omega) (by simp; omega)).writeLE _
      (List.mem_cons_self ..) (by simp; omega) (by simp; omega)
  janus_run until [Extracted.program.contractAddr "runtime.memequal"]
  · have hlen := hbr
    refine ReachesRet.call hm rfl ⟨eqPre_call (F := 16) hpre (by decide) hd hd' hsp
      (by simp [setReg]) hmf (by simp [setReg]) (by simp [setReg]) (.inr (by decide)), ?_, ?_⟩ ?_
    · simp only [Input, setReg_apply, Nat.reduceEqDiff, reduceIte, toNat_ofNat_readLE8]
      rw [← hbr] at *
      exact ⟨hp1, by rw [hmf.accessible]; exact hp2, sub_win hd hd1 hsp (.inr (by decide)) hp3⟩
    · simp only [Input, setReg_apply, Nat.reduceEqDiff, reduceIte, toNat_ofNat_readLE8]
      exact ⟨hq1, by rw [hmf.accessible]; exact hq2, sub_win hd hd1 hsp (.inr (by decide)) hq3⟩
    intro s' hpc' ⟨r, v, fl, fs, m, hs', hfr, hres⟩
    subst hs'
    have hfr0 := hfr
    simp only [calleeStack, hsp] at hfr
    janus_run
    refine EqRet.intro rfl rfl (by simp [setReg, Map.keepABI]) (by simp [setReg, Map.keepABI])
      (by simp [setReg]) rfl rfl rfl (frame_ret0 hd hd1 hsp (.inr (by decide)) hmf hfr0) ?_
    simp only [setReg_apply, Map.keepABI, Nat.reduceEqDiff, reduceIte, toNat_ofNat_readLE8, BoolRes]
      at hres ⊢
    rw [← hlen] at hres hq3
    rw [hmf.readLE _ _ hp3, hmf.readLE _ _ hq3] at hres
    simp only [or_self, ite_false, strEq, strLen, strPtr, hlen, beq_self_eq_true, Bool.true_and]
    rw [← hlen]; exact hres
  · rename_i hlen _
    refine EqRet.intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
      hmf ?_
    have : (strLen s.mem (s.regs 0).toNat == strLen s.mem (s.regs 1).toNat) = false :=
      beq_false_of_ne (fun h => hlen (by simp only [strLen] at h; rw [h]))
    simp [BoolRes, setReg, strEq, this]


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

/-- The witness call state: `MemSat.wstate` at the entry, with `strequal(STR, STR)` (the string header `STR` = `(VAL, 8)`, twice). -/
def r : Nat → W64 := fun i => if i = 0 ∨ i = 1 then BitVec.ofNat 64 STR else 0
def s0 : State := { MemSat.wstate r with pc := BitVec.ofNat 64 Extracted.entry }

theorem pre : EqPre 64 2 s0 ∧ StrInput s0 64 2 (s0.regs 0).toNat ∧ StrInput s0 64 2 (s0.regs 1).toNat := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [CallOK, Input, StrInput, strPtr, strLen, varlenSize, calleeStack, outside_cons,
      outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together (bounds `d' = 48`, `d = 64`). -/
theorem nonvacuous : ∃ (impl : List Segment) (d d' : Nat), 8 ≤ d' ∧ d' + 16 ≤ d ∧
    Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d' ∧
    ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧ (EqPre d 2 s ∧ StrInput s d 2 (s.regs 0).toNat ∧ StrInput s d 2 (s.regs 1).toNat) :=
  ⟨implAt, 64, 48, by decide, by decide, model 48, s0, rfl, pre⟩

/-- `correctness` at `s0`. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (s0.regs 30) s0
    (fun s' => EqRet 64 2 s0 s' fun r => BoolRes r (strEq s0.mem (s0.regs 0).toNat (s0.regs 1).toNat)) :=
  correctness implAt 64 48 (by decide) (by decide) (model 48) s0 rfl pre

end Witness

end Proof
