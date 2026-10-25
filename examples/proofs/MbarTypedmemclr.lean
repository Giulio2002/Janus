import Extracted

/-!
# `runtime.typedmemclr` meets the `TypedMemclr` contract (write barrier off)

**Guarantee.** For every typed-memory model `M` satisfying its laws, stack bounds with `8 ≤ d'` and
`d' + 48 ≤ d`, and every code at `runtime.memclrNoHeapPointers` meeting `MemclrNoHeapPointers`
with bound `d'`, the machine code of Go 1.26's `runtime.typedmemclr(typ, ptr)` satisfies
`Janus.Contracts.Mem.TypedMemclr … M wb d` for the flag address `wb` the code loads: the
`typ.Size_` bytes at `ptr` become zero.

**What the code does.** A 48-byte frame; it reads `runtime.writeBarrier.enabled` (off), skips the barrier and calls
`memclrNoHeapPointers(ptr, typ.Size_)`. The barrier path is unreachable.

**Assumptions.** `M.Laws` and the callee's `MemclrNoHeapPointers` contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem

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

/-- The return of a typed-memory call, from the final state's fields. -/
theorem tRet_intro {M : MemModel} {d nargs : Nat} {extra : List (Nat × Nat)} {s s' : State}
    {P : Memory → Prop}
    (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18)
    (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid)
    (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr)
    (hf : MemFrame s.mem s'.mem (M.priv ++ calleeStack s d nargs ++ extra)) (he : M.Env s'.mem (s.regs 28))
    (hp : P s'.mem) : TRet M d nargs extra s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.fpsr, s'.mem, ?_, hf, he, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s'
  simp only at hsp hpc hdz htp hfc h18 h28 h29 ⊢
  subst hsp hpc hdz htp hfc
  congr
  funext i
  simp only [Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

theorem envM_of_frame {M : MemModel} (hl : M.Laws) {s : State} {m : Memory} {g : W64} {d n : Nat}
    (he : M.Env s.mem g) (hout : Outside (s.sp.toNat - d) (d + 8 + 8 * n) M.priv)
    (hd1 : d ≤ s.sp.toNat) (hm : MemFrame s.mem m (calleeStack s d n)) : M.Env m g :=
  hl.env_frame _ _ _ he (Agrees.of_memFrame hm fun a ha => by
    have := inRanges_apart ha hout
    simp only [calleeStack, outside_cons, outside_nil, and_true]; omega)

theorem toNat_ofNat_readLE8 (m : Memory) (a : Nat) :
    (BitVec.ofNat 64 (m.readLE a 8)).toNat = m.readLE a 8 := by
  have := m.readLE_lt a 8
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simpa using this)

/-- A byte outside a frame's ranges is unchanged. -/
theorem MemFrame.bytes {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {a : Nat}
    (ho : Outside a 1 rs) : m'.bytes a = m.bytes a := by
  have := h.readLE a 1 ho
  simp only [Memory.readLE] at this
  exact BitVec.eq_of_toNat_eq (by omega)

/-- The write-barrier flag word is zero, so its first byte (`enabled`) is. -/
theorem wbOff_byte {m : Memory} {wb : Nat} (h : WriteBarrierOff m wb) : m.readLE wb 1 = 0 := by
  unfold WriteBarrierOff at h
  rw [show 4 = 1 + 3 from rfl, Memory.readLE_add] at h
  omega

/-- The address of `runtime.writeBarrier` (in `.noptrbss`; the extraction warns that it is a
runtime variable outside the extracted code): the target of the `ADRP X27` + `LDRB W4, [X27,
#0x410]` pair at `+0xc`, recomputed from the extracted words. -/
def wb : Nat :=
  adrpLdTarget (Extracted.entry + 0xc) (segWord Extracted.program "runtime.typedmemclr" 3)
    (segWord Extracted.program "runtime.typedmemclr" 4) 0

set_option maxHeartbeats 2000000 in
theorem correctness (impl : List Segment) (M : MemModel) (hl : M.Laws) (d d' : Nat)
    (hd' : 8 ≤ d') (hd : d' + 48 ≤ d)
    (hmc : MemclrNoHeapPointers (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") M d') :
    TypedMemclr (Extracted.program.link impl) Extracted.entry M wb d := by
  intro s hpc ⟨hpre, ⟨ht1, ht2⟩, ht3, ⟨hD1, hD2, hD3, hD4⟩⟩
  have hpre' := hpre
  obtain ⟨he, hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hout, ⟨hw1, hw2, hw3⟩, hwb, hgo, hgp⟩ := hpre'
  have hg' := hg
  obtain ⟨hg1, hg2, hg3⟩ := hg'
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have hwb1 := wbOff_byte hwb
  janus_eval_nat hwbv : wb
  rw [hwbv] at hw1 hw2 hw3 hwb1
  simp only [typSize] at hD1 hD2 hD3 hD4 ⊢
  have ho1 : Outside (s.sp.toNat - 48) 8 M.priv := hout.of_sub (by omega) (by omega)
  have ho2 : Outside (s.sp.toNat - 56) 8 M.priv := hout.of_sub (by omega) (by omega)
  have hsp : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hmf : MemFrame s.mem ((s.mem.writeLE (s.sp.toNat - 48) 8 (s.regs 30).toNat).writeLE
      (s.sp.toNat - 56) 8 (s.regs 29).toNat) (calleeStack s d 2) :=
    (MemFrame.of_writeLE _ _ (List.mem_cons_self ..) (by simp; omega) (by simp; omega)).writeLE _
      (List.mem_cons_self ..) (by simp; omega) (by simp; omega)
  have hw3' := hw3
  have ht3' := ht3
  have hD3' := hD3
  simp only [calleeStack, outside_cons, outside_nil, and_true] at hw3' ht3' hD3'
  janus_run until [Extracted.program.contractAddr "runtime.memclrNoHeapPointers"]
  have hn := toNat_ofNat_readLE8 s.mem (s.regs 0).toNat
  refine ReachesRet.call hmc rfl ⟨envM_of_frame hl he hout hd1 hmf,
    eqPre_call (F := 48) ⟨hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hgo⟩ (by decide) hd hd' hsp
      (by simp [setReg]) hmf (by simp [setReg]) (by simp [setReg]) (.inr (by decide)),
    hout.of_sub (by rw [hsp]; omega) (by rw [hsp]; omega), ?_⟩ ?_
  · simp only [Dest, setReg_apply, Nat.reduceEqDiff, reduceIte, hn]
    exact ⟨hD1, by rw [hmf.accessible]; exact hD2, sub_win hd hd1 hsp (.inr (by decide)) hD3, hD4⟩
  intro s' hpc' ⟨r, v, fl, fs, m, hs', hfr, henv, hres⟩
  subst hs'
  have hfr0 := hfr
  simp only [setReg_apply, Nat.reduceEqDiff, reduceIte, hn] at hfr0 hres
  simp only [calleeStack, hsp, setReg_apply, Nat.reduceEqDiff, reduceIte, hn] at hfr
  janus_run
  have hF : MemFrame s.mem m (M.priv ++ calleeStack s d 2 ++
      [((s.regs 1).toNat, (s.regs 1).toNat + s.mem.readLE (s.regs 0).toNat 8)]) :=
    hmf.trans hfr0 fun a k h => by
      simp only [outside_append] at h ⊢
      exact ⟨h.1.2, ⟨h.1.1, sub_win hd hd1 hsp (.inr (by decide)) h.1.2⟩, h.2⟩
  exact tRet_intro rfl rfl (by simp [setReg, Map.keepABI]) (by simp [setReg, Map.keepABI])
    (by simp [setReg]) rfl rfl rfl hF (by simpa [setReg] using henv) hres


namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MemSat

/-- `MemSat.memclrCode` (model `M0`) at `A0`, reached from `runtime.memclrNoHeapPointers`'s address by a branch. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.memclrNoHeapPointers"
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := memclrCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model (d : Nat) : MemclrNoHeapPointers (Extracted.program.link implAt) cAddr M0 d := by
  have hA : MemclrNoHeapPointers (Extracted.program.link implAt) A0 M0 d := by
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (memclrNoHeapPointers_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨e, ⟨⟨g1, g2, g3⟩, hc, hgo⟩, hrest⟩ := hpre
  exact hA _ rfl ⟨e, ⟨⟨g1, g2, g3⟩, hc, hgo⟩, hrest⟩

/-- The witness memory: `EqHashModel.wmem` with a readable 4-byte region at the write-barrier flag
address `wb` (the code's `runtime.writeBarrier`, zero: off). -/
def wmemW : Memory := ⟨EqHashModel.wmem.bytes, EqHashModel.wmem.regions ++ [⟨wb, 4, false⟩]⟩

/-- The witness call state: `MemSat.wstate` at the entry with memory `wmemW`, and `typedmemclr(TD, DST)` (clear an 8-byte `TD`-value at `DST`). -/
def r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 TD else if i = 1 then BitVec.ofNat 64 DST else 0
def s0 : State := { MemSat.wstate r with pc := BitVec.ofNat 64 Extracted.entry, mem := wmemW }

theorem pre : TPre M0 wb 64 2 s0 ∧ TypeOK s0.mem (s0.regs 0).toNat ∧ Outside (s0.regs 0).toNat 16 (calleeStack s0 64 2) ∧
    Dest M0 s0 64 2 (s0.regs 1).toNat (typSize s0.mem (s0.regs 0).toNat) := by
  refine ⟨⟨trivial, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    (try simp only [CallOK, Input, Dest, TypeOK, WriteBarrierOff, typSize, calleeStack, M0, outside_cons,
      outside_nil]) <;> decide

/-- All hypotheses of `correctness` hold together (the model `M0`, bounds `d' = 16`, `d = 64`). -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MemModel) (d d' : Nat), M.Laws ∧ 8 ≤ d' ∧
    d' + 48 ≤ d ∧
    MemclrNoHeapPointers (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") M d' ∧
    ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧ (TPre M wb d 2 s ∧ TypeOK s.mem (s.regs 0).toNat ∧ Outside (s.regs 0).toNat 16 (calleeStack s d 2) ∧
    Dest M s d 2 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat)) :=
  ⟨implAt, M0, 64, 16, M0_laws, by decide, by decide, model 16, s0, rfl, pre⟩

/-- `correctness` at `s0`. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (s0.regs 30) s0
    (fun s' => TRet M0 64 2 [((s0.regs 1).toNat, (s0.regs 1).toNat + typSize s0.mem (s0.regs 0).toNat)] s0 s'
      fun m => Zeroed m (s0.regs 1).toNat (typSize s0.mem (s0.regs 0).toNat)) :=
  correctness implAt M0 M0_laws 64 16 (by decide) (by decide) (model 16) s0 rfl pre

end Witness

end Proof
