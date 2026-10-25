import Extracted

/-!
# `runtime.memclrHasPointers` meets the `MemclrHasPointers` contract (write barrier off)

**Guarantee.** For every typed-memory model `M` satisfying its laws, every flag address `wb`, stack bounds with
`8 ≤ db`, `db + 48 ≤ d`, `8 ≤ dc`, `dc + 48 ≤ d`, and every code at `runtime.bulkBarrierPreWrite`
and `runtime.memclrNoHeapPointers` meeting `BulkBarrierOff … M wb db` and
`MemclrNoHeapPointers … M dc`, the machine code of Go 1.26's `runtime.memclrHasPointers(ptr, n)`
satisfies `Janus.Contracts.Mem.MemclrHasPointers … M wb d`: the `n` bytes at `ptr` become zero.

**What the code does.** A 48-byte frame; `ptr` and `n` are spilled to the caller's slots (`SP + 8`, `SP + 16`),
`bulkBarrierPreWrite(ptr, 0, n, 0)` is called (with the barrier off it changes only `M.priv` and
its window), both are reloaded and `memclrNoHeapPointers(ptr, n)` is called. The second call's
guard word is outside `M.priv` (`TPre`), so it reads unchanged (`eqPre_call2`). The function reads
no flag itself, so `wb` is universally quantified.

**Assumptions.** `M.Laws` and the callees' `BulkBarrierOff` and `MemclrNoHeapPointers` contracts.
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

/-- `EqPre` at a later call site whose memory has the same accessible ranges and the same guard
word as the entry's (a second call, after the first changed the runtime's memory). -/
theorem eqPre_call2 {s S : State} {d n d' n' F : Nat} (hp : EqPre d n s) (hF : F % 16 = 0)
    (hd : d' + F ≤ d) (hd8 : 8 ≤ d') (hsp : S.sp.toNat = s.sp.toNat - F) (hg : S.regs 28 = s.regs 28)
    (hacc : ∀ a k w, S.mem.accessible a k w = s.mem.accessible a k w)
    (hgd : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48)
    (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) : EqPre d' n' S := by
  obtain ⟨⟨g1, g2, g3⟩, ⟨l1, l2, al, dsp, d8, top, acc⟩, go⟩ := hp
  simp only [regG, stackguard0Offset, stackguard0] at g1 g2 g3
  refine ⟨⟨?_, ?_, ?_⟩, ⟨hlr, hlr', ?_, ?_, hd8, ?_, ?_⟩, sub_win hd dsp hsp hn (by rw [hg]; exact go)⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hacc]; exact g2
  · simp only [stackguard0, regG, stackguard0Offset, hg, hsp, hgd]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hacc]; exact Memory.accessible_mono _ acc (by omega) (by omega)

set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Segment) (M : MemModel) (hl : M.Laws) (wb d db dc : Nat)
    (hdb : 8 ≤ db) (hdb' : db + 48 ≤ d) (hdc : 8 ≤ dc) (hdc' : dc + 48 ≤ d)
    (hbb : BulkBarrierOff (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.bulkBarrierPreWrite") M wb db)
    (hmc : MemclrNoHeapPointers (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") M dc) :
    MemclrHasPointers (Extracted.program.link impl) Extracted.entry M wb d := by
  intro s hpc ⟨hpre, hp8, hn8, ⟨hD1, hD2, hD3, hD4⟩⟩
  have hpre' := hpre
  obtain ⟨he, hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hout, ⟨hw1, hw2, hw3⟩, hwb, hgo, hgp⟩ := hpre'
  have hg' := hg
  obtain ⟨hg1, hg2, hg3⟩ := hg'
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have ho1 : Outside (s.sp.toNat - 48) 8 M.priv := hout.of_sub (by omega) (by omega)
  have ho2 : Outside (s.sp.toNat - 56) 8 M.priv := hout.of_sub (by omega) (by omega)
  have ho3 : Outside (s.sp.toNat + 8) 16 M.priv := hout.of_sub (by omega) (by omega)
  have hsp : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hmf : MemFrame s.mem ((((s.mem.writeLE (s.sp.toNat - 48) 8 (s.regs 30).toNat).writeLE
      (s.sp.toNat - 56) 8 (s.regs 29).toNat).writeLE (s.sp.toNat + 8) 8 (s.regs 0).toNat).writeLE
      (s.sp.toNat + 16) 8 (s.regs 1).toNat) (calleeStack s d 2) :=
    (((MemFrame.of_writeLE _ _ (List.mem_cons_self ..) (by simp; omega) (by simp; omega)).writeLE _
      (List.mem_cons_self ..) (by simp; omega) (by simp; omega)).writeLE _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by simp) (by simp)).writeLE _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by simp) (by simp)
  have hw3' := hw3
  have hD3' := hD3
  simp only [calleeStack, outside_cons, outside_nil, and_true] at hw3' hD3'
  janus_run until [Extracted.program.contractAddr "runtime.bulkBarrierPreWrite"]
  refine ReachesRet.call hbb rfl ?_ ?_
  · have hE : ∀ {S : State}, S.sp.toNat = s.sp.toNat - 48 → S.regs 28 = s.regs 28 →
        MemFrame s.mem S.mem (calleeStack s d 2) → (S.regs 30).toNat % 4 = 0 →
        (S.regs 30).toNat < 2 ^ 48 → EqPre db 4 S := fun h1 h2 h3 h4 h5 =>
      eqPre_call (F := 48) ⟨hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hgo⟩ (by decide) hdb' hdb h1 h2 h3
        h4 h5 (.inr (by decide))
    refine ⟨⟨envM_of_frame hl he hout hd1 hmf,
      (hE (by exact hsp) (by simp [setReg]) (by exact hmf) (by simp [setReg]) (by simp [setReg])).1,
      (hE (by exact hsp) (by simp [setReg]) (by exact hmf) (by simp [setReg]) (by simp [setReg])).2.1,
      hout.of_sub (by rw [hsp]; omega) (by rw [hsp]; omega),
      ⟨hw1, by rw [hmf.accessible]; exact hw2, sub_win hdb' hd1 hsp (.inr (by decide)) hw3⟩,
      by unfold WriteBarrierOff; rw [hmf.readLE _ _ hw3]; exact hwb,
      (hE (by exact hsp) (by simp [setReg]) (by exact hmf) (by simp [setReg]) (by simp [setReg])).2.2,
      by simpa [setReg] using hgp⟩, by simpa [setReg] using hp8, by simp [setReg], by simpa [setReg] using hn8⟩
  intro s1 hpc1 ⟨r1, v1, fl1, fs1, m1, hs1, hfr1, henv1, _⟩
  subst hs1
  have hfr1' := hfr1
  simp only [List.append_nil] at hfr1'
  simp only [List.append_nil, calleeStack, hsp] at hfr1
  janus_run until [Extracted.program.contractAddr "runtime.memclrNoHeapPointers"]
  have hF1 : MemFrame s.mem m1 (M.priv ++ calleeStack s d 2) := hmf.trans hfr1' fun a k h => by
    simp only [outside_append] at h ⊢
    exact ⟨h.2, h.1, sub_win hdb' hd1 hsp (.inr (by decide)) h.2⟩
  have hacc : ∀ a k w, m1.accessible a k w = s.mem.accessible a k w := fun a k w => hF1.accessible a k w
  have hgd : m1.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hF1.readLE _ _ (by simp only [outside_append]; exact ⟨hgp, hgo⟩)
  refine ReachesRet.call hmc rfl ?_ ?_
  · refine ⟨by simpa [setReg, Map.keepABI] using henv1,
      eqPre_call2 (F := 48) ⟨hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hgo⟩ (by decide) hdc' hdc hsp
        (by simp [setReg, Map.keepABI]) hacc hgd (by simp [setReg]) (by simp [setReg]) (.inr (by decide)),
      hout.of_sub (by rw [hsp]; omega) (by rw [hsp]; omega), ?_⟩
    simp only [Dest, setReg_apply, Nat.reduceEqDiff, reduceIte]
    exact ⟨hD1, by rw [hacc]; exact hD2, sub_win hdc' hd1 hsp (.inr (by decide)) hD3, hD4⟩
  intro s2 hpc2 ⟨r2, v2, fl2, fs2, m2, hs2, hfr2, henv2, hres2⟩
  subst hs2
  have hfr2' := hfr2
  simp only [setReg_apply, Nat.reduceEqDiff, reduceIte] at hfr2' hres2
  simp only [calleeStack, hsp, setReg_apply, Nat.reduceEqDiff, reduceIte] at hfr2
  janus_run
  have hF2 : MemFrame s.mem m2 (M.priv ++ calleeStack s d 2 ++
      [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 1).toNat)]) := hF1.trans hfr2' fun a k h => by
    simp only [outside_append] at h ⊢
    exact ⟨h.1, ⟨h.1.1, sub_win hdc' hd1 hsp (.inr (by decide)) h.1.2⟩, h.2⟩
  exact tRet_intro rfl rfl (by simp [setReg, Map.keepABI]) (by simp [setReg, Map.keepABI])
    (by simp [setReg]) rfl rfl rfl hF2 (by simpa [setReg, Map.keepABI] using henv2) hres2


namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MemSat

/-- `MemSat.memclrCode` (model `M0`) at `A0`, reached from `runtime.memclrNoHeapPointers`'s address by a branch. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.memclrNoHeapPointers"
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := memclrCode }

/-- `runtime.bulkBarrierPreWrite` with the barrier off: a `RET`, placed directly at its address. -/
def bAddr : Nat := Extracted.program.contractAddr "runtime.bulkBarrierPreWrite"
def bSeg : Segment := { name := "bulkBarrierPreWrite", base := bAddr, words := bulkBarrierCode }
def implAt : List Segment := [tramp, bSeg, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp, bSeg]).link [model0] := by
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

theorem modelB (wb d : Nat) : BulkBarrierOff (Extracted.program.link implAt) bAddr M0 wb d := by
  rw [show Extracted.program.link implAt =
    { Extracted.program with segments := Extracted.program.segments ++ implAt } from rfl]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _⟩
  janus_eval_nat hC : bAddr
  rw [hC] at hpc
  janus_run
  exact tRet_intro rfl rfl rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) trivial trivial

/-- The witness call state: `MemSat.wstate` at the entry, with `memclrHasPointers(DST, 64)` and
the write-barrier flag `WB` (off). -/
def r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 DST else if i = 1 then 64 else 0
def s0 : State := { MemSat.wstate r with pc := BitVec.ofNat 64 Extracted.entry }

theorem pre : TPre M0 WB 64 2 s0 ∧ (s0.regs 0).toNat % 8 = 0 ∧ (s0.regs 1).toNat % 8 = 0 ∧
    Dest M0 s0 64 2 (s0.regs 0).toNat (s0.regs 1).toNat := by
  refine ⟨⟨trivial, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    (try simp only [CallOK, Input, Dest, WriteBarrierOff, calleeStack, M0, outside_cons, outside_nil]) <;>
    decide

/-- All hypotheses of `correctness` hold together (`M0`, `wb = WB`, `db = dc = 16`, `d = 64`). -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MemModel) (wb d db dc : Nat), M.Laws ∧ 8 ≤ db ∧
    db + 48 ≤ d ∧ 8 ≤ dc ∧ dc + 48 ≤ d ∧
    BulkBarrierOff (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.bulkBarrierPreWrite") M wb db ∧
    MemclrNoHeapPointers (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") M dc ∧
    ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧ (TPre M wb d 2 s ∧ (s.regs 0).toNat % 8 = 0 ∧ (s.regs 1).toNat % 8 = 0 ∧
    Dest M s d 2 (s.regs 0).toNat (s.regs 1).toNat) :=
  ⟨implAt, M0, WB, 64, 16, 16, M0_laws, by decide, by decide, by decide, by decide, modelB WB 16,
    model 16, s0, rfl, pre⟩

/-- `correctness` at `s0`: the 64 bytes at `DST` become zero. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (s0.regs 30) s0
    (fun s' => TRet M0 64 2 [((s0.regs 0).toNat, (s0.regs 0).toNat + (s0.regs 1).toNat)] s0 s'
      fun m => Zeroed m (s0.regs 0).toNat (s0.regs 1).toNat) :=
  correctness implAt M0 M0_laws WB 64 16 16 (by decide) (by decide) (by decide) (by decide)
    (modelB WB 16) (model 16) s0 rfl pre

end Witness

end Proof
