import Extracted

/-!
# `runtime.gcWriteBarrier1` … `8` meet `WbContract`, from the machine code (arm64)

**Guarantee.** For every list `rt` of runtime-owned ranges and every `N = 1 … 8`, the machine code
of Go 1.26's `runtime.gcWriteBarrierN` (`MOVD $8N, R25; JMP gcWriteBarrier<>`, and the shared
body, `runtime/asm_arm64.s`) satisfies `WbContract … (HRoom rt N) N`
(`Janus/Contracts/WriteBarrier.lean`): from every call with `[SP-232, SP)` writable at which the
runtime is ready in the sense of `HRoom` (`g.m`, `m.p` and `p.wbBuf.{next,end}` lie in `rt`, the
buffer has room for `N` pointers, the frame is outside `rt`), it returns to `X30` with `R25` the
address of `8N` fresh, writable, 8-aligned buffer bytes inside `rt`, `R27` (and the flags)
changed, every other general register preserved, and memory changed only in `rt` (the cursor
`p.wbBuf.next`, advanced by `8N`) and its frame.

So the write-barrier contract that the compiler's barrier calls rely on is met by the real
runtime whenever the buffer has room (`HRoom` excludes only the flush, `runtime.wbBufFlush`, left
out as a contract and never reached); `Witness` gives a concrete state meeting the precondition
for every `N` and runs the real `gcWriteBarrier1` from it. The offsets of `g.m`, `m.p` and the
buffer fields are read off the code (`ldrOff`).

**How.** `core_meets` runs the shared body once for `R25 = 8N` (the fast path: the loads, the
compare that does not branch, the store of the new cursor, the restores); each `wbN_meets` runs
the two instructions of its entry and applies it.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
namespace Proof

/-- The unsigned offset of the `LDR X` at word `i` of the barrier's code (`gcWriteBarrier<>`). -/
def ldrOff (i : Nat) : Nat := bits (segWord Extracted.program "gcWriteBarrier" i) 21 10 * 8
def offM : Nat := ldrOff 4
def offP : Nat := ldrOff 5
def offNext : Nat := ldrOff 6
def offEnd : Nat := ldrOff 7

/-- The runtime is ready for `gcWriteBarrierN` (`N = n`) when, in its view `v` of memory, `g.m`,
`m.p` and `p.wbBuf.{next,end}` lie in `rt` (readable; the cursor writable), the buffer has room
for `n` pointers at `next` (writable, in `rt`, 8-aligned), and the barrier's frame `[SP-232, SP)`
is outside `rt`. -/
def HRoom (rt : List (Nat × Nat)) (n : Nat) : RtReady := fun a g sp v =>
  a = [n] ∧
  InRanges (g + offM) 8 rt ∧ v.accessible (g + offM) 8 false = true ∧
  InRanges (v.readLE (g + offM) 8 + offP) 8 rt ∧
  v.accessible (v.readLE (g + offM) 8 + offP) 8 false = true ∧
  InRanges (v.readLE (v.readLE (g + offM) 8 + offP) 8 + offNext) 16 rt ∧
  v.accessible (v.readLE (v.readLE (g + offM) 8 + offP) 8 + offNext) 16 true = true ∧
  InRanges (v.readLE (v.readLE (v.readLE (g + offM) 8 + offP) 8 + offNext) 8) (8 * n) rt ∧
  v.accessible (v.readLE (v.readLE (v.readLE (g + offM) 8 + offP) 8 + offNext) 8) (8 * n) true = true ∧
  v.readLE (v.readLE (v.readLE (g + offM) 8 + offP) 8 + offNext) 8 % 8 = 0 ∧
  v.readLE (v.readLE (v.readLE (g + offM) 8 + offP) 8 + offNext) 8 + 8 * n ≤
    v.readLE (v.readLE (v.readLE (g + offM) 8 + offP) 8 + offEnd) 8 ∧
  v.readLE (v.readLE (v.readLE (g + offM) 8 + offP) 8 + offEnd) 8 ≤ 2 ^ 48 ∧
  Outside (sp - 232) 232 rt

/-- Introduction of `WbContract`'s postcondition. -/
theorem wb_post_intro {rt : List (Nat × Nat)} {n : Nat} {s : State} {r : Nat → W64} {f : Flags}
    {m : Memory} {buf : W64} {junk : Nat → W64} (hr : r = wbRegs s.regs junk buf)
    (hfr : MemFrame s.mem m (rt ++ [(s.sp.toNat - 232, s.sp.toNat - 8)])) (hw : WbSlots rt m buf.toNat n) :
    ∃ (buf : W64) (junk : Nat → W64) (f' : Flags) (v : Nat → BitVec 128) (m' : Memory),
      { s with regs := r, pc := s.regs 30, flags := f, mem := m } =
        { s with regs := wbRegs s.regs junk buf, pc := s.regs 30, flags := f', vregs := v, mem := m' } ∧
      MemFrame s.mem m' (rt ++ [(s.sp.toNat - 232, s.sp.toNat - 8)]) ∧ WbSlots rt m' buf.toNat n :=
  ⟨buf, junk, f, s.vregs, m, by rw [hr], hfr, hw⟩

def core : Nat := segAddr Extracted.program "gcWriteBarrier"

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The shared body `gcWriteBarrier<>`, entered with `R25 = 8·n`. -/
theorem core_meets (rt : List (Nat × Nat)) (n : Nat) (hn1 : 1 ≤ n) (hn8 : n ≤ 8) :
    Tactic.Summary Extracted.program core
      (fun s => CallOK s 232 0 ∧ Ready (HRoom rt n) rt [n] s ∧ s.regs 25 = BitVec.ofNat 64 (8 * n))
      (fun s s' => ∃ (buf : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
      s' = { s with regs := wbRegs s.regs junk buf, pc := s.regs 30, flags := f, vregs := v, mem := m } ∧
      MemFrame s.mem m (rt ++ [(s.sp.toNat - 232, s.sp.toNat - 8)]) ∧ WbSlots rt m buf.toNat n) := by
  rintro s hpc ⟨⟨hra, hrb, hal, hsb, -, hsa, hacc⟩, hH, h25⟩
  obtain ⟨-, hg1, hg2, hm1, hm2, hp1, hp2, hn1, hn2, hn3, hroom, hend, hout⟩ := hH
  janus_eval_nat h_offM : offM
  janus_eval_nat h_offP : offP
  janus_eval_nat h_offN : offNext
  janus_eval_nat h_offE : offEnd
  simp only [h_offM, h_offP, h_offN, h_offE] at *
  rw [readLE_rtView hg1] at hm1 hm2 hp1 hp2 hn1 hn2 hn3 hroom hend
  rw [readLE_rtView hm1] at hp1 hp2 hn1 hn2 hn3 hroom hend
  rw [readLE_rtView (hp1.sub (Nat.le_refl _) (by omega))] at hn1 hn2 hn3 hroom
  rw [readLE_rtView (hp1.sub (by omega) (by omega))] at hroom hend
  simp only [rtView_accessible] at hg2 hm2 hp2 hn2
  have hb1 := Memory.accessible_bound _ hg2
  have hb2 := Memory.accessible_bound _ hm2
  have hb3 := Memory.accessible_bound _ hp2
  have hb4 := Memory.accessible_bound _ hn2
  have hd1 := InRanges.disjoint hg1 hout
  have hd2 := InRanges.disjoint hm1 hout
  have hd3 := InRanges.disjoint hp1 hout
  have hd4 := InRanges.disjoint hn1 hout
  janus_run
  apply wb_post_intro (buf := BitVec.ofNat 64
      (s.mem.readLE (s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 208) 8 + 9552) 8))
    (junk := fun i => if i = 27 then BitVec.ofNat 64
      (s.mem.readLE (s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 208) 8 + 9560) 8) else s.regs i)
  · funext i
    simp only [setReg, wbRegs, BitVec.add_sub_cancel]
    repeat' split
    all_goals first | rfl | (exfalso; omega) | simp_all
  · janus_frame
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨hn1, by omega, ?_, hn3⟩
    simp only [Memory.accessible_writeLE]; exact hn2

theorem rr_mono' {p : Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', h1, h2, h3⟩ := h; exact ⟨k, s', h1, h2, hQ _ h3⟩

theorem wbRegs_setReg25 (r junk : Nat → W64) (v buf : W64) :
    wbRegs (setReg r 25 v) junk buf = wbRegs r junk buf := by
  funext i; simp only [wbRegs, setReg]; split <;> simp_all

set_option hygiene false in
/-- `gcWriteBarrierN`: `R25 = 8·N`, then the shared body (`core_meets`). -/
macro "wb_entry" n:num : tactic => `(tactic| (
  rintro s hpc ⟨hcall, hH⟩
  have h28 := hH
  janus_run until [core]
  refine rr_mono' (core_meets rt $n (by decide) (by decide) _ (by dsimp only; decide) ⟨hcall, hH, ?_⟩) ?_
  · first | rfl | decide | simp [setReg]
  · rintro s' ⟨buf, junk, f, v, m, hs', hfr, hw⟩
    refine ⟨buf, junk, f, v, m, s.excl, s.exclPass, ?_, hfr, hw⟩
    rw [hs']
    simp only [wbRegs_setReg25]
    rfl))

def wb1 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier1"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier1` meets `WbContract`** when the buffer has room. -/
theorem wb1_meets (rt : List (Nat × Nat)) : WbContract Extracted.program wb1 rt 232 (HRoom rt 1) 1 := by
  wb_entry 1

def wb2 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier2"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier2` meets `WbContract`** when the buffer has room. -/
theorem wb2_meets (rt : List (Nat × Nat)) : WbContract Extracted.program wb2 rt 232 (HRoom rt 2) 2 := by
  wb_entry 2

def wb3 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier3"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier3` meets `WbContract`** when the buffer has room. -/
theorem wb3_meets (rt : List (Nat × Nat)) : WbContract Extracted.program wb3 rt 232 (HRoom rt 3) 3 := by
  wb_entry 3

def wb4 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier4"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier4` meets `WbContract`** when the buffer has room. -/
theorem wb4_meets (rt : List (Nat × Nat)) : WbContract Extracted.program wb4 rt 232 (HRoom rt 4) 4 := by
  wb_entry 4

def wb5 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier5"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier5` meets `WbContract`** when the buffer has room. -/
theorem wb5_meets (rt : List (Nat × Nat)) : WbContract Extracted.program wb5 rt 232 (HRoom rt 5) 5 := by
  wb_entry 5

def wb6 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier6"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier6` meets `WbContract`** when the buffer has room. -/
theorem wb6_meets (rt : List (Nat × Nat)) : WbContract Extracted.program wb6 rt 232 (HRoom rt 6) 6 := by
  wb_entry 6

def wb7 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier7"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier7` meets `WbContract`** when the buffer has room. -/
theorem wb7_meets (rt : List (Nat × Nat)) : WbContract Extracted.program wb7 rt 232 (HRoom rt 7) 7 := by
  wb_entry 7

def wb8 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier8"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier8` meets `WbContract`** when the buffer has room. -/
theorem wb8_meets (rt : List (Nat × Nat)) : WbContract Extracted.program wb8 rt 232 (HRoom rt 8) 8 := by
  wb_entry 8

/-- **All eight barriers meet their contracts** (when the buffer has room). -/
theorem correctness (rt : List (Nat × Nat)) :
    WbContract Extracted.program wb1 rt 232 (HRoom rt 1) 1 ∧
    WbContract Extracted.program wb2 rt 232 (HRoom rt 2) 2 ∧
    WbContract Extracted.program wb3 rt 232 (HRoom rt 3) 3 ∧
    WbContract Extracted.program wb4 rt 232 (HRoom rt 4) 4 ∧
    WbContract Extracted.program wb5 rt 232 (HRoom rt 5) 5 ∧
    WbContract Extracted.program wb6 rt 232 (HRoom rt 6) 6 ∧
    WbContract Extracted.program wb7 rt 232 (HRoom rt 7) 7 ∧
    WbContract Extracted.program wb8 rt 232 (HRoom rt 8) 8 :=
  ⟨wb1_meets rt, wb2_meets rt, wb3_meets rt, wb4_meets rt, wb5_meets rt, wb6_meets rt, wb7_meets rt, wb8_meets rt⟩

/-! ## Non-vacuity: a call with room in the buffer -/

namespace Witness

/-- The runtime's area: `g` at `G`, its `m` at `M`, the `p` at `P`, the buffer `[NX, EN)`. -/
def G : Nat := 0x40000
def M : Nat := 0x40100
def P : Nat := 0x41000
def NX : Nat := 0x48000
def EN : Nat := 0x49000
def SP0 : Nat := 0x20000
def rt : List (Nat × Nat) := [(0x40000, 0x50000)]

/-- The words `g.m = M`, `m.p = P`, `p.wbBuf.next = NX`, `p.wbBuf.end = EN`. -/
def words : List (Nat × Nat) := [(G + 48, M), (M + 208, P), (P + 9552, NX), (P + 9560, EN)]

def mem0 : Memory :=
  ⟨fun a => match words.find? (fun w => w.1 ≤ a && a < w.1 + 8) with
      | some w => BitVec.ofNat 8 (w.2 / 256 ^ (a - w.1))
      | none => 0,
    [⟨SP0 - 0x1000, 0x2000, true⟩, ⟨0x40000, 0x10000, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 G else if i = 30 then 0x100000#64 else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 wb1, flags := ⟨false, false, false, false⟩,
    mem := mem0 }

theorem r1 : (rtView rt mem0).readLE (G + 48) 8 = M := by decide
theorem r2 : (rtView rt mem0).readLE (M + 208) 8 = P := by decide
theorem r3 : (rtView rt mem0).readLE (P + 9552) 8 = NX := by decide
theorem r4 : (rtView rt mem0).readLE (P + 9560) 8 = EN := by decide

theorem ready (n : Nat) (hn : n ≤ 8) : Ready (HRoom rt n) rt [n] s0 := by
  janus_eval_nat h_offM : offM
  janus_eval_nat h_offP : offP
  janus_eval_nat h_offN : offNext
  janus_eval_nat h_offE : offEnd
  show HRoom rt n [n] (BitVec.ofNat 64 G).toNat (BitVec.ofNat 64 SP0).toNat (rtView rt mem0)
  simp only [HRoom, h_offM, h_offP, h_offN, h_offE, BitVec.toNat_ofNat, show G % 2 ^ 64 = G from rfl,
    show SP0 % 2 ^ 64 = SP0 from rfl, r1, r2, r3, r4, rtView_accessible]
  have hacc : mem0.accessible 0x40000 0x10000 true = true := by decide
  refine ⟨trivial, ⟨_, List.mem_singleton.2 rfl, by decide, by decide⟩, Memory.accessible_read_of_write _
      (Memory.accessible_mono _ hacc (by decide) (by decide)), ⟨_, List.mem_singleton.2 rfl, by decide, by decide⟩,
    Memory.accessible_read_of_write _ (Memory.accessible_mono _ hacc (by decide) (by decide)),
    ⟨_, List.mem_singleton.2 rfl, by decide, by decide⟩, Memory.accessible_mono _ hacc (by decide) (by decide),
    ⟨_, List.mem_singleton.2 rfl, by simp [NX], by simp [NX]; omega⟩,
    Memory.accessible_mono _ hacc (by simp [NX]) (by simp [NX]; omega), by decide, by simp [NX, EN]; omega,
    by decide, by simp [rt, outside_cons, outside_nil, SP0]⟩

theorem callOK (n : Nat) : CallOK s0 232 0 := by
  have hw : mem0.accessible (SP0 - 0x1000) 0x2000 true = true := by decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    Memory.accessible_mono _ hw (by decide) (by decide)⟩

/-- The real `gcWriteBarrier1` meets its contract for `Witness.rt`, and for every `N = 1 … 8` the
precondition of `gcWriteBarrierN`'s contract, with `HRoom`, holds at the concrete state `s0`, so
the `wbN_meets` are not vacuous. -/
theorem nonvacuous : ∃ (rt : List (Nat × Nat)) (s : State),
    WbContract Extracted.program wb1 rt 232 (HRoom rt 1) 1 ∧
    ∀ n, n ≤ 8 → CallOK s 232 0 ∧ Ready (HRoom rt n) rt [n] s :=
  ⟨rt, s0, wb1_meets rt, fun n hn => ⟨callOK n, ready n hn⟩⟩

/-- From that state (at `gcWriteBarrier1`) the real code returns, with `R25` the reserved slot. -/
theorem returns : ReachesRet Extracted.program (s0.regs 30) s0 fun s' =>
    s'.pc = s0.regs 30 ∧ ∃ buf : W64, s'.regs 25 = buf ∧ WbSlots rt s'.mem buf.toNat 1 :=
  rr_mono' (wb1_meets rt s0 rfl ⟨callOK 1, ready 1 (by decide)⟩) fun s' ⟨buf, junk, f, v, m, hs, _, hw⟩ =>
    ⟨by rw [hs], buf, by rw [hs]; simp [wbRegs], by rw [hs]; exact hw⟩

end Witness

end Proof
