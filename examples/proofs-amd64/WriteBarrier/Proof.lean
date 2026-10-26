import Janus
import Extracted

/-!
# `runtime.gcWriteBarrier1` … `8` meet `WbContract64`, from the machine code (amd64)

**Guarantee.** As for arm64 (`examples/proofs/WriteBarrier.lean`): for every `rt` and
`N = 1 … 8`, Go 1.26's `runtime.gcWriteBarrierN` (`MOVL $8N, R11; JMP gcWriteBarrier<>`,
`runtime/asm_amd64.s`) satisfies `WbContract64 … (HRoom rt N) N`
(`Janus/Contracts/WriteBarrier.lean`): from every call with `[RSP-120, RSP+8)` writable at which
the P's buffer has room for `N` pointers (`HRoom`), it returns with `RSP + 8`, `R11` the address
of `8N` fresh, writable, 8-aligned buffer bytes in `rt`, every other general register (`R12`,
`R13` restored from its frame) unchanged, and memory changed only in `rt` (the cursor) and its
frame. The flush `wbBufFlush` stays out as a contract and is never reached. `Witness` gives a
concrete state for every `N` and runs the real `gcWriteBarrier1` from it.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
namespace Proof

/-- The offsets of `g.m`, `m.p`, `p.wbBuf.next` and `p.wbBuf.end` (Go 1.26, as the barrier's code
loads them; the proof below checks them against the code). -/
def offM : Nat := 0x30
def offP : Nat := 0xd0
def offNext : Nat := 0x2550
def offEnd : Nat := 0x2558

/-- The runtime is ready for `gcWriteBarrierN` (`N = n`, amd64): as on arm64, with the barrier's
frame `[RSP-120, RSP)` outside `rt`. -/
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
  Outside (sp - 120) 128 rt

/-- Introduction of `WbContract64`'s postcondition. -/
theorem wb64_post_intro {rt : List (Nat × Nat)} {n : Nat} {s : State} {r : Nat → W64} {f : Flags}
    {m : Arm64.Memory} {buf : W64}
    (hr : r = fun i => if i = 4 then s.regs 4 + 8#64 else if i = 11 then buf else s.regs i)
    (hfr : MemFrame s.mem m (rt ++ [((s.regs 4).toNat - 120, (s.regs 4).toNat)]))
    (hw : WbSlots rt m buf.toNat n) :
    ∃ (buf : W64) (f' : Flags) (x yh : Nat → BitVec 128) (m' : Arm64.Memory)
      (zh : Nat → BitVec 256) (kr : Nat → W64),
      { s with regs := r, rip := retAddrOf s, flags := f, mem := m } =
        { s with regs := fun i => if i = 4 then s.regs 4 + 8#64 else if i = 11 then buf else s.regs i,
                 rip := retAddrOf s, flags := f', xmm := fun i => if i = 15 then s.xmm 15 else x i,
                 ymmHi := yh, mem := m', zmmHi := zh, kreg := kr } ∧
      MemFrame s.mem m' (rt ++ [((s.regs 4).toNat - 120, (s.regs 4).toNat)]) ∧ WbSlots rt m' buf.toNat n := by
  refine ⟨buf, f, s.xmm, s.ymmHi, m, s.zmmHi, s.kreg, ?_, hfr, hw⟩
  rw [hr]; congr 1; funext i; split <;> simp_all

def core : Nat := segAddr Extracted.program "gcWriteBarrier"

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem core_meets (rt : List (Nat × Nat)) (n : Nat) (hn1 : 1 ≤ n) (hn8 : n ≤ 8) :
    Janus.Amd64.Tactic.Summary Extracted.program core
      (fun s => CallOK64 s 120 0 ∧ Ready64 (HRoom rt n) rt [n] s ∧ s.regs 11 = BitVec.ofNat 64 (8 * n))
      (fun s s' => ∃ (buf : W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Arm64.Memory),
      s' = { s with regs := fun i => if i = 4 then s.regs 4 + 8#64 else if i = 11 then buf else s.regs i,
                    rip := retAddrOf s, flags := f,
                    xmm := fun i => if i = 15 then s.xmm 15 else x i, ymmHi := yh, mem := m } ∧
      MemFrame s.mem m (rt ++ [((s.regs 4).toNat - 120, (s.regs 4).toNat)]) ∧ WbSlots rt m buf.toNat n) := by
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, hH, h11⟩
  obtain ⟨-, hg1, hg2, hm1, hm2, hp1, hp2, hn1, hn2, hn3, hroom, hend, hout⟩ := hH
  simp only [offM, offP, offNext, offEnd] at *
  rw [readLE_rtView hg1] at hm1 hm2 hp1 hp2 hn1 hn2 hn3 hroom hend
  rw [readLE_rtView hm1] at hp1 hp2 hn1 hn2 hn3 hroom hend
  rw [readLE_rtView (hp1.sub (Nat.le_refl _) (by omega))] at hn1 hn2 hn3 hroom
  rw [readLE_rtView (hp1.sub (by omega) (by omega))] at hroom hend
  simp only [rtView_accessible] at hg2 hm2 hp2 hn2
  have hb1 := Arm64.Memory.accessible_bound _ hg2
  have hb2 := Arm64.Memory.accessible_bound _ hm2
  have hb3 := Arm64.Memory.accessible_bound _ hp2
  have hb4 := Arm64.Memory.accessible_bound _ hn2
  have hd1 := InRanges.disjoint hg1 hout
  have hd2 := InRanges.disjoint hm1 hout
  have hd3 := InRanges.disjoint hp1 hout
  have hd4 := InRanges.disjoint hn1 hout
  janus64_run
  apply wb64_post_intro (s := s) (buf := BitVec.ofNat 64
      (s.mem.readLE (s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 208) 8 + 9552) 8))
  · funext i
    simp only [setRegF, BitVec.add_sub_cancel]
    repeat' split
    all_goals first | rfl | (exfalso; omega) | simp_all
  · janus_frame
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨hn1, by omega, ?_, hn3⟩
    simp only [Arm64.Memory.accessible_writeLE]; exact hn2

theorem rr_mono' {p : Amd64.Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', h1, h2, h3⟩ := h; exact ⟨k, s', h1, h2, hQ _ h3⟩

set_option hygiene false in
macro "wb_entry" n:num : tactic => `(tactic| (
  rintro s hpc ⟨hcall, hH⟩
  janus64_run until [core]
  refine rr_mono' (core_meets rt $n (by decide) (by decide) _ (by dsimp only; decide)
    ⟨by simpa [CallOK64, setRegF] using hcall, by simpa [Ready64, setRegF] using hH, ?_⟩) ?_
  · first | rfl | decide | simp [setRegF]
  · rintro s' ⟨buf, f, x, yh, m, zh, kr, hs, hfr, hw⟩
    refine ⟨buf, f, x, yh, m, zh, kr, ?_, by simpa [setRegF] using hfr, hw⟩
    rw [hs]
    dsimp only
    congr 1
    all_goals first | (funext i; simp only [setRegF]; split <;> simp_all) | simp [retAddrOf, setRegF]))

def wb1 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier1"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier1` meets `WbContract64`** when the buffer has room. -/
theorem wb1_meets (rt : List (Nat × Nat)) : WbContract64 Extracted.program wb1 rt 120 (HRoom rt 1) 1 := by
  wb_entry 1

def wb2 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier2"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier2` meets `WbContract64`** when the buffer has room. -/
theorem wb2_meets (rt : List (Nat × Nat)) : WbContract64 Extracted.program wb2 rt 120 (HRoom rt 2) 2 := by
  wb_entry 2

def wb3 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier3"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier3` meets `WbContract64`** when the buffer has room. -/
theorem wb3_meets (rt : List (Nat × Nat)) : WbContract64 Extracted.program wb3 rt 120 (HRoom rt 3) 3 := by
  wb_entry 3

def wb4 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier4"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier4` meets `WbContract64`** when the buffer has room. -/
theorem wb4_meets (rt : List (Nat × Nat)) : WbContract64 Extracted.program wb4 rt 120 (HRoom rt 4) 4 := by
  wb_entry 4

def wb5 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier5"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier5` meets `WbContract64`** when the buffer has room. -/
theorem wb5_meets (rt : List (Nat × Nat)) : WbContract64 Extracted.program wb5 rt 120 (HRoom rt 5) 5 := by
  wb_entry 5

def wb6 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier6"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier6` meets `WbContract64`** when the buffer has room. -/
theorem wb6_meets (rt : List (Nat × Nat)) : WbContract64 Extracted.program wb6 rt 120 (HRoom rt 6) 6 := by
  wb_entry 6

def wb7 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier7"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier7` meets `WbContract64`** when the buffer has room. -/
theorem wb7_meets (rt : List (Nat × Nat)) : WbContract64 Extracted.program wb7 rt 120 (HRoom rt 7) 7 := by
  wb_entry 7

def wb8 : Nat := segAddr Extracted.program "runtime.gcWriteBarrier8"
set_option maxRecDepth 20000 in
/-- **`runtime.gcWriteBarrier8` meets `WbContract64`** when the buffer has room. -/
theorem wb8_meets (rt : List (Nat × Nat)) : WbContract64 Extracted.program wb8 rt 120 (HRoom rt 8) 8 := by
  wb_entry 8

/-- **All eight barriers meet their contracts** (when the buffer has room). -/
theorem correctness (rt : List (Nat × Nat)) :
    WbContract64 Extracted.program wb1 rt 120 (HRoom rt 1) 1 ∧
    WbContract64 Extracted.program wb2 rt 120 (HRoom rt 2) 2 ∧
    WbContract64 Extracted.program wb3 rt 120 (HRoom rt 3) 3 ∧
    WbContract64 Extracted.program wb4 rt 120 (HRoom rt 4) 4 ∧
    WbContract64 Extracted.program wb5 rt 120 (HRoom rt 5) 5 ∧
    WbContract64 Extracted.program wb6 rt 120 (HRoom rt 6) 6 ∧
    WbContract64 Extracted.program wb7 rt 120 (HRoom rt 7) 7 ∧
    WbContract64 Extracted.program wb8 rt 120 (HRoom rt 8) 8 :=
  ⟨wb1_meets rt, wb2_meets rt, wb3_meets rt, wb4_meets rt, wb5_meets rt, wb6_meets rt, wb7_meets rt, wb8_meets rt⟩

/-! ## Non-vacuity: a call with room in the buffer -/

namespace Witness

def G : Nat := 0x40000
def M : Nat := 0x40100
def P : Nat := 0x41000
def NX : Nat := 0x48000
def EN : Nat := 0x49000
def SP0 : Nat := 0x20000
def rt : List (Nat × Nat) := [(0x40000, 0x50000)]

/-- The words `g.m = M`, `m.p = P`, `p.wbBuf.next = NX`, `p.wbBuf.end = EN`. -/
def words : List (Nat × Nat) := [(G + 0x30, M), (M + 0xd0, P), (P + 0x2550, NX), (P + 0x2558, EN)]

def mem0 : Arm64.Memory :=
  ⟨fun a => match words.find? (fun w => w.1 ≤ a && a < w.1 + 8) with
      | some w => BitVec.ofNat 8 (w.2 / 256 ^ (a - w.1))
      | none => 0,
    [⟨SP0 - 0x1000, 0x2000, true⟩, ⟨0x40000, 0x10000, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G else 0,
    rip := BitVec.ofNat 64 wb1, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0 }

theorem r1 : (rtView rt mem0).readLE (G + 0x30) 8 = M := by decide
theorem r2 : (rtView rt mem0).readLE (M + 0xd0) 8 = P := by decide
theorem r3 : (rtView rt mem0).readLE (P + 0x2550) 8 = NX := by decide
theorem r4 : (rtView rt mem0).readLE (P + 0x2558) 8 = EN := by decide

theorem ready (n : Nat) (hn : n ≤ 8) : Ready64 (HRoom rt n) rt [n] s0 := by
  show HRoom rt n [n] (BitVec.ofNat 64 G).toNat (BitVec.ofNat 64 SP0).toNat (rtView rt mem0)
  simp only [HRoom, offM, offP, offNext, offEnd, BitVec.toNat_ofNat, show G % 2 ^ 64 = G from rfl,
    show SP0 % 2 ^ 64 = SP0 from rfl, r1, r2, r3, r4, rtView_accessible]
  have hacc : mem0.accessible 0x40000 0x10000 true = true := by decide
  refine ⟨trivial, ⟨_, List.mem_singleton.2 rfl, by decide, by decide⟩, Arm64.Memory.accessible_read_of_write _
      (Arm64.Memory.accessible_mono _ hacc (by decide) (by decide)), ⟨_, List.mem_singleton.2 rfl, by decide, by decide⟩,
    Arm64.Memory.accessible_read_of_write _ (Arm64.Memory.accessible_mono _ hacc (by decide) (by decide)),
    ⟨_, List.mem_singleton.2 rfl, by decide, by decide⟩, Arm64.Memory.accessible_mono _ hacc (by decide) (by decide),
    ⟨_, List.mem_singleton.2 rfl, by simp [NX], by simp [NX]; omega⟩,
    Arm64.Memory.accessible_mono _ hacc (by simp [NX]) (by simp [NX]; omega), by decide, by simp [NX, EN]; omega,
    by decide, by simp [rt, outside_cons, outside_nil, SP0]⟩

theorem callOK : CallOK64 s0 120 0 := by
  have hw : mem0.accessible (SP0 - 0x1000) 0x2000 true = true := by decide
  refine ⟨by decide, by decide, by decide, by decide, Arm64.Memory.accessible_mono _ hw (by decide) (by decide)⟩

/-- The real `gcWriteBarrier1` meets its contract for `Witness.rt`, and for every `N = 1 … 8` the
precondition of `gcWriteBarrierN`'s contract, with `HRoom`, holds at the concrete state `s0`. -/
theorem nonvacuous : ∃ (rt : List (Nat × Nat)) (s : State),
    WbContract64 Extracted.program wb1 rt 120 (HRoom rt 1) 1 ∧
    ∀ n, n ≤ 8 → CallOK64 s 120 0 ∧ Ready64 (HRoom rt n) rt [n] s :=
  ⟨rt, s0, wb1_meets rt, fun n hn => ⟨callOK, ready n hn⟩⟩

/-- From that state (at `gcWriteBarrier1`) the real code returns, with `R11` the reserved slot. -/
theorem returns : ReachesRet Extracted.program (retAddrOf s0) s0 fun s' =>
    ∃ buf : W64, s'.regs 11 = buf ∧ WbSlots rt s'.mem buf.toNat 1 :=
  rr_mono' (wb1_meets rt s0 rfl ⟨callOK, ready 1 (by decide)⟩) fun s' ⟨buf, f, x, yh, m, zh, kr, hs, _, hw⟩ =>
    ⟨buf, by rw [hs]; simp, by rw [hs]; exact hw⟩

end Witness

end Proof
