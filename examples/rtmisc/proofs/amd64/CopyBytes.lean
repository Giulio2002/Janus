import Extracted

/-!
# `CopyBytes(dst, src []byte) int` is `copy(dst, src)` (amd64)

```go
func CopyBytes(dst, src []byte) int { return copy(dst, src) }
```

`runtime.memmove` is the **live** contract `MemmoveLive64` of `Janus/Contracts/Live.lean`, with the
runtime hypothesis `R`; the call is skipped when `dst` and `src` start at the same address. The point of
the example is its **Witness**: the stub runtime that makes the contract satisfiable at
`Extracted.program`'s own contract address is the generic `Janus.Contracts.LiveStubAmd64`
(`LiveStubAmd64.memmoveSeg`, `janus64_live_memmove`).

**Guarantee.** For every runtime `R` satisfying the contract, every live set `L` and call state whose
frame is outside the runtime-owned ranges, whose slices (of at most `2^63 - 1` elements) are readable
(`src`) and writable (`dst`: inside a live object or outside the runtime's ranges), the call returns
`n = min(len dst, len src)`, the `n` bytes at `dst` are those of `src`, the runtime's invariant holds
again for the same `L`, and memory changed only in the frame and the first `n` bytes of `dst`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (dp dl dc sp sl sc : BitVec 64)
    (hm : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R) :
    Ensures (Extracted.program.link impl) Extracted.entry [dp, dl, dc, sp, sl, sc]
      (fun s => StackGuardOK s 4144 ∧ StackWritable s 4144 40 ∧ (s.regs 4).toNat % 8 = 0 ∧ Outside ((s.regs 4).toNat - 4144) 4184 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4144) 4184 ∧
        Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 40)]) ∧
        dl.toNat < 2 ^ 63 ∧ sl.toNat < 2 ^ 63 ∧
        Apart dp.toNat (min sl.toNat dl.toNat) ((s.regs 4).toNat - 4144) 4184 ∧
        Apart sp.toNat (min sl.toNat dl.toNat) ((s.regs 4).toNat - 4144) 4184 ∧
        (dp ≠ sp →
          R.ok (Extracted.program.contractAddr "runtime.memmove")
            [dp.toNat, sp.toNat, min sl.toNat dl.toNat] ∧
          dp.toNat + min sl.toNat dl.toNat ≤ 2 ^ 48 ∧ sp.toNat + min sl.toNat dl.toNat ≤ 2 ^ 48 ∧
          s.mem.accessible dp.toNat (min sl.toNat dl.toNat) true = true ∧
          s.mem.accessible sp.toNat (min sl.toNat dl.toNat) false = true ∧
          (InRanges dp.toNat (min sl.toNat dl.toNat) L ∨
            Outside dp.toNat (min sl.toNat dl.toNat) R.rt)))
      (fun s s' => (s'.regs 0).toNat = min sl.toNat dl.toNat ∧
        Mem.Copied s.mem s'.mem dp.toNat sp.toNat (min sl.toNat dl.toNat) ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s'.mem) ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 40),
          (dp.toNat, dp.toNat + min sl.toNat dl.toNat)])) := by
  intro ret hret s hs ⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hinv, hLs, hdl, hsl, hapd, haps, hdest⟩
  janus64_intro hs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr ⊢
  by_cases hdp : dp = sp
  · subst hdp
    janus64_run
    refine ⟨fun i hi => ?_, RtInv.inv_frame (ws := [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 40)])
      (by janus_frame)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have e : (s.regs 4).toNat + 40 - ((s.regs 4).toNat - 4144) = 4184 := by omega
        simp only [e]; exact hout) hinv, by janus_frame⟩
    refine Janus.MemFrame.bytes (m := s.mem) (rs := [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 40)]) (by janus_frame) ?_
    unfold Apart at hapd
    simp only [Janus.outside_cons, Janus.outside_nil, and_true]
    omega
  · obtain ⟨hok, hb48d, hb48s, haccd, haccs, hd2⟩ := hdest hdp
    have hne : dp.toNat ≠ sp.toNat := fun h => hdp (BitVec.eq_of_toNat_eq h)
    have hdl64 := dp.isLt
    have hsl64 := sp.isLt
    janus64_run calls [hm]
    all_goals try (exfalso; omega)
    unfold Apart at haps
    refine ⟨fun i hi => ?_, by assumption, by janus_frame⟩
    rw [‹Mem.Copied _ _ _ _ _› i hi]
    repeat rw [Arm64.Memory.bytes_writeLE_outside _ (by omega)]

namespace Witness

instance (a n b k : Nat) : Decidable (Apart a n b k) := by unfold Apart; infer_instance

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64
open Janus.Contracts.LiveSat (bump_acc)

def mvA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memmove")
def dp0 : Nat := 0x250000
def src0 : Nat := 0x270000

/-- The stub runtime: generic code, placed at `Extracted.program`'s own contract address. -/
def implAt : List Amd64.Segment := [memmoveSeg mvA 12]

/-- The requests the witness runtime serves: `CopyBytes`'s (12 bytes from `src0` to `dp0`). -/
def ok : Nat → List Nat → Prop := fun a args => a = mvA ∧ args = [dp0, src0, 12]

def R : RtInv := toyR [] ok

def linked : Amd64.Program := Extracted.program.link implAt

theorem addr_mv : Extracted.program.contractAddr "runtime.memmove" = mvA := by decide

theorem hok_mv : ∀ args, ok mvA args → ∃ d sr, args = [d, sr, 12] := fun _ h => ⟨dp0, src0, h.2⟩

theorem model_mv : MemmoveLive64 linked mvA 4096 R := by janus64_live_memmove 12 hok_mv

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

/-- The bump cell holds `HEAP`; the return address `ret = 0x1000` is at `[RSP]`; `dp0` holds `0xff`,
`src0` `0x5a`. -/
def bytes0 (a : Nat) : Arm64.Byte :=
  if a = BUMP + 3 then 0x10 else if a = sp0 + 1 then 0x10 else if dp0 ≤ a ∧ a < dp0 + 16 then 0xff
  else if src0 ≤ a ∧ a < src0 + 16 then 0x5a else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4144, 4184, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨dp0, 0x100, true⟩, ⟨src0, 0x100, false⟩]⟩

/-- `CopyBytes(dst, src)` for two 12-element slices at `dp0` and `src0`. -/
def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 dp0 else if i = 3 then 12 else if i = 1 then 12
      else if i = 7 then BitVec.ofNat 64 src0 else if i = 6 then 12 else if i = 8 then 12
      else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry
    [BitVec.ofNat 64 dp0, 12, 12, BitVec.ofNat 64 src0, 12, 12] s0 :=
  ⟨rfl, by decide, rfl, by decide,
    by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl,
    rfl⟩

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide

theorem inv0 : R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 14).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_)
    (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega),
    if_neg (by simp only [dp0, HEAP] at *; omega), if_neg (by simp only [src0, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : (StackGuardOK s0 4144 ∧ StackWritable s0 4144 40 ∧ (s0.regs 4).toNat % 8 = 0 ∧ Outside ((s0.regs 4).toNat - 4144) 4184 R.rt ∧
        Apart ((s0.regs 14).toNat + 16) 8 ((s0.regs 4).toNat - 4144) 4184 ∧
        Outside ((s0.regs 14).toNat + 16) 8 R.rt ∧
        R.inv 0x400 ([] : List (Nat × Nat)) (s0.regs 14).toNat (view R.rt ([] : List (Nat × Nat)) s0.mem) ∧
        (∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) [((s0.regs 4).toNat - 4144, (s0.regs 4).toNat + 40)]) ∧
        (12 : BitVec 64).toNat < 2 ^ 63 ∧ (12 : BitVec 64).toNat < 2 ^ 63 ∧
        Apart (BitVec.ofNat 64 dp0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) ((s0.regs 4).toNat - 4144) 4184 ∧
        Apart (BitVec.ofNat 64 src0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) ((s0.regs 4).toNat - 4144) 4184 ∧
        (BitVec.ofNat 64 dp0 ≠ BitVec.ofNat 64 src0 →
          R.ok (Extracted.program.contractAddr "runtime.memmove")
            [(BitVec.ofNat 64 dp0).toNat, (BitVec.ofNat 64 src0).toNat, min (12 : BitVec 64).toNat (12 : BitVec 64).toNat] ∧
          (BitVec.ofNat 64 dp0).toNat + min (12 : BitVec 64).toNat (12 : BitVec 64).toNat ≤ 2 ^ 48 ∧
          (BitVec.ofNat 64 src0).toNat + min (12 : BitVec 64).toNat (12 : BitVec 64).toNat ≤ 2 ^ 48 ∧
          s0.mem.accessible (BitVec.ofNat 64 dp0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) true = true ∧
          s0.mem.accessible (BitVec.ofNat 64 src0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) false = true ∧
          (InRanges (BitVec.ofNat 64 dp0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) ([] : List (Nat × Nat)) ∨
            Outside (BitVec.ofNat 64 dp0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) R.rt))) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, ?_, by decide, ?_,
    inv0, fun r hr => absurd hr (by simp), by decide, by decide, by decide, by decide,
    fun _ => ⟨?_, by decide, by decide, by decide, by decide, Or.inr ?_⟩⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_mv]; exact ⟨rfl, rfl⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide

theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (s : Amd64.State),
    MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry
      [BitVec.ofNat 64 dp0, 12, 12, BitVec.ofNat 64 src0, 12, 12] s ∧
    (StackGuardOK s 4144 ∧ StackWritable s 4144 40 ∧ (s.regs 4).toNat % 8 = 0 ∧ Outside ((s.regs 4).toNat - 4144) 4184 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4144) 4184 ∧
        Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 40)]) ∧
        (12 : BitVec 64).toNat < 2 ^ 63 ∧ (12 : BitVec 64).toNat < 2 ^ 63 ∧
        Apart (BitVec.ofNat 64 dp0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) ((s.regs 4).toNat - 4144) 4184 ∧
        Apart (BitVec.ofNat 64 src0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) ((s.regs 4).toNat - 4144) 4184 ∧
        (BitVec.ofNat 64 dp0 ≠ BitVec.ofNat 64 src0 →
          R.ok (Extracted.program.contractAddr "runtime.memmove")
            [(BitVec.ofNat 64 dp0).toNat, (BitVec.ofNat 64 src0).toNat, min (12 : BitVec 64).toNat (12 : BitVec 64).toNat] ∧
          (BitVec.ofNat 64 dp0).toNat + min (12 : BitVec 64).toNat (12 : BitVec 64).toNat ≤ 2 ^ 48 ∧
          (BitVec.ofNat 64 src0).toNat + min (12 : BitVec 64).toNat (12 : BitVec 64).toNat ≤ 2 ^ 48 ∧
          s.mem.accessible (BitVec.ofNat 64 dp0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) true = true ∧
          s.mem.accessible (BitVec.ofNat 64 src0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) false = true ∧
          (InRanges (BitVec.ofNat 64 dp0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) L ∨
            Outside (BitVec.ofNat 64 dp0).toNat (min (12 : BitVec 64).toNat (12 : BitVec 64).toNat) R.rt))) :=
  ⟨implAt, R, 0x400, [], ret, s0, by rw [addr_mv]; exact model_mv, hret, setup, pre⟩

theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 12 ∧ Mem.Copied s0.mem s'.mem dp0 src0 12 :=
  (correctness implAt R 0x400 [] (BitVec.ofNat 64 dp0) 12 12 (BitVec.ofNat 64 src0) 12 12
    (by rw [addr_mv]; exact model_mv) ret hret s0 setup pre).mono fun _ ⟨habi, h0, hc, _⟩ =>
    ⟨habi, by simpa using h0, by simpa [dp0, src0] using hc⟩

end Witness

end Proof
