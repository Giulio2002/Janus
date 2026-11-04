import Janus.Contracts.LiveStub
import Janus.Contracts.LiveStubMem

/-!
# Live runtime contracts at a program's own addresses: `memmove`, `memclrNoHeapPointers` (arm64)

Stubs for the copy and clear contracts (`MemmoveLive`, `MemclrNoHeapPointersLive`,
`MemclrHasPointersLive`) in the style of `LiveStub.lean`: unrolled loads and stores
(`LiveStubMem.chunkList`) for a request of `n` bytes that the runtime's `ok` predicate pins
(`hok : ∀ args, ok addr args → ∃ d sr, args = [d, sr, n]`), so the code is straight-line and
the executor runs it at the program's own address:

```lean
def implAt : List Segment := [LiveStub.memmoveSeg mvA 12, LiveStub.memclrSeg clA 12]
theorem model_mv : MemmoveLive linked mvA 4096 R := by janus_live_memmove 12 hok_mv
theorem model_cl : MemclrNoHeapPointersLive linked clA 4096 R := by janus_live_memclr 12 hok_cl
```

A copy is `ceil(n/8)`-ish loads into `X3..` then the same number of stores, so overlapping source
and destination are fine; at most 13 chunks (`n` up to 104 bytes, fewer when `n % 8 ≠ 0`). A clear
is stores of `XZR`, no register limit.
-/

namespace Janus.Contracts.LiveStub

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

/-- `LDR` of `w` bytes (`8, 4, 2, 1`) at `[Xrn, #off]` into `rt`. -/
def ldrW (w off rn rt : Nat) : Nat :=
  if w = 8 then 0xf9400000 + off / 8 * 1024 + rn * 32 + rt
  else if w = 4 then 0xb9400000 + off / 4 * 1024 + rn * 32 + rt
  else if w = 2 then 0x79400000 + off / 2 * 1024 + rn * 32 + rt
  else 0x39400000 + off * 1024 + rn * 32 + rt

/-- `STR` of `w` bytes at `[Xrn, #off]` from `rt` (`31` = `XZR`). -/
def strW (w off rn rt : Nat) : Nat :=
  if w = 8 then 0xf9000000 + off / 8 * 1024 + rn * 32 + rt
  else if w = 4 then 0xb9000000 + off / 4 * 1024 + rn * 32 + rt
  else if w = 2 then 0x79000000 + off / 2 * 1024 + rn * 32 + rt
  else 0x39000000 + off * 1024 + rn * 32 + rt

/-- `memmove(dst = X0, src = X1, n)` for a pinned `n`: load all chunks into `X3…`, store them all. -/
def memmoveCodeN (n : Nat) : List Nat :=
  (chunkList n).mapIdx (fun j c => ldrW c.2 c.1 1 (3 + j)) ++
  (chunkList n).mapIdx (fun j c => strW c.2 c.1 0 (3 + j)) ++ [0xd65f03c0]

/-- `memclrNoHeapPointers(ptr = X0, n)` for a pinned `n`: stores of `XZR`. -/
def memclrCodeN (n : Nat) : List Nat :=
  (chunkList n).map (fun c => strW c.2 c.1 0 31) ++ [0xd65f03c0]

def memmoveSeg (addr n : Nat) : Segment := ⟨"live-stub.memmove", addr, memmoveCodeN n⟩
def memclrSeg (addr n : Nat) : Segment := ⟨"live-stub.memclr", addr, memclrCodeN n⟩

/-- A copy or clear whose stores are `ws` (inside `[dst, dst + n)`) returns as `LiveMemRet`. -/
theorem liveMemRet_writes {R : RtInv} {d nargs b dst n : Nat} {L : List (Nat × Nat)} {s fin : State}
    {P : Memory → Prop} (ws : List Wr) (hws : ∀ w ∈ ws, dst ≤ w.1 ∧ w.1 + w.2.1 ≤ dst + n)
    (hpc : fin.pc = s.regs 30) (hsp : fin.sp = s.sp) (h18 : fin.regs 18 = s.regs 18)
    (h28 : fin.regs 28 = s.regs 28) (h29 : fin.regs 29 = s.regs 29) (hdz : fin.dczid = s.dczid)
    (htp : fin.tpidr = s.tpidr) (hfc : fin.fpcr = s.fpcr) (hfs : fin.fpsr = s.fpsr)
    (hmem : fin.mem = applyWrites s.mem ws) (hdst : InRanges dst n L ∨ Outside dst n R.rt)
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)) (hP : P (applyWrites s.mem ws)) :
    LiveMemRet R d nargs [(dst, dst + n)] L b s fin P := by
  obtain ⟨junk, f, vr, m, ex, ep, hs⟩ := retStateX_intro (res := []) hpc hsp h18 h28 h29 hdz htp hfc hfs
    (fun i hi => absurd hi (by simp))
  have hm : m = applyWrites s.mem ws := by
    have := congrArg State.mem hs
    simp only [retStateX] at this
    rw [← hmem]; exact this.symm ▸ rfl
  have hbytes : ∀ a k, (a + k ≤ dst ∨ dst + n ≤ a) → ∀ i, i < k →
      (applyWrites s.mem ws).bytes (a + i) = s.mem.bytes (a + i) := by
    intro a k hk i hi
    exact bytes_applyWrites_untouched ws (fun w hw => by have := hws w hw; omega) _
  refine ⟨junk, f, vr, m, ex, ep, hs, ⟨fun a k hout => ?_, fun a k w => ?_⟩, ⟨fun a k hin hout => ?_⟩, ?_, ?_⟩
  · simp only [outside_append, outside_cons, outside_nil, and_true] at hout
    rw [hm]
    exact Memory.readLE_congr (fun i hi => hbytes a k hout.2 i hi)
  · rw [hm, accessible_applyWrites]
  · simp only [outside_cons, outside_nil, and_true] at hout
    rw [hm]
    exact Memory.readLE_congr (fun i hi => hbytes a k hout i hi)
  · rw [hm, view_applyWrites ws hws hdst]; exact hinv
  · rw [hm]; exact hP

end Janus.Contracts.LiveStub

/-- `MemmoveLive linked a 4096 (toyR [] ok)` for the stub `LiveStub.memmoveSeg a n`; `hok` pins the
request: `∀ args, ok a args → ∃ d sr, args = [d, sr, n]`. -/
syntax "janus_live_memmove " term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_memmove $n $ok) => `(tactic| (
      intro L b s hpc pre
      obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
      obtain ⟨d0, s0, hargs⟩ := $ok _ hLm.1
      simp only [List.cons.injEq, and_true] at hargs
      have hn : (s.regs 2).toNat = $n := hargs.2.2
      rw [hn] at hs2 hd2 hd4
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      rw [hn]
      open Janus.Contracts.LiveStub in
        refine liveMemRet_writes (copyWrites s.mem (s.regs 0).toNat (s.regs 1).toNat $n)
          (copyWrites_sub _ _ _ _) rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ hd4 hLm.2.1 ?_
      · (try simp only [Janus.Contracts.LiveStub.readLE_mod_of_le, Nat.reducePow, Nat.reduceLeDiff]); rfl
      · exact Janus.Contracts.LiveStub.copied_copyWrites _ _ _ _ _))

/-- `MemclrNoHeapPointersLive linked a 4096 (toyR [] ok)` for `LiveStub.memclrSeg a n`; `hok`:
`∀ args, ok a args → ∃ d, args = [d, n]`. Also proves `MemclrHasPointersLive` (the same code). -/
syntax "janus_live_memclr " term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_memclr $n $ok) => `(tactic| (
      intro L b s hpc pre
      obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, hrest⟩ := pre
      obtain ⟨d0, hargs⟩ := $ok _ hLm.1
      simp only [List.cons.injEq, and_true] at hargs
      have hn : (s.regs 1).toNat = $n := hargs.2
      obtain ⟨hd1, hd2, hd3, hd4⟩ := hrest
      rw [hn] at hd2 hd4
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      rw [hn]
      open Janus.Contracts.LiveStub in
        refine liveMemRet_writes (clearWrites (s.regs 0).toNat $n)
          (clearWrites_sub _ _) rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ hd4 hLm.2.1 ?_
      · rfl
      · exact Janus.Contracts.LiveStub.zeroed_clearWrites _ _ _))
