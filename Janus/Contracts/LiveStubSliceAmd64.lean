import Janus.Contracts.LiveStubAmd64
import Janus.Contracts.LiveStubMem

/-!
# Live runtime contracts at a program's own addresses: `memmove`, `memclrNoHeapPointers` (amd64)

The amd64 twin of `LiveStubSlice.lean`. `memmove(dst = RAX, src = RBX, n = RCX)` loads every chunk
(`chunkList n`) into `RDX, RSI, RDI, R8…R13` (at most 9 chunks) and then stores them;
`memclrNoHeapPointers(ptr = RAX, n = RBX)` stores immediate zeros (offsets below 128).
Tactics: `janus64_live_memmove n hok`, `janus64_live_memclr n hok`.
-/

namespace Janus.Contracts.LiveStubAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy
open Janus.Contracts.LiveStub (chunkList applyWrites Wr)

/-- The scratch registers of a copy: `RDX, RSI, RDI, R8, …, R13`. -/
def scratch (j : Nat) : Nat := if j = 0 then 2 else if j = 1 then 6 else if j = 2 then 7 else j + 5

/-- `MOV r, [base + off]` (load) / `MOV [base + off], r` (store) of `w` bytes (`base < 8`); the narrow loads
are `MOVZX` (they zero-extend: a partial-register `MOV` would merge into the old value). -/
def movMem (load : Bool) (base w off r : Nat) : List Nat :=
  let rex : Nat := if r ≥ 8 then 4 else 0
  let modrm : Nat := 0x40 + (r % 8) * 8 + base
  if w = 8 then [0x48 + rex, if load then 0x8b else 0x89, modrm, off]
  else if w = 4 then (if r ≥ 8 then [0x44] else []) ++ [if load then 0x8b else 0x89, modrm, off]
  else if w = 2 then
    if load then (if r ≥ 8 then [0x44] else []) ++ [0x0f, 0xb7, modrm, off]
    else [0x66] ++ (if r ≥ 8 then [0x44] else []) ++ [0x89, modrm, off]
  else
    if load then (if r ≥ 8 then [0x44] else []) ++ [0x0f, 0xb6, modrm, off]
    else [0x40 + rex, 0x88, modrm, off]

/-- `MOV [RAX + off], 0` of `w` bytes. -/
def movZero (w off : Nat) : List Nat :=
  if w = 8 then [0x48, 0xc7, 0x40, off, 0, 0, 0, 0]
  else if w = 4 then [0xc7, 0x40, off, 0, 0, 0, 0]
  else if w = 2 then [0x66, 0xc7, 0x40, off, 0, 0]
  else [0xc6, 0x40, off, 0]

def memmoveCodeN (n : Nat) : List Nat :=
  ((chunkList n).mapIdx (fun j c => movMem true 3 c.2 c.1 (scratch j))).flatten ++
  ((chunkList n).mapIdx (fun j c => movMem false 0 c.2 c.1 (scratch j))).flatten ++ [0xc3]

def memclrCodeN (n : Nat) : List Nat :=
  ((chunkList n).map (fun c => movZero c.2 c.1)).flatten ++ [0xc3]

def memmoveSeg (addr n : Nat) : Janus.Amd64.Segment := ⟨"live-stub.memmove", addr, memmoveCodeN n⟩
def memclrSeg (addr n : Nat) : Janus.Amd64.Segment := ⟨"live-stub.memclr", addr, memclrCodeN n⟩

theorem liveMemRet_writes64 {R : RtInv} {d nargs b dst n : Nat} {L : List (Nat × Nat)} {s fin : State}
    {P : Memory → Prop} (ws : List Wr) (hws : ∀ w ∈ ws, dst ≤ w.1 ∧ w.1 + w.2.1 ≤ dst + n)
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64)
    (h5 : fin.regs 5 = s.regs 5) (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15)
    (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr)
    (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (hmem : fin.mem = applyWrites s.mem ws) (hdst : InRanges dst n L ∨ Outside dst n R.rt)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) (hP : P (applyWrites s.mem ws)) :
    LiveMemRet64 R d nargs [(dst, dst + n)] L b s fin P := by
  obtain ⟨junk, f, x, yh, m, zh, kr, hs⟩ := retState64_intro (res := []) hrip h4 h5 h14 hx hfs hdf hmx
    (by simp) (by simp) (by simp) hx87 hfw
  have hm : m = applyWrites s.mem ws := by
    have := congrArg State.mem hs
    simp only [retState64] at this
    rw [← hmem]; exact this.symm ▸ rfl
  have hbytes : ∀ a k, (a + k ≤ dst ∨ dst + n ≤ a) → ∀ i, i < k →
      (applyWrites s.mem ws).bytes (a + i) = s.mem.bytes (a + i) := by
    intro a k hk i hi
    exact Janus.Contracts.LiveStub.bytes_applyWrites_untouched ws
      (fun w hw => by have := hws w hw; omega) _
  refine ⟨junk, f, x, yh, m, zh, kr, hs, ⟨fun a k hout => ?_, fun a k w => ?_⟩, ⟨fun a k hin hout => ?_⟩,
    ?_, ?_⟩
  · simp only [outside_append, outside_cons, outside_nil, and_true] at hout
    rw [hm]
    exact Janus.Arm64.Memory.readLE_congr (fun i hi => hbytes a k hout.2 i hi)
  · rw [hm, Janus.Contracts.LiveStub.accessible_applyWrites]
  · simp only [outside_cons, outside_nil, and_true] at hout
    rw [hm]
    exact Janus.Arm64.Memory.readLE_congr (fun i hi => hbytes a k hout i hi)
  · rw [hm, Janus.Contracts.LiveStub.view_applyWrites ws hws hdst]; exact hinv
  · rw [hm]; exact hP

end Janus.Contracts.LiveStubAmd64

syntax "janus64_live_memmove " term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_live_memmove $n $ok) => `(tactic| (
      intro L b s hpc pre
      obtain ⟨⟨_, ⟨hra, hal, h3, h4, h5⟩, _⟩, hLm, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4, hd5⟩⟩ := pre
      obtain ⟨d0, s0, hargs⟩ := $ok _ hLm.1
      simp only [List.cons.injEq, and_true] at hargs
      have hn : (s.regs 1).toNat = $n := hargs.2.2
      rw [hn] at hs2 hd2 hd4 hd5
      have hap : Apart (s.regs 0).toNat $n (s.regs 4).toNat 8 := by
        have h := hd5; simp only [outside_cons, outside_nil, and_true] at h; exact h
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      rw [hn]
      open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
        Janus.Contracts.LiveStub Janus.Contracts.LiveStubAmd64 in
        refine liveMemRet_writes64 (copyWrites s.mem (s.regs 0).toNat (s.regs 3).toNat $n)
          (copyWrites_sub _ _ _ _) (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
          (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl ?_ hd4 hLm.2.1 ?_
      · (try simp only [Janus.Contracts.LiveStub.readLE_mod_of_le, Nat.reducePow, Nat.reduceLeDiff]); rfl
      · exact Janus.Contracts.LiveStub.copied_copyWrites _ _ _ _ _))

syntax "janus64_live_memclr " term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_live_memclr $n $ok) => `(tactic| (
      intro L b s hpc pre
      obtain ⟨⟨_, ⟨hra, hal, h3, h4, h5⟩, _⟩, hLm, ⟨hd1, hd2, hd3, hd4, hd5⟩⟩ := pre
      obtain ⟨d0, hargs⟩ := $ok _ hLm.1
      simp only [List.cons.injEq, and_true] at hargs
      have hn : (s.regs 3).toNat = $n := hargs.2
      rw [hn] at hd2 hd4 hd5
      have hap : Apart (s.regs 0).toNat $n (s.regs 4).toNat 8 := by
        have h := hd5; simp only [outside_cons, outside_nil, and_true] at h; exact h
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      rw [hn]
      open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
        Janus.Contracts.LiveStub Janus.Contracts.LiveStubAmd64 in
        refine liveMemRet_writes64 (clearWrites (s.regs 0).toNat $n)
          (clearWrites_sub _ _) (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
          (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl ?_ hd4 hLm.2.1 ?_
      · rfl
      · exact Janus.Contracts.LiveStub.zeroed_clearWrites _ _ _))
