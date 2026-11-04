import Janus

/-! # Accessibility across a callee frame (U-ACCSUB)

After a call the memory is `S.mem` with `hfr : MemFrame s.mem S.mem rs`, and the facts about the buffers are
stated about either memory. The discharger of the accessibility side condition of a load or store follows the
`MemFrame` links in both directions (a fact about the entry memory `s.mem` proves a store into `S.mem`, and a
fact about `S.mem` proves one in `s.mem`), instead of rewriting the goal to the earliest memory and ignoring the
facts about the later ones.

* (a) `str x1, [x0, x2]` at `P + l` with `S.mem.accessible P C true` and `l + 8 ≤ C`;
* (b) a spill `str x1, [sp, #0x70]` below the entry stack pointer, inside the stack window `[sp - 4232, sp + 40)`;
* (c) a `b.hs` guard on `x2 <u x3` is a `toNat` fact for the access `strb w1, [x0, x2]` into `[P, P + x3)`.

The same on amd64 and for a precondition `0 < n → m.accessible …` of a callee's summary about the entry memory. -/

namespace JanusTests.AccSub

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-- `add x3, x0, x2; str x1, [x3]; ret` -/
def storeA : Program where
  segments := [{ name := "storeA", base := 0x10000, words := [0x8b020003, 0xf9000061, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0

/-- (a), the fact is about the memory of the store (`S.mem`). -/
theorem store_later (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr storeA ret) (s S : State)
    (P l C : Nat) (v : W64) (hfr : MemFrame s.mem S.mem rs) (hacc : S.mem.accessible P C true = true)
    (hl : l + 8 ≤ C) (hP : P + C ≤ 2 ^ 48) (hpc : S.pc = 0x10000#64) (h0 : S.regs 0 = BitVec.ofNat 64 P)
    (h1 : S.regs 1 = v) (h2 : S.regs 2 = BitVec.ofNat 64 l) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (storeA.withExit ret) S (IsReturn fun _ => True) := by
  janus_run

/-- (a), the fact is about the memory before the call (`s.mem`). -/
theorem store_earlier (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr storeA ret) (s S : State)
    (P l C : Nat) (v : W64) (hfr : MemFrame s.mem S.mem rs) (hacc : s.mem.accessible P C true = true)
    (hl : l + 8 ≤ C) (hP : P + C ≤ 2 ^ 48) (hpc : S.pc = 0x10000#64) (h0 : S.regs 0 = BitVec.ofNat 64 P)
    (h1 : S.regs 1 = v) (h2 : S.regs 2 = BitVec.ofNat 64 l) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (storeA.withExit ret) S (IsReturn fun _ => True) := by
  janus_run

/-- `sub sp, sp, #0x90; str x1, [sp, #0x70]; add sp, sp, #0x90; ret` -/
def spill : Program where
  segments := [{ name := "spill", base := 0x20000, words := [0xd10243ff, 0xf9003be1, 0x910243ff, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0

/-- (b) -/
theorem spill_window (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr spill ret) (s S : State)
    (hfr : MemFrame s.mem S.mem rs) (hal : S.sp.toNat % 16 = 0) (hb : 4232 ≤ S.sp.toNat)
    (ha : S.sp.toNat + 40 ≤ 2 ^ 48) (hw : S.mem.accessible (S.sp.toNat - 4232) (4232 + 40) true = true)
    (hpc : S.pc = 0x20000#64) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (spill.withExit ret) S (IsReturn fun _ => True) := by
  janus_run

/-- `cmp x2, x3; b.hs end; strb w1, [x0, x2]; end: ret` -/
def guarded : Program where
  segments := [{ name := "guarded", base := 0x30000, words := [0xeb03005f, 0x54000042, 0x38226801, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0

/-- (c): the guard `x2 <u x3` alone (one memory). -/
theorem guard_ult_plain (ret : Nat) (hret : RetAddr guarded ret) (S : State)
    (P : Nat) (v i n : W64) (hacc : S.mem.accessible P n.toNat true = true)
    (hP : P + n.toNat ≤ 2 ^ 48) (hpc : S.pc = 0x30000#64) (h0 : S.regs 0 = BitVec.ofNat 64 P)
    (h1 : S.regs 1 = v) (h2 : S.regs 2 = i) (h3 : S.regs 3 = n) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (guarded.withExit ret) S (IsReturn fun _ => True) := by
  janus_run

/-- (c), with the fact about the memory before the call -/
theorem guard_ult (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr guarded ret) (s S : State)
    (P : Nat) (v i n : W64) (hfr : MemFrame s.mem S.mem rs) (hacc : s.mem.accessible P n.toNat true = true)
    (hP : P + n.toNat ≤ 2 ^ 48) (hpc : S.pc = 0x30000#64) (h0 : S.regs 0 = BitVec.ofNat 64 P)
    (h1 : S.regs 1 = v) (h2 : S.regs 2 = i) (h3 : S.regs 3 = n) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (guarded.withExit ret) S (IsReturn fun _ => True) := by
  janus_run

/-- `cmp x3, x2; b.ls end; strb w1, [x0, x2]; end: ret` (the guard is `ule`: `x3 ≤u x2` skips the store). -/
def guardedLs : Program where
  segments := [{ name := "guardedLs", base := 0x40000, words := [0xeb02007f, 0x54000049, 0x38226801, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0

/-- (c), `ule`, one memory -/
theorem guard_ule_plain (ret : Nat) (hret : RetAddr guardedLs ret) (S : State)
    (P : Nat) (v i n : W64) (hacc : S.mem.accessible P n.toNat true = true)
    (hP : P + n.toNat ≤ 2 ^ 48) (hpc : S.pc = 0x40000#64) (h0 : S.regs 0 = BitVec.ofNat 64 P)
    (h1 : S.regs 1 = v) (h2 : S.regs 2 = i) (h3 : S.regs 3 = n) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (guardedLs.withExit ret) S (IsReturn fun _ => True) := by
  janus_run

/-- (c), `ule`, with a callee frame -/
theorem guard_ule (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr guardedLs ret) (s S : State)
    (P : Nat) (v i n : W64) (hfr : MemFrame s.mem S.mem rs) (hacc : S.mem.accessible P n.toNat true = true)
    (hP : P + n.toNat ≤ 2 ^ 48) (hpc : S.pc = 0x40000#64) (h0 : S.regs 0 = BitVec.ofNat 64 P)
    (h1 : S.regs 1 = v) (h2 : S.regs 2 = i) (h3 : S.regs 3 = n) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (guardedLs.withExit ret) S (IsReturn fun _ => True) := by
  janus_run

/-! ## The precondition of a callee's summary about the entry memory

`f: str x30,[sp,#-16]!; bl g; ldr x30,[sp],#16; ret`; the summary of `g` needs `0 < n → s.mem.accessible P n false`.
The fact in the context is about the memory `S.mem` after an earlier callee, the goal is the memory at the call
(`S.mem` after one store, rewritten to the entry memory `s.mem` through `hfr`): the discharger looks at the
facts about both, and `0 < n →` is assumed. -/

def callAcc : Program where
  segments := [{ name := "callAcc", base := 0x60000, words := [0xf81f0ffe, 0x94000003, 0xf84107fe, 0xd65f03c0, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0

theorem callAcc_pre (P n : Nat) :
    Summary callAcc 0x60010 (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧
      (0 < n → s.mem.accessible P n false = true))
      (fun s s' => s' = { s with pc := s.regs 30 }) := by
  intro s hpc ⟨h1, h2, h3⟩
  janus_run

theorem call_pre_frame (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr callAcc ret) (s S : State)
    (P n : Nat) (hfr : MemFrame s.mem S.mem rs) (hacc : S.mem.accessible P n false = true)
    (hal : S.sp.toNat % 16 = 0) (hb : 16 ≤ S.sp.toNat) (ha : S.sp.toNat + 8 ≤ 2 ^ 48)
    (hw : S.mem.accessible (S.sp.toNat - 16) 24 true = true)
    (hpc : S.pc = 0x60000#64) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (callAcc.withExit ret) S (IsReturn fun _ => True) := by
  janus_run calls [callAcc_pre P n]

/-! ## A new array: the accessible range inside a named predicate

`f: mov x19,x30; bl g; strb w1,[x0]; mov x30,x19; ret`: `g` returns a fresh writable array, stated by a
named predicate `NewArr` (as the postcondition of `growslice` does), and the store into it needs no
`janus_data` and no hand-derived `accessible` fact. -/

def NewArr (m : Memory) (r0 c : Nat) : Prop := r0 + c ≤ 2 ^ 48 ∧ m.accessible r0 c true = true

def callNew : Program where
  segments := [{ name := "callNew", base := 0x70000, words := [0xaa1e03f3, 0x94000004, 0x39000001, 0xaa1303fe, 0xd65f03c0, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0

theorem new_array_store (ret : Nat) (hret : RetAddr callNew ret) (S : State) (v : W64)
    (hg : Summary callNew 0x70014 (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56)
      (fun s s' => ∃ r0 c : Nat, 0 < c ∧ NewArr s'.mem r0 c ∧ s'.regs 0 = BitVec.ofNat 64 r0 ∧
        s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 30 = s.regs 30 ∧ s'.regs 19 = s.regs 19 ∧
        MemFrame s.mem s'.mem [(r0, r0 + c)] ∧
        (∀ i, i ≠ 0 → s'.regs i = s.regs i)))
    (hpc : S.pc = 0x70000#64) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (callNew.withExit ret) S (IsReturn fun _ => True) := by
  janus_run calls [hg]

/-! ## `janus_data hd [*]`: every writable range of the context is disjoint from the read-only data

`str x1, [x0]; adrp x2, page; add x2, x2, #0x100; ldr x0, [x2]; ret` stores into a writable buffer and then reads the
first word of a table: the store is disjoint from the table because the buffer is writable (`DataLoaded`). -/

def storeTbl : Program where
  segments := [{ name := "storeTbl", base := 0x40000, words := [0xf9000001, 0x90000002, 0x91040042, 0xf9400040, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0
  data := [{ name := ".rodata", base := 0x40100, bytes := [7, 0, 0, 0, 0, 0, 0, 0] }]

theorem store_tbl (p v : W64) :
    Ensures storeTbl 0x40000 [p, v]
      (fun s => storeTbl.DataLoaded s.mem ∧ s.mem.accessible p.toNat 8 true = true ∧ p.toNat + 8 ≤ 2 ^ 48)
      (fun _ s' => (s'.regs 0).toNat = 7) := by
  intro ret hret s hs ⟨hd, hw, hp⟩
  janus_intro hs
  janus_data hd [*]
  janus_run

/-! ## The diagnostic names the failed obligation and prints the exact side goal

The step's own discharger (with the `MemFrame` links) is run on the goal it could not prove; the message prints that
goal and says `ACCESSIBILITY` when the discharger fails on it. -/

#guard_msgs (substring := true) in
/-- error: janus_run: stuck at pc 0x10004 (storeA+0x4): str x1, [x3] -/
theorem diag_access (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr storeA ret) (s S : State)
    (P l C : Nat) (v : W64) (hfr : MemFrame s.mem S.mem rs) (hacc : S.mem.accessible P C true = true)
    (hl : l + 9 ≤ C) (hP : P + C ≤ 2 ^ 48) (hpc : S.pc = 0x10000#64) (h0 : S.regs 0 = BitVec.ofNat 64 P)
    (h1 : S.regs 1 = v) (h2 : S.regs 2 = BitVec.ofNat 64 (l + C)) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (storeA.withExit ret) S (IsReturn fun _ => True) := by
  janus_run

#guard_msgs (substring := true) in
/-- error: Obligation that failed: ACCESSIBILITY -/
theorem diag_access2 (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr storeA ret) (s S : State)
    (P l C : Nat) (v : W64) (hfr : MemFrame s.mem S.mem rs) (hacc : S.mem.accessible P C true = true)
    (hl : l + 9 ≤ C) (hP : P + C ≤ 2 ^ 48) (hpc : S.pc = 0x10000#64) (h0 : S.regs 0 = BitVec.ofNat 64 P)
    (h1 : S.regs 1 = v) (h2 : S.regs 2 = BitVec.ofNat 64 (l + C)) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (storeA.withExit ret) S (IsReturn fun _ => True) := by
  janus_run

#guard_msgs (substring := true) in
/-- error: S.mem.accessible (P + (l + C)) 8 true = true -/
theorem diag_access3 (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr storeA ret) (s S : State)
    (P l C : Nat) (v : W64) (hfr : MemFrame s.mem S.mem rs) (hacc : S.mem.accessible P C true = true)
    (hl : l + 9 ≤ C) (hP : P + C ≤ 2 ^ 48) (hpc : S.pc = 0x10000#64) (h0 : S.regs 0 = BitVec.ofNat 64 P)
    (h1 : S.regs 1 = v) (h2 : S.regs 2 = BitVec.ofNat 64 (l + C)) (h30 : S.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (storeA.withExit ret) S (IsReturn fun _ => True) := by
  janus_run

end JanusTests.AccSub
