import Janus

/-! # Accessibility across a callee frame, amd64 (U-ACCSUB)

The twin of `JanusTests/AccSub.lean`: the facts about a buffer and about the stack window are stated about the memory
before a call (`s.mem`) or after it (`S.mem`), related by `hfr : MemFrame s.mem S.mem rs`; the accessibility discharger of
`janus64_run` follows the `MemFrame` links in both directions.

* (a) `mov [rdi+rsi], rdx` at `P + l`, with `accessible P C true` and `l + 8 ≤ C`;
* (b) a spill `mov [rsp+0x70], rdx` below the entry stack pointer, inside the stack window;
* (c) a `jae` guard on `rsi <u rdx` for `mov byte [rdi+rsi], dl` into `[P, P + rdx)`. -/

namespace JanusTests.AccSub64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `mov [rdi+rsi], rdx; ret` -/
def storeA : Janus.Amd64.Program where
  segments := [{ name := "storeA", base := 0x10000, bytes := [0x48, 0x89, 0x14, 0x37, 0xc3] }]
  stubs := []
  exitAddr := 0

/-- (a), the fact is about the memory of the store (`S.mem`). -/
theorem store_later (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr storeA ret) (s S : Janus.Amd64.State)
    (P l C : Nat) (hfr : MemFrame s.mem S.mem rs) (hacc : S.mem.accessible P C true = true)
    (hl : l + 8 ≤ C) (hP : P + C ≤ 2 ^ 48) (hpc : S.rip = 0x10000#64)
    (h7 : S.regs 7 = BitVec.ofNat 64 P) (h6 : S.regs 6 = BitVec.ofNat 64 l)
    (hsp : (S.regs 4).toNat + 8 ≤ 2 ^ 48) (hsa : S.mem.accessible (S.regs 4).toNat 8 false = true)
    (hrd : S.mem.readLE (S.regs 4).toNat 8 = ret) (hdis : P + C ≤ (S.regs 4).toNat ∨ (S.regs 4).toNat + 8 ≤ P) :
    Reaches (storeA.withExit ret) S (IsReturn fun _ => True) := by
  janus64_run

/-- (a), the fact is about the memory before the call (`s.mem`). -/
theorem store_earlier (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr storeA ret) (s S : Janus.Amd64.State)
    (P l C : Nat) (hfr : MemFrame s.mem S.mem rs) (hacc : s.mem.accessible P C true = true)
    (hl : l + 8 ≤ C) (hP : P + C ≤ 2 ^ 48) (hpc : S.rip = 0x10000#64)
    (h7 : S.regs 7 = BitVec.ofNat 64 P) (h6 : S.regs 6 = BitVec.ofNat 64 l)
    (hsp : (S.regs 4).toNat + 8 ≤ 2 ^ 48) (hsa : S.mem.accessible (S.regs 4).toNat 8 false = true)
    (hrd : S.mem.readLE (S.regs 4).toNat 8 = ret) (hdis : P + C ≤ (S.regs 4).toNat ∨ (S.regs 4).toNat + 8 ≤ P) :
    Reaches (storeA.withExit ret) S (IsReturn fun _ => True) := by
  janus64_run

/-- `sub rsp, 0x90; mov [rsp+0x70], rdx; add rsp, 0x90; ret` -/
def spill : Janus.Amd64.Program where
  segments := [{ name := "spill", base := 0x20000, bytes := [0x48, 0x81, 0xec, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x70, 0x48, 0x81, 0xc4, 0x90, 0x00, 0x00, 0x00, 0xc3] }]
  stubs := []
  exitAddr := 0

/-- (b): the stack window `[sp - 4232, sp + 40)` is a fact about `S.mem`. -/
theorem spill_window (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr spill ret) (s S : Janus.Amd64.State)
    (hfr : MemFrame s.mem S.mem rs) (hal : (S.regs 4).toNat % 8 = 0) (hb : 4232 ≤ (S.regs 4).toNat)
    (ha : (S.regs 4).toNat + 40 ≤ 2 ^ 48)
    (hw : S.mem.accessible ((S.regs 4).toNat - 4232) (4232 + 40) true = true)
    (hpc : S.rip = 0x20000#64) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ret) :
    Reaches (spill.withExit ret) S (IsReturn fun _ => True) := by
  janus64_run

/-- `cmp rsi, rdx; jae end; mov [rdi+rsi], dl; end: ret` -/
def guarded : Janus.Amd64.Program where
  segments := [{ name := "guarded", base := 0x30000, bytes := [0x48, 0x39, 0xd6, 0x73, 0x03, 0x88, 0x14, 0x37, 0xc3] }]
  stubs := []
  exitAddr := 0

/-- (c): the guard `rsi <u rdx` (`ult`) bounds the index for the access, with the fact about the entry memory. -/
theorem guard_ult (rs : List (Nat × Nat)) (ret : Nat) (hret : RetAddr guarded ret) (s S : Janus.Amd64.State)
    (P : Nat) (hfr : MemFrame s.mem S.mem rs) (hacc : s.mem.accessible P (S.regs 2).toNat true = true)
    (hP : P + (S.regs 2).toNat ≤ 2 ^ 48) (hpc : S.rip = 0x30000#64) (h7 : S.regs 7 = BitVec.ofNat 64 P)
    (hsp : (S.regs 4).toNat + 8 ≤ 2 ^ 48) (hsa : S.mem.accessible (S.regs 4).toNat 8 false = true)
    (hrd : S.mem.readLE (S.regs 4).toNat 8 = ret)
    (hdis : P + (S.regs 2).toNat ≤ (S.regs 4).toNat ∨ (S.regs 4).toNat + 8 ≤ P) :
    Reaches (guarded.withExit ret) S (IsReturn fun _ => True) := by
  janus64_run

/-! ## A new array: the accessible range inside a named predicate

`f: call g; mov [rax], dl; ret`: `g` returns a fresh writable array, stated by a named predicate `NewArr` (as the
postcondition of `growslice` does); the store into it needs no `janus_data` and no hand-derived `accessible` fact. -/

def NewArr (m : Memory) (r0 c : Nat) : Prop := r0 + c ≤ 2 ^ 48 ∧ m.accessible r0 c true = true

def callNew : Janus.Amd64.Program where
  segments := [{ name := "callNew", base := 0x70000, bytes := [0xe8, 0x03, 0x00, 0x00, 0x00, 0x88, 0x10, 0xc3, 0xc3] }]
  stubs := []
  exitAddr := 0

theorem new_array_store (ret : Nat) (hret : RetAddr callNew ret) (S : Janus.Amd64.State)
    (hg : Summary callNew 0x70008 (fun _ => True)
      (fun s s' => ∃ r0 c : Nat, 0 < c ∧ NewArr s'.mem r0 c ∧ s'.regs 0 = BitVec.ofNat 64 r0 ∧
        s'.rip = BitVec.ofNat 64 (s.mem.readLE (s.regs 4).toNat 8) ∧ s'.regs 4 = s.regs 4 + 8#64 ∧
        s'.regs 2 = s.regs 2 ∧ MemFrame s.mem s'.mem [(r0, r0 + c)] ∧
        (r0 + c ≤ (s.regs 4).toNat + 8 ∨ (s.regs 4).toNat + 16 ≤ r0) ∧
        s'.mem.readLE ((s.regs 4).toNat + 8) 8 = s.mem.readLE ((s.regs 4).toNat + 8) 8))
    (hpc : S.rip = 0x70000#64) (hsp : (S.regs 4).toNat + 16 ≤ 2 ^ 48) (hal : (S.regs 4).toNat % 8 = 0)
    (hw : S.mem.accessible ((S.regs 4).toNat - 8) 8 true = true) (hb : 8 ≤ (S.regs 4).toNat)
    (hsa : S.mem.accessible (S.regs 4).toNat 8 false = true)
    (hrd : S.mem.readLE (S.regs 4).toNat 8 = ret) :
    Reaches (callNew.withExit ret) S (IsReturn fun _ => True) := by
  janus64_run calls [hg]

end JanusTests.AccSub64
