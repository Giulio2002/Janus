import Janus

/-! # Byte-exact forwarding of partially overlapping reads over earlier stores

A read that partially overlaps an earlier store (a 16-byte `MOVUPS` load over an 8-byte store, a read
running past the end of a store, a read ending inside one) at constant offsets from the same base
used to stay `(m.writeLE a n v).readLE b k` ("aliasing unknown"). The three lemmas
`readLE_writeLE_contained/overrun/underrun` forward the stored bytes and keep the old bytes of the
rest of the read. Negative cases: unrelated bases and unknown offsets stay unresolved. -/

namespace JanusTests.MemoryOverlap

open Janus.Arm64

/-! ## Pure memory lemmas, checked on concrete memories -/

def m0 : Memory := ⟨fun i => BitVec.ofNat 8 (i * 7 + 3), [⟨0x1000, 64, true⟩]⟩

-- store inside the read (8 bytes at +4 of a 16-byte read)
example : (m0.writeLE 0x1004 8 0x1122334455667788).readLE 0x1000 16 =
    m0.readLE 0x1000 4 + 256 ^ 4 * (0x1122334455667788 % 256 ^ 8 +
      256 ^ 8 * m0.readLE 0x100c 4) := by
  rw [Memory.readLE_writeLE_contained _ _ (by omega) (by omega)]
-- the same, evaluated
example : (m0.writeLE 0x1004 8 0x1122334455667788).readLE 0x1000 16 =
    m0.readLE 0x1000 4 + 256 ^ 4 * (0x1122334455667788 % 256 ^ 8 +
      256 ^ 8 * m0.readLE 0x100c 4) := by decide
-- read running past the end of the store
example : (m0.writeLE 0x1000 8 0x1122334455667788).readLE 0x1004 8 =
    0x11223344 + 256 ^ 4 * m0.readLE 0x1008 4 := by decide
-- read ending inside the store
example : (m0.writeLE 0x1004 8 0x1122334455667788).readLE 0x1000 8 =
    m0.readLE 0x1000 4 + 256 ^ 4 * 0x55667788 := by decide

-- general statements for symbolic addresses
example (m : Memory) (a v : Nat) :
    (m.writeLE (a + 8) 8 v).readLE a 16 =
      m.readLE a 8 + 256 ^ 8 * (v % 256 ^ 8) := by
  rw [Memory.readLE_writeLE_contained _ _ (by omega) (by omega)]
  simp [Nat.add_sub_cancel_left, show a + 8 + 8 = a + 16 from rfl, Nat.sub_self]
example (m : Memory) (a v : Nat) :
    (m.writeLE a 8 v).readLE (a + 4) 8 = v / 256 ^ 4 % 256 ^ 4 + 256 ^ 4 * m.readLE (a + 8) 4 := by
  rw [Memory.readLE_writeLE_overrun _ _ (by omega) (by omega) (by omega)]
  simp only [show a + 4 - a = 4 by omega, show a + 8 - (a + 4) = 4 by omega,
    show a + 4 + 8 - (a + 8) = 4 by omega]
example (m : Memory) (a v : Nat) :
    (m.writeLE (a + 12) 8 v).readLE a 16 = m.readLE a 12 + 256 ^ 12 * (v % 256 ^ 4) := by
  rw [Memory.readLE_writeLE_underrun _ _ (by omega) (by omega) (by omega)]
  simp only [show a + 12 - a = 12 by omega, show a + 16 - (a + 12) = 4 by omega]

/-! ## amd64: `MOVUPS` over a stored word -/

theorem lt64 (v : BitVec 64) : v.toNat < 2 ^ 64 := v.isLt

section Amd64
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- A program `f` of `store; load; ret` over `rbx = p` (the value is `rax = v`). -/
def prog (name : String) (code : List Nat) : Program where
  segments := [⟨name, 0x1000, code ++ [0xc3]⟩]
  stubs := []
  exitAddr := 0

/-- `mov [rbx+8], rax; movups xmm0, [rbx]`: the store is the upper half of the load. -/
def hi : Program := prog "hi" [0x48, 0x89, 0x43, 0x08, 0x0f, 0x10, 0x03]
/-- `mov [rbx+4], rax; movups xmm0, [rbx]`: the store is in the middle of the load. -/
def mid : Program := prog "mid" [0x48, 0x89, 0x43, 0x04, 0x0f, 0x10, 0x03]
/-- `mov [rbx], rax; movups xmm0, [rbx+4]`: the load runs past the end of the store. -/
def over : Program := prog "over" [0x48, 0x89, 0x03, 0x0f, 0x10, 0x43, 0x04]
/-- `mov [rbx+12], rax; movups xmm0, [rbx]`: the load ends inside the store. -/
def under : Program := prog "under" [0x48, 0x89, 0x43, 0x0c, 0x0f, 0x10, 0x03]
/-- `mov [rbx-64], rax; movups xmm0, [rbx-72]`: offsets below the base (a stack frame). -/
def neg : Program := prog "neg" [0x48, 0x89, 0x43, 0xc0, 0x0f, 0x10, 0x43, 0xb8]

/-- The precondition: `[p, p+16+pad)` is writable (`lo`: and the frame below), and above the stack. -/
def Pre (s : Janus.Amd64.State) (p : BitVec 64) (lo hi : Nat) : Prop :=
  StackWritable s 0 8 ∧ lo ≤ p.toNat ∧ s.mem.accessible (p.toNat - lo) (lo + hi) true = true ∧
    p.toNat + hi ≤ 2 ^ 48 ∧ p.toNat + hi ≤ (s.regs 4).toNat


example (v p : BitVec 64) :
    Ensures hi 0x1000 [v, p] (fun s => Pre s p 0 16)
      (fun s s' => (s'.xmm 0).toNat = s.mem.readLE p.toNat 8 + 2 ^ 64 * v.toNat) := by
  intro ret hret s hs ⟨⟨hle, hnw, hacc⟩, hl, hp, hp', hd⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run
  have := Memory.readLE_lt s.mem p.toNat 8
  have := lt64 v
  simp only [Nat.reducePow] at *
  omega

example (v p : BitVec 64) :
    Ensures mid 0x1000 [v, p] (fun s => Pre s p 0 16)
      (fun s s' => (s'.xmm 0).toNat = s.mem.readLE p.toNat 4 +
        2 ^ 32 * (v.toNat + 2 ^ 64 * s.mem.readLE (p.toNat + 12) 4)) := by
  intro ret hret s hs ⟨⟨hle, hnw, hacc⟩, hl, hp, hp', hd⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run
  have := Memory.readLE_lt s.mem p.toNat 4
  have := Memory.readLE_lt s.mem (p.toNat + 12) 4
  have := lt64 v
  simp only [Nat.reducePow] at *
  omega

example (v p : BitVec 64) :
    Ensures over 0x1000 [v, p] (fun s => Pre s p 0 20)
      (fun s s' => (s'.xmm 0).toNat = v.toNat / 2 ^ 32 + 2 ^ 32 * s.mem.readLE (p.toNat + 8) 12) := by
  intro ret hret s hs ⟨⟨hle, hnw, hacc⟩, hl, hp, hp', hd⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run
  have := Memory.readLE_lt s.mem (p.toNat + 8) 12
  have := lt64 v
  simp only [Nat.reducePow] at *
  omega

example (v p : BitVec 64) :
    Ensures under 0x1000 [v, p] (fun s => Pre s p 0 20)
      (fun s s' => (s'.xmm 0).toNat = s.mem.readLE p.toNat 12 + 2 ^ 96 * (v.toNat % 2 ^ 32)) := by
  intro ret hret s hs ⟨⟨hle, hnw, hacc⟩, hl, hp, hp', hd⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run
  have := Memory.readLE_lt s.mem p.toNat 12
  have := lt64 v
  simp only [Nat.reducePow] at *
  omega

/-- The shape of the stack frame: the same base, constant offsets below it (`p - 64`, `p - 72`). -/
example (v p : BitVec 64) :
    Ensures neg 0x1000 [v, p] (fun s => Pre s p 72 16)
      (fun s s' => (s'.xmm 0).toNat = s.mem.readLE (p.toNat - 72) 8 + 2 ^ 64 * v.toNat) := by
  intro ret hret s hs ⟨⟨hle, hnw, hacc⟩, hl, hp, hp', hd⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run
  have := Memory.readLE_lt s.mem (p.toNat - 72) 8
  have := lt64 v
  simp only [Nat.reducePow] at *
  omega

/-! Negative cases: disjoint stays disjoint, unknown relations stay unknown. -/

/-- `mov [rbx+16], rax; movups xmm0, [rbx]`: disjoint, the load sees the old memory. -/
def disj : Program := prog "disj" [0x48, 0x89, 0x43, 0x10, 0x0f, 0x10, 0x03]

example (v p : BitVec 64) :
    Ensures disj 0x1000 [v, p] (fun s => Pre s p 0 32)
      (fun s s' => (s'.xmm 0).toNat = s.mem.readLE p.toNat 16) := by
  intro ret hret s hs ⟨⟨hle, hnw, hacc⟩, hl, hp, hp', hd⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run

/-- `mov [rbx+8], rax; movups xmm0, [rcx]`: two unrelated pointers. -/
def unk : Program := prog "unk" [0x48, 0x89, 0x43, 0x08, 0x0f, 0x10, 0x01]

/-- info: janus64_run: the remaining goals contain reads over earlier stores whose aliasing is unknown -/
#guard_msgs (substring := true) in
example (v p q : BitVec 64) :
    Ensures unk 0x1000 [v, p, q]
      (fun s => Pre s p 0 16 ∧ s.mem.accessible q.toNat 16 false = true ∧ q.toNat + 16 ≤ 2 ^ 48)
      (fun _ s' => (s'.xmm 0).toNat ≤ 2 ^ 128) := by
  intro ret hret s hs ⟨⟨⟨hle, hnw, hacc⟩, hl, hp, hp', hd⟩, hq, hq'⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run
  janus64_arith

/-! A read wider than `janus.readOverlap.maxWidth` (default 16) keeps its form: `vmovdqu ymm0, [rbx]`
over the store at `rbx + 8`. Raising the option forwards it. -/

/-- `mov [rbx+8], rax; vmovdqu ymm0, [rbx]` -/
def wide : Program := prog "wide" [0x48, 0x89, 0x43, 0x08, 0xc5, 0xfe, 0x6f, 0x03]

/-- info: janus64_run: the remaining goals contain reads over earlier stores whose aliasing is unknown -/
#guard_msgs (substring := true) in
example (v p : BitVec 64) :
    Ensures wide 0x1000 [v, p] (fun s => Pre s p 0 32)
      (fun _ s' => (s'.xmm 0).toNat ≤ 2 ^ 128) := by
  intro ret hret s hs ⟨⟨hle, hnw, hacc⟩, hl, hp, hp', hd⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run
  janus64_arith

set_option janus.readOverlap.maxWidth 32 in
example (v p : BitVec 64) :
    Ensures wide 0x1000 [v, p] (fun s => Pre s p 0 32)
      (fun s s' => (s'.xmm 0).toNat = s.mem.readLE p.toNat 8 + 2 ^ 64 * v.toNat) := by
  intro ret hret s hs ⟨⟨hle, hnw, hacc⟩, hl, hp, hp', hd⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run
  have := Memory.readLE_lt s.mem p.toNat 8
  have := lt64 v
  simp only [Nat.reducePow] at *
  omega

end Amd64

/-! ## arm64: a 16-byte `LDR Q` over an 8-byte `STR` -/

section Arm64
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-- `str x1, [x0, #8]; ldr q0, [x0]; ret` -/
def armHi : Program where
  segments := [{ name := "armHi", base := 0x10000, words := [0xf9000401, 0x3dc00000, 0xd65f03c0] }]
  stubs := []
  exitAddr := 0

example (p v : BitVec 64) :
    Ensures armHi 0x10000 [p, v]
      (fun s => s.mem.accessible p.toNat 16 true = true ∧ p.toNat + 16 ≤ 2 ^ 48)
      (fun s s' => (s'.vregs 0).toNat = s.mem.readLE p.toNat 8 + 2 ^ 64 * v.toNat) := by
  intro ret hret s hs ⟨hp, hp'⟩
  janus_intro hs
  janus_run
  have := Memory.readLE_lt s.mem p.toNat 8
  have := lt64 v
  simp only [Nat.reducePow] at *
  omega

end Arm64
end JanusTests.MemoryOverlap
