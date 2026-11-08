import Extracted

/-!
# `int64_t e_bump(int64_t x)` (C, amd64): a writable C global updated through the GOT

```c
int64_t e_counter;          /* .bss */
int64_t e_scale = 3;        /* .data */
int64_t e_bump(int64_t x) { e_counter += x * e_scale; return e_counter; }
```

**Guarantee.** For every `x`, every System V call of the gcc-compiled `e_bump` in a state whose
memory holds the function's read-only data (`DataLoaded`: the two GOT slots), with `e_scale`
readable and `e_counter` writable (apart from the return-address slot), returns
`e_counter + x * e_scale (mod 2^64)` in `RAX` and stores it in `e_counter`; nothing else changes.

**How.** cgo compiles C with `-fPIC`; this binary is linked with `-Wl,--no-relax`
(`examples-cenv-norelax-amd64`), so the code keeps its GOT loads (`mov sym@GOTPCREL(%rip), %rdx`):
the GOT slots are copied as read-only data (`got:e_scale`, `got:e_counter`), the objects are
writable C data (`Extracted.cdata`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic

namespace Proof

abbrev scale : Nat := CData.addr Extracted.cdata "e_scale"
abbrev counter : Nat := CData.addr Extracted.cdata "e_counter"

def bumped (m : Janus.Arm64.Memory) (x : BitVec 64) : Nat :=
  (m.readLE counter 8 + x.toNat * m.readLE scale 8) % 2 ^ 64

theorem writeLE8_congr (m : Janus.Arm64.Memory) (a : Nat) {v w : Nat} (h : v % 2 ^ 64 = w % 2 ^ 64) :
    m.writeLE a 8 v = m.writeLE a 8 w := by
  rw [← Janus.Arm64.Memory.writeLE_mod (v := v), ← Janus.Arm64.Memory.writeLE_mod (v := w)]
  exact congrArg _ h

theorem correctness (x : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [x]
      (fun s => CStack s 0 8 ∧ Extracted.program.DataLoaded s.mem ∧ s.mem.accessible scale 8 false = true ∧
        s.mem.accessible counter 8 true = true ∧ Disjoint (BitVec.ofNat 64 counter) 8 (s.regs 4) 8)
      (fun s s' => (s'.regs 0).toNat = bumped s.mem x ∧
        s'.mem = s.mem.writeLE counter 8 (bumped s.mem x)) := by
  intro ret hret s hs ⟨⟨_, _, hnw, hacc⟩, hd, hsc, hco, hdj⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = x := hs.reg (i := 0) (by simp)
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Amd64.Program.withExit] at hacc hnw h_ret
  have e1 : scale = janus_eval% scale := rfl
  have e2 : counter = janus_eval% counter := rfl
  rw [e1] at hsc
  rw [e2] at hco hdj
  simp only [Disjoint, BitVec.toNat_ofNat, Nat.reduceMod] at hdj
  janus64_data hd []
  janus64_run
  have hr := Janus.Arm64.Memory.readLE_lt s.mem (janus_eval% scale) 8
  have hmul : (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (janus_eval% scale) 8) * x).toNat =
      x.toNat * Janus.Arm64.Memory.readLE s.mem (janus_eval% scale) 8 % 2 ^ 64 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := Janus.Arm64.Memory.readLE s.mem (janus_eval% scale) 8)
      (by simpa using hr), Nat.mul_comm]
  simp only [bumped, e1, e2, hmul]
  refine ⟨?_, writeLE8_congr _ _ ?_⟩ <;>
  · generalize x.toNat * Janus.Arm64.Memory.readLE s.mem (janus_eval% scale) 8 = t
    omega

namespace Witness

open Janus.Contracts.PanicSat (witMemD)

def ret : Nat := 0x1000
def wsp : Nat := 0x48008  -- addr-ok: a chosen stack word in the witness memory's stack
def x0 : BitVec 64 := 5#64

/-- The witness memory (stack holding the return address, the program's read-only data), with
`e_scale` readable and `e_counter` writable. -/
def wm : Janus.Arm64.Memory :=
  { witMemD [(wsp, ret)] Extracted.data with
    regions := (witMemD [(wsp, ret)] Extracted.data).regions ++ [⟨scale, 8, false⟩, ⟨counter, 8, true⟩] }

def s0 : State :=
  { regs := fun i => if i = 7 then x0 else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wm }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem call : CCall (Extracted.program.withExit ret) Extracted.entry [x0] s0 :=
  ⟨rfl, by decide, by decide, by intro i h; simp at h; subst h; rfl, by decide, rfl⟩

theorem dataLoaded : Extracted.program.DataLoaded wm := by
  unfold Janus.Amd64.Program.DataLoaded
  set_option maxRecDepth 100000 in decide

theorem pre : CStack s0 0 8 ∧ Extracted.program.DataLoaded s0.mem ∧ s0.mem.accessible scale 8 false = true ∧
    s0.mem.accessible counter 8 true = true ∧ Disjoint (BitVec.ofNat 64 counter) 8 (s0.regs 4) 8 := by
  refine ⟨⟨by decide, by decide, by decide, by decide⟩, dataLoaded, by decide +kernel, by decide +kernel, ?_⟩
  unfold Janus.Amd64.GoABI.Disjoint; decide +kernel

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (x : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [x] s ∧
    (CStack s 0 8 ∧ Extracted.program.DataLoaded s.mem ∧ s.mem.accessible scale 8 false = true ∧
      s.mem.accessible counter 8 true = true ∧ Disjoint (BitVec.ofNat 64 counter) 8 (s.regs 4) 8) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧
      ((s'.regs 0).toNat = bumped s.mem x ∧
        s'.mem = s.mem.writeLE counter 8 (bumped s.mem x))) :=
  ⟨x0, ret, s0, hret, call, pre, correctness x0 ret hret s0 call pre⟩

end Witness

end Proof
