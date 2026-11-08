import Extracted

/-!
# `int64_t e_bump(int64_t x)` (C, arm64): a writable C global updated through the GOT

```c
int64_t e_counter;          /* .bss */
int64_t e_scale = 3;        /* .data */
int64_t e_bump(int64_t x) { e_counter += x * e_scale; return e_counter; }
```

**Guarantee.** For every `x`, every AAPCS64 call of the gcc-compiled `e_bump` in a state whose
memory holds the function's read-only data (`DataLoaded`: here the two GOT slots, which the
linker resolved to the addresses of `e_scale` and `e_counter`), with `e_scale` readable and
`e_counter` writable, returns without faulting, restores the callee-saved state, returns
`e_counter + x * e_scale (mod 2^64)` and stores it in `e_counter`; nothing else changes.

**How.** cgo compiles C with `-fPIC`, so both globals are reached through the GOT
(`adrp`+`ldr` of the slot, then the access). The GOT slots are copied as read-only data
(`got:e_scale`, `got:e_counter`: no dynamic relocation touches them, and they lie in
`PT_GNU_RELRO`); the objects themselves are writable C data (`Extracted.cdata`), named here by
`CData.addr`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI

namespace Proof

/-- The C globals, by name. -/
abbrev scale : Nat := CData.addr Extracted.cdata "e_scale"
abbrev counter : Nat := CData.addr Extracted.cdata "e_counter"

/-- The new counter value. -/
def bumped (m : Memory) (x : BitVec 64) : Nat :=
  (m.readLE counter 8 + x.toNat * m.readLE scale 8) % 2 ^ 64

theorem writeLE8_congr (m : Memory) (a : Nat) {v w : Nat} (h : v % 2 ^ 64 = w % 2 ^ 64) :
    m.writeLE a 8 v = m.writeLE a 8 w := by
  rw [← Memory.writeLE_mod (v := v), ← Memory.writeLE_mod (v := w)]
  exact congrArg _ h

theorem correctness (x : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [x]
      (fun s => Extracted.program.DataLoaded s.mem ∧ s.mem.accessible scale 8 false = true ∧
        s.mem.accessible counter 8 true = true)
      (fun s s' => (s'.regs 0).toNat = bumped s.mem x ∧
        s'.mem = s.mem.writeLE counter 8 (bumped s.mem x)) := by
  intro ret hret s hs ⟨hd, hsc, hco⟩
  janus_intro hs.call
  janus_data hd []
  janus_run
  have hsc' : scale = janus_eval% scale := rfl
  have hco' : counter = janus_eval% counter := rfl
  simp only [bumped, hsc', hco', true_and]
  apply writeLE8_congr
  generalize x.toNat * s.mem.readLE (janus_eval% scale) 8 = t
  omega

namespace Witness

open Janus.Contracts.PanicSat (witMemD)

def RET : Nat := 0x1000
def x0 : BitVec 64 := 5#64

/-- The witness memory with the program's read-only data in place, `e_scale` readable and
`e_counter` writable. -/
def wm : Memory :=
  { witMemD [] Extracted.data with
    regions := (witMemD [] Extracted.data).regions ++ [⟨scale, 8, false⟩, ⟨counter, 8, true⟩] }

def s0 : State :=
  { regs := fun i => if i = 0 then x0 else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 0x300000, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wm, exclPass := fun _ => true }

theorem hret : RetAddr Extracted.program RET := RetAddr.of_check (by decide +kernel)

theorem call : CCall (Extracted.program.withExit RET) Extracted.entry [x0] s0 :=
  ⟨⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩, by decide, by decide⟩

theorem dataLoaded : Extracted.program.DataLoaded wm := by
  unfold Janus.Program.DataLoaded
  set_option maxRecDepth 100000 in decide

theorem pre : Extracted.program.DataLoaded s0.mem ∧ s0.mem.accessible scale 8 false = true ∧
    s0.mem.accessible counter 8 true = true :=
  ⟨dataLoaded, by decide +kernel, by decide +kernel⟩

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (x : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [x] s ∧
    (Extracted.program.DataLoaded s.mem ∧ s.mem.accessible scale 8 false = true ∧
      s.mem.accessible counter 8 true = true) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧
      ((s'.regs 0).toNat = bumped s.mem x ∧
        s'.mem = s.mem.writeLE counter 8 (bumped s.mem x))) :=
  ⟨x0, RET, s0, hret, call, pre, correctness x0 RET hret s0 call pre⟩

end Witness

end Proof
