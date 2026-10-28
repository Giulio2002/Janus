import Extracted

/-!
# `char *e_env_at(size_t i)` (C, arm64): a libc variable through a GOT slot the dynamic linker
# fills

```c
extern char **environ;
char *e_env_at(size_t i) { return environ[i]; }
```

`-fPIC` code reads `environ` through its GOT slot (`ADRP`; `LDR X1, [X1, :got_lo12:environ]`).
The slot is the target of an `R_AARCH64_GLOB_DAT` relocation for `environ` (the variable lives
in libc): its run-time value is the dynamic linker's, not a link-time constant, so the extractor
does not copy it but names it (`Extracted.dyngot`). The theorem takes the value as an explicit
precondition stated in terms of the relocation's symbol: `GotBound Extracted.dyngot "environ" v`
(the slot of `environ` is readable and holds `v`, the address the dynamic linker bound `environ`
to), for every `v`.

**Guarantee.** For every `i` and `v`, every AAPCS64 call of `e_env_at` in a state where the
dynamic linker bound `environ` to `v` (`GotBound`), the 8 bytes at `v` (the variable `environ`)
are readable and so is `environ[i]` (the 8 bytes at `*v + 8i`), returns `environ[i]` and changes
no memory.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI

namespace Proof

/-- The value of `environ` (the pointer array) in memory `m`, when `environ` is at `v`. -/
def envp (m : Memory) (v : Nat) : Nat := m.readLE v 8

def Pre (i : W64) (v : Nat) (s : State) : Prop :=
  GotBound Extracted.dyngot "environ" v s.mem ∧ v + 8 ≤ 2 ^ 48 ∧ s.mem.accessible v 8 false = true ∧
    envp s.mem v + 8 * i.toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (envp s.mem v + 8 * i.toNat) 8 false = true

theorem correctness (i : W64) (v : Nat) :
    CEnsures Extracted.program Extracted.entry [i] (Pre i v)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE (envp s.mem v + 8 * i.toNat) 8 ∧ s'.mem = s.mem) := by
  intro ret hret s hs ⟨⟨hsb, hsa, hsv⟩, hvb, hva, heb, hea⟩
  janus_intro hs.call
  have e1 : DynGOT.slotOf Extracted.dyngot "environ" = janus_eval% (DynGOT.slotOf Extracted.dyngot "environ") := rfl
  rw [e1] at hsb hsa hsv
  simp only [envp] at heb hea ⊢
  subst hsv
  janus_run

namespace Witness

/-- The witness: `environ` at `VAR`, its pointer array at `ARR`, the stack at `SP0`, the return
address `RET` (no code there). -/
def VAR : Nat := 0x100000
def ARR : Nat := 0x200000
def SP0 : Nat := 0x300000
def RET : Nat := 0x1000
abbrev slot : Nat := DynGOT.slotOf Extracted.dyngot "environ"

/-- Little-endian byte `j` of `v`. -/
def byteOf (v j : Nat) : Byte := BitVec.ofNat 8 (v / 256 ^ j)

/-- The witness memory: the GOT slot holds `VAR`, `environ` holds `ARR`, `ARR[0] = 0`. -/
def mem0 : Memory :=
  ⟨fun a => if slot ≤ a ∧ a < slot + 8 then byteOf VAR (a - slot)
      else if VAR ≤ a ∧ a < VAR + 8 then byteOf ARR (a - VAR) else 0,
   [⟨slot, 8, false⟩, ⟨VAR, 8, false⟩, ⟨ARR, 8, false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr Extracted.program RET := RetAddr.of_check (by decide +kernel)

theorem call : CCall (Extracted.program.withExit RET) Extracted.entry [0#64] s0 :=
  ⟨⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩, by decide, by decide⟩

theorem pre : Pre 0#64 VAR s0 := by
  refine ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (i : W64) (v ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [i] s ∧ Pre i v s :=
  ⟨0#64, VAR, RET, s0, hret, call, pre⟩

/-- So the guarantee is reached: `e_env_at(0)` returns `environ[0]` (here `0`). -/
theorem returns : GoABI.Returns (Extracted.program.withExit RET) s0 fun s' =>
    CReturn s0 s' ∧ (s'.regs 0).toNat = s0.mem.readLE (envp s0.mem VAR + 8 * (0#64).toNat) 8 ∧ s'.mem = s0.mem :=
  correctness 0#64 VAR RET hret s0 call pre

end Witness

end Proof
