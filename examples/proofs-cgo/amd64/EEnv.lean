import Extracted

/-!
# `char *e_env_at(size_t i)` (C, amd64): a libc variable through a GOT slot the dynamic linker
# fills

```c
extern char **environ;
char *e_env_at(size_t i) { return environ[i]; }
```

`-fPIC` code reads `environ` through its GOT slot (`MOV RAX, [RIP + environ@GOTPCREL]`; the
linker cannot relax it, `environ` being libc's). The slot is the target of an
`R_X86_64_GLOB_DAT` relocation for `environ` (the variable lives
in libc): its run-time value is the dynamic linker's, not a link-time constant, so the extractor
does not copy it but names it (`Extracted.dyngot`). The theorem takes the value as an explicit
precondition stated in terms of the relocation's symbol: `GotBound Extracted.dyngot "environ" v`
(the slot of `environ` is readable and holds `v`, the address the dynamic linker bound `environ`
to), for every `v`.

**Guarantee.** For every `i` and `v`, every System V call of `e_env_at` in a state where the
dynamic linker bound `environ` to `v` (`GotBound`), the return-address slot is readable, the 8 bytes at `v` (the variable `environ`)
are readable and so is `environ[i]` (the 8 bytes at `*v + 8i`), returns `environ[i]` and changes
no memory.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI

namespace Proof

/-- The value of `environ` (the pointer array) in memory `m`, when `environ` is at `v`. -/
def envp (m : Janus.Arm64.Memory) (v : Nat) : Nat := m.readLE v 8

def Pre (i : W64) (v : Nat) (s : State) : Prop :=
  CStack s 0 8 ∧ GotBound Extracted.dyngot "environ" v s.mem ∧ v + 8 ≤ 2 ^ 48 ∧ s.mem.accessible v 8 false = true ∧
    envp s.mem v + 8 * i.toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (envp s.mem v + 8 * i.toNat) 8 false = true

theorem correctness (i : W64) (v : Nat) :
    CEnsures Extracted.program Extracted.entry [i] (Pre i v)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE (envp s.mem v + 8 * i.toNat) 8 ∧ s'.mem = s.mem) := by
  intro ret hret s hs ⟨⟨_, _, hnw, hacc⟩, ⟨hsb, hsa, hsv⟩, hvb, hva, heb, hea⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = i := hs.reg (i := 0) (by simp)
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Amd64.Program.withExit] at hacc hnw h_ret
  have e1 : DynGOT.slotOf Extracted.dyngot "environ" = janus_eval% (DynGOT.slotOf Extracted.dyngot "environ") := rfl
  rw [e1] at hsb hsa hsv
  simp only [envp] at heb hea ⊢
  subst hsv
  janus64_run
  rw [Nat.mul_comm]

namespace Witness

/-- The witness: `environ` at `VAR`, its pointer array at `ARR`, the stack at `SP0` (its
return-address slot holding `RET`, where there is no code). -/
def VAR : Nat := 0x100000
def ARR : Nat := 0x200000
def SP0 : Nat := 0x300008
def RET : Nat := 0x1000
abbrev slot : Nat := DynGOT.slotOf Extracted.dyngot "environ"

/-- Little-endian byte `j` of `v`. -/
def byteOf (v j : Nat) : BitVec 8 := BitVec.ofNat 8 (v / 256 ^ j)

/-- The witness memory: the GOT slot holds `VAR`, `environ` holds `ARR`, `ARR[0] = 0`, the
return-address slot holds `RET`. -/
def mem0 : Janus.Arm64.Memory :=
  ⟨fun a => if slot ≤ a ∧ a < slot + 8 then byteOf VAR (a - slot)
      else if VAR ≤ a ∧ a < VAR + 8 then byteOf ARR (a - VAR)
      else if SP0 ≤ a ∧ a < SP0 + 8 then byteOf RET (a - SP0) else 0,
   [⟨slot, 8, false⟩, ⟨VAR, 8, false⟩, ⟨ARR, 8, false⟩, ⟨SP0, 8, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 SP0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr Extracted.program RET := RetAddr.of_check (by decide +kernel)

theorem call : CCall (Extracted.program.withExit RET) Extracted.entry [0#64] s0 :=
  ⟨rfl, by decide +kernel, by decide, by intro i h; simp at h; subst h; rfl, by decide, rfl⟩

theorem pre : Pre 0#64 VAR s0 := by
  refine ⟨⟨by decide, by decide, by decide, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel,
    by decide +kernel⟩, by decide, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (i : W64) (v ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [i] s ∧ Pre i v s :=
  ⟨0#64, VAR, RET, s0, hret, call, pre⟩

end Witness

end Proof
