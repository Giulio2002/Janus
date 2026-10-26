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

end Proof
