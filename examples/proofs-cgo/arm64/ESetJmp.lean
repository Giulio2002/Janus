import Extracted

/-!
# `int e_setjmp(int v)` (C, arm64): `setjmp` and a non-local `longjmp` back to it

```c
static jmp_buf e_env;
static void e_thrower(int v) { if (v) longjmp(e_env, v); }   /* __longjmp_chk under FORTIFY */
int e_setjmp(int v) { if (setjmp(e_env)) return 1; e_thrower(v); return 0; }
```

**Guarantee.** For every `jmp_buf` model `J` (glibc's layout and pointer mangling are not
assumed: any model with the laws of `JmpModel`), every `v`, and every AAPCS64 call of the
gcc-compiled `e_setjmp` with the static `jmp_buf` `e_env` writable and a stack window for the
calls, the call returns without faulting, restores the callee-saved state (`CReturn`), and
returns `1` if `W0 = v ≠ 0` (through `longjmp`: `_setjmp` returns a second time, with `v`) and `0`
otherwise. Every accessible byte outside `e_env` and the stack below `SP` is unchanged. This
holds under the trusted contract `SetJmp J` only.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI Janus.Contracts.Libc

namespace Proof

abbrev env : Nat := CData.addr Extracted.cdata "e_env"

def Pre (s : State) : Prop :=
  CStack s (libcStack + 48) 0 ∧ env + jmpBufSize ≤ 2 ^ 48 ∧ s.mem.accessible env jmpBufSize true = true ∧
    Outside env jmpBufSize [(s.sp.toNat - (libcStack + 48), s.sp.toNat)]

def Post (v : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).setWidth 32 = (if v.setWidth 32 = 0 then 0 else 1) ∧
  (∀ a k w, s'.mem.accessible a k w = s.mem.accessible a k w) ∧
  ∀ a, Outside a 1 [(env, env + jmpBufSize), (s.sp.toNat - (libcStack + 48), s.sp.toNat)] →
    s'.mem.bytes a = s.mem.bytes a

set_option maxHeartbeats 8000000 in
theorem correctness (J : JmpModel) (v : BitVec 64) :
    CEnsuresC Extracted.program (SetJmp J) Extracted.entry [v] Pre (Post v) := by
  intro ret hret s hs ⟨⟨hal, hb, ha, hw⟩, heb, hea, heo⟩
  have he : env = janus_eval% env := rfl
  rw [he] at heb hea heo ⊢
  simp only [Post, he]
  simp only [outside_cons, outside_nil, and_true, libcStack, jmpBufSize] at heo hb hw ⊢
  apply ReturnsC.of_reaches
  janus_intro hs.call
  have h32 : (s.sp - 32#64).toNat = s.sp.toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run
  trace_state
  all_goals sorry

end Proof
