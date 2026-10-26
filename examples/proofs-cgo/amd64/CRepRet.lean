import Extracted

/-!
# `uint64_t c_repret_umax(uint64_t a, uint64_t b)` (C, amd64): hand-written assembly ending in `REP RET`

```
c_repret_umax:  mov %rsi,%rax;  cmp %rsi,%rdi;  jbe 1f;  mov %rdi,%rax;  1: repz ret   (f3 c3)
```

The function is hand-written assembly in the style of the perlasm (OpenSSL-derived) libraries that
cgo programs link (`cx87.c`): its last instruction is the AMD branch-predictor idiom `repz ret`,
which the CPU executes as a plain `ret` (the `F3` prefix has no effect on a near `RET`; the
amd64 oracle checks this against hardware, `docs/ORACLE-AMD64.md`).

**Guarantee.** For all 64-bit `a` and `b`, every System V call of `c_repret_umax` (any admissible
return address at `[RSP]`, `RSP + 8` 16-byte aligned, the 8 bytes of the return address readable;
every other register, the flags and memory arbitrary) returns after finitely many steps without
faulting, pops the return address, restores `RBX RBP R12–R15` and the direction flag (`CReturn`),
and leaves the unsigned maximum of `a` and `b` in `RAX`. The `RET` that returns is the
`F3 C3` form; before the decoder accepted it, no proof about this function (or any of the 98 perlasm
functions that end in it) could even start.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic

namespace Proof

theorem correctness (a b : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [a, b] (fun s => CStack s 0 8)
      (fun _ s' => (s'.regs 0).toNat = max a.toNat b.toNat) := by
  intro ret hret s hs ⟨_, _, hnw, hacc⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = a := hs.reg (i := 0) (by simp)
  have h_a1 : s.regs 6 = b := hs.reg (i := 1) (by simp)
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Program.withExit] at hacc hnw h_ret
  janus64_run
  all_goals simp [Nat.max_def]
  all_goals omega

/-! ## The hypotheses are satisfiable, and the guarantee is reached

A concrete call `c_repret_umax(3, 5)`: the return address `0x1000` (outside the code, a valid
`RetAddr`) at `[RSP]`, `RSP = 0x20008`, a writable window around it. -/

namespace Witness

def ret : Nat := 0x1000
def wsp : Nat := 0x20008

/-- The stack window `[wsp - 64, wsp + 64)` (writable); the return address at `[wsp]`. -/
def smem : Janus.Arm64.Memory :=
  ⟨fun a => if wsp ≤ a ∧ a < wsp + 8 then BitVec.ofNat 8 (ret / 256 ^ (a - wsp)) else 0,
   [⟨wsp - 64, 128, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 7 then 3#64 else if i = 6 then 5#64 else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := smem }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem call : CCall (Extracted.program.withExit ret) Extracted.entry [3#64, 5#64] s0 :=
  ⟨rfl, by decide, by decide, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, by decide, rfl⟩

theorem stack : CStack s0 0 8 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

/-- All the hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [3#64, 5#64] s ∧ CStack s 0 8 :=
  ⟨ret, s0, hret, call, stack⟩

/-- So the guarantee is reached: the call returns with `max 3 5 = 5` in `RAX`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    CReturn s0 s' ∧ (s'.regs 0).toNat = 5 :=
  (correctness 3#64 5#64 ret hret s0 call stack).mono fun _ h => ⟨h.1, by simpa using h.2⟩

end Witness

end Proof
