import Extracted

/-!
# `uint32_t e_atomic_inc(uint32_t *p)` (C, arm64): GCC `__atomic` through libgcc's outline atomics

```c
uint32_t e_atomic_inc(uint32_t *p) { return __atomic_add_fetch(p, 1, __ATOMIC_ACQ_REL); }
```

**Guarantee.** For every 4-aligned pointer `p` to 4 writable bytes, every AAPCS64 call of the
gcc-compiled `e_atomic_inc` returns without faulting, restores the callee-saved state, stores
`*p + 1 (mod 2^32)` at `p` and returns it in `W0`; memory changes nowhere else but in the frame
record below `SP`. This holds on **both** paths of libgcc's helper: on a CPU with the Armv8.1 LSE
atomics (libgcc's flag `__aarch64_have_lse_atomics`, a writable C global its constructor sets from
`HWCAP_ATOMICS`, is non-zero) the helper does `LDADDAL W0, W0, [X1]`; otherwise its LL/SC loop
(`LDAXR`; `ADD`; `STLXR`; `CBNZ` back), which returns once a store-exclusive passes. That it
eventually does is the stated progress hypothesis `∃ k, s.exclPass k = true` (the `k+1`-th
store-exclusive to the marked bytes passes; docs/SOUNDNESS.md, "Retry loops terminate only under a
stated progress hypothesis"), assumed only when the flag is clear.

**How.** gcc's `-moutline-atomics` (Ubuntu's default) compiles the atomic to a call of the libgcc
helper `__aarch64_ldadd4_acq_rel`, which is statically linked into the executable and so extracted
and executed like the rest. The LL/SC loop is proved by induction on the index of the first
passing attempt, with the registers the loop changes (`W0`, `W15`, `W17`), the flags, the exclusive
monitor and the outcome stream generalised: a failed attempt returns to the loop head with memory
unchanged and the stream advanced by one.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI

namespace Proof

/-- libgcc's CPU-feature flag. -/
abbrev lse : Nat := CData.addr Extracted.cdata "__aarch64_have_lse_atomics"

/-- The LL/SC loop head of the helper, `ldaxr w0, [x1]`. -/
abbrev head : Nat := segAddr Extracted.program "__aarch64_ldadd4_acq_rel" + 0x18

/-- Where the helper returns in `e_atomic_inc` (after its `bl`). -/
abbrev retPc : Nat := Extracted.entry + 0x14

theorem correctness (p : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p]
      (fun s => p.toNat % 4 = 0 ∧ p.toNat + 4 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 4 true = true ∧
        s.mem.accessible lse 1 false = true ∧ (s.mem.readLE lse 1 ≠ 0 ∨ ∃ k, s.exclPass k = true) ∧ CStack s 16 0 ∧
        Outside p.toNat 4 [(s.sp.toNat - 16, s.sp.toNat)] ∧ Outside lse 1 [(s.sp.toNat - 16, s.sp.toNat)])
      (fun s s' => (s'.regs 0).toNat % 2 ^ 32 = (s.mem.readLE p.toNat 4 + 1) % 2 ^ 32 ∧
        s'.mem.readLE p.toNat 4 = (s.mem.readLE p.toNat 4 + 1) % 2 ^ 32 ∧
        MemFrame s.mem s'.mem [(p.toNat, p.toNat + 4), (s.sp.toNat - 16, s.sp.toNat)]) := by
  intro ret hret s hs ⟨hal4, hpb, hpw, hla, hlv, ⟨hal, hb, ha, hw⟩, hout, hlo⟩
  janus_intro hs.call
  have hl : lse = janus_eval% lse := rfl
  rw [hl] at hla hlv hlo
  simp only [outside_cons, outside_nil, and_true] at hout hlo
  have hlt : s.mem.readLE (janus_eval% lse) 1 < 256 ^ 1 := Memory.readLE_lt _ _ _
  by_cases hl0 : s.mem.readLE (janus_eval% lse) 1 = 0
  · -- the LL/SC path, under the progress hypothesis
    obtain ⟨k, hk⟩ := hlv.resolve_left (by omega)
    have hh : head = janus_eval% head := rfl
    have hrp : retPc = janus_eval% retPc := rfl
    janus_run until [janus_eval% head]
    -- the loop head with every register the loop changes (`W0`, `W15`, `W17`), the flags, the
    -- exclusive monitor and the outcome stream generalised: induction on the first passing attempt
    suffices key : ∀ n (r : Nat → W64) (fl : Flags) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
        ep n = true → (∀ i, i ≠ 0 → i ≠ 15 → i ≠ 17 →
          r i = setReg (setReg (setReg (setReg (setReg s.regs 0 1#64) 1 p) 16 1#64) 29 (s.sp - 16#64)) 30
            (BitVec.ofNat 64 (janus_eval% retPc)) i) →
        Reaches (Extracted.program.withExit ret)
          { regs := r, sp := s.sp - 16#64, pc := BitVec.ofNat 64 (janus_eval% head), flags := fl,
            mem := (s.mem.writeLE (s.sp.toNat - 16) 8 (s.regs 29).toNat).writeLE (s.sp.toNat - 8) 8 ret,
            dczid := s.dczid, vregs := s.vregs, tpidr := s.tpidr, fpcr := s.fpcr, fpsr := s.fpsr, excl := ex,
            exclPass := ep }
          (IsReturn fun s' => CReturn s s' ∧
            ((s'.regs 0).toNat % 2 ^ 32 = (s.mem.readLE p.toNat 4 + 1) % 2 ^ 32 ∧
              s'.mem.readLE p.toNat 4 = (s.mem.readLE p.toNat 4 + 1) % 2 ^ 32 ∧
              MemFrame s.mem s'.mem [(p.toNat, p.toNat + 4), (s.sp.toNat - 16, s.sp.toNat)])) by
      exact key k _ _ _ _ hk (fun _ _ _ _ => rfl)
    intro n
    induction n with
    | zero =>
      intro r fl ex ep hep hr
      have h1 : r 1 = p := by rw [hr 1 (by decide) (by decide) (by decide)]; simp [setReg]
      have h16 : r 16 = 1#64 := by rw [hr 16 (by decide) (by decide) (by decide)]; simp [setReg]
      have h29 : r 29 = s.sp - 16#64 := by rw [hr 29 (by decide) (by decide) (by decide)]; simp [setReg]
      have h30 : r 30 = BitVec.ofNat 64 (janus_eval% retPc) := by
        rw [hr 30 (by decide) (by decide) (by decide)]; simp [setReg]
      have hcs : ∀ i, 19 ≤ i → i ≤ 28 → r i = s.regs i := fun i h1 h2 => by
        rw [hr i (by omega) (by omega) (by omega)]; simp only [setReg]; split <;> (try split) <;> (try split) <;>
          (try split) <;> (try split) <;> first | rfl | omega
      janus_run [hep, h1, h16, h29, h30, hcs 19 (by decide) (by decide), hcs 20 (by decide) (by decide), hcs 21 (by decide) (by decide), hcs 22 (by decide) (by decide), hcs 23 (by decide) (by decide), hcs 24 (by decide) (by decide), hcs 25 (by decide) (by decide), hcs 26 (by decide) (by decide), hcs 27 (by decide) (by decide), hcs 28 (by decide) (by decide)]
      have h4 := Memory.readLE_lt s.mem p.toNat 4
      refine ⟨?_, ?_, by janus_frame⟩ <;>
        simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
    | succ n ih =>
      intro r fl ex ep hep hr
      have h1 : r 1 = p := by rw [hr 1 (by decide) (by decide) (by decide)]; simp [setReg]
      have h16 : r 16 = 1#64 := by rw [hr 16 (by decide) (by decide) (by decide)]; simp [setReg]
      have h29 : r 29 = s.sp - 16#64 := by rw [hr 29 (by decide) (by decide) (by decide)]; simp [setReg]
      have h30 : r 30 = BitVec.ofNat 64 (janus_eval% retPc) := by
        rw [hr 30 (by decide) (by decide) (by decide)]; simp [setReg]
      have hcs : ∀ i, 19 ≤ i → i ≤ 28 → r i = s.regs i := fun i h1 h2 => by
        rw [hr i (by omega) (by omega) (by omega)]; simp only [setReg]; split <;> (try split) <;> (try split) <;>
          (try split) <;> (try split) <;> first | rfl | omega
      by_cases h0 : ep 0 = true
      · janus_run [h0, h1, h16, h29, h30, hcs 19 (by decide) (by decide), hcs 20 (by decide) (by decide), hcs 21 (by decide) (by decide), hcs 22 (by decide) (by decide), hcs 23 (by decide) (by decide), hcs 24 (by decide) (by decide), hcs 25 (by decide) (by decide), hcs 26 (by decide) (by decide), hcs 27 (by decide) (by decide), hcs 28 (by decide) (by decide)]
        have h4 := Memory.readLE_lt s.mem p.toNat 4
        refine ⟨?_, ?_, by janus_frame⟩ <;>
          simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
      · have h0' : ep 0 = false := by simpa using h0
        janus_run [h0', h1, h16, h29, h30] until [janus_eval% head]
        refine ih _ _ _ _ (by simpa using hep) (fun i i0 i15 i17 => ?_)
        simp only [setReg_apply, i0, i15, i17, if_false]
        rw [hr i i0 i15 i17]; simp only [setReg_apply, i0, if_false]
  janus_run
  refine ⟨?_, by janus_frame⟩
  have h4 : s.mem.readLE p.toNat 4 < 2 ^ 32 := Memory.readLE_lt _ _ _
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

namespace Witness

/-- The witness: a CPU without LSE (the flag at `lse` is `0`), so the LL/SC path runs; the
counter at `P`, the stack at `SP0`, the return address `RET` (no code there), and a stream of
store-exclusive outcomes whose first attempt passes. -/
def P : Nat := 0x100000
def SP0 : Nat := 0x300000
def RET : Nat := 0x1000

def mem0 : Memory := ⟨fun _ => 0, [⟨P, 4, true⟩, ⟨lse, 1, false⟩, ⟨SP0 - 16, 16, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 P else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0, exclPass := fun _ => true }

theorem hret : RetAddr Extracted.program RET := RetAddr.of_check (by decide +kernel)

theorem call : CCall (Extracted.program.withExit RET) Extracted.entry [BitVec.ofNat 64 P] s0 :=
  ⟨⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩, by decide, by decide⟩

/-- All hypotheses of `correctness` hold together, on the LL/SC path (flag clear, progress
hypothesis met). -/
theorem nonvacuous : ∃ (p : W64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [p] s ∧
    (p.toNat % 4 = 0 ∧ p.toNat + 4 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 4 true = true ∧
      s.mem.accessible lse 1 false = true ∧ (s.mem.readLE lse 1 ≠ 0 ∨ ∃ k, s.exclPass k = true) ∧
      CStack s 16 0 ∧ Outside p.toNat 4 [(s.sp.toNat - 16, s.sp.toNat)] ∧
      Outside lse 1 [(s.sp.toNat - 16, s.sp.toNat)]) ∧ s.mem.readLE lse 1 = 0 :=
  ⟨_, RET, s0, hret, call, ⟨by decide, by decide, by decide +kernel, by decide +kernel,
    Or.inr ⟨0, rfl⟩, ⟨by decide, by decide, by decide, by decide +kernel⟩,
    by simp only [outside_cons, outside_nil, and_true]; decide +kernel,
    by simp only [outside_cons, outside_nil, and_true]; decide +kernel⟩, by decide +kernel⟩

end Witness

end Proof
