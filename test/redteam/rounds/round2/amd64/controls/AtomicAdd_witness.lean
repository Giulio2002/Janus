import Proof

/-! Positive control (round 2): the precondition of `AtomicAdd.correctness` is satisfiable, and
instantiating the theorem on a concrete call gives the hardware answer
(`*p = 40`, `d = 2` -> returns 42 and `*p = 42`). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI

namespace AuditWitness

def ret : Nat := 0x1000
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- `p = 0x2000` holds 40, `RSP = 0x8000` holds `ret`. -/
def mem : Memory :=
  ⟨fun a => if a = 0x2000 then 40 else if a = 0x8000 then BitVec.ofNat 8 ret
      else if a = 0x8001 then BitVec.ofNat 8 (ret / 256) else 0,
   [⟨0x2000, 8, true⟩, ⟨0x8000, 8, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then 0x2000 else if i = 3 then 2 else if i = 4 then 0x8000 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem }

theorem setup : CallSetup0 Extracted.entry [0x2000, 2] s0 := by
  refine ⟨rfl, rfl, by decide, ?_, rfl⟩
  intro i h; simp at h; rcases i with _ | _ | i <;> simp_all [s0, argReg, intArgRegs] <;> omega

/-- The call state `s0.setRet ret` agrees with `s0` on the word at `p` (the return slot `[0x8000, 0x8008)` is elsewhere), so
the rewrites of the theorem's readLE terms, which are about the state the run starts from, go through `readLE_setRet_of_disjoint`. -/
theorem rd_setRet : (s0.setRet ret).mem.readLE (0x2000 : BitVec 64).toNat 8 = 40 := by
  rw [readLE_setRet_of_disjoint (by simp [s0])]; decide

theorem pre : StackWritable s0 0 8 ∧ Buffer s0 0x2000 8 true ∧ (0x2000 : BitVec 64).toNat % 8 = 0 ∧
    Disjoint 0x2000 8 (s0.regs regSP) 8 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_, ?_⟩ <;> decide) | (refine ⟨?_, ?_, ?_⟩ <;> decide)

example : ∃ fuel s', (Extracted.program.withExit ret).run fuel (s0.setRet ret) = .ok (.returned s') ∧
    s'.regs 0 = 42 ∧ s'.mem.readLE 0x2000 8 = 42 := by
  obtain ⟨f, s', h1, _, h2, h3⟩ := (Proof.correctness 0x2000 2) s0 setup pre ret hret
  rw [rd_setRet] at h2
  refine ⟨f, s', h1, by rw [h2]; decide, ?_⟩
  rw [show (0x2000 : BitVec 64).toNat = 0x2000 from rfl] at h3; rw [h3, h2]; decide


/-! ## Finding R2-A1 (split-lock): the precondition admits a word that straddles a 64-byte
cache line. `p = 0x203C` covers `0x203C..0x2043`, across the line boundary `0x2040`. The theorem
promised (before the alignment conjunct was added) a normal return; on Linux with `split_lock_detect=fatal` the `LOCK XADDQ` raises `#AC`
and the process gets `SIGBUS` (see `host/splitlock.c`; in the default `warn` mode the kernel
logs a split-lock trap and the result is correct). -/
namespace Split
/-- Since the fix (AtomicAdd's precondition now says `p.toNat % 8 = 0`; `docs/AMD64.md`), the straddling word is no longer admitted: the
theorem cannot be instantiated at `p = 0x203C`, in any state. (This control used to instantiate the theorem there; that was the finding.) -/
example : ¬ ((0x203C : BitVec 64).toNat % 8 = 0) := by decide
/-- The word still straddles the cache line at `0x2040`, so the alignment conjunct is exactly what excludes it. -/
example : 0x203C / 64 ≠ (0x203C + 7) / 64 := by decide
theorem excluded (s : State) :
    ¬ (StackWritable s 0 8 ∧ Buffer s 0x203C 8 true ∧ (0x203C : BitVec 64).toNat % 8 = 0 ∧
        Disjoint 0x203C 8 (s.regs regSP) 8) := fun h => by have := h.2.2.1; revert this; decide
end Split

end AuditWitness

#print axioms Proof.correctness
