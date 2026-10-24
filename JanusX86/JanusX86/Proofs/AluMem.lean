import JanusX86.Proofs.MemOp

/-! # ALU instructions, memory forms -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- Janus' state after a store of `n` bytes of `v` at `E`. -/
def memWrite (js : Janus.Amd64.State) (E n v : Nat) : Janus.Amd64.State := { js with mem := js.mem.writeLE E n v }

open Janus.Amd64 in
theorem readLocRW_mem {js : State} {next : BitVec 64} {w : Nat} {a : Addr} {y : BitVec w}
    (h : readLocRW js next w (.mem a) = .ok y) :
    js.mem.accessible (ea js next a).toNat (w / 8) true = true ∧
      y = BitVec.ofNat w (js.mem.readLE (ea js next a).toNat (w / 8)) := by
  simp only [readLocRW] at h
  cases hl : loadRW js.mem (ea js next a).toNat (w / 8) with
  | error e => simp [hl] at h
  | ok v =>
    simp only [hl, Except.ok.injEq] at h; subst h
    unfold loadRW at hl
    split at hl <;> (try split at hl) <;> simp_all

open Janus.Amd64 in
theorem readLoc_mem {js : State} {next : BitVec 64} {w : Nat} {a : Addr} {y : BitVec w}
    (h : readLoc js next w (.mem a) = .ok y) :
    js.mem.accessible (ea js next a).toNat (w / 8) false = true ∧
      y = BitVec.ofNat w (js.mem.readLE (ea js next a).toNat (w / 8)) := by
  simp only [readLoc] at h
  cases hl : load js.mem (ea js next a).toNat (w / 8) with
  | error e => simp [hl] at h
  | ok v =>
    simp only [hl, Except.ok.injEq] at h; subst h
    unfold load at hl
    split at hl <;> simp_all

open Janus.Amd64 in
theorem writeLoc_mem {js : State} {next : BitVec 64} {w : Nat} {a : Addr} (v : BitVec w)
    (h : js.mem.accessible (ea js next a).toNat (w / 8) true = true) :
    writeLoc js next w (.mem a) v = .ok (memWrite js (ea js next a).toNat (w / 8) v.toNat) := by
  simp [writeLoc, store, h, Janus.Arm64.Memory.accessible_read_of_write js.mem h, memWrite]

open Janus.Amd64 in
/-- Janus' `execAlu` with a memory destination and a register source. -/
theorem execAlu_mem {js js' : State} {next : BitVec 64} {op : AluOp} {w : Nat} {a : Addr} {sl : Loc}
    (hs : readLoc js next w sl = .ok (regVal js w sl))
    (hJ : execAlu js next op w (.mem a) (.loc sl) = .ok js') :
    ∃ c, ((op = .adc ∨ op = .sbb) → js.flags.cf = some c) ∧
      js.mem.accessible (ea js next a).toNat (w / 8) (decide (op ≠ .cmp)) = true ∧
      js' = ((if op = .cmp then js else memWrite js (ea js next a).toNat (w / 8)
          (aluRes op (BitVec.ofNat w (js.mem.readLE (ea js next a).toNat (w / 8))) (regVal js w sl) c).1.toNat).setFlags
        (aluRes op (BitVec.ofNat w (js.mem.readLE (ea js next a).toNat (w / 8))) (regVal js w sl) c).2).setRip next := by
  unfold execAlu at hJ
  simp only [readSrc, hs] at hJ
  cases op
  all_goals first
    | (cases hrd : readLoc js next w (.mem a) with
       | error e => simp [hrd] at hJ
       | ok y =>
         obtain ⟨hacc, rfl⟩ := readLoc_mem hrd
         simp only [hrd, Except.ok.injEq] at hJ
         exact ⟨false, by simp, by simpa (config := {decide := true}) using hacc, by simp [← hJ, aluRes]⟩)
    | (cases hrd : readLocRW js next w (.mem a) with
       | error e => simp [hrd] at hJ
       | ok y =>
         obtain ⟨hacc, rfl⟩ := readLocRW_mem hrd
         first
         | (simp only [hrd, writeLoc_mem _ hacc] at hJ
            refine ⟨false, by simp, by simpa (config := {decide := true}) using hacc, ?_⟩
            simp only [Except.ok.injEq] at hJ; simp [← hJ, aluRes])
         | (cases hc : js.flags.cf with
            | none => simp [hrd, hc] at hJ
            | some c =>
              refine ⟨c, fun _ => rfl, by simpa (config := {decide := true}) using hacc, ?_⟩
              simp [hrd, hc, writeLoc_mem _ hacc] at hJ; simp [← hJ, aluRes]))

end JanusX86.Proofs
