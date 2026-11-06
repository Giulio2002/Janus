import Janus.Arm64.Exec
import Janus.Arm64.Decode
import Janus.Tactic.Basic

/-!
# Translation invariance of position-independent arm64 code

A runtime-contract stub proven once, at one address, holds at *any* address where a program links the same words. The
engine proves `Summary (codeProg a ws) a pre post` for a stub at a fixed `a`; a consumer needs the contract at its own
contract address `a1` in `P.link impl` (the "witness" for the live contracts). This file proves

* `exec_shift`: for the position-independent instruction classes (`RelOK`) `exec i` commutes with adding a constant to
  `pc` (branches are `pc`-relative; `ret x30` is absolute and is handled apart),
* `exec_target`/`exec_regs`: where a `RelOK` step lands (`pc + one of relTargets`) and that it keeps a register not in `dest`,
* `CodeOK`: the decidable static check on the words (every word decodes; each is `ret x30` or a `RelOK` instruction that
  does not write `X30` and whose branch targets lie in the stub),
* `sim`: a run of the stub at `a` is a run at `a1` (shifted start state, same final state),
* `summary_transport`: `Summary (codeProg a ws) a pre post` gives `Summary p1 a1 pre post` for every `p1` that fetches
  `ws` at `a1` (not a stub, not the exit address). `pre` must force the return address below `a` (so `a` is chosen at or
  above `2^48`, where no `CallOK` return address can lie), and `pre`/`post` must not mention `pc`.

Nothing is trusted: all kernel-checked, no axiom. Every live-contract stub of the framework (newobject, growslice, ...)
can use the same lemma; add a class to `RelOK` (with its `exec_shift`/`exec_target`/`exec_regs` cases) if a stub needs one.
-/

open Janus Janus.Arm64 Janus.Tactic

namespace Janus.Contracts.RelocArm64

def shiftPc (d : BitVec 64) (s : State) : State := { s with pc := s.pc + d }

@[simp] theorem readZR_s (d) (s : State) r : (shiftPc d s).readZR r = s.readZR r := rfl
@[simp] theorem readSP_s (d) (s : State) r : (shiftPc d s).readSP r = s.readSP r := rfl
@[simp] theorem getX_s (d) (s : State) N r : (shiftPc d s).getX N r = s.getX N r := rfl
@[simp] theorem getXSP_s (d) (s : State) N r : (shiftPc d s).getXSP N r = s.getXSP N r := rfl
@[simp] theorem flags_s (d) (s : State) : (shiftPc d s).flags = s.flags := rfl
@[simp] theorem mem_s (d) (s : State) : (shiftPc d s).mem = s.mem := rfl
@[simp] theorem regs_s (d) (s : State) : (shiftPc d s).regs = s.regs := rfl
@[simp] theorem sp_s (d) (s : State) : (shiftPc d s).sp = s.sp := rfl
@[simp] theorem pc_s (d) (s : State) : (shiftPc d s).pc = s.pc + d := rfl
@[simp] theorem writeZR_s (d) (s : State) r v : (shiftPc d s).writeZR r v = shiftPc d (s.writeZR r v) := by
  unfold State.writeZR shiftPc; split <;> rfl
@[simp] theorem writeSP_s (d) (s : State) r v : (shiftPc d s).writeSP r v = shiftPc d (s.writeSP r v) := by
  unfold State.writeSP shiftPc; split <;> rfl
@[simp] theorem setX_s (d) (s : State) {N} r (v : BitVec N) : (shiftPc d s).setX r v = shiftPc d (s.setX r v) := by
  unfold State.setX; simp
@[simp] theorem setXSP_s (d) (s : State) {N} r (v : BitVec N) : (shiftPc d s).setXSP r v = shiftPc d (s.setXSP r v) := by
  unfold State.setXSP; simp
@[simp] theorem setFlags_s (d) (s : State) f : (shiftPc d s).setFlags f = shiftPc d (s.setFlags f) := rfl
@[simp] theorem next_s (d) (s : State) : (shiftPc d s).next = shiftPc d s.next := by
  unfold State.next shiftPc; simp only [State.mk.injEq, and_true, true_and]; rw [BitVec.add_assoc, BitVec.add_assoc]; exact congrArg _ (BitVec.add_comm _ _)
@[simp] theorem mem_upd (d) (s : State) m : shiftPc d { s with mem := m } = { shiftPc d s with mem := m } := rfl

theorem t1 (d) (N op S sh imm12 rn rd) (s : State) :
    execAddSubImm N (shiftPc d s) op S sh imm12 rn rd = shiftPc d (execAddSubImm N s op S sh imm12 rn rd) := by
  unfold execAddSubImm; repeat (first | rfl | simp | split)
theorem t2 (d) (N opc hw imm16 rd) (s : State) :
    execMoveWide N (shiftPc d s) opc hw imm16 rd = shiftPc d (execMoveWide N s opc hw imm16 rd) := by
  unfold execMoveWide; repeat (first | rfl | simp | split)
theorem t3 (d) (N opc shift inv rm imm6 rn rd) (s : State) :
    execLogicalShifted N (shiftPc d s) opc shift inv rm imm6 rn rd = shiftPc d (execLogicalShifted N s opc shift inv rm imm6 rn rd) := by
  unfold execLogicalShifted; repeat (first | rfl | simp | split)
theorem t4 (d) (N op S shift rm imm6 rn rd) (s : State) :
    execAddSubShifted N (shiftPc d s) op S shift rm imm6 rn rd = shiftPc d (execAddSubShifted N s op S shift rm imm6 rn rd) := by
  unfold execAddSubShifted; repeat (first | rfl | simp | split)
theorem t5 (d) (N op rm cond o2 rn rd) (s : State) :
    execCondSel N (shiftPc d s) op rm cond o2 rn rd = shiftPc d (execCondSel N s op rm cond o2 rn rd) := by
  unfold execCondSel; repeat (first | rfl | simp | split)
theorem t6 (d) (N o0 rm ra rn rd) (s : State) :
    execMadd N (shiftPc d s) o0 rm ra rn rd = shiftPc d (execMadd N s o0 rm ra rn rd) := by
  unfold execMadd; repeat (first | rfl | simp | split)
theorem t7 (d) (N o1 rm rn rd) (s : State) :
    execDiv N (shiftPc d s) o1 rm rn rd = shiftPc d (execDiv N s o1 rm rn rd) := by
  unfold execDiv; repeat (first | rfl | simp | split)
theorem t8 (d) (s : State) (rn) : baseAddr (shiftPc d s) rn = baseAddr s rn := by
  unfold baseAddr; repeat (first | rfl | simp | split)
theorem t9 (d) (s : State) (size opc rt) (a) :
    memSingle (shiftPc d s) size opc rt a = (memSingle s size opc rt a).map (shiftPc d) := by
  unfold memSingle; repeat (first | rfl | simp | split)

theorem t10 (d) (s : State) (rn : Nat) (off : W64) (pi wb : Bool)
    (access : State → W64 → Except Fault State)
    (hacc : ∀ s a, access (shiftPc d s) a = (access s a).map (shiftPc d)) :
    memIndexed (shiftPc d s) rn off pi wb access = (memIndexed s rn off pi wb access).map (shiftPc d) := by
  unfold memIndexed
  rw [t8]
  split
  · rfl
  · simp only [hacc]
    generalize access s _ = r
    cases r <;> simp [Except.map]
    split <;> simp

theorem add_rc (a d o : BitVec 64) : a + d + o = a + o + d := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; exact congrArg _ (BitVec.add_comm _ _)
theorem jmp_s (d) (s : State) (o : BitVec 64) :
    ({ shiftPc d s with pc := s.pc + d + o } : State) = shiftPc d { s with pc := s.pc + o } := by
  unfold shiftPc; simp only [State.mk.injEq, and_true, true_and]; exact add_rc _ _ _
def RelOK : Instr → Bool
  | .moveWide .. | .ldstUImm .. | .addSubImm .. | .condSel .. | .div .. | .madd .. | .ldstImm9 ..
  | .logicalShifted .. | .cb .. | .addSubShifted .. | .bcond .. => true
  | .b false _ => true
  | _ => false

theorem pcs_ite (d) (c : Prop) [Decidable c] (a b : State) :
    (if c then shiftPc d a else shiftPc d b) = shiftPc d (if c then a else b) := by split <;> rfl

theorem exec_shift (d) (i : Instr) (h : RelOK i = true) (s : State) :
    exec i (shiftPc d s) = (exec i s).map (shiftPc d) := by
  cases i <;> first | (have h' := h; simp [RelOK] at h'; done) | skip
  case addSubImm sf op S sh imm12 rn rd =>
    simp only [exec]; cases sf <;> simp [t1, Except.map]
  case moveWide sf opc hw imm16 rd =>
    simp only [exec]; cases sf <;> simp [t2, Except.map]
  case logicalShifted sf opc shift N rm imm6 rn rd =>
    simp only [exec]; cases sf <;> simp [t3, Except.map]
  case addSubShifted sf op S shift rm imm6 rn rd =>
    simp only [exec]; cases sf <;> simp [t4, Except.map]
  case condSel sf op rm cond o2 rn rd =>
    simp only [exec]; cases sf <;> simp [t5, Except.map]
  case madd sf o0 rm ra rn rd =>
    simp only [exec]; cases sf <;> simp [t6, Except.map]
  case div sf o1 rm rn rd =>
    simp only [exec]; cases sf <;> simp [t7, Except.map]
  case ldstUImm size opc imm12 rn rt =>
    simp only [exec]
    rw [t10 d s rn _ false false (fun s a => memSingle s size opc rt a) (fun s a => t9 d s size opc rt a)]
    cases memIndexed s rn _ false false (fun s a => memSingle s size opc rt a) <;> simp [Except.map]
  case ldstImm9 size opc mode imm9 rn rt =>
    simp only [exec]
    rw [t10 d s rn _ _ _ (fun s a => memSingle s size opc rt a) (fun s a => t9 d s size opc rt a)]
    cases memIndexed s rn _ _ _ (fun s a => memSingle s size opc rt a) <;> simp [Except.map]
  case cb sf op imm19 rt =>
    simp only [exec, getX_s]
    rw [apply_ite (Except.map (shiftPc d))]
    cases sf <;> simp only [if_true, Bool.false_eq_true, if_false] <;> split <;> split <;> rename_i hc hc'
    all_goals first
      | exact absurd hc' hc
      | exact absurd hc hc'
      | exact congrArg Except.ok (jmp_s d s _)
      | exact congrArg Except.ok (next_s d s)
  case bcond imm19 cond =>
    simp only [exec, flags_s]
    by_cases hc : conditionHolds cond s.flags = true
    · simp only [hc, ↓reduceIte, Except.map]
      exact congrArg Except.ok (jmp_s d s _)
    · simp only [hc, ↓reduceIte, Except.map]
      exact congrArg Except.ok (next_s d s)
  case b op imm26 =>
    cases op
    · exact congrArg Except.ok (jmp_s d s _)
    · simp [RelOK] at h

@[simp] theorem pcw_zr (s : State) r v : (s.writeZR r v).pc = s.pc := by unfold State.writeZR; split <;> rfl
@[simp] theorem pcw_sp (s : State) r v : (s.writeSP r v).pc = s.pc := by unfold State.writeSP; split <;> rfl
@[simp] theorem pcw_x (s : State) {N} r (v : BitVec N) : (s.setX r v).pc = s.pc := by unfold State.setX; simp
@[simp] theorem pcw_xsp (s : State) {N} r (v : BitVec N) : (s.setXSP r v).pc = s.pc := by unfold State.setXSP; simp
@[simp] theorem pcw_fl (s : State) f : (s.setFlags f).pc = s.pc := rfl
@[simp] theorem pcw_next (s : State) : s.next.pc = s.pc + 4 := rfl

theorem q1 (N op S sh imm12 rn rd) (s : State) : (execAddSubImm N s op S sh imm12 rn rd).pc = s.pc := by
  unfold execAddSubImm; repeat (first | rfl | simp | split)
theorem q2 (N opc hw imm16 rd) (s : State) : (execMoveWide N s opc hw imm16 rd).pc = s.pc := by
  unfold execMoveWide; repeat (first | rfl | simp | split)
theorem q3 (N opc shift inv rm imm6 rn rd) (s : State) : (execLogicalShifted N s opc shift inv rm imm6 rn rd).pc = s.pc := by
  unfold execLogicalShifted; repeat (first | rfl | simp | split)
theorem q4 (N op S shift rm imm6 rn rd) (s : State) : (execAddSubShifted N s op S shift rm imm6 rn rd).pc = s.pc := by
  unfold execAddSubShifted; repeat (first | rfl | simp | split)
theorem q5 (N op rm cond o2 rn rd) (s : State) : (execCondSel N s op rm cond o2 rn rd).pc = s.pc := by
  unfold execCondSel; repeat (first | rfl | simp | split)
theorem q6 (N o0 rm ra rn rd) (s : State) : (execMadd N s o0 rm ra rn rd).pc = s.pc := by
  unfold execMadd; repeat (first | rfl | simp | split)
theorem q7 (N o1 rm rn rd) (s : State) : (execDiv N s o1 rm rn rd).pc = s.pc := by
  unfold execDiv; repeat (first | rfl | simp | split)
theorem q9 (s : State) (size opc rt : Nat) (a : W64) (s1 : State) (h : memSingle s size opc rt a = .ok s1) :
    s1.pc = s.pc := by
  unfold memSingle at h
  split at h <;> split at h <;> simp at h <;> subst h <;> simp
theorem q10 (s : State) (rn : Nat) (off : W64) (pi wb : Bool) (access : State → W64 → Except Fault State)
    (hacc : ∀ s a s1, access s a = .ok s1 → s1.pc = s.pc) (s1 : State)
    (h : memIndexed s rn off pi wb access = .ok s1) : s1.pc = s.pc := by
  unfold memIndexed at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i base hb
    generalize (if pi = true then base else base + off) = addr at h
    split at h
    · simp at h
    · rename_i s' hs'
      simp only [Except.ok.injEq] at h
      split at h <;> (subst h; simp [hacc _ _ _ hs'])

def relTargets : Instr → List (BitVec 64)
  | .b _ imm26 => [sext64 28 (imm26 * 4)]
  | .bcond imm19 _ => [4, sext64 21 (imm19 * 4)]
  | .cb _ _ imm19 _ => [4, sext64 21 (imm19 * 4)]
  | _ => [4]

theorem exec_target (i : Instr) (h : RelOK i = true) (s s1 : State) (hx : exec i s = .ok s1) :
    ∃ o ∈ relTargets i, s1.pc = s.pc + o := by
  cases i <;> first | (have h' := h; simp [RelOK] at h'; done) | skip
  case addSubImm sf op S sh imm12 rn rd =>
    simp only [exec] at hx
    cases sf <;> simp at hx <;> subst hx <;> exact ⟨4, by simp [relTargets], by simp [q1]⟩
  case moveWide sf opc hw imm16 rd =>
    simp only [exec] at hx
    cases sf <;> simp at hx <;> subst hx <;> exact ⟨4, by simp [relTargets], by simp [q2]⟩
  case logicalShifted sf opc shift N rm imm6 rn rd =>
    simp only [exec] at hx
    cases sf <;> simp at hx <;> subst hx <;> exact ⟨4, by simp [relTargets], by simp [q3]⟩
  case addSubShifted sf op S shift rm imm6 rn rd =>
    simp only [exec] at hx
    cases sf <;> simp at hx <;> subst hx <;> exact ⟨4, by simp [relTargets], by simp [q4]⟩
  case condSel sf op rm cond o2 rn rd =>
    simp only [exec] at hx
    cases sf <;> simp at hx <;> subst hx <;> exact ⟨4, by simp [relTargets], by simp [q5]⟩
  case madd sf o0 rm ra rn rd =>
    simp only [exec] at hx
    cases sf <;> simp at hx <;> subst hx <;> exact ⟨4, by simp [relTargets], by simp [q6]⟩
  case div sf o1 rm rn rd =>
    simp only [exec] at hx
    cases sf <;> simp at hx <;> subst hx <;> exact ⟨4, by simp [relTargets], by simp [q7]⟩
  case ldstUImm size opc imm12 rn rt =>
    simp only [exec] at hx
    split at hx
    · cases hx
    · rename_i s' hs'
      simp only [Except.ok.injEq] at hx; subst hx
      exact ⟨4, by simp [relTargets], by simp [q10 _ _ _ _ _ _ (fun s a s1 h => q9 s _ _ _ a s1 h) _ hs']⟩
  case ldstImm9 size opc mode imm9 rn rt =>
    simp only [exec] at hx
    split at hx
    · cases hx
    · rename_i s' hs'
      simp only [Except.ok.injEq] at hx; subst hx
      exact ⟨4, by simp [relTargets], by simp [q10 _ _ _ _ _ _ (fun s a s1 h => q9 s _ _ _ a s1 h) _ hs']⟩
  case cb sf op imm19 rt =>
    simp only [exec] at hx
    cases sf <;> simp only [if_true, Bool.false_eq_true, if_false] at hx <;> split at hx
    all_goals first
      | (simp only [Except.ok.injEq] at hx; subst hx; exact ⟨sext64 21 (imm19 * 4), by simp [relTargets], rfl⟩)
      | (simp only [Except.ok.injEq] at hx; subst hx; exact ⟨4, by simp [relTargets], rfl⟩)
  case bcond imm19 cond =>
    simp only [exec] at hx
    split at hx
    · (try simp only [Except.ok.injEq] at hx); subst hx
      exact ⟨sext64 21 (imm19 * 4), by simp [relTargets], rfl⟩
    · (try simp only [Except.ok.injEq] at hx); subst hx
      exact ⟨4, by simp [relTargets], rfl⟩
  case b op imm26 =>
    cases op
    · simp only [exec, Except.ok.injEq] at hx; subst hx
      exact ⟨sext64 28 (imm26 * 4), by simp [relTargets], rfl⟩
    · simp [RelOK] at h

theorem exec_ret_shift (d) (rn : Nat) (s : State) :
    exec (.ret rn) (shiftPc d s) = exec (.ret rn) s := rfl

@[simp] theorem rg_fl (s : State) f (r : Nat) : (s.setFlags f).regs r = s.regs r := rfl
@[simp] theorem rg_next (s : State) (r : Nat) : s.next.regs r = s.regs r := rfl
@[simp] theorem rg_zr (s : State) r v (r' : Nat) (h : r' ≠ r) : (s.writeZR r v).regs r' = s.regs r' := by
  unfold State.writeZR; split <;> simp [h]
@[simp] theorem rg_sp (s : State) r v (r' : Nat) (h : r' ≠ r) : (s.writeSP r v).regs r' = s.regs r' := by
  unfold State.writeSP; split <;> simp [h]
@[simp] theorem rg_x (s : State) {N} r (v : BitVec N) (r' : Nat) (h : r' ≠ r) : (s.setX r v).regs r' = s.regs r' := by
  unfold State.setX; simp [h]
@[simp] theorem rg_xsp (s : State) {N} r (v : BitVec N) (r' : Nat) (h : r' ≠ r) : (s.setXSP r v).regs r' = s.regs r' := by
  unfold State.setXSP; simp [h]

theorem g1 (N op S sh imm12 rn rd r) (h : r ≠ rd) (s : State) : (execAddSubImm N s op S sh imm12 rn rd).regs r = s.regs r := by
  unfold execAddSubImm; repeat (first | rfl | simp [h] | split)
theorem g2 (N opc hw imm16 rd r) (h : r ≠ rd) (s : State) : (execMoveWide N s opc hw imm16 rd).regs r = s.regs r := by
  unfold execMoveWide; repeat (first | rfl | simp [h] | split)
theorem g3 (N opc shift inv rm imm6 rn rd r) (h : r ≠ rd) (s : State) : (execLogicalShifted N s opc shift inv rm imm6 rn rd).regs r = s.regs r := by
  unfold execLogicalShifted; repeat (first | rfl | simp [h] | split)
theorem g4 (N op S shift rm imm6 rn rd r) (h : r ≠ rd) (s : State) : (execAddSubShifted N s op S shift rm imm6 rn rd).regs r = s.regs r := by
  unfold execAddSubShifted; repeat (first | rfl | simp [h] | split)
theorem g5 (N op rm cond o2 rn rd r) (h : r ≠ rd) (s : State) : (execCondSel N s op rm cond o2 rn rd).regs r = s.regs r := by
  unfold execCondSel; repeat (first | rfl | simp [h] | split)
theorem g6 (N o0 rm ra rn rd r) (h : r ≠ rd) (s : State) : (execMadd N s o0 rm ra rn rd).regs r = s.regs r := by
  unfold execMadd; repeat (first | rfl | simp [h] | split)
theorem g7 (N o1 rm rn rd r) (h : r ≠ rd) (s : State) : (execDiv N s o1 rm rn rd).regs r = s.regs r := by
  unfold execDiv; repeat (first | rfl | simp [h] | split)
theorem g9 (s : State) (size opc rt : Nat) (a : W64) (s1 : State) (r : Nat) (h : r ≠ rt)
    (hx : memSingle s size opc rt a = .ok s1) : s1.regs r = s.regs r := by
  unfold memSingle at hx
  split at hx <;> split at hx <;> simp at hx <;> subst hx <;> simp [h]
theorem g10 (s : State) (rn : Nat) (off : W64) (pi wb : Bool) (access : State → W64 → Except Fault State) (r : Nat)
    (hr : wb = true → r ≠ rn) (hacc : ∀ s a s1, access s a = .ok s1 → s1.regs r = s.regs r) (s1 : State)
    (hx : memIndexed s rn off pi wb access = .ok s1) : s1.regs r = s.regs r := by
  unfold memIndexed at hx
  dsimp only at hx
  split at hx
  · simp at hx
  · rename_i base hb
    generalize (if pi = true then base else base + off) = addr at hx
    split at hx
    · simp at hx
    · rename_i s' hs'
      simp only [Except.ok.injEq] at hx
      split at hx
      · rename_i hw; subst hx; simp [hacc _ _ _ hs', hr hw]
      · subst hx; simp [hacc _ _ _ hs']

def dest : Instr → List Nat
  | .addSubImm _ _ _ _ _ _ rd | .moveWide _ _ _ _ rd | .logicalShifted _ _ _ _ _ _ _ rd
  | .addSubShifted _ _ _ _ _ _ _ rd | .condSel _ _ _ _ _ _ rd | .madd _ _ _ _ _ rd | .div _ _ _ _ rd => [rd]
  | .ldstUImm _ _ _ _ rt => [rt]
  | .ldstImm9 _ _ _ _ rn rt => [rt, rn]
  | _ => []

theorem exec_regs (i : Instr) (h : RelOK i = true) (r : Nat) (hr : r ∉ dest i) (s s1 : State)
    (hx : exec i s = .ok s1) : s1.regs r = s.regs r := by
  cases i <;> first | (have h' := h; simp [RelOK] at h'; done) | skip
  case addSubImm sf op S sh imm12 rn rd =>
    simp only [exec] at hx
    have : r ≠ rd := by simpa [dest] using hr
    cases sf <;> simp at hx <;> subst hx <;> simp [g1, this]
  case moveWide sf opc hw imm16 rd =>
    simp only [exec] at hx
    have : r ≠ rd := by simpa [dest] using hr
    cases sf <;> simp at hx <;> subst hx <;> simp [g2, this]
  case logicalShifted sf opc shift N rm imm6 rn rd =>
    simp only [exec] at hx
    have : r ≠ rd := by simpa [dest] using hr
    cases sf <;> simp at hx <;> subst hx <;> simp [g3, this]
  case addSubShifted sf op S shift rm imm6 rn rd =>
    simp only [exec] at hx
    have : r ≠ rd := by simpa [dest] using hr
    cases sf <;> simp at hx <;> subst hx <;> simp [g4, this]
  case condSel sf op rm cond o2 rn rd =>
    simp only [exec] at hx
    have : r ≠ rd := by simpa [dest] using hr
    cases sf <;> simp at hx <;> subst hx <;> simp [g5, this]
  case madd sf o0 rm ra rn rd =>
    simp only [exec] at hx
    have : r ≠ rd := by simpa [dest] using hr
    cases sf <;> simp at hx <;> subst hx <;> simp [g6, this]
  case div sf o1 rm rn rd =>
    simp only [exec] at hx
    have : r ≠ rd := by simpa [dest] using hr
    cases sf <;> simp at hx <;> subst hx <;> simp [g7, this]
  case ldstUImm size opc imm12 rn rt =>
    simp only [exec] at hx
    have : r ≠ rt := by simpa [dest] using hr
    split at hx
    · cases hx
    · rename_i s' hs'
      simp only [Except.ok.injEq] at hx; subst hx
      simp [g10 _ _ _ _ _ _ r (by simp) (fun s a s1 h => g9 s _ _ _ a s1 r this h) _ hs']
  case ldstImm9 size opc mode imm9 rn rt =>
    simp only [exec] at hx
    have h1 : r ≠ rt := fun e => hr (by simp [dest, e])
    have h2 : r ≠ rn := fun e => hr (by simp [dest, e])
    split at hx
    · cases hx
    · rename_i s' hs'
      simp only [Except.ok.injEq] at hx; subst hx
      simp [g10 _ _ _ _ _ _ r (fun _ => h2) (fun s a s1 h => g9 s _ _ _ a s1 r h1 h) _ hs']
  case cb sf op imm19 rt =>
    simp only [exec] at hx
    cases sf <;> simp only [if_true, Bool.false_eq_true, if_false] at hx <;> split at hx <;>
      (simp only [Except.ok.injEq] at hx; subst hx; rfl)
  case bcond imm19 cond =>
    simp only [exec] at hx
    split at hx <;> (simp only [Except.ok.injEq] at hx; subst hx; rfl)
  case b op imm26 =>
    cases op
    · simp only [exec, Except.ok.injEq] at hx; subst hx; rfl
    · simp [RelOK] at h


/-- The stub `ws` at `a`, as a closed program (like `AllocSat.withCode`). -/
def codeProg (a : Nat) (ws : List Nat) : Program := { segments := [⟨"reloc", a, ws⟩], stubs := [], exitAddr := 0 }

def InR (a n pc : Nat) : Prop := a ≤ pc ∧ pc < a + 4 * n ∧ (pc - a) % 4 = 0

instance (a n pc : Nat) : Decidable (InR a n pc) := by unfold InR; infer_instance

/-- The static check: every word decodes; each is `ret x30` or a position-independent instruction that does not write
`X30` and whose branch targets lie in the stub. -/
def CodeOK (a : Nat) (ws : List Nat) : Bool :=
  (List.range ws.length).all fun j =>
    match decodeAll (ws.getD j 0) with
    | none => false
    | some i =>
      match i with
      | .ret 30 => true
      | _ => RelOK i && (relTargets i).all (fun o => decide (InR a ws.length (BitVec.ofNat 64 (a + 4 * j) + o).toNat))
              && !(dest i).contains 30

theorem fetch_codeProg {a : Nat} {ws : List Nat} {pc w : Nat} (h : (codeProg a ws).fetch pc = some w) :
    ∃ j, j < ws.length ∧ pc = a + 4 * j ∧ ws[j]? = some w := by
  simp only [codeProg, Program.fetch, Program.fetchIn] at h
  split at h
  · rename_i hc
    split at h
    · rename_i w' hw
      simp only [Option.some.injEq] at h; subst h
      have hlt := (List.getElem?_eq_some_iff.mp hw).1
      refine ⟨(pc - a) / 4, ?_, by omega, ?_⟩
      · exact hlt
      · exact hw
    · simp [Program.fetchIn] at h
  · simp [Program.fetchIn] at h

theorem pc_shift (a a1 j : Nat) (hj : a + 4 * j < 2 ^ 64) (h1 : a1 + 4 * j < 2 ^ 64) (pc : BitVec 64)
    (hpc : pc.toNat = a + 4 * j) :
    (pc + (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a)).toNat = a1 + 4 * j := by
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hpc]
  omega

theorem ret_pc (s s1 : State) (h : exec (.ret 30) s = .ok s1) : s1.pc = s.regs 30 := by
  by_cases c1 : 2 ^ 56 ≤ (s.regs 30).toNat
  · simp [exec, branchReg, State.readZR, c1] at h
  · by_cases c2 : (s.regs 30).toNat % 4 = 0
    · simp [exec, branchReg, State.readZR, c1, c2] at h; subst h; rfl
    · simp [exec, branchReg, State.readZR, c1, c2] at h

theorem sim (a a1 : Nat) (ws : List Nat) (p1 : Program) (hc : CodeOK a ws = true)
    (hfit : a + 4 * ws.length < 2 ^ 64) (hfit1 : a1 + 4 * ws.length < 2 ^ 64)
    (hp1 : ∀ j w, ws[j]? = some w → p1.fetch (a1 + 4 * j) = some w ∧ p1.stubAt (a1 + 4 * j) = none ∧
      a1 + 4 * j ≠ p1.exitAddr) :
    ∀ k s s', Program.Steps (codeProg a ws) s k s' → InR a ws.length s.pc.toNat → (s.regs 30).toNat < a →
      ¬ InR a ws.length s'.pc.toNat →
      Program.Steps p1 (shiftPc (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) s) k s' := by
  intro k s s' hs
  induction hs with
  | refl s => intro h1 _ h3; exact absurd h1 h3
  | @step s s1 s2 k w hx hst hf hexec rest ih =>
    intro hin h30 hout
    obtain ⟨j, hj, hpc, hw⟩ := fetch_codeProg hf
    have hjr : j ∈ List.range ws.length := List.mem_range.mpr hj
    have hcj := List.all_eq_true.mp hc j hjr
    have hwj : ws.getD j 0 = w := by simp [List.getD_eq_getElem?_getD, hw]
    rw [hwj] at hcj
    obtain ⟨hf1, hst1, hx1⟩ := hp1 j w hw
    have hspc : (shiftPc (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) s).pc.toNat = a1 + 4 * j := by
      have := pc_shift a a1 j (by omega) (by have := List.length_pos_of_mem (List.mem_of_getElem? hw); omega) s.pc (by omega)
      exact this
    cases hd : decodeAll w with
    | none => rw [hd] at hcj; simp at hcj
    | some i =>
      rw [hd] at hcj
      have hstep := Arm64.step_of_decodeAll hd s
      have hstep1 := Arm64.step_of_decodeAll hd (shiftPc (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) s)
      by_cases hr : i = .ret 30
      · subst hr
        have hx0 : exec (.ret 30) s = .ok s1 := by rw [← hstep]; exact hexec
        have hpc1 : s1.pc = s.regs 30 := by
          exact ret_pc s s1 hx0
        have hnot : ¬ InR a ws.length s1.pc.toNat := by
          intro h; have := h.1; rw [hpc1] at this; omega
        have h1step : Arm64.step w (shiftPc (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) s) = .ok s1 := by
          rw [hstep1]; exact hx0
        cases rest with
        | refl => exact Program.Steps.single (by rw [hspc]; exact hx1) (by rw [hspc]; exact hst1) (by rw [hspc]; exact hf1) h1step
        | @step _ s3 _ k' w' hx' hst' hf' hexec' rest' =>
          obtain ⟨j', hj', hpc', _⟩ := fetch_codeProg hf'
          exact absurd ⟨by omega, by omega, by omega⟩ hnot
      · have hcj' : RelOK i = true ∧ (relTargets i).all (fun o => decide (InR a ws.length (BitVec.ofNat 64 (a + 4 * j) + o).toNat)) = true ∧
            (!(dest i).contains 30) = true := by
          revert hcj; cases i <;> simp_all
        obtain ⟨hrel, htg, hd30⟩ := hcj'
        have hx0 : exec i s = .ok s1 := by rw [← hstep]; exact hexec
        obtain ⟨o, ho, hs1pc⟩ := exec_target i hrel s s1 hx0
        have hspc0 : s.pc = BitVec.ofNat 64 (a + 4 * j) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat]; omega
        have hin1 : InR a ws.length s1.pc.toNat := by
          have := List.all_eq_true.mp htg o ho
          simp only [decide_eq_true_eq] at this
          rw [hs1pc, hspc0]; exact this
        have h30' : (s1.regs 30).toNat < a := by
          have hn : 30 ∉ dest i := by simpa using hd30
          rw [exec_regs i hrel 30 hn s s1 hx0]; exact h30
        have ih' := ih hin1 h30' hout
        have h1step : Arm64.step w (shiftPc (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) s) = .ok (shiftPc (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) s1) := by
          rw [hstep1, exec_shift _ i hrel, hx0]; rfl
        exact Program.Steps.step (by rw [hspc]; exact hx1) (by rw [hspc]; exact hst1) (by rw [hspc]; exact hf1) h1step ih'

open Janus.Tactic

theorem shift_back (a a1 : Nat) (t : State) (ht : t.pc = BitVec.ofNat 64 a1) :
    shiftPc (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) { t with pc := BitVec.ofNat 64 a } = t := by
  unfold shiftPc
  cases t
  simp only [State.mk.injEq, and_true, true_and]
  simp only at ht
  rw [ht]; bv_omega

/-- **Translation invariance (arm64).** A summary of the stub `ws` at `a` is a summary of the same stub at `a1`, in any
program `p1` that fetches the stub's words there. Needs: the static check `CodeOK`, nothing wraps around, `pre` forces the
return address below `a` (a code address of a stub above `2^48` is never a return address), and `pre`/`post` do not
mention the pc. -/
theorem summary_transport (a a1 : Nat) (ws : List Nat) (p1 : Program) (pre : State → Prop) (post : State → State → Prop)
    (hn : 0 < ws.length) (hc : CodeOK a ws = true)
    (hfit : a + 4 * ws.length < 2 ^ 64) (hfit1 : a1 + 4 * ws.length < 2 ^ 64)
    (hp1 : ∀ j w, ws[j]? = some w → p1.fetch (a1 + 4 * j) = some w ∧ p1.stubAt (a1 + 4 * j) = none ∧
      a1 + 4 * j ≠ p1.exitAddr)
    (hret : ∀ t, pre t → (t.regs 30).toNat < a)
    (hpre : ∀ s (q : BitVec 64), pre s → pre { s with pc := q })
    (hpost : ∀ s s' (q : BitVec 64), post s s' → post { s with pc := q } s')
    (h : Summary (codeProg a ws) a pre post) : Summary p1 a1 pre post := by
  intro t ht hp
  have hs0 : ({ t with pc := BitVec.ofNat 64 a } : State).pc = BitVec.ofNat 64 a := rfl
  have hpre0 : pre { t with pc := BitVec.ofNat 64 a } := hpre t _ hp
  have h30 := hret _ hpre0
  obtain ⟨k, s', hsteps, hpc', hq⟩ := h _ hs0 hpre0
  have hlt : (({ t with pc := BitVec.ofNat 64 a } : State).regs 30).toNat < a := h30
  have hnot : ¬ InR a ws.length s'.pc.toNat := by
    intro hin; have h1 := hin.1; rw [hpc'] at h1
    have h2 : (({ t with pc := BitVec.ofNat 64 a } : State).regs GoABI.regLR).toNat < a := h30
    omega
  have hin : InR a ws.length (({ t with pc := BitVec.ofNat 64 a } : State).pc.toNat) := by
    rw [hs0, BitVec.toNat_ofNat]
    refine ⟨by omega, by omega, by omega⟩
  have := sim a a1 ws p1 hc hfit hfit1 hp1 k _ s' hsteps hin hlt hnot
  rw [shift_back a a1 t ht] at this
  refine ⟨k, s', this, hpc', ?_⟩
  have := hpost _ s' t.pc hq
  simpa using this

end Janus.Contracts.RelocArm64
