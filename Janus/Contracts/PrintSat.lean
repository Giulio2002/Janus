import Janus.Contracts.Print
import Janus.Contracts.SyscallSat

/-!
# The print path's runtime contracts are satisfiable (arm64, round 9 SAT)

`Lock2Contract`, `Unlock2Contract` (`runtime.lock2`/`unlock2` on `debuglock`) and
`MemmoveContract` (`runtime.memmove`) are `Summary` contracts. For each this file gives machine
code that meets it, proved by symbolic execution, and a call state that satisfies its
precondition (`<name>_satisfiable`, `audit/round9/run-round9.sh`, row SAT):

* `lock2`: `MOV W1, #1; STRB W1, [X0]; LDR X2, [X28, #48]; LDR W3, [X2, #264]; ADD W3, W3, #1;
  STR W3, [X2, #264]; RET` (the uncontended fast path: the key's low byte set, `m.locks++`);
* `unlock2`: `STRB WZR, [X0]; LDR X2, [X28, #48]; LDR W3, [X2, #264]; SUB W3, W3, #1;
  STR W3, [X2, #264]; RET`;
* `memmove`: a forward byte loop `CBZ X2, done; loop: LDRB W3, [X1], #1; STRB W3, [X0], #1;
  SUBS X2, X2, #1; B.NE loop; done: RET` (the contract's ranges are disjoint).

The same code at the contract addresses of the print examples' binaries is what their
`Witness.nonvacuous` theorems link (examples/proofs-print/*/src/95-witness.lean).
-/

namespace Janus.Print.Sat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Kernel Janus.Print

def lock2Code : List Nat := [0x52800021, 0x39000001, 0xf9401b82, 0xb9410843, 0x11000463, 0xb9010843, 0xd65f03c0]
def unlock2Code : List Nat := [0x3900001f, 0xf9401b82, 0xb9410843, 0x51000463, 0xb9010843, 0xd65f03c0]
def memmoveCode : List Nat := [0xb40000a2, 0x38401423, 0x38001403, 0xf1000442, 0x54ffffa1, 0xd65f03c0]

def prog (code : List Nat) : Program := { segments := [⟨"w", 0x1000, code⟩], stubs := [], exitAddr := 0 }

set_option maxHeartbeats 4000000 in
theorem lock2_witness (rt : List (Nat × Nat)) (stack : Nat) :
    Lock2Contract (prog lock2Code) 0x1000 rt stack := by
  intro s hpc ⟨⟨h30a, h30b, hal, hst, h8, hsp, hw⟩, ⟨hl1, hl2, hin1, hg1, hg2, hgo, hm1, hm2, hin2, hap, hlo, hhi⟩, hfree⟩
  simp only [mLocksOf, gM, mLocks] at *
  have hd1 := hin1.disjoint hgo
  have hd2 := hin2.disjoint hgo
  unfold Apart at hap
  janus_run
  refine ⟨0, _, _, _, _, _, _, by ret_state, by janus_frame, ?_, ?_⟩
  all_goals janus_simp
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 4000000 in
theorem unlock2_witness (rt : List (Nat × Nat)) (stack : Nat) :
    Unlock2Contract (prog unlock2Code) 0x1000 rt stack := by
  intro s hpc ⟨⟨h30a, h30b, hal, hst, h8, hsp, hw⟩, ⟨hl1, hl2, hin1, hg1, hg2, hgo, hm1, hm2, hin2, hap, hlo, hhi⟩, hheld⟩
  simp only [mLocksOf, gM, mLocks] at *
  have hd1 := hin1.disjoint hgo
  have hd2 := hin2.disjoint hgo
  unfold Apart at hap
  janus_run
  refine ⟨0, _, _, _, _, _, _, by ret_state, by janus_frame, ?_, ?_⟩
  all_goals janus_simp
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem readBytes_copy_step (m m0 : Memory) (D Sr j : Nat) (h : readBytes m D j = readBytes m0 Sr j) :
    readBytes (m.writeLE (D + j) 1 (m0.readLE (Sr + j) 1 % 18446744073709551616)) D (j + 1) =
      readBytes m0 Sr (j + 1) := by
  rw [readBytes_add, readBytes_add m0, readBytes_writeLE (Or.inr (Nat.le_refl _)), h]
  congr 1
  simp only [readBytes, Memory.writeLE, Memory.readLE_one, List.range_one, List.map_cons, List.map_nil]
  have := (m0.bytes (Sr + j)).isLt
  simp [Nat.mod_eq_of_lt (show (m0.bytes (Sr + j)).toNat < 18446744073709551616 by omega)]

/-- The byte loop of `memmoveCode`: from the loop head with `k` bytes left, the rest is copied. -/
theorem memmove_loop (s0 : State) (h30a : (s0.regs 30).toNat % 4 = 0) (h30b : (s0.regs 30).toNat < 2 ^ 48)
    (D Sr N : Nat) (hD : D + N ≤ 2 ^ 48) (hS : Sr + N ≤ 2 ^ 48)
    (hwd : s0.mem.accessible D N true = true) (hrs : s0.mem.accessible Sr N false = true)
    (hdisj : D + N ≤ Sr ∨ Sr + N ≤ D) :
    ∀ k (S : State), 0 < k → k ≤ N →
      S.pc = 0x1004#64 → S.regs 0 = BitVec.ofNat 64 (D + (N - k)) →
      S.regs 1 = BitVec.ofNat 64 (Sr + (N - k)) → S.regs 2 = BitVec.ofNat 64 k →
      S.regs 30 = s0.regs 30 → S.sp = s0.sp → S.regs 18 = s0.regs 18 → S.regs 28 = s0.regs 28 →
      S.regs 29 = s0.regs 29 →
      S.dczid = s0.dczid → S.tpidr = s0.tpidr → S.fpcr = s0.fpcr → S.fpsr = s0.fpsr →
      MemFrame s0.mem S.mem [(D, D + N)] →
      readBytes S.mem D (N - k) = readBytes s0.mem Sr (N - k) →
      ReachesRet (prog memmoveCode) (s0.regs regLR) S (fun s' =>
        ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
          (ex : Option (Nat × Nat)) (ep : Nat → Bool),
          s' = retStateX s0 junk [] f v m ex ep ∧ MemFrame s0.mem m [(D, D + N)] ∧
          readBytes m D N = readBytes s0.mem Sr N) := by
  intro k
  induction k with
  | zero => intro S hk; omega
  | succ k ih =>
    intro S _ hk hpc h0 h1 h2 h30 hsp h18 h28 h29 hdz htp hfc hfs hf hrb
    have hrb' := readBytes_copy_step S.mem s0.mem D Sr (N - (k + 1)) hrb
    rw [show N - (k + 1) + 1 = N - k by omega] at hrb'
    by_cases hk0 : k = 0
    · subst hk0
      janus_run
      refine ⟨_, _, _, _, _, _, by ret_state [h18, h28, h29, hsp, hdz, htp, hfc, hfs], by janus_frame, ?_⟩
      simpa using hrb'
    · janus_run until [0x1004]
      refine ih _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals try (simp only [setReg_apply]; first | assumption | rfl)
      all_goals try (apply BitVec.eq_of_toNat_eq; simp [setReg]; omega)
      all_goals try janus_frame
      all_goals simpa using hrb'

set_option maxHeartbeats 4000000 in
theorem memmove_witness : MemmoveContract (prog memmoveCode) 0x1000 := by
  intro s hpc ⟨h30a, h30b, hD, hS, hwd, hrs, hdisj⟩
  by_cases hN : (s.regs 2).toNat = 0
  · janus_run
    refine ⟨_, _, _, _, _, _, by ret_state, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
    simp [hN, readBytes]
  · have hx0 : s.regs 0 = BitVec.ofNat 64 ((s.regs 0).toNat + ((s.regs 2).toNat - (s.regs 2).toNat)) := by simp
    have hx1 : s.regs 1 = BitVec.ofNat 64 ((s.regs 1).toNat + ((s.regs 2).toNat - (s.regs 2).toNat)) := by simp
    janus_run until [0x1004]
    refine memmove_loop s h30a h30b _ _ _ hD hS hwd hrs hdisj (s.regs 2).toNat _ (by omega) (Nat.le_refl _)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try (simp only [setReg_apply]; first | assumption | rfl)
    all_goals try (simp [setReg])
    all_goals try exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    all_goals simp [readBytes]

/-! ## Call states satisfying the preconditions

`g` at `0x30000` (read-only, `g.m = 0x31000`), the M at `0x31000` and the mutex key at `0x32000`
(writable, the runtime-owned range `rt0`), the stack at `0x200000` (as `Kernel.Sat.wstate`). -/

def rt0 : List (Nat × Nat) := [(0x31000, 0x32008)]

/-- The memory: `g.m = 0x31000`, `m.locks = locks`, the key's low byte `key`. -/
def wmem (locks key : Nat) : Memory :=
  ⟨fun a => if a = 0x30031 then 0x10 else if a = 0x30032 then 0x03
      else if a = 0x31108 then BitVec.ofNat 8 locks else if a = 0x32000 then BitVec.ofNat 8 key else 0,
    [⟨0x30000, 0x100, false⟩, ⟨0x31000, 0x1008, true⟩, ⟨0x200000 - 4096, 4096 + 64, true⟩]⟩

def wst (locks key : Nat) (r : Nat → W64) : State :=
  { regs := fun i => if i = 30 then 0x2000#64 else if i = 28 then 0x30000#64 else r i, sp := 0x200000#64,
    pc := 0x1000#64, flags := ⟨false, false, false, false⟩, mem := wmem locks key }

def rKey : Nat → W64 := fun i => if i = 0 then 0x32000#64 else 0

theorem lock2_satisfiable : ∃ (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat),
    Lock2Contract p addr rt stack ∧
      ∃ s : State, s.pc = BitVec.ofNat 64 addr ∧ CallOK s stack 1 ∧ LockPre rt 0 s ∧
        ¬ lockHeld s.mem (s.regs 0).toNat :=
  ⟨prog lock2Code, 0x1000, rt0, 4096, lock2_witness rt0 4096, wst 0 0 rKey, rfl,
    by unfold CallOK; decide +kernel, by
      unfold LockPre mLocksOf InRanges Apart; simp only [gM, mLocks, rt0, outside_cons, outside_nil]
      decide +kernel, by unfold lockHeld; decide +kernel⟩

theorem unlock2_satisfiable : ∃ (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat),
    Unlock2Contract p addr rt stack ∧
      ∃ s : State, s.pc = BitVec.ofNat 64 addr ∧ CallOK s stack 1 ∧ LockPre rt 1 s ∧
        lockHeld s.mem (s.regs 0).toNat :=
  ⟨prog unlock2Code, 0x1000, rt0, 4096, unlock2_witness rt0 4096, wst 1 1 rKey, rfl,
    by unfold CallOK; decide +kernel, by
      unfold LockPre mLocksOf InRanges Apart; simp only [gM, mLocks, rt0, outside_cons, outside_nil]
      decide +kernel, by unfold lockHeld; decide +kernel⟩

/-- `memmove(0x31000, 0x30000, 4)`. -/
def rMove : Nat → W64 := fun i => if i = 0 then 0x31000#64 else if i = 1 then 0x30000#64 else if i = 2 then 4#64 else 0

theorem memmove_satisfiable : ∃ (p : Program) (addr : Nat),
    MemmoveContract p addr ∧ ∃ s : State, s.pc = BitVec.ofNat 64 addr ∧ MemmovePre s :=
  ⟨prog memmoveCode, 0x1000, memmove_witness, wst 0 0 rMove, rfl, by unfold MemmovePre; decide +kernel⟩

end Janus.Print.Sat
