import Janus.Contracts.PrintAmd64
import Janus.Contracts.PrintSat

/-!
# The print path's runtime contracts are satisfiable (amd64, round 9 SAT)

As `Janus.Contracts.PrintSat`: x86-64 code meeting `Amd64.Print.Lock2Contract`,
`Unlock2Contract` and `MemmoveContract`, and call states satisfying their preconditions.
-/

namespace Janus.Amd64.Print.Sat

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print

/-- `MOVB $1, (AX); MOVQ 48(R14), CX; MOVL 264(CX), DX; ADDL $1, DX; MOVL DX, 264(CX); RET`. -/
def lock2Code : List Nat :=
  [0xc6, 0x00, 0x01, 0x49, 0x8b, 0x4e, 0x30, 0x8b, 0x91, 0x08, 0x01, 0x00, 0x00, 0x83, 0xc2, 0x01,
   0x89, 0x91, 0x08, 0x01, 0x00, 0x00, 0xc3]
/-- `MOVB $0, (AX); MOVQ 48(R14), CX; MOVL 264(CX), DX; SUBL $1, DX; MOVL DX, 264(CX); RET`. -/
def unlock2Code : List Nat :=
  [0xc6, 0x00, 0x00, 0x49, 0x8b, 0x4e, 0x30, 0x8b, 0x91, 0x08, 0x01, 0x00, 0x00, 0x83, 0xea, 0x01,
   0x89, 0x91, 0x08, 0x01, 0x00, 0x00, 0xc3]
/-- `TESTQ CX, CX; JE done; loop: MOVZBL (BX), DX; MOVB DL, (AX); INCQ AX; INCQ BX; DECQ CX; JNE loop;
done: RET`. -/
def memmoveCode : List Nat :=
  [0x48, 0x85, 0xc9, 0x74, 0x10, 0x0f, 0xb6, 0x13, 0x88, 0x10, 0x48, 0xff, 0xc0, 0x48, 0xff, 0xc3,
   0x48, 0xff, 0xc9, 0x75, 0xf0, 0xc3]

def prog (code : List Nat) : Amd64.Program :=
  { segments := [⟨"w", 0x1000, code⟩], stubs := [], exitAddr := 0 }

set_option maxHeartbeats 4000000 in
theorem lock2_witness (rt : List (Nat × Nat)) (stack : Nat) :
    Lock2Contract (prog lock2Code) 0x1000 rt stack := by
  intro s hpc ⟨hc, ⟨hl1, hl2, hin1, hg1, hg2, hgo, hm1, hm2, hin2, hap, hlo, hhi, hsp⟩, hfree⟩
  simp only [mLocksOf, gM, mLocks] at *
  have hd1 := hin1.disjoint hgo
  have hd2 := hin2.disjoint hgo
  have hd3 := hin1.disjoint hsp
  have hd4 := hin2.disjoint hsp
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hc
  unfold Apart at hap
  janus64_run
  refine ⟨0, _, _, _, _, _, by ret_state64 [], by janus_frame, ?_, ?_⟩
  all_goals (try unfold lockHeld)
  all_goals janus64_simp
  all_goals omega

set_option maxHeartbeats 4000000 in
theorem unlock2_witness (rt : List (Nat × Nat)) (stack : Nat) :
    Unlock2Contract (prog unlock2Code) 0x1000 rt stack := by
  intro s hpc ⟨hc, ⟨hl1, hl2, hin1, hg1, hg2, hgo, hm1, hm2, hin2, hap, hlo, hhi, hsp⟩, hheld⟩
  simp only [mLocksOf, gM, mLocks] at *
  have hd1 := hin1.disjoint hgo
  have hd2 := hin2.disjoint hgo
  have hd3 := hin1.disjoint hsp
  have hd4 := hin2.disjoint hsp
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hc
  unfold Apart at hap
  janus64_run
  refine ⟨0, _, _, _, _, _, by ret_state64 [], by janus_frame, ?_, ?_⟩
  all_goals (try unfold lockHeld)
  all_goals janus64_simp
  all_goals omega

open Janus.Print.Sat (readBytes_copy_step)

/-- The byte loop of `memmoveCode`: from the loop head with `k` bytes left, the rest is copied. -/
theorem memmove_loop (s0 : State) (hc : CallOK64 s0 0 0)
    (D Sr N : Nat) (hD : D + N ≤ 2 ^ 48) (hS : Sr + N ≤ 2 ^ 48)
    (hwd : s0.mem.accessible D N true = true) (hrs : s0.mem.accessible Sr N false = true)
    (hdisj : D + N ≤ Sr ∨ Sr + N ≤ D)
    (hsp : (s0.regs 4).toNat + 8 ≤ D ∨ D + N ≤ (s0.regs 4).toNat) :
    ∀ k (S : State), 0 < k → k ≤ N →
      S.rip = 0x1005#64 → S.regs 0 = BitVec.ofNat 64 (D + (N - k)) →
      S.regs 3 = BitVec.ofNat 64 (Sr + (N - k)) → S.regs 1 = BitVec.ofNat 64 k →
      S.regs 4 = s0.regs 4 → S.fsBase = s0.fsBase → S.df = s0.df → S.mxcsr = s0.mxcsr →
      S.xmm 15 = s0.xmm 15 → S.regs 5 = s0.regs 5 → S.regs 14 = s0.regs 14 →
      MemFrame s0.mem S.mem [(D, D + N)] →
      readBytes S.mem D (N - k) = readBytes s0.mem Sr (N - k) →
      ReachesRet (prog memmoveCode) (retAddrOf s0) S (fun s' =>
        ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory),
          s' = retState64 s0 junk [] f x yh m ∧ MemFrame s0.mem m [(D, D + N)] ∧
          readBytes m D N = readBytes s0.mem Sr N) := by
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hc
  intro k
  induction k with
  | zero => intro S hk; omega
  | succ k ih =>
    intro S _ hk hpc h0 h1 h2 h4 hfs hdf hmx hx15 h5 h14 hf hrb
    have hrb' := Janus.Print.Sat.readBytes_copy_step S.mem s0.mem D Sr (N - (k + 1)) hrb
    rw [show N - (k + 1) + 1 = N - k by omega] at hrb'
    by_cases hk0 : k = 0
    · subst hk0
      janus64_run
      refine ⟨_, _, _, _, _, by ret_state64 [h4, h5, h14, hfs, hdf, hmx, hx15], by janus_frame, ?_⟩
      have hb8 := (s0.mem.bytes (Sr + (N - 1))).isLt
      simpa [Nat.mod_eq_of_lt (show (s0.mem.bytes (Sr + (N - 1))).toNat < 18446744073709551616 by omega)] using hrb'
    · janus64_run until [0x1005]
      refine ih _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals try (simp only [setRegF_apply]; first | assumption | rfl)
      all_goals try (apply BitVec.eq_of_toNat_eq; simp [setRegF]; omega)
      all_goals try janus_frame
      all_goals (try dsimp only)
      have hb8 := (s0.mem.bytes (Sr + (N - (k + 1)))).isLt
      all_goals simpa [Nat.mod_eq_of_lt (show (s0.mem.bytes (Sr + (N - (k + 1)))).toNat < 18446744073709551616 by omega)] using hrb'

set_option maxHeartbeats 4000000 in
theorem memmove_witness : MemmoveContract (prog memmoveCode) 0x1000 := by
  intro s hpc ⟨hc, hD, hS, hwd, hrs, hdisj, hsp⟩
  have hc' := hc
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hc
  by_cases hN : (s.regs 1).toNat = 0
  · janus64_run
    refine ⟨_, _, _, _, _, by ret_state64 [], ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
    simp [readBytes]
  · janus64_run until [0x1005]
    refine memmove_loop s hc' _ _ _ hD hS hwd hrs hdisj hsp (s.regs 1).toNat _ (by omega) (Nat.le_refl _)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try dsimp only)
    all_goals first
      | rfl
      | exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
      | (simp only [Nat.sub_self]; rfl)
      | (simp; done)

/-! ## Call states satisfying the preconditions

`g` at `0x30000` (read-only, `g.m = 0x31000`), the M at `0x31000` and the mutex key at `0x32000`
(writable, the runtime-owned range `rt0`), the stack at `0x200000`. -/

def rt0 : List (Nat × Nat) := [(0x31000, 0x32008)]

/-- The memory: `g.m = 0x31000`, `m.locks = locks`, the key's low byte `key`. -/
def wmem (locks key : Nat) : Memory :=
  ⟨fun a => if a = 0x30031 then 0x10 else if a = 0x30032 then 0x03
      else if a = 0x31108 then BitVec.ofNat 8 locks else if a = 0x32000 then BitVec.ofNat 8 key else 0,
    [⟨0x30000, 0x100, false⟩, ⟨0x31000, 0x1008, true⟩, ⟨0x200000 - 4096, 4096 + 64, true⟩]⟩

def wst (locks key : Nat) (r : Nat → W64) : State :=
  { regs := fun i => if i = 4 then 0x200000#64 else if i = 14 then 0x30000#64 else r i, rip := 0x1000#64,
    flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := wmem locks key }

def rKey : Nat → W64 := fun i => if i = 0 then 0x32000#64 else 0

theorem lock2_satisfiable : ∃ (p : Amd64.Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat),
    Lock2Contract p addr rt stack ∧
      ∃ s : State, s.rip = BitVec.ofNat 64 addr ∧ CallOK64 s stack 1 ∧ LockPre rt 0 s ∧
        ¬ lockHeld s.mem (s.regs 0).toNat :=
  ⟨prog lock2Code, 0x1000, rt0, 4096, lock2_witness rt0 4096, wst 0 0 rKey, rfl,
    by unfold CallOK64; decide +kernel, by
      unfold LockPre mLocksOf InRanges Apart; simp only [gM, mLocks, rt0, outside_cons, outside_nil]
      decide +kernel, by unfold lockHeld; decide +kernel⟩

theorem unlock2_satisfiable : ∃ (p : Amd64.Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat),
    Unlock2Contract p addr rt stack ∧
      ∃ s : State, s.rip = BitVec.ofNat 64 addr ∧ CallOK64 s stack 1 ∧ LockPre rt 1 s ∧
        lockHeld s.mem (s.regs 0).toNat :=
  ⟨prog unlock2Code, 0x1000, rt0, 4096, unlock2_witness rt0 4096, wst 1 1 rKey, rfl,
    by unfold CallOK64; decide +kernel, by
      unfold LockPre mLocksOf InRanges Apart; simp only [gM, mLocks, rt0, outside_cons, outside_nil]
      decide +kernel, by unfold lockHeld; decide +kernel⟩

/-- `memmove(0x31000, 0x30000, 4)`. -/
def rMove : Nat → W64 := fun i =>
  if i = 0 then 0x31000#64 else if i = 3 then 0x30000#64 else if i = 1 then 4#64 else 0

theorem memmove_satisfiable : ∃ (p : Amd64.Program) (addr : Nat),
    MemmoveContract p addr ∧ ∃ s : State, s.rip = BitVec.ofNat 64 addr ∧ MemmovePre s :=
  ⟨prog memmoveCode, 0x1000, memmove_witness, wst 0 0 rMove, rfl, by
    unfold MemmovePre CallOK64; decide +kernel⟩

end Janus.Amd64.Print.Sat
