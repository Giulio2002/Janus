import PrintProofs.Arm64.FnHead

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

namespace PrintFn

/-! ## Non-vacuity: code for the three contracts and a call state

`Janus.Print.Sat`'s witness code (`lock2Code`, `unlock2Code`, `memmoveCode`, proved there against
the contracts on a toy program) linked at the contract addresses of this binary, proved again
here against the contracts for the linked program; the runtime-owned ranges `wrt` (the mutex key
and `m.locks`); and a memory `wmem` holding the read-only data, a stack, `g` and its M, and the
print globals (zero: not panicking, backlog index 0, no `overrideWrite`, `debuglock` free). Each
example's `Witness.nonvacuous` builds its call state on it. -/

namespace Witness

open Janus.Print.Sat

def L2 : Nat := P.contractAddr "runtime.lock2"
def U2 : Nat := P.contractAddr "runtime.unlock2"
def MM : Nat := P.contractAddr "runtime.memmove"

/-- The witness code at the given contract addresses. -/
def implAtOf (l2 u2 mm : Nat) : List Segment :=
  [⟨"lock2", l2, lock2Code⟩, ⟨"unlock2", u2, unlock2Code⟩, ⟨"memmove", mm, memmoveCode⟩]

def implAt : List Segment := implAtOf L2 U2 MM

/-- The program linked with it, as a closed program. -/
def linked : Program := { P with segments := P.segments ++ implAt }

theorem linked_eq : P.link implAt = linked := rfl

set_option maxHeartbeats 4000000 in
theorem lock2_model (rt : List (Nat × Nat)) (stack : Nat) :
    Lock2Contract (P.link implAt) (P.contractAddr "runtime.lock2") rt stack := by
  rw [linked_eq]
  intro s hpc ⟨⟨h30a, h30b, hal, hst, h8, hsp, hw⟩, ⟨hl1, hl2, hin1, hg1, hg2, hgo, hm1, hm2, hin2, hap, hlo, hhi⟩, hfree⟩
  simp only [mLocksOf, gM, mLocks] at *
  have hd1 := hin1.disjoint hgo
  have hd2 := hin2.disjoint hgo
  unfold Apart at hap
  janus_run
  refine ⟨0, _, _, _, _, by ret_state, by janus_frame, ?_, ?_⟩
  all_goals janus_simp
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 4000000 in
theorem unlock2_model (rt : List (Nat × Nat)) (stack : Nat) :
    Unlock2Contract (P.link implAt) (P.contractAddr "runtime.unlock2") rt stack := by
  rw [linked_eq]
  intro s hpc ⟨⟨h30a, h30b, hal, hst, h8, hsp, hw⟩, ⟨hl1, hl2, hin1, hg1, hg2, hgo, hm1, hm2, hin2, hap, hlo, hhi⟩, hheld⟩
  simp only [mLocksOf, gM, mLocks] at *
  have hd1 := hin1.disjoint hgo
  have hd2 := hin2.disjoint hgo
  unfold Apart at hap
  janus_run
  refine ⟨0, _, _, _, _, by ret_state, by janus_frame, ?_, ?_⟩
  all_goals janus_simp
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem mm_loop (s0 : State) (h30a : (s0.regs 30).toNat % 4 = 0) (h30b : (s0.regs 30).toNat < 2 ^ 48)
    (D Sr N : Nat) (hD : D + N ≤ 2 ^ 48) (hS : Sr + N ≤ 2 ^ 48)
    (hwd : s0.mem.accessible D N true = true) (hrs : s0.mem.accessible Sr N false = true)
    (hdisj : D + N ≤ Sr ∨ Sr + N ≤ D) :
    ∀ k (S : State), 0 < k → k ≤ N →
      S.pc = BitVec.ofNat 64 (MM + 4) → S.regs 0 = BitVec.ofNat 64 (D + (N - k)) →
      S.regs 1 = BitVec.ofNat 64 (Sr + (N - k)) → S.regs 2 = BitVec.ofNat 64 k →
      S.regs 30 = s0.regs 30 → S.sp = s0.sp → S.regs 18 = s0.regs 18 → S.regs 28 = s0.regs 28 →
      S.regs 29 = s0.regs 29 →
      S.dczid = s0.dczid → S.tpidr = s0.tpidr → S.fpcr = s0.fpcr → S.fpsr = s0.fpsr →
      MemFrame s0.mem S.mem [(D, D + N)] →
      readBytes S.mem D (N - k) = readBytes s0.mem Sr (N - k) →
      ReachesRet linked (s0.regs regLR) S (fun s' =>
        ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
          s' = retState s0 junk [] f v m ∧ MemFrame s0.mem m [(D, D + N)] ∧
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
      refine ⟨_, _, _, _, by ret_state [h18, h28, h29, hsp, hdz, htp, hfc, hfs], by janus_frame, ?_⟩
      simpa using hrb'
    · janus_run until [MM + 4]
      refine ih _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals try (simp only [setReg_apply]; first | assumption | rfl)
      all_goals try (apply BitVec.eq_of_toNat_eq; simp [setReg]; omega)
      all_goals try janus_frame
      all_goals simpa using hrb'

set_option maxHeartbeats 4000000 in
theorem memmove_model : MemmoveContract (P.link implAt) (P.contractAddr "runtime.memmove") := by
  rw [linked_eq]
  intro s hpc ⟨h30a, h30b, hD, hS, hwd, hrs, hdisj⟩
  by_cases hN : (s.regs 2).toNat = 0
  · janus_run
    refine ⟨_, _, _, _, by ret_state, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
    simp [hN, readBytes]
  · have hx0 : s.regs 0 = BitVec.ofNat 64 ((s.regs 0).toNat + ((s.regs 2).toNat - (s.regs 2).toNat)) := by simp
    have hx1 : s.regs 1 = BitVec.ofNat 64 ((s.regs 1).toNat + ((s.regs 2).toNat - (s.regs 2).toNat)) := by simp
    janus_run until [MM + 4]
    refine mm_loop s h30a h30b _ _ _ hD hS hwd hrs hdisj (s.regs 2).toNat _ (by omega) (Nat.le_refl _)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try (simp only [setReg_apply]; first | assumption | rfl)
    all_goals try (simp [setReg])
    all_goals try exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    all_goals simp [readBytes]

/-- The witness goroutine, its M, the stack pointer and the return address. -/
def WG : Nat := 0x50000
def WM : Nat := 0x51000
def WSP : Nat := 0x48000
def ret : Nat := 0x200000

/-- The runtime-owned ranges: the mutex key `debuglock` and `m.locks`. -/
def wrt : List (Nat × Nat) := [(DL, DL + 8), (WM + 264, WM + 268)]

/-- The byte of the read-only data `ds` at `a`, if any. -/
def dbyteOf (ds : List DataSegment) (a : Nat) : Option Nat :=
  ds.findSome? fun d => if d.base ≤ a ∧ a < d.base + d.bytes.length then d.bytes[a - d.base]? else none

/-- The witness memory: the read-only data (read-only regions), `g.m = WM` (`g` read-only), the M,
the print globals' range (from `runtime.overrideWrite` to the end of `printBacklog`) and the
stack (writable); every other byte 0. -/
def wmemOf (ow bl : Nat) (ds : List DataSegment) : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((dbyteOf ds a).getD (if a = WG + 49 then 0x10 else if a = WG + 50 then 0x05 else 0)),
    [⟨WG, 0x100, false⟩, ⟨WM, 0x200, true⟩, ⟨WSP - 0x8000, 0x10000, true⟩, ⟨ow, bl + 512 - ow, true⟩] ++
      ds.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def dbyte (a : Nat) : Option Nat := dbyteOf P.data a

def wmem : Memory := wmemOf OW BL P.data

/-- A call state of the example with arguments `r` (`X0`, `X1`, …). -/
def wstateMem (m : Memory) (e : Nat) (r : Nat → W64) : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 WG else if i = 30 then BitVec.ofNat 64 ret else r i,
    sp := BitVec.ofNat 64 WSP, pc := BitVec.ofNat 64 e,
    flags := ⟨false, false, false, false⟩, mem := m }

def wstate (e : Nat) (r : Nat → W64) : State := wstateMem wmem e r

theorem hret : RetAddr (P.link implAt) ret := RetAddr.of_check (by decide +kernel)

theorem wmem_data : P.DataLoaded wmem := by
  unfold Program.DataLoaded; decide +kernel

theorem wrt_data : DataOutside P wrt := by
  unfold DataOutside; simp only [wrt, outside_cons, outside_nil, and_true]; decide +kernel

/-- `PrintReady` looks only at `SP`, `g` and memory. -/
theorem ready_of {A : PrintGlobals} {rt : List (Nat × Nat)} {b a j : Nat} {s s' : State}
    (h1 : s'.sp = s.sp) (h2 : s'.regs 28 = s.regs 28) (h3 : s'.mem = s.mem) (h : PrintReady A rt b a j s) :
    PrintReady A rt b a j s' := by
  unfold PrintReady StackOK GuardOK at *; rw [h1, h2, h3]; exact h

theorem ready0 (above : Nat) (ha : above = 16 ∨ above = 24) :
    PrintReady ⟨PK, BI, BL, OW, DL⟩ wrt 1088 above 256 (wstate 0 fun _ => 0) := by
  rcases ha with rfl | rfl <;>
  · unfold PrintReady StackOK GuardOK
    simp only [sep_cons, sep_nil, and_true, wrt, outside_cons, outside_nil, InRanges, lockHeld, Apart,
      gM, gWritebuf, mLocks, mDying, mPrintlock, List.mem_cons, List.mem_nil_iff, or_false,
      exists_eq_or_imp, exists_eq_left]
    repeat' apply And.intro
    all_goals decide +kernel

theorem ready (e : Nat) (r : Nat → W64) (above : Nat) (ha : above = 16 ∨ above = 24) :
    PrintReady ⟨PK, BI, BL, OW, DL⟩ wrt 1088 above 256 (wstate e r) :=
  ready_of rfl rfl rfl (ready0 above ha)

end Witness

end PrintFn
