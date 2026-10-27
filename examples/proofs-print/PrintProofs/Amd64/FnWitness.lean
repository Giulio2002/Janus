import PrintProofs.Amd64.FnHead
import Janus.Contracts.PrintSatAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

namespace PrintFn

/-! ## Non-vacuity: code for the three contracts and a call state (amd64)

`Janus.Amd64.Print.Sat`'s witness code (`lock2Code`, `unlock2Code`, `memmoveCode`, proved there
against the contracts on a toy program) linked at the contract addresses of this binary, proved
again here against the contracts for the linked program; the runtime-owned ranges `wrt` (the mutex
key and `m.locks`); and a memory `wmem` holding the read-only data, a stack, `g` and its M, the TLS
slot holding `g`, and the print globals (zero: not panicking, backlog index 0, no `overrideWrite`,
`debuglock` free). Each example's `Witness.nonvacuous` builds its call state on it. -/

namespace Witness

open Janus.Amd64.Print.Sat

def L2 : Nat := P.contractAddr "runtime.lock2"
def U2 : Nat := P.contractAddr "runtime.unlock2"
def MM : Nat := P.contractAddr "runtime.memmove"

/-- The witness code at the given contract addresses. -/
def implAtOf (l2 u2 mm : Nat) : List Amd64.Segment :=
  [⟨"lock2", l2, lock2Code⟩, ⟨"unlock2", u2, unlock2Code⟩, ⟨"memmove", mm, memmoveCode⟩]

def implAt : List Amd64.Segment := implAtOf L2 U2 MM

/-- The program linked with it, as a closed program. -/
def linked : Amd64.Program := { P with segments := P.segments ++ implAt }

theorem linked_eq : P.link implAt = linked := rfl

set_option maxHeartbeats 4000000 in
theorem lock2_model (rt : List (Nat × Nat)) (stack : Nat) :
    Lock2Contract (P.link implAt) (P.contractAddr "runtime.lock2") rt stack := by
  rw [linked_eq]
  intro s hpc ⟨hc, ⟨hl1, hl2, hin1, hg1, hg2, hgo, hm1, hm2, hin2, hap, hlo, hhi, hsp⟩, hfree⟩
  simp only [mLocksOf, gM, mLocks] at *
  have hd1 := hin1.disjoint hgo
  have hd2 := hin2.disjoint hgo
  have hd3 := hin1.disjoint hsp
  have hd4 := hin2.disjoint hsp
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hc
  unfold Apart at hap
  janus64_run
  refine ⟨0, _, _, _, _, _, _, _, by ret_state64 [], by janus_frame, ?_, ?_⟩
  all_goals (try unfold lockHeld)
  all_goals janus64_simp
  all_goals omega

set_option maxHeartbeats 4000000 in
theorem unlock2_model (rt : List (Nat × Nat)) (stack : Nat) :
    Unlock2Contract (P.link implAt) (P.contractAddr "runtime.unlock2") rt stack := by
  rw [linked_eq]
  intro s hpc ⟨hc, ⟨hl1, hl2, hin1, hg1, hg2, hgo, hm1, hm2, hin2, hap, hlo, hhi, hsp⟩, hheld⟩
  simp only [mLocksOf, gM, mLocks] at *
  have hd1 := hin1.disjoint hgo
  have hd2 := hin2.disjoint hgo
  have hd3 := hin1.disjoint hsp
  have hd4 := hin2.disjoint hsp
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hc
  unfold Apart at hap
  janus64_run
  refine ⟨0, _, _, _, _, _, _, _, by ret_state64 [], by janus_frame, ?_, ?_⟩
  all_goals (try unfold lockHeld)
  all_goals janus64_simp
  all_goals omega

/-- The byte loop of `memmoveCode`: from the loop head with `k` bytes left, the rest is copied. -/
theorem mm_loop (s0 : State) (hc : CallOK64 s0 0 0)
    (D Sr N : Nat) (hD : D + N ≤ 2 ^ 48) (hS : Sr + N ≤ 2 ^ 48)
    (hwd : s0.mem.accessible D N true = true) (hrs : s0.mem.accessible Sr N false = true)
    (hdisj : D + N ≤ Sr ∨ Sr + N ≤ D)
    (hsp : (s0.regs 4).toNat + 8 ≤ D ∨ D + N ≤ (s0.regs 4).toNat) :
    ∀ k (S : State), 0 < k → k ≤ N →
      S.rip = BitVec.ofNat 64 (MM + 5) → S.regs 0 = BitVec.ofNat 64 (D + (N - k)) →
      S.regs 3 = BitVec.ofNat 64 (Sr + (N - k)) → S.regs 1 = BitVec.ofNat 64 k →
      S.regs 4 = s0.regs 4 → S.fsBase = s0.fsBase → S.df = s0.df → S.mxcsr = s0.mxcsr → S.x87 = s0.x87 → S.fpucw = s0.fpucw →
      S.xmm 15 = s0.xmm 15 → S.regs 5 = s0.regs 5 → S.regs 14 = s0.regs 14 →
      MemFrame s0.mem S.mem [(D, D + N)] →
      readBytes S.mem D (N - k) = readBytes s0.mem Sr (N - k) →
      ReachesRet linked (retAddrOf s0) S (fun s' =>
        ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256) (kr : Nat → W64),
          s' = retState64 s0 junk [] f x yh m zh kr ∧ MemFrame s0.mem m [(D, D + N)] ∧
          readBytes m D N = readBytes s0.mem Sr N) := by
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hc
  intro k
  induction k with
  | zero => intro S hk; omega
  | succ k ih =>
    intro S _ hk hpc h0 h1 h2 h4 hfs hdf hmx hx87 hfw hx15 h5 h14 hf hrb
    have hrb' := Janus.Print.Sat.readBytes_copy_step S.mem s0.mem D Sr (N - (k + 1)) hrb
    rw [show N - (k + 1) + 1 = N - k by omega] at hrb'
    by_cases hk0 : k = 0
    · subst hk0
      janus64_run
      refine ⟨_, _, _, _, _, _, _, by ret_state64 [h4, h5, h14, hfs, hdf, hmx, hx87, hfw, hx15], by janus_frame, ?_⟩
      have hb8 := (s0.mem.bytes (Sr + (N - 1))).isLt
      simpa [Nat.mod_eq_of_lt (show (s0.mem.bytes (Sr + (N - 1))).toNat < 18446744073709551616 by omega)] using hrb'
    · janus64_run until [MM + 5]
      refine ih _ (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals try (simp only [setRegF_apply]; first | assumption | rfl)
      all_goals try (apply BitVec.eq_of_toNat_eq; simp [setRegF]; omega)
      all_goals try janus_frame
      all_goals (try dsimp only)
      have hb8 := (s0.mem.bytes (Sr + (N - (k + 1)))).isLt
      all_goals simpa [Nat.mod_eq_of_lt (show (s0.mem.bytes (Sr + (N - (k + 1)))).toNat < 18446744073709551616 by omega)] using hrb'

set_option maxHeartbeats 4000000 in
theorem memmove_model : MemmoveContract (P.link implAt) (P.contractAddr "runtime.memmove") := by
  rw [linked_eq]
  intro s hpc ⟨hc, hD, hS, hwd, hrs, hdisj, hsp⟩
  have hc' := hc
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hc
  by_cases hN : (s.regs 1).toNat = 0
  · janus64_run
    refine ⟨_, _, _, _, _, _, _, by ret_state64 [], ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
    simp [readBytes]
  · janus64_run until [MM + 5]
    refine mm_loop s hc' _ _ _ hD hS hwd hrs hdisj hsp (s.regs 1).toNat _ (by omega) (Nat.le_refl _)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try dsimp only)
    all_goals first
      | rfl
      | exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
      | (simp only [Nat.sub_self]; rfl)
      | (simp; done)


/-- The witness goroutine, its M, the TLS slot, the stack pointer and the return address. -/
def WG : Nat := 0x50000
def WM : Nat := 0x51000
def WTL : Nat := 0x60000
def WSP : Nat := 0x48000
def ret : Nat := 0x200000

/-- The runtime-owned ranges: the mutex key `debuglock` and `m.locks`. -/
def wrt : List (Nat × Nat) := [(DL, DL + 8), (WM + 264, WM + 268)]

/-- The byte of the read-only data `ds` at `a`, if any. -/
def dbyteOf (ds : List DataSegment) (a : Nat) : Option Nat :=
  ds.findSome? fun d => if d.base ≤ a ∧ a < d.base + d.bytes.length then d.bytes[a - d.base]? else none

/-- The witness memory: the read-only data (read-only regions), `g.m = WM` (`g` read-only), the M,
the TLS slot (holding `g`), the print globals' range (from `runtime.overrideWrite` to the end of
`printBacklog`) and the stack (writable, with the return address `ret` at `[WSP]`); every other
byte 0. -/
def wmemOf (ow bl : Nat) (ds : List DataSegment) : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((dbyteOf ds a).getD
      (if a = WG + 49 then 0x10 else if a = WG + 50 then 0x05 else if a = WTL + 2 then 0x05
        else if a = WSP + 2 then 0x20 else 0)),
    [⟨WG, 0x100, false⟩, ⟨WM, 0x200, true⟩, ⟨WSP - 0x8000, 0x10000, true⟩, ⟨WTL, 8, false⟩,
      ⟨ow, bl + 512 - ow, true⟩] ++ ds.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def dbyte (a : Nat) : Option Nat := dbyteOf P.data a

def wmem : Memory := wmemOf OW BL P.data

/-- A call state with arguments `r` (`RAX`, `RBX`, …) at entry `e`. -/
def wstateMem (m : Memory) (e : Nat) (r : Nat → W64) : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 WSP else if i = 14 then BitVec.ofNat 64 WG else r i,
    rip := BitVec.ofNat 64 e, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := m, fsBase := BitVec.ofNat 64 (WTL + 8) }

def wstate (e : Nat) (r : Nat → W64) : State := wstateMem wmem e r

theorem hret : RetAddr (P.link implAt) ret := RetAddr.of_check (by decide +kernel)

theorem wmem_data : Amd64.Program.DataLoaded P wmem := by
  unfold Amd64.Program.DataLoaded; decide +kernel

theorem wrt_data : Amd64.Print.DataOutside P wrt := by
  unfold Amd64.Print.DataOutside; simp only [wrt, outside_cons, outside_nil, and_true]; decide +kernel

/-- `PrintReady` looks only at `SP`, `g`, the TLS base and memory. -/
theorem ready_of {A : PrintGlobals} {rt : List (Nat × Nat)} {b a j : Nat} {s s' : State}
    (h1 : s'.regs 4 = s.regs 4) (h2 : s'.regs 14 = s.regs 14) (h3 : s'.mem = s.mem)
    (h4 : s'.fsBase = s.fsBase) (h : Amd64.Print.PrintReady A rt b a j s) : Amd64.Print.PrintReady A rt b a j s' := by
  unfold Amd64.Print.PrintReady at *; rw [h1, h2, h3, h4]; exact h

theorem ready0 (above : Nat) (ha : above = 8 ∨ above = 16 ∨ above = 24) :
    Amd64.Print.PrintReady ⟨PK, BI, BL, OW, DL⟩ wrt 1088 above 256 (wstate 0 fun _ => 0) := by
  rcases ha with rfl | rfl | rfl <;>
  · unfold Amd64.Print.PrintReady
    simp only [sep_cons, sep_nil, and_true, wrt, outside_cons, outside_nil, InRanges, lockHeld, Apart,
      gM, gWritebuf, mLocks, mDying, mPrintlock, List.mem_cons, List.mem_nil_iff, or_false,
      exists_eq_or_imp, exists_eq_left]
    repeat' apply And.intro
    all_goals decide +kernel

theorem ready (e : Nat) (r : Nat → W64) (above : Nat) (ha : above = 8 ∨ above = 16 ∨ above = 24) :
    Amd64.Print.PrintReady ⟨PK, BI, BL, OW, DL⟩ wrt 1088 above 256 (wstate e r) :=
  ready_of rfl rfl rfl rfl (ready0 above ha)

end Witness

end PrintFn
