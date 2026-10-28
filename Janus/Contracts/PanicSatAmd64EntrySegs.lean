import Janus.Contracts.PanicSatAmd64EngineLoop


/-!
# The entry of the amd64 model engine: `gopanic`, `Goexit`, `deferreturn`

The segments of the entry code of the amd64 model engine (`docs/model/panic_model_amd64.s`): the
`_panic` push, the function-table search, `FOUND`/`SETUP` which write the loop's frame (96 bytes
below the entry `RSP`), and the entry of `deferreturn`. The x86-64 twin of the first half of
`Janus.Contracts.PanicSatEntry`.
-/

namespace Janus.Contracts.PanicSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.PanicAmd64 Janus.Contracts.PanicModel
open Janus.Spec.Map

set_option maxHeartbeats 0 in
/-- The entry of `gopanic`: the `_panic` for `v` is pushed. -/
theorem seg_gp_push (s : State) (k : Nat) (hpc : s.rip = BitVec.ofNat 64 eGopanic)
    (hB : s.mem.accessible B 0x1000 true = true) (hk : npan s.mem = k) (hk8 : k < 8) (hsp : (s.regs 4).toNat + 8 < 2 ^ 64) :
    ReachesRet qE (BitVec.ofNat 64 eLookup) s (fun d => d.regs 4 = s.regs 4 ∧ d.regs 5 = s.regs 5 ∧
      d.regs 14 = s.regs 14 ∧ d.xmm 15 = s.xmm 15 ∧ d.df = s.df ∧ d.regs 7 = 0 ∧
      MemFrame s.mem d.mem [(B, B + 8), (panAt k, panAt k + 32)] ∧
      npan d.mem = k + 1 ∧ rd d.mem (panAt k) = (s.regs 0).toNat ∧ rd d.mem (panAt k + 8) = (s.regs 3).toNat ∧
      rd d.mem (panAt k + 16) = (s.regs 4).toNat + 8 ∧ rd d.mem (panAt k + 24) = 0) := by
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  have hk' : s.mem.readLE 65536 8 = k := hk
  have hmul : (BitVec.ofNat 64 k <<< 5).toNat = 32 * k := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.shiftLeft_eq]; omega
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := s
  dsimp only at *
  simp only [eGopanic, eLookup, E, B, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus64_run [hk', hmul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [panAt, B]; janus_frame
  all_goals
    simp only [rd, panAt, B]
    model_simp
    try (apply Nat.mod_eq_of_lt; have := BitVec.isLt (cr 0); have := BitVec.isLt (cr 3); have := BitVec.isLt (cr 4); omega)

set_option maxHeartbeats 0 in
/-- The entry of `Goexit`: the `_panic` with `goexit` set is pushed. -/
theorem seg_ge_push (s : State) (k : Nat) (hpc : s.rip = BitVec.ofNat 64 eGoexit)
    (hB : s.mem.accessible B 0x1000 true = true) (hk : npan s.mem = k) (hk8 : k < 8)
    (hsp : (s.regs 4).toNat + 8 < 2 ^ 64) :
    ReachesRet qE (BitVec.ofNat 64 eLookup) s (fun d => d.regs 4 = s.regs 4 ∧ d.regs 5 = s.regs 5 ∧
      d.regs 14 = s.regs 14 ∧ d.xmm 15 = s.xmm 15 ∧ d.df = s.df ∧ d.regs 7 = 1 ∧
      MemFrame s.mem d.mem [(B, B + 8), (panAt k, panAt k + 32)] ∧
      npan d.mem = k + 1 ∧ rd d.mem (panAt k) = 0 ∧ rd d.mem (panAt k + 8) = 0 ∧
      rd d.mem (panAt k + 16) = (s.regs 4).toNat + 8 ∧ rd d.mem (panAt k + 24) = 1) := by
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  have hk' : s.mem.readLE 65536 8 = k := hk
  have hmul : (BitVec.ofNat 64 k <<< 5).toNat = 32 * k := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.shiftLeft_eq]; omega
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := s
  dsimp only at *
  simp only [eGoexit, eLookup, E, B, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus64_run [hk', hmul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [panAt, B]; janus_frame
  all_goals
    simp only [rd, panAt, B]
    model_simp
    try (apply Nat.mod_eq_of_lt; have := BitVec.isLt (cr 4); omega)

set_option maxHeartbeats 0 in
/-- The entry of `deferreturn`: the saved state is read and cleared, the loop's frame is written. -/
theorem seg_dr_entry (s : State) (hpc : s.rip = BitVec.ofNat 64 eDeferreturn)
    (hal : (s.regs 4).toNat % 8 = 0) (hsp : (s.regs 4).toNat + 8 ≤ 2 ^ 48) (h96 : 104 ≤ (s.regs 4).toNat)
    (hacc : s.mem.accessible ((s.regs 4).toNat - 104) 104 true = true)
    (hB : s.mem.accessible B 0x1000 true = true)
    (hspB : (s.regs 4).toNat + 8 ≤ B ∨ B + 0x1000 + 112 ≤ (s.regs 4).toNat + 8) :
    ReachesRet qE (BitVec.ofNat 64 eLH) s (fun c => c.rip = BitVec.ofNat 64 eLH ∧
      c.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 96) ∧ c.regs 5 = s.regs 5 ∧ c.regs 14 = s.regs 14 ∧
      c.xmm 15 = s.xmm 15 ∧ c.df = s.df ∧
      MemFrame s.mem c.mem [(B + 0x10, B + 0x18), ((s.regs 4).toNat - 96, (s.regs 4).toNat - 32)] ∧
      rd c.mem (B + 0x10) = 0 ∧
      c.mem.readLE ((s.regs 4).toNat - 96) 8 = (s.regs 4).toNat + 8 ∧
      c.mem.readLE ((s.regs 4).toNat - 96 + 8) 8 = (s.regs 4).toNat + 8 ∧
      c.mem.readLE ((s.regs 4).toNat - 96 + 16) 8 = 0 ∧ c.mem.readLE ((s.regs 4).toNat - 96 + 24) 8 = 2 ∧
      c.mem.readLE ((s.regs 4).toNat - 96 + 32) 8 = s.mem.readLE (B + 0x10) 8 ∧
      c.mem.readLE ((s.regs 4).toNat - 96 + 40) 8 = s.mem.readLE (B + 0x18) 8 ∧
      c.mem.readLE ((s.regs 4).toNat - 96 + 48) 8 = s.mem.readLE (B + 0x20) 8) := by
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  have hacc' : s.mem.accessible ((s.regs 4).toNat - 96) 64 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have hsp64 : (s.regs 4).toNat + 8 < 2 ^ 64 := by omega
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := s
  dsimp only at *
  simp only [eDeferreturn, eLH, E, B, Nat.reduceAdd] at hpc ⊢ hspB
  subst hpc
  janus64_run
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    have := (cr 4).isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · janus_frame

set_option maxHeartbeats 0 in
/-- The start of the function-table search. -/
theorem seg_lk_entry (c : State) (hpc : c.rip = BitVec.ofNat 64 eLookup)
    (hB : c.mem.accessible B 0x1000 true = true)
    (hra : c.mem.accessible (c.regs 4).toNat 8 false = true) (hsp : (c.regs 4).toNat + 8 ≤ 2 ^ 48) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x245)) c (fun d => d.mem = c.mem ∧ d.regs 4 = c.regs 4 ∧
      d.regs 5 = c.regs 5 ∧ d.regs 14 = c.regs 14 ∧ d.xmm 15 = c.xmm 15 ∧ d.df = c.df ∧ d.regs 7 = c.regs 7 ∧
      d.regs 1 = BitVec.ofNat 64 (c.mem.readLE (c.regs 4).toNat 8) ∧
      d.regs 9 = BitVec.ofNat 64 (c.mem.readLE (B + 0x28) 8) ∧ d.regs 10 = BitVec.ofNat 64 (tabAt 0)) := by
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [eLookup, E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus64_run

set_option maxHeartbeats 0 in
/-- The test of the table search's loop head: a non-zero count goes on. -/
theorem seg_lk_cbz (c : State) (r : Nat) (hpc : c.rip = BitVec.ofNat 64 (E + 0x245))
    (h9 : c.regs 9 = BitVec.ofNat 64 (r + 1)) (hr : r + 1 < 2 ^ 64) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x24a)) c (fun d => d.mem = c.mem ∧ d.regs = c.regs ∧
      d.xmm = c.xmm ∧ d.df = c.df) := by
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  have hnz : (BitVec.ofNat 64 (r + 1) = 0) = False := by
    apply eq_false; intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_ofNat] at this; omega
  janus64_run [h9, hnz]


set_option maxHeartbeats 0 in
/-- One step of the model's table search, entry found. -/
theorem seg_lk_found (c : State) (ptr e sz ra : Nat) (hpc : c.rip = BitVec.ofNat 64 (E + 0x24a))
    (h10 : c.regs 10 = BitVec.ofNat 64 ptr) (h1 : c.regs 1 = BitVec.ofNat 64 ra)
    (hp1 : ptr + 16 ≤ 2 ^ 48) (hacc : c.mem.accessible ptr 16 false = true)
    (he : c.mem.readLE ptr 8 = e) (hs : c.mem.readLE (ptr + 8) 8 = sz) (hovf : e + sz < 2 ^ 64)
    (hra : ra < 2 ^ 64) (hle : e ≤ ra) (hlt : ra < e + sz) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x26a)) c (fun d => d.mem = c.mem ∧ d.regs 4 = c.regs 4 ∧
      d.regs 5 = c.regs 5 ∧ d.regs 14 = c.regs 14 ∧ d.xmm 15 = c.xmm 15 ∧ d.df = c.df ∧ d.regs 7 = c.regs 7 ∧
      d.regs 10 = BitVec.ofNat 64 ptr ∧ d.regs 0 = BitVec.ofNat 64 e) := by
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus64_run [he, hs, h10, h1, Nat.not_lt.2 hle, hlt]

set_option maxHeartbeats 0 in
/-- One step of the model's table search, entry not matching: on to the next. -/
theorem seg_lk_next (c : State) (ptr e sz ra : Nat) (hpc : c.rip = BitVec.ofNat 64 (E + 0x24a))
    (h10 : c.regs 10 = BitVec.ofNat 64 ptr) (h1 : c.regs 1 = BitVec.ofNat 64 ra)
    (hp1 : ptr + 16 ≤ 2 ^ 48) (hacc : c.mem.accessible ptr 16 false = true)
    (he : c.mem.readLE ptr 8 = e) (hs : c.mem.readLE (ptr + 8) 8 = sz) (hovf : e + sz < 2 ^ 64)
    (hra : ra < 2 ^ 64) (hn : ra < e ∨ e + sz ≤ ra) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x245)) c (fun d => d.mem = c.mem ∧ d.regs 4 = c.regs 4 ∧
      d.regs 5 = c.regs 5 ∧ d.regs 14 = c.regs 14 ∧ d.xmm 15 = c.xmm 15 ∧ d.df = c.df ∧ d.regs 7 = c.regs 7 ∧
      d.regs 9 = c.regs 9 - 1 ∧ d.regs 10 = c.regs 10 + 56 ∧ d.regs 1 = c.regs 1) := by
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  rcases hn with hn | hn
  · janus64_run [he, hs, h10, h1, hn]
  · janus64_run [he, hs, h10, h1, (show ¬ ra < e by omega), (show ¬ ra < e + sz by omega)]

set_option maxHeartbeats 0 in
/-- `FOUND`/`SETUP` for a function without open-coded defers. -/
theorem seg_found_noopen (c : State) (j fr dr entry : Nat) (hpc : c.rip = BitVec.ofNat 64 (E + 0x26a))
    (h10 : c.regs 10 = BitVec.ofNat 64 (tabAt j)) (h0 : c.regs 0 = BitVec.ofNat 64 entry)
    (hal : (c.regs 4).toNat % 8 = 0) (hsp : (c.regs 4).toNat + 8 ≤ 2 ^ 48) (h96 : 104 ≤ (c.regs 4).toNat)
    (hacc : c.mem.accessible ((c.regs 4).toNat - 104) 104 true = true)
    (hB : c.mem.accessible B 0x1000 true = true) (hj : j < 16)
    (hfr : c.mem.readLE (tabAt j + 16) 8 = fr) (hdr : c.mem.readLE (tabAt j + 24) 8 = dr)
    (hop : c.mem.readLE (tabAt j + 32) 8 = 0) (hf64 : (c.regs 4).toNat + 8 + fr < 2 ^ 64)
    (hd64 : entry + dr < 2 ^ 64) (hent : entry < 2 ^ 64) :
    ReachesRet qE (BitVec.ofNat 64 eLH) c (fun d => d.rip = BitVec.ofNat 64 eLH ∧
      d.regs 4 = BitVec.ofNat 64 ((c.regs 4).toNat - 96) ∧ d.regs 5 = c.regs 5 ∧ d.regs 14 = c.regs 14 ∧
      d.xmm 15 = c.xmm 15 ∧ d.df = c.df ∧
      MemFrame c.mem d.mem [((c.regs 4).toNat - 96, (c.regs 4).toNat - 32)] ∧
      d.mem.readLE ((c.regs 4).toNat - 96) 8 = (c.regs 4).toNat + 8 ∧
      d.mem.readLE ((c.regs 4).toNat - 96 + 8) 8 = (c.regs 4).toNat + 8 + fr ∧
      d.mem.readLE ((c.regs 4).toNat - 96 + 16) 8 = entry + dr ∧
      d.mem.readLE ((c.regs 4).toNat - 96 + 24) 8 = (c.regs 7).toNat ∧
      d.mem.readLE ((c.regs 4).toNat - 96 + 32) 8 = 0) := by
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  have hacc' : c.mem.accessible ((c.regs 4).toNat - 96) 64 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [eLH, E, B, Nat.reduceAdd] at hpc ⊢
  subst hpc
  simp only [tabAt, B] at hfr hdr hop h10
  janus64_run [hfr, hdr, hop, h10, h0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    have := (cr 4).isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · janus_frame
  · omega
  · omega

set_option maxHeartbeats 0 in
/-- `FOUND`/`SETUP` for a function with open-coded defers (offsets `o1` of the `deferBits` byte and
`o2` of the first slot below `varp`). -/
theorem seg_found_open (c : State) (j fr dr entry o1 o2 b ph : Nat) (hpc : c.rip = BitVec.ofNat 64 (E + 0x26a))
    (h10 : c.regs 10 = BitVec.ofNat 64 (tabAt j)) (h0 : c.regs 0 = BitVec.ofNat 64 entry)
    (hal : (c.regs 4).toNat % 8 = 0) (hsp : (c.regs 4).toNat + 8 ≤ 2 ^ 48) (h96 : 104 ≤ (c.regs 4).toNat)
    (hacc : c.mem.accessible ((c.regs 4).toNat - 104) 104 true = true)
    (hB : c.mem.accessible B 0x1000 true = true) (hj : j < 16)
    (hfr : c.mem.readLE (tabAt j + 16) 8 = fr) (hdr : c.mem.readLE (tabAt j + 24) 8 = dr)
    (hop : c.mem.readLE (tabAt j + 32) 8 = 1) (ho1 : c.mem.readLE (tabAt j + 40) 8 = o1)
    (ho2 : c.mem.readLE (tabAt j + 48) 8 = o2) (hf64 : (c.regs 4).toNat + 8 + fr < 2 ^ 64)
    (hd64 : entry + dr < 2 ^ 64) (hent : entry < 2 ^ 64) (hfr8 : 8 ≤ fr) (ho1' : o1 ≤ fr - 8)
    (ho2' : o2 ≤ fr - 8)
    (hba : c.mem.accessible ((c.regs 4).toNat + fr - o1) 1 false = true)
    (hb : c.mem.readLE ((c.regs 4).toNat + fr - o1) 1 = b) (hphd : (b = 0 ∧ ph = 0) ∨ (b ≠ 0 ∧ ph = 1)) :
    ReachesRet qE (BitVec.ofNat 64 eLH) c (fun d => d.rip = BitVec.ofNat 64 eLH ∧
      d.regs 4 = BitVec.ofNat 64 ((c.regs 4).toNat - 96) ∧ d.regs 5 = c.regs 5 ∧ d.regs 14 = c.regs 14 ∧
      d.xmm 15 = c.xmm 15 ∧ d.df = c.df ∧
      MemFrame c.mem d.mem [((c.regs 4).toNat - 96, (c.regs 4).toNat - 32)] ∧
      d.mem.readLE ((c.regs 4).toNat - 96) 8 = (c.regs 4).toNat + 8 ∧
      d.mem.readLE ((c.regs 4).toNat - 96 + 8) 8 = (c.regs 4).toNat + 8 + fr ∧
      d.mem.readLE ((c.regs 4).toNat - 96 + 16) 8 = entry + dr ∧
      d.mem.readLE ((c.regs 4).toNat - 96 + 24) 8 = (c.regs 7).toNat ∧
      d.mem.readLE ((c.regs 4).toNat - 96 + 32) 8 = ph ∧
      d.mem.readLE ((c.regs 4).toNat - 96 + 40) 8 = (c.regs 4).toNat + fr - o1 ∧
      d.mem.readLE ((c.regs 4).toNat - 96 + 48) 8 = (c.regs 4).toNat + fr - o2) := by
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  have hacc' : c.mem.accessible ((c.regs 4).toNat - 96) 64 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [eLH, E, B, Nat.reduceAdd] at hpc ⊢
  subst hpc
  simp only [tabAt, B] at hfr hdr hop ho1 ho2 h10
  have hadr : (18446744073709551616 - (8 + o1) + (fr + (BitVec.toNat (cr 4) + 8))) % 18446744073709551616 =
      BitVec.toNat (cr 4) + fr - o1 := by omega
  have hb' : cm.readLE ((18446744073709551616 - (8 + o1) + (fr + (BitVec.toNat (cr 4) + 8))) % 18446744073709551616) 1 = b := by
    rw [hadr]; exact hb
  have hba' : cm.accessible ((18446744073709551616 - (8 + o1) + (fr + (BitVec.toNat (cr 4) + 8))) % 18446744073709551616) 1 false = true := by
    rw [hadr]; exact hba
  have hb256 : b < 256 := by rw [← hb]; simpa using Janus.Arm64.Memory.readLE_lt cm (BitVec.toNat (cr 4) + fr - o1) 1
  rcases hphd with ⟨hb0, rfl⟩ | ⟨hb0, rfl⟩
  · subst hb0
    janus64_run [hfr, hdr, hop, ho1, ho2, h10, h0, hb, hb']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      have := (cr 4).isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · janus_frame
    · omega
    · omega
    · omega
    · omega
  · have hnz := nz8 b hb256 (by omega)
    janus64_run [hfr, hdr, hop, ho1, ho2, h10, h0, hb, hb', hnz]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      have := (cr 4).isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · janus_frame
    · omega
    · omega
    · omega
    · omega

end Janus.Contracts.PanicSatAmd64
