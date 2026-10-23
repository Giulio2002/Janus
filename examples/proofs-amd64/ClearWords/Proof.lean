import Janus
import Extracted

/-! `example.com/basic.ClearWords(b []uint64)` on amd64: `clear(b)`, which the compiler lowers
to a call of `runtime.memclrNoHeapPointers(ptr, 8 * len(b))` (skipped when `len(b) = 0`).

`memclrNoHeapPointers` (Go 1.26, `runtime/memclr_amd64.s`) is proved for every length. From
its loop head `top` (`TESTQ BX, BX`) it

* clears `n ≤ 256` bytes with straight-line, possibly overlapping stores from both ends
  (`MOVB`/`MOVW`/`MOVL`/`MOVQ` of `AX = 0`, `MOVDQU` of `X15 = 0`) and returns;
* for `n > 256` reads `internal/cpu.X86.HasERMS`: with ERMS and `n ≥ 2048` it clears
  `8 * (n / 8)` bytes with `REP STOSQ` and goes back to `top` with `n % 8`; otherwise it runs
  the 256-byte `MOVDQU` loop `sseLoop` and goes back to `top` with `n mod 256` left;
* reads `internal/cpu.X86.HasAVX2` on both paths and takes a VEX (AVX2) path when it is 1.

The feature bytes live in `.noptrbss` (written by Go at start-up from `CPUID`), so the
extractor does not copy them: the precondition makes them readable, assumes `HasAVX2 ≠ 1`
(the VEX path is not modelled) and quantifies over `HasERMS`. The proof is a strong induction
on the remaining length, with both loop heads in one statement. Memory is summarised by
`Zeroed M M' d n` (`M'` is `M` with `[d, d + n)` zeroed). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `memclrNoHeapPointers`: the loop head (`TESTQ BX, BX`). These addresses are also written
as numerals in the `janus64_run until [...]` lists and the `facts` below. -/
def top : Nat := 0x47d446
/-- `memclrNoHeapPointers`: the 256-byte `MOVDQU X15` loop. -/
def sseLoop : Nat := 0x47d4ce
/-- `memclrNoHeapPointers`: `REP STOSQ`. -/
def repSite : Nat := 0x47d5d9
/-- `ClearWords`: the instruction after `CALL runtime.memclrNoHeapPointers`. -/
def retSite : Nat := 0x4897c5
/-- `internal/cpu.X86.HasAVX2` (`internal/cpu.X86+68`, `.noptrbss`). -/
def hasAVX2 : Nat := 0x576984
/-- `internal/cpu.X86.HasERMS` (`internal/cpu.X86+85`, `.noptrbss`). -/
def hasERMS : Nat := 0x576995

/-- What holds at both loop heads of `memclrNoHeapPointers`, while clearing `[d0, d0 + n)`
of the memory `M0`: `DI = d`, `BX = m` bytes are left, `[d0, d)` is already zero, `AX = 0`,
`X15 = 0`, and `RSP`, `RBP`, `g` are the caller's. -/
def Inv (M0 : Memory) (d0 n : Nat) (R B G : BitVec 64) (t : State) (d m : Nat) : Prop :=
  t.regs 7 = BitVec.ofNat 64 d ∧ t.regs 3 = BitVec.ofNat 64 m ∧ t.regs 0 = 0 ∧ t.xmm 15 = 0 ∧
    t.regs 4 = R ∧ t.regs 5 = B ∧ t.regs 14 = G ∧ d0 ≤ d ∧ d + m = d0 + n ∧
    Zeroed M0 t.mem d0 (d - d0)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `memclrNoHeapPointers` from either loop head clears the rest of `[d0, d0 + n)` and
returns to `retSite`, for every value of `HasERMS` and with `HasAVX2 ≠ 1`, provided the range
is writable and disjoint from the return-address slot and the feature bytes. -/
theorem clear_loop (ret : Nat) (hret : RetAddr Extracted.program ret) (Q : Outcome → Prop)
    (M0 : Memory) (d0 n : Nat) (R B G : BitVec 64) (hn : d0 + n ≤ 2 ^ 48)
    (hacc : M0.accessible d0 n true = true) (hR : M0.accessible R.toNat 8 false = true)
    (hRd : d0 + n ≤ R.toNat ∨ R.toNat + 8 ≤ d0) (hra : M0.readLE R.toNat 8 = retSite)
    (hav : M0.accessible hasAVX2 1 false = true) (hav1 : M0.readLE hasAVX2 1 ≠ 1)
    (her : M0.accessible hasERMS 1 false = true) (hfd : d0 + n ≤ hasAVX2 ∨ hasERMS + 1 ≤ d0)
    (hk : ∀ t', t'.rip = BitVec.ofNat 64 retSite → t'.regs 4 = R + 8 → t'.regs 5 = B →
      t'.regs 14 = G → t'.xmm 15 = 0 → Zeroed M0 t'.mem d0 n →
      Reaches (Extracted.program.withExit ret) t' Q) :
    ∀ m, (∀ t d, t.rip = BitVec.ofNat 64 sseLoop → 256 ≤ m → Inv M0 d0 n R B G t d m →
        Reaches (Extracted.program.withExit ret) t Q) ∧
      (∀ t d, t.rip = BitVec.ofNat 64 top → Inv M0 d0 n R B G t d m →
        Reaches (Extracted.program.withExit ret) t Q) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  simp only [top, sseLoop, retSite, hasAVX2, hasERMS] at *
  have hR' : R.toNat < 2 ^ 64 := R.isLt
  -- the facts about the current memory, from those about `M0`
  have facts : ∀ (t : State) d, Inv M0 d0 n R B G t d m →
      t.mem.accessible d m true = true ∧ t.mem.accessible R.toNat 8 false = true ∧
      t.mem.readLE R.toNat 8 = 4757445 ∧ t.mem.accessible 5728644 1 false = true ∧
      t.mem.readLE 5728644 1 ≠ 1 ∧ t.mem.accessible 5728661 1 false = true := by
    intro t d ⟨_, _, _, _, _, _, _, hd0, hdm, hz⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hz.accessible]; exact accessible_sub hacc (by decide) (by omega) (by omega)
    · rw [hz.accessible]; exact hR
    · rw [hz.readLE_outside (by omega)]; exact hra
    · rw [hz.accessible]; exact hav
    · rw [hz.readLE_outside (by omega)]; exact hav1
    · rw [hz.accessible]; exact her
  have hsse : ∀ t d, t.rip = BitVec.ofNat 64 0x47d4ce → 256 ≤ m → Inv M0 d0 n R B G t d m →
      Reaches (Extracted.program.withExit ret) t Q := by
    intro t d h_rip hm hinv
    obtain ⟨hacc', hR'', hra', hav', hav1', her'⟩ := facts t d hinv
    obtain ⟨h7, h3, h0, hx, h4, h5, h14, hd0, hdm, hz⟩ := hinv
    have hm64 : m < 2 ^ 64 := by omega
    janus64_run until [0x47d446, 0x47d4ce]
    -- 512 or more left: once more round the loop; less: back to the head
    all_goals first
      | (refine (ih (m - 256) (by omega)).1 _ (d + 256) rfl (by omega) ⟨by bvn, by bvn,
          by simp [setRegF, h0], hx, by simp [setRegF, h4], by simp [setRegF, h5],
          by simp [setRegF, h14], by omega, by omega, ?_⟩
         refine Zeroed.congr (hz.trans (j := 256) ?_) rfl (by omega)
         zeroed_writes)
      | (refine (ih (m - 256) (by omega)).2 _ (d + 256) rfl ⟨by bvn, by bvn,
          by simp [setRegF, h0], hx, by simp [setRegF, h4], by simp [setRegF, h5],
          by simp [setRegF, h14], by omega, by omega, ?_⟩
         refine Zeroed.congr (hz.trans (j := 256) ?_) rfl (by omega)
         zeroed_writes)
  refine ⟨hsse, ?_⟩
  intro t d h_rip hinv
  obtain ⟨hacc', hR'', hra', hav', hav1', her'⟩ := facts t d hinv
  have hinv' := hinv
  obtain ⟨h7, h3, h0, hx, h4, h5, h14, hd0, hdm, hz⟩ := hinv
  have hm64 : m < 2 ^ 64 := by omega
  janus64_run until [0x47d446, 0x47d4ce, 0x47d5d9, 4757445]
  all_goals first
    | -- a straight-line case returned to `ClearWords`
      (refine hk _ rfl (by simp [setRegF, h4]) (by simp [setRegF, h5]) (by simp [setRegF, h14])
        hx ?_
       refine Zeroed.congr (hz.trans (j := m) ?_) rfl (by omega)
       zeroed_writes)
    | -- `m > 256`: the 256-byte loop, with the same `m`
      (exact hsse _ d rfl (by omega) hinv')
    | -- `m ≥ 2048` with ERMS: `REP STOSQ` of `m / 8` words, then back to the head
      (refine Reaches.repStos hret (c := 0x47d5d9) (len := 3) (w := 64) rfl rfl d (m / 8)
        (by simp [setRegF, h7]) (by simp [setRegF, bv_ushiftRight_ofNat m 3 hm64]) (by omega)
        (by exact accessible_sub hacc' (by decide) (by omega) (by omega))
        (by omega) ?_
       janus64_run until [0x47d446]
       refine (ih (m % 8) (by omega)).2 _ (d + 8 * (m / 8)) rfl ⟨by bvn,
         by bvn, by simp [setRegF, h0],
         by simpa using hx, by simp [setRegF, h4], by simp [setRegF, h5], by simp [setRegF, h14],
         by omega, by omega, ?_⟩
       refine Zeroed.congr (hz.trans (j := 8 * (m / 8)) ?_) rfl (by omega)
       exact (zeroed_fillLE t.mem d 8 (m / 8)).congr (by omega) rfl)

/-- `clear_loop` entered at `top` from the call: nothing is zeroed yet. -/
theorem clear_from_top (ret : Nat) (hret : RetAddr Extracted.program ret) (Q : Outcome → Prop)
    (t : State) (d n : Nat) (h_rip : t.rip = BitVec.ofNat 64 top)
    (h7 : t.regs 7 = BitVec.ofNat 64 d) (h3 : t.regs 3 = BitVec.ofNat 64 n) (h0 : t.regs 0 = 0)
    (hx : t.xmm 15 = 0) (hn : d + n ≤ 2 ^ 48) (hacc : t.mem.accessible d n true = true)
    (hR : t.mem.accessible (t.regs 4).toNat 8 false = true)
    (hRd : d + n ≤ (t.regs 4).toNat ∨ (t.regs 4).toNat + 8 ≤ d)
    (hra : t.mem.readLE (t.regs 4).toNat 8 = retSite)
    (hav : t.mem.accessible hasAVX2 1 false = true) (hav1 : t.mem.readLE hasAVX2 1 ≠ 1)
    (her : t.mem.accessible hasERMS 1 false = true) (hfd : d + n ≤ hasAVX2 ∨ hasERMS + 1 ≤ d)
    (hk : ∀ t', t'.rip = BitVec.ofNat 64 retSite → t'.regs 4 = t.regs 4 + 8 →
      t'.regs 5 = t.regs 5 → t'.regs 14 = t.regs 14 → t'.xmm 15 = 0 → Zeroed t.mem t'.mem d n →
      Reaches (Extracted.program.withExit ret) t' Q) :
    Reaches (Extracted.program.withExit ret) t Q :=
  (clear_loop ret hret Q t.mem d n (t.regs 4) (t.regs 5) (t.regs 14) hn hacc hR hRd hra hav hav1
    her hfd hk n).2 t d h_rip
    ⟨h7, h3, h0, hx, rfl, rfl, rfl, Nat.le_refl _, rfl, (Zeroed.refl t.mem d).congr rfl (by omega)⟩

/-- `ClearWords(b)` zeroes the `len(b)` words of `b` and changes no other memory outside its
own stack frame (`[RSP - 32, RSP + 16)`: the saved frame pointer, the return address of the
call, and the spill slot of `b.ptr`).

Assumptions: the words are writable, below `2^48`, and disjoint from that stack area and from
the two CPU-feature bytes `memclrNoHeapPointers` reads; the feature bytes are readable and
`internal/cpu.X86.HasAVX2 ≠ 1` (every value of `HasERMS` is covered); and the stack check of
the prologue passes. -/
theorem correctness (b len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [b, len, cap]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 32 16 ∧ Buffer s b (8 * len.toNat) true ∧
        (b.toNat + 8 * len.toNat ≤ (s.regs regSP).toNat - 32 ∨
          (s.regs regSP).toNat + 16 ≤ b.toNat) ∧
        s.mem.accessible hasAVX2 1 false = true ∧ s.mem.readLE hasAVX2 1 ≠ 1 ∧
        s.mem.accessible hasERMS 1 false = true ∧
        (b.toNat + 8 * len.toNat ≤ hasAVX2 ∨ hasERMS + 1 ≤ b.toNat) ∧
        (hasERMS + 1 ≤ (s.regs regSP).toNat - 32 ∨ (s.regs regSP).toNat + 16 ≤ hasAVX2))
      (fun s s' => (∀ j, j < len.toNat → s'.mem.readLE (b.toNat + 8 * j) 8 = 0) ∧
        ∀ x, (x < b.toNat ∨ b.toNat + 8 * len.toNat ≤ x) →
          (x < (s.regs regSP).toNat - 32 ∨ (s.regs regSP).toNat + 16 ≤ x) →
          s'.mem.bytes x = s.mem.bytes x) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, ⟨hle, hnw, hacc⟩, ⟨hbw, hb⟩, hbd, hav, hav1, her, hfd, hfs⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, hasAVX2, hasERMS] at *
  have hsp := (s.regs 4).isLt
  have e32 : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run until [0x47d446]
  · -- `len(b) = 0`: no call
    refine ⟨fun j hj => absurd hj (by omega), fun x h1 h2 => ?_⟩
    rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega),
      Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]
  · refine clear_from_top ret hret _ _ b.toNat (8 * len.toNat) rfl (by simp [setRegF]) (by bvn)
      (by simp [setRegF]) (by simpa using h_x15) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp only [hasAVX2, hasERMS]; omega) ?_
    all_goals
      simp (config := { decide := true }) only [setRegF, ↓reduceIte, e32, hasAVX2, hasERMS,
        Janus.Arm64.Memory.accessible_writeLE]
    · exact hb
    · exact accessible_sub hacc (by decide) (by omega) (by omega)
    · omega
    · rw [Janus.Arm64.Memory.readLE_writeLE_self]; rfl
    · exact hav
    · rw [readLE_writeLE_disjoint _ _ (by omega), readLE_writeLE_disjoint _ _ (by omega),
        readLE_writeLE_disjoint _ _ (by omega)]; exact hav1
    · exact her
    · -- back in `ClearWords` after the call: `ADDQ $0x10, SP ; POPQ BP ; RET`
      intro t' hrip h4' h5' h14' hx' hz'
      simp only [retSite] at hrip
      have hbp : t'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        rw [hz'.readLE_outside (by omega), readLE_writeLE_disjoint _ _ (by omega),
          readLE_writeLE_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
          Nat.mod_eq_of_lt (s.regs 5).isLt]
      have hrt : t'.mem.readLE (s.regs 4).toNat 8 = ret := by
        rw [hz'.readLE_outside (by omega), readLE_writeLE_disjoint _ _ (by omega),
          readLE_writeLE_disjoint _ _ (by omega), readLE_writeLE_disjoint _ _ (by omega), h_ret]
      have hacc' : t'.mem.accessible ((s.regs 4).toNat - 32) (32 + 16) true = true := by
        rw [hz'.accessible]; simpa using hacc
      janus64_run
      refine ⟨rfl, fun j hj => hz'.readLE (by omega) (by omega), fun x h1 h2 => ?_⟩
      rw [hz'.2 x, ite_eq_right (by omega), Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega),
        Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega),
        Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]

end Proof
