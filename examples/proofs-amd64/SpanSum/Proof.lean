import Janus
import Extracted

/-!
# `SpanSum(lo, hi uint64) uint64` on amd64: range over a non-inlined function iterator

**Guarantee.** For all 64-bit `lo`, `hi` and every Go call state whose stack-growth prologues
(`SpanSum`, `Span.All`, `SpanSum-range1`) fall through (`StackGuardOK s 120`, the guard word
outside the stack window), with `[RSP-136, RSP+8)` writable, the call returns, obeys the ABI, and
`RAX = lo + (lo+1) + ... + (hi-1) mod 2^64` (`spanSum lo (hi - lo)`): the same statement as arm64.

**What is exercised.** As on arm64: `SpanSum` builds the funcval of the loop body
`SpanSum-range1` in its frame (`LEAQ` of the code address, pointers to `#state` and `s`) and passes
it in `RCX` to `Span.All`, which spills it to its caller's argument slot and calls it per element
through `CALL BX` with the context register `RDX` = the funcval; the body checks `#state`
(`runtime.panicrangestate` otherwise, never reached), adds `x` to `s` through the captured pointer
(`ADDQ AX, 0(DX)`) and returns `true`. `loop` is the invariant at `Span.All`'s loop head
(`CMPQ BX, AX`, offset `0x2c`).
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

abbrev head : Nat := segAddr Extracted.program "example.com/basic.Span.All" + 0x2c

/-- `lo + (lo+1) + ... + (lo+n-1)` in 64-bit arithmetic. -/
def spanSum (lo : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => spanSum lo n + (lo + BitVec.ofNat 64 n)

/-- The memory at the loop head before any iteration. -/
abbrev mem0 (s : State) (hi : BitVec 64) : Janus.Arm64.Memory :=
  (((((((((Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8 (BitVec.toNat (s.regs 5))).writeLE
    (BitVec.toNat (s.regs 4) - 48) 8 0).writeLE (BitVec.toNat (s.regs 4) - 40) 8 1).writeLE
    (BitVec.toNat (s.regs 4) - 32) 8 4742784).writeLE
    (BitVec.toNat (s.regs 4) - 24) 8 (BitVec.toNat (s.regs 4) - 40)).writeLE
    (BitVec.toNat (s.regs 4) - 16) 8 (BitVec.toNat (s.regs 4) - 48)).writeLE
    (BitVec.toNat (s.regs 4) - 80) 8 4742698).writeLE
    (BitVec.toNat (s.regs 4) - 88) 8 (BitVec.toNat (s.regs 4) - 8)).writeLE
    (BitVec.toNat (s.regs 4) - 56) 8 (BitVec.toNat (s.regs 4) - 32)).writeLE
    (BitVec.toNat (s.regs 4) - 96) 8 hi.toNat

theorem loop (lo hi : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hle : 136 ≤ (s.regs 4).toNat) (hnw : (s.regs 4).toNat + 8 ≤ 2 ^ 48)
    (hacc : Janus.Arm64.Memory.accessible s.mem ((s.regs 4).toNat - 136) (136 + 8) true = true)
    (h_ret : Janus.Arm64.Memory.readLE s.mem (s.regs 4).toNat 8 = ret)
    (hgl : (s.regs 14).toNat + 16 + 8 ≤ 2 ^ 48)
    (hgr : Janus.Arm64.Memory.accessible s.mem ((s.regs 14).toNat + 16) 8 false = true)
    (hgb : Janus.Arm64.Memory.readLE s.mem ((s.regs 14).toNat + 16) 8 + 120 < (s.regs 4).toNat)
    (hgd : (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 136) :
    ∀ n (S : State) (i acc : BitVec 64) (m : Janus.Arm64.Memory), n = hi.toNat - i.toNat →
      lo.toNat ≤ i.toNat → (i.toNat ≤ hi.toNat ∨ i = lo) →
      S.rip = BitVec.ofNat 64 head → S.regs 0 = i → S.regs 3 = hi → S.regs 1 = s.regs 4 - 32#64 →
      S.regs 4 = s.regs 4 - 112#64 → S.regs 14 = s.regs 14 → S.xmm = s.xmm →
      S.mem = m → Janus.MemFrame (mem0 s hi) m
        [((s.regs 4).toNat - 136, (s.regs 4).toNat - 112), ((s.regs 4).toNat - 104, (s.regs 4).toNat - 96),
         ((s.regs 4).toNat - 48, (s.regs 4).toNat - 32)] →
      m.readLE ((s.regs 4).toNat - 40) 8 = 1 → m.readLE ((s.regs 4).toNat - 48) 8 = acc.toNat →
      acc = spanSum lo (i.toNat - lo.toNat) →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        s'.regs 0 = spanSum lo (hi.toNat - lo.toNat)) := by
  intro n
  induction n with
  | zero =>
    intro S i acc m hn hlo hih hpc h0 h3 h1 hsp h14 hx hm hfr hst hsum hacc'
    janus64_run [hst, hsum]
    refine ⟨by rw [hx], ?_⟩
    rw [hacc']
    rcases hih with h | h
    · rw [show i.toNat = hi.toNat by omega]
    · subst h; rw [show hi.toNat - i.toNat = 0 by omega, Nat.sub_self]
  | succ n ih =>
    intro S i acc m hn hlo hih hpc h0 h3 h1 hsp h14 hx hm hfr hst hsum hacc'
    janus64_run until [head]
    all_goals first | (exfalso; omega) | skip
    have hlt : i.toNat < hi.toNat := by omega
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hi.isLt; omega
    have hr1 : ((s.regs 4).toNat - 136, (s.regs 4).toNat - 112) ∈ [((s.regs 4).toNat - 136, (s.regs 4).toNat - 112),
        ((s.regs 4).toNat - 104, (s.regs 4).toNat - 96), ((s.regs 4).toNat - 48, (s.regs 4).toNat - 32)] := by simp
    have hr2 : ((s.regs 4).toNat - 104, (s.regs 4).toNat - 96) ∈ [((s.regs 4).toNat - 136, (s.regs 4).toNat - 112),
        ((s.regs 4).toNat - 104, (s.regs 4).toNat - 96), ((s.regs 4).toNat - 48, (s.regs 4).toNat - 32)] := by simp
    have hr3 : ((s.regs 4).toNat - 48, (s.regs 4).toNat - 32) ∈ [((s.regs 4).toNat - 136, (s.regs 4).toNat - 112),
        ((s.regs 4).toNat - 104, (s.regs 4).toNat - 96), ((s.regs 4).toNat - 48, (s.regs 4).toNat - 32)] := by simp
    apply ih _ (i + 1#64) (acc + i)
    all_goals try (with_reducible rfl)
    all_goals try janus64_simp
    · omega
    · omega
    · left; omega
    · apply BitVec.eq_of_toNat_eq; simp; omega
    · exact hx
    · exact (((((hfr.writeLE _ hr2 (by omega) (by omega)).writeLE _ hr1 (by omega) (by omega)).writeLE _ hr1
        (by omega) (by omega)).writeLE _ hr3 (by omega) (by omega)).writeLE _ hr3 (by omega) (by omega)).writeLE _
        hr3 (by omega) (by omega)
    · have hl : lo + BitVec.ofNat 64 (i.toNat - lo.toNat) = i := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := i.isLt; omega
      rw [show i.toNat + 1 - lo.toNat = (i.toNat - lo.toNat) + 1 by omega, spanSum, ← hacc', hl]

theorem correctness (lo hi : BitVec 64) :
    Ensures Extracted.program Extracted.entry [lo, hi]
      (fun s => StackGuardOK s 120 ∧ StackWritable s 136 8 ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 136))
      (fun _ s' => s'.regs 0 = spanSum lo (hi.toNat - lo.toNat)) := by
  intro ret hret s hs ⟨hg, ⟨hle, hnw, hacc⟩, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run until [head]
  exact loop lo hi ret hret s hle hnw hacc h_ret (by omega) hgr (by omega) hgd _ _ lo 0#64 _ rfl (Nat.le_refl _) (Or.inr rfl)
    (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
    (by janus64_simp) rfl rfl (Janus.MemFrame.refl _ _) (by janus64_simp) (by janus64_simp) (by simp [spanSum])
end Proof
