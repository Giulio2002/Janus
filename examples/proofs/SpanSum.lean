import Extracted

/-!
# `SpanSum(lo, hi uint64) uint64`: range over a function iterator that stays a real call

**Guarantee.** For all 64-bit `lo`, `hi` and every Go call state of `example.com/basic.SpanSum`
whose stack-growth prologues (of `SpanSum`, `Span.All` and the loop body `SpanSum-range1`) fall
through (`GuardOK s 128`, the guard word outside the stack window), with `SP` aligned and
`[SP-168, SP)` writable, the call returns (never faulting or panicking), obeys the ABI, and
`X0 = lo + (lo+1) + ... + (hi-1) mod 2^64` (`spanSum lo (hi - lo)`; no iteration when
`hi ≤ lo`).

**What is exercised.** Go 1.23+ rewrites `for x := range (Span{lo, hi}).All { s += x }` into a call
of the iterator `Span.All` (not inlined: `//go:noinline`) with the loop body as the closure
`SpanSum-range1`. `SpanSum` builds its funcval in its own frame (the code address, then pointers to
the loop-state word `#state` and to `s`), `Span.All` calls it once per element through `BLR` with
the context register `X26` = the funcval, and the body checks and updates `#state` (`1` = ready,
`2` = running; any other value calls `runtime.panicrangestate`, a panic stub this run never
reaches) and adds `x` to `s` through the captured pointer. After the iterator returns, `SpanSum`
checks `#state ≠ 2` (else `panicrangestate`), sets it to `3` (done) and returns `s`. Everything
the indirect calls depend on is written by the code being proved, so there is no hypothesis about
the closure; the extraction finds `SpanSum-range1` from the code address `SpanSum` computes.

**How.** `loop` is the invariant at the loop head of `Span.All` (`cmp x0, x1`, offset `0x34`) for
`hi - i` remaining iterations: `#state = 1`, `s = spanSum lo (i - lo)`, and the memory equal to the
memory at the first arrival (`mem0`) outside the words the iterations write (`MemFrame`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

abbrev head : Nat := segAddr Extracted.program "example.com/basic.Span.All" + 0x34

/-- `lo + (lo+1) + ... + (lo+n-1)` in 64-bit arithmetic. -/
def spanSum (lo : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => spanSum lo n + (lo + BitVec.ofNat 64 n)

/-- The memory at the loop head before any iteration. -/
abbrev mem0 (s : State) (ret : Nat) (hi : BitVec 64) : Memory :=
  ((((((((((s.mem.writeLE (BitVec.toNat s.sp - 80) 8 ret).writeLE (BitVec.toNat s.sp - 88) 8
    (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp - 48) 8 0).writeLE
    (BitVec.toNat s.sp - 40) 8 1).writeLE (BitVec.toNat s.sp - 32) 8 (segAddr Extracted.program "example.com/basic.SpanSum-range1")).writeLE
    (BitVec.toNat s.sp - 24) 8 (BitVec.toNat s.sp - 40)).writeLE
    (BitVec.toNat s.sp - 16) 8 (BitVec.toNat s.sp - 48)).writeLE
    (BitVec.toNat s.sp - 128) 8 (segAddr Extracted.program "example.com/basic.SpanSum" + 0x44)).writeLE (BitVec.toNat s.sp - 136) 8 (BitVec.toNat s.sp - 88)).writeLE
    (BitVec.toNat s.sp - 56) 8 (BitVec.toNat s.sp - 32)).writeLE (BitVec.toNat s.sp - 96) 8 hi.toNat

theorem loop (lo hi : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hg1 : BitVec.toNat (s.regs 28) + 24 ≤ 2 ^ 48)
    (hg2 : s.mem.accessible (BitVec.toNat (s.regs 28) + 16) 8 false = true)
    (hg3 : s.mem.readLE (BitVec.toNat (s.regs 28) + 16) 8 + 128 < BitVec.toNat s.sp)
    (hal : BitVec.toNat s.sp % 16 = 0) (hb : 168 ≤ BitVec.toNat s.sp) (ha : BitVec.toNat s.sp ≤ 2 ^ 48)
    (hw : s.mem.accessible (BitVec.toNat s.sp - 168) 168 true = true)
    (hgd : BitVec.toNat (s.regs 28) + 16 + 8 ≤ BitVec.toNat s.sp - 168 ∨
      BitVec.toNat s.sp ≤ BitVec.toNat (s.regs 28) + 16) :
    ∀ n (S : State) (i acc : BitVec 64) (m : Memory), n = hi.toNat - i.toNat →
      lo.toNat ≤ i.toNat → (i.toNat ≤ hi.toNat ∨ i = lo) →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = i → S.regs 1 = hi → S.regs 2 = s.sp - 32#64 →
      S.sp = s.sp - 128#64 → S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
      S.mem = m → MemFrame (mem0 s ret hi) m
        [(s.sp.toNat - 168, s.sp.toNat - 152), (s.sp.toNat - 104, s.sp.toNat - 96),
         (s.sp.toNat - 48, s.sp.toNat - 32)] →
      m.readLE (s.sp.toNat - 40) 8 = 1 → m.readLE (s.sp.toNat - 48) 8 = acc.toNat →
      acc = spanSum lo (i.toNat - lo.toNat) →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        s'.regs 0 = spanSum lo (hi.toNat - lo.toNat)) := by
  intro n
  induction n with
  | zero =>
    intro S i acc m hn hlo hih hpc h0 h1 h2 hsp h28 h18 hm hfr hst hsum hacc
    simp only [mem0, reduceSegAddr, Nat.reduceAdd] at hfr
    janus_run [hst, hsum]
    rw [hacc]
    rcases hih with h | h
    · rw [show i.toNat = hi.toNat by omega]
    · subst h; rw [show hi.toNat - i.toNat = 0 by omega, Nat.sub_self]
  | succ n ih =>
    intro S i acc m hn hlo hih hpc h0 h1 h2 hsp h28 h18 hm hfr hst hsum hacc
    simp only [mem0, reduceSegAddr, Nat.reduceAdd] at hfr
    janus_run until [head]
    have hlt : i.toNat < hi.toNat := by omega
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hi.isLt; omega
    apply ih _ (i + 1#64) (acc + i)
    all_goals try (with_reducible rfl)
    all_goals try janus_simp
    · omega
    · omega
    · left; omega
    · apply BitVec.eq_of_toNat_eq; simp; omega
    · have hr1 : (BitVec.toNat s.sp - 168, BitVec.toNat s.sp - 152) ∈ [(BitVec.toNat s.sp - 168, BitVec.toNat s.sp - 152),
          (BitVec.toNat s.sp - 104, BitVec.toNat s.sp - 96), (BitVec.toNat s.sp - 48, BitVec.toNat s.sp - 32)] := by simp
      have hr2 : (BitVec.toNat s.sp - 104, BitVec.toNat s.sp - 96) ∈ [(BitVec.toNat s.sp - 168, BitVec.toNat s.sp - 152),
          (BitVec.toNat s.sp - 104, BitVec.toNat s.sp - 96), (BitVec.toNat s.sp - 48, BitVec.toNat s.sp - 32)] := by simp
      have hr3 : (BitVec.toNat s.sp - 48, BitVec.toNat s.sp - 32) ∈ [(BitVec.toNat s.sp - 168, BitVec.toNat s.sp - 152),
          (BitVec.toNat s.sp - 104, BitVec.toNat s.sp - 96), (BitVec.toNat s.sp - 48, BitVec.toNat s.sp - 32)] := by simp
      simp only [mem0, reduceSegAddr, Nat.reduceAdd]
      exact (((((hfr.writeLE _ hr2 (by omega) (by omega)).writeLE _ hr1 (by omega) (by omega)).writeLE _ hr1
        (by omega) (by omega)).writeLE _ hr3 (by omega) (by omega)).writeLE _ hr3 (by omega) (by omega)).writeLE _
        hr3 (by omega) (by omega)
    · rw [hsum]
    · have hl : lo + BitVec.ofNat 64 (i.toNat - lo.toNat) = i := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := i.isLt; omega
      rw [show i.toNat + 1 - lo.toNat = (i.toNat - lo.toNat) + 1 by omega, spanSum, ← hacc, hl]


theorem correctness (lo hi : BitVec 64) :
    Ensures Extracted.program Extracted.entry [lo, hi]
      (fun s => GuardOK s 128 ∧ StackOK s 168 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 168) 168)
      (fun _ s' => s'.regs 0 = spanSum lo (hi.toNat - lo.toNat)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hgd
  janus_run until [head]
  exact loop lo hi ret hret s hg1 hg2 hg3 hal hb (by omega) (by simpa using hw) (by omega) _ _ lo 0#64 _ rfl
    (Nat.le_refl _) (Or.inr rfl) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp) rfl (MemFrame.refl _ _) (by janus_simp) (by janus_simp)
    (by simp [spanSum])


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0) else if i = 1 then (5) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0 : BitVec 64), (5 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (lo : BitVec 64) (hi : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [lo, hi] s ∧ (GuardOK s 128 ∧ StackOK s 168 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 168) 168) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.regs 0 = spanSum lo (hi.toNat - lo.toNat))) := by
  refine ⟨ret, s0, (0), (5), hret, setup, ?pre, correctness (0) (5) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
