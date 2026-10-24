import Extracted

/-!
# `MapSum(f func(uint64) uint64, xs []uint64) uint64` calls a closure in a loop

**Guarantee.** For every funcval pointer `f` in `X0`, slice header `(ptr, len, cap)` in `X1`–`X3`,
all `a`, `b`, and every Go call state `s` of `example.com/basic.MapSum` such that

* `f` is the closure `AffineSum.func1` (`FuncvalIs`: its code word is that function's address)
  that captured `a` and `b` (`ClosureCtx`: the next two words), and these 24 bytes are outside
  the stack window,
* `len < 2^63`, the `8·len` bytes at `ptr` are readable and outside the stack window,
* the stack-growth prologue falls through and `[SP-56, SP+32)` is writable with `SP` aligned,

the call returns, obeys the ABI, and `X0 = Σ_{j<len} (a·xs[j] + b) mod 2^64` (`affineSum`): the
loop calls the closure once per element and adds up what it returns.

**What it assumes.** That `f` is this closure is a hypothesis (`AffineSum` passes it; the
extraction names `AffineSum.func1` with `--targets`). The closure's body
(`ldp x1, x2, [x26, #8]; madd x0, x0, x1, x2; ret`) is executed: it reads `a` and `b` through
the context register `X26`, which the caller set to `f`.

**How.** `loop` is the invariant at the loop head (`cmp x2, x3`, offset `0x68`). The stack slots
the loop writes each iteration are described by a `MemFrame` over the memory at the head, so
the invariant does not need the exact store chain. `janus_dyn hf hc` turns the closure
hypotheses into the read equations the executor uses at every `BLR`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

abbrev head : Nat := Extracted.entry + 0x68
abbrev func1 : Nat := segAddr Extracted.program "example.com/basic.AffineSum.func1"

/-- `Σ_{j<n} (a·xs[j] + b)` in 64-bit arithmetic, `xs[j]` the word at `ptr + 8j` of `m`. -/
def affineSum (m : Memory) (ptr : Nat) (a b : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => affineSum m ptr a b n + (BitVec.ofNat 64 (m.readLE (ptr + 8 * n) 8) * a + b)

/-- The memory at the loop head before any iteration. -/
abbrev mem0 (s : State) (ret : Nat) (f ptr len : BitVec 64) : Memory :=
  ((((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
    (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 8) 8 f.toNat).writeLE
    (BitVec.toNat s.sp + 24) 8 len.toNat).writeLE (BitVec.toNat s.sp + 16) 8 ptr.toNat

theorem loop (f ptr len a b : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hf : FuncvalIs s.mem f func1) (hc : Spec.ClosureCtx s.mem f [a, b])
    (hfd : f.toNat + 24 ≤ s.sp.toNat - 56 ∨ s.sp.toNat - 56 + 88 ≤ f.toNat)
    (hlen : len.toNat < 2 ^ 63)
    (hp : s.mem.accessible ptr.toNat (8 * len.toNat) false = true)
    (hp' : ptr.toNat + 8 * len.toNat ≤ 2 ^ 48)
    (hd : ptr.toNat + 8 * len.toNat ≤ s.sp.toNat - 56 ∨ s.sp.toNat - 56 + 88 ≤ ptr.toNat)
    (hal : s.sp.toNat % 16 = 0) (hb : 56 ≤ s.sp.toNat) (ha : s.sp.toNat + 32 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 56) (56 + 32) true = true) :
    ∀ n (S : State) (i acc : BitVec 64) (m : Memory), i.toNat + n = len.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = f → S.regs 1 = ptr → S.regs 2 = len →
      S.regs 3 = i → S.regs 4 = acc → acc = affineSum s.mem ptr.toNat a b i.toNat →
      S.sp = s.sp - 48#64 → S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
      S.mem = m → MemFrame (mem0 s ret f ptr len) m [(s.sp.toNat - 24, s.sp.toNat - 8)] →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        s'.regs 0 = affineSum s.mem ptr.toNat a b len.toNat) := by
  janus_dyn hf hc
  intro n
  induction n with
  | zero =>
    intro S i acc m hn hpc h0 h1 h2 h3 h4 hacc hsp h28 h18 hm hfr
    janus_run
    rw [hacc, show i.toNat = len.toNat by omega]
  | succ n ih =>
    intro S i acc m hn hpc h0 h1 h2 h3 h4 hacc hsp h28 h18 hm hfr
    janus_run until [head]
    apply ih _ (i + 1#64) (acc + (BitVec.ofNat 64 (s.mem.readLE (ptr.toNat + 8 * i.toNat) 8) * a + b))
      ((m.writeLE (s.sp.toNat - 16) 8 i.toNat).writeLE (s.sp.toNat - 24) 8 acc.toNat)
    all_goals try janus_simp
    · omega
    · rw [BitVec.add_comm b]
    · rw [hacc]; rfl
    · exact (hfr.writeLE _ List.mem_cons_self (by omega) (by omega)).writeLE _
        List.mem_cons_self (by omega) (by omega)

theorem correctness (f ptr len cap a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [f, ptr, len, cap]
      (fun s => FuncvalIs s.mem f func1 ∧ Spec.ClosureCtx s.mem f [a, b] ∧
        Disjoint f.toNat 24 (s.sp.toNat - 56) 88 ∧
        len.toNat < 2 ^ 63 ∧ Ptr s.mem ptr (8 * len.toNat) false ∧
        Disjoint ptr.toNat (8 * len.toNat) (s.sp.toNat - 56) 88 ∧
        GuardOK s 0 ∧ StackOK s 56 32)
      (fun s s' => s'.regs 0 = affineSum s.mem ptr.toNat a b len.toNat) := by
  intro ret hret s hs ⟨hf, hc, hfd, hlen, ⟨hp, hp'⟩, hd, ⟨hg1, hg2, hg3⟩, hal, hb, ha, hw⟩
  janus_intro hs
  simp only [Disjoint] at hd hfd
  janus_run until [head]
  exact loop f ptr len a b ret hret s hf hc hfd hlen hp hp' hd hal hb ha hw len.toNat _ 0#64 0#64 _
    (by simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
    (by janus_simp) (by simp [affineSum]) (by janus_simp) (by janus_simp) (by janus_simp) rfl
    (MemFrame.refl _ _)

end Proof
