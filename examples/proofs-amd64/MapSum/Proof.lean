import Janus
import Extracted

/-! `example.com/basic.MapSum(f, xs)` on amd64: the closure `f` (funcval in `RAX`, called with
`CALL BX` and the context in `DX`) called once per element of `xs` (`RBX`, `RCX`, `RDI`).

If `f` is the closure `AffineSum.func1` that captured `a` and `b` (`FuncvalIs` and `ClosureCtx`:
its code word and the two words after it, outside the stack window), `len < 2^63`, the
`8·len` bytes at `ptr` are readable outside the window, the stack-growth check falls through and
`[RSP-40, RSP+32)` is writable, the call returns `Σ_{j<len} (a·xs[j] + b) mod 2^64`.

`loop` is the invariant at the loop head (`CMPQ CX, DX` at offset `0x60`); the slots each
iteration writes (the loop variables and the return address of the call) are a `MemFrame` over
the memory at the head. The closure body is executed. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Janus.Spec (FuncvalIs)

abbrev head : Nat := Extracted.entry + 0x60
abbrev func1 : Nat := segAddr Extracted.program "example.com/basic.AffineSum.func1"

/-- `Σ_{j<n} (a·xs[j] + b)` in 64-bit arithmetic, `xs[j]` the word at `ptr + 8j` of `m`. -/
def affineSum (m : Janus.Arm64.Memory) (ptr : Nat) (a b : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => affineSum m ptr a b n + (BitVec.ofNat 64 (m.readLE (ptr + 8 * n) 8) * a + b)

/-- The memory at the loop head before any iteration. -/
abbrev mem0 (s : State) (f ptr len : BitVec 64) : Janus.Arm64.Memory :=
  (((Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8 (BitVec.toNat (s.regs 5))).writeLE
    (BitVec.toNat (s.regs 4) + 8) 8 f.toNat).writeLE (BitVec.toNat (s.regs 4) + 24) 8 len.toNat).writeLE
    (BitVec.toNat (s.regs 4) + 16) 8 ptr.toNat

theorem loop (f ptr len a b : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hf : FuncvalIs s.mem f func1) (hc : Janus.Spec.ClosureCtx s.mem f [a, b])
    (hlen : len.toNat < 2 ^ 63)
    (hp : Janus.Arm64.Memory.accessible s.mem ptr.toNat (8 * len.toNat) false = true)
    (hp' : ptr.toNat + 8 * len.toNat ≤ 2 ^ 48)
    (hle : 40 ≤ (s.regs 4).toNat) (hnw : (s.regs 4).toNat + 32 ≤ 2 ^ 48)
    (hacc : Janus.Arm64.Memory.accessible s.mem ((s.regs 4).toNat - 40) (40 + 32) true = true)
    (h_ret : Janus.Arm64.Memory.readLE s.mem (s.regs 4).toNat 8 = ret)
    (hfd : f.toNat + 24 ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat + 32 ≤ f.toNat)
    (hd : ptr.toNat + 8 * len.toNat ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat + 32 ≤ ptr.toNat) :
    ∀ n (S : State) (i acc : BitVec 64) (m : Janus.Arm64.Memory), i.toNat + n = len.toNat →
      S.rip = BitVec.ofNat 64 head → S.regs 0 = f → S.regs 3 = ptr → S.regs 1 = len →
      S.regs 2 = i → S.regs 6 = acc → acc = affineSum s.mem ptr.toNat a b i.toNat →
      S.regs 4 = s.regs 4 - 32#64 → S.regs 5 = s.regs 4 - 8#64 → S.regs 14 = s.regs 14 →
      S.xmm = s.xmm →
      S.mem = m → Janus.MemFrame (mem0 s f ptr len) m [((s.regs 4).toNat - 40, (s.regs 4).toNat - 8)] →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        s'.regs 0 = affineSum s.mem ptr.toNat a b len.toNat) := by
  janus_dyn hf hc
  intro n
  induction n with
  | zero =>
    intro S i acc m hn hpc h0 h1 h2 h3 h4 hacc' hsp hfp h14 hx hm hfr
    janus64_run
    exact ⟨by rw [hx], by rw [hacc', show i.toNat = len.toNat by omega]⟩
  | succ n ih =>
    intro S i acc m hn hpc h0 h1 h2 h3 h4 hacc' hsp hfp h14 hx hm hfr
    janus64_run until [head]
    apply ih _ (i + 1#64) (acc + (BitVec.ofNat 64 (s.mem.readLE (ptr.toNat + 8 * i.toNat) 8) * a + b))
    all_goals try (with_reducible rfl)
    all_goals try janus64_simp
    · omega
    · rw [Nat.mul_comm i.toNat 8]
    · rw [hacc']; rfl
    · exact hx
    · exact ((hfr.writeLE _ List.mem_cons_self (by omega) (by omega)).writeLE _
        List.mem_cons_self (by omega) (by omega)).writeLE _ List.mem_cons_self (by omega) (by omega)

theorem correctness (f ptr len cap a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [f, ptr, len, cap]
      (fun s => FuncvalIs s.mem f func1 ∧ Janus.Spec.ClosureCtx s.mem f [a, b] ∧
        len.toNat < 2 ^ 63 ∧ Buffer s ptr (8 * len.toNat) false ∧
        StackGuardOK s 0 ∧ StackWritable s 40 32 ∧
        (f.toNat + 24 ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat + 32 ≤ f.toNat) ∧
        (ptr.toNat + 8 * len.toNat ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat + 32 ≤ ptr.toNat))
      (fun s s' => s'.regs 0 = affineSum s.mem ptr.toNat a b len.toNat) := by
  intro ret hret s hs ⟨hf, hc, hlen, ⟨hp', hp⟩, hg, ⟨hle, hnw, hacc⟩, hfd, hd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run until [head]
  exact loop f ptr len a b ret hret s hf hc hlen hp hp' hle hnw hacc h_ret hfd hd len.toNat _ 0#64 0#64 _
    (by simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
    (by janus64_simp) (by janus64_simp) (by simp [affineSum]) (by janus64_simp) (by janus64_simp)
    (by janus64_simp) rfl rfl (Janus.MemFrame.refl _ _)

end Proof
