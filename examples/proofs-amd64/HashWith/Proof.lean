import Janus
import Extracted

/-! `example.com/basic.HashWith(h Hasher, x)` on amd64: the interface method call `h.Hash(x)`
(`MOVQ 24(AX), DX; CALL DX`), with the itab `tab` in `RAX`, the receiver `h` in `RBX` and `x` in
`RCX`.

For every call state whose stack-growth check falls through, with `[RSP-32, RSP+24)` writable and
the receiver's field `K` (8 bytes at `h`) readable outside it: if `tab` is the static itab of
`*MulHasher` for `Hasher` (`ItabIs`: its address, with its 32 bytes from `.rodata` in read-only
memory), the call returns `x · K`; if it is the itab of `*RotHasher`, it returns
`rotl(x, 13) + K`.

The itab is a hypothesis of the theorem, not something derived from Go's types. Both methods are
proved once as callee summaries; `janus_dyn hi` turns `ItabIs` into the itab's literal address
and words, so `janus64_run` finds a literal `CALL` target and applies that method's summary. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Janus.Spec (ItabIs)

abbrev mulItab : String := "go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher"
abbrev rotItab : String := "go:itab.*example.com/basic.RotHasher,example.com/basic.Hasher"

theorem mul_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.(*MulHasher).Hash")
      (fun s => s.mem.accessible (s.regs 0).toNat 8 false = true ∧
        s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => ∃ f, s' = { s with
        regs := setRegF (setRegF s.regs 0 (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) * s.regs 3)) 4
          (s.regs 4 + 8), rip := retAddrOf s, flags := f }) := by
  intro s hpc ⟨h0, h1, h2⟩
  have := Janus.Arm64.Memory.accessible_bound _ h0
  janus64_run
  exact ⟨_, rfl⟩

theorem rot_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.(*RotHasher).Hash")
      (fun s => s.mem.accessible (s.regs 0).toNat 8 false = true ∧
        s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => ∃ v3 f, s' = { s with
        regs := setRegF (setRegF (setRegF s.regs 0
          ((s.regs 3).rotateLeft 13 + BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8))) 3 v3) 4
          (s.regs 4 + 8), rip := retAddrOf s, flags := f }) := by
  intro s hpc ⟨h0, h1, h2⟩
  have := Janus.Arm64.Memory.accessible_bound _ h0
  janus64_run
  exact ⟨_, _, rfl⟩

theorem correctness (tab h x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [tab, h, x]
      (fun s => ItabIs Extracted.program.data s.mem tab mulItab ∧ Buffer s h 8 false ∧
        StackGuardOK s 0 ∧ StackWritable s 32 24 ∧
        ((s.regs 4).toNat + 24 ≤ h.toNat ∨ h.toNat + 8 ≤ (s.regs 4).toNat - 32))
      (fun s s' => s'.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) ∧
    Ensures Extracted.program Extracted.entry [tab, h, x]
      (fun s => ItabIs Extracted.program.data s.mem tab rotItab ∧ Buffer s h 8 false ∧
        StackGuardOK s 0 ∧ StackWritable s 32 24 ∧
        ((s.regs 4).toNat + 24 ≤ h.toNat ∨ h.toNat + 8 ≤ (s.regs 4).toNat - 32))
      (fun s s' => s'.regs 0 = x.rotateLeft 13 + BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) := by
  constructor
  all_goals
    intro ret hret s hs ⟨hi, ⟨hhb, hh⟩, hg, ⟨hle, hnw, hacc⟩, hd⟩
    janus64_intro hs
    have hgl := hg.load
    have hgb := hg.below
    have hnw2 := hg.noWrap
    have hgr := hg.readable
    simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
    janus_dyn hi
    janus64_run calls [mul_summary, rot_summary]
  rw [BitVec.mul_comm]

end Proof
