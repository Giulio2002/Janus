import Extracted

/-!
# `WriteTo(w io.Writer, b []byte) (int, error)` calls `w.Write(b)` on an arbitrary writer

**Guarantee.** For **every** code address `fn`, every memory `rt` the callee may write, every relation `R` of
its results to its arguments, and every call state of `example.com/basic.WriteTo` in which the
stack-growth prologue falls through, `SP` is aligned with the callee's stack and the function's frame writable,
the itab word `tab` of the writer has `Fun[0] = fn` (`s.mem.readLE (tab + 24) 8 = fn`, 8 readable bytes) and `rt` is
apart from the function's frame:

* if the code at `fn` satisfies `ICallContract` (the Go ABI only: a return to the caller with `SP`, `X18`, `X28`,
  `X29` preserved, memory changed only in `rt` and the callee's stack, results related by
  `R` to the arguments), then `WriteTo` returns, and
* the call to `fn` is **entered with the receiver `w` and the slice `(ptr, len, cap)` that `WriteTo` received** (the
  call-site property `P` is what `janus_run` proves at the call: the theorem assumes the callee only for such calls),
* the results of `WriteTo` are the callee's results, unchanged: `R w ptr len cap n e₁ e₂` and
  `(X0, X1, X2) = (n, e₁, e₂)`,

**What it assumes.** Only `ICallContract fn …` (a hypothesis about code that is not extracted: the printed statement
shows it) and the link between the itab word and `fn`. Nothing is assumed about which writer it is, nor that it leaves
the heap alone.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.ICall

namespace Proof

theorem correctness (impl : List Segment) (fn stack : Nat) (rt : List (Nat × Nat)) (R : Res) (tab w ptr len cap : BitVec 64) :
    ICallContract (Extracted.program.link impl) fn 4 stack 48 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧ sc.regs 1 = ptr ∧ sc.regs 2 = len ∧ sc.regs 3 = cap) →
    Ensures (Extracted.program.link impl) Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ CodePtrOK fn ∧ Disjoint (tab.toNat + 24) 8 (s.sp.toNat - 56) 88 ∧
        GuardOK s 0 ∧ StackOK s (48 + stack) 40 ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧ s.mem.readLE (tab.toNat + 24) 8 = fn ∧
        Outside (s.sp.toNat - 56) 56 rt)
      (fun _ s' => ∃ n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = n ∧ s'.regs 1 = e1 ∧ s'.regs 2 = e2) := by
  intro hc ret hret s hs ⟨h8, ⟨hfn4, hfn⟩, hd, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, htb, ht, hF, hrt⟩
  janus_intro hs
  simp only [Disjoint] at hd
  have hrt' : Outside (s.sp.toNat - 48 - 8) (48 + 8) rt := hrt.of_sub (by omega) (by omega)
  janus_run [hF] calls [hc]
  case hq =>
    rename_i _ _ hR
    exact ⟨_, _, _, hR, rfl, rfl, rfl⟩

/-! ## Non-vacuity witness

A concrete writer (`Janus.Contracts.ICallSat`: A64 code at `0x100000` returning `(len, nil)`), linked into the example's
program, meets the abstract-callee contract for the call-site property of `correctness` (`ICallSat.impl_okP`, moved into the
linked program by `Summary.of_codeIn`); a concrete itab whose `Fun[0]` word is the writer's address; and a call state of
`WriteTo` that satisfies the whole precondition. So the hypothesis and the precondition are satisfiable together. -/

namespace Witness

open Janus.Contracts.EqHashModel (codeIn_link Summary.of_codeIn)
open Janus.Contracts.ICallSat (impl A0 rt0 R0 toy)

def ret : Nat := 0x1000
def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000
def tabA : Nat := 0x400000

/-- The itab: its `Fun[0]` word (offset 24) is the writer's address, little-endian; zero elsewhere. -/
def bytes (a : Nat) : Byte :=
  if tabA + 24 ≤ a ∧ a < tabA + 32 then BitVec.ofNat 8 ((A0 / 256 ^ (a - (tabA + 24))) % 256) else 0

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 tabA else if i = 1 then 0x600000 else if i = 2 then 0x500000
      else if i = 3 then 3 else if i = 4 then 3 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 64, 104, true⟩, ⟨g0, 0x100, false⟩, ⟨tabA, 0x40, false⟩]⟩ }

/-- The writer meets the contract for `WriteTo`'s call-site property, in the example's linked program. -/
theorem hc : ICallContract (Extracted.program.link impl) A0 4 16 48 rt0 (fun _ => []) R0
    (fun sc => sc.regs 0 = 0x600000 ∧ sc.regs 1 = 0x500000 ∧ sc.regs 2 = 3 ∧ sc.regs 3 = 3) := by
  have h := Janus.Contracts.ICallSat.impl_okP (nargs := 4) (stack := 16) (above := 48)
    (P := fun sc => sc.regs 0 = 0x600000 ∧ sc.regs 1 = 0x500000 ∧ sc.regs 2 = 3 ∧ sc.regs 3 = 3)
    (fun _ _ => True) (fun _ => trivial)
  exact Summary.of_codeIn (codeIn_link Extracted.program _ (by decide)) h

theorem hret : RetAddr (Extracted.program.link impl) ret := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry
    [BitVec.ofNat 64 tabA, 0x600000, 0x500000, 3, 3] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

/-- The hypotheses are satisfiable together: a writer meeting the contract, and a call state of `WriteTo` (with a concrete itab)
that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (fn stack : Nat) (rt : List (Nat × Nat)) (R : Res) (ret : Nat) (s : State)
    (tab w ptr len cap : BitVec 64),
    ICallContract (Extracted.program.link impl) fn 4 stack 48 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧ sc.regs 1 = ptr ∧ sc.regs 2 = len ∧ sc.regs 3 = cap) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [tab, w, ptr, len, cap] s ∧
    (8 ≤ stack ∧ CodePtrOK fn ∧ Disjoint (tab.toNat + 24) 8 (s.sp.toNat - 56) 88 ∧
      GuardOK s 0 ∧ StackOK s (48 + stack) 40 ∧
      tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧ s.mem.readLE (tab.toNat + 24) 8 = fn ∧
      Outside (s.sp.toNat - 56) 56 rt) :=
  ⟨impl, A0, 16, rt0, R0, ret, s0, BitVec.ofNat 64 tabA, 0x600000, 0x500000, 3, 3, hc, hret, setup,
    by decide, ⟨by decide, by decide⟩, (by unfold Janus.Spec.Disjoint; decide), ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩,
    by decide, by decide, by decide, by simp [s0, sp0, rt0]⟩

end Witness

end Proof
