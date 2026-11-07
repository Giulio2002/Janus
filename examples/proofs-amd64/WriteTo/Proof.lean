import Janus
import Extracted

/-! `example.com/basic.WriteTo(w io.Writer, b []byte) (int, error)` on amd64: `w.Write(b)` through the itab
(`MOVQ 24(AX), DX; CALL DX`), with `w = (tab, data)` in `RAX`, `RBX` and `b = (ptr, len, cap)` in `RCX`, `RDI`, `RSI`.

The same guarantee as the arm64 proof (`examples/proofs/WriteTo.lean`): for **every** code address `fn`, memory `rt` and
relation `R`, if the code at `fn` satisfies `ICallContract64` (the Go ABI only: `RSP` popped, `RBP` and `R14` preserved,
memory changed only in `rt` and the callee's stack, results related by `R` to the arguments),
then `WriteTo` returns, the call is entered with the receiver and slice it received, its results are the callee's
(`R w ptr len cap n e₁ e₂` and `(RAX, RBX, RCX) = (n, e₁, e₂)`). -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.ICall

theorem correctness (impl : List Janus.Amd64.Segment) (fn stack : Nat) (rt : List (Nat × Nat)) (R : Res) (tab w ptr len cap : BitVec 64) :
    ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧ sc.regs 3 = ptr ∧ sc.regs 1 = len ∧ sc.regs 7 = cap) →
    Ensures (Extracted.program.link impl) Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ CodePtrOK64 fn ∧
        (tab.toNat + 32 ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 32 ≤ tab.toNat + 24) ∧
        StackGuardOK s 0 ∧ StackWritable s (48 + stack) 32 ∧ SPAligned s ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn ∧ Outside ((s.regs 4).toNat - 48) 56 rt)
      (fun _ s' => ∃ n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = n ∧ s'.regs 3 = e1 ∧ s'.regs 1 = e2) := by
  intro hc ret hret s hs ⟨h8, hfn, hd, hg, ⟨hle, hnw, hacc⟩, hal, htb, ht, hF, hrt⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, SPAligned, CodePtrOK64] at hfn
  simp only [regSP, regG, stackguard0Offset, stackguard0, SPAligned] at hacc hle hnw hgl hgb hnw2 hgr hal hd hF hrt
  have hrt' : Outside ((s.regs 4).toNat - 8 - 32 - 8) 56 rt := hrt.of_sub (by omega) (by omega)
  have hal48 : ((s.regs 4).toNat - 48) % 8 = 0 := by omega
  janus64_run [hF] calls [hc]
  case hq =>
    rename_i _ _ hR
    exact ⟨_, _, _, hR, rfl, rfl, rfl⟩

/-! ## Non-vacuity witness

As the arm64 proof: a concrete writer (`Janus.Contracts.ICallSatAmd64`: x86-64 code at `0x100000` returning `(len, nil)`) meets the
contract for `correctness`'s call-site property in the example's linked program (`Summary.of_codeIn`), the itab's `Fun[0]` word is its
address, and a call state of `WriteTo` satisfies the whole precondition. -/

namespace Witness

open Janus.Contracts.EqHashModel (codeIn_link64 Summary.of_codeIn64)
open Janus.Contracts.ICallSat (rt0 R0)
open Janus.Contracts.ICallSatAmd64 (impl A0 impl_okP)

def ret : Nat := 0x1000
def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000
def tabA : Nat := 0x400000

/-- The itab's `Fun[0]` word (offset 24) is the writer's address, and the return address `ret` is at `[RSP]`; zero elsewhere. -/
def bytes (a : Nat) : Janus.Arm64.Byte :=
  if tabA + 24 ≤ a ∧ a < tabA + 32 then BitVec.ofNat 8 ((A0 / 256 ^ (a - (tabA + 24))) % 256)
  else if sp0 ≤ a ∧ a < sp0 + 8 then BitVec.ofNat 8 ((ret / 256 ^ (a - sp0)) % 256) else 0

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 tabA else if i = 3 then 0x600000 else if i = 1 then 0x500000
      else if i = 7 then 3 else if i = 6 then 3 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 64, 96, true⟩, ⟨g0, 0x100, false⟩, ⟨tabA, 0x40, false⟩]⟩ }

theorem hc : ICallContract64 (Extracted.program.link impl) A0 4 16 56 rt0 (fun _ => []) R0
    (fun sc => sc.regs 0 = 0x600000 ∧ sc.regs 3 = 0x500000 ∧ sc.regs 1 = 3 ∧ sc.regs 7 = 3) := by
  have h := impl_okP (nargs := 4) (stack := 16) (above := 56)
    (P := fun sc => sc.regs 0 = 0x600000 ∧ sc.regs 3 = 0x500000 ∧ sc.regs 1 = 3 ∧ sc.regs 7 = 3)
    (fun _ _ => True) (fun _ => trivial)
  exact Summary.of_codeIn64 (codeIn_link64 Extracted.program _ (by decide)) h

theorem hret : RetAddr (Extracted.program.link impl) ret := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry
    [BitVec.ofNat 64 tabA, 0x600000, 0x500000, 3, 3] s0 :=
  ⟨rfl, by decide, rfl, by decide, (fun i h => by
      have h5 : i < 5 := by simpa using h
      match i, h5 with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl
      | 4, _ => rfl), rfl⟩

theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (fn stack : Nat) (rt : List (Nat × Nat)) (R : Res) (ret : Nat)
    (s : State) (tab w ptr len cap : BitVec 64),
    ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧ sc.regs 3 = ptr ∧ sc.regs 1 = len ∧ sc.regs 7 = cap) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [tab, w, ptr, len, cap] s ∧
    (8 ≤ stack ∧ CodePtrOK64 fn ∧
      (tab.toNat + 32 ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 32 ≤ tab.toNat + 24) ∧
      StackGuardOK s 0 ∧ StackWritable s (48 + stack) 32 ∧ SPAligned s ∧
      tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧
      s.mem.readLE (tab.toNat + 24) 8 = fn ∧ Outside ((s.regs 4).toNat - 48) 56 rt) :=
  ⟨impl, A0, 16, rt0, R0, ret, s0, BitVec.ofNat 64 tabA, 0x600000, 0x500000, 3, 3, hc, hret, setup,
    by decide, (by unfold CodePtrOK64; decide), by decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    (by unfold SPAligned; decide), by decide, by decide, by decide, by simp [s0, sp0, rt0]⟩

/-- The theorem fires: the concrete call of `WriteTo` (the concrete writer serves the itab) returns, and its results are the ones
`correctness` describes. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    ∃ n e1 e2, R0 0x600000 0x500000 3 3 n e1 e2 ∧ s'.regs 0 = n ∧ s'.regs 3 = e1 ∧ s'.regs 1 = e2 :=
  correctness impl A0 16 rt0 R0 (BitVec.ofNat 64 tabA) 0x600000 0x500000 3 3 hc ret hret s0 setup
    ⟨by decide, (by unfold CodePtrOK64; decide), by decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    (by unfold SPAligned; decide), by decide, by decide, by decide, by simp [s0, sp0, rt0]⟩

end Witness

end Proof
