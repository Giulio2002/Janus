import Janus
import Extracted

/-!
# `Double(x uint64) uint64` (amd64): a run-time flag global, for every value it may hold

**Guarantee.** Extracted with `--global example.com/basic.useFast`. `useFast` is a `bool` set by
package initialisation (like math/big's `hasADX`, set from `internal/cpu` at startup), so its
link-time image (`.noptrbss`, zero) is not its value at a call, and the theorem does not assume
it. For every 64-bit `x`, every byte value `v` of the flag (`GlobalBytesIs … "useFast" 0 1 v`)
and every Go call state whose return-address slot is writable, the call returns, obeys the ABI,
and `RAX = 2x mod 2^64`: the fast path (`ADDQ AX, AX`, taken when `CMPB useFast(SB), $0` finds
the byte non-zero) and the two-iteration loop agree.

**Non-vacuity.** `Witness.nonvacuous`: the precondition holds for the flag clear (the link-time
image) and set (the byte stored as `1`); `Witness.returns`: both calls `Double(21)` return `42`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec

namespace Proof

/-- The named global lies apart from the return slot `[rsp, rsp + 8)` (the precondition no longer sees the return
address, so the flag's byte must not be the slot). -/
def GlobalApart (gs : List Janus.GlobalSegment) (n : String) (rsp : Nat) : Prop :=
  ∀ g, globalNamed gs n = some g → rsp + 8 ≤ g.base ∨ g.base + g.size ≤ rsp

theorem GlobalApart.of_eq {gs : List Janus.GlobalSegment} {n : String} {g : Janus.GlobalSegment} {rsp : Nat}
    (hg : globalNamed gs n = some g) (h : rsp + 8 ≤ g.base ∨ g.base + g.size ≤ rsp) : GlobalApart gs n rsp :=
  fun g' hg' => by rw [hg] at hg'; cases hg'; exact h

/-- `GlobalBytesIs` survives writing the return slot, when the global is apart from it. -/
theorem globalBytesIs_setRet {gs : List Janus.GlobalSegment} {n : String} {off k v : Nat} {s : State} {ret : Nat}
    (hap : GlobalApart gs n (s.regs 4).toNat) (h : GlobalBytesIs gs s.mem n off k v) :
    GlobalBytesIs gs (s.setRet ret).mem n off k v := by
  obtain ⟨g, hg, h1, h2, h3⟩ := h
  have := hap g hg
  refine ⟨g, hg, h1, by simpa using h2, ?_⟩
  rw [readLE_setRet_of_disjoint (by omega)]
  exact h3

theorem correctness (x : BitVec 64) (v : Nat) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 0 8 ∧
        GlobalApart Extracted.program.globals "example.com/basic.useFast" (s.regs regSP).toNat ∧
        GlobalBytesIs Extracted.program.globals s.mem "example.com/basic.useFast" 0 1 v)
      (fun _ s' => results 1 s' = [x + x]) := by
  refine Ensures.of_old (fun s ret _ _ hp => ?_) ?_
  · obtain ⟨hw, hap, h⟩ := hp
    exact ⟨by simpa [StackWritable] using hw, hap, globalBytesIs_setRet hap h⟩
  intro ret hret s hs ⟨hsw, _, h⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hsw
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  have hfa := h.accessible rfl false
  simp only [Nat.add_zero] at hfa
  janus64_run

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The link-time image of the global (the flag clear) over `EqHashModel.wmem64`. -/
def mem0 : Memory := globalsImage Extracted.program.globals wmem64

/-- The same memory after initialisation set the flag. -/
def mem1 : Memory := mem0.writeLE (globalAddr Extracted.program.globals "example.com/basic.useFast") 1 1

def s0 (m : Memory) : State :=
  { regs := fun i => if i = 0 then 21#64 else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := m }

theorem setup0 : CallSetup0 Extracted.entry [21#64] (s0 mem0) :=
  ⟨rfl, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem setup1 : CallSetup0 Extracted.entry [21#64] (s0 mem1) :=
  ⟨rfl, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem apart (m : Memory) :
    GlobalApart Extracted.program.globals "example.com/basic.useFast" ((s0 m).regs regSP).toNat :=
  GlobalApart.of_eq rfl (by
    have h : (s0 m).regs regSP = BitVec.ofNat 64 wsp := by simp [s0, regSP]
    rw [h]; decide)

theorem pre0 : StackWritable (s0 mem0) 0 8 ∧
    GlobalApart Extracted.program.globals "example.com/basic.useFast" ((s0 mem0).regs regSP).toNat ∧
    GlobalBytesIs Extracted.program.globals (s0 mem0).mem "example.com/basic.useFast" 0 1 0 :=
  ⟨(by first | exact ⟨by decide, by decide, by decide, by decide⟩ | exact ⟨by decide, by decide, by decide⟩), apart _,
    (globalsInit_image Extracted.program.globals wmem64 ["example.com/basic.useFast"]
      (by decide) (by decide)).bytesIs (n := "example.com/basic.useFast") (by simp) rfl
      (off := 0) (k := 1) (by decide)⟩

theorem pre1 : StackWritable (s0 mem1) 0 8 ∧
    GlobalApart Extracted.program.globals "example.com/basic.useFast" ((s0 mem1).regs regSP).toNat ∧
    GlobalBytesIs Extracted.program.globals (s0 mem1).mem "example.com/basic.useFast" 0 1 1 :=
  ⟨(by first | exact ⟨by decide, by decide, by decide, by decide⟩ | exact ⟨by decide, by decide, by decide⟩), apart _, ⟨_, rfl, by decide, by decide, by decide⟩⟩

/-- So the guarantee is reached on both paths: `Double(21)` returns `42`. -/
theorem returns :
    Returns (Extracted.program.withExit ret) ((s0 mem0).setRet ret)
      (fun s' => ABIReturn ((s0 mem0).setRet ret) s' ∧ results 1 s' = [42#64]) ∧
    Returns (Extracted.program.withExit ret) ((s0 mem1).setRet ret)
      (fun s' => ABIReturn ((s0 mem1).setRet ret) s' ∧ results 1 s' = [42#64]) := by
  refine ⟨((correctness 21#64 0) _ setup0 pre0 ret hret).mono ?_,
    ((correctness 21#64 1) _ setup1 pre1 ret hret).mono ?_⟩
  all_goals intro s' h; exact ⟨h.1, by rw [h.2]; decide⟩

/-- The hypotheses of `correctness` hold together, for the flag clear and for the flag set. -/
theorem nonvacuous : ∃ (ret : Nat) (s s' : State), RetAddr Extracted.program ret ∧
    CallSetup0 Extracted.entry [21#64] s ∧
    (StackWritable s 0 8 ∧ GlobalApart Extracted.program.globals "example.com/basic.useFast" (s.regs regSP).toNat ∧
      GlobalBytesIs Extracted.program.globals s.mem "example.com/basic.useFast" 0 1 0) ∧
    CallSetup0 Extracted.entry [21#64] s' ∧
    (StackWritable s' 0 8 ∧ GlobalApart Extracted.program.globals "example.com/basic.useFast" (s'.regs regSP).toNat ∧
      GlobalBytesIs Extracted.program.globals s'.mem "example.com/basic.useFast" 0 1 1) ∧
    Returns (Extracted.program.withExit ret) (s.setRet ret) (fun t => ABIReturn (s.setRet ret) t ∧ results 1 t = [42#64]) ∧
    Returns (Extracted.program.withExit ret) (s'.setRet ret) (fun t => ABIReturn (s'.setRet ret) t ∧ results 1 t = [42#64]) :=
  ⟨ret, s0 mem0, s0 mem1, hret, setup0, pre0, setup1, pre1, returns.1, returns.2⟩

end Witness

end Proof
