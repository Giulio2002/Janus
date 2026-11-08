import Janus
import Extracted

/-! `example.com/basic/v3.BitMix(x, y uint64, n uint) uint64` on amd64 built with `GOAMD64=v3`:
`(x &^ y) ^ (x & (x-1)) ^ (y << (n & 63))`. The compiler emits three BMI instructions,

    ANDN AX, BX, DX     ; DX = AX AND NOT BX  (andn %rax,%rbx,%rdx)
    SHLX CX, BX, CX     ; CX = BX << (CX & 63)
    BLSR AX, AX         ; AX = (AX - 1) AND AX
    XORQ DX, AX
    XORQ CX, AX
    RET

and the theorem states the result for all arguments. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (x y n : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y, n] 1
      (fun s => StackWritable s 0 8)
      (fun r => r = [(x &&& ~~~y) ^^^ (x &&& (x - 1)) ^^^ (y <<< (n.toNat % 64))]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  rw [BitVec.and_comm (x - 1#64) x, BitVec.and_comm (~~~y) x,
    BitVec.xor_comm (x &&& (x - 1#64)) (x &&& ~~~y)]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def x : BitVec 64 := 0xF0F0#64
def y : BitVec 64 := 0x1234#64
def n : BitVec 64 := 5#64

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 3 then y else if i = 1 then n else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y, n] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64) (n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y, n] s ∧ (StackWritable s 0 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (results 1 s') = [(x &&& ~~~y) ^^^ (x &&& (x - 1)) ^^^ (y <<< (n.toNat % 64))]) :=
  ⟨ret, s0, x, y, n, hret, setup, hpre, correctness x y n ret hret s0 setup hpre⟩

end Witness

end Proof
