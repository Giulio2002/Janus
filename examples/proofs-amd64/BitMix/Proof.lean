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

end Proof
